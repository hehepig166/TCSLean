# Proposal: Lovász Local Lemma (Asymmetric Form)

## Motivation

The Lovász Local Lemma (LLL) is the workhorse existence theorem of the probabilistic method: a
family of bad events may be simultaneously avoidable even when the union bound is useless,
provided each bad event is sufficiently unlikely and depends on only a limited number of the
others. StatsMLlib currently has a deep concentration-of-measure arsenal (Hoeffding, McDiarmid,
Efron–Stein, Chernoff, Talagrand) but **no probabilistic-method result at all**: nothing that
converts local probability bounds plus local dependence structure into an existence statement.

Formalizing the LLL fills that gap and unlocks the classical applications:

- bounded-dependency k-SAT (`d ≤ 2^(k−2)` ⇒ satisfiable),
- proper colorings of uniform hypergraphs (`Δ ≤ q^(k−1)/(ek)` ⇒ q-colorable),
- later, the variable model (events determined by disjoint independent-variable sets) and the
  symmetric/`4pd` corollaries.

Survey C confirmed this is a green field with proven technology: mathlib v4.32.0 contains no
LLL (and no mathlib PR is in flight), the Isabelle AFP entry (Edmonds 2023) is the first
machine-checked LLL, and three standalone Lean efforts exist (two classical, one
constructive Moser–Tardos). The contribution here is the classical LLL done *properly for
mathlib* — library-grade, in StatsMLlib's Probability layer, statement-level compatible with a
future Moser–Tardos extension (but not duplicating it).

This proposal formalizes the simplest version: the **asymmetric LLL** with an explicit
dependency graph, following the classical conditional-probability proof. A key survey finding
(B_proof_strategy) is that the proof can be reorganized as an order-free *peeling* strong
induction over arbitrary finite subsets, so the whole core avoids conditional probability,
division, and any enumeration of the index type — the ENNReal route below is the result.

## Proposed Theorem (Simplest Version: Asymmetric LLL)

### Definitions

For a finite index type `ι` and a family of measurable "bad events" `A : ι → Set Ω`, write
`bset A S := ⋂ j ∈ S, (A j)ᶜ` ("none of the events indexed by `S` occurs"). The dependency
structure is a loopless `SimpleGraph ι`; the neighborhood `Γ(i) := G.neighborSet i`.

```lean
def bset (A : ι → Set Ω) (S : Finset ι) : Set Ω := ⋂ j ∈ S, (A j)ᶜ

/-- `G` is a dependency graph for `A`: each `A i` is independent of `bset A S` for every
index set `S` of non-neighbors of `i` (not containing `i`). This is the fragment of the
classical definition (gpt-notes Def 3.1 / Def 1.1) that the proof actually consumes. -/
def IsDependencyGraph (G : SimpleGraph ι) (A : ι → Set Ω) : Prop :=
  ∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) → IndepSet (A i) (bset A S)
```

Tracing the classical proof shows that independence of `A i` from *every Boolean combination*
of non-neighbor events is never used — only independence from `bset A S` itself. The weak
`IsDependencyGraph` above is therefore the honest minimal hypothesis; an equivalence with the
strong classical form is a deferred follow-up (~100–150 lines, see Open Questions).

### Main Theorem (Asymmetric LLL)

```lean
theorem lovaszLocalLemma {G : SimpleGraph ι} [DecidableRel G.Adj] {A : ι → Set Ω} (x : ι → ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hdg : IsDependencyGraph G A)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))) :
    ENNReal.ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)

theorem lovaszLocalLemma_pos (same hypotheses) :
    0 < μ (⋂ i, (A i)ᶜ)          -- the "existence" form: some outcome avoids all bad events

theorem lovaszLocalLemma_probReal (same hypotheses) :
    ∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)          -- ℝ corollary via μ.real
```

In words: if for every `i` the probability of `A i` is at most `x i · ∏_{j ∈ Γ(i)} (1 - x j)`
for some weights `x i ∈ [0,1)`, then the probability that *no* bad event occurs is at least
`∏ i (1 - x i) > 0`.

### Initial Scope (decisions, with rationale — see survey B §1)

- **Index type: `{ι : Type*} [Fintype ι] [DecidableEq ι]`, not `Fin n`.** The proof needs no
  total order: the chain-rule steps of the classical proof are replaced by peeling identities
  over `Finset`s and a strong induction on `S.card`. Applications keep their natural index
  types (clauses, hyperedges) with no transport glue.
- **Dependency structure: `SimpleGraph ι`** (with `[DecidableRel G.Adj]` as a theorem
  hypothesis). `G.neighborFinset i` needs only `[Fintype ι]`, and loop-freeness makes
  `Γ(i) ∪ {i}` collapse to `Γ(i)`. The symmetric corollaries read `G.degree i`.
- **Independence hypothesis: weak `IsDependencyGraph`** (above) — the classical strong form
  (independence from the family of all Boolean combinations, gpt-notes Def 1.1) is strictly
  stronger than what the proof consumes and is deferred.
- **Weights: `x : ι → ℝ`** with hypotheses `0 ≤ x i` and `x i < 1` (keeps `linarith`/`field_simp`
  usable; no `tsub` casting noise).
- **Arithmetic: ENNReal for measures and the induction, ℝ only in the final corollary.**
  All inequalities are written multiplicatively — **no conditional probability and no division
  appear anywhere in the core proof** (the optional conditional form of the classical key lemma
  is a cheap add-on, see Missing Infrastructure).
- **Mathlib ℝ-probability API: `μ.real`** (the old `ProbabilityTheory.probReal` function no
  longer exists in v4.32.0 — it was renamed to `Measure.real`).

## Proposed Location & Expected Modifications (Files)

**Single new file: `StatsMLlib/Probability/LovaszLocal.lean`**
(module `StatsMLlib.Probability.LovaszLocal`)

Placed flat under `Probability/`, exactly like `SmallBall.lean` — the precedent for a
standalone named-theorem package that fits no existing subfolder (`Concentration`, `Entropy`,
`Independence`, …). It satisfies the ARCHITECTURE.md import tiers (mathlib imports + optionally
same-layer `StatsMLlib.Probability.Independence.FinsetPi`). Promotion trigger to
`Probability/LovaszLocal/{Basic,Applications}.lean`: when a second theorem family (symmetric,
Moser–Tardos, applications) lands, or the file approaches ~1500 lines (survey D §4).

| Status | File | Description |
|---|---|---|
| NEW | `StatsMLlib/Probability/LovaszLocal.lean` | Asymmetric LLL: `bset`, `IsDependencyGraph`, the (P1)/(P2) induction, `lovaszLocalLemma(_pos/_probReal)` (~600–750 lines). Mathlib-style header + `/-!` docstring with `## Main definitions` / `## Main results` / `## References`. |
| EDIT | `StatsMLlib/FILE_TREE.md` | Add the `LovaszLocal.lean` line under `Probability/`; update counts (Probability 42 → 43/44, Total 89 → 90/91 — the file is hand-maintained and already stale by one: the in-flight `ConvexDistance.lean` is missing from the tree and counts). |
| EDIT | `StatsMLlib/README.md` | Update "The public source contains 89 modules"; optionally add the LLL to "Selected results". |
| — | mathlib, `lakefile.lean`, `ARCHITECTURE.md` | Unchanged. No mathlib modification; the flat file fits existing rules and linters. |
| NEW (doc, outer repo) | `doc/lovasz/01_proposal/proposal.md` (+ optional `proposal_concise.md` for talagram parity) | This document. |
| NEW (doc, later phases) | `doc/lovasz/02_blueprint/BLUEPRINT.md`, `03_gpt_review/*.md`, `04_pr/PR_DESCRIPTION.md` | Follow the talagram lifecycle (survey D §5). |

Git choreography: code commits inside the submodule as `feat(LL.NN): attempt N — <summary>`;
doc milestones in the outer repo as `doc(LL.NN): mark <item> as done; bump StatsMLlib pointer`.

## Proof Approach

The classical proof (gpt-notes Lemma 4.2 + §4.2, Alon–Spencer ch. 5) proves, by induction on
`|S|`, a conditional bound `P(A i | B S) ≤ x i` plus positivity of `P(B S)`, and assembles the
final product via the chain rule over an enumeration. **Survey B's reorganization** removes
every conditional probability, division, and enumeration: prove by `Finset.strongInductionOn`
the simultaneous invariant

```
(P1 S)  ENNReal.ofReal (∏ j ∈ S, (1 - x j)) ≤ μ (bset A S)
(P2 i S)  i ∉ S → μ (A i ∩ bset A S) ≤ ENNReal.ofReal (x i) * μ (bset A S)
```

- **Base `S = ∅`:** `bset A ∅ = univ`; (P1) is `ofReal 1 = 1 ≤ μ univ = 1`; (P2) is the LLL
  hypothesis plus `∏_{Γ(i)} (1 - x j) ≤ 1` (pointwise factors ≤ 1).
- **P1 step:** pick `r ∈ S`; the peeling identity `μ (B S) = μ (B (S.erase r)) − μ (A r ∩ B (S.erase r))`
  (measure split, finiteness from `IsProbabilityMeasure`) plus P2-IH at `(r, S.erase r)` gives
  `μ (B S) ≥ (1 − ofReal (x r)) · μ (B (S.erase r)) ≥ ofReal (∏ j ∈ S, (1 − x j))`, using the
  glue `ofReal (1 − x r) = 1 − ofReal (x r)` (from `ENNReal.ofReal_sub`, or a 4-line
  `ofReal_one_sub`).
- **P2 step:** split `S` into neighbors `N := S.filter (G.Adj i ·)` and non-neighbors
  `M := S.filter (¬ G.Adj i ·)`. If `N = ∅`, `hdg` at `(i, S)` closes it as in the base case.
  If `N ≠ ∅`:

  ```
  μ (A i ∩ B S) ≤ μ (A i ∩ B M)                                    -- B S ⊆ B M, measure_mono
               = μ (A i) · μ (B M)                                 -- hdg at (i, M)
               ≤ ofReal (x i · ∏_{Γ(i)} (1 - x j)) · μ (B M)      -- hLLL
               ≤ ofReal (x i · ∏_{N} (1 - x j)) · μ (B M)         -- N ⊆ Γ(i), prod_le_prod_of_subset_of_le_one'
               ≤ ofReal (x i) · μ (B (N ∪ M))                     -- product-chain bound (below)
               = ofReal (x i) · μ (B S)                            -- S = N ∪ M
  ```

  The **product-chain bound** `ofReal (∏_{j∈N} (1 − x j)) · μ (B M) ≤ μ (B (N ∪ M))` is proved
  by nested `Finset.induction` on `N`, peeling one element at a time with the same one-step
  bound as in the P1 step and P2-IH at the set `M ∪ (N.erase r)` of size `|S| − 1` — this is
  the order-free replacement for the classical chain rule (gpt-notes (4)).
- **Assembly:** (P1) at `S = univ` is the theorem, since `bset A univ = ⋂ i, (A i)ᶜ`.
  Positivity: each `1 − x i > 0`, so `∏ i (1 − x i) > 0` (`Finset.prod_pos`), hence
  `0 < ofReal (∏ i, (1 − x i))` and `0 < μ (⋂ i, (A i)ᶜ)`.

### Proof decomposition

| Step (gpt-notes anchor) | Lean declaration | Difficulty | Est. lines |
|---|---|---|---|
| §3 setup: `B S` | `bset` + `bset_empty/_insert/_subset_of_subset/_union/_univ_eq_iInter` | Easy | 60 |
| measurability of `B S` | `measurableSet_bset` (from `Finset.measurableSet_biInter`) | Easy | 15 |
| Def 3.1 (weak) | `IsDependencyGraph` | Easy | 10 |
| `1 − ofReal x` glue | `ofReal_one_sub` (or direct `ENNReal.ofReal_sub` use) | Easy | 8 |
| peeling identity | `measure_bset_insert` | Easy–Medium | 40 |
| one-step peeling bound | `measure_bset_insert_le` | **Medium** | 50 |
| chain-rule-free product bound | `prob_bset_inter_prod` | **Medium** | 70 |
| **(P1)+(P2) strong induction** | `lll_prob_bset` | **Hard** | 250–350 |
| final assembly | `lovaszLocalLemma` | Easy | 25 |
| positivity | `lovaszLocalLemma_pos` | Easy | 10 |
| ℝ corollary | `lovaszLocalLemma_probReal` (`μ.real`, `ofReal_le_iff_le_toReal`) | Easy | 15 |
| conditional form `μ[A i ‖ B S] ≤ ofReal (x i)` (Lemma 4.2 verbatim) | `lovaszLocalLemma_cond` *(optional)* | Easy | 20 |

**Total estimate: ~600–750 lines** for the asymmetric LLL core. The three hard points are the
peeling bound (ENNReal `sub_mul` finiteness threading), the product-chain bound (nested
induction), and the combined induction (IH access at two different smaller sets).

## Relevant Existing Modules

### Mathlib (all present in v4.32.0 — verified in survey A)

| Module | Provides |
|---|---|
| `Probability.Independence.Basic` | `IndepSet`, `iIndepSet`, `Indep`, `iIndep`, `IndepSet.measure_inter_eq_mul` (:584), `indepSet_iff_measure_inter_eq_mul` (:579), `iIndep.meas_biInter` (:195), `iIndepSet.indep_generateFrom_of_disjoint` (:506) — the independence hypothesis needs **no new definitions** |
| `Probability.ConditionalProbability` | `cond`, `cond_apply`, `cond_mul_eq_inter` — **not needed by the core route**; only the optional conditional-form lemma |
| `Combinatorics.SimpleGraph.Finite` | `neighborSet`, `neighborFinset` (needs `[Fintype (G.neighborSet v)]`, automatic from `[Fintype ι]`), `degree`, `maxDegree` |
| `Data.Finset.Card` | `Finset.strongInductionOn` (:852), `card_erase_lt_of_mem` (:159) — the descent step |
| `Algebra.Order.BigOperators.*` | `Finset.prod_le_prod_of_subset_of_le_one'` (:141) — exactly the `N ⊆ Γ(i)` step; `prod_le_one'`, `prod_pos` |
| `Data.ENNReal.{Real,Operations,Inv}` | `ofReal_mul`, `ofReal_prod_of_nonneg`, `ofReal_sub`, `sub_eq_of_eq_add`, `sub_mul`, `le_div_iff_mul_le` — the full multiplicative toolbox |
| `MeasureTheory.Measure.*` | `measure_inter_add_sdiff` (peeling), `Finset.measurableSet_biInter`, `measure_ne_top`; `Measure.real` (ℝ API, **replaces the removed `probReal`**) |
| `Algebra.Order.Ring.Pow` | `one_add_mul_le_pow` (Bernoulli) — symmetric `4pd` follow-up |
| `Analysis.Complex.Exponential` | `Real.one_add_inv_pow_le_exp` ((1+1/d)^d ≤ e), `Real.exp_pos` — symmetric `ep(d+1)` follow-up |

### StatsMLlib (none strictly required for the core)

| Module | Potential Use |
|---|---|
| `Probability.Independence.FinsetPi` | `pi_eval_iIndepFun`, `pi_comp_eval_iIndepFun`, `pi_map_eval` — the variable-model independence infrastructure for future applications (Proposition 3.2 of gpt-notes) |

Survey A also confirmed: **LLL absent from mathlib v4.32.0** (only unrelated Lovász-form
Kruskal–Katona hits); StatsMLlib has no uses of `ProbabilityTheory.cond` yet; no
dependency-graph API exists anywhere — `IsDependencyGraph` is new.

### External formalizations (survey C)

- **Isabelle AFP** [*Lovász Local Lemma*](https://www.isa-afp.org/entries/Lovasz_Local.html)
  (Edmonds 2023; CPP 2024, arXiv:2310.00513) — the first machine-checked LLL: asymmetric LLL
  over a dependency *digraph* + symmetric corollary, strong-induction proof with conditional
  probability; constructive version explicitly future work. Its main lesson: the LLL proof
  itself is routine — *proving independence for concrete events* is where effort concentrates.
- **Lean:** nothing in mathlib (docs/issues/Zulip checked). Three standalone repos:
  `nsglover/lean-lovasz-local-lemma` (Lean 3 course project), `Mahesh-Ramani/lovasz-local-lemma-lean4`
  (Lean 4.28, ℝ/`toReal` arithmetic, peeling induction — the closest precedent), and
  `EdouardBonnet/moser-tardos` (**sorry-free, active as of 2026-08-08** — Moser–Tardos and HSS
  distributional LLL; the natural upstream for any future algorithmic extension, not to be
  duplicated).
- **Coq/HOL4/HOL Light/Mizar:** nothing.

## Missing Infrastructure (Must Be Created)

All declarations live in the proposed file. The critical new pieces:

1. **`bset` + `IsDependencyGraph`** — the two definitions (and 5 trivial `bset` lemmas). Easy.
2. **`ofReal_one_sub`** — `ofReal (1 − x) = 1 − ofReal x` for `0 ≤ x ≤ 1` (~4 lines; only real
   ENNReal glue gap found by survey A).
3. **`measure_bset_insert` / `measure_bset_insert_le`** — the peeling identity and one-step
   bound (Medium; the ENNReal `sub_mul` finiteness threading lives here, wrapped once).
4. **`prob_bset_inter_prod`** — the chain-rule-free product lower bound (Medium).
5. **`lll_prob_bset`** — the (P1)+(P2) strong induction, the heart of the proof (Hard,
   ~250–350 lines).
6. **`lovaszLocalLemma`, `lovaszLocalLemma_pos`, `lovaszLocalLemma_probReal`** — the three
   public statements (Easy).
7. Optional: **`lovaszLocalLemma_cond`** + the three small `cond` glue lemmas
   (`cond_eq_of_indepSet`, `cond_compl_eq_one_sub`, `cond_le_one` — all absent from mathlib,
   survey A §2.3) *only if* the conditional form of the classical key lemma is included;
   the core route avoids `cond` entirely.

## Code Conventions

Survey D §2–3 provides the full template. Key constraints (from `lakefile.lean` +
CONTRIBUTING.md):

- **Header:** `/- Copyright (c) <year> <holder>. All rights reserved. / Released under Apache
  2.0 license as described in the file LICENSE. / Authors: … -/`; `/-!` docstring with
  `## Main definitions`, `## Main results`, `## References` (bare `[key]`-style citations).
- **Namespace:** module-specific namespace (`SmallBall` pattern, e.g. `namespace LovaszLocal`)
  or top-level prefixed names (`McDiarmid` pattern) — open question below.
- **Statements:** ENNReal for measures, ℝ for real-valued statements (`μ.real`).
- **Strict linters:** no `sorry`/`axiom`/`admit`; no `#`-commands; no `λ` (use `fun`);
  bullets must be `·`; lines ≤ 100; `autoImplicit := false`; `pp.unicode.fun := true`;
  no `obtain`-as-`rcases`/`refine`-as-sugar; warning-free builds.

## API Questions for Maintainers

1. **Weak `IsDependencyGraph` as the public definition — acceptable?** The proof consumes only
   independence from `bset A S` (intersections of complements); the classical strong form
   (gpt-notes Def 1.1) is ~100–150 lines away as an equivalence. Recommend: weak form as the
   public hypothesis, strong-form equivalence as a follow-up.
2. **Weights: `x : ι → ℝ` with `hx₀ : 0 ≤ x i` and `hx₁ : x i < 1` — or `ι → Ioo (0 : ℝ) 1`?**
   Recommend the flat ℝ form with two hypotheses (proofs use the endpoints explicitly).
3. **Bundled or split `ofReal` in `hLLL`?** Recommend the bundled
   `μ (A i) ≤ ofReal (x i * ∏ …)` (one `ofReal_mul`/`ofReal_prod_of_nonneg` away from either
   use; symmetric corollaries plug in untouched).
4. **Primary public statement: the product bound, the `_pos` existence form, or both?**
   Recommend all three (`lovaszLocalLemma`, `lovaszLocalLemma_pos`, `lovaszLocalLemma_probReal`);
   `_pos` is the headline "probabilistic method" statement.
5. **Include the conditional-probability form of the key lemma (`μ[A i ‖ B S] ≤ ofReal (x i)`)
   for math-text fidelity?** Cheap (step 14) but requires creating the three `cond` glue
   lemmas. Recommend deferring until needed; the multiplicative form is fully self-contained.
6. **Naming/namespace:** `namespace LovaszLocal` (SmallBall pattern) vs top-level
   `lovasz_local_*`-prefixed (McDiarmid pattern)? Recommend the SmallBall pattern.

## Future Extensions (Out of Scope for Initial PR)

| Extension | Difficulty | Notes |
|---|---|---|
| Symmetric LLL `e·p·(d+1) ≤ 1` | Medium | `x i := 1/(d+1)`, `Real.one_add_inv_pow_le_exp`; sharper `p ≤ d^d/(d+1)^(d+1)` internal form bypasses `e` |
| `4pd ≤ 1` criterion | Easy–Medium | `x i := 1/(2d)`, Bernoulli `one_add_mul_le_pow`; no exp |
| Strong-form equivalence | Medium | `IsDependencyGraph` ⟺ classical independence-from-family, via π-system/atoms lemmas |
| Variable model (Prop 3.2) | Medium | Needs a new "disjoint index sets ⟹ independent projections" lemma for `Measure.pi` (not in mathlib, TBC); then `IsDependencyGraph` follows via `Independence.FinsetPi` |
| k-SAT application | Medium | After variable model: `μ (A C) = 2^(-k)` via `Measure.pi_pi`, conclude `Nonempty` from `0 < μ` |
| Hypergraph coloring | Medium | `μ (A e) = q^(1−k)`, degree counting `d ≤ k(Δ−1)` |
| Lopsided LLL | Hard | Definitional subtlety + witness-tree swap argument (MT §6); defer |
| Shearer's bound | Hard | Optimization-flavored; defer |
| Constructive Moser–Tardos | — | **Do not duplicate**: already sorry-free in `EdouardBonnet/moser-tardos` (active) |

PR split recommendation (survey B §4): PR 1 = asymmetric LLL only; PR 2 = symmetric + `4pd`;
PR 3 = variable model; PR 4+ = applications.

## References

- P. Erdős and L. Lovász, "Problems and results on 3-chromatic hypergraphs and some related
  questions", in *Infinite and Finite Sets* (Colloq., Keszthely, 1973), Vol. II, pp. 609–627,
  North-Holland, 1975.
- N. Alon and J. H. Spencer, *The Probabilistic Method*, Wiley, 4th ed. 2016, Chapter 5
  (asymmetric form via `x₁,…,xₙ ∈ (0,1)`, symmetric form `ep(d+1) ≤ 1`).
- C. Edmonds, L. C. Paulson, "Formal Probabilistic Methods for Combinatorial Structures using
  the Lovász Local Lemma", CPP 2024, DOI 10.1145/3636501.3636946, arXiv:2310.00513.
- R. A. Moser and G. Tardos, "A constructive proof of the general Lovász Local Lemma",
  J. ACM 57(2), 2010. arXiv:0903.0544.
- Yitong Yin, *Basics of Randomized Algorithms* (LLL lecture slides), NJU summer school 2025
  (`ref/尹一通-lll.pdf`).
- Reference proof notes: `ref/gpt-notes.md` (this proposal follows its Theorem 4.1 statement;
  the proof is reorganized per survey B).

---

## Survey Reports

Detailed research reports supporting this proposal are in the `survey/` directory:

| File | Content |
|---|---|
| [PLAN.md](survey/PLAN.md) | Survey plan and checklist |
| [A_mathlib_inventory.md](survey/A_mathlib_inventory.md) | mathlib v4.32.0 inventory: LLL absent; full independence/cond/SimpleGraph/Finset/ENNReal audit with verified names and lines |
| [B_proof_strategy.md](survey/B_proof_strategy.md) | Pinned statement, the (P1)/(P2) order-free peeling induction, 14-step decomposition, risks, open questions |
| [C_external_formalizations.md](survey/C_external_formalizations.md) | Isabelle AFP entry, 3 Lean repos, other provers, literature anchors, lopsided-LLL scoping |
| [D_repo_conventions.md](survey/D_repo_conventions.md) | ARCHITECTURE rules, file style, linters, placement recommendation, doc/git workflow, expected modifications |
