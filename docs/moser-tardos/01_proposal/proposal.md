# Proposal: Moser–Tardos Algorithmic Lovász Local Lemma (Asymmetric Form)

## Motivation

The classical Lovász Local Lemma formalized in `StatsMLlib.Probability.LovaszLocal` is an
*existence* statement: under the LLL condition some outcome avoids all bad events, but it gives
no way to find one. In the **variable framework** — bad events are determined by finitely many
mutually independent variables — the **Moser–Tardos resampling algorithm** closes this gap: it
starts from a random assignment and, while some bad event occurs, resamples all variables of one
occurring event. Moser and Tardos proved (arXiv:0903.0544, Thm 1.2) that under the same
asymmetric LLL condition, the expected number of resamplings of event `A` is at most
`x(A)/(1 − x(A))`, with the total bounded by `∑ x(A)/(1 − x(A))` — making the LLL *constructive*
and giving an expected-time analysis on top of mere existence.

For StatsMLlib this is the natural next step after `LovaszLocal.lean`: the variable model
(events determined by independent-variable sets) was already flagged in the LLL PR description
as the key follow-up, and the algorithmic LLL is its canonical application (bounded-dependency
k-SAT, hypergraph coloring — Alon–Spencer §5.7).

**Prior-art caveat (survey C).** The core MT bound was very recently formalized in Lean,
sorry-free, by Édouard Bonnet (`EdouardBonnet/moser-tardos`, registered as **lax-41** in the new
Lax Lean Archive, ~2,100 proof lines, on an infinite resampling table via
`Measure.infinitePi`). This proposal is *not* a duplication play: the contribution here is a
**library-grade integration into StatsMLlib** — (1) a deliberately different, simpler
**finite-truncation formulation** (`Ω_N` tables, uniform-in-`N` bounds, multiplicative Markov
tail bound, ε–N termination) that states the useful quantitative corollaries directly and
avoids infinite-product machinery entirely; (2) the **constructive variable-model LLL**
(`∃ σ, ∀ i, σ ∉ A i`) as a corollary, cross-linked to the existing `LovaszLocal` file;
(3) the symmetric form and (later) applications; (4) house API and conventions. Coordination
with lax-41 is listed as an open question for maintainers rather than silently re-proving.

## Proposed Theorem (Simplest Version: Asymmetric Moser–Tardos, Finite Truncation)

### Variable framework (informal)

Finite event index `ι` and variable index `κ` (both `[Fintype] [DecidableEq]`); variable `j`
takes values in a measurable space `Ω j` with probability measure `μ j`; the joint law on
`Π j, Ω j` is `Measure.pi μ` (denoted `μπ`). Each bad event `A i ⊆ Π j, Ω j` is **determined
by** `vbl i : Finset κ`. The dependency structure is the **variable-overlap graph**
(`Adj i j ↔ i ≠ j ∧ (vbl i ∩ vbl j).Nonempty`), with inclusive neighborhood
`Γ⁺ i = Γ(i) ∪ {i}`. LLL condition for weights `x : ι → ℝ` with `0 ≤ x i`, `x i < 1`:

```
μπ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ Γ(i), (1 - x j))        for all i        (LLL)
```

### Definitions

```lean
namespace MoserTardos

def DeterminedBy (A : Set (Π j, Ω j)) (S : Finset κ) : Prop :=
  ∃ f : (Π j : S, Ω j) → Prop, ∀ σ, σ ∈ A ↔ f fun j => σ j

-- truncated resampling table: N+1 rows per variable (the cumulative-row convention of the
-- notes §7: "resampled s times ⟹ value is X^(s)"; up to N steps can reach row N)
def ΩN (N : ℕ) (Ω : κ → Type*) : Type* := Π j : κ, Fin (N + 1) → Ω j
def μN (N : ℕ) (μ : ∀ j, Measure (Ω j)) : Measure (ΩN N Ω) :=
  Measure.pi (fun p : Σ j : κ, Fin (N + 1) => μ p.1)      -- probability measure, inferable
```

The algorithm is a deterministic function of the table: state = rows consumed per variable
`c : κ → Fin (N+1)`; the occurring-and-available violated set is selected by an arbitrary
deterministic rule `pick : {S : Set ι // S.Nonempty} → ι` with `hpick : pick S ∈ S.1` (the
analysis is uniform over the rule — the notes' "fix any rule"); resampling `i` advances `c j`
for `j ∈ vbl i`. This yields the **padded execution log** `log : ΩN N Ω → ℕ → Option ι`
(`some e` at genuine steps, `none` after termination), the stopping time
`R : ΩN N Ω → ℕ` (first `t ≤ N` with no violated event, else `N`; always `R ≤ N`), and

```lean
def countLog {N} (Λ : ΩN N Ω → ℕ → Option ι) (ω) (i) : ℕ :=
  ((Finset.range N).filter fun t => Λ ω t = some i).card
```

### Main Theorem (Asymmetric Moser–Tardos)

```lean
theorem moserTardos_bound {N : ℕ} (Ω : κ → Type*) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
    (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1)
    (i : ι) :
    ∫⁻ ω : ΩN N Ω, (countLog (log vbl A pick hpick) ω i : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (x i / (1 - x i))
```

The theorem holds for **every** `pick` — uniformity over the choice rule is free by
parametricity. The `x i = 0` case needs no division: it is absorbed inside the proof via a
single `by_cases` (the root factor `μπ (A i) = 0` kills every witness-tree weight). All
arithmetic on the right is ℝ inside `ENNReal.ofReal`; **no ENNReal division occurs anywhere**.

### Corollaries (all in initial scope)

```lean
theorem moserTardos_total : ∫⁻ ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
    ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))

theorem moserTardos_tail : (N : ℝ≥0∞) * μN N μ {ω | R vbl A pick hpick ω = N}
    ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))
    -- multiplicative Markov bound; the divided form μN(R = N) ≤ Σx/(1-x)/N is FALSE for N = 0
    -- in Lean's ℝ (0/0 = 0), so the honest statement is multiplicative; the ε–N form is a
    -- follow-up with N ≠ 0

theorem moserTardos_exists : ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i
    -- constructive LLL: pick N with Σ x/(1-x) < N; μN(R = N) < 1 forces μN{R < N} > 0, and the
    -- algorithm's output at R < N avoids every bad event. No [Nonempty (Π j, Ω j)] needed.

theorem moserTardos_symmetric {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ p)
    (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∫⁻ ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / d)
    -- follow-up PR (survey B §1.2): x ≡ 1/(d+1); the d = 0 pitfall is excluded by hd1
```

### Initial Scope (decisions, with rationale — survey B §4)

- **Finite truncation, not the infinite table.** `Measure.infinitePi` *does* exist in mathlib
  v4.32.0 (survey A: `Mathlib/Probability/ProductMeasure.lean:356`, Ionescu–Tulcea), so the
  infinite-table a.s. formulation is feasible — but the truncated statement is strictly simpler
  (no ENNReal∞-valued stopping times, no monotone-convergence pass), and it is exactly what
  produces the useful corollaries (uniform-in-`N` bound, multiplicative tail bound, constructive
  existence). The infinite a.s. version is a clean follow-up, and lax-41 precedent confirms the
  route if wanted later.
- **Table rows: `Fin (N+1)` per variable, not `Fin N`** (survey B finding 1) — the cumulative
  row convention of the notes requires it; with `Fin N` rows a variable resampled at every step
  overflows and the coupling identity (14.5) provably breaks.
- **Padded log: `Option ι`-valued** (survey B finding 2) — no `[Nonempty ι]` dummy, padded
  entries are structurally excluded from witness trees, Prop 12.1 stated for `t < R` only.
- **Pick rule: parameterized** `pick`/`hpick` — the notes' "the analysis does not depend on
  which rule is used" becomes the theorem statement itself (least-index is a one-line
  `Finset.min'` corollary if wanted); no `[LinearOrder ι]`.
- **Witness trees: custom inductive** `WitnessTree ι` with `List` children (mathlib's `Tree` is
  a binary storage tree); `Proper` = distinct child labels per parent; `IsGood` = proper +
  same-depth vertices have disjoint `vbl` (path-based; the coupling's hypothesis).
- **Determinism: `DeterminedBy` as an ∃-hypothesis** — exactly what the structural τ-check
  consumes; no coordinate completion, no `Nonempty (Ω j)`.
- **Expectations: `lintegral`** (ENNReal monotone arithmetic), matching the `LovaszLocal` house
  style; ℝ only inside `ofReal`.
- **Dependency graph: defined as the overlap graph** — no graph parameter; this makes the
  notes' Lemma 11.1 clean (`[u] ∈ Γ⁺([v])` holds unconditionally when variables overlap,
  inclusive of the equal-label case; the notes' sentence `[u] ∈ Γ([v])` is sloppy there but the
  needed conclusion survives).

## Proposed Location & Expected Modifications (Files)

**New folder: `StatsMLlib/Probability/MoserTardos/`** — the core estimate is ≈ 2400–2900
lines, far past the ~1500-line flat-file promotion trigger used for `LovaszLocal.lean`
(surveys B §6 + D §3). Suggested split (survey B):

| File | Items | Content | Est. lines |
|---|---|---|---|
| `VariableModel.lean` | A1–A3 | `overlapGraph`, `DeterminedBy`, `ΩN`/`μN` | ~85 |
| `Algorithm.lean` | B4–B8 | state/step/run, stopping time `R`, padded log, measurability | ~390 |
| `WitnessTree.lean` | C9–C15 | tree type + path API, construction `treeAt`/`T`, structural lemmas (properness, depth lemma, injectivity) | ~640 |
| `Coupling.lean` | D16–D18 | τ-check, `check_probability`, coupling lemma | ~570 |
| `GaltonWatson.lean` | E19–E21 | `gwWeight` + telescope, `𝒯_i(N)` Fintype, sum bound | ~420 |
| `Basic.lean` | F22–F26 | counting identity, **`moserTardos_bound`**, total/tail/exists corollaries (+ module docstring) | ~460 |

| Status | File | Description |
|---|---|---|
| NEW | `StatsMLlib/Probability/MoserTardos/*.lean` (6 files, modules `StatsMLlib.Probability.MoserTardos.*`) | The formalization above; `Basic.lean` carries the `/-!` docstring with `## Main definitions` / `## Main results` / `## References` and re-exports the public API |
| EDIT | `StatsMLlib/FILE_TREE.md` | Insert the `MoserTardos/` lines under `Probability/` (between `LovaszLocal.lean` and `SmallBall.lean`); counts 90 → 91 modules, Probability 43 → 44 (current counts verified accurate on this branch, survey D §4) |
| EDIT | `StatsMLlib/README.md` | Module count (line 15); optionally add MT to "Selected results" |
| — | mathlib, `lakefile.lean`, `ARCHITECTURE.md`, `AUTHORS` | Unchanged |
| NEW (doc, outer repo) | `doc/moser-tardos/01_proposal/…` | This proposal + survey |
| NEW (doc, later phases) | `doc/moser-tardos/02_blueprint/BLUEPRINT.md`, `03_gpt_review/*.md`, `04_pr/PR_DESCRIPTION.md` | Follow the talagram/lovasz lifecycle |

Git choreography: submodule commits `feat(MT.NN): attempt N — …` on `zzk/moser-tardos`
(stacked on `zzk/lovasz-local-lemma-gptv2`); outer-repo doc commits
`doc(MT.NN): …; bump StatsMLlib pointer`.

## Proof Approach

The chain of the notes (§6–§20) transfers to the truncated table verbatim (survey B audited
every step, §3):

```
resampling algorithm → execution log → witness trees → coupling lemma → Galton–Watson sum → bound
```

- **Witness trees.** `T(ω,t)` is built by folding the reversed log prefix: each genuine entry
  `some i` is attached below the deepest eligible vertex (`i ∈ Γ⁺(label)`), ties broken
  deterministically (leftmost). Structural lemmas, all consequences of one spec lemma for the
  fold: occurring trees are **proper** (Prop 10.1); **Lemma 11.1** (earlier entry sharing a
  variable ⟹ strictly deeper) and **Cor 11.2** (same depth ⟹ disjoint `vbl`) — clean because
  Γ⁺ is the overlap graph; **Prop 12.1** injectivity (`s ≠ t, s,t < R ⟹ T s ≠ T t`, via the
  exact-`r`-`A`-vertices counting argument; padded entries never enter, since the scan of a
  genuine `t` only sees genuine `s < t`).
- **Coupling lemma (Lemma 14.1, the heart).** For a fixed good tree `τ`, define the **τ-check
  structurally**: vertex `v` at depth `d` is tested on table entries
  `(j, treeProfile τ j (d+1))` for `j ∈ vbl (label v)` — exactly the notes'
  `(X, |S_X(u)|)` indices, no sequential process. Then: (a) **entry injectivity** for good
  trees — same depth: disjoint `vbl`; different depths `d(v') > d(v)`: `v'` is counted in the
  shallower profile but not its own, giving the strict inequality
  `profile j (d(v)+1) ≥ profile j (d(v')) + 1`; (b) **occurrence ⟹ check passes**: for
  `T(ω,t) = τ`, the resamplings of `X` before `q(u)` biject with `S_X(u)` (forward: earlier
  overlapping entries are inserted below the max-depth eligible vertex, hence deeper; backward:
  `q(v) < q(u)` since the reverse contradiction would flip depths), so MT's value of `X` just
  before resampling `u` is precisely the entry the check reads — and the algorithm only
  resamples occurring events, so every check succeeds; (c) **probability**: injective fresh
  coordinates of a product measure factor, so `μN {check τ} = treeProd τ := ∏_{u} μπ (A[u])`
  (disjoint-coordinate independence — compile-tested by survey A — plus cylinder marginals).
  Assembly: `μN {∃ t < R, T = τ} ≤ μN {check τ} = treeProd τ`.
- **Galton–Watson block.** `gwWeight τ` is the genuine branching probability (accepted-child
  products × rejected `(1−x)` products — no division); the telescope
  `gwWeight τ = ((1−x i)/x i) · ∏_u x'([u])` for `x i ≠ 0` by tree induction (child→non-root
  reindexing + `Γ⁺ = children ⊔ rejected` cancellation); the sum bound
  `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ 1` by height induction with the multinomial factorization
  `∏_B ((1−x B) + x B · S_h(B))`.
- **Final chain (F23):** counting identity (injectivity turns `countLog` into a sum of tree
  indicators) → coupling → `hLLL` per node → `by_cases x i = 0` (root factor kills everything,
  no GW) vs `x i > 0` (telescope + sum bound → `ofReal (x i/(1−x i)) · 1`).

### Proof decomposition (27 items; critical path ★ ≈ 2370 lines)

| # | Anchor | Declaration | Diff. | Lines |
|---|---|---|---|---|
| A1 | notes §2 | `overlapGraph`, `mem_gammaPlus_of_overlap` | Easy | 40 |
| A2 | notes §1 | `DeterminedBy` | Easy | 15 |
| A3 | notes §7 | `ΩN`, `μN` + probability instance | Easy | 30 |
| B4 | notes §4 | `State`/`assign`/`Avail`/`step` (availability-certificate-carrying) | Easy–Med | 90 |
| B5 | notes §4 | `run`, `count`, `run_count_le` ★ | Medium | 80 |
| B6 | notes §4 | `NoViolation`, `R`, `R_le` | Easy–Med | 60 |
| B7 | notes §6 | `log` (Option-valued) + `run_step_of_lt_R` ★ | Medium | 60 |
| B8 | meas. | `measurable_run`/`measurableSet_R_eq` | Medium | 100 |
| C9 | notes §8 | `WitnessTree` + path API, `Proper`, `IsGood`, `instDecidableEq` | Medium | 200 |
| C10 | notes §9 | `attachBelow`/`attachInFirst` + **fold spec lemma** ★ | **Hard** | 200 |
| C11 | notes §9 | `treeAt`, `forgetTime`, `T` ★ | Easy | 50 |
| C12 | Prop 10.1 | `treeAt_proper` ★ | Medium | 80 |
| C13 | Lemma 11.1/Cor 11.2 | `depth_gt_of_earlier_overlap`, `vbl_disjoint_of_same_depth` ★ | Med–Hard | 150 |
| C14 | Prop 12.1 | `treeAt_injective` ★ | Medium | 100 |
| C15 | — | `treeAt_isGood`, `treeAt_size_le` | Easy–Med | 60 |
| D16 | notes §14 | `treeProfile`, `check` + profile inequality | Medium | 120 |
| D17 | (14.2) | `check_probability` ★ | **Hard** | 200 |
| D18 | Lemma 14.1 | `occurrence_implies_check`, `coupling` ★ | **Hard** | 250 |
| E19 | Lemma 17.1 | `x'`, `gwWeight`, `gwWeight_telescope` ★ | Medium | 150 |
| E20 | — | Fintype `𝒯_i(N)` (proper trees, ≤ N vertices) | Medium | 120 |
| E21 | §16–18 | `gwWeight_sum_le_one` ★ | Med–Hard | 150 |
| F22 | §13 | `countLog_eq_sum_tree_indicators` ★ | Medium | 80 |
| F23 | Thm 5.1 | **`moserTardos_bound`** ★ (`by_cases x i = 0`) | **Hard** | 200 |
| F24 | (5.2) | `moserTardos_total` ★ | Easy | 40 |
| F25 | §19 | `moserTardos_tail` ★ (multiplicative form) | Easy–Med | 60 |
| F26 | §19 | `moserTardos_exists` ★ (constructive LLL) | Medium | 80 |
| F27 | §20 | `moserTardos_symmetric` (follow-up PR) | Medium | 150 |

**Core estimate ≈ 2400–2900 lines + ~150 symmetric.** The three Hard points are **C10** (the
fold spec lemma all structural lemmas consume), **D17** (check-probability factorization), and
**D18** (the coupling), plus **F23** (assembly with the `x i = 0` split).

## Relevant Existing Modules

### Mathlib (all present in v4.32.0 — verified in survey A)

| Module | Provides |
|---|---|
| `Probability.Independence.Basic` | `iIndepFun_pi` (:893), `iIndepFun.indepFun_finset₀` (:803), `IndepFun.comp` (:756), `Indep.indepSet_of_measurableSet` (:595), `IndepSet.measure_inter_eq_mul` (:584), `indepFun_iff_measure_inter_preimage_eq_mul` (:644) — the disjoint-coordinate independence engine, **compile-tested** (~10 lines per claim) |
| `Probability.ProductMeasure` | `Measure.infinitePi` (:356) — **exists** (Ionescu–Tulcea); not needed for the core, enables the infinite a.s. follow-up and trivializes the cylinder identity |
| `MeasureTheory.Constructions.Pi` | `Measure.pi_pi_finset` (:315), coordinatewise-map law (:390) — cylinder marginals |
| `MeasureTheory.Integral.Lebesgue.*` | `lintegral_indicator`, `lintegral_finsetSum'` (**renamed** from `lintegral_finset_sum`, Add.lean:341) |
| `Data.Finset.*` | `Finset.min'` (pick instantiation), `Finset.sum_boole` (Ring/Finset.lean:44), `prod_sum` (multinomial factorization) |
| `Data.Fintype.OfMap` | `Fintype.ofInjective` (:67) — the `𝒯_i(N)` finiteness encoding |
| `Data.ENNReal.Inv/Real` | `ofReal_div_of_pos` (:952, **no unconditional `ofReal_div`**), `ofReal_div_le` (:946), `ofReal_natCast` (Real.lean:311) |
| `Analysis.SpecialFunctions.Exp` | `Real.add_one_le_exp` (:211) — symmetric form `(1+1/d)^d ≤ e` |
| `MeasureTheory.Measure.Restrict` | `exists_mem_of_measure_ne_zero_of_ae` (:414) — constructive existence step |
| — | **No `Fintype (List α)` / `Fintype (Multiset α)`** (only `fintypeNodupList`) — tree finiteness needs the encoding; `deriving DecidableEq` **fails** for the List-children inductive (manual instance) |

### StatsMLlib

| Module | Use |
|---|---|
| `Probability.LovaszLocal` | Style + ENNReal-first conventions; `ofReal_one_sub` reusable; **cross-file bridge** (follow-up): the overlap graph satisfies `IsDependencyGraph`, so `moserTardos_exists` and `lovaszLocalLemma` become two proofs of the same variable-model statement (survey D: ~30–80 lines, HIGH feasibility — the MT `hLLL` must be stated with the overlap graph's `neighborFinset` so it matches definitionally) |
| `Probability.Independence.FinsetPi` | Optional alternative determinism vocabulary; not required by the ∃-form `DeterminedBy` |

### External formalizations (survey C)

- **Isabelle AFP** `Lovasz_Local` (Edmonds 2023, CPP 2024): classical LLL only, **no
  Moser–Tardos** (verified three ways, incl. grepping afp-devel sources). Reusable ideas:
  `mutual_indep_events` predicate shape, the `S ≠ ∅` conditioning hygiene.
- **Lean:** `EdouardBonnet/moser-tardos` — **lax-41 in the Lax Lean Archive**, sorry-free,
  ~2,100 proof lines, formalizes exactly MT Thm 1.2 + HSS Thm 2.2 on an **infinite resampling
  table** (`Measure.infinitePi`), mathlib c5ea0035. Design lessons adopted here: three-layer
  tree split (algebraic weight calculus / timed construction / proper-tree finsets),
  `cellIndex`-style fresh-sample coupling, label-count injectivity. **Not in mathlib.** Our
  differentiation and the coordination question are in the Motivation.
- **Other provers:** nothing completed (Coq/Agda/HOL Light/Mizar/PVS all empty); near-misses:
  Krčál's 2010 DIMAP approach sketch, Lê's 2014 bounded-arithmetic thesis (Moser's Fix-It).

## Missing Infrastructure (Must Be Created)

All declarations live in the proposed folder (survey B §5 items A1–F27). The critical new
pieces: the **variable model** (overlap graph, `DeterminedBy`, `ΩN`/`μN`); the **truncated
algorithm** (certificate-carrying `step`, `run_count_le`, padded `Option` log, `R`);
the **witness-tree layer** (`WitnessTree`, path API, `Proper`/`IsGood`, the C10 fold spec,
structural lemmas, injectivity); the **coupling** (`treeProfile`/`check`,
`check_probability` via disjoint-coordinate independence, `occurrence_implies_check`);
the **Galton–Watson algebra** (`gwWeight` + telescope, `𝒯_i(N)` Fintype, sum bound); and the
**four public theorems**. ENNReal glue needed: `ofReal_div_of_pos` applications (already in
mathlib); no new ENNReal lemmas expected beyond `LovaszLocal.ofReal_one_sub`.

## Code Conventions

Survey D §1 (unchanged from the LLL cycle): Apache-2.0 header, `/-!` docstring with
`## Main definitions` / `## Main results` / `## References`, `namespace MoserTardos`,
ENNReal-first statements, strict linters (no sorry/axiom/`#`-commands, `·` bullets, 100-char
lines, `autoImplicit := false`, warning-free builds), `(μ := μ)` discipline (the LLL file has
20 occurrences; expect more here on `Ω_N`), submodule commits `feat(MT.NN): attempt N — …`.

## API Questions for Maintainers

1. **Finite-truncation formulation as the public shape** — acceptable, given lax-41 already has
   the infinite-table version? Recommend yes: the truncated form is what produces the uniform
   bound, the honest tail bound, and the constructive-LLL corollary; the infinite a.s. form is
   a follow-up (now feasible via `Measure.infinitePi`).
2. **Folder vs flat file** (≈ 2700 core lines): recommend the 6-file folder above (surveys
   B+D); the flat-file trigger (~1500 lines) is blown.
3. **`DeterminedBy` ∃-hypothesis vs data interface** (`eval : ∀ i, (Π j : vbl i, Ω j) → Prop` +
   `hEval`): recommend the ∃-form + `Classical.choose`; the data form is a mechanical wrapper —
   include both?
4. **Log interface:** `Ω_N → ℕ → Option ι` (recommended) vs `ℕ → ι` with a `[Nonempty ι]`
   dummy — the Option form keeps every tree lemma junk-free.
5. **`hLLL` shape:** bundled `μπ (A i) ≤ ofReal (x i * ∏ j ∈ Γ vbl i, (1 - x j))`
   (recommended; matches `LovaszLocal.lean` and keeps the future `IsDependencyGraph` bridge
   definitional).
6. **Tie-break:** fix one deterministic tie-break in the construction and document its
   arbitrariness (recommended), vs. a tie-break-parametric refactor (not worth the cost).
7. **Tail-bound statement:** `μN {R = N}` (recommended, matches the notes) vs `μN {log ω N = none}`.
8. **Coordination with lax-41 / Édouard Bonnet:** reach out before or after landing? Options:
   proceed independently (different formulation + StatsMLlib integration), or align APIs first.
   Recommend proceeding, with a PR description that credits lax-41 and invites upstreaming.

## Future Extensions (Out of Scope for Initial PR)

| Extension | Difficulty | Notes |
|---|---|---|
| Infinite-table a.s. formulation (`E[N_i] ≤ x_i/(1−x_i)` on `infinitePi`) | Medium | `Measure.infinitePi` + monotone convergence over the truncations; precedent: lax-41 |
| ε–N divided tail form (`N ≠ 0`) | Easy | Follows from `moserTardos_tail` |
| Cross-file bridge: overlap graph satisfies `LovaszLocal.IsDependencyGraph` | Easy–Med | ~30–80 lines; makes `moserTardos_exists` a constructive companion of `lovaszLocalLemma` |
| k-SAT application | Medium | After the variable model: `μ (A C) = 2^(-k)` via `Measure.pi_pi`; `d < 2^k/e − 1`-style hypothesis |
| Hypergraph coloring | Medium | `μ (A e) = q^(1−k)`, degree counting `d ≤ k(Δ−1)` |
| Parallel Moser–Tardos (Thm 1.3) | Hard | Rounds of a maximal independent set; defer |
| Lopsided LLL (Thm 6.1) | Hard | Defer (as in the LLL proposal) |

PR split recommendation (survey B §6): PR 1 = core folder A1–F26; PR 2 = symmetric form +
ε–N tail; PR 3+ = applications. (Fallback if PR 1 is judged too large: 1a = framework +
algorithm + witness trees, 1b = coupling + GW + main theorem — but 1a lands no named theorem.)

## References

- R. A. Moser, G. Tardos, "A constructive proof of the general Lovász Local Lemma",
  J. ACM 57(2), 11:1–11:15, 2010. DOI 10.1145/1667053.1667060, arXiv:0903.0544 (Thm 1.2 =
  target; Thm 1.3 parallel and Thm 6.1 lopsided out of scope).
- N. Alon, J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016, ch. 5, esp. §5.7
  "The Algorithmic Aspect".
- C. Edmonds, L. C. Paulson, "Formal Probabilistic Methods for Combinatorial Structures using
  the Lovász Local Lemma", CPP 2024, DOI 10.1145/3636501.3636946, arXiv:2310.00513 (classical
  LLL only).
- É. Bonnet, "moser-tardos", Lean 4 repository, registered as lax-41 in the Lax Lean Archive
  (laxarchive.org), 2026 (MT Thm 1.2 + HSS Thm 2.2, infinite-table formulation).
- Yitong Yin, *Basics of Randomized Algorithms* (LLL lecture slides), 计算理论之美 summer
  school, 2025-06-30 (`ref/尹一通-lll.pdf`).
- R. A. Moser, "A constructive proof of the Lovász Local Lemma", STOC 2009; and T. Tao,
  "Moser's entropy compression argument" (blog, 2009-08-05) — for Moser's Fix-It (out of
  scope).
- Reference proof notes: `ref/moser_tardos_algorithmic_lll_notes.md` (the GPT-written detailed
  proof this proposal follows; Thm 5.1 = target statement).

---

## Survey Reports

Detailed research reports supporting this proposal are in the `survey/` directory:

| File | Content |
|---|---|
| [PLAN.md](survey/PLAN.md) | Survey plan (axes, constraints, architectural seed) |
| [CHECKLIST.md](survey/CHECKLIST.md) | The user's proposal checklist + per-agent checklists |
| [A_mathlib_inventory.md](survey/A_mathlib_inventory.md) | mathlib v4.32.0 inventory: `Measure.infinitePi` exists, disjoint-coordinate independence + tree finiteness compile-tested, name surprises (`lintegral_finsetSum'`, `ofReal_div_of_pos`, no `Fintype (List α)`) |
| [B_proof_strategy.md](survey/B_proof_strategy.md) | Pinned statements (with the two load-bearing amendments), full proof audit, 27-item decomposition, risks |
| [C_external_formalizations.md](survey/C_external_formalizations.md) | AFP has no MT; lax-41 (É. Bonnet) is the first MT formalization; literature anchors |
| [D_repo_conventions.md](survey/D_repo_conventions.md) | Conventions verified current, `LovaszLocal` API inventory, placement, FILE_TREE/README edit list, git choreography |
