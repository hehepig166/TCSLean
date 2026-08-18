# Blueprint: Lovász Local Lemma (Asymmetric Form)

## Format

Each item has this structure. See the end of this section for the log column spec.

- **meta**
    - kind: <def|lemma|theorem>
    - priority: <1|2|3>          (1 = nice-to-have, 2 = important, 3 = critical path)
    - status: <pending|working|done>
    - attempts: <current> / <bucket>    (bucket default = 15)
    - file: `<Path/To/File.lean>`
- **informal**
    - statement: |
        <LaTeX or plain-English statement. For defs, describe what it defines.>
    - proof: |
        <Proof sketch. Bullet points or paragraph. Empty for defs.>
- **prep**
    - `<Lean.Declaration.Name>` — <brief description>
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|

Log columns:
- `Date`, `Att`, `Status`(initial=`working`), `Goal`, `Tmp` — written by Survey at attempt start.
- `Proof Feedback` — filled by Review from Proof subagent's report.
- `Review Feedback` — filled by Review (verification, integration decision, next-attempt guidance).
- `Status`(final) — updated by Review: `done` | `pending` | `stuck`.
- **Newest entries first.**

### Numbering

Hierarchical: `## 10. Group`, `### 10.1. item`, `#### 10.1.1. sub-item`. Gaps allowed for insertion.

Group ranges: `10`--`19` Definitions, `20`--`39` Basic properties, `40`--`59` Core lemmas,
`60`--`79` Main theorem, `80`--`99` Corollaries.

### Status Lifecycle

```
pending ---> working ---> done
  ^           |
  +-----------+  (retry)
```

`attempts = bucket / bucket` with status != `done` --> **blocked**, needs human intervention.

## Overview

Formalize the **asymmetric Lovász Local Lemma** (gpt-notes Theorem 4.1) over an arbitrary finite
index type `ι` with a `SimpleGraph` dependency structure, following survey B's *order-free peeling
reorganization* of the classical conditional-probability proof. This blueprint covers **PR 1 only**:
the asymmetric core (survey B steps 1--13, ~600--750 lines). **PR 2** (items 80.10/80.15/80.20,
added 2026-08-15): the symmetric forms — sharp `p ≤ d^d/(d+1)^(d+1)`, classical `ep(d+1) ≤ 1`,
and the `4pd` criterion (survey B §4.1--4.2). Out of scope (later PRs): the variable model,
applications (k-SAT, hypergraph coloring), lopsided LLL, Moser--Tardos.

**Setup.** `(Ω, μ)` a probability space (`[MeasurableSpace Ω]`, `[IsProbabilityMeasure μ]`), `ι`
finite (`[Fintype ι] [DecidableEq ι]`), bad events `A : ι → Set Ω` measurable, dependency graph
`G : SimpleGraph ι` (loopless by definition), weights `x : ι → ℝ` with `0 ≤ x i` and `x i < 1`.
Write $B_S := \bigcap_{j\in S} \overline{A_j}$ (`bset A S`) and $\Gamma(i) := G.\mathrm{neighborFinset}\,i$.

**Main theorem** (`lovaszLocalLemma`, ENNReal form): if
$\mu(A_i) \le \mathrm{ofReal}\bigl(x_i \cdot \prod_{j \in \Gamma(i)} (1 - x_j)\bigr)$ for all $i$,
then
$$\mathrm{ofReal}\Bigl(\prod_i (1 - x_i)\Bigr) \le \mu\Bigl(\bigcap_i \overline{A_i}\Bigr),$$
with `lovaszLocalLemma_pos : 0 < μ (⋂ i, (A i)ᶜ)` (the existence statement),
`lovaszLocalLemma_exists : ∃ ω, ∀ i, ω ∉ A i` (the witness corollary), and
`lovaszLocalLemma_probReal : ∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)` (the ℝ corollary).

**Proof strategy — no conditionals, no division, no order on `ι`.** Prove by
`Finset.strongInductionOn` (on `⊂`, hence on `card`) the simultaneous invariant
$$(P1_S)\quad \mathrm{ofReal}\Bigl(\prod_{j \in S} (1-x_j)\Bigr) \le \mu(B_S), \qquad
(P2_{i,S})\quad i \notin S \implies \mu(A_i \cap B_S) \le \mathrm{ofReal}(x_i)\cdot \mu(B_S).$$
The P1 step peels one element `r ∈ S` off via the disjoint splitting
$\mu(B_S) = \mu(B_{S\setminus\{r\}}) - \mu(A_r \cap B_{S\setminus\{r\}})$ plus P2-IH at
$(r, S\setminus\{r\})$. The P2 step splits `S` into neighbors `N := S.filter (G.Adj i ·)` and
non-neighbors `M := S.filter (¬ G.Adj i ·)`; if `N ≠ ∅`, the five-step chain of survey B §1.3 ends
with the product-chain bound `ofReal (∏_{j∈N} (1-x_j)) · μ(B_M) ≤ μ(B_{N∪M})` (item 40.15), the
order-free replacement for the classical chain rule, proved by nested `Finset.induction` on `N`
with one P2-IH peel per element. (P1) at `S = univ` assembles the theorem. All arithmetic is
ENNReal-multiplicative; the only subtraction glue is `ofReal_one_sub` (item 40.1) plus the
finiteness threads `μ s ≠ ∞` from `[IsProbabilityMeasure μ]` (survey B risk 1).

**File layout.** All declarations go into the new flat file
`StatsMLlib/Probability/LovaszLocal.lean` (module `StatsMLlib.Probability.LovaszLocal`), the
`SmallBall.lean`-style precedent for standalone named-theorem packages (survey D §4). Recommended
namespace: `namespace LovaszLocal` (SmallBall pattern), with
`open MeasureTheory ProbabilityTheory` and `open scoped BigOperators ENNReal`. Mathlib-style header
and `/-!` docstring with `## Main definitions` / `## Main results` / `## References`
(`[erdosLovasz1975]`, `[alonSpencer2016]`, `[edmondsPaulson2024]`). Imports:
`Mathlib.Probability.Independence.Basic`, `Mathlib.Combinatorics.SimpleGraph.Finite`,
`Mathlib.MeasureTheory.Measure.Typeclasses.Probability`, `Mathlib.Data.ENNReal.Real` (all verified
in mathlib v4.32.0).

**Pinned hypotheses** (proposal API questions, decided): weak `IsDependencyGraph` as the public
definition (item 10.5; the strong-form equivalence is optional item 90.10); flat
`x : ι → ℝ` with `hx₀`/`hx₁`; bundled `hLLL : μ (A i) ≤ ENNReal.ofReal (x i * ∏ …)`;
`[DecidableRel G.Adj]` as a theorem hypothesis (for `neighborFinset`).

**Item count:** 21 items (18 PR-1 + 3 PR-2 symmetric forms in group 80). Group 90 is optional
(priority 1) and may be dropped from PR 1 without losing the theorem.

## Items

---
## 10. Definitions

### 10.1. bset

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        For a family of events $A : \iota \to \mathrm{Set}\,\Omega$ and a finite index set
        $S \subseteq \iota$, define the event "none of the bad events indexed by $S$ occurs":
        $$B_S(A) := \bigcap_{j \in S} \overline{A_j},$$
        with the convention $B_\emptyset = \Omega$ (empty intersection). In Lean, the `Finset`
        binder form:
        ```lean
        def bset (A : ι → Set Ω) (S : Finset ι) : Set Ω := ⋂ j ∈ S, (A j)ᶜ
        ```
        (Survey-verified 2026-08-15: the binder `⋂ j ∈ S, …` elaborates via the plain
        `Set.iInter` notation3 to the **nested form**
        `⋂ j, ⋂ (_ : j ∈ S), (A j)ᶜ` = `Set.iInter (fun j ↦ Set.iInter (fun _ : j ∈ S ↦ (A j)ᶜ))`,
        NOT to the `Finset.inf` fold. The fold form `S.inf (fun j ↦ (A j)ᶜ)` is connected
        propositionally by the `@[simp]` lemma `Finset.inf_set_eq_iInter`.)
    - proof: |
        Definition, no proof.
- **prep**
    - `Finset.inf_set_eq_iInter` — `s.inf f = ⋂ x ∈ s, f x` (`Mathlib/Data/Finset/Lattice/Fold.lean:308`, `@[simp]`) — simp bridge from the `Finset.inf` fold form to the `⋂ x ∈ s, …` notation form (the notation does NOT elaborate via this lemma).
    - `Finset.inf` — `s.inf f : Set Ω` (fold of `⊓` with `⊤`; `Mathlib/Data/Finset/Lattice/Fold.lean:44`, generated via `@[to_dual]` from `Finset.sup`) — transitively available through the four planned imports (Survey-verified 2026-08-15; no extra import needed). Note: `Mathlib.Data.Finset.Lattice` is NOT a module in mathlib v4.32.0 (directory only; leaf modules are `…Finset.Lattice.Basic` / `.Fold`).
    - `Set.mem_iInter₂` — `(x ∈ ⋂ i j, s i j) ↔ ∀ i j, x ∈ s i j` (`Mathlib/Data/Set/Lattice.lean:61`) — exact membership form of the nested `⋂ j, ⋂ (_ : j ∈ S), (A j)ᶜ` elaboration; `Set.iInter₂` itself is notation only, no declaration.
    - `Set.mem_iInter` — `(x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i` (`Mathlib/Data/Set/Lattice.lean:246`) — membership in the outer intersection of the nested form.
    - `Set.compl` — complement notation `(A j)ᶜ`.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Create the new file skeleton (header, docstring, four planned imports, namespace LovaszLocal, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators ENNReal`) and the definition `bset`; the Finset-binder elaboration of `⋂ j ∈ S, (A j)ᶜ` is Survey-verified — compiles with the four planned imports alone, elaborated as nested `Set.iInter` (NOT `Finset.inf`) | Def item — no proof needed; Setup wrote the body directly. Full skeleton delivered: mathlib-style header (Copyright 2026 Zhu Zekai), the four planned imports, `# Lovász Local Lemma` docstring with `## Main definitions` / `## Main results` / `## References` ([erdosLovasz1975], [alonSpencer2016], [edmondsPaulson2024]), `namespace LovaszLocal`, the two opens, explicit variable block, and `def bset (A : ι → Set Ω) (S : Finset ι) : Set Ω := ⋂ j ∈ S, (A j)ᶜ`. Elaboration matches the Survey-verified nested `Set.iInter` form. | Re-verified independently: `lake env lean` exits 0 with empty output; LSP diagnostics empty (no errors/warnings/infos); no `sorry`/`axiom`/`admit`/`native_decide`; no lines over 100 chars; 46 lines. Content matches item 10.1 and survey D §2 conventions (header/docstring/namespace/imports all per blueprint). Integrated as `StatsMLlib/Probability/LovaszLocal.lean`; tmp file deleted. `lake build StatsMLlib.Probability.LovaszLocal` succeeds with weak linters active (no warnings). Next: item 10.5 (`IsDependencyGraph`). | `tmp_bset.lean` |

### 10.5. IsDependencyGraph

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        `G : SimpleGraph ι` is a **dependency graph** for the bad events `A : ι → Set Ω` if, for
        every index `i` and every finite set `S` of indices with `i ∉ S` whose members are all
        non-neighbors of `i` in `G`, the event `A i` is independent of `bset A S`:
        $$i \notin S,\ \ \forall j \in S,\ \neg\, G.\mathrm{Adj}\, i\, j
          \ \Longrightarrow\ A_i \perp\!\!\!\perp B_S(A).$$
        In Lean (the **weak** form — exactly the fragment of the classical definition 3.1 that the
        proof consumes, see survey B §1.2(b)):
        ```lean
        def IsDependencyGraph (G : SimpleGraph ι) (A : ι → Set Ω) : Prop :=
          ∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) → IndepSet (A i) (bset A S) μ
        ```
        The guard `i ∉ S` is required for satisfiability: without it, `S = {i}` would demand
        `IndepSet (A i) ((A i)ᶜ)`, forcing `μ (A i) ∈ {0,1}`.
    - proof: |
        Definition, no proof.
- **prep**
    - `ProbabilityTheory.IndepSet` — independence of two events, `Mathlib/Probability/Independence/Basic.lean:129`. Survey-verified 2026-08-15 signature (quote): `def IndepSet {_mΩ : MeasurableSpace Ω} (s t : Set Ω) (μ : Measure Ω := by volume_tac) : Prop := Kernel.IndepSet s t (Kernel.const Unit μ) (Measure.dirac () : Measure Unit)`. The measure IS an optional `autoParam` argument defaulting to `volume_tac`, and `volume_tac` is literally `exact MeasureTheory.MeasureSpace.volume` (`MeasureSpaceDef.lean:379`) — it does NOT pick up the local `{μ : Measure Ω}` variable. Since the file has only `[IsProbabilityMeasure μ]` (no `[MeasureSpace Ω]`), the definition MUST pass `μ` explicitly: `IndepSet (A i) (bset A S) μ`. No extra typeclass beyond the variable block: only the implicit `{_mΩ : MeasurableSpace Ω}` (inferred from `[MeasurableSpace Ω]`); all `Kernel.const Unit μ` instances are internal to the already-compiled def. Note: `IndepSet` lives directly in namespace `ProbabilityTheory` (the `Definitions` block in Basic.lean is a `section`, not a nested namespace), so the main file's `open ProbabilityTheory` resolves it.
    - `bset` (item 10.1) — the event $B_S$ that `A i` must be independent of. Lives in namespace `LovaszLocal` of the main file, so the tmp file MUST `import StatsMLlib.Probability.LovaszLocal` (instead of re-importing the four mathlib files) and re-open `namespace LovaszLocal` with the same variable block and opens — variables/`open`s are file-scoped and are NOT carried over by `import`.
    - `SimpleGraph` / `SimpleGraph.Adj` — `Mathlib.Combinatorics.SimpleGraph.Basic:93`: `structure SimpleGraph (V : Type u) where Adj : V → V → Prop` (plus `symm`, `loopless`); the field name is `Adj`, so `G.Adj i j` and `¬ G.Adj i j` are valid projection notation. In scope from the main file's existing import `Mathlib.Combinatorics.SimpleGraph.Finite` via the public import chain `Finite → Maps → Dart → Basic` (Survey-verified 2026-08-15). Loopless by definition, so `Γ(i) ∪ {i}` collapses to `Γ(i)`.
    - Tmp file structure (for Setup): continuation of the main file — `import StatsMLlib.Probability.LovaszLocal`, `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators ENNReal`, `namespace LovaszLocal`, then re-declare the variable block `{Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]` before the def. Survey compile-tested 2026-08-15 via `lake env lean` (stdin): the exact body `∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) → IndepSet (A i) (bset A S) μ` elaborates to `LovaszLocal.IsDependencyGraph.{u_1, u_2} {Ω} {ι} [MeasurableSpace Ω] {μ : Measure Ω} (G : SimpleGraph ι) (A : ι → Set Ω) : Prop` with zero errors and no extra imports. Note: `[DecidableEq ι]` is needed for the `i ∉ S` finset membership; `[Fintype ι]` is not used by this def but stays for later items.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Write the definition `IsDependencyGraph` in namespace `LovaszLocal` (tmp continuation of the main file), with explicit `μ` argument, compilable against the existing `LovaszLocal.lean` | Def item — no proof needed; Setup wrote the body directly. Tmp continuation file (23 lines) imports the main module, re-opens the namespace/variable block, and defines `def IsDependencyGraph (G : SimpleGraph ι) (A : ι → Set Ω) : Prop := ∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) → IndepSet (A i) (bset A S) μ` with a docstring; `μ` passed explicitly per the prep note (the `autoParam` default would be `volume_tac`, not the local variable). | Re-verified independently: `lake env lean` on the tmp continuation exits 0 with empty output; LSP diagnostics empty; no `sorry`/`axiom`/`admit`/`native_decide`; no lines over 100 chars; no `#`-commands or `λ`; 23 lines (well under the 500-line limit). Body matches item 10.5's informal statement exactly, with explicit `μ`. Integrated into the main file (def + docstring only, after `def bset`); tmp deleted; main file re-verified via LSP diagnostics (empty) and `lake env lean` (exit 0). Next: item 20.1 (`bset_empty`). | `tmp_dep_graph.lean` |

---
## 20. Basic Properties

### 20.1. bset_empty, bset_insert

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        Structural identities for `bset` (one item, two `@[simp]` lemmas):
        - `bset_empty : bset A ∅ = Set.univ` — the empty intersection is the whole space.
        - `bset_insert : bset A (insert r S) = (A r)ᶜ ∩ bset A S` — inserting an index prepends
          one complement (holds unconditionally; the `r ∉ S` guard is not needed for the identity).
    - proof: |
        NOT the `Finset.inf` route: `bset` (item 10.1) elaborates to the **nested** `Set.iInter`
        form `⋂ j, ⋂ (_ : j ∈ S), (A j)ᶜ` (re-confirmed here by an `rfl` test against that form),
        so `simp [bset]` closes both goals directly on the `iInter` form — no `Finset.inf_*`
        lemma is involved. Survey compile-tested 2026-08-15 via `lake env lean` (stdin):
        - `bset_empty`: `by simp [bset]` (simp only `[bset, Finset.notMem_empty,
          Set.iInter_of_empty, Set.iInter_univ]`). NOT `rfl` — tested: the LHS `bset A ∅` is not
          definitionally equal to `Set.univ`.
        - `bset_insert`: `by simp [bset]` (simp only `[bset, Finset.mem_insert,
          Set.iInter_iInter_eq_or_left]` — the last lemma rewrites
          `⋂ j, ⋂ (_ : j = r ∨ j ∈ S), t` to `t r (Or.inl rfl) ∩ ⋂ j, ⋂ (_ : j ∈ S), t (Or.inr h)`,
          i.e. exactly `(A r)ᶜ ∩ bset A S`).
        (`ext ω; simp [bset]` and `aesop` also close both; plain `simp [bset]` is shortest.)
- **prep**
    - `bset` (item 10.1) — unfolds to the nested `iInter₂` elaboration
      `⋂ j, ⋂ (_ : j ∈ S), (A j)ᶜ`; the proofs are pure `simp [bset]` on this form.
    - `Finset.notMem_empty` — `a ∉ (∅ : Finset α)` (`Mathlib/Data/Finset/Empty.lean:107`,
      `@[simp, grind ←]`) — kills the `j ∈ ∅` binder in `bset_empty` (simp-discharged).
    - `Set.iInter_of_empty` — `[IsEmpty ι] : (⋂ i, s i) = univ`
      (`Mathlib/Data/Set/Lattice.lean:1074`, `@[simp]`) — empty inner intersection is `univ`.
    - `Set.iInter_univ` — `(⋂ _ : ι, (univ : Set α)) = univ`
      (`Mathlib/Data/Set/Lattice.lean:502`, `@[simp]`) — collapses the remaining outer
      intersection in `bset_empty`.
    - `Finset.mem_insert` — `a ∈ insert b s ↔ a = b ∨ a ∈ s`
      (`Mathlib/Data/Finset/Insert.lean:364`, `@[simp, grind =]`) — turns the insert-membership
      binder into a disjunction in `bset_insert`.
    - `Set.iInter_iInter_eq_or_left` — for `h : x = b ∨ p x`,
      `⋂ (x) (h), s x h = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h)`
      (`Mathlib/Data/Set/Lattice.lean:622`, `@[simp]`) — splits the disjunction binder in
      `bset_insert` into exactly `(A r)ᶜ ∩ bset A S`.
    - REMOVED (route disproven): `Finset.inf_empty` / `Finset.inf_insert` (to_dual of
      `Finset.sup_empty`/`sup_insert`, Fold.lean:58/62) and `Finset.inf_set_eq_iInter`
      (Fold.lean:308, exists but irrelevant) — `bset` never elaborates to a `Finset.inf` term,
      so none of these are consumed by the proof.
    - Note for Proof (warning-free form, compile-tested 2026-08-15): with the full variable
      block re-declared, `linter.unusedSectionVars` flags `[MeasurableSpace Ω] [Fintype ι]
      [DecidableEq ι]` on `bset_empty` and `[MeasurableSpace Ω] [Fintype ι]` on `bset_insert`
      (auto-included, consumed only via `bset`). The linter-suggested form
      `omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in @[simp] lemma bset_empty ...`
      (resp. `omit [MeasurableSpace Ω] [Fintype ι] in` for `bset_insert`) compiles warning-free
      (exit 0); resulting signatures are `{Ω ι} (A : ι → Set Ω) : bset A ∅ = Set.univ` and
      `{Ω ι} [DecidableEq ι] (A : ι → Set Ω) (r : ι) (S : Finset ι) : …`.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `bset_empty` (`bset A ∅ = Set.univ`) and `bset_insert` (`bset A (insert r S) = (A r)ᶜ ∩ bset A S`) as `@[simp]` lemmas — simp-based route on the iInter elaboration; Survey compile-tested 2026-08-15: both close by plain `simp [bset]` | Both lemmas proved by plain `simp [bset]` directly on the nested-iInter elaboration, warning-free. `@[simp]` applied via post-hoc `attribute [simp]` (the `omit … in @[simp] lemma` form does not parse in this Lean version), with the Survey's linter-suggested omit lines: `omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in` for `bset_empty`, `omit [MeasurableSpace Ω] [Fintype ι] in` for `bset_insert`; resulting signatures `{Ω ι} (A : ι → Set Ω) : bset A ∅ = Set.univ` and `{Ω ι} [DecidableEq ι] (A : ι → Set Ω) (r : ι) (S : Finset ι) : bset A (insert r S) = (A r)ᶜ ∩ bset A S`. | Re-verified independently: `lake env lean` on the tmp file exits 0 with empty output (warning-free); LSP diagnostics empty; no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 33 lines (well under the 500-line limit). Both statements match the informal spec exactly. Integrated into `LovaszLocal.lean` after `IsDependencyGraph` (docstrings, omit-lines, `attribute [simp]` lines); tmp file deleted; main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty. | `tmp_bset_basic.lean` |

### 20.5. bset_subset_bset_of_subset, bset_union

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        Monotonicity and union identities for `bset` (one item, two lemmas):
        - `bset_subset_bset_of_subset {S T} (h : S ⊆ T) : bset A T ⊆ bset A S` — enlarging the
          index set shrinks the event `bset` (antitone). Consumed by the P2 step's first
          inequality $\mu(A_i \cap B_S) \le \mu(A_i \cap B_M)$ for `M ⊆ S` (survey B identity (iv)).
        - `bset_union {S T} : bset A (S ∪ T) = bset A S ∩ bset A T` — the union split (survey B
          identity (iii)). **Statement changed by Survey 2026-08-15: the `h : Disjoint S T`
          hypothesis is DROPPED** — the identity holds unconditionally (the proof never uses
          disjointness: avoiding every bad event indexed in `S ∪ T` is the same as avoiding those
          in `S` and those in `T`). The unconditional form is better API and makes the `@[simp]`
          attribute safe (no side condition). Not strictly needed by the ENNReal core route, but
          cheap, structural, and expected API. No other blueprint item consumes `bset_union`
          with a disjointness hypothesis (checked), so the drop is safe blueprint-wide.
    - proof: |
        NOT the `Finset.inf` route (disproven for `bset`, as in 20.1 — `bset` elaborates to the
        nested `Set.iInter`, never `Finset.inf`). **Pitfall found by Survey 2026-08-15**
        (compile-tested): `Set.iInter` is defined as `iInf s` (via `sInf (Set.range s)`, cf. the
        `rfl` proof of `Set.mem_iInter`, SetNotation.lean:246), which does NOT whnf to a forall.
        Consequence: a hypothesis `hω : ω ∈ bset A T` cannot be applied directly (`hω j hj` fails
        to elaborate) and `intro`/`fun` over a goal `ω ∈ bset A S` mis-introduces a binder of type
        `Set Ω`. The fix, used by both proofs: normalize with `simp only [bset, Set.mem_iInter]`
        (at hypothesis and/or goal) FIRST, so the iInter membership becomes a plain forall, then
        do membership reasoning.
        - `bset_subset_bset_of_subset` (compile-tested, warning-free):
          ```
          intro ω hω
          simp only [bset, Set.mem_iInter] at hω ⊢
          intro j hj
          exact hω j (h hj)
          ```
        - `bset_union` (compile-tested, warning-free):
          ```
          ext ω
          simp only [bset, Set.mem_iInter, Set.mem_inter_iff]
          constructor <;> intro hω
          · constructor <;> intro j hj
            · exact hω j (Finset.mem_union.mpr (Or.inl hj))
            · exact hω j (Finset.mem_union.mpr (Or.inr hj))
          · intro j hj
            rcases Finset.mem_union.mp hj with hjS | hjT
            · exact hω.1 j hjS
            · exact hω.2 j hjT
          ```
          (The residual goal `(∀ j, j ∈ S ∨ j ∈ T → …) ↔ (∀ j, j ∈ S → …) ∧ (∀ j, j ∈ T → …)`
          is not closed by `simp` alone — forall does not distribute over `∨` — hence the manual
          `constructor`/`rcases`.)
    - attributes: |
        Survey recommendation (compile-tested 2026-08-15): `@[simp]` on `bset_union` only.
        Attachment form: either the two-line form `omit … in` followed by `@[simp] lemma`
        (compile-tested 2026-08-15, warning-free — the same-line `omit … in @[simp] lemma` form
        does not parse), or post-hoc `attribute [simp]` (as used in 20.1). Justification:
        unconditional identity, composes with `bset_insert`
        (`bset A (insert r (S ∪ T))` closes by plain `simp`), no loop (RHS contains no
        `bset A (_ ∪ _)`), and `by simp` closes `bset A (S ∪ T) = bset A S ∩ bset A T`.
        NO attribute on `bset_subset_bset_of_subset`: subset lemmas with side conditions are
        conventionally not simp (mathlib's `iInter_mono` is not simp), and simp would have to
        discharge `S ⊆ T` by decidability, which is unreliable.
- **prep**
    - `bset` (item 10.1) — unfolds to the nested `Set.iInter` elaboration
      `⋂ j, ⋂ (_ : j ∈ S), (A j)ᶜ`; must be normalized via `Set.mem_iInter` before applying
      membership hypotheses (see pitfall in informal.proof).
    - `Set.mem_iInter` — `x ∈ ⋂ i, s i ↔ ∀ i, x ∈ s i` (`Mathlib/Order/SetNotation.lean:246`,
      `@[simp, push]`, proof by `rfl`) — the workhorse; applied once per iInter nesting level.
    - `Set.mem_inter_iff` — `x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b` (`Mathlib/Data/Set/Basic.lean:701`,
      `@[simp, mfld_simps, grind =, push]`) — splits the `∩` on `bset_union`'s RHS.
    - `Finset.mem_union` — `a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t`
      (`Mathlib/Data/Finset/Lattice/Basic.lean:103`, `@[simp, grind =]`) — turns the
      `j ∈ S ∪ T` binder into a disjunction for the case split.
    - `Set.mem_iInter₂` — `x ∈ ⋂ i, ⋂ j, s i j ↔ ∀ i j, x ∈ s i j`
      (`Mathlib/Data/Set/Lattice.lean:61`) — alternative normalizer (`rw [bset, Set.mem_iInter₂]`
      also compile-tested); `simp` itself prefers two applications of `Set.mem_iInter`
      (an unused `mem_iInter₂` in a `simp only` list triggers `linter.unusedSimpArgs`).
    - REMOVED (route disproven, verified to exist but unused): `Set.subset_iInter₂`
      (`Mathlib/Data/Set/Lattice.lean:152`), `Finset.inf_mono`
      (`Mathlib/Data/Finset/Lattice/Fold.lean:151`, to_dual of `Finset.sup_mono`),
      `Finset.inf_union` (`Mathlib/Data/Finset/Lattice/Fold.lean:128`, to_dual of
      `Finset.sup_union`), `Finset.inf_set_eq_iInter` (`Mathlib/Data/Finset/Lattice/Fold.lean:308`,
      exists but irrelevant) — `bset` never elaborates to a `Finset.inf` term, so none of these
      are consumed by either proof.
    - Note for Proof (warning-free form, compile-tested 2026-08-15): with the full variable block
      re-declared, `linter.unusedSectionVars` flags `[MeasurableSpace Ω] [Fintype ι]
      [DecidableEq ι]` on `bset_subset_bset_of_subset` and `[MeasurableSpace Ω] [Fintype ι]` on
      `bset_union`. Linter-suggested omit lines (compiled warning-free, exit 0):
      `omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in` for `bset_subset_bset_of_subset`,
      `omit [MeasurableSpace Ω] [Fintype ι] in` for `bset_union`; resulting signatures
      `{Ω ι} (A : ι → Set Ω) {S T : Finset ι} (h : S ⊆ T) : bset A T ⊆ bset A S` and
      `{Ω ι} [DecidableEq ι] (A : ι → Set Ω) {S T : Finset ι} :
      bset A (S ∪ T) = bset A S ∩ bset A T`.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `bset_subset_bset_of_subset` and `bset_union` (stated UNCONDITIONALLY — `Disjoint S T` dropped, unused) via the membership-normalization route (`simp only [bset, Set.mem_iInter]` before applying iInter hypotheses, since `Set.iInter := iInf s` does not whnf); `@[simp]` on `bset_union` only | Both lemmas proved with the Survey's compile-tested proof skeletons: `bset_subset_bset_of_subset` by `intro ω hω; simp only [bset, Set.mem_iInter] at hω ⊢; intro j hj; exact hω j (h hj)`; `bset_union` by `ext` + `simp only [bset, Set.mem_iInter, Set.mem_inter_iff]` + constructor/rcases case split on `Finset.mem_union` (the forall-over-`∨` residual is not closed by `simp` alone). Warning-free with the Survey's omit lines: `omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in` for the subset lemma, `omit [MeasurableSpace Ω] [Fintype ι] in` for `bset_union`; signatures `{Ω ι} (A : ι → Set Ω) {S T : Finset ι} (h : S ⊆ T) : bset A T ⊆ bset A S` and `{Ω ι} [DecidableEq ι] (A : ι → Set Ω) {S T : Finset ι} : bset A (S ∪ T) = bset A S ∩ bset A T`. `@[simp]` attached post-hoc via `attribute [simp] bset_union`; no attribute on the subset lemma. | Re-verified independently: `lake env lean` on the tmp file exits 0 with empty output (warning-free); LSP diagnostics empty; no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 44 lines (well under the 500-line limit). Both statements match the informal spec exactly (antitone subset lemma; unconditional `bset_union` — no `Disjoint` hypothesis). Integrated into `LovaszLocal.lean` after `bset_insert` (docstrings, omit-lines, `attribute [simp] bset_union`); tmp file deleted; main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty. | `tmp_bset_mono.lean` |

### 20.10. bset_univ_eq_iInter

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        Bridge from the `Finset` binder to the unbounded indexed intersection:
        $$B_{\mathrm{univ}}(A) = \bigcap_{i : \iota} \overline{A_i},$$
        i.e. `bset A Finset.univ = ⋂ i, (A i)ᶜ`. This is the rewrite connecting (P1) at
        `S = univ` with the final theorem statement (survey B risk 2: keep `Set.iInter` only in
        the final statement, bridge here).
        **PITFALL (new, Survey-verified 2026-08-15):** there is NO `univ` notation in mathlib
        v4.32.0 (zero `"univ"` notation declarations in `.lake/packages/mathlib`). `univ` is the
        plain identifier `Finset.univ`; outside `namespace Finset` a bare `univ` is unresolved
        and, with `autoImplicit` (Lean default), silently elaborates as an implicit free variable
        — the statement becomes `∀ {univ : Finset ι}, bset A univ = ⋂ i, (A i)ᶜ` (an arbitrary
        finset!), after which the proof fails loudly. MUST write `Finset.univ` (the main file's
        opens do NOT bring the name into scope).
    - proof: |
        Extensionality plus membership: `simp [bset]` unfolds `bset` to the nested
        `⋂ j, ⋂ (_ : j ∈ Finset.univ), (A j)ᶜ`, normalizes both membership levels via
        `Set.mem_iInter` (automatic, it is `@[simp]`), and discharges the `j ∈ Finset.univ`
        binder with `Finset.mem_univ` (`@[simp, grind ←]`). Both directions of the residual iff
        close. Compile-tested 2026-08-15 (stdin, warning-free, exit 0):
        ```lean
        omit [MeasurableSpace Ω] [DecidableEq ι] in
        lemma bset_univ_eq_iInter (A : ι → Set Ω) : bset A Finset.univ = ⋂ i, (A i)ᶜ := by
          ext ω
          simp [bset]
        ```
        Fallback (also compile-tested, same omit lines): manual normalization
        ```lean
        ext ω
        simp only [bset, Set.mem_iInter]
        constructor <;> intro h
        · intro i; exact h i (Finset.mem_univ i)
        · intro i hi; exact h i
        ```
        (The original survey-A sketch with `bset A (univ : Finset ι)` fails exactly because that
        `univ` elaborates as a free variable — the fix is `Finset.univ` in the statement, not a
        different proof.)
    - attributes: |
        Survey recommendation (compile-tested 2026-08-15): `@[simp]`, attached post-hoc via
        `attribute [simp] bset_univ_eq_iInter` (matches the file's style for `bset_empty` /
        `bset_insert` / `bset_union`; alternatively the two-line `omit … in` + `@[simp] lemma`
        form — the same-line `omit … in @[simp] lemma` form does not parse, per 20.5).
        Justification: unconditional identity, no side conditions; RHS contains no `bset` (no
        loop — verified one-way: `by simp` does NOT rewrite `⋂ i, (A i)ᶜ` back into `bset`).
        **Direction at assembly (item 60.5): FORWARD.** `lovaszLocalLemma` is stated in terms of
        `⋂ i, (A i)ᶜ`, while (P1) at `S = univ` concludes `… ≤ μ (bset A Finset.univ)`, so the
        final theorem must rewrite `bset A Finset.univ → ⋂ i, (A i)ᶜ` — exactly `@[simp]`'s
        direction. Compile-tested assembly simulation closes the whole bridge in one `simpa`:
        ```lean
        example (A : ι → Set Ω) (x : ι → ℝ)
            (h : ENNReal.ofReal (∏ j ∈ (Finset.univ : Finset ι), (1 - x j)) ≤ μ (bset A Finset.univ)) :
            ENNReal.ofReal (∏ j, (1 - x j)) ≤ μ (⋂ i, (A i)ᶜ) := by
          simpa using h
        ```
        The LHS product needs NO lemma: `∏ j ∈ (Finset.univ : Finset ι), (1 - x j)` is
        definitionally `∏ j, (1 - x j)` (the `∈` binder is notation; verified by simp trace
        `eq_self`). Interactions with the other `@[simp]` lemmas (all compile-tested with the
        attribute present): `bset A (insert r Finset.univ)` rewrites via
        `Finset.insert_eq_of_mem` (`r ∈ univ` → `insert r univ = univ`, `@[simp]`,
        `Mathlib/Data/Finset/Insert.lean:397`) and then this bridge — no conflict, no loop;
        `bset_empty`, `bset_insert`, `bset_union` still close by plain `by simp`.
- **prep**
    - `Finset.mem_univ` — `x ∈ (univ : Finset α)` (`Mathlib/Data/Fintype/Defs.lean:96`,
      `@[simp, grind ←]`, proof by `Fintype.complete`) — the workhorse: `simp` discharges the
      `j ∈ Finset.univ` binder with it (needs `[Fintype ι]`).
    - `Set.mem_iInter` — `x ∈ ⋂ i, s i ↔ ∀ i, x ∈ s i` (`Mathlib/Order/SetNotation.lean:246`,
      `@[simp, push]`) — applied twice by `simp [bset]` to normalize the nested `Set.iInter`
      elaboration of `bset` (see pitfall in item 10.1).
    - `Finset.insert_eq_of_mem` — `(h : a ∈ s) : insert a s = s`
      (`Mathlib/Data/Finset/Insert.lean:397`, `@[simp]`) — not used by the proof itself, but the
      interaction that makes `bset A (insert r Finset.univ)` reduce to `bset A Finset.univ`
      under `simp` (no conflict with the attribute).
    - REMOVED (exists, unused by the working route): `Set.mem_iInter₂`
      (`Mathlib/Data/Set/Lattice.lean:61`) — `simp [bset]` prefers two applications of
      `Set.mem_iInter`; the original sketch's `simp [bset, Set.mem_iInter₂]` route is superseded.
    - `bset` (item 10.1) — unfolds to the nested `Set.iInter` elaboration
      `⋂ j, ⋂ (_ : j ∈ S), (A j)ᶜ`; membership must be normalized via `Set.mem_iInter`
      before reasoning.
    - Note for Proof (warning-free form, compile-tested 2026-08-15): with the full variable block
      re-declared, `linter.unusedSectionVars` flags `[MeasurableSpace Ω]` and `[DecidableEq ι]`.
      Linter-suggested omit line (compiled warning-free, exit 0):
      `omit [MeasurableSpace Ω] [DecidableEq ι] in`; resulting signature
      `{Ω ι} [Fintype ι] (A : ι → Set Ω) : bset A Finset.univ = ⋂ i, (A i)ᶜ`.
      (`{μ : Measure Ω}` and `[IsProbabilityMeasure μ]` are NOT auto-included — `μ` does not
      appear in the type; `[Fintype ι]` IS included and used, for `Finset.univ`.)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `bset_univ_eq_iInter` via `ext ω; simp [bset]` (the `Finset.mem_univ` route); statement MUST use `Finset.univ` — bare `univ` is not a notation in mathlib v4.32.0 and silently auto-binds as an implicit free variable; attach `@[simp]` post-hoc (forward direction is what item 60.5 needs) | Proved `bset_univ_eq_iInter (A : ι → Set Ω) : bset A Finset.univ = ⋂ i, (A i)ᶜ` by `ext ω; simp [bset]` — `simp` unfolds `bset` to the nested iInter, normalizes both membership levels via `Set.mem_iInter`, and discharges the `j ∈ Finset.univ` binder with `Finset.mem_univ`; both residual iff directions close. Statement uses `Finset.univ` (pitfall respected — no bare `univ`). `@[simp]` attached post-hoc via `attribute [simp] bset_univ_eq_iInter` (same-line `omit … in @[simp] lemma` form does not parse); omit-line `omit [MeasurableSpace Ω] [DecidableEq ι] in` per the Survey's linter note (resulting signature `{Ω ι} [Fintype ι] (A : ι → Set Ω) : bset A Finset.univ = ⋂ i, (A i)ᶜ`). Tmp file compiled warning-free. | Re-verified independently: `lake env lean` on the tmp exits 0 with empty output (warning-free); LSP diagnostics empty; no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 28 lines (well under the 500-line limit). Statement matches item 20.10's informal spec exactly (`Finset.univ`, not bare `univ`). Integrated into `LovaszLocal.lean` after `bset_union` (docstring, omit-line, proof, `attribute [simp] bset_univ_eq_iInter`); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds. Next: item 20.15 (`measurableSet_bset`). | `tmp_bset_univ.lean` |

### 20.15. measurableSet_bset

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        If every bad event is measurable, so is every `bset`:
        `measurableSet_bset (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
        MeasurableSet (bset A S)`.
        Needed to apply `indepSet_iff_measure_inter_eq_mul` (measurability of both sets) in the
        P2 step and, later, `cond_apply` in the conditional form.
    - proof: |
        RE-EVALUATED (Survey, attempt 1, all compile-tested via `lake env lean`): the feared
        binder mismatch does NOT materialize. `Finset.measurableSet_biInter`'s conclusion
        `MeasurableSet (⋂ b ∈ s, f b)` uses the same `⋂ b ∈ s, …` notation as `bset`'s body, so
        the nested-iInter elaborations are defeq. Working route (warning-free):
        ```lean
        omit [Fintype ι] [DecidableEq ι] in
        lemma measurableSet_bset (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι) :
            MeasurableSet (bset A S) := by
          simp only [bset]
          exact Finset.measurableSet_biInter S (fun i _ => (hA i).compl)
        ```
        `simp only [bset]` unfolds to the finset-indexed intersection; each `(A i)ᶜ` is
        measurable by `MeasurableSet.compl (hA i)`; `[DecidableEq ι]` is NOT needed. (~3 lines.)
        Fallback route (also compile-tested): `classical` +
        `induction S using Finset.induction` with `| empty => simp [bset]` and
        `| insert r S hr ih => rw [bset_insert]; exact (hA r).compl.inter ih`
        (`classical` supplies the `[DecidableEq ι]` that `Finset.induction` requires).
        Attribute decision: NO `@[simp]` — compile-tested: with `attribute [simp]
        measurableSet_bset`, `simp` makes NO progress even on the exact goal
        `MeasurableSet (bset A S)` with `hA` in the local context (`simp` made no progress);
        the `∀ i, MeasurableSet (A i)` side condition is never discharged, so the tag is inert
        (and no conflict with the other bset simp lemmas — they still close by `by simp`).
        Recommended instead (compile-tested, warning-free): post-hoc
        `attribute [measurability] measurableSet_bset` — then the `measurability` tactic closes
        the goal; idiomatic mathlib tag for measurability closure lemmas.
    - **prep**
        - `Finset.measurableSet_biInter` — `{f : β → Set α} (s : Finset β)
          (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b)`
          (`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:149`; NO `[DecidableEq β]` required;
          conclusion matches `bset`'s nested-iInter body defeq — same `⋂ b ∈ s, …` notation).
        - `MeasurableSet.compl` — `MeasurableSet s → MeasurableSet sᶜ`
          (`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:83`).
        - `bset` (item 10.1) — unfolds to the nested `Set.iInter` elaboration
          `⋂ j, ⋂ (_ : j ∈ S), (A j)ᶜ`; see pitfall in item 10.1.
        - Fallback-route deps (all verified, optional): `Finset.induction`
          (`Mathlib/Data/Finset/Insert.lean:480`, needs `[DecidableEq α]` → `classical`);
          `bset_empty` / `bset_insert` (item 20.1, both `@[simp]`); `MeasurableSet.univ`
          (`Defs.lean:94`); `MeasurableSet.inter` (`Defs.lean:169`, `@[simp, measurability]`).
        - REMOVED (exists, unused by both tested routes): `Finset.inf_set_eq_iInter`
          (`Mathlib/Data/Finset/Lattice/Fold.lean:308`) — the defeq match makes the
          `s.inf f` bridge unnecessary.
        - Note for Proof (warning-free form, compile-tested 2026-08-15): with the full variable
          block re-declared, `linter.unusedSectionVars` flags `[Fintype ι]` and
          `[DecidableEq ι]`; omit line (compiled warning-free, exit 0):
          `omit [Fintype ι] [DecidableEq ι] in`. `[MeasurableSpace Ω]` IS used (by
          `MeasurableSet`); `{μ : Measure Ω}` and `[IsProbabilityMeasure μ]` are not
          auto-included (don't appear in the type; same as item 20.10).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `measurableSet_bset` via `Finset.measurableSet_biInter` (re-evaluated: conclusion matches `bset`'s nested-iInter body defeq — no binder mismatch; induction fallback also tested); NO `@[simp]` (tested: simp no-progress even with `hA` in context); attach `[measurability]` post-hoc (tested: tactic closes); omit `[Fintype ι] [DecidableEq ι]` | Proved `measurableSet_bset (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι) : MeasurableSet (bset A S)` via the Survey-tested route: omit-line `omit [Fintype ι] [DecidableEq ι] in` (avoids `linter.unusedSectionVars`; `[MeasurableSpace Ω]` stays), then `simp only [bset]` unfolds `bset` to its finset-indexed intersection and `exact Finset.measurableSet_biInter S (fun i _ => (hA i).compl)` closes it (the defeq match with the `⋂ b ∈ s, …` conclusion holds as surveyed). No `@[simp]` (survey: tag is inert on the goal); `attribute [measurability] measurableSet_bset` attached post-hoc so `measurability` closes the goal. Tmp file compiled warning-free. | Re-verified independently: `lake env lean` on the tmp exits 0 with empty output (warning-free); LSP diagnostics empty; no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 27 lines (well under the 500-line limit). Final signature (via outline) is exactly `(A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (S : Finset ι) : MeasurableSet (bset A S)` — matches the informal spec; no `@[simp]`, `[measurability]` attached. Integrated into `LovaszLocal.lean` after `bset_univ_eq_iInter` (docstring, omit-line, proof, `attribute [measurability] measurableSet_bset`); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty. | `tmp_bset_measurable.lean` |

---
## 40. Core Lemmas

### 40.1. ofReal_one_sub

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        The single ENNReal glue gap found by survey A:
        `ofReal_one_sub {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal (1 - x) = 1 - ENNReal.ofReal x`.
        On the LLL range (`0 ≤ x ≤ 1`) both sides are the exact (non-truncated) subtraction; for
        general `x ≥ 0` the identity still holds as an ENNReal statement (both sides truncate at 0
        when `1 - x < 0`). This is the bridge used in the P1 peel:
        $(1 - \mathrm{ofReal}(x_r)) \cdot \mu = \mathrm{ofReal}(1 - x_r) \cdot \mu$.
    - proof: |
        Direct from `ENNReal.ofReal_sub` (`(p) {q} (hq : 0 ≤ q) : ofReal (p - q) = ofReal p - ofReal q`;
        `p` is EXPLICIT, so apply as `ofReal_sub 1 hx` with `q := x` inferred from `hx`), plus
        `ENNReal.ofReal_one` (`@[simp]`):
        `ofReal (1 - x) = ofReal 1 - ofReal x = 1 - ofReal x`. Surveyed compile-clean (exit 0,
        warning-free) as a one-liner: `simpa using (ENNReal.ofReal_sub 1 hx)` (equivalently
        `rw [ENNReal.ofReal_sub 1 hx]; simp`). NO `@[simp]` (surveyed 2026-08-15): with the
        attribute on, plain `simp` does NOT fire on `ofReal (1 - x)` even with `hx : 0 ≤ x` in
        the local context — simp's default discharger cannot prove the `0 ≤ x` side condition
        from local hypotheses (control: mathlib's own conditional `@[simp] ENNReal.ofReal_mul`
        also fails to fire from `hx`). Explicit `simp [ofReal_one_sub hx]`,
        `rw [ofReal_one_sub hx]`, and `rw [← ofReal_one_sub hx]` all work. The two use-sites are
        explicit applications anyway: 40.10 forward; the 60.1 P1 chain needs `← ofReal_one_sub`
        for `μ(B_T) - ofReal(x_r)·μ(B_T) = ofReal (1 - x_r)·μ(B_T)` and must keep the
        `ofReal (1 - x_r)` factor for the closing `← ENNReal.ofReal_mul`. No loop risk: nothing
        in ENNReal simp-rewrites `1 - ENNReal.ofReal x` (no `one_sub`-family simp lemma; simp is
        left-to-right only).
    - **prep**
        - `ENNReal.ofReal_sub` — `(p : ℝ) {q : ℝ} (hq : 0 ≤ q) : ofReal (p - q) = ofReal p - ofReal q` (`Mathlib/Data/ENNReal/Operations.lean:436`; signature verified, NOT `@[simp]` — the `@[simp]` at :435 belongs to `toReal_sub_of_le`).
        - `ENNReal.ofReal_one` — `ofReal 1 = 1` (`Mathlib/Data/ENNReal/Basic.lean:297`, `@[simp]`, verified).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `ofReal_one_sub` via `simpa using (ENNReal.ofReal_sub 1 hx)` (surveyed: `p` explicit, not `@[simp]`; one-liner compiles warning-free, exit 0). NO `@[simp]` on the result (surveyed: attribute inert — plain `simp` cannot discharge `0 ≤ x` from local `hx`, same as mathlib's conditional `ofReal_mul`; use-sites are explicit rw, 60.1 P1 needs `←`; no loop risk). No omit line (type mentions no section vars — compiled warning-free with the full variable block; fallback `omit [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] in` also verified) | Proved `ofReal_one_sub {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal (1 - x) = 1 - ENNReal.ofReal x` as the surveyed one-liner: `simpa using (ENNReal.ofReal_sub 1 hx)` (closes via `ofReal_one`). No `@[simp]` (surveyed: attribute inert — plain `simp` cannot discharge the `0 ≤ x` side condition from local `hx`; both use-sites are explicit rw applications). No omit line needed (type mentions no section vars). Tmp compiled warning-free (exit 0, empty output). | Re-verified independently: `lake env lean` on the tmp exits 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 22 lines (under the 500-line limit). Statement matches the informal spec exactly; no `@[simp]` (side-condition-inert decision upheld). Integrated into `LovaszLocal.lean` after `measurableSet_bset` and its `[measurability]` attribute, before `end LovaszLocal` (docstring + lemma + one-line proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty. | `tmp_ofReal_one_sub.lean` |

### 40.5. measure_bset_insert

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Peeling identity** (survey B identity (ii), replacing both chain-rule uses of the
        classical proof):
        `measure_bset_insert (hA : ∀ i, MeasurableSet (A i)) {S : Finset ι} {r : ι} :
        μ (bset A (insert r S)) = μ (bset A S) - μ (A r ∩ bset A S)`
        — the measure of $B_{\{r\} \cup S}$ equals the measure of $B_S$ minus the "bad part"
        $A_r \cap B_S$ (a disjoint splitting, valid since `μ` is a probability measure and all
        quantities are finite). The `hr : r ∉ S` hypothesis was DROPPED in survey (attempt 1,
        compile-verified): the splitting `bset A S = ((A r)ᶜ ∩ bset A S) ⊔ (A r ∩ bset A S)` is
        unconditional (as is `bset_insert`, 20.1), so `hr` is unused (linter warning "not
        explicitly referenced"; 20.5 Disjoint precedent); dropping it only strengthens the lemma
        for consumers. NOT `@[simp]`: the RHS is an ENNReal subtraction, not a normal form — a
        simp rewrite of `μ (bset A (insert r S))` into a difference would fire whenever `bset` is
        applied to an insert and pollute goals with truncated-subtraction terms; the main
        consumer (40.10) applies it FORWARD via `rw [measure_bset_insert A hA]` (compile-verified
        in the 40.10 survey: the goal RHS there is exactly this lemma's LHS; backward rw fails
        with "Did not find an occurrence");
        `bset_insert` already provides the structural simp rewrite for `insert`.
    - proof: |
        ```
        rw [bset_insert]
        rw [ENNReal.sub_eq_of_eq_add (measure_ne_top μ (A r ∩ bset A S))]
        rw [← measure_inter_add_sdiff (bset A S) (hA r)]
        rw [Set.inter_comm, Set.sdiff_eq, Set.inter_comm]
        ac_rfl
        ```
        (compile-verified warning-free via stdin, exit 0, with `omit [Fintype ι] in`.)
        - `bset_insert` (item 20.1) turns the LHS into `μ ((A r)ᶜ ∩ bset A S)`.
        - `ENNReal.sub_eq_of_eq_add` unifies `b := μ (A r ∩ bset A S)` (the SUBTRACTED term —
          not `bset A (insert r S)`, contra the original sketch) and its finiteness hypothesis is
          `measure_ne_top μ (A r ∩ bset A S)` via the `IsProbabilityMeasure →
          IsZeroOrProbabilityMeasure → IsFiniteMeasure` instance chain
          (Probability.lean:74, :53). Goal becomes
          `μ (bset A S) = μ ((A r)ᶜ ∩ bset A S) + μ (A r ∩ bset A S)`.
        - `rw [← measure_inter_add_sdiff (bset A S) (hA r)]` rewrites `μ (bset A S)` by the
          add-form `μ (bset A S ∩ A r) + μ (bset A S \ A r) = μ (bset A S)`.
        - `Set.inter_comm` (`bset A S ∩ A r = A r ∩ bset A S`), `Set.sdiff_eq`
          (`bset A S \ A r = bset A S ∩ (A r)ᶜ`), `Set.inter_comm`
          (`bset A S ∩ (A r)ᶜ = (A r)ᶜ ∩ bset A S`) bring the two sides to the same summands;
          `ac_rfl` closes the commuted additive sum. No `hr` used anywhere.
    - **prep**
        - `bset_insert` (item 20.1).
        - `measure_inter_add_sdiff` — `(s) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s` (`Mathlib/MeasureTheory/Measure/MeasureSpace.lean:118`; signature verified; `measure_inter_add_diff` is a deprecated alias).
        - `Set.sdiff_eq` — `s \ t = s ∩ tᶜ` (`Mathlib/Data/Set/Operations.lean:109`, rfl, NOT `@[simp]` — `rw` it explicitly).
        - `Set.inter_comm` — `a ∩ b = b ∩ a` (`Mathlib/Data/Set/Basic.lean:725`).
        - `ENNReal.sub_eq_of_eq_add` — `(hb : b ≠ ∞) : a = c + b → a - b = c` (`Mathlib/Data/ENNReal/Operations.lean:306`; the symmetric form is `ENNReal.eq_sub_of_add_eq` — `(hc : c ≠ ∞) : a + c = b → a = b - c`, :316 — NOT `ENNReal.eq_tsub_of_add_eq`, which does not exist; that name is the generic `TSub` lemma inside the ENNReal proof).
        - `measure_ne_top` — `(μ) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞` (`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean:55`); `[IsProbabilityMeasure μ]` provides `IsFiniteMeasure μ` via `IsZeroOrProbabilityMeasure.toIsFiniteMeasure` (Probability.lean:53).
        - `ac_rfl` — core tactic, closes the final commuted sum.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `measure_bset_insert` as the surveyed 5-tactic calc (compile-verified warning-free via stdin, exit 0): `rw [bset_insert]`, `rw [ENNReal.sub_eq_of_eq_add (measure_ne_top μ (A r ∩ bset A S))]`, `rw [← measure_inter_add_sdiff (bset A S) (hA r)]`, `rw [Set.inter_comm, Set.sdiff_eq, Set.inter_comm]`, `ac_rfl`. DROP `hr : r ∉ S` (compile-verified unused — linter "not explicitly referenced"; splitting is unconditional, 20.5 precedent). NO `@[simp]` (RHS is an ENNReal subtraction, not a normal form; 40.10 consumes it BACKWARD via `rw [← measure_bset_insert hA]`; `bset_insert` already covers the structural rewrite). Omit line: `omit [Fintype ι] in` (verified: the only unused section var). Prep fixed: `ENNReal.eq_tsub_of_add_eq` does not exist — symmetric form is `ENNReal.eq_sub_of_add_eq` (Operations.lean:316). | Proved `measure_bset_insert` exactly as surveyed: the 5-tactic proof (`bset_insert`; `ENNReal.sub_eq_of_eq_add (measure_ne_top μ (A r ∩ bset A S))`; `← measure_inter_add_sdiff (bset A S) (hA r)`; `Set.inter_comm`/`Set.sdiff_eq`/`Set.inter_comm`; `ac_rfl`) compiles warning-free via stdin, exit 0. `hr : r ∉ S` dropped (linter "not explicitly referenced" — the splitting is unconditional, 20.5 precedent). No `@[simp]` (RHS is an ENNReal subtraction, not a normal form; `bset_insert` covers the structural rewrite; 40.10 consumes BACKWARD). `omit [Fintype ι] in` used (the only unused section var). Reported success. | Re-verified independently: `lake env lean` on the tmp exits 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 31 lines (under the 500-line limit). Statement matches the informal spec exactly: `μ (bset A (insert r S)) = μ (bset A S) - μ (A r ∩ bset A S)`, no `hr`, no `@[simp]`, `omit [Fintype ι] in`. Integrated into `LovaszLocal.lean` after `ofReal_one_sub`, before `end LovaszLocal` (omit line + docstring + lemma + proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty. | `tmp_measure_bset_insert.lean` |

### 40.10. measure_bset_insert_le

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **One-step peeling bound** (the P1-step ingredient, extracted as a standalone lemma with
        an explicit P2-like hypothesis — survey B risk 5): if the "bad part" of the peel is
        controlled at $(r, S)$,
        `measure_bset_insert_le (hA : ∀ i, MeasurableSet (A i)) {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i)
        {S : Finset ι} {r : ι}
        (hP2 : μ (A r ∩ bset A S) ≤ ENNReal.ofReal (x r) * μ (bset A S)) :
        ENNReal.ofReal (1 - x r) * μ (bset A S) ≤ μ (bset A (insert r S))`.
        In symbols:
        $\mathrm{ofReal}(1 - x_r)\cdot\mu(B_S) \le \mu(B_{\{r\} \cup S})$.
        This is where the ENNReal `sub_mul` finiteness threading lives, wrapped once.
        The `hr : r ∉ S` hypothesis was DROPPED in survey (attempt 1, compile-verified): the
        proof never references it (linter "not explicitly referenced", same as 40.5's dropped
        `hr`), and no `hx₁ : ∀ i, x i < 1` is needed (the bound holds without any upper-bound
        control on `x`). NOT `@[simp]`: an inequality with hypotheses `hA`, `hx₀`, `hP2` that
        simp cannot discharge.
    - proof: |
        ```
        rw [ofReal_one_sub (hx₀ r)]
        rw [ENNReal.sub_mul (fun _ _ => measure_ne_top μ (bset A S))]
        rw [one_mul, measure_bset_insert A hA]
        exact tsub_le_tsub_left hP2 (μ (bset A S))
        ```
        (compile-verified warning-free via stdin, exit 0, with `omit [Fintype ι] in`.)
        In symbols:
        $$\mathrm{ofReal}(1 - x_r)\cdot\mu(B_S) = (1 - \mathrm{ofReal}(x_r))\cdot\mu(B_S)
        = \mu(B_S) - \mathrm{ofReal}(x_r)\cdot\mu(B_S) \le \mu(B_S) - \mu(A_r \cap B_S)
        = \mu(B_{\{r\} \cup S}).$$
        - First equality: `ofReal_one_sub (hx₀ r)` (item 40.1) — turns `ofReal (1 - x r)` into
          `1 - ofReal (x r)`.
        - Second: `ENNReal.sub_mul` with `a = 1`, `b = ofReal (x r)`, `c = μ (bset A S)` (all
          inferred by unification — no explicit args needed); its hypothesis
          `0 < b → b < a → c ≠ ∞` discharges unconditionally via the explicit lambda
          `fun _ _ => measure_ne_top μ (bset A S)` (a metavariable `?h` + bullet form also
          compiles). Leaves the artifact `1 * μ (bset A S)`.
        - Third: `one_mul` clears the `1 * μ (bset A S)` artifact (in the same `rw` line as the
          next step).
        - Fourth: `rw [measure_bset_insert A hA]` (item 40.5, applied FORWARD — the goal RHS
          `μ (bset A (insert r S))` is exactly 40.5's LHS; the original sketch's "BACKWARD" was
          wrong: compile-verified, backward `rw [← ...]` fails with "Did not find an occurrence"
          because the goal does not yet contain the difference).
        - Inequality: `tsub_le_tsub_left hP2 (μ (bset A S))` (monotonicity of `μ (B S) - ·`)
          closes.
    - **prep**
        - `ofReal_one_sub` (item 40.1).
        - `measure_bset_insert` (item 40.5) — apply FORWARD via `rw [measure_bset_insert A hA]`
          (goal RHS `μ (bset A (insert r S))` is 40.5's LHS; `hr`-free statement).
        - `ENNReal.sub_mul` — `protected` lemma, `(h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c` (`Mathlib/Data/ENNReal/Operations.lean:408`; signature verified); discharge `h` with the lambda `fun _ _ => measure_ne_top μ (bset A S)`; the symmetric form is `ENNReal.mul_sub` (:413, not needed).
        - `tsub_le_tsub_left` — `(h : a ≤ b) (c) : c - b ≤ c - a` (`Mathlib/Algebra/Order/Sub/Defs.lean:115`; signature verified; ENNReal instance via `OrderedSub`).
        - `measure_ne_top` — finiteness of `μ (bset A S)` (probability measure).
        - `one_mul` — `1 * c = c`; clears the `1 * μ (bset A S)` artifact left by `sub_mul`.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `measure_bset_insert_le` as the surveyed 4-tactic proof (compile-verified warning-free via stdin, exit 0): `rw [ofReal_one_sub (hx₀ r)]`, `rw [ENNReal.sub_mul (fun _ _ => measure_ne_top μ (bset A S))]`, `rw [one_mul, measure_bset_insert A hA]`, `exact tsub_le_tsub_left hP2 (μ (bset A S))`. DROP `hr : r ∉ S` (compile-verified unused — linter "not explicitly referenced", 40.5 precedent; no `hx₁` needed either). NO `@[simp]` (inequality with hypotheses `hA`, `hx₀`, `hP2` — simp cannot discharge them). `measure_bset_insert` applies FORWARD, not backward (goal RHS is 40.5's LHS; backward rw compile-verified to fail). Omit line: `omit [Fintype ι] in` (verified: the only unused section var — `DecidableEq ι` used by `Finset.insert`). Verified for later: unprimed `mul_le_mul_left`/`mul_le_mul_right` exist (Algebra/Order/Monoid/Unbundled/Basic.lean:70/81); primed names are only deprecated meaning-swapped aliases — 40.15 must use the unprimed ones. | Proved `measure_bset_insert_le` exactly as surveyed: the 4-tactic proof (`ofReal_one_sub (hx₀ r)`; `ENNReal.sub_mul (fun _ _ => measure_ne_top μ (bset A S))`; `one_mul` + `measure_bset_insert A hA`; `tsub_le_tsub_left hP2 (μ (bset A S))`) compiles warning-free via stdin, exit 0. `hr : r ∉ S` dropped (linter "not explicitly referenced", 40.5 precedent; no `hx₁` needed). No `@[simp]` (inequality with hypotheses simp cannot discharge). `measure_bset_insert` applied FORWARD (goal RHS is 40.5's LHS; backward rw compile-verified to fail). `omit [Fintype ι] in` used (the only unused section var). Reported success. | Re-verified independently: `lake env lean` on the tmp exits 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 31 lines (under the 500-line limit). Statement matches the informal spec exactly: the hP2-controlled one-step bound `ENNReal.ofReal (1 - x r) * μ (bset A S) ≤ μ (bset A (insert r S))`, no `hr`, no `@[simp]`, `omit [Fintype ι] in`. Integrated into `LovaszLocal.lean` after `measure_bset_insert`, before `end LovaszLocal` (omit line + docstring + lemma + proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty. | `tmp_bset_insert_le.lean` |

### 40.15. prob_bset_inter_prod

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Product-chain bound** — the order-free replacement for the classical chain rule
        (gpt-notes step (4), survey B step 8): for disjoint `N, M`,
        ```lean
        prob_bset_inter_prod (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            {N M : Finset ι} (hNM : Disjoint N M)
            (hP2 : ∀ (U : Finset ι), U ⊆ M ∪ N → ∀ i, i ∈ N → i ∉ U →
              μ (A i ∩ bset A U) ≤ ENNReal.ofReal (x i) * μ (bset A U)) :
            ENNReal.ofReal (∏ j ∈ N, (1 - x j)) * μ (bset A M) ≤ μ (bset A (N ∪ M))
        ```
        In symbols:
        $\mathrm{ofReal}\Bigl(\prod_{j \in N} (1 - x_j)\Bigr)\cdot\mu(B_M) \le \mu(B_{N \cup M})$.
        `hP2` is the P2-invariant restricted to the subsets of `S = N ∪ M` — exactly the shape the
        60.1 strong-induction IH provides (each such `U` is a strict subset of `S` since `i ∈ S \ U`).
        **STATEMENT CORRECTED by Survey 2026-08-15 (attempt 1): the originally planned statement
        is FALSE.** The original plan had `hP2` only at the sets `M ∪ (N.erase i)`. Counterexample
        (ingredients compile-verified): `N = {r, s}`, `M = ∅`, `A_r = A_s = Ω`, `0 < x_r, x_s < 1`.
        Both hypotheses hold — `μ (A_r ∩ B_{M ∪ {s}}) = μ (Ω ∩ Ā_s) = μ ∅ = 0 ≤ ofReal(x_r) · 0` —
        yet the conclusion reads `ofReal ((1-x_r)(1-x_s)) · μ(B_∅) = ofReal ((1-x_r)(1-x_s)) > 0
        ≤ μ(B_{r,s}) = μ ∅ = 0`, absurd. Structural reason: peeling `r` needs the P2-bound at
        `(r, M ∪ (N.erase r))`, and the nested induction's IH at `N'` needs it at every
        `(i, M ∪ T)` with `T ⊆ N'.erase i`; the `N.erase i` shape provides at `i ∈ N'` only
        `M ∪ insert r (N'.erase i)`. Fix: quantify over **all** `U ⊆ M ∪ N`. `hNM` is **kept** and
        genuinely used (the peel needs `r ∉ M ∪ N'`).
    - proof: |
        `Finset.induction` on `N` with `M` FIXED (`induction N using Finset.induction with` — the
        induction auto-generalizes `hNM`/`hP2`, which mention `N`; the `with` form auto-introduces
        the case hypotheses). Compile-tested warning-free via `lake env lean` (stdin) 2026-08-15,
        exit 0:
        ```lean
        omit [Fintype ι] in
        lemma prob_bset_inter_prod (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            {N M : Finset ι} (hNM : Disjoint N M)
            (hP2 : ∀ (U : Finset ι), U ⊆ M ∪ N → ∀ i, i ∈ N → i ∉ U →
              μ (A i ∩ bset A U) ≤ ENNReal.ofReal (x i) * μ (bset A U)) :
            ENNReal.ofReal (∏ j ∈ N, (1 - x j)) * μ (bset A M) ≤ μ (bset A (N ∪ M)) := by
          induction N using Finset.induction with
          | empty =>
              simp
          | insert r N' hr ih =>
              have hpeel : ENNReal.ofReal (1 - x r) * μ (bset A (N' ∪ M)) ≤
                  μ (bset A (insert r (N' ∪ M))) := by
                refine measure_bset_insert_le A hA hx₀ ?_
                have hUsub : N' ∪ M ⊆ M ∪ insert r N' := by
                  rw [Finset.union_comm]
                  exact Finset.union_subset_union_right (Finset.subset_insert r N')
                have hrM : r ∉ M := (Finset.disjoint_left.mp hNM) (Finset.mem_insert_self r N')
                have hrU : r ∉ N' ∪ M := by
                  simp [hr, hrM]
                exact hP2 (N' ∪ M) hUsub r (Finset.mem_insert_self r N') hrU
              have hih : ENNReal.ofReal (∏ j ∈ N', (1 - x j)) * μ (bset A M) ≤ μ (bset A (N' ∪ M)) := by
                refine ih (Disjoint.mono_left (Finset.subset_insert r N') hNM) ?_
                intro U hU i hi hiu
                exact hP2 U (hU.trans (Finset.union_subset_union_right (Finset.subset_insert r N'))) i
                  (Finset.mem_insert.mpr (Or.inr hi)) hiu
              calc
                ENNReal.ofReal (∏ j ∈ insert r N', (1 - x j)) * μ (bset A M)
                    = ENNReal.ofReal ((1 - x r) * ∏ j ∈ N', (1 - x j)) * μ (bset A M) := by
                        rw [Finset.prod_insert hr]
                _ = (ENNReal.ofReal (1 - x r) * ENNReal.ofReal (∏ j ∈ N', (1 - x j))) * μ (bset A M) := by
                        rw [ENNReal.ofReal_mul (sub_nonneg.mpr (le_of_lt (hx₁ r)))]
                _ = ENNReal.ofReal (1 - x r) * (ENNReal.ofReal (∏ j ∈ N', (1 - x j)) * μ (bset A M)) := by
                        rw [mul_assoc]
                _ ≤ ENNReal.ofReal (1 - x r) * μ (bset A (N' ∪ M)) := by
                        exact mul_le_mul_right hih (ENNReal.ofReal (1 - x r))
                _ ≤ μ (bset A (insert r (N' ∪ M))) := hpeel
                _ = μ (bset A (insert r N' ∪ M)) := by
                        rw [← Finset.insert_union]
        ```
        Structure: (1) peel `r` off the FULL set `N' ∪ M` via `measure_bset_insert_le` (40.10) at
        `(r, N' ∪ M)`; its hypothesis is `hP2` at `(r, U := N' ∪ M)` — the subset certificate
        `hUsub` is `Finset.union_comm` + `Finset.union_subset_union_right (Finset.subset_insert r N')`,
        and `r ∉ N' ∪ M` comes from `hr` plus `r ∉ M` (`hNM` via `Finset.disjoint_left`).
        (2) IH at `N'` with the SAME `M`: `Disjoint N' M` via `Disjoint.mono_left
        (Finset.subset_insert r N') hNM`; its hP2 is `hP2` restricted to `U ⊆ M ∪ N'`
        (`hU.trans (Finset.union_subset_union_right …)`), `i ∈ N'` lifted via `Finset.mem_insert`.
        (3) the calc chain: `Finset.prod_insert hr` → `ENNReal.ofReal_mul` (`0 ≤ 1 - x r` from
        `sub_nonneg.mpr (le_of_lt (hx₁ r))` — only the first factor's nonneg is needed) →
        `mul_assoc` → `mul_le_mul_right` (the v4.32 left-multiplication lemma) with the IH
        conclusion → `hpeel` → `← Finset.insert_union`. Base case: plain `simp`
        (`Finset.prod_empty`, `ENNReal.ofReal_one`, `Finset.empty_union`).
    - attributes: |
        Survey decision (2026-08-15): NO `@[simp]` — inequality with hypotheses `hA`, `hx₀`, `hx₁`,
        `hNM`, `hP2` that simp cannot discharge (40.10 precedent). The sole consumer (60.1 step (5))
        applies it explicitly.
    - **prep**
        - `measure_bset_insert_le` (item 40.10) — the one-step peel, applied at `(r, N' ∪ M)` (NOT at `(r, M)` — the hP2 shape cannot reach `M` alone).
        - `Finset.induction` — `[DecidableEq α] (empty : motive ∅) (insert : ∀ a s, a ∉ s → motive s → motive (insert a s)) (s) : motive s` (`Mathlib/Data/Finset/Insert.lean:480`) — via `induction N using Finset.induction with | empty => … | insert r N' hr ih => …`; `M` stays fixed, `hNM`/`hP2` auto-generalized.
        - `Finset.prod_insert` — `(h : a ∉ s) : ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:49`, `[DecidableEq ι]`).
        - `ENNReal.ofReal_mul` — `(hp : 0 ≤ p) : ofReal (p * q) = ofReal p * ofReal q` (`Mathlib/Data/ENNReal/Real.lean:297`) — applied with `p := 1 - x r`; only the FIRST factor's nonneg is needed.
        - `sub_nonneg` — `[AddGroup α] [LE α] [AddRightMono α] {a b} : 0 ≤ a - b ↔ b ≤ a` (signature #check-verified 2026-08-15) — `sub_nonneg.mpr (le_of_lt (hx₁ r)) : 0 ≤ 1 - x r`.
        - `le_of_lt` — core.
        - `ENNReal.ofReal_one` — base case (`Mathlib/Data/ENNReal/Basic.lean:297`, `@[simp]`; consumed by `simp`).
        - `mul_le_mul_right` — **left-multiplication in v4.32**: `[MulLeftMono α] {b c} (bc : b ≤ c) (a) : a * b ≤ a * c` (`Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:70`). NAME-SWAP CAUTION (compile-verified 2026-08-15): the unprimed names are counterintuitive — `mul_le_mul_right` multiplies on the LEFT, `mul_le_mul_left` (:81) multiplies on the RIGHT (`b * a ≤ c * a`); the primed `mul_le_mul_left'`/`mul_le_mul_right'` are deprecated aliases with the SAME meaning (NOT meaning-swapped — correcting 40.10's log note). This proof multiplies on the left → `mul_le_mul_right hih (ofReal (1 - x r))` (ENNReal's `MulLeftMono` comes from `IsOrderedMonoid.toMulLeftMono`, priority 900).
        - `mul_assoc` — `(a * b) * c = a * (b * c)` (ENNReal).
        - `Finset.insert_union` — `insert a s ∪ t = insert a (s ∪ t)` (`Mathlib/Data/Finset/Lattice/Lemmas.lean:83`) — applied BACKWARD to close.
        - `Finset.union_comm` — `s ∪ t = t ∪ s` (`Mathlib/Data/Finset/Lattice/Basic.lean:137`).
        - `Finset.union_subset_union_right` — `(h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂` (`Mathlib/Data/Finset/Lattice/Basic.lean:134`) — the subset certificates for the `hP2` applications.
        - `Finset.disjoint_left` — `Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t` (`Mathlib/Data/Finset/Disjoint.lean:47`) — `r ∉ M` from `hNM`.
        - `Disjoint.mono_left` — `[PartialOrder α] [OrderBot α] {a b c} (h : a ≤ b) : Disjoint b c → Disjoint a c` (`Mathlib/Order/Disjoint.lean:80`) — `Disjoint N' M` for the IH.
        - `Finset.subset_insert` — `s ⊆ insert a s` (`@[simp]`).
        - `Finset.mem_insert_self` / `Finset.mem_insert` / `Finset.mem_union` — membership bookkeeping (`@[simp]`-handled).
        - REMOVED (obsolete in the corrected route; all verified to exist but unused): `Finset.erase_insert`, `Finset.erase_union_distrib`, `Finset.prod_nonneg`, `ENNReal.ofReal_prod_of_nonneg` — the corrected statement has no `erase`; the product-nonneg condition is not needed (`ofReal_mul` requires only `0 ≤ p` for the first factor).
        - Note for Proof (warning-free form, compile-tested 2026-08-15): `omit [Fintype ι] in` — the only unused section var (`[IsProbabilityMeasure μ]` IS used, via 40.10's `measure_ne_top`; `[DecidableEq ι]` used by `Finset.induction`/`prod_insert`). NO `classical` needed — the section's `[DecidableEq ι]` serves the whole proof. Resulting signature (verified via #check): `{Ω ι} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [DecidableEq ι] (A) (hA) {x} (hx₀) (hx₁) {N M} (hNM) (hP2) : …`.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove the CORRECTED product-chain bound. Survey found the planned statement FALSE (counterexample N={r,s}, M=∅, A≡Ω, compile-verified: hP2 at `M ∪ (N.erase i)` holds yet conclusion demands `ofReal ((1-x_r)(1-x_s)) ≤ 0`); hP2 strengthened to all `U ⊆ M ∪ N` with `i ∈ N \ U` (what 60.1's IH(P2) actually provides); hNM KEPT (used: `r ∉ M` for the peel). Route: `induction N using Finset.induction` with M fixed; peel `r` off `N' ∪ M` via `measure_bset_insert_le` (40.10); IH at `(N', M)`; calc chain `prod_insert` → `ofReal_mul` → `mul_assoc` → `mul_le_mul_right` → peel → `← insert_union`. Compile-tested warning-free via stdin (exit 0), omit `[Fintype ι]` | Proved the corrected statement exactly as surveyed: `Finset.induction` on `N` with `M` fixed; `hpeel` = `measure_bset_insert_le` (40.10) at `(r, N' ∪ M)` with subset certificate `Finset.union_comm` + `Finset.union_subset_union_right (Finset.subset_insert r N')` and `r ∉ N' ∪ M` from `hr` + `r ∉ M` (hNM via `Finset.disjoint_left`); IH at `(N', M)` via `Disjoint.mono_left (Finset.subset_insert r N') hNM` with `hP2` restricted to `U ⊆ M ∪ N'`; calc chain `Finset.prod_insert hr` → `ENNReal.ofReal_mul (sub_nonneg.mpr (le_of_lt (hx₁ r)))` → `mul_assoc` → `mul_le_mul_right` (left-mult in v4.32) → `hpeel` → `← Finset.insert_union`; base case `simp`. Compiles warning-free via `lake env lean` (exit 0, empty output). `omit [Fintype ι] in`, no `@[simp]`, no `classical`. | Re-verified independently: tmp `lake env lean` exit 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`; 59 lines (under the 500-line limit). Statement matches the corrected informal spec exactly: hP2 at all `U ⊆ M ∪ N` with `i ∈ N \ U`, hNM kept, no `@[simp]`, `omit [Fintype ι]`. `lake build StatsMLlib.Probability.LovaszLocal` succeeds (project linters). Integrated into `LovaszLocal.lean` after `measure_bset_insert_le`, before `end LovaszLocal` (omit line + docstring + lemma + proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, lake build succeeds. | `tmp_prob_bset_inter_prod.lean` |

---
## 60. Main Theorem

### 60.1. lll_prob_bset

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **The (P1)+(P2) strong induction** — the heart of the proof (survey B step 10,
        gpt-notes Lemma 4.2, reorganized without conditional probabilities). Under the full LLL
        hypotheses
        $$hA : \forall i,\ \mathrm{MeasurableSet}(A_i),\qquad hdg : \mathrm{IsDependencyGraph}\, G\, A,$$
        $$hx_0 : \forall i,\ 0 \le x_i,\qquad hx_1 : \forall i,\ x_i < 1,$$
        $$hLLL : \forall i,\ \mu(A_i) \le \mathrm{ofReal}\Bigl(x_i \cdot \prod_{j \in \Gamma(i)} (1 - x_j)\Bigr),$$
        prove, for **every** finite `S : Finset ι`, simultaneously:
        $$(P1_S)\quad \mathrm{ofReal}\Bigl(\prod_{j \in S} (1-x_j)\Bigr) \le \mu(B_S),$$
        $$(P2_{i,S})\quad i \notin S \ \Longrightarrow\ \mu(A_i \cap B_S) \le \mathrm{ofReal}(x_i)\cdot \mu(B_S).$$
        Lean statement: `lll_prob_bset ... (S : Finset ι) :
        ENNReal.ofReal (∏ j ∈ S, (1 - x j)) ≤ μ (bset A S) ∧
        ∀ i, i ∉ S → μ (A i ∩ bset A S) ≤ ENNReal.ofReal (x i) * μ (bset A S)`.
        One `And` (Lean cannot do mutual recursion over `strongInductionOn` cleanly — risk 5);
        the reusable pieces are items 40.10 and 40.15, so the induction body only assembles them.
        Binder notes (from the 2026-08-15 Survey, all compile-verified): the theorem needs
        `[DecidableRel G.Adj]` (for `S.filter`); `hdg` must be written `IsDependencyGraph (μ := μ) G A`
        (its `μ` is an implicit parameter — a bare `IsDependencyGraph G A` fails header elaboration);
        use `omit [DecidableEq ι] in` (the statement does not mention it; the proof's `classical`
        supplies local `DecidableEq` for `erase`); NOT `@[simp]` (inequality with hypotheses).
        Est. 250--350 lines (the verified skeleton is 137).
    - proof: |
        `Finset.strongInductionOn S` (`classical` first, then `refine Finset.strongInductionOn S ?_`
        + `intro S ih`). Full skeleton compile-verified warning-free via `lake env lean /dev/stdin`
        (137 lines, no `sorry`, axioms only `propext`/`Classical.choice`/`Quot.sound`). Structure:
        - **Shared `hμi (i : ι) : μ (A i) ≤ ofReal (x i)`** (used by the base P2 and the `N = ∅`
          case): `hLLL i` + `ENNReal.ofReal_mul (hx₀ i)`, then `ofReal (∏_{Γ(i)} (1 - x j)) ≤ 1`
          via `ENNReal.ofReal_prod_of_nonneg` (factors `0 ≤ 1 - x j` from `hx₁ j` via `sub_nonneg`)
          + `Finset.prod_le_one'` **on the ENNReal product** (`MulLeftMono ℝ` does NOT exist!),
          factors `ofReal (1 - x j) ≤ 1` via `ENNReal.ofReal_le_ofReal` + `linarith [hx₀ j]`; close
          with `mul_le_mul_right` + `ofReal_one` simp.
        - **Base `S = ∅`**: `by_cases hS : S = ∅`; `subst S`; (P1) `simp` closes alone
          (`bset_empty`, `measure_univ`, `ofReal_one`, `prod_empty` all `@[simp]`); (P2)
          `simp` then `exact hμi i`.
        - **P1 step** (`¬ S = ∅`): `⟨r, hr⟩` from `S.Nonempty` (`Finset.nonempty_iff_ne_empty.mpr
          hS`); IH at `S.erase r` via `Finset.erase_ssubset hr`; `r ∉ S.erase r` via
          `Finset.notMem_erase r S`; calc: `← Finset.mul_prod_erase S (fun j => 1 - x j) hr`
          (peel — `mul_prod_erase` has `f r` FIRST; `prod_erase_mul` is the swapped variant and is
          NOT what this step needs) → `ENNReal.ofReal_mul (sub_nonneg.mpr (le_of_lt (hx₁ r)))` →
          `mul_le_mul_right (IH P1) (ofReal (1 - x r))` → `measure_bset_insert_le A hA hx₀
          (IH P2 at (r, S.erase r))` → `Finset.insert_erase hr`. (`measure_bset_insert` (40.5) is
          used only inside 40.10.)
        - **P2 step** (`i ∉ S`): `let N := S.filter (fun j => G.Adj i j)`, `let M := S.filter
          (fun j => ¬ G.Adj i j)`; `by_cases hN : N = ∅`:
          * `N = ∅`: every `j ∈ S` is a non-neighbor (`Finset.mem_filter.mpr` + `rw [hN] at hjN` +
            `Finset.notMem_empty j hjN`); `hdg i S hiS hnonadjS` gives `IndepSet (A i) (bset A S)`;
            `(indepSet_iff_measure_inter_eq_mul (μ := μ) (hA i) (measurableSet_bset A hA S)).mp`
            (the explicit `(μ := μ)` is REQUIRED — the `volume_tac` default whnf-TIMEOUTS on an
            Ω without MeasureSpace) gives `μ (A i ∩ B S) = μ (A i) * μ (B S)`; close with
            `mul_le_mul_left (hμi i) (μ (bset A S))`.
          * `N ≠ ∅` (the 5-inequality chain):
            $$\mu(A_i \cap B_S) \le \mu(A_i \cap B_M)
            = \mu(A_i)\cdot\mu(B_M)
            \le \mathrm{ofReal}(x_i)\cdot\mathrm{ofReal}\Bigl(\prod_{\Gamma(i)}(1-x_j)\Bigr)\cdot\mu(B_M)
            \le \mathrm{ofReal}(x_i)\cdot\mathrm{ofReal}\Bigl(\prod_{N}(1-x_j)\Bigr)\cdot\mu(B_M)
            \le \mathrm{ofReal}(x_i)\cdot\mu(B_{N \cup M})
            = \mathrm{ofReal}(x_i)\cdot\mu(B_S).$$
            - `hNM : Disjoint N M` via `Finset.disjoint_left` (filter partition);
              `hSMN : N ∪ M = S` via `Finset.filter_union_filter_not_eq (fun j => G.Adj i j) S`
              (the predicate is an EXPLICIT first argument).
            - (1): `measure_mono (by simpa [Set.inter_comm] using Set.inter_subset_inter_left (A i)
              (bset_subset_bset_of_subset A hMS))` with `hMS : M ⊆ S` from `Finset.filter_subset
              (fun j => ¬ G.Adj i j) S` (again: predicate explicit first).
            - (2): `hdg i M hiM hnonadjM` (with `hiM : i ∉ M` from `i ∉ S` + `filter_subset`) +
              `indepSet_iff_measure_inter_eq_mul (μ := μ)`.
            - (3): `hLLL i` + `ENNReal.ofReal_mul (hx₀ i)` + `mul_le_mul_left _ (μ (bset A M))`.
            - (4): `hNΓ : N ⊆ G.neighborFinset i` via `simpa using (Finset.mem_filter.mp hjN).2`
              (`mem_neighborFinset` is `@[simp]`); BOTH products lifted by
              `ENNReal.ofReal_prod_of_nonneg` and compared by
              `Finset.prod_le_prod_of_subset_of_le_one' hNΓ` **on the ENNReal products** (off-set
              factors `ofReal (1 - x j) ≤ 1` via `ofReal_le_ofReal` + `linarith [hx₀ j]` — no
              `MulLeftMono ℝ`); then `mul_le_mul_left (mul_le_mul_right hofN (ofReal (x i)))
              (μ (bset A M))`.
            - (5): `prob_bset_inter_prod A hA hx₀ hx₁ hNM hP2'` under `rw [mul_assoc]` +
              `mul_le_mul_right _ (ofReal (x i))`; its `hP2` (corrected shape, see 40.15) is the
              IH(P2) at every `U ⊆ M ∪ N = S` with `k ∈ N \ U`: `U ⊆ S` via `rw [← hSMN]` +
              `simpa [Finset.union_comm] using hU`; `U ≠ S` since `k ∈ S` (from `k ∈ N` via
              `Finset.mem_filter.mp`) and `k ∉ U`; conclude `U ⊂ S` via
              `Finset.ssubset_iff_subset_ne.mpr ⟨hUS, hUne⟩`.
            - (=): `rw [hSMN]` (`N ∪ M = S`).
    - **prep**
        - Internal: `bset` (10.1), `IsDependencyGraph` (10.5), `bset_empty` (20.1),
          `bset_subset_bset_of_subset` (20.5), `measurableSet_bset` (20.15), `ofReal_one_sub` (40.1),
          `measure_bset_insert` (40.5), `measure_bset_insert_le` (40.10), `prob_bset_inter_prod` (40.15).
        - `Finset.strongInductionOn` — `{p : Finset α → Sort*} (s) : (∀ s, (∀ t ⊂ s, p t) → p s) → p s`
          (`Mathlib/Data/Finset/Card.lean:852`, `@[elab_as_elim]`) — use via
          `refine Finset.strongInductionOn S ?_` + `intro S ih`.
        - `Finset.erase_ssubset` — `(h : a ∈ s) : s.erase a ⊂ s` (`Mathlib/Data/Finset/Basic.lean:151`)
          — the IH access for `S.erase r`.
        - `Finset.insert_erase` — `(h : a ∈ s) : insert a (s.erase a) = s` (`Basic.lean:142`, `@[simp]`).
        - `Finset.mul_prod_erase` — `[DecidableEq ι] (s) (f) {a} (h : a ∈ s) :
          f a * ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:742`);
          use `←` to peel `∏_{j∈S}` into `(1 - x_r) * ∏_{j∈S.erase r}`. NOTE: `Finset.prod_erase_mul`
          (`:747`) is the SWAPPED variant (product first) — not what the P1 step needs.
        - `Finset.ssubset_iff_subset_ne` — `s ⊂ t ↔ s ⊆ t ∧ s ≠ t` (`Mathlib/Data/Finset/Defs.lean:270`)
          — the `U ⊂ S` certificate for 40.15's hP2 (from `U ⊆ S` + `k ∈ S \ U`); the old
          `M ∪ (N.erase i) = S.erase i` computation (`Finset.erase_union_distrib`) is obsolete after
          the 40.15 statement correction.
        - `Finset.filter_union_filter_not_eq` — `(p : α → Prop) [∀ x, Decidable (¬p x)] (s : Finset α) :
          s.filter p ∪ s.filter (¬p·) = s` (`Mathlib/Data/Finset/Basic.lean:427`); **p is an EXPLICIT
          first argument** (the Filter section declares `variable (p q : α → Prop)`) — use
          `Finset.filter_union_filter_not_eq (fun j => G.Adj i j) S`; gives `N ∪ M = S` directly.
          (the `filter_union_filter_neg_eq` alias is deprecated since 2025-12-12).
        - `Finset.filter_subset` — `(p : α → Prop) [DecidablePred p] (s) : s.filter p ⊆ s`
          (`Mathlib/Data/Finset/Filter.lean:121`, `@[simp]`) — predicate explicit FIRST (same section);
          gives `M ⊆ S` and `i ∉ M`.
        - `Finset.mem_filter` — `a ∈ s.filter p ↔ a ∈ s ∧ p a` (`Mathlib/Data/Finset/Filter.lean:127`, `@[simp]`).
        - `Finset.notMem_empty` — `(a : α) : a ∉ (∅ : Finset α)` (`Mathlib/Data/Finset/Empty.lean:108`).
        - `Finset.nonempty_iff_ne_empty` — `s.Nonempty ↔ s ≠ ∅` (`Mathlib/Data/Finset/Empty.lean:146`;
          `Finset.Nonempty s` is `∃ x, x ∈ s`) — the P1 `⟨r, hr⟩` extraction; plus
          `Finset.notMem_erase (a) (s) : a ∉ s.erase a` (`Basic.lean` ~215) for `r ∉ S.erase r`.
        - `Finset.disjoint_left` — `Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t`
          (`Mathlib/Data/Finset/Disjoint.lean:47`) — the `hNM` certificate from the filter partition.
        - `Finset.prod_le_one'` — `[MulLeftMono N] (h : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1`
          (`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:128`); and
          `Finset.prod_le_prod_of_subset_of_le_one'` — `[CommMonoid N] [Preorder N] [MulLeftMono N]
          (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i` (`:141`).
          **CRITICAL: `MulLeftMono ℝ` does NOT exist** (multiplication by a negative real is not
          monotone — compile-verified `inferInstance` failure) — apply these to the ENNReal products
          `∏ ofReal (1 - x j)` instead, after `ENNReal.ofReal_prod_of_nonneg`; factor bounds
          `1 - x j ≤ 1` via `linarith [hx₀ j]` (no generic `sub_le_self` exists in mathlib for ℝ).
        - `indepSet_iff_measure_inter_eq_mul` — `(hs_meas) (ht_meas) (μ := by volume_tac)
          [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`
          (`Mathlib/Probability/Independence/Basic.lean:579`). **MUST pass `(μ := μ)` explicitly** —
          the `volume_tac` default whnf-TIMEOUTS (200k heartbeats) on an Ω without MeasureSpace.
          The `[IsZeroOrProbabilityMeasure μ]` instance comes from `IsProbabilityMeasure`
          (instance, priority 100, `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:73`).
        - `IsDependencyGraph` — its `μ` is an implicit parameter (`{Ω ι} [MeasurableSpace Ω] {μ}
          (G) (A)`); theorem headers must write `IsDependencyGraph (μ := μ) G A` (a bare
          `IsDependencyGraph G A` fails header elaboration: "don't know how to synthesize implicit
          argument μ").
        - `SimpleGraph.mem_neighborFinset` — `w ∈ G.neighborFinset v ↔ G.Adj v w`
          (`Mathlib/Combinatorics/SimpleGraph/Finite.lean:177`, `@[simp]`) — the `N ⊆ Γ(i)` step
          (`simpa using (Finset.mem_filter.mp hjN).2`). `SimpleGraph.notMem_neighborFinset_self`
          (`:180`) — available but unused by the skeleton.
        - `measure_mono` — `(h : s ⊆ t) : μ s ≤ μ t` (`Mathlib/MeasureTheory/OuterMeasure/Basic.lean:51`).
        - `Set.inter_subset_inter_left` — `(u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u`
          (`Mathlib/Data/Set/Basic.lean:793`) — note the arg order `(u) (H)`; wrap with
          `simpa [Set.inter_comm]` to match `A i ∩ bset A S`.
        - `measure_ne_top`, `measure_univ` — transitive via `measure_bset_insert_le` / the base-case
          `simp` (`[IsProbabilityMeasure μ]`; `Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean:55`,
          `.../Probability.lean:65`).
        - `ENNReal.ofReal_mul` — `{p q : ℝ} (hp : 0 ≤ p) : ofReal (p * q) = ofReal p * ofReal q`
          (`Mathlib/Data/ENNReal/Real.lean:297`, single explicit hypothesis);
          `ENNReal.ofReal_prod_of_nonneg` — `(hf : ∀ i, i ∈ s → 0 ≤ f i) :
          ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ofReal (f i)` (`Mathlib/Data/ENNReal/BigOperators.lean:64`);
          `ENNReal.ofReal_one` — `Mathlib/Data/ENNReal/Basic.lean:297` (`@[simp]`);
          `ENNReal.ofReal_le_ofReal` — `(h : p ≤ q) : ofReal p ≤ ofReal q`
          (`Mathlib/Data/ENNReal/Real.lean:137`). (`ENNReal.ofReal_pos` — not needed by the skeleton.)
        - `mul_le_mul_left` / `mul_le_mul_right` — `[MulRightMono α] (bc : b ≤ c) (a) : b * a ≤ c * a`
          resp. `[MulLeftMono α] (bc : b ≤ c) (a) : a * b ≤ a * c`
          (`Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:81/70`) — unprimed LEFT/RIGHT
          multiplication semantics (right = multiplies on left `a * b ≤ a * c`).
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove the full `lll_prob_bset` in one go following the Survey's compile-verified skeleton (base + P1 + P2, 137 lines, no sorry, warning-free via stdin, axioms only propext/Classical.choice/Quot.sound) — no item splitting needed | Survey compile-verified the full proof (8 blockers fixed during development, all recorded in the informal section: `MulLeftMono ℝ` absence, `(μ := μ)` requirements, `omit [DecidableEq ι]`, `mul_le_mul_left/right` semantics, `Finset.filter_union_filter_not_eq` explicit predicate, etc.); Setup materialized it as the tmp file (153 lines, zero sorries, warning-free, no separate Proof role needed). | Re-verified independently: tmp `lake env lean` exit 0 with empty output (warning-free); LSP diagnostics empty; `lake build StatsMLlib.Probability.LovaszLocal` succeeds (project linters); grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`; 153 lines (under the 500-line limit). Statement matches the informal spec exactly: (P1)+(P2) conjunction, `[DecidableRel G.Adj]`, `IsDependencyGraph (μ := μ) G A`, `omit [DecidableEq ι]`, no `@[simp]`. `#print axioms LovaszLocal.lll_prob_bset` = [propext, Classical.choice, Quot.sound] (only the standard set). Integrated into `LovaszLocal.lean` after `prob_bset_inter_prod`, before `end LovaszLocal` (omit line + docstring + theorem + full proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, lake build succeeds. | `tmp_lll_prob_bset.lean` |

### 60.5. lovaszLocalLemma

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Asymmetric Lovász Local Lemma** (gpt-notes Theorem 4.1, ENNReal form). For
        `{G : SimpleGraph ι} [DecidableRel G.Adj] {A : ι → Set Ω} (x : ι → ℝ)` with hypotheses
        `hA` (measurability), `hdg : IsDependencyGraph G A`, `hx₀ : ∀ i, 0 ≤ x i`,
        `hx₁ : ∀ i, x i < 1`, and
        $hLLL : \forall i,\ \mu(A_i) \le \mathrm{ofReal}\Bigl(x_i \cdot \prod_{j \in \Gamma(i)} (1 - x_j)\Bigr)$:
        $$\mathrm{ofReal}\Bigl(\prod_{i} (1 - x_i)\Bigr) \le \mu\Bigl(\bigcap_i \overline{A_i}\Bigr).$$
        Assembly only — all substance is item 60.1. (gpt-notes §4.2's chain-rule assembly is
        replaced by (P1) at `S = univ`; no enumeration, no order on `ι`.)
    - proof: |
        Apply `lll_prob_bset` (item 60.1) at `S = Finset.univ`; the (P1) conclusion is
        `ofReal (∏ j ∈ Finset.univ, (1 - x j)) ≤ μ (bset A Finset.univ)`. One `simpa` closes the
        final statement: the LHS product `∏ j ∈ (Finset.univ : Finset ι), (1 - x j)` is
        definitionally `∏ j, (1 - x j)` (no lemma needed), and the RHS rewrites by the
        `@[simp]` lemma `bset_univ_eq_iInter` (item 20.10). The exact one-liner
        `simpa using (lll_prob_bset A hA hdg hx₀ hx₁ hLLL Finset.univ).1` was compile-verified
        end-to-end by this item's Survey (attempt 1) via `lake env lean /dev/stdin` — exit 0,
        empty output (warning-free). ~15 lines. Layout: `omit [DecidableEq ι] in` line, THEN the
        docstring, then the theorem (same layout as item 60.1); no `@[simp]` (it is an
        inequality with hypotheses).
    - **prep**
        - `lll_prob_bset` (item 60.1) — (P1) at `S = Finset.univ` (NOT bare `univ`: no `univ` notation exists in mathlib v4.32.0; a bare `univ` silently auto-binds as an implicit free variable — see the pitfall in item 20.10). Binder shape matches 60.1 exactly: `(A) (hA) {G} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A) {x} (hx₀) (hx₁) (hLLL)`.
        - `bset_univ_eq_iInter` (item 20.10, `@[simp]`) — `bset A Finset.univ = ⋂ i, (A i)ᶜ`; the RHS rewrite is automatic under `simp`. Assembly is one `simpa` (compile-verified by this item's Survey, attempt 1: (P1)-at-univ conclusion `… ≤ μ (bset A Finset.univ)` → `… ≤ μ (⋂ i, (A i)ᶜ)`), and the LHS product needs NO lemma — `∏ j ∈ (Finset.univ : Finset ι), (1 - x j)` is definitionally `∏ j, (1 - x j)` (the `∈` binder is notation; verified by simp trace `eq_self`).
        - `omit [DecidableEq ι] in` — required: without it the linter warns `automatically included section variable(s) unused in theorem … [DecidableEq ι]` (compile-verified both ways by this Survey). Docstring goes AFTER the omit line, matching item 60.1's layout; no `@[simp]`.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Assemble `lovaszLocalLemma` from `lll_prob_bset` at `S = Finset.univ` via the one-line `simpa using (lll_prob_bset A hA hdg hx₀ hx₁ hLLL Finset.univ).1` (Survey compile-verified warning-free via stdin, exit 0; `omit [DecidableEq ι] in` required, docstring after the omit line, no `@[simp]`); then integrate after `lll_prob_bset` in `LovaszLocal.lean` | Assembled exactly as planned: `omit [DecidableEq ι] in`, docstring, theorem, and the one-line proof `simpa using (lll_prob_bset A hA hdg hx₀ hx₁ hLLL Finset.univ).1` — the LHS product `∏ j ∈ Finset.univ` is definitionally `∏ j`, and the RHS `bset A Finset.univ` rewrites to `⋂ i, (A i)ᶜ` via the `@[simp]` lemma `bset_univ_eq_iInter`. Tmp file: 29 lines, warning-free, no `sorry`/`axiom`/`admit`/`native_decide`/`#`. | Re-verified independently: tmp `lake env lean` exit 0 with empty output (warning-free); LSP diagnostics empty; `lake build StatsMLlib.Probability.LovaszLocal` succeeds (project linters); grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`; 29 lines (well under the 500-line limit). Statement matches item 60.5's informal spec exactly: binder shape identical to item 60.1 (`IsDependencyGraph (μ := μ) G A`, `[DecidableRel G.Adj]`), conclusion `ENNReal.ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)`, `omit [DecidableEq ι] in`, no `@[simp]`. `#print axioms LovaszLocal.lovaszLocalLemma` (via `lake env lean --stdin` after `lake build` of the tmp module) = [propext, Classical.choice, Quot.sound] — only the standard set. Integrated into `LovaszLocal.lean` after `lll_prob_bset`, before `end LovaszLocal` (omit line + docstring + theorem + proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds. Next: item 80.1 (`lovaszLocalLemma_pos`). | `tmp_lovasz_local_lemma.lean` |

---
## 80. Corollaries

### 80.1. lovaszLocalLemma_pos

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Existence form** (the headline "probabilistic method" statement): under the same
        hypotheses as `lovaszLocalLemma`,
        $$0 < \mu\Bigl(\bigcap_i \overline{A_i}\Bigr).$$
        Some outcome avoids all bad events.
    - proof: |
        Three `have`s and an `exact`, compile-verified warning-free by this item's Survey
        (attempt 1) via `lake env lean /dev/stdin` — exit 0, empty output. Layout identical to
        item 60.5: `omit [DecidableEq ι] in` line, THEN the docstring, then the theorem; no
        `@[simp]` (inequality with hypotheses). The exact proof:
        ```
        omit [DecidableEq ι] in
        theorem lovaszLocalLemma_pos (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))) :
            0 < μ (⋂ i, (A i)ᶜ) := by
          have hprod : 0 < ∏ i, (1 - x i) := Finset.prod_pos (fun i hi => sub_pos.mpr (hx₁ i))
          have hofReal : 0 < ENNReal.ofReal (∏ i, (1 - x i)) := ENNReal.ofReal_pos.mpr hprod
          exact lt_of_lt_of_le hofReal (lovaszLocalLemma A hA hdg hx₀ hx₁ hLLL)
        ```
        Each factor `1 - x i > 0` (`sub_pos.mpr (hx₁ i)`), so `∏ i, (1 - x i) > 0` by
        `Finset.prod_pos` (applies directly to the unindexed `∏ i, …`: it is definitionally
        `∏ i ∈ Finset.univ, …`, same defeq fact as in item 60.5); lift to
        `0 < ofReal (∏ i, (1 - x i))` via `ENNReal.ofReal_pos.mpr`; chain with
        `lovaszLocalLemma` via `lt_of_lt_of_le`. ~12 lines.
    - **prep**
        - `lovaszLocalLemma` (item 60.5) — same binder shape, conclusion `ENNReal.ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)`.
        - `Finset.prod_pos` — `(h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i` (`Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:107`). Works directly on the unindexed `∏ i, (1 - x i)` (defeq to the `∈ Finset.univ` product); NO `Fintype.prod_pos` exists in mathlib v4.32.0 (grep-verified: only List/Multiset/Finset variants) and none is needed.
        - `sub_pos` — `0 < a - b ↔ b < a`, `@[simp]`, generated by `@[to_additive (attr := simp) sub_pos]` from `one_lt_div'` (`Mathlib/Algebra/Order/Group/Unbundled/Basic.lean:602-603`); NOT the canonically-ordered `tsub_pos_iff_lt` (`Mathlib/Algebra/Order/Sub/Basic.lean:117`) which has a different typeclass shape. Used as `sub_pos.mpr (hx₁ i) : 0 < 1 - x i`.
        - `ENNReal.ofReal_pos` — `0 < ofReal p ↔ 0 < p` (`Mathlib/Data/ENNReal/Real.lean:176`). Used as `ENNReal.ofReal_pos.mpr hprod`.
        - `lt_of_lt_of_le` — chaining strict and non-strict inequalities (`a < b → b ≤ c → a < c`).
        - `omit [DecidableEq ι] in` — required: without it the linter warns `automatically included section variable(s) unused in theorem … [DecidableEq ι]` (compile-verified BOTH ways by this item's Survey: with omit, exit 0 empty output; without, the warning fires). Docstring goes AFTER the omit line, matching item 60.5's layout; no `@[simp]`.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Write `lovaszLocalLemma_pos` (existence form, `0 < μ (⋂ i, (A i)ᶜ)`) from `lovaszLocalLemma` via the 3-line chain `Finset.prod_pos` → `ENNReal.ofReal_pos.mpr` → `lt_of_lt_of_le` (Survey compile-verified warning-free via stdin, exit 0; `omit [DecidableEq ι] in` required — negative test fires the unused-section-variable warning; no `@[simp]`); then integrate after `lovaszLocalLemma` in `LovaszLocal.lean` | Proved exactly as surveyed: `omit [DecidableEq ι] in`, docstring, theorem `lovaszLocalLemma_pos` with the three `have`s — `hprod : 0 < ∏ i, (1 - x i)` by `Finset.prod_pos (fun i hi => sub_pos.mpr (hx₁ i))`, `hofReal : 0 < ENNReal.ofReal (∏ i, (1 - x i))` by `ENNReal.ofReal_pos.mpr hprod`, closed by `lt_of_lt_of_le hofReal (lovaszLocalLemma A hA hdg hx₀ hx₁ hLLL)`. Tmp file: 29 lines, warning-free, no `sorry`/`axiom`/`admit`/`native_decide`/`#`. | Re-verified independently: tmp `lake env lean` exit 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`; 29 lines (well under the 500-line limit). Statement matches item 80.1's informal spec exactly: binder shape identical to `lovaszLocalLemma` (`IsDependencyGraph (μ := μ) G A`, `[DecidableRel G.Adj]`), conclusion `0 < μ (⋂ i, (A i)ᶜ)`, `omit [DecidableEq ι] in`, no `@[simp]`. `#print axioms LovaszLocal.lovaszLocalLemma_pos` = [propext, Classical.choice, Quot.sound] — only the standard set. Integrated into `LovaszLocal.lean` after `lovaszLocalLemma`, before `end LovaszLocal` (omit line + docstring + theorem + proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds. Next: item 80.5 (`lovaszLocalLemma_probReal`). | `tmp_lovasz_pos.lean` |

### 80.5. lovaszLocalLemma_probReal

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **ℝ-valued corollary** via `μ.real` (mathlib v4.32.0's replacement for the removed
        `ProbabilityTheory.probReal`): under the same hypotheses,
        $$\prod_i (1 - x_i) \le \mu.\mathrm{real}\Bigl(\bigcap_i \overline{A_i}\Bigr).$$
    - proof: |
        Survey compile-verified (stdin, exit 0, empty output) the whole theorem as a one-liner:
        `exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ (⋂ i, (A i)ᶜ))).mp
        (lovaszLocalLemma A hA hdg hx₀ hx₁ hLLL)` — the `.mp` turns
        `ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)` into
        `∏ i, (1 - x i) ≤ ENNReal.toReal (μ (⋂ i, (A i)ᶜ))`, which is definitionally
        `∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)` (`Measure.real` unfolds to `(μ s).toReal`), so
        no `measureReal_def` rewrite is needed. `hb : b ≠ ∞` is an EXPLICIT hypothesis of
        `ofReal_le_iff_le_toReal` and cannot be left as a metavariable — supply
        `measure_ne_top μ (⋂ i, (A i)ᶜ)` directly (verified by grep of
        `Mathlib/Data/ENNReal/Real.lean:262`). `omit [DecidableEq ι] in` required (negative test
        fires the unused-section-variable warning); docstring after the omit line; no `@[simp]`
        (inequality conclusion). ~12 lines total.
    - **prep**
        - `lovaszLocalLemma` (item 60.5).
        - `Measure.real` — protected def `(μ : Measure α) (s : Set α) : ℝ := (μ s).toReal`
          (`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:101`); field notation `μ.real s`
          resolves; `measureReal_def`/`Measure.real_def` (`μ.real s = (μ s).toReal`, rfl, :105)
          NOT needed — definitional equality suffices.
        - `ENNReal.ofReal_le_iff_le_toReal` — `{a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) :
          ofReal a ≤ b ↔ a ≤ ENNReal.toReal b` (`Mathlib/Data/ENNReal/Real.lean:262`).
          `hb` is explicit: the naive `.mp` without it does not compile.
        - `measure_ne_top` — `(μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞`
          (`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean:55`); `[IsFiniteMeasure μ]`
          synthesized from `[IsProbabilityMeasure μ]` via
          `IsZeroOrProbabilityMeasure.toIsFiniteMeasure`
          (`Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:52`) — same instance chain
          already used in `measure_bset_insert` of the main file.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Write `lovaszLocalLemma_probReal` (ℝ-valued corollary, `∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)`) from `lovaszLocalLemma` via `ENNReal.ofReal_le_iff_le_toReal` with explicit `hb` = `measure_ne_top μ (⋂ i, (A i)ᶜ)` (Survey compile-verified warning-free via stdin, exit 0; negative omit test fires the unused-section-variable warning; no `@[simp]`); then integrate after `lovaszLocalLemma_pos` in `LovaszLocal.lean` | Proved exactly as surveyed: `omit [DecidableEq ι] in`, docstring, theorem `lovaszLocalLemma_probReal` closed by the one-liner `exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ (⋂ i, (A i)ᶜ))).mp (lovaszLocalLemma A hA hdg hx₀ hx₁ hLLL)` — `.mp` converts `ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)` into the goal, which is definitionally `∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)` via `Measure.real` unfolding, so no `measureReal_def` rewrite needed. Tmp file: 29 lines, warning-free, no `sorry`/`axiom`/`admit`/`native_decide`/`#`. | Re-verified independently: tmp `lake env lean` exit 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`; 29 lines (well under the 500-line limit). Statement matches item 80.5's informal spec exactly: binder shape identical to `lovaszLocalLemma` (`IsDependencyGraph (μ := μ) G A`, `[DecidableRel G.Adj]`), conclusion `∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)`, `omit [DecidableEq ι] in`, docstring after omit line, no `@[simp]`. `#print axioms LovaszLocal.lovaszLocalLemma_probReal` = [propext, Classical.choice, Quot.sound] — only the standard set. Integrated into `LovaszLocal.lean` after `lovaszLocalLemma_pos`, before `end LovaszLocal` (omit line + docstring + theorem + proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds. This was the last in-scope item (group 90 skipped by decision). | `tmp_lovasz_probReal.lean` |

### 80.25. lovaszLocalLemma_exists

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Existence-witness corollary** (from the GPT review 2026-08-15, API polish): under the same
        hypotheses as `lovaszLocalLemma`, there is an outcome that avoids every bad event:
        $$\exists \omega,\ \forall i,\ \omega \notin A_i.$$
        Lean: same binder shape as `lovaszLocalLemma` (`(A) (hA) {G} [DecidableRel G.Adj]
        (hdg : IsDependencyGraph (μ := μ) G A) {x} (hx₀) (hx₁) (hLLL)`), conclusion
        `∃ ω, ∀ i, ω ∉ A i`; `omit [DecidableEq ι] in`; no `@[simp]`.
    - proof: |
        From `lovaszLocalLemma_pos` (item 80.1): `0 < μ (⋂ i, (A i)ᶜ)`. Positive measure implies
        nonempty via the direct mathlib lemma `nonempty_of_measure_ne_zero` (pinned, see prep) —
        the by-contra route through `measure_empty` is NOT needed (fallback names verified and
        recorded in prep as unused). Destruct the nonempty witness, then close the forall by
        `simpa` (`Set.mem_iInter` is `@[simp]`; `ω ∈ (A i)ᶜ` is defeq to `ω ∉ A i`). Whole
        theorem compile-verified warning-free by this item's Survey (attempt 1) via
        `lake env lean /dev/stdin` — exit 0, empty output:
        ```
        omit [DecidableEq ι] in
        theorem lovaszLocalLemma_exists (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))) :
            ∃ ω, ∀ i, ω ∉ A i := by
          obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero
            (ne_of_gt (lovaszLocalLemma_pos A hA hdg hx₀ hx₁ hLLL))
          refine ⟨ω, ?_⟩
          simpa using hω
        ```
        ~11 lines. Notes: `ne_of_gt` (core, always in scope) converts
        `0 < μ (⋂ i, (A i)ᶜ)` to `μ (⋂ i, (A i)ᶜ) ≠ 0` (Portmanteau-style `hpos.ne'` also
        works); `obtain ⟨ω, hω⟩` destructs `(⋂ i, (A i)ᶜ).Nonempty`, which is `Set.Nonempty` =
        `∃ x, x ∈ s` (two binders). **Pitfall (compile-observed, attempt 1):** `simpa using hω`
        directly after the `obtain` FAILS — the goal is an ∃ and `simpa` does not introduce the
        witness; the `refine ⟨ω, ?_⟩` line is required.
    - **prep**
        - `lovaszLocalLemma_pos` (item 80.1) — `0 < μ (⋂ i, (A i)ᶜ)`.
        - `nonempty_of_measure_ne_zero` — `(h : μ s ≠ 0) : s.Nonempty`
          (`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:189`; PINNED 2026-08-15). Lives
          DIRECTLY in namespace `MeasureTheory` (the file's `end Measure` is at :155), so plain
          `open MeasureTheory` resolves it unqualified — same situation as `measure_ne_top`.
          Internal proof: `Set.nonempty_iff_ne_empty` (`s.Nonempty ↔ s ≠ ∅`,
          `Mathlib/Data/Set/Basic.lean:434`) + `measure_empty`.
        - `Set.mem_iInter` — `(x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i`
          (`Mathlib/Order/SetNotation.lean:246`, `@[simp]`) — applied by `simpa` to the witness.
        - `ne_of_gt` — core lemma `a > b → a ≠ b` (always in scope); converts the strict
          positivity into the `≠ 0` hypothesis of the pinned lemma.
        - `measure_empty` — `μ ∅ = 0`, `@[simp]`, via `OuterMeasureClass.measure_empty`
          (`Mathlib/MeasureTheory/OuterMeasure/Basic.lean:48`) through
          `Measure.instOuterMeasureClass` (`MeasureSpaceDef.lean:94`) — consumed only INTERNALLY
          by `nonempty_of_measure_ne_zero`. REMOVED (by-contra fallback route, verified to exist
          but unused by the primary proof): `Set.not_nonempty_iff_eq_empty` —
          `¬s.Nonempty ↔ s = ∅` (`Mathlib/Data/Set/Basic.lean:429`).
        - Note for Proof (warning-free form, compile-tested 2026-08-15 BOTH ways): with the full
          variable block re-declared, the negative test (no omit) fires exactly
          `automatically included section variable(s) unused in theorem … [DecidableEq ι]`
          (linter suggests `omit [DecidableEq ι] in theorem ...`); `[Fintype ι]` is NOT flagged.
          With `omit [DecidableEq ι] in` (docstring AFTER the omit line, item 60.5 layout):
          exit 0, empty output.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Write `lovaszLocalLemma_exists` (`∃ ω, ∀ i, ω ∉ A i`) from `lovaszLocalLemma_pos` via the pinned lemma `MeasureTheory.nonempty_of_measure_ne_zero` (MeasureSpaceDef.lean:189, direct mathlib lemma — no by-contra needed): `obtain ⟨ω, hω⟩` + `refine ⟨ω, ?_⟩` + `simpa using hω` (Survey compile-verified warning-free via stdin, exit 0; pitfall: simpa without refine fails on the ∃ goal; negative omit test fires exactly the `[DecidableEq ι]` warning; `omit [DecidableEq ι] in`; NO `@[simp]` — theorem with hypotheses, ∃-conclusion); then integrate after `lovaszLocalLemma_probReal` in `LovaszLocal.lean` | Proved exactly the Survey's sketch in a 29-line tmp file: `obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero (ne_of_gt (lovaszLocalLemma_pos A hA hdg hx₀ hx₁ hLLL))`, then `refine ⟨ω, ?_⟩` + `simpa using hω`. Tmp compiles via `lake env lean` exit 0, no output; binder shape identical to `lovaszLocalLemma_pos`; `omit [DecidableEq ι] in` before the docstring (item 60.5 layout); no `@[simp]`. | Independently re-verified: tmp `lake env lean` exit 0, no output; LSP diagnostics empty; 29 lines; grep for sorry/axiom/admit/native_decide/# clean. Statement matches the 80.25 informal exactly (same binder shape, `∃ ω, ∀ i, ω ∉ A i`, `omit [DecidableEq ι] in`, no `@[simp]`). Integrated into `LovaszLocal.lean` after the 90.10 strong-form `IsDependencyGraph.strong`, before `end LovaszLocal` (not after `lovaszLocalLemma_probReal` as the Goal cell says — section order changed since the Survey ran; final placement follows the orchestrator's instruction); tmp file deleted. Main file: `lake env lean` exit 0, no warnings; LSP diagnostics empty; `lake build StatsMLlib.Probability.LovaszLocal` succeeds. Done. | `tmp_lovasz_exists.lean` |

*PR-2 scope — symmetric forms (added 2026-08-15, Planner): items 80.10/80.15/80.20 fill the
numbering gaps left in the PR-1 plan. Listed after 80.25 to keep the PR-1 block untouched; all
three live in the same file `StatsMLlib/Probability/LovaszLocal.lean` and consume only the
completed PR-1 API (`lovaszLocalLemma_pos`, item 80.1).*

### 80.30. lovaszLocalLemma_symmetric_optimalWeight (rename)

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Rename** `lovaszLocalLemma_symmetric_sharp` to `lovaszLocalLemma_symmetric_optimalWeight`
        (GPT review v2 naming fix): the condition `(d+1)^(d+1) · p ≤ d^d` is the optimal constant
        for the UNIFORM-weight choice `x = 1/(d+1)` (the maximizer of `x(1-x)^d`), not
        Shearer-type global sharpness. Rename the declaration, its use in
        `lovaszLocalLemma_symmetric`, the module docstring entries, and replace the
        `(gpt-notes §5.1)` docstring reference with [alonSpencer2016].
    - proof: |
        Pure rename — no proof change. Update all reference sites and rebuild.
    - **prep**
        - `lovaszLocalLemma_symmetric_sharp` (item 80.10) — the declaration being renamed.
        - `lovaszLocalLemma_symmetric` (item 80.15) — its only in-file consumer.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Rename `lovaszLocalLemma_symmetric_sharp` to `lovaszLocalLemma_symmetric_optimalWeight` everywhere (declaration, use-site in `lovaszLocalLemma_symmetric`, module docstring); replace `(gpt-notes §5.1)` with [alonSpencer2016]; reword weak/strong docstrings to avoidance-event/generated-σ-algebra formulations | Done directly by the orchestrator (pure rename, no proof change): 5 edits to `LovaszLocal.lean`; grep confirms zero `symmetric_sharp`/`gpt-notes` occurrences remain; `lake env lean` exit 0 and `lake build StatsMLlib.Probability.LovaszLocal` succeeds (1923 jobs) | Same — re-verified: rename complete, build green | — |

### 80.10. lovaszLocalLemma_symmetric_sharp

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
    - note: renamed to `lovaszLocalLemma_symmetric_optimalWeight` by item 80.30 (GPT review v2).
- **informal**
    - statement: |
        **Sharp symmetric LLL without `e`** (gpt-notes §5.1, the internal sharp form of survey B
        §4.1): if every bad event has probability at most $p$, every vertex of the dependency graph
        has degree at most $d \ge 1$, and $p$ is below the sharp threshold
        $$p \le \frac{d^d}{(d+1)^{d+1}},$$
        then some outcome avoids all bad events: $0 < \mu\bigl(\bigcap_i \overline{A_i}\bigr)$.
        Lean statement (binder shape follows the 80.1 convention; `p`/`d` implicit like `x`):
        ```lean
        omit [DecidableEq ι] in
        theorem lovaszLocalLemma_symmetric_sharp (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {p : ℝ} (hp : ∀ i, μ (A i) ≤ ENNReal.ofReal p) {d : ℕ}
            (hd : ∀ i, G.degree i ≤ d) (hd₁ : 1 ≤ d)
            (hcond : ((d : ℝ) + 1) ^ (d + 1) * p ≤ (d : ℝ) ^ d) :
            0 < μ (⋂ i, (A i)ᶜ)
        ```
        **Smallness condition — DECISION (Planner 2026-08-15): multiplicative form
        `(d+1)^(d+1) · p ≤ d^d`, NOT the fractional `p ≤ d^d/(d+1)^(d+1)`.** Justification:
        (1) no division in the hypothesis — no `(d+1) ≠ 0` side condition and no sign assumption on
        `p` in the statement; (2) uniform API with the classical `ep(d+1) ≤ 1` of 80.15 and the
        `4pd ≤ 1` of 80.20 (all three smallness conditions are "positive factor times p ≤ positive
        factor"); (3) the one-time conversion to the fractional form is a single `le_div_iff₀`
        inside the proof, where positivity of `(d+1)^(d+1)` is established locally (`pow_pos`).
        **`d = 0` — DECISION (Planner 2026-08-15): excluded by the explicit hypothesis
        `hd₁ : 1 ≤ d`; there is NO d = 0 branch.** The task's sketch (at d = 0 use `x i := p`,
        needing `p < 1` derived from the smallness condition) fails twice: (a) at `d = 0` the
        multiplicative condition reduces to `1 · p ≤ 0^0 = 1`, i.e. only `p ≤ 1` — strictness is
        not derivable; (b) the theorem itself is FALSE at d = 0. Counterexample:
        `Ω = PUnit` (Dirac), `ι = {0, 1}`, `A i = Set.univ`, `G` edgeless, `p = 1`: `hp` holds
        (`μ univ = 1 ≤ ofReal 1`), `hd` holds (all degrees 0), `hcond` holds (`1·1 ≤ 1`), `hdg`
        holds (`IndepSet univ (bset A S)` — both sides measure `μ (bset A S)`), yet
        `μ (⋂ i, (A i)ᶜ) = μ ∅ = 0`. The d = 0 case is instead covered by 80.15, whose
        `ep(d+1) ≤ 1` condition at d = 0 yields `p ≤ 1/e < 1`. NOTE: no `0 ≤ p` hypothesis is
        needed anywhere in this item (the only lift to ENNReal is the unconditional
        `ENNReal.ofReal_le_ofReal`).
    - proof: |
        Apply item 80.1 (`lovaszLocalLemma_pos`) with the constant weights
        `x := fun _ => 1 / ((d : ℝ) + 1)`. Let `hdpos : 0 < (d : ℝ) + 1 := by exact_mod_cast
        Nat.succ_pos d` (or `by positivity`).
        - `hx₀ : 0 ≤ 1/(d+1)` — `div_nonneg zero_le_one (le_of_lt hdpos)`.
        - `hx₁ : 1/(d+1) < 1` — `(div_lt_one hdpos).2` with `1 < (d : ℝ) + 1` from
          `have hd₁ℝ : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd₁` then `linarith`
          (this is exactly where `hd₁` is consumed; NOTE `one_div_lt_one` does not exist in
          mathlib v4.32.0 — grep-verified — use `(div_lt_one hdpos).2`).
        - `hLLL` per `i` — the ℝ chain, lifted to ENNReal only at the end:
          $$p \le \frac{d^d}{(d+1)^{d+1}} = \frac{1}{d+1}\Bigl(\frac{d}{d+1}\Bigr)^d
          \le \frac{1}{d+1}\Bigl(\frac{d}{d+1}\Bigr)^{G.\mathrm{degree}\,i}
          = x_i \prod_{j \in \Gamma(i)} (1 - x_j),$$
          where $|\Gamma(i)| = G.\mathrm{degree}\,i \le d$ (`hd i`).
          1. `p ≤ d^d/(d+1)^(d+1)`:
             `(le_div_iff₀ (pow_pos hdpos (d+1))).mpr (by simpa [mul_comm] using hcond)`.
          2. `d^d/(d+1)^(d+1) = (1/(d+1))·(d/(d+1))^d` — **real-algebra step needing care**:
             `rw [div_pow]` then `field_simp [hdnz, pow_ne_zero d hdnz,
             pow_ne_zero (d + 1) hdnz]` with `hdnz : ((d : ℝ) + 1) ≠ 0 := ne_of_gt hdpos`
             (field_simp does NOT derive the pow-nonzero goals from `hdnz` alone — pass them
             explicitly; verified 2026-08-15), then `ring`.
          3. `(d/(d+1))^d ≤ (d/(d+1))^(G.degree i)` — `pow_le_pow_of_le_one` with
             `ha₀ : 0 ≤ d/(d+1)` (`div_nonneg (Nat.cast_nonneg d) (le_of_lt hdpos)`),
             `ha₁ : d/(d+1) ≤ 1` (`(div_le_one hdpos).2 (by linarith)` — plain `linarith`
             proves `(d : ℝ) ≤ d + 1` unaided; do NOT feed `Nat.cast_nonneg d` to `linarith`
             here — the unannotated cast sticks typeclass search (`IsOrderedRing ?m`),
             verified 2026-08-15), `hmn := hd i`.
          4. multiply by `0 ≤ 1/(d+1)` (hx₀): `mul_le_mul_of_nonneg_left hpow hx₀i`.
          5. `(1/(d+1))·(d/(d+1))^(G.degree i) = x i · ∏_{j∈Γ(i)} (1 - x j)` — per-factor
             `1 - 1/(d+1) = d/(d+1)` via `field_simp [ne_of_gt hdpos]; ring` (as a local
             `hfactor (j : ι)`); then `simp_rw [hfactor]`, `rw [Finset.prod_const]`
             (`∏ _x ∈ s, b = b ^ #s`), `rfl` — the exponent `#(G.neighborFinset i)` is defeq
             `G.degree i` (so `SimpleGraph.card_neighborFinset_eq_degree` is not needed).
             PITFALL (verified 2026-08-15): `simp only [hfactor]` then plain `simp` FAILS —
             simp splits via a `mul_left_cancel`-style lemma and leaves the goal
             `↑d + 1 = 0`; use `simp_rw [hfactor]` + targeted `rw` + `rfl` instead.
          6. lift: `μ (A i) ≤ ENNReal.ofReal p ≤ ENNReal.ofReal (x i * ∏ …)` via
             `le_trans (hp i) (ENNReal.ofReal_le_ofReal hpx)` — `ofReal_le_ofReal` is
             unconditional, so no `0 ≤ p` is needed anywhere.
        Close with `let x : ι → ℝ := fun _ => 1 / ((d : ℝ) + 1)` and
        `exact lovaszLocalLemma_pos A hA hdg hx₀ hx₁ hLLL` (the `{x}` of item 80.1 is inferred
        from `hx₀`).
        Survey compiled the complete proof warning-free via stdin 2026-08-15 (exit 0); it is
        ~55 lines — the real-algebra glue (steps 2 and 5) is the bulk.
- **prep**
    - `lovaszLocalLemma_pos` (item 80.1) — same binder shape
      (`(A) (hA) {G} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A) {x} (hx₀)
      (hx₁) (hLLL)`); applied with `x := fun _ => 1 / ((d : ℝ) + 1)`.
    - `ENNReal.ofReal_le_ofReal` — `(h : p ≤ q) : ofReal p ≤ ofReal q`
      (`Mathlib/Data/ENNReal/Real.lean:137`, item 60.1) — unconditional; the single lift of the
      ℝ chain (no `0 ≤ p` needed in this item).
    - `SimpleGraph.degree` — def, `#(G.neighborFinset v)` (rfl with card)
      (`Mathlib/Combinatorics/SimpleGraph/Finite.lean:200`); `[Fintype ι]` IS used (via the
      neighborSet Fintype instance from `[Fintype ι] [DecidableRel G.Adj]`, survey B §1.2).
    - `SimpleGraph.card_neighborFinset_eq_degree` — `#(G.neighborFinset v) = G.degree v := rfl`
      (`Finite.lean:203`) — available for step 5's exponent rewrite, but NOT needed in the
      verified route: `#(G.neighborFinset i)` is defeq `G.degree i`, plain `rfl` closes.
    - `Finset.prod_const` — `∏ _x ∈ s, b = b ^ #s`
      (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:629`, `@[simp]` via to_additive) —
      the Γ(i)-product becomes a power.
    - `pow_le_pow_of_le_one` — `[PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) {m n : ℕ}
      (hmn : m ≤ n) : a ^ n ≤ a ^ m` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:393`) —
      step 3 with `a := d/(d+1)`, `hmn := hd i`.
    - `div_nonneg` — `(ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b`
      (`Algebra/Order/GroupWithZero/Basic.lean:883`) — step 3's `ha₀`.
    - `div_le_one` — `(hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b`
      (`Mathlib/Algebra/Order/Field/Basic.lean:43`) — step 3's `ha₁` from `d ≤ d + 1`
      (plain `linarith` — see the informal proof step 3 note).
    - `div_lt_one` — `(hb : 0 < b) : a / b < 1 ↔ a < b` (`Algebra/Order/Field/Basic.lean:47`) —
      hx₁. NOTE: `one_div_lt_one` does NOT exist in mathlib v4.32.0 (grep-verified 2026-08-15).
    - `le_div_iff₀` — `(hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b`
      (`Algebra/Order/GroupWithZero/Basic.lean:1134`) — step 1, with `c := (d+1)^(d+1)`.
    - `pow_pos` — `[ZeroLEOneClass M₀] (ha : 0 < a) : ∀ n, 0 < a ^ n`
      (`Algebra/Order/GroupWithZero/Basic.lean:541`, `@[simp]`) — positivity of `(d+1)^(d+1)`.
    - `pow_ne_zero` — `(ha : a ≠ 0) (n : ℕ) : a ^ n ≠ 0` — step 2's `field_simp` side goals
      (field_simp does NOT derive `(d+1)^n ≠ 0` from `(d+1) ≠ 0` by itself — pass explicitly,
      verified 2026-08-15).
    - `mul_le_mul_of_nonneg_left` — `[PosMulMono α] (hbc : b ≤ c) (ha : 0 ≤ a) : a * b ≤ a * c`
      (`Mathlib/Algebra/Order/GroupWithZero/Defs.lean:226`) — step 4.
    - `div_pow` — `(a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n`
      (`Mathlib/Algebra/Group/Basic.lean:585`) — step 2's rewrite.
    - `Nat.cast_nonneg` / `Nat.cast_pos` — `0 ≤ (n : ℝ)` / `0 < (n : ℝ) ↔ 0 < n`
      (`Mathlib/Data/Nat/Cast/Order/Ring.lean:30` / `:55`) — cast positivity for `d`, `d + 1`.
    - `field_simp`, `ring_nf`, `linarith`, `positivity` — the real-algebra glue of steps 2 and 5
      (tactics; transitively available — item 60.1 already uses `linarith`).
    - `sub_nonneg` — `0 ≤ a - b ↔ b ≤ a` (item 40.15-verified) — alternative for
      `0 ≤ 1 - 1/(d+1)` if needed.
    - Note for Proof (established layout, items 60.5/80.1): `omit [DecidableEq ι] in` before the
      docstring — the statement does not use `DecidableEq ι` (`[Fintype ι]` IS used via
      `G.degree`); no `@[simp]` (inequality theorem with hypotheses).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove the full theorem: constant weights `x i := 1/(d+1)`; ℝ chain `p ≤ d^d/(d+1)^(d+1) = (1/(d+1))·(d/(d+1))^d ≤ (1/(d+1))·(d/(d+1))^(G.degree i) = x i · ∏ (1 - x j)` lifted via `ENNReal.ofReal_le_ofReal`; close with `lovaszLocalLemma_pos`. Survey compiled the complete proof warning-free via stdin (exit 0); three route refinements recorded in the informal proof (field_simp nonzero args, plain `linarith` for `ha₁`, `simp_rw`+`rw`+`rfl` for step 5). | Full theorem proved (no separate Proof role this attempt — Survey produced the complete compile-verified proof, Setup materialized it): constant weights `x i := 1/((d:ℝ)+1)`; `hdpos`/`hdnz` from `Nat.succ_pos d`; `hx₀` by `div_nonneg`, `hx₁` by `(div_lt_one hdpos).2` with `hd₁` cast via `exact_mod_cast` then `linarith` (the only `hd₁` use-site); `hLLL` is the six-step ℝ chain of the informal proof (`le_div_iff₀`+`pow_pos`; `div_pow`+`field_simp`+`ring`; `pow_le_pow_of_le_one` at `hd i`; `mul_le_mul_of_nonneg_left`; per-factor `simp_rw [hfactor]` + `rw [Finset.prod_const]` + `rfl`), lifted once by `ENNReal.ofReal_le_ofReal`, closed with `lovaszLocalLemma_pos A hA hdg hx₀ hx₁ hLLL`. Tmp compiled warning-free (exit 0), zero sorries, 73 lines. | Re-verified independently: `lake env lean` on the tmp exits 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 75 lines (under the 500-line limit); `#print axioms` via Bash stdin returns exactly `[propext, Classical.choice, Quot.sound]` (acceptable). Statement matches the informal spec exactly: `hp`, `hd : ∀ i, G.degree i ≤ d`, `hd₁ : 1 ≤ d`, multiplicative `hcond : ((d:ℝ)+1)^(d+1) * p ≤ (d:ℝ)^d`, conclusion `0 < μ (⋂ i, (A i)ᶜ)`, `omit [DecidableEq ι] in`, no `@[simp]`. Integrated into `LovaszLocal.lean` after `lovaszLocalLemma_exists`, before `end LovaszLocal` (omit line + docstring + theorem + proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds. Next: item 80.15 (`lovaszLocalLemma_symmetric`). | `tmp_lovasz_symmetric_sharp.lean` |

### 80.15. lovaszLocalLemma_symmetric

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Classical symmetric LLL** (`e·p·(d+1) ≤ 1`, gpt-notes Corollary 5.1.1 / Alon--Spencer
        Thm 5.1.1): if every bad event has probability at most $p$ and every vertex has degree at
        most $d$, with $e\,p\,(d+1) \le 1$, then $0 < \mu\bigl(\bigcap_i \overline{A_i}\bigr)$.
        ```lean
        omit [DecidableEq ι] in
        theorem lovaszLocalLemma_symmetric (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {p : ℝ} (hp : ∀ i, μ (A i) ≤ ENNReal.ofReal p) {d : ℕ}
            (hd : ∀ i, G.degree i ≤ d) (hcond : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
            0 < μ (⋂ i, (A i)ᶜ)
        ```
        **The `0 ≤ p` question — DECISION (Planner 2026-08-15): NO `0 ≤ p` hypothesis; the
        planned derivation of `0 ≤ p` from `hcond` is IMPOSSIBLE, and the theorem is true and
        provable without it.** Derivation-refutation steps (as requested): if `p = -1`, `d = 0`,
        then `e·(-1)·1 = -e ≤ 1`, so `hcond` holds with `p < 0` — `hcond` alone does not force
        `p ≥ 0` (the "positivity of `Real.exp 1` and `d+1`" argument only shows the factor
        `e·(d+1)` is positive, which bounds `p` from ABOVE, not below). `hp` does not force it
        either: for `p < 0`, `ofReal p = 0` makes all `A i` null, consistent with any data.
        Consequently the d = 0 branch uses the constant `x i := 1/2` (needs only
        `p ≤ 1/e ≤ 1/2`, no sign of `p`) instead of the task sketch's `x i := p`. The `x i := p`
        route is recorded as fallback: it needs an explicit hypothesis `hp₀ : 0 ≤ p` plus
        `p < 1` (`p ≤ 1/e < 1` via `1 < e`) — pick only if the Survey prefers the classical
        statement shape over hypothesis-minimality.
    - proof: |
        Case split `by_cases hd1 : 1 ≤ d`.
        - **`hd1 : 1 ≤ d`** — reduce to 80.10 by deriving its multiplicative smallness condition
          `((d+1)^(d+1))·p ≤ d^d`:
          1. `p ≤ 1/(e·(d+1))`: `(le_div_iff₀ (mul_pos (Real.exp_pos 1) hdpos)).mpr
             (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcond)`.
          2. `1/(e·(d+1)) ≤ d^d/(d+1)^(d+1)` — by the sub-chain `1/e ≤ (d/(d+1))^d`:
             - `(d/(d+1))^d = 1/((1+1/d)^d)`: `d/(d+1) = 1/(1+1/d)` via
               `field_simp [ne_of_gt hdposℝ]` where `hdposℝ : 0 < (d : ℝ)` from `hd1`
               (`Nat.cast_pos.mpr (Nat.succ_le_iff.mp hd1)`); then rfl (`1/x = x⁻¹`), `inv_pow`,
               rfl.
             - `(1+1/d)^d ≤ e`: `Real.one_add_inv_pow_le_exp` with `n := d` — statement
               `(1 + (n : ℝ)⁻¹) ^ n ≤ exp 1`, NO hypothesis (usable for all d); `simpa` (since
               `(d : ℝ)⁻¹ = 1/d`).
             - `1/e ≤ 1/((1+1/d)^d)`: `one_div_le_one_div_of_le (pow_pos (by positivity :
               0 < 1 + 1/d) d) hpow` (signature `(ha : 0 < a) (h : a ≤ b) : 1/b ≤ 1/a`;
               `0 < 1/d` via `one_div_pos.mpr hdposℝ`).
             - assemble: `1/(e(d+1)) = (1/(d+1))·(1/e)` via `← one_div_mul_one_div` +
               `mul_comm`; `d^d/(d+1)^(d+1) = (1/(d+1))·(d/(d+1))^d` (80.10 step 2);
               `mul_le_mul_of_nonneg_left h_inv (by positivity : 0 ≤ 1/(d+1))`.
          3. `((d+1)^(d+1))·p ≤ d^d`: `(le_div_iff₀ (pow_pos hdpos (d+1))).mp hp_frac` +
             `simpa [mul_comm]`.
          4. `exact lovaszLocalLemma_symmetric_sharp A hA hdg hp hd hd1 hcond'` (item 80.10).
        - **`¬ hd1` (so `d = 0`)** — `have hd0 : d = 0 := Nat.eq_zero_of_le_zero
          (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hd1))` (both core Init lemmas; alternative:
          `omega`); `subst d`. Then:
          - all degrees are 0: `hdeg0 : G.degree i = 0 := Nat.eq_zero_of_le_zero (hd i)`;
            `(SimpleGraph.degree_eq_zero).mp hdeg0 : G.IsIsolated i`;
            `IsIsolated.neighborFinset_eq_empty : G.neighborFinset i = ∅`.
          - `p ≤ 1/e`: `(le_div_iff₀ (Real.exp_pos 1)).mpr (by simpa using hcond)` — at d = 0,
            `hcond` is `e·p·1 ≤ 1`.
          - `1/e ≤ 1/2`: `one_div_le_one_div_of_le (by norm_num : 0 < (2 : ℝ))
            (by simpa using (Real.add_one_le_exp 1) : (2 : ℝ) ≤ Real.exp 1)`;
            so `p ≤ 1/2` by `le_trans`.
          - apply item 80.1 with `x := fun _ => 1/2` (`hx₀`/`hx₁` by `norm_num`): `hLLL'` is
            `μ (A i) ≤ ofReal p ≤ ofReal ((1/2) · ∏_{Γ(i)} (1 - 1/2))` — rewrite
            `IsIsolated.neighborFinset_eq_empty`, `Finset.prod_empty` (`@[simp]`), `mul_one`,
            then `ENNReal.ofReal_le_ofReal` with the `p ≤ 1/2` chain.
        Est. 80–120 lines; the `1/e ≤ (d/(d+1))^d` chain (step 2) is the bulk. Real-algebra
        steps needing care: the `d/(d+1) = 1/(1+1/d)` rewrite (step 2, needs `d ≠ 0` — this is
        the only place `hd1`-positivity enters) and the 80.10 step-2 equality.
        **COMPILE-VERIFIED ROUTE (Survey 2026-08-15, attempt 1) — full working proof, `lake env
        lean` exit 0 with empty output (warning-free), axioms `[propext, Classical.choice,
        Quot.sound]`, 88-line stdin file (75-line theorem body). Deviations from the sketch
        above, all found empirically:**
        - REQUIRED NEW IMPORT: `import Mathlib.Analysis.Complex.Exponential` — `Real.exp`,
          `Real.exp_pos`, `Real.add_one_le_exp`, `Real.one_add_inv_pow_le_exp` are NOT
          transitively available from `LovaszLocal.lean`'s current imports (compile fails with
          `Unknown constant Real.exp` without it). Setup must add it to the tmp; Review must
          add it to the main file at integration.
        - `hfrac : (d : ℝ) / ((d : ℝ) + 1) = (1 + (d : ℝ)⁻¹)⁻¹` — `field_simp [hdnz]` closes it
          ENTIRELY (do NOT append `ring`: "No goals to be solved").
        - the `1/(1+d⁻¹)^d = ((1+d⁻¹)⁻¹)^d` calc step — `rw [inv_pow]` then `simp` (rw handles
          the `∀ n` binder; simp's `one_div` closes the remainder).
        - the `1/(e·(d+1)) = (1/(d+1))·(1/e)` step — `rw [one_div_mul_one_div]; ring` (plain
          `rw [one_div_mul_one_div, mul_comm]` does NOT close: mul_comm flips BOTH sides).
        - the `2 ≤ exp 1` step — `linarith [Real.add_one_le_exp (1 : ℝ)]`; BOTH `simpa using
          (Real.add_one_le_exp 1)` and `norm_num [Real.add_one_le_exp 1]` FAIL (simp/norm_num
          do not normalize `1 + 1` to `2` here — verified both ways).
        - `SimpleGraph.degree_eq_zero` has EXPLICIT `G v` binders (`∀ (G : SimpleGraph ?m) (v :
          ?m) [inst : Fintype ↑(G.neighborSet v)], …`): use `(SimpleGraph.degree_eq_zero G
          i).mp hdeg0` — the projection `(SimpleGraph.degree_eq_zero).mp` fails to elaborate
          ("The environment does not contain Function.mp").
        - the `hdnz1` for the 80.10 step-2 `field_simp` is `((d : ℝ) + 1) ≠ 0` (mirror of
          80.10's `hdnz`); `hdnz : (d : ℝ) ≠ 0` is used only for `hfrac`.
        - `hd0 : d = 0 := by omega` in the second branch (the `Nat.lt_of_not_ge` chain in the
          sketch is the documented fallback).
        ```lean
        import Mathlib.Analysis.Complex.Exponential
        import StatsMLlib.Probability.LovaszLocal

        open MeasureTheory ProbabilityTheory
        open scoped BigOperators ENNReal

        namespace LovaszLocal

        variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
          [Fintype ι] [DecidableEq ι]

        omit [DecidableEq ι] in
        /-- The classical symmetric Lovász local lemma: with `e·p·(d+1) ≤ 1`, some outcome
        avoids all bad events. -/
        theorem lovaszLocalLemma_symmetric (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {p : ℝ} (hp : ∀ i, μ (A i) ≤ ENNReal.ofReal p) {d : ℕ}
            (hd : ∀ i, G.degree i ≤ d) (hcond : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
            0 < μ (⋂ i, (A i)ᶜ) := by
          by_cases hd1 : 1 ≤ d
          · have hdposℝ : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hd1)
            have hdnz : (d : ℝ) ≠ 0 := ne_of_gt hdposℝ
            have hdpos1 : 0 < (d : ℝ) + 1 := by exact_mod_cast Nat.succ_pos d
            have hdnz1 : ((d : ℝ) + 1) ≠ 0 := ne_of_gt hdpos1
            have hp1 : p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) :=
              (le_div_iff₀ (mul_pos (Real.exp_pos 1) hdpos1)).mpr
                (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcond)
            have hfrac : (d : ℝ) / ((d : ℝ) + 1) = (1 + (d : ℝ)⁻¹)⁻¹ := by
              field_simp [hdnz]
            have hpos1 : 0 < 1 + (d : ℝ)⁻¹ := by positivity
            have hpow : (1 + (d : ℝ)⁻¹) ^ d ≤ Real.exp 1 :=
              Real.one_add_inv_pow_le_exp (n := d)
            have h2b : 1 / Real.exp 1 ≤ ((d : ℝ) / ((d : ℝ) + 1)) ^ d := by
              calc
                1 / Real.exp 1 ≤ 1 / (1 + (d : ℝ)⁻¹) ^ d :=
                  one_div_le_one_div_of_le (pow_pos hpos1 d) hpow
                _ = ((1 + (d : ℝ)⁻¹)⁻¹) ^ d := by
                  rw [inv_pow]
                  simp
                _ = ((d : ℝ) / ((d : ℝ) + 1)) ^ d := by
                  rw [← hfrac]
            have h2 : 1 / (Real.exp 1 * ((d : ℝ) + 1)) ≤
                (d : ℝ) ^ d / ((d : ℝ) + 1) ^ (d + 1) := by
              calc
                1 / (Real.exp 1 * ((d : ℝ) + 1)) = (1 / ((d : ℝ) + 1)) * (1 / Real.exp 1) := by
                  rw [one_div_mul_one_div]
                  ring
                _ ≤ (1 / ((d : ℝ) + 1)) * ((d : ℝ) / ((d : ℝ) + 1)) ^ d :=
                  mul_le_mul_of_nonneg_left h2b (div_nonneg zero_le_one (le_of_lt hdpos1))
                _ = (d : ℝ) ^ d / ((d : ℝ) + 1) ^ (d + 1) := by
                  rw [div_pow]
                  field_simp [hdnz1, pow_ne_zero d hdnz1, pow_ne_zero (d + 1) hdnz1]
                  ring
            have hp_frac : p ≤ (d : ℝ) ^ d / ((d : ℝ) + 1) ^ (d + 1) := le_trans hp1 h2
            have hcond' : ((d : ℝ) + 1) ^ (d + 1) * p ≤ (d : ℝ) ^ d := by
              simpa [mul_comm] using (le_div_iff₀ (pow_pos hdpos1 (d + 1))).mp hp_frac
            exact lovaszLocalLemma_symmetric_sharp A hA hdg hp hd hd1 hcond'
          · have hd0 : d = 0 := by omega
            subst d
            have hp1 : p ≤ 1 / Real.exp 1 :=
              (le_div_iff₀ (Real.exp_pos 1)).mpr
                (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcond)
            have h12 : 1 / Real.exp 1 ≤ (1 : ℝ) / 2 := by
              refine one_div_le_one_div_of_le (by norm_num) ?_
              linarith [Real.add_one_le_exp (1 : ℝ)]
            have hp12 : p ≤ (1 : ℝ) / 2 := le_trans hp1 h12
            let x : ι → ℝ := fun _ => (1 : ℝ) / 2
            have hx₀ : ∀ i, 0 ≤ x i := by
              intro i
              dsimp [x]
              norm_num
            have hx₁ : ∀ i, x i < 1 := by
              intro i
              dsimp [x]
              norm_num
            have hLLL : ∀ i,
                μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) := by
              intro i
              have hdeg0 : G.degree i = 0 := Nat.eq_zero_of_le_zero (hd i)
              have hiso : G.IsIsolated i := (SimpleGraph.degree_eq_zero G i).mp hdeg0
              have hchain : p ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j) := by
                calc
                  p ≤ (1 : ℝ) / 2 := hp12
                  _ = x i * ∏ j ∈ G.neighborFinset i, (1 - x j) := by
                    dsimp [x]
                    simp [hiso.neighborFinset_eq_empty]
              exact le_trans (hp i) (ENNReal.ofReal_le_ofReal hchain)
            exact lovaszLocalLemma_pos A hA hdg hx₀ hx₁ hLLL
        ```
        Negative omit test (compile-verified 2026-08-15): without the `omit [DecidableEq ι] in`
        line exactly `automatically included section variable(s) unused in theorem … [DecidableEq
        ι]` fires; `[Fintype ι]` is NOT flagged (as in 80.10). `@[simp]`: NO (inequality theorem
        with hypotheses).
- **prep**
    - `Mathlib.Analysis.Complex.Exponential` (IMPORT, added by Survey 2026-08-15) — REQUIRED NEW
      import: `Real.exp`, `Real.exp_pos`, `Real.add_one_le_exp`, `Real.one_add_inv_pow_le_exp`
      are NOT transitively available from `LovaszLocal.lean`'s current imports (compile-verified
      failure: `Unknown constant Real.exp` without it). Setup adds it to the tmp; Review adds it
      to the main file at integration.
    - `lovaszLocalLemma_symmetric_sharp` (item 80.10) — the `hd1 : 1 ≤ d` branch target;
      hypothesis list matches exactly (`hp`, `hd`, `hd₁ := hd1`, `hcond'`).
    - `lovaszLocalLemma_pos` (item 80.1) — the d = 0 branch, with `x := fun _ => 1/2`.
    - `Real.one_add_inv_pow_le_exp` — `{n : ℕ} : (1 + (n : ℝ)⁻¹) ^ n ≤ exp 1`
      (`Mathlib/Analysis/Complex/Exponential.lean:653`, namespace `Real`, NO hypothesis — the
      classical $(1+1/d)^d \le e$; `d ≠ 0` is needed only for the separate
      `d/(d+1) = 1/(1+1/d)` rewrite, not for this lemma).
    - `Real.exp_pos` — `(x : ℝ) : 0 < exp x` (`Exponential.lean:282`, `@[bound]`) — positivity
      of `e` in step 1 and in the d = 0 branch.
    - `Real.add_one_le_exp` — `(x : ℝ) : x + 1 ≤ Real.exp x` (`Exponential.lean:631`) — `2 ≤ e`
      at `x = 1`, the `1/e ≤ 1/2` step of the d = 0 branch.
    - `Real.one_lt_exp_iff` — `{x : ℝ} : 1 < exp x ↔ 0 < x` (`Exponential.lean:330`) —
      alternative `1 < e` source for the fallback `x i := p` route (`p < 1`); unused by the
      primary `x := 1/2` route.
    - `one_div_le_one_div_of_le` — `(ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a`
      (`Mathlib/Algebra/Order/Field/Basic.lean:69`) — both `1/e` steps.
    - `inv_pow` — `(a : α) : ∀ n : ℕ, a⁻¹ ^ n = (a ^ n)⁻¹` (`Mathlib/Algebra/Group/Basic.lean:411`).
    - `one_div_mul_one_div` — `1 / a * (1 / b) = 1 / (a * b)` (`Algebra/Group/Basic.lean:533`).
    - `le_div_iff₀`, `pow_pos`, `mul_le_mul_of_nonneg_left`, `div_pow`, `one_div_pos`
      (`Algebra/Order/GroupWithZero/Basic.lean:855`), `Nat.cast_pos`, `field_simp`, `positivity` —
      as in 80.10.
    - `pow_le_pow_left₀` — `(ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n`
      (`Algebra/Order/GroupWithZero/Basic.lean:470`) — from the task's name list; NOT consumed by
      the chosen route (the chain uses `one_add_inv_pow_le_exp` directly); kept for the Survey as
      the alternative `(d/(d+1))^d`-monotonicity tool.
    - `Real.exp_nat_mul` — `(x : ℝ) (n : ℕ) : exp (n * x) = exp x ^ n` (`Exponential.lean:231`) —
      from the task's name list; unused by the chosen route (only needed if the proof passes
      through `(exp 1)^d`).
    - `SimpleGraph.degree_eq_zero` — `G.degree v = 0 ↔ G.IsIsolated v`
      (`Combinatorics/SimpleGraph/Finite.lean:208`); aliases `IsIsolated.of_degree_eq_zero`
      (`:211`) and `IsIsolated.neighborFinset_eq_empty` (`:194`, alias of the `@[simp]`
      `neighborFinset_eq_empty` `:188`) — the d = 0 branch's `Γ(i) = ∅`. CORRECTION (verified
      2026-08-15): `G` and `v` are EXPLICIT `∀`-binders — `(SimpleGraph.degree_eq_zero G i).mp
      hdeg0`, NOT `(SimpleGraph.degree_eq_zero).mp` (projection fails to elaborate: "The
      environment does not contain Function.mp").
    - `Nat.eq_zero_of_le_zero` (core Init, used at `Data/Nat/Init.lean:144`), `Nat.lt_succ_iff`
      (core Init, used at `Data/Nat/Init.lean:407`), `Nat.lt_of_not_ge` — `d = 0` from
      `¬ 1 ≤ d`; alternative: `omega`.
    - `Finset.prod_empty` — `∏ x ∈ (∅ : Finset ι), f x = 1` (`@[simp]`) — d = 0 branch hLLL.
    - `inv_le_inv₀` — `(ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a`
      (`Algebra/Order/GroupWithZero/Basic.lean:1218`, grep-verified 2026-08-15) — from the
      task's spot-check list; the chosen route uses `one_div_le_one_div_of_le` instead; kept as
      the equivalent alternative for the `1/e` steps.
    - `linarith` — the `2 ≤ Real.exp 1` step of the d = 0 branch is `linarith
      [Real.add_one_le_exp (1 : ℝ)]`; both `simpa using (Real.add_one_le_exp 1)` and
      `norm_num [Real.add_one_le_exp 1]` FAIL (simp/norm_num do not normalize `1 + 1` to `2`
      here — compile-verified 2026-08-15).
    - `ENNReal.ofReal_le_ofReal` (item 60.1).
    - Note for Proof (established layout): `omit [DecidableEq ι] in` before the docstring; no
      `@[simp]`; the full compile-verified proof is recorded in the informal proof section
      (Survey 2026-08-15). FALLBACK ROUTE (only if the Survey prefers the task's `x i := p`
      sketch): add
      explicit hypothesis `hp₀ : 0 ≤ p` and in the d = 0 branch use `x := fun _ => p` with
      `hx₁` from `p ≤ 1/e < 1` — the `1/e < 1` step via `(div_lt_one (Real.exp_pos 1)).2
      (Real.one_lt_exp_iff.2 zero_lt_one)`.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `lovaszLocalLemma_symmetric` (`e·p·(d+1) ≤ 1`): case split on `1 ≤ d`; the `d ≥ 1` branch derives 80.10's multiplicative `hcond'` via `p ≤ 1/(e·(d+1))` (`le_div_iff₀` with `mul_pos (Real.exp_pos 1) hdpos1`) and `1/(e·(d+1)) ≤ d^d/(d+1)^(d+1)` through `1/e ≤ (d/(d+1))^d` ⇐ `(1+d⁻¹)^d ≤ e` (`Real.one_add_inv_pow_le_exp`) with the fraction identity `d/(d+1) = (1+d⁻¹)⁻¹` (`field_simp [hdnz]`); the `d = 0` branch uses constant weights `x := 1/2` via `p ≤ 1/e ≤ 1/2` (`linarith [Real.add_one_le_exp 1]`), `Γ(i) = ∅` from `(SimpleGraph.degree_eq_zero G i).mp`, closed with `lovaszLocalLemma_pos`. Survey compile-verified the COMPLETE proof via `lake env lean` (exit 0, empty output = warning-free; axioms `[propext, Classical.choice, Quot.sound]`; 88-line stdin file, 75-line theorem body); full proof + five route refinements recorded in the informal proof; prep updated (new import `Mathlib.Analysis.Complex.Exponential`, explicit-binder correction for `degree_eq_zero`, `inv_le_inv₀` grep-verified). | Full theorem proved (no separate Proof role this attempt — Survey produced the complete compile-verified proof, Setup materialized it): `by_cases hd1 : 1 ≤ d`; the `hd1` branch builds `hp1 : p ≤ 1/(e·(d+1))`, the `(1+d⁻¹)^d ≤ e` chain via `Real.one_add_inv_pow_le_exp` (`hfrac` closed by `field_simp [hdnz]` alone, `inv_pow`+`simp`, `one_div_mul_one_div`+`ring`), derives 80.10's `hcond'` with `(le_div_iff₀ (pow_pos hdpos1 (d+1))).mp`, closes with `lovaszLocalLemma_symmetric_sharp`; the `d = 0` branch (`hd0` by `omega`) uses constant weights `x := 1/2` (`p ≤ 1/e ≤ 1/2` via `linarith [Real.add_one_le_exp 1]`), `Γ(i) = ∅` from `(SimpleGraph.degree_eq_zero G i).mp hdeg0` + `neighborFinset_eq_empty`, closes with `lovaszLocalLemma_pos`. Tmp compiled warning-free (exit 0), zero sorries, 99 lines. | Re-verified independently: `lake env lean` on the tmp exits 0 with empty output (warning-free); LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; 99 lines (under the 500-line limit); `#print axioms` via Bash stdin returns exactly `[propext, Classical.choice, Quot.sound]` (acceptable). Statement matches the informal spec exactly: `hp`, `hd : ∀ i, G.degree i ≤ d`, `hcond : Real.exp 1 * p * ((d:ℝ)+1) ≤ 1`, NO `0 ≤ p` hypothesis, conclusion `0 < μ (⋂ i, (A i)ᶜ)`, `omit [DecidableEq ι] in`, no `@[simp]`. Integration: added `import Mathlib.Analysis.Complex.Exponential` FIRST in the main file's import block (alphabetical position, before `Mathlib.Probability...`); theorem inserted after `lovaszLocalLemma_symmetric_sharp`, before `end LovaszLocal` (omit line + docstring + full proof); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds (1923 jobs), integrated `#print axioms` via stdin again `[propext, Classical.choice, Quot.sound]`. Next: item 80.20 (`lovaszLocalLemma_4pd`). | `tmp_lovasz_symmetric.lean` |

### 80.20. lovaszLocalLemma_4pd

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **The `4pd` criterion** (gpt-notes Corollary 5.2): if every bad event has probability at
        most $p$ and every vertex has degree at most $d \ge 1$, with $4pd \le 1$, then some
        outcome avoids all bad events: $0 < \mu\bigl(\bigcap_i \overline{A_i}\bigr)$.
        ```lean
        omit [DecidableEq ι] in
        theorem lovaszLocalLemma_4pd (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {p : ℝ} (hp : ∀ i, μ (A i) ≤ ENNReal.ofReal p) {d : ℕ}
            (hd : ∀ i, G.degree i ≤ d) (hd₀ : 1 ≤ d) (hcond : 4 * p * (d : ℝ) ≤ 1) :
            0 < μ (⋂ i, (A i)ᶜ)
        ```
        `hd₀ : 1 ≤ d` is required, as in survey B §4.2: at `d = 0` the condition `4·p·0 ≤ 1` is
        vacuous in `p` (gives no bound on `p` at all), so the criterion genuinely needs `d ≥ 1`.
        NO `0 ≤ p` hypothesis: every step divides or multiplies by the positive quantities
        `2d`, `4d` only (positivity from `hd₀`), and the ENNReal lift
        (`ENNReal.ofReal_le_ofReal`) is unconditional — the proof works verbatim for any `p`.
    - proof: |
        **COMPILE-VERIFIED ROUTE (Survey 2026-08-15, attempt 1) — full working proof, `lake env
        lean` exit 0 with empty output (warning-free), axioms `[propext, Classical.choice,
        Quot.sound]`, 75-line stdin file (63-line theorem incl. docstring), zero sorries.**
        Apply item 80.1 with the constant weights `x := fun _ => 1 / (2 * (d : ℝ))`. Let
        `hdℝ : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd₀` (defined ONCE up front — every
        `linarith` step below silently relies on it being in the local context),
        `hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hd₀)`,
        `hdnz : (d : ℝ) ≠ 0 := ne_of_gt hdpos`,
        `h2dpos : 0 < 2 * (d : ℝ) := by positivity`, `h4dpos : 0 < 4 * (d : ℝ) := by positivity`.
        - `hx₀ : 0 ≤ 1/(2d)` — `change 0 ≤ 1 / (2 * (d : ℝ)); exact div_nonneg zero_le_one
          (le_of_lt h2dpos)`.
        - `hx₁ : 1/(2d) < 1` — `change 1 / (2 * (d : ℝ)) < 1; exact (div_lt_one h2dpos).2
          (by linarith)` (linarith uses `hdℝ` for `1 < 2d`).
        - **Bernoulli step**: `one_add_mul_le_pow` at `a := -1/(2d)`, `n := d`, with the
          hypothesis `H : -2 ≤ -1/(2d)` discharged INLINE via `by linarith` (needs
          `h12d : 1 / (2 * (d : ℝ)) ≤ (2 : ℝ) := (div_le_iff₀ h2dpos).mpr (by linarith)` in
          context — the `1 ≤ 2 * (2 * (d : ℝ))` goal is LINEAR in `d`, so plain `linarith`
          (not `nlinarith`) closes it from `hdℝ`):
          `have hbernoulli : 1 + (d : ℝ) * (-(1 / (2 * (d : ℝ)))) ≤
          (1 + (-(1 / (2 * (d : ℝ))))) ^ d := one_add_mul_le_pow (by linarith) d`.
          Then `hb : 1/2 ≤ (1 - 1/(2d))^d` by rewriting BOTH occurrences in `hbernoulli`:
          `hb' : 1 + (d : ℝ) * (-(1 / (2 * (d : ℝ)))) = (1 : ℝ) / 2` via
          `field_simp [hdnz]; ring` (field_simp alone leaves a residual — both needed),
          `hb'' : 1 + (-(1 / (2 * (d : ℝ)))) = 1 - 1 / (2 * (d : ℝ))` via `ring`,
          then `rwa [hb', hb''] at hbernoulli`.
        - **degree monotonicity**: `(1 - 1/(2d))^d ≤ (1 - 1/(2d))^(G.degree i)` via
          `refine pow_le_pow_of_le_one ?_ ?_ (hd i)` with
          `ha₀ : 0 ≤ 1 - 1/(2d)` = `sub_nonneg.mpr ((div_le_one h2dpos).2 (by linarith))`
          (linarith uses `hdℝ`), and `ha₁ : 1 - 1/(2d) ≤ 1` =
          `linarith [div_nonneg zero_le_one (le_of_lt h2dpos)]` — DEVIATION from the sketch:
          do NOT write `linarith [hx₀ i]` (the goal is stated in the concrete `1/(2d)` form
          while `hx₀ i : 0 ≤ x i` mentions the `let`-bound `x`); feed the concrete
          nonnegativity fact instead. Then `hdeg : 1/2 ≤ (1 - 1/(2d))^(G.degree i)` by
          `le_trans hb hpow`.
        - `p ≤ 1/(4d)`: `hpfrac := (le_div_iff₀ h4dpos).mpr
          (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcond)` — simp's AC
          normalization closes `4 * p * d` vs `p * (4 * d)` as sketched.
        - `hfrac : 1 / (4 * (d : ℝ)) = (1 / (2 * (d : ℝ))) * ((1 : ℝ) / 2)` via
          `field_simp [hdnz]; ring` (both needed, as for `hb'`).
        - chain: $p \le \frac{1}{4d} = \frac{1}{2d}\cdot\frac12 \le
          \frac{1}{2d}\bigl(1 - \frac{1}{2d}\bigr)^{G.\mathrm{degree}\,i}
          = x_i \prod_{j \in \Gamma(i)} (1 - x_j)$ — a 4-line `calc`; the middle inequality by
          `mul_le_mul_of_nonneg_left hdeg (hx₀ i)` (the `hx₀ i : 0 ≤ x i` is defeq-accepted
          for the concrete `0 ≤ 1/(2d)` goal, same as 80.10 step 4); the last equality —
          SIMPLER than 80.10 step 5, NO `hfactor` needed (the calc LHS is already the concrete
          `(1/(2d))·(1 - 1/(2d))^(G.degree i)`):
          `change (1 / (2 * (d : ℝ))) * (1 - 1 / (2 * (d : ℝ))) ^ G.degree i =
          (1 / (2 * (d : ℝ))) * ∏ j ∈ G.neighborFinset i, (1 - 1 / (2 * (d : ℝ)))` then
          `rw [Finset.prod_const]; rfl` (`#(G.neighborFinset i)` is defeq `G.degree i`, so
          `SimpleGraph.card_neighborFinset_eq_degree` is NOT consumed).
        - `hLLL` via `exact le_trans (hp i) (ENNReal.ofReal_le_ofReal hchain)`; close with
          `exact lovaszLocalLemma_pos A hA hdg hx₀ hx₁ hLLL`.
        **Omit test (negative, compile-verified 2026-08-15):** without the `omit [DecidableEq
        ι] in` line exactly `automatically included section variable(s) unused in theorem …
        [DecidableEq ι]` fires (signature gains `[DecidableEq ι]`); `[Fintype ι]`,
        `[IsProbabilityMeasure μ]`, `[MeasurableSpace Ω]` are NOT flagged (used via
        `G.degree`/`lovaszLocalLemma_pos`). `@[simp]`: NO (inequality theorem with hypotheses).
        The full proof is recorded below for the Proof/Setup roles.
        ```lean
        import Mathlib.Analysis.Complex.Exponential
        import StatsMLlib.Probability.LovaszLocal

        open MeasureTheory ProbabilityTheory
        open scoped BigOperators ENNReal

        namespace LovaszLocal

        variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
          [Fintype ι] [DecidableEq ι]

        omit [DecidableEq ι] in
        /-- The `4pd` criterion for the symmetric Lovász local lemma: if every bad event has
        probability at most `p` and every vertex of the dependency graph has degree at most
        `d ≥ 1`, with `4·p·d ≤ 1`, then some outcome avoids all bad events:
        `0 < μ (⋂ i, (A i)ᶜ)`. -/
        theorem lovaszLocalLemma_4pd (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {p : ℝ} (hp : ∀ i, μ (A i) ≤ ENNReal.ofReal p) {d : ℕ}
            (hd : ∀ i, G.degree i ≤ d) (hd₀ : 1 ≤ d) (hcond : 4 * p * (d : ℝ) ≤ 1) :
            0 < μ (⋂ i, (A i)ᶜ) := by
          let x : ι → ℝ := fun _ => 1 / (2 * (d : ℝ))
          have hdℝ : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd₀
          have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.succ_le_iff.mp hd₀)
          have hdnz : (d : ℝ) ≠ 0 := ne_of_gt hdpos
          have h2dpos : 0 < 2 * (d : ℝ) := by positivity
          have h4dpos : 0 < 4 * (d : ℝ) := by positivity
          have hx₀ : ∀ i, 0 ≤ x i := by
            intro i
            change 0 ≤ 1 / (2 * (d : ℝ))
            exact div_nonneg zero_le_one (le_of_lt h2dpos)
          have hx₁ : ∀ i, x i < 1 := by
            intro i
            change 1 / (2 * (d : ℝ)) < 1
            exact (div_lt_one h2dpos).2 (by linarith)
          have hLLL : ∀ i,
              μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)) := by
            intro i
            -- Bernoulli: `1/2 ≤ (1 - 1/(2d))^d` via `one_add_mul_le_pow` at `a = -1/(2d)`.
            have h12d : 1 / (2 * (d : ℝ)) ≤ (2 : ℝ) :=
              (div_le_iff₀ h2dpos).mpr (by linarith)
            have hbernoulli : 1 + (d : ℝ) * (-(1 / (2 * (d : ℝ)))) ≤
                (1 + (-(1 / (2 * (d : ℝ))))) ^ d := one_add_mul_le_pow (by linarith) d
            have hb : (1 : ℝ) / 2 ≤ (1 - 1 / (2 * (d : ℝ))) ^ d := by
              have hb' : 1 + (d : ℝ) * (-(1 / (2 * (d : ℝ)))) = (1 : ℝ) / 2 := by
                field_simp [hdnz]
                ring
              have hb'' : 1 + (-(1 / (2 * (d : ℝ)))) = 1 - 1 / (2 * (d : ℝ)) := by
                ring
              rwa [hb', hb''] at hbernoulli
            -- degree monotonicity
            have hpow : (1 - 1 / (2 * (d : ℝ))) ^ d ≤
                (1 - 1 / (2 * (d : ℝ))) ^ G.degree i := by
              refine pow_le_pow_of_le_one ?_ ?_ (hd i)
              · exact sub_nonneg.mpr ((div_le_one h2dpos).2 (by linarith))
              · linarith [div_nonneg zero_le_one (le_of_lt h2dpos)]
            have hdeg : (1 : ℝ) / 2 ≤ (1 - 1 / (2 * (d : ℝ))) ^ G.degree i :=
              le_trans hb hpow
            -- `p ≤ 1/(4d)`
            have hpfrac : p ≤ 1 / (4 * (d : ℝ)) :=
              (le_div_iff₀ h4dpos).mpr (by simpa [mul_assoc, mul_comm, mul_left_comm] using hcond)
            have hfrac : 1 / (4 * (d : ℝ)) = (1 / (2 * (d : ℝ))) * ((1 : ℝ) / 2) := by
              field_simp [hdnz]
              ring
            have hchain : p ≤ x i * ∏ j ∈ G.neighborFinset i, (1 - x j) := by
              calc
                p ≤ 1 / (4 * (d : ℝ)) := hpfrac
                _ = (1 / (2 * (d : ℝ))) * ((1 : ℝ) / 2) := hfrac
                _ ≤ (1 / (2 * (d : ℝ))) * (1 - 1 / (2 * (d : ℝ))) ^ G.degree i :=
                    mul_le_mul_of_nonneg_left hdeg (hx₀ i)
                _ = x i * ∏ j ∈ G.neighborFinset i, (1 - x j) := by
                    change (1 / (2 * (d : ℝ))) * (1 - 1 / (2 * (d : ℝ))) ^ G.degree i =
                      (1 / (2 * (d : ℝ))) * ∏ j ∈ G.neighborFinset i, (1 - 1 / (2 * (d : ℝ)))
                    rw [Finset.prod_const]
                    rfl
            exact le_trans (hp i) (ENNReal.ofReal_le_ofReal hchain)
          exact lovaszLocalLemma_pos A hA hdg hx₀ hx₁ hLLL
        ```
- **prep**
    - `one_add_mul_le_pow` — **Bernoulli's inequality**: `{R} [Ring R] [LinearOrder R]
      [IsStrictOrderedRing R] {a : R} (H : -2 ≤ a) (n : ℕ) : 1 + ↑n * a ≤ (1 + a) ^ n`
      (`Mathlib/Algebra/Order/Ring/Pow.lean:100`, root namespace, `section LinearOrderedRing`;
      `#check`-verified 2026-08-15) — instantiate `a := -1/(2d)`, `n := d`; the hypothesis `H`
      is `-2 ≤ -1/(2d)`, discharged inline via `by linarith` from
      `h12d : 1/(2d) ≤ 2 := (div_le_iff₀ h2dpos).mpr (by linarith)` (the `1 ≤ 2·(2·d)` goal
      is LINEAR in `d` — plain `linarith` with `hdℝ` in context, NOT `nlinarith`).
    - `lovaszLocalLemma_pos` (item 80.1) — applied with `x := fun _ => 1 / (2 * (d : ℝ))`.
    - `div_le_iff₀` — `(hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c`
      (`Algebra/Order/GroupWithZero/Basic.lean:1138`) — the `1/(2d) ≤ 2` step for `H`.
    - `pow_le_pow_of_le_one` — `[PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) {m n : ℕ}
      (hmn : m ≤ n) : a ^ n ≤ a ^ m` (`GroupWithZero/Basic.lean:393`) — degree monotonicity
      with `a := 1 - 1/(2d)`, `hmn := hd i`.
    - `div_nonneg` (`GroupWithZero/Basic.lean:883`), `div_le_one`/`div_lt_one`
      (`Algebra/Order/Field/Basic.lean:43/47`), `le_div_iff₀` (`GroupWithZero/Basic.lean:1134`),
      `sub_nonneg`, `Nat.cast_pos`, `Nat.succ_le_iff` (core), `exact_mod_cast`,
      `mul_le_mul_of_nonneg_left`, `ENNReal.ofReal_le_ofReal` — all consumed as in 80.10.
    - `Finset.prod_const` — `(b : M) : ∏ _x ∈ s, b = b ^ s.card`
      (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:629` — a `theorem`, not `lemma`;
      `#check`-verified 2026-08-15) — the Γ(i)-product becomes a power.
    - `field_simp`, `linarith`, `positivity`, `ring` — the arithmetic glue (the two
      `field_simp [hdnz]` + `ring` steps, the `hdℝ`-fed `linarith` steps, `positivity` for
      `h2dpos`/`h4dpos`).
    - REMOVED (exist, unused by the verified route): `pow_pos` (no pow-positivity needed — the
      Bernoulli RHS is bounded below by `1/2 > 0` directly); `nlinarith` (all remaining
      inequalities are linear in `d`); `SimpleGraph.card_neighborFinset_eq_degree` (`#(G.
      neighborFinset i)` is defeq `G.degree i`, plain `rfl` closes); `inv_nonneg`
      (`GroupWithZero/Basic.lean:851`, `@[simp]` — verified to exist for the spot-check list,
      but the route divides by the positive constants `2d`/`4d` instead of using inverses).
    - Note for Proof (established layout): `omit [DecidableEq ι] in` before the docstring; no
      `@[simp]` (inequality theorem with hypotheses). Omit requirement compile-verified
      negative 2026-08-15: without the omit line exactly `[DecidableEq ι]` is flagged
      (signature gains `[DecidableEq ι]`); `[Fintype ι]`/`[IsProbabilityMeasure μ]`/
      `[MeasurableSpace Ω]` are used and NOT flagged. Full compile-verified proof (75-line
      stdin file, axioms `[propext, Classical.choice, Quot.sound]`) recorded in the informal
      proof section above. NO new import: the main file already imports
      `Mathlib.Analysis.Complex.Exponential` (added at 80.15), and the snippet's
      `import Mathlib.Analysis.Complex.Exponential` line is redundant (kept for parity with
      80.15's tmp; Setup may drop it — `import StatsMLlib.Probability.LovaszLocal` alone
      suffices).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove `lovaszLocalLemma_4pd` (`4pd ≤ 1`): constant weights `x i := 1/(2·(d:ℝ))`; the ℝ chain `p ≤ 1/(4d) = (1/(2d))·(1/2) ≤ (1/(2d))·(1 - 1/(2d))^(G.degree i) = x i · ∏ (1 - x j)` with the middle bound from Bernoulli `one_add_mul_le_pow` at `a = -1/(2d)` (`(1 - 1/(2d))^d ≥ 1/2`, hypothesis `-2 ≤ -1/(2d)` via `div_le_iff₀` + linarith) and `pow_le_pow_of_le_one` at `hd i`; lift once via `ENNReal.ofReal_le_ofReal`; close with `lovaszLocalLemma_pos`. Survey compile-verified the COMPLETE proof warning-free via `lake env lean` (exit 0, empty output; axioms `[propext, Classical.choice, Quot.sound]`; 75-line stdin file) — full proof + route deviations recorded in the informal proof | No separate Proof role this attempt — the Survey produced the complete compile-verified proof and Setup materialized it verbatim into `tmp_lovasz_4pd.lean` (88 lines, zero sorries): constant weights `x i := 1/(2·(d:ℝ))`; Bernoulli `one_add_mul_le_pow` at `a = -1/(2d)` (`hb : 1/2 ≤ (1 - 1/(2d))^d` via `hb'` (`field_simp [hdnz]; ring`) + `hb''` (`ring`) + `rwa`), degree step `pow_le_pow_of_le_one ?_ ?_ (hd i)`, `hpfrac : p ≤ 1/(4d)` via `(le_div_iff₀ h4dpos).mpr` with simp AC normalization of `hcond`, `hfrac : 1/(4d) = (1/(2d))·(1/2)` via `field_simp [hdnz]; ring`, 4-line `calc` chain with the last equality via `change` + `Finset.prod_const` + `rfl`, single ENNReal lift `le_trans (hp i) (ENNReal.ofReal_le_ofReal hchain)`, closed with `lovaszLocalLemma_pos`. Tmp compiled warning-free (exit 0), zero sorries, 88 lines. | Re-verified independently: tmp `lake env lean` exit 0 with empty output (warning-free); LSP diagnostics empty; 88 lines (under the 500-line limit); grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#`-commands; `#print axioms` returns exactly `[propext, Classical.choice, Quot.sound]` (acceptable). Statement matches the informal spec exactly: `hp`, `hd : ∀ i, G.degree i ≤ d`, `hd₀ : 1 ≤ d`, `hcond : 4 * p * (d : ℝ) ≤ 1`, NO `0 ≤ p` hypothesis, conclusion `0 < μ (⋂ i, (A i)ᶜ)`, `omit [DecidableEq ι] in`, no `@[simp]`. Integration: theorem inserted after `lovaszLocalLemma_symmetric`, before `end LovaszLocal` (omit line + docstring + full proof, verbatim from tmp); imports unchanged (`Mathlib.Analysis.Complex.Exponential` already present from 80.15); tmp file deleted. Main file re-verified: `lake env lean` exit 0 (no warnings), full-file LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds (1923 jobs); integrated `#print axioms` again `[propext, Classical.choice, Quot.sound]`. Done. | `tmp_lovasz_4pd.lean` |

---
## 90. Optional Items (Conditional Form & Strong-Form Equivalence)

Group 90 is priority 1 throughout: nice-to-have, **may be dropped from PR 1** without losing the
theorem. Items 90.1/90.5 deliver the classical conditional-probability key lemma (gpt-notes
Lemma 4.2 verbatim); item 90.10 delivers the equivalence between the weak `IsDependencyGraph`
(10.5) and the classical strong form (gpt-notes Def 1.1).

### 90.1. cond_eq_of_indepSet, cond_compl_eq_one_sub, cond_le_one

- **meta**
    - kind: lemma
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        The three small `ProbabilityTheory.cond` glue lemmas absent from mathlib (survey A §2.3),
        needed only by the optional conditional form (item 90.5):
        - `cond_eq_of_indepSet (hs : MeasurableSet s) (ht : MeasurableSet t)
          (hst : IndepSet s t μ) (hμt₀ : μ t ≠ 0) (hμt : μ t ≠ ∞) : μ[s | t] = μ s` —
          conditioning on an independent event does nothing. (The compiled statement also
          carries the ambient `[IsProbabilityMeasure μ]` instance — see proof route below.)
        - `cond_compl_eq_one_sub (hms : MeasurableSet s) (ht : MeasurableSet t)
          (hμs₀ : μ s ≠ 0) : μ[tᶜ | s] = 1 - μ[t | s]` (with `[IsProbabilityMeasure μ]`
          supplying `μ s ≠ ∞`) — the complement-of-the-event identity used by the classical
          chain rule (gpt-notes (4)); the tsub is exact because `μ[t | s] ≤ 1` (third lemma).
          **Statement fix (Survey): `ht : MeasurableSet t` was ADDED** — without it the identity
          is false (non-measurable `t` of outer measure 1 in `[0,1]`, `s = univ`: LHS `= 1`,
          RHS `= 0`), and `measure_inter_add_sdiff s ht` needs it anyway. Available downstream
          in 90.5 (`A i` measurable).
        - `cond_le_one (hms : MeasurableSet s) [IsProbabilityMeasure μ] (hμs₀ : μ s ≠ 0) :
          μ[t | s] ≤ 1` — conditional probabilities of a probability measure are ≤ 1.
    - proof: |
        Survey compile-verified the COMPLETE proofs warning-free via `lake env lean` (stdin,
        exit 0, no output; axioms `[propext, Classical.choice, Quot.sound]`; 32-line file):
        ```lean
        omit [Fintype ι] [DecidableEq ι] in
        lemma cond_eq_of_indepSet {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t)
            (hst : IndepSet s t μ) (hμt₀ : μ t ≠ 0) (hμt : μ t ≠ ∞) : μ[s | t] = μ s := by
          rw [cond_apply ht, Set.inter_comm, (indepSet_iff_measure_inter_eq_mul hs ht (μ := μ)).mp hst,
            mul_comm (μ s) (μ t), ← mul_assoc, ENNReal.inv_mul_cancel hμt₀ hμt, one_mul]
        ```
        Route notes: `cond_apply ht` (needs measurability of the conditioning set) →
        `Set.inter_comm` → the iff `indepSet_iff_measure_inter_eq_mul hs ht` (Independence/
        Basic.lean:579; uses BOTH `hs` and `ht` so no unused-hypothesis warning; its
        `[IsZeroOrProbabilityMeasure μ]` instance is supplied by the ambient
        `[IsProbabilityMeasure μ]`, making that instance load-bearing) → `mul_comm (μ s) (μ t)`
        (explicit args — bare `mul_comm` would also flip the outer product) → `← mul_assoc` →
        `ENNReal.inv_mul_cancel hμt₀ hμt` → `one_mul`.
        ```lean
        omit [Fintype ι] [DecidableEq ι] in
        lemma cond_compl_eq_one_sub {s t : Set Ω} (hms : MeasurableSet s) (ht : MeasurableSet t)
            (hμs₀ : μ s ≠ 0) : μ[tᶜ | s] = 1 - μ[t | s] := by
          have hsum : μ[tᶜ | s] + μ[t | s] = 1 := by
            rw [cond_apply hms, cond_apply hms]
            rw [← mul_add, ← Set.sdiff_eq, add_comm, measure_inter_add_sdiff s ht]
            exact ENNReal.inv_mul_cancel hμs₀ (measure_ne_top μ s)
          exact (ENNReal.sub_eq_of_eq_add' ENNReal.one_ne_top hsum.symm).symm
        ```
        Route notes: sum-first — `cond_apply hms` twice, factor `(μ s)⁻¹` via `← mul_add`
        (avoids `mul_sub`'s implication hypothesis), `← Set.sdiff_eq` (`s ∩ tᶜ = s \ t`, rfl),
        `add_comm` + `measure_inter_add_sdiff s ht`, `ENNReal.inv_mul_cancel`; then pull the
        tsub out of `hsum` with `ENNReal.sub_eq_of_eq_add' ENNReal.one_ne_top` (the `'`-variant
        needs only `1 ≠ ∞`, avoiding a separate `μ[t | s] ≠ ∞` proof). `ENNReal.one_ne_top` must
        be qualified — `open scoped ENNReal` does not open names.
        ```lean
        omit [Fintype ι] [DecidableEq ι] in
        lemma cond_le_one {s t : Set Ω} (hms : MeasurableSet s) (hμs₀ : μ s ≠ 0) : μ[t | s] ≤ 1 := by
          rw [cond_apply hms, ← ENNReal.inv_mul_cancel hμs₀ (measure_ne_top μ s)]
          exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.mpr (measure_ne_top μ s))
            (ENNReal.inv_ne_top.mpr hμs₀)).2 (measure_mono Set.inter_subset_left)
        ```
        Route notes: `cond_apply hms` → rewrite `1` to `(μ s)⁻¹ * μ s` via `← inv_mul_cancel` →
        `ENNReal.mul_le_mul_iff_right` (Operations.lean:74; ENNReal has NO `MulLeftMono`
        instance, so the generic `mul_le_mul_left'`/`gcongr` are unavailable) with
        `ENNReal.inv_ne_zero.mpr (measure_ne_top μ s)` + `ENNReal.inv_ne_top.mpr hμs₀` →
        `measure_mono Set.inter_subset_left`.
        NO `@[simp]` / `@[gcongr]` on any of the three (all carry hypotheses;
        `cond_le_one` is a bound, not a monotonicity lemma). The `omit [Fintype ι]
        [DecidableEq ι] in` lines follow the main file's convention; a negative omit test
        produced no CLI linter warning (these lemmas do not mention `ι` at all), omit kept
        for consistency with `LovaszLocal.lean` style.
    - **prep**
        - `ProbabilityTheory.cond` — `cond μ s : Measure Ω := (μ s)⁻¹ • μ.restrict s` (`Mathlib/Probability/ConditionalProbability.lean:76`); notation `μ[t | s]` (:83).
        - `ProbabilityTheory.cond_apply` — `(hms : MeasurableSet s) : μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)` (:216); `cond_apply'` (:220) assumes `MeasurableSet t` instead.
        - `indepSet_iff_measure_inter_eq_mul` — `(hs_meas) (ht_meas) (μ := by volume_tac) [IsZeroOrProbabilityMeasure μ] : IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t` (`Mathlib/Probability/Independence/Basic.lean:579`); use with `(μ := μ)`.
        - `IndepSet.measure_inter_eq_mul` — `(h : IndepSet s t μ) : μ (s ∩ t) = μ s * μ t` (`Mathlib/Probability/Independence/Basic.lean:584`); unused in final route.
        - `measure_inter_add_sdiff` — `(s) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s` (`MeasureSpace.lean:118`).
        - `Set.sdiff_eq` — `s \ t = s ∩ tᶜ` (rfl; `Mathlib/Data/Set/Operations.lean:109`). NOTE: there is NO `Set.sdiff_eq_inter_compl`.
        - `ENNReal.sub_eq_of_eq_add'` — `(ha : a ≠ ∞) : a = c + b → a - b = c` (`Mathlib/Data/ENNReal/Operations.lean:311`); `sub_eq_of_eq_add` (:306) needs `b ≠ ∞` instead.
        - `ENNReal.mul_le_mul_iff_right` — `(h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b ≤ a * c ↔ b ≤ c` (`Operations.lean:74`); ENNReal has no `MulLeftMono`, so `mul_le_mul_left'`/`gcongr` do NOT work.
        - `ENNReal.inv_mul_cancel` — `(h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1` — **PINNED cancellation lemma** (`Mathlib/Data/ENNReal/Inv.lean:107`); `mul_inv_cancel` (`a * a⁻¹ = 1`) at :102.
        - `ENNReal.inv_ne_zero` — `a⁻¹ ≠ 0 ↔ a ≠ ∞` (`Inv.lean:219`); `ENNReal.inv_ne_top` — `a⁻¹ ≠ ∞ ↔ a ≠ 0` (`Inv.lean:200`).
        - `ENNReal.one_ne_top` — `1 ≠ ∞` (`Mathlib/Data/ENNReal/Basic.lean:366`); needs `ENNReal.` qualification.
        - `measure_mono`, `measure_ne_top` — `measure_ne_top (μ) [IsFiniteMeasure μ] (s) : μ s ≠ ∞` (`Typeclasses/Finite.lean:55`); instance `[IsProbabilityMeasure μ] → IsFiniteMeasure μ` (`Typeclasses/Probability.lean:74`).
        - `mul_add`, `one_mul`, `mul_assoc`, `mul_comm`, `Set.inter_comm`, `add_comm` — algebra bookkeeping.
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Prove the three `cond` glue lemmas with the Survey-pinned routes: `cond_eq_of_indepSet` via `cond_apply ht` + `indepSet_iff_measure_inter_eq_mul hs ht (μ := μ)` (uses both `hs`/`ht`; cancellation pinned to `ENNReal.inv_mul_cancel`, Inv.lean:107); `cond_compl_eq_one_sub` with **`ht : MeasurableSet t` ADDED to the statement** (identity false without it) via the sum-first route `← mul_add` + `measure_inter_add_sdiff` + `ENNReal.sub_eq_of_eq_add' ENNReal.one_ne_top`; `cond_le_one` via `ENNReal.mul_le_mul_iff_right` (no `MulLeftMono` on ENNReal). All three compile-verified warning-free by Survey via `lake env lean` stdin (exit 0, axioms `[propext, Classical.choice, Quot.sound]`); `omit [Fintype ι] [DecidableEq ι] in` on each, no `@[simp]`/`@[gcongr]`. | Survey produced complete compile-verified proofs (no separate Proof role); Setup materialized them verbatim into `tmp_cond_glue.lean` (52 lines, zero sorries, warning-free): `cond_eq_of_indepSet` via `cond_apply ht` + `Set.inter_comm` + `indepSet_iff_measure_inter_eq_mul hs ht (μ := μ)` + `mul_comm (μ s) (μ t)` + `← mul_assoc` + `ENNReal.inv_mul_cancel` + `one_mul`; `cond_compl_eq_one_sub` (with the ADDED `ht : MeasurableSet t`) via the sum-first route `cond_apply hms` twice + `← mul_add` + `← Set.sdiff_eq` + `add_comm` + `measure_inter_add_sdiff s ht` + `ENNReal.inv_mul_cancel`, then `ENNReal.sub_eq_of_eq_add' ENNReal.one_ne_top`; `cond_le_one` via `cond_apply hms` + `← ENNReal.inv_mul_cancel` + `ENNReal.mul_le_mul_iff_right`. `omit [Fintype ι] [DecidableEq ι] in` on each, no `@[simp]`/`@[gcongr]`. | Re-verified independently: tmp `lake env lean` exit 0, empty output (warning-free); LSP diagnostics empty; 52 lines (< 500-line limit); grep clean (no sorry/axiom/admit/native_decide/#-commands). Statements match item 90.1's corrected informal exactly (three lemmas; `cond_compl_eq_one_sub` carries `ht : MeasurableSet t`; `omit [Fintype ι] [DecidableEq ι] in` on each; no attributes). Integrated verbatim into `LovaszLocal.lean` after `lovaszLocalLemma_4pd`, before `end LovaszLocal` (namespace `variable` line already present — not duplicated); tmp file deleted. Main file re-verified: `lake env lean` exit 0, no warnings; LSP diagnostics empty; `lake build StatsMLlib.Probability.LovaszLocal` succeeds (1923 jobs). Done. | `tmp_cond_glue.lean` |

### 90.5. lovaszLocalLemma_cond

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Conditional form of the key lemma** (gpt-notes Lemma 4.2, survey B step 14):
        under the same hypotheses as `lovaszLocalLemma`, for every finite `S` and every `i ∉ S`,
        $$\mu\bigl[A_i \,\big|\, B_S\bigr] \le \mathrm{ofReal}(x_i),$$
        together with positivity $\mu(B_S) > 0$ (obtained from (P1) and the strict positivity of
        $\prod_{j \in S} (1 - x_j)$).
        **Statement-shape decision (Survey 2026-08-15): TWO theorems.** The positivity is split
        out as the standalone reusable theorem `lovaszLocalLemma_bset_pos` (the classical
        well-definedness fact $\mu(B_S) > 0$ for every finite $S$ — no `i`/`hi` involved), and
        `lovaszLocalLemma_cond` carries the classical bound alone, obtaining the positivity as an
        internal `have` from `lovaszLocalLemma_bset_pos`. Rationale: (1) mathlib style prefers
        non-conjunctive conclusions (no `.1`/`.2` projections downstream); (2) the classical
        chain-rule proof of the LLL needs $\mu(B_S) > 0$ for arbitrary `S` independently of any
        `i ∉ S`, which a conjunction at `(S, i)` does not deliver; (3) the bound proof uses the
        positivity only internally, so bundling it into the conclusion adds noise. Signatures
        (compile-verified; `omit [DecidableEq ι] in` on both, matching
        `lll_prob_bset`/`lovaszLocalLemma`; `#check` output confirms `[Fintype ι]` retained,
        `[DecidableEq ι]` dropped):
        ```lean
        theorem lovaszLocalLemma_bset_pos (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)))
            (S : Finset ι) : 0 < μ (bset A S)

        theorem lovaszLocalLemma_cond (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)))
            {S : Finset ι} {i : ι} (hi : i ∉ S) : μ[A i | bset A S] ≤ ENNReal.ofReal (x i)
        ```
        Integration order: `lovaszLocalLemma_bset_pos` MUST be placed before
        `lovaszLocalLemma_cond` in the main file; both go after the item 90.1 glue, before
        `end LovaszLocal`.
    - proof: |
        Survey compile-verified BOTH COMPLETE proofs warning-free via `lake env lean` stdin
        (exit 0, empty output; axioms `[propext, Classical.choice, Quot.sound]` for both).
        ```lean
        omit [DecidableEq ι] in
        theorem lovaszLocalLemma_bset_pos (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)))
            (S : Finset ι) : 0 < μ (bset A S) := by
          have hprod : 0 < ∏ j ∈ S, (1 - x j) :=
            Finset.prod_pos (fun j _ => sub_pos.mpr (hx₁ j))
          have hofReal : 0 < ENNReal.ofReal (∏ j ∈ S, (1 - x j)) := ENNReal.ofReal_pos.mpr hprod
          exact lt_of_lt_of_le hofReal ((lll_prob_bset A hA hdg hx₀ hx₁ hLLL S).1)
        ```
        Positivity route: strict positivity of the product via `Finset.prod_pos` +
        `sub_pos.mpr (hx₁ j)`, lifted through `ENNReal.ofReal_pos.mpr`, then (P1) of
        `lll_prob_bset` via `lt_of_lt_of_le` — exactly the `lovaszLocalLemma_pos` pattern
        (LovaszLocal.lean:354-356), specialized from `univ` to an arbitrary finite `S`.
        ```lean
        omit [DecidableEq ι] in
        theorem lovaszLocalLemma_cond (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
            {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
            {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j)))
            {S : Finset ι} {i : ι} (hi : i ∉ S) :
            μ[A i | bset A S] ≤ ENNReal.ofReal (x i) := by
          have hμS₀ : 0 < μ (bset A S) := lovaszLocalLemma_bset_pos A hA hdg hx₀ hx₁ hLLL S
          have hP2 : μ (A i ∩ bset A S) ≤ ENNReal.ofReal (x i) * μ (bset A S) :=
            (lll_prob_bset A hA hdg hx₀ hx₁ hLLL S).2 i hi
          calc
            μ[A i | bset A S] = (μ (bset A S))⁻¹ * μ (bset A S ∩ A i) := by
                rw [cond_apply (measurableSet_bset A hA S)]
            _ = (μ (bset A S))⁻¹ * μ (A i ∩ bset A S) := by
                rw [Set.inter_comm]
            _ ≤ (μ (bset A S))⁻¹ * (ENNReal.ofReal (x i) * μ (bset A S)) := by
                exact mul_le_mul_right hP2 (μ (bset A S))⁻¹
            _ = ENNReal.ofReal (x i) := by
                rw [mul_comm (ENNReal.ofReal (x i)) (μ (bset A S)), ← mul_assoc,
                  ENNReal.inv_mul_cancel (ne_of_gt hμS₀) (measure_ne_top μ (bset A S)), one_mul]
        ```
        Bound route notes: (P2) of `lll_prob_bset` at `(i, S)` via `.2 i hi` — its conclusion
        already has the `A i ∩ bset A S` order, so only the FIRST calc step needs the inter-order
        fix (`cond_apply` returns `s ∩ t` with `s` = the conditioning set; flip via
        `Set.inter_comm`). Left-multiply by the inverse via
        `mul_le_mul_right hP2 (μ (bset A S))⁻¹`. NAMING QUIRK (verified in mathlib v4.32
        `Algebra/Order/Monoid/Unbundled/Basic.lean`): `mul_le_mul_right h c : c * a ≤ c * b`
        (LEFT multiplication by `c`, :70) and `mul_le_mul_left h c : a * c ≤ b * c` (RIGHT
        multiplication, :81) — the names refer to the class they use (`MulLeftMono`/
        `MulRightMono`), not the side they multiply on. Both work on ENNReal because
        `CanonicallyOrderedAdd` supplies `MulLeftMono`/`MulRightMono` (Ring/Canonical.lean:40,
        priority 100) — this SUPERSEDES the 90.1 pitfall "ENNReal has NO MulLeftMono": the
        unbundled `mul_le_mul_left`/`mul_le_mul_right` compile on ENNReal (main file lines
        194/268/307/318/322); only the primed positivity variants `mul_le_mul_left'`/`gcongr`
        and cancellation (the `ENNReal.mul_le_mul_iff_right` iff) are the 90.1 concern. Final
        cancellation with explicit `mul_comm (ofReal (x i)) (μS)` (a bare `mul_comm` would also
        flip the outer product), then `← mul_assoc`,
        `ENNReal.inv_mul_cancel (ne_of_gt hμS₀) (measure_ne_top μ (bset A S))`
        (`ne_of_gt h : a < b → b ≠ a`, matching `lovaszLocalLemma_exists`'s usage at line 463),
        `one_mul`. `hA` is load-bearing in both theorems (`measurableSet_bset` / `lll_prob_bset`).
        NO `@[simp]` on either (hypothesis-carrying; `bset_pos` is a bound, not an equation).
    - **prep** (all verified 2026-08-15 against mathlib v4.32.0 sources)
        - `lll_prob_bset` (item 60.1, LovaszLocal.lean:204) — `(S : Finset ι) :
          ofReal (∏ j ∈ S, (1 - x j)) ≤ μ (bset A S) ∧
          ∀ i, i ∉ S → μ (A i ∩ bset A S) ≤ ofReal (x i) * μ (bset A S)`; used as `.1`
          (positivity) and `.2 i hi` (bound).
        - `measurableSet_bset` (item 20.15, LovaszLocal.lean:118) — `(A) (hA) (S) :
          MeasurableSet (bset A S)`; `omit [Fintype ι] [DecidableEq ι] in`.
        - `ProbabilityTheory.cond_apply` — `(hms : MeasurableSet s) (μ : Measure Ω) (t : Set Ω) :
          μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)` (`Mathlib/Probability/ConditionalProbability.lean:216`;
          `cond_apply'` :220 assumes `MeasurableSet t` instead — not used).
        - `Finset.prod_pos` — `(h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i`
          (`Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:107`).
        - `sub_pos` — `0 < a - b ↔ b < a` (`Mathlib/Algebra/Order/Group/Unbundled/Basic.lean:603`,
          to_additive of `one_lt_div'`); use `sub_pos.mpr (hx₁ j)`.
        - `ENNReal.ofReal_pos` — `0 < ENNReal.ofReal p ↔ 0 < p` (`Mathlib/Data/ENNReal/Real.lean:176`);
          use `.mpr`.
        - `lt_of_lt_of_le`, `measure_ne_top` — `measure_ne_top (μ) [IsFiniteMeasure μ] (s) :
          μ s ≠ ∞` (Typeclasses/Finite.lean:55); `[IsProbabilityMeasure μ] → IsFiniteMeasure μ`.
        - `ENNReal.inv_mul_cancel` — `(h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1` — PINNED
          cancellation lemma (`Mathlib/Data/ENNReal/Inv.lean:107`); `mul_inv_cancel` at :102.
        - `mul_le_mul_right` — `[MulLeftMono α] (bc : b ≤ c) (a : α) : a * b ≤ a * c`
          (`Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:70`); on ENNReal via
          `CanonicallyOrderedAdd` (Ring/Canonical.lean:40). `mul_le_mul_left` :81 is the
          right-multiplier variant.
        - `ne_of_gt` — `(h : a < b) : b ≠ a` (matches LovaszLocal.lean:463 usage).
        - `Set.inter_comm`, `mul_comm`, `mul_assoc`, `one_mul` — algebra bookkeeping.
        - `cond_le_one` (item 90.1) — NOT needed in the final route (the bound is direct from (P2);
          no per-`cond_apply` splitting).
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Statement-shape decision + complete compile-verified proofs: TWO theorems — `lovaszLocalLemma_bset_pos` (standalone positivity `0 < μ (bset A S)`, reusable well-definedness fact, no `i`/`hi`) placed first, and `lovaszLocalLemma_cond` (`{S} {i} (hi : i ∉ S) : μ[A i | bset A S] ≤ ENNReal.ofReal (x i)`) with the positivity as an internal `have` from the former. Positivity via `Finset.prod_pos` + `sub_pos.mpr (hx₁ j)` + `ENNReal.ofReal_pos.mpr` + (P1)`.1` + `lt_of_lt_of_le`; bound via (P2)`.2 i hi` + `cond_apply` + `Set.inter_comm` + `mul_le_mul_right hP2 (μ (bset A S))⁻¹` (left-multiplication; naming quirk pinned — ENNReal HAS MulLeftMono/MulRightMono via CanonicallyOrderedAdd, superseding the 90.1 pitfall) + `mul_comm`/`← mul_assoc`/`ENNReal.inv_mul_cancel`/`one_mul`; `omit [DecidableEq ι] in` on both, no `@[simp]` | Survey produced complete compile-verified proofs for both theorems (no separate Proof role); Setup materialized them verbatim into `tmp_lovasz_cond.lean` (61 lines, zero sorries, warning-free). `lovaszLocalLemma_bset_pos` via `Finset.prod_pos` + `sub_pos.mpr (hx₁ j)` + `ENNReal.ofReal_pos.mpr` + (P1) of `lll_prob_bset` + `lt_of_lt_of_le`; `lovaszLocalLemma_cond` with the positivity as an internal `have` from `lovaszLocalLemma_bset_pos`, then (P2)`.2 i hi` + `cond_apply (measurableSet_bset A hA S)` + `Set.inter_comm` + `mul_le_mul_right hP2 (μ (bset A S))⁻¹` + `mul_comm`/`← mul_assoc`/`ENNReal.inv_mul_cancel (ne_of_gt hμS₀) (measure_ne_top μ (bset A S))`/`one_mul`. | Re-verified independently: tmp `lake env lean` exit 0, empty output (warning-free); LSP diagnostics empty; 61 lines (< 500-line limit); grep clean (no sorry/axiom/admit/native_decide/#-commands, no `@[` attributes); axioms for BOTH theorems via stdin `#print axioms`: `[propext, Classical.choice, Quot.sound]` (acceptable). Statements match item 90.5's pinned shape exactly (`lovaszLocalLemma_bset_pos` with explicit `S`; `lovaszLocalLemma_cond` with `hi : i ∉ S`; `omit [DecidableEq ι] in` on both). Integrated verbatim into `LovaszLocal.lean` inside `namespace LovaszLocal` after the 90.1 cond glue block, before `end LovaszLocal` (`lovaszLocalLemma_bset_pos` first — namespace `variable` line already present, not duplicated); tmp file deleted. Main file re-verified: `lake env lean` exit 0, no warnings; LSP diagnostics empty; `lake build StatsMLlib.Probability.LovaszLocal` succeeds (1923 jobs). This was the LAST blueprint item. Done. | `tmp_lovasz_cond.lean` |

### 90.10. IsDependencyGraph strong-form equivalence

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
    - note: Superseded by 90.15 (2026-08-15) — its per-finite-S `IsDependencyGraphStrong` def and both bridge theorems were REPLACED in the main file by the global-form versions; the proof ideas (π-system p2, hgen1/hgen2, `IndepSets.indep'`) carried over.
- **informal**
    - statement: |
        **Strong-form equivalence package** (survey B §1.2(a), proposal API question 1; the
        bridge the GPT review 2026-08-15 asked for). Define the classical strong hypothesis
        (gpt-notes Def 1.1: `A i` independent of every Boolean combination of the non-neighbor
        events) as `IsDependencyGraphStrong G A : Prop` — **atoms-only shape** (verified
        2026-08-15; `generateFrom {t | t = A i}` IS the two-atom algebra `{∅, A i, (A i)ᶜ, Ω}`
        since `generateFrom` closes under complements, so this is exactly Boolean-combination
        independence; the shape matches `generateFrom_piiUnionInter_singleton_left` and
        `iIndepSet.indep_generateFrom_of_disjoint`):
        `∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) →
          Indep (MeasurableSpace.generateFrom {t | t = A i})
                (MeasurableSpace.generateFrom {t | ∃ j ∈ S, t = A j}) μ`.
        Then prove both directions:
        - `IsDependencyGraph.of_strong : IsDependencyGraphStrong G A → IsDependencyGraph G A`
          (strong → weak; no `hA`, no measure typeclass).
        - `IsDependencyGraph.strong (hA : ∀ i, MeasurableSet (A i)) :
          IsDependencyGraph G A → IsDependencyGraphStrong G A` (weak → strong;
          `hA` and `[IsZeroOrProbabilityMeasure μ]` (free from `[IsProbabilityMeasure μ]`)
          enter only here, in the π-λ lifting).
    - proof: |
        Both directions FULLY compile-tested via stdin on 2026-08-15 (no sorries left); the
        verified skeleton is embedded at the end of this section — the Proof agent transcribes
        it into `tmp_dep_graph_strong.lean`, adds doc comments and `omit` clauses
        (`of_strong`/def: omit `[IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]`;
        `.strong`: omit `[Fintype ι]`).

        strong → weak: `A i` is a generator of its own two-atom algebra
        (`MeasurableSpace.measurableSet_generateFrom rfl`); `bset A S` is a finite intersection
        of complements of generators of the atoms algebra
        (`Finset.measurableSet_biInter` under `letI : MeasurableSpace Ω := generateFrom …`);
        conclude via `Indep.indepSet_of_measurableSet` (no measure class needed).

        weak → strong: fix `i, S`; let `p2 := {u | ∃ U : Finset ι, U ⊆ S ∧ u = bset A U}`.
        (1) `IndepSets {t | t = A i} p2 μ` — unfold with
        `simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure,
        Kernel.const_apply, Set.mem_setOf_eq]`; per pair use
        `indepSet_iff_measure_inter_eq_mul` + `h i U hiU hnonadjU` (`U ⊆ S` gives both
        `i ∉ U` and all-non-neighbors).
        (2) `IsPiSystem {t | t = A i}` (`Set.inter_self`; note `IsPiSystem`'s hypothesis is
        `(s ∩ t).Nonempty`) and `IsPiSystem p2` (`bset_union` on `U ∪ V`).
        (3) `IndepSets.indep'` (Basic.lean:495 — preferred over `.indep`, no `m ≤ _mΩ` needed)
        lifts to `Indep (generateFrom {t | t = A i}) (generateFrom p2) μ`
        (measurability from `hA` / `measurableSet_bset`).
        (4) Rewrite the second algebra:
        `generateFrom p2 = generateFrom {t | ∃ k ∈ S, t = (A k)ᶜ}`
        (each `bset A U` is a finite iInter of generators; each `(A k)ᶜ = bset A {k}`), then
        complement symmetry `generateFrom {t | ∃ k ∈ S, t = (A k)ᶜ} =
        generateFrom {t | ∃ k ∈ S, t = A k}` (`generateFrom_le` both ways, `.compl`).
        The `piiUnionInter` route from the original plan is bypassed — not needed.
    - **prep** (all verified 2026-08-15 against mathlib v4.32.0 sources)
        - From the main file: `bset` (:54), `IsDependencyGraph` (:59), `bset_union` (:91,
          `[simp]`), `measurableSet_bset` (:117).
        - `ProbabilityTheory.Indep` (Independence/Basic.lean:118) —
          `Indep (m₁ m₂ : MeasurableSpace Ω) {_mΩ} (μ) : Prop`.
        - `Indep.indepSet_of_measurableSet` (Basic.lean:595) — `Indep m₁ m₂ μ →
          MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ` (no measure class).
        - `IndepSets.indep'` (Basic.lean:495) — `[IsZeroOrProbabilityMeasure μ]`,
          `(hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s)
          (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2) (hyp : IndepSets p1 p2 μ) :
          Indep (generateFrom p1) (generateFrom p2) μ`. `IndepSets.indep` (:488) also exists
          but needs `m1 ≤ _mΩ` / `m2 ≤ _mΩ` hypotheses — don't use.
        - `indepSet_iff_measure_inter_eq_mul` (Basic.lean:579) — `MeasurableSet s →
          MeasurableSet t → [IsZeroOrProbabilityMeasure μ] →
          IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`.
        - `MeasurableSpace.generateFrom` / `MeasurableSpace.measurableSet_generateFrom`
          (MeasurableSpace/Defs.lean:336) / `MeasurableSpace.generateFrom_le` (:350) /
          `MeasurableSpace.generateFrom_mono` (:399). PITFALL: all live in namespace
          `MeasurableSpace` — must qualify (not exported at root).
        - `Finset.measurableSet_biInter` (Defs.lean:149) — `{f : β → Set α} (s : Finset β)
          (h : ∀ b ∈ s, MeasurableSet (f b)) : MeasurableSet (⋂ b ∈ s, f b)`.
        - `IsPiSystem` (MeasureTheory/PiSystem.lean:72) — hypothesis is
          `(s ∩ t : Set α).Nonempty`, NOT `s ∩ t ≠ ∅`.
        - Unfolding `IndepSets`: `Kernel.IndepSets` def is
          `∀ t1 t2, t1 ∈ s1 → t2 ∈ s2 → ∀ᵐ a ∂μ, κ a (t1 ∩ t2) = κ a t1 * κ a t2`
          (Probability/Independence/Kernel/Indep.lean:75); unfold with
          `simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure,
          Kernel.const_apply, Set.mem_setOf_eq]` (`ae_dirac_eq` Measure/Dirac.lean:209,
          `Kernel.const_apply` Kernel/Basic.lean:184, both `[simp]`).
        - NOT needed (verified; the plan below bypasses them): `piiUnionInter`,
          `isPiSystem_piiUnionInter`, `generateFrom_piiUnionInter_singleton_left`
          (PiSystem.lean:357/413/399 — statements correct as listed before but the bespoke
          `p2` route is shorter), `indepSet_iff_indepSets_singleton` (Basic.lean:574 — needs
          both measurability hyps AND `[IsZeroOrProbabilityMeasure μ]`).
    - verified skeleton (compiles as-is via `lake env lean` stdin against the main file):
      ```lean
      def IsDependencyGraphStrong (G : SimpleGraph ι) (A : ι → Set Ω) : Prop :=
        ∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) →
          Indep (MeasurableSpace.generateFrom {t : Set Ω | t = A i})
            (MeasurableSpace.generateFrom {t : Set Ω | ∃ j ∈ S, t = A j}) μ

      theorem IsDependencyGraph.of_strong {G : SimpleGraph ι} {A : ι → Set Ω}
          (h : IsDependencyGraphStrong (μ := μ) G A) : IsDependencyGraph (μ := μ) G A := by
        intro i S hiS hnonadj
        have hAi : MeasurableSet[MeasurableSpace.generateFrom {t : Set Ω | t = A i}] (A i) :=
          MeasurableSpace.measurableSet_generateFrom rfl
        have hB : MeasurableSet[MeasurableSpace.generateFrom {t : Set Ω | ∃ j ∈ S, t = A j}]
            (bset A S) := by
          letI : MeasurableSpace Ω := MeasurableSpace.generateFrom {t : Set Ω | ∃ j ∈ S, t = A j}
          simp only [bset]
          exact Finset.measurableSet_biInter S (fun j hj =>
            (MeasurableSpace.measurableSet_generateFrom
              (show A j ∈ ({t : Set Ω | ∃ k ∈ S, t = A k}) from ⟨j, hj, rfl⟩)).compl)
        exact Indep.indepSet_of_measurableSet (μ := μ) (h i S hiS hnonadj) hAi hB

      theorem IsDependencyGraph.strong {G : SimpleGraph ι} {A : ι → Set Ω}
          (hA : ∀ i, MeasurableSet (A i)) (h : IsDependencyGraph (μ := μ) G A) :
          IsDependencyGraphStrong (μ := μ) G A := by
        intro i S hiS hnonadj
        let p2 : Set (Set Ω) := {u | ∃ U : Finset ι, U ⊆ S ∧ u = bset A U}
        have hp1m : ∀ s ∈ ({t : Set Ω | t = A i}), MeasurableSet s := by
          rintro s rfl
          exact hA i
        have hp2m : ∀ s ∈ p2, MeasurableSet s := by
          rintro s ⟨U, hUS, rfl⟩
          exact measurableSet_bset A hA U
        have hpi1 : IsPiSystem ({t : Set Ω | t = A i}) := by
          rintro s rfl t rfl _
          exact Set.inter_self (A i)
        have hpi2 : IsPiSystem p2 := by
          rintro u ⟨U, hUS, rfl⟩ v ⟨V, hVS, rfl⟩ _
          refine ⟨U ∪ V, Finset.union_subset hUS hVS, ?_⟩
          simp [bset_union]
        have hIndepSets : IndepSets ({t : Set Ω | t = A i}) p2 μ := by
          simp only [IndepSets, Kernel.IndepSets, ae_dirac_eq, Filter.eventually_pure,
            Kernel.const_apply, Set.mem_setOf_eq]
          rintro t1 t2 rfl ⟨U, hUS, rfl⟩
          have hiU : i ∉ U := fun hi => hiS (hUS hi)
          have hnonadjU : ∀ j ∈ U, ¬ G.Adj i j := fun j hj => hnonadj j (hUS hj)
          exact (indepSet_iff_measure_inter_eq_mul (μ := μ) (hA i) (measurableSet_bset A hA U)).mp
            (h i U hiU hnonadjU)
        have hind : Indep (MeasurableSpace.generateFrom ({t : Set Ω | t = A i}))
            (MeasurableSpace.generateFrom p2) μ :=
          IndepSets.indep' (μ := μ) hp1m hp2m hpi1 hpi2 hIndepSets
        have hgen1 : MeasurableSpace.generateFrom p2 =
            MeasurableSpace.generateFrom {t : Set Ω | ∃ k ∈ S, t = (A k)ᶜ} := by
          refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_mono ?_)
          · rintro u ⟨U, hUS, rfl⟩
            letI : MeasurableSpace Ω := MeasurableSpace.generateFrom {t : Set Ω | ∃ k ∈ S, t = (A k)ᶜ}
            simp only [bset]
            exact Finset.measurableSet_biInter U (fun k hk =>
              MeasurableSpace.measurableSet_generateFrom ⟨k, hUS hk, rfl⟩)
          · rintro t ⟨k, hkS, rfl⟩
            exact ⟨{k}, by intro x hx; rw [Finset.mem_singleton.mp hx]; exact hkS, by simp [bset]⟩
        have hgen2 : MeasurableSpace.generateFrom {t : Set Ω | ∃ k ∈ S, t = (A k)ᶜ} =
            MeasurableSpace.generateFrom {t : Set Ω | ∃ k ∈ S, t = A k} := by
          refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
          · rintro t ⟨k, hkS, rfl⟩
            exact (MeasurableSpace.measurableSet_generateFrom
              (show A k ∈ ({t : Set Ω | ∃ k ∈ S, t = A k}) from ⟨k, hkS, rfl⟩)).compl
          · rintro t ⟨k, hkS, rfl⟩
            simpa using (MeasurableSpace.measurableSet_generateFrom
              (show (A k)ᶜ ∈ ({t : Set Ω | ∃ k ∈ S, t = (A k)ᶜ}) from ⟨k, hkS, rfl⟩)).compl
        rw [hgen1, hgen2] at hind
        exact hind
      ```
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | ONE attempt, both directions: transcribe the survey-verified skeleton (compiles via stdin, zero sorries) into the tmp — def `IsDependencyGraphStrong` (atoms-only shape), `of_strong`, `.strong`; add doc comments + `omit` clauses | Setup materialized the survey-verified skeleton into `tmp_dep_graph_strong.lean` (102 lines, zero sorries): def `IsDependencyGraphStrong` (atoms-only shape) with docstring, `IsDependencyGraph.of_strong`, `IsDependencyGraph.strong`, each with the survey's `omit` clauses; no separate Proof role (same as 60.1) | Re-verified independently: `lake env lean` on the tmp exits 0 with no output; LSP diagnostics empty; grep found no `sorry`/`axiom`/`admit`/`native_decide`/`#` (only the word "sorry" inside the header comment); 102 lines. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all three declarations — the standard list; the def's axioms come from unfolding `ProbabilityTheory.Indep`, which itself prints the same list (matches existing `IsDependencyGraph`/`bset_union`). Signatures match the item's informal statement: atoms-only def shape, `of_strong` without `hA`/measure class, `.strong` with `hA` and `[Fintype ι]` omitted. Integrated into `LovaszLocal.lean` after `lovaszLocalLemma_probReal`, before `end LovaszLocal`; tmp deleted. `lake env lean` on the main file exits 0 with no warnings; LSP diagnostics empty; `lake build StatsMLlib.Probability.LovaszLocal` succeeds with weak linters. | `tmp_dep_graph_strong.lean` |

### 90.15. IsDependencyGraphStrong global-form rework

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/LovaszLocal.lean`
- **informal**
    - statement: |
        **Global-form rework** (GPT review v2, point 1): redefine `IsDependencyGraphStrong` as
        independence from the σ-algebra generated by ALL non-neighbor events (no `[Fintype ι]`
        needed):
        `def IsDependencyGraphStrong (G : SimpleGraph ι) (A : ι → Set Ω) : Prop :=
          ∀ i, Indep (MeasurableSpace.generateFrom {A i})
            (MeasurableSpace.generateFrom {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = A j}) μ`.
        Replace the existing (per-finite-S) def and re-prove both directions:
        - `IsDependencyGraph.of_strong : IsDependencyGraphStrong G A → IsDependencyGraph (μ := μ) G A`
          (restriction: `bset A S` is measurable w.r.t. the smaller generated σ-algebra).
        - `IsDependencyGraph.strong (hA : ∀ i, MeasurableSet (A i)) :
          IsDependencyGraph (μ := μ) G A → IsDependencyGraphStrong G A` — the π-system route with
          `p2 := {u | ∃ U : Finset ι, i ∉ U ∧ (∀ j ∈ U, ¬ G.Adj i j) ∧ u = bset A U}` (closed under
          binary intersection via `bset_union`; contains every single non-neighbor complement
          `(A j)ᶜ = bset A {j}`; `generateFrom p2` = the all-non-neighbors σ-algebra), NO Fintype
          required.
        - NEW `isDependencyGraph_iff_strong (hA) : IsDependencyGraph (μ := μ) G A ↔
          IsDependencyGraphStrong G A` — the explicit iff wrapper.
        Also (GPT review v2 points 2–3, 5): rewrite the `hIndepSets` step via the public
        `IndepSets_iff` (no `Kernel.IndepSets`/`ae_dirac_eq`/`Filter.eventually_pure` unfolding);
        reword docstrings from weak/strong to "avoidance-event formulation" /
        "generated-σ-algebra formulation"; remove the `(gpt-notes Def 1.1)` reference.
    - proof: |
        See the blueprint 90.10 informal for the existing proofs (hgen1/hgen2 stay; strong→weak
        stays essentially unchanged). The weak→global-strong proof: p2 as above; `IndepSets_iff`
        turns `IndepSets ({A i}) p2 μ` into the pairwise product condition, discharged by the weak
        hypothesis + `indepSet_iff_measure_inter_eq_mul` (measurability from `hA` +
        `measurableSet_bset`); `IndepSets.indep'` lifts to `Indep (generateFrom {A i})
        (generateFrom p2) μ`; `generateFrom p2 = generateFrom {t | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧
        t = A j}` by two containments (each `(A j)ᶜ` is a generator of p2 and σ-algebras are
        closed under complement; each `bset A U` is a finite intersection of non-neighbor
        complements). The iff is one line from the two directions.

        **Survey compile-test 2026-08-15 (attempt 1/15)**: the FULL package (def + `of_strong` +
        `.strong` + iff) compiles warning-free via `lake env lean` stdin against the main file's
        imports/namespace/variables; the verified skeleton is embedded at the end of this section
        — the Proof agent transcribes it into `tmp_dep_graph_global.lean` verbatim. Omit lines
        PINNED by testing (section vars are `{Ω ι} [MeasurableSpace Ω] {μ} [IsProbabilityMeasure
        μ] [Fintype ι] [DecidableEq ι]`; `omit [Fintype ι]` on a decl whose body needs it FAILS
        typeclass synthesis, since omit also removes the var from elaboration scope):
        - def + `of_strong`: `omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] in` (as
          before). Elaborated signatures: `{Ω ι} [MeasurableSpace Ω] {μ} (G) (A) : Prop` resp.
          `{Ω ι} [MeasurableSpace Ω] {μ} {G} {A} (h) : IsDependencyGraph G A`.
        - `.strong` + iff: `omit [Fintype ι] in`. `[DecidableEq ι]` IS used (`U ∪ V` needs the
          `Union (Finset ι)` instance, section-parameterized by `[DecidableEq ι]`, and
          `Finset.mem_union` has `[DecidableEq α]`); `[IsProbabilityMeasure μ]` used by
          `IndepSets.indep'`/`indepSet_iff_measure_inter_eq_mul` and kept. Elaborated: both carry
          `[IsProbabilityMeasure μ] [DecidableEq ι]`.
        - KEY simplifications found: `Set.mem_singleton_iff` is `Iff.rfl`, so `s ∈ {A i}` is DEFEQ
          `s = A i` — the old 90.10 `rintro s rfl t rfl _` patterns carry over verbatim to the
          `{A i}` singleton form; `Finset.mem_singleton` is `[simp]` (no DecidableEq).
        - `of_strong`: `bset A S` measurable w.r.t. `generateFrom {A j | j ∈ S}` exactly as in
          90.10; the new step is `generateFrom_mono` on the set inclusion
          `{A j | j ∈ S} ⊆ {t | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = A j}` (witness `j` with
          `i ∉ S` + `hnonadj`).
        - `.strong` hgen1/hgen2: same two-containment pattern as 90.10 with the global condition;
          the `i ∉ U`-witness for `k ∈ U` is `fun hki => hiU (hki ▸ hk)`; the `{j}`-finset
          witnesses for `(A j)ᶜ = bset A {j}` use `hji ((Finset.mem_singleton.mp hx).symm)` and
          `rw [Finset.mem_singleton.mp hk]`.
    - **prep**
        - Existing: `IsDependencyGraph`, `bset`, `bset_union`, `measurableSet_bset` (items 10.1/10.5/20.5/20.15).
        - `IndepSets_iff` — `IndepSets s1 s2 μ ↔ ∀ t1 t2, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2` (Independence/Basic.lean:175) — replaces the kernel-unfolding simp block.
        - `IndepSets.indep'` — π-system independence → σ-algebra independence (Basic.lean:495).
        - `IsPiSystem`, `Indep.indepSet_of_measurableSet`, `indepSet_iff_measure_inter_eq_mul`,
          `MeasurableSpace.generateFrom_mono`/`generateFrom_le` — as in 90.10.
    - verified skeleton (survey compile-tested 2026-08-15 via `lake env lean` stdin against the
      main file's imports/namespace/variables — compiles with zero errors, zero warnings, zero
      sorries; `bset`/`IsDependencyGraph`/`bset_union`/`measurableSet_bset` from the main file are
      in scope):
      ```lean
      omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] in
      /-- `IsDependencyGraphStrong G A` is the strong dependency-graph hypothesis of the Lovász
      local lemma: for every index `i`, the bad event `A i` is independent of the σ-algebra
      generated by all non-neighbor bad events `A j` (`j ≠ i`, `¬ G.Adj i j`) — equivalently,
      `A i` is independent of every Boolean combination of the non-neighbor events. -/
      def IsDependencyGraphStrong (G : SimpleGraph ι) (A : ι → Set Ω) : Prop :=
        ∀ i, Indep (MeasurableSpace.generateFrom {A i})
          (MeasurableSpace.generateFrom {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = A j}) μ

      omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] in
      /-- The strong (generated-σ-algebra) dependency-graph hypothesis implies the weak
      (avoidance-event) one: independence from the σ-algebra generated by all non-neighbor events
      implies independence from the finite intersection `bset A S` of their complements. -/
      theorem IsDependencyGraph.of_strong {G : SimpleGraph ι} {A : ι → Set Ω}
          (h : IsDependencyGraphStrong (μ := μ) G A) : IsDependencyGraph (μ := μ) G A := by
        intro i S hiS hnonadj
        have hAi : MeasurableSet[MeasurableSpace.generateFrom {A i}] (A i) :=
          MeasurableSpace.measurableSet_generateFrom rfl
        have hB : MeasurableSet[MeasurableSpace.generateFrom
            {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = A j}] (bset A S) := by
          have hle : MeasurableSpace.generateFrom {A j | j ∈ S} ≤
              MeasurableSpace.generateFrom {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = A j} :=
            MeasurableSpace.generateFrom_mono (by
              rintro t ⟨j, hjS, rfl⟩
              exact ⟨j, fun hij => hiS (hij ▸ hjS), hnonadj j hjS, rfl⟩)
          have hB' : MeasurableSet[MeasurableSpace.generateFrom {A j | j ∈ S}] (bset A S) := by
            letI : MeasurableSpace Ω := MeasurableSpace.generateFrom {A j | j ∈ S}
            simp only [bset]
            exact Finset.measurableSet_biInter S (fun j hj =>
              (MeasurableSpace.measurableSet_generateFrom
                (show A j ∈ {A k | k ∈ S} from ⟨j, hj, rfl⟩)).compl)
          exact hle _ hB'
        exact Indep.indepSet_of_measurableSet (μ := μ) (h i) hAi hB

      omit [Fintype ι] in
      /-- The weak (avoidance-event) dependency-graph hypothesis implies the strong
      (generated-σ-algebra) one when every bad event is measurable: independence from every
      finite intersection `bset A U` of non-neighbor complements lifts through the π-system of
      such intersections (`IndepSets.indep'`) to independence of the generated σ-algebras. -/
      theorem IsDependencyGraph.strong {G : SimpleGraph ι} {A : ι → Set Ω}
          (hA : ∀ i, MeasurableSet (A i)) (h : IsDependencyGraph (μ := μ) G A) :
          IsDependencyGraphStrong (μ := μ) G A := by
        intro i
        let p2 : Set (Set Ω) :=
          {u | ∃ U : Finset ι, i ∉ U ∧ (∀ j ∈ U, ¬ G.Adj i j) ∧ u = bset A U}
        have hp1m : ∀ s ∈ ({A i} : Set (Set Ω)), MeasurableSet s := by
          rintro s rfl
          exact hA i
        have hp2m : ∀ s ∈ p2, MeasurableSet s := by
          rintro s ⟨U, hiU, hnU, rfl⟩
          exact measurableSet_bset A hA U
        have hpi1 : IsPiSystem ({A i} : Set (Set Ω)) := by
          rintro s rfl t rfl _
          exact Set.inter_self (A i)
        have hpi2 : IsPiSystem p2 := by
          rintro u ⟨U, hiU, hnU, rfl⟩ v ⟨V, hiV, hnV, rfl⟩ _
          refine ⟨U ∪ V, ?_, ?_, ?_⟩
          · intro hi
            rw [Finset.mem_union] at hi
            exact hi.elim hiU hiV
          · intro j hj
            rw [Finset.mem_union] at hj
            exact hj.elim (hnU j) (hnV j)
          · simp
        have hIndepSets : IndepSets ({A i} : Set (Set Ω)) p2 μ := by
          rw [IndepSets_iff]
          intro s t hs ht
          rw [Set.mem_singleton_iff] at hs
          subst s
          obtain ⟨U, hiU, hnU, rfl⟩ := ht
          exact (indepSet_iff_measure_inter_eq_mul (μ := μ) (hA i) (measurableSet_bset A hA U)).mp
            (h i U hiU hnU)
        have hind : Indep (MeasurableSpace.generateFrom ({A i} : Set (Set Ω)))
            (MeasurableSpace.generateFrom p2) μ :=
          IndepSets.indep' (μ := μ) hp1m hp2m hpi1 hpi2 hIndepSets
        have hgen1 : MeasurableSpace.generateFrom p2 =
            MeasurableSpace.generateFrom {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = (A j)ᶜ} := by
          refine le_antisymm (MeasurableSpace.generateFrom_le ?_)
            (MeasurableSpace.generateFrom_mono ?_)
          · rintro u ⟨U, hiU, hnU, rfl⟩
            letI : MeasurableSpace Ω :=
              MeasurableSpace.generateFrom {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = (A j)ᶜ}
            simp only [bset]
            exact Finset.measurableSet_biInter U (fun k hk =>
              MeasurableSpace.measurableSet_generateFrom
                ⟨k, fun hki => hiU (hki ▸ hk), hnU k hk, rfl⟩)
          · rintro t ⟨j, hji, hnj, rfl⟩
            refine ⟨{j}, ?_, ?_, ?_⟩
            · intro hx
              exact hji (Finset.mem_singleton.mp hx).symm
            · intro k hk
              rw [Finset.mem_singleton.mp hk]
              exact hnj
            · simp [bset]
        have hgen2 :
            MeasurableSpace.generateFrom {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = (A j)ᶜ} =
            MeasurableSpace.generateFrom {t : Set Ω | ∃ j, j ≠ i ∧ ¬ G.Adj i j ∧ t = A j} := by
          refine le_antisymm (MeasurableSpace.generateFrom_le ?_)
            (MeasurableSpace.generateFrom_le ?_)
          · rintro t ⟨j, hji, hnj, rfl⟩
            exact (MeasurableSpace.measurableSet_generateFrom
              (show A j ∈ ({t : Set Ω | ∃ k, k ≠ i ∧ ¬ G.Adj i k ∧ t = A k}) from
                ⟨j, hji, hnj, rfl⟩)).compl
          · rintro t ⟨j, hji, hnj, rfl⟩
            simpa using (MeasurableSpace.measurableSet_generateFrom
              (show (A j)ᶜ ∈ ({t : Set Ω | ∃ k, k ≠ i ∧ ¬ G.Adj i k ∧ t = (A k)ᶜ}) from
                ⟨j, hji, hnj, rfl⟩)).compl
        rw [hgen1, hgen2] at hind
        exact hind

      omit [Fintype ι] in
      /-- The weak and strong dependency-graph hypotheses are equivalent (when every bad event is
      measurable): the avoidance-event formulation and the generated-σ-algebra formulation. -/
      theorem isDependencyGraph_iff_strong {G : SimpleGraph ι} {A : ι → Set Ω}
          (hA : ∀ i, MeasurableSet (A i)) :
          IsDependencyGraph (μ := μ) G A ↔ IsDependencyGraphStrong (μ := μ) G A :=
        ⟨IsDependencyGraph.strong hA, IsDependencyGraph.of_strong⟩
      ```
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | ONE attempt, full package (def + `of_strong` + `.strong` + iff): transcribe the survey-verified skeleton (compiles via stdin, zero sorries/warnings) into the tmp — global-form def `IsDependencyGraphStrong`, both bridge directions re-proved (strong→weak via `generateFrom_mono` restriction; weak→strong via π-system p2 + `IndepSets_iff` + `IndepSets.indep'` + hgen1/hgen2), new `isDependencyGraph_iff_strong` wrapper; omit lines pinned: def/`of_strong` `omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]`, `.strong`/iff `omit [Fintype ι]` (DecidableEq genuinely needed: `U ∪ V`/`Finset.mem_union`) | Transcribed the survey-verified skeleton verbatim into a 185-line STANDALONE tmp (no import of the main module; `bset`/`IsDependencyGraph`/`bset_union`/`measurableSet_bset` copied in): global-form `IsDependencyGraphStrong` def, `of_strong` (no `hA`, via `generateFrom_mono` restriction), `.strong` (`hA`, `omit [Fintype ι]`, π-system p2 + `IndepSets_iff` + `IndepSets.indep'` + hgen1/hgen2), new `isDependencyGraph_iff_strong`. `lake env lean` exit 0, no output; zero sorries/warnings. | Independently re-verified: tmp `lake env lean` exit 0 no output, LSP diagnostics empty, 185 lines, grep for sorry/axiom/admit/native_decide/# clean; `#print axioms` of all four declarations = `[propext, Classical.choice, Quot.sound]` (standard). Statement matches the 90.15 informal exactly: global-form def (`∀ i`, all non-neighbor events), `of_strong` without `hA`, `.strong` with `hA` and no `[Fintype ι]`, `hIndepSets` via public `IndepSets_iff` (no Kernel-internal unfolding). REPLACED the old per-finite-S 90.10 declarations in `LovaszLocal.lean` with the new four; new docstrings reworded to avoidance-event / generated-σ-algebra formulations (no weak/strong wording), `[alonSpencer2016]` cited instead of `(gpt-notes Def 1.1)`; module docstring `IsDependencyGraphStrong` + bridge bullets updated. Main file `lake env lean` exit 0 no warnings, LSP diagnostics empty, `lake build StatsMLlib.Probability.LovaszLocal` succeeds; tmp deleted. Committed to submodule branch `zzk/lovasz-local-lemma-gptv2`. | `tmp_dep_graph_global.lean` |
