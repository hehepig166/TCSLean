# Blueprint: Moser–Tardos Algorithmic Lovász Local Lemma (Asymmetric Form, Variable Framework, Finite Truncation)

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
- **Newest entries first.** Fresh items carry the header row only (no attempts yet).

### Numbering

Hierarchical: `## 10. Group`, `### 10.1. item`, `#### 10.1.1. sub-item`. Gaps allowed for insertion.

Group ranges: `10`–`19` Definitions, `20`–`39` Basic properties, `40`–`59` Core lemmas,
`60`–`79` Main theorem, `80`–`99` Corollaries.

### Status Lifecycle

```
pending ──→ working ──→ done
  ↑           │
  └───────────┘  (retry)
```

`attempts = bucket / bucket` with status ≠ `done` → **blocked**, needs human intervention.

### Location (project deviation from the generic harness)

This BLUEPRINT lives in the **outer repo** at
`doc/moser-tardos/02_blueprint/BLUEPRINT.md` (doc-folder lifecycle, talagram/lovasz precedent),
NOT at the project root of the `StatsMLlib` submodule. The Lean targets live in the submodule
under `StatsMLlib/Probability/MoserTardos/`. Tmp files live in the **same directory as the
target Lean file** (`tmp_<theme>.lean`), per `harness/CONVENTIONS.md` — never at the project
root or in `harness/tmp/`.

## Overview

**Target.** The Moser–Tardos resampling algorithm for the asymmetric Lovász Local Lemma in the
*variable framework* (arXiv:0903.0544, Thm 1.2 = reference notes Thm 5.1): the expected number
of resamplings of each bad event is ≤ `x i / (1 - x i)`, the total ≤ `∑ i, x i / (1 - x i)`,
with the multiplicative Markov tail bound and the constructive-LLL corollary
`∃ σ, ∀ i, σ ∉ A i` — all stated on a **finite truncation** (an `N+1`-row resampling table per
variable, uniform in `N`), with no infinite-product machinery. Approved by the proposal:
[`doc/moser-tardos/01_proposal/proposal.md`](../01_proposal/proposal.md) (statements, scope
decisions, folder plan, the A1–F27 decomposition). Authoritative proof audit + design decisions:
[`01_proposal/survey/B_proof_strategy.md`](../01_proposal/survey/B_proof_strategy.md) (§3 proof
audit, §4 design decisions, §5 declaration table, §6 PR split); verified mathlib names with
file:line: [`01_proposal/survey/A_mathlib_inventory.md`](../01_proposal/survey/A_mathlib_inventory.md).

**Setup.** Finite event index `ι` and variable index `κ` (both `[Fintype] [DecidableEq]`);
variable `j` takes values in a measurable space `Ω j` with probability measure `μ j`; the joint
law `μπ μ := Measure.pi μ` on `Π j, Ω j`. Bad events `A i ⊆ Π j, Ω j` are measurable (`hA`) and
`DeterminedBy` the finset `vbl i`. The dependency structure is the **variable-overlap graph**
(`overlapGraph vbl`), with inclusive neighborhood `Γ⁺ i = insert i ((overlapGraph vbl).neighborFinset i)`.
The LLL condition for weights `x : ι → ℝ`, `0 ≤ x i`, `x i < 1`:

```
μπ μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j))   (LLL)
```

Truncated table `ΩN N Ω := Π j, Fin (N + 1) → Ω j` (**N+1 rows** — survey B finding 1),
`μN N μ := Measure.pi` over `Σ j, Fin (N+1)` (a probability measure, inferable). The algorithm
is a deterministic function of the table: state `c : κ → Fin (N+1)`; while a violated event is
available, resample all variables of `pick (Avail …)`. It yields the **padded log**
`log : ΩN N Ω → ℕ → Option ι` (survey B finding 2), the stopping time `R ≤ N`, and the count
`countLog ω i = #{t < N : log ω t = some i}`.

**Main theorem** (`moserTardos_bound`, item 60.2 — pinned shape, survey B §1.1):

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
parametricity. The `x i = 0` case needs no division: absorbed by a single `by_cases` (item
60.2). All arithmetic on the right is ℝ inside `ENNReal.ofReal`; **no ENNReal division occurs
anywhere**.

**Corollaries** (all in initial scope, items 60.3–60.5; symmetric form 70.1 is a follow-up PR):

```lean
theorem moserTardos_total (…same hypotheses…) :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))

theorem moserTardos_tail (…same hypotheses…) :
    (N : ℝ≥0∞) * μN N μ {ω | R vbl A pick hpick ω = N}
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))        -- multiplicative Markov form

theorem moserTardos_exists (…same hypotheses…) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i                    -- constructive LLL; no [Nonempty (Π j, Ω j)]

theorem moserTardos_symmetric {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ p)
    (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1) (…pick…) :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / d)
```

**Proof strategy** (notes §6–§20, audited for the truncation in survey B §3):
resampling algorithm → execution log → witness trees (custom `WitnessTree`, reverse-scan fold
with the deepest-eligible rule, C10 fold spec lemma) → structural lemmas (properness Prop 10.1;
Lemma 11.1/Cor 11.2 depth facts; Prop 12.1 injectivity) → coupling lemma (structural τ-check on
injective table coordinates; `μN {∃t < R, T = τ} ≤ treeProd τ`) → Galton–Watson sum bound
(`gwWeight` telescope + `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ 1`) → final chain
(`by_cases x i = 0` root-factor case vs `x i > 0` GW case).

**Pinned design decisions** (proposal + survey B §4; the attempt loop must not revisit these):
(1) pick rule parameterized (`pick`/`hpick`), no `[LinearOrder ι]`; (2) custom `WitnessTree`
with `List` children (mathlib's `BinaryTree` is a binary storage tree); (3) `IsGood` =
proper + same-depth vertices have disjoint `vbl`, path-based on the abstract tree; (4)
`ΩN` = `Fin (N+1)` rows; (5) `lintegral`/ENNReal-first expectations (ℝ only inside `ofReal`),
matching `LovaszLocal.lean` house style; (6) `DeterminedBy` as an ∃-hypothesis; (7)
time-labeled construction trees `WitnessTree (ℕ × ι)` with `forgetTime` transport to abstract
trees. Code conventions (survey D §1): Apache-2.0 header, `/-!` docstring with
`## Main definitions` / `## Main results` / `## References`, `namespace MoserTardos`,
`autoImplicit := false`, `·` bullets, 100-char lines, warning-free builds, no
sorry/axiom/`#`-commands, `(μ := μ)` discipline.

**File layout** (proposal "Proposed Location"; all 6 modules new; ~2760 core lines ≈ 2400–2900
estimate from survey B §6):

| File | Items | Content | Est. lines |
|---|---|---|---|
| `StatsMLlib/Probability/MoserTardos/VariableModel.lean` | 10.1–10.3 | `overlapGraph`/Γ⁺, `DeterminedBy`, `ΩN`/`μN`/`μπ` | ~85 |
| `StatsMLlib/Probability/MoserTardos/Algorithm.lean` | 20.1–20.5 | state/step/run, stopping time `R`, padded log + `countLog`, measurability | ~390 |
| `StatsMLlib/Probability/MoserTardos/WitnessTree.lean` | 30.1–30.7 | tree type + path API, construction `treeAt`/`T`, structural lemmas | ~640 |
| `StatsMLlib/Probability/MoserTardos/Coupling.lean` | 40.1–40.3 | τ-check, `check_probability`, coupling lemma | ~570 |
| `StatsMLlib/Probability/MoserTardos/GaltonWatson.lean` | 50.1–50.3 | `gwWeight` + telescope, `𝒯_i(N)` Fintype, sum bound | ~420 |
| `StatsMLlib/Probability/MoserTardos/Basic.lean` | 60.1–60.5 | counting identity, **`moserTardos_bound`**, total/tail/exists corollaries; carries the module `/-!` docstring and re-exports the public API | ~460 |
| `StatsMLlib/Probability/MoserTardos/Symmetric.lean` | 70.1 | `moserTardos_symmetric` (follow-up PR) | ~150 |

The files do not exist yet — Setup creates them with the skeleton on first touch; tmp files
live next to them in the same folder. `FILE_TREE.md` / `README.md` edits are PR chore, not
blueprint items (proposal).

**Harness conventions (this project).**
- Attempt loop per item: **Survey → Setup → Proof → Review** (`harness/CONVENTIONS.md`); Survey
  writes the attempt goal into the log, Review updates status, handles the tmp lifecycle, commits.
- Commit convention: submodule commits `feat(MT.<item-no>): attempt <N> — <brief outcome>` on
  `zzk/moser-tardos` (stacked on `zzk/lovasz-local-lemma-gptv2`); outer-repo doc commits
  `doc(MT.<item-no>): <summary>; bump StatsMLlib pointer` (proposal "Git choreography").
- Suggested tmp themes (Setup's choice, one per item): `tmp_variable_model` (10.1–10.3),
  `tmp_step` (20.1), `tmp_run` (20.2), `tmp_stopping` (20.3), `tmp_log` (20.4),
  `tmp_measurable` (20.5), `tmp_witness_tree` (30.1), `tmp_attach` (30.2), `tmp_tree_at` (30.3),
  `tmp_tree_proper` (30.4), `tmp_tree_depth` (30.5), `tmp_tree_injective` (30.6),
  `tmp_tree_good` (30.7), `tmp_tree_profile` (40.1), `tmp_check_prob` (40.2), `tmp_coupling`
  (40.3), `tmp_gw_weight` (50.1), `tmp_trees_finset` (50.2), `tmp_gw_sum` (50.3),
  `tmp_count_identity` (60.1), `tmp_mt_bound` (60.2), `tmp_mt_total` (60.3), `tmp_mt_tail`
  (60.4), `tmp_mt_exists` (60.5), `tmp_mt_symmetric` (70.1).

**Item count and priorities.** 27 items: 19 priority-3 (critical path, ≈ 2370 lines) + 7
priority-2 (off-path needed) + 1 priority-1 (symmetric form, follow-up PR). Total est.
≈ 2765 core + 150 symmetric ≈ 2915 lines (survey B §6: 2400–2900 + 150). The three **Hard**
items are 30.2 (fold spec lemma), 40.2 (check probability), 40.3 (coupling), plus 60.2
(assembly with the `x i = 0` split).

**Critical path** (priority-3 items, survey B §5): 10.3 → 20.2 → 20.4 → 30.1 → 30.2 → 30.3 →
30.4 → 30.5 → 30.6 → 40.2 → 40.3 → 50.1 → 50.2 → 50.3 → 60.1 → 60.2 → 60.3 → 60.4 → 60.5.
The priority-2 items sit immediately before their consumers in dependency order and must be
attempted at that point regardless of priority: 10.1/10.2 before 20.x and 30.5 (Γ⁺ and
`DeterminedBy`), 20.1 before 20.2 (survey B's critical path includes B4), 20.3 before 20.4,
30.7 before 40.3, 40.1 before 40.2, 20.5 before 60.4. (Survey B's critical path also lists
B4/20.1; this blueprint follows the mission's priority assignment — 20.1 = 2 — with the
dependency order enforcing it is done first anyway.)

## Items

---
## 10. Variable Model (Definitions)

### 10.1. overlapGraph, mem_gammaPlus_of_overlap

- **meta**
    - kind: def
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/VariableModel.lean`
- **informal**
    - statement: |
        The variable-overlap dependency graph and its inclusive neighborhood (survey B A1,
        notes §2; difficulty Easy, est. ~40 lines):
        - `overlapGraph (vbl : ι → Finset κ) : SimpleGraph ι` with
          `Adj i j ↔ i ≠ j ∧ (vbl i ∩ vbl j).Nonempty` (loopless via the `i ≠ j` guard).
        - `gammaPlus (vbl : ι → Finset κ) (i : ι) : Finset ι :=
          insert i (overlapGraph vbl).neighborFinset i` (the inclusive neighborhood Γ⁺ i).
        - `mem_overlap_neighborFinset : j ∈ (overlapGraph vbl).neighborFinset i ↔
          i ≠ j ∧ (vbl i ∩ vbl j).Nonempty` — the `neighborFinset` membership bridge for
          the overlap graph (unfolds `overlapGraph` under `mem_neighborFinset`).
        - `mem_gammaPlus_of_overlap : i = j ∨ (vbl i ∩ vbl j).Nonempty → i ∈ gammaPlus vbl j`
          — the two-case lemma that fixes the notes' sloppy Lemma 11.1 sentence ("Hence
          [u] ∈ Γ([v])" is wrong when `[u] = [v]`): if `i ≠ j` the overlap gives adjacency
          (neighbor membership), and if `i = j` the inclusive self-loop `i ∈ insert i …`
          applies — both cases land in Γ⁺(j). This is the exact input Lemma 11.1 (item 30.5)
          consumes; no fix needed beyond stating it.
        - `mem_gammaPlus_self : i ∈ gammaPlus vbl i` — the inclusive self-membership
          (`@[simp]`; via `Finset.mem_insert_self`).
        - `mem_gammaPlus : j ∈ gammaPlus vbl i ↔ j = i ∨ (overlapGraph vbl).Adj i j` — the
          membership iff for Γ⁺ (loop-free, so safe as `@[simp]` if Proof wants; downstream
          items 30.5/11.1 and Cor 11.2 consume Γ⁺ membership through these two lemmas).
        Design decision (survey B §1.1, overruling survey A §4.1's bare-`Adj` suggestion):
        `SimpleGraph ι`, because `hLLL` must be stated with
        `(overlapGraph vbl).neighborFinset` so the future `LovaszLocal.IsDependencyGraph`
        bridge matches definitionally (proposal API question 5).
    - proof: |
        Definitional, no deep proof: build via the `SimpleGraph` structure constructor
        (fields `Adj`/`symm`/`loopless`; do NOT use `SimpleGraph.fromRel`, which
        symmetrizes with `∨` and would break the definitional `Adj`) with `symm` by
        `Finset.inter_comm` and `loopless` by the `i ≠ j` guard; `mem_gammaPlus_of_overlap`
        splits the disjunction — case `i = j` via `Finset.mem_insert`, case
        `(vbl i ∩ vbl j).Nonempty` splits again on `i = j` (mem_insert) vs `i ≠ j`
        (adjacency via `mem_neighborFinset` + `Finset.inter_comm`).
        `[DecidableRel (overlapGraph vbl).Adj]` (needed by `neighborFinset`'s
        `[Fintype (G.neighborSet v)]`) falls out of `[DecidableEq ι]` alone —
        `Finset.decidableNonempty` is unconditional and `≠` uses `instDecidableNe`; no
        `classical` needed, `gammaPlus` stays computable. `[DecidableEq κ]` is still
        required in scope to elaborate the `∩` in `Adj` (the `Inter (Finset α)` instance
        lives under `variable [DecidableEq α]`).
- **prep**
    - `SimpleGraph` — `Mathlib/Combinatorics/SimpleGraph/Basic.lean:92-97` —
      `structure SimpleGraph (V : Type u)` with fields `Adj : V → V → Prop`,
      `symm : Std.Symm Adj`, `loopless : Std.Irrefl Adj` (batteries relations; `Std.Symm`
      has implicit `{a b}` binders, so `intro i j h` introduces them). Build with the
      structure constructor + explicit `symm`/`loopless`; `SimpleGraph.fromRel`
      (Basic.lean:133) exists but is NOT used (it adds `r a b ∨ r b a`).
    - `SimpleGraph.neighborFinset` — `Mathlib/Combinatorics/SimpleGraph/Finite.lean:166` —
      requires `[Fintype (G.neighborSet v)]` (local finiteness), which synthesizes from
      `[Fintype ι]` + `[DecidableRel G.Adj]` via `Subtype.fintype` (module doc
      Finite.lean:36-40).
    - `SimpleGraph.mem_neighborFinset` — `Finite.lean:177` — `@[simp]`,
      `w ∈ G.neighborFinset v ↔ G.Adj v w`; also `notMem_neighborFinset_self`
      (Finite.lean:180).
    - `Finset.insert` — `Insert (Finset α)` instance, `Mathlib/Data/Finset/Insert.lean:344-347`,
      requires `[DecidableEq α]`; `Finset.mem_insert` — `Insert.lean:365` — `@[simp]`,
      `a ∈ insert b s ↔ a = b ∨ a ∈ s`; `mem_insert_self` — `Insert.lean:368`.
    - `Finset.inter` — `Inter (Finset α)` instance, `Mathlib/Data/Finset/Lattice/Basic.lean:55-64`,
      requires `[DecidableEq α]` (so `overlapGraph`/`gammaPlus` need `[DecidableEq κ]` in
      scope); `Finset.mem_inter` `@[simp]` — Lattice/Basic.lean:197; `Finset.inter_comm` —
      Lattice/Basic.lean:224 — NOT simp, use `rw`/`simpa [Finset.inter_comm]`.
    - `Finset.Nonempty` — `Mathlib/Data/Finset/Empty.lean:47` — `∃ x, x ∈ s`;
      `Finset.decidableNonempty` — Empty.lean:50 — unconditional (no `[DecidableEq]`).
    - Section variables for the 10.1 block: `{ι : Type u} [Fintype ι] [DecidableEq ι]` plus
      `[DecidableEq κ]` (reuse the file's existing `{κ} [Fintype κ]`). Integration: either
      add `[DecidableEq κ]` to the file-level section variables (existing ΩN/μN/μπ decls
      are unaffected — unused section vars are not added) or wrap 10.1 in its own section.
    - Import: `Mathlib.Combinatorics.SimpleGraph.Finite` (import chain
      `Finite → Maps → Dart → Basic` verified: Finite.lean:8, Maps.lean:8); the Finset API
      is already available via the existing `Mathlib.MeasureTheory.Constructions.Pi` import.
    - Internal deps (survey B §5): none — leaf item.
- **note**
    - Deviations from the sketch: (1) `omit [Fintype κ]` inside `section OverlapGraph` —
      the namespace-level `variable {κ : Type u} [Fintype κ]` auto-includes the binder in
      every theorem header mentioning `κ`, but no declaration in the section uses it
      (`linter.unusedSectionVars` fires without the omit); (2) an explicit named
      `overlapGraph.instDecidableRelAdj` instance was added (`change` to the unfolded
      `Adj` + `infer_instance`) — `neighborFinset`'s local-finiteness
      `Fintype (G.neighborSet v)` synthesizes from it; (3) `mem_gammaPlus_of_overlap`
      concludes `j ∈ gammaPlus vbl i` (i/j mirrored vs the item statement
      `i ∈ gammaPlus vbl j`) — equivalent under the `i = j` disjunct; 30.5 consumes it
      with a rename.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `overlapGraph` (structure constructor, `Adj i j := i ≠ j ∧ (vbl i ∩ vbl j).Nonempty`) and `gammaPlus` in `VariableModel.lean`; prove `mem_gammaPlus_of_overlap`, `mem_overlap_neighborFinset`, `mem_gammaPlus_self` (`@[simp]`), and `mem_gammaPlus` (`j ∈ gammaPlus vbl i ↔ j = i ∨ (overlapGraph vbl).Adj i j`) | 4/4 lemmas per the Survey sketch: `mem_overlap_neighborFinset` (rw `mem_neighborFinset` + rfl), `mem_gammaPlus_self` (`@[simp]`, `mem_insert_self`), `mem_gammaPlus` (`mem_insert` + `mem_neighborFinset`), `mem_gammaPlus_of_overlap` (rcases on the disjunction + nested by_cases); defs `overlapGraph`/`gammaPlus` + `overlapGraph.instDecidableRelAdj` instance; tmp compiled 0 errors/warnings | Independently verified (0 LSP diagnostics, `lake env lean` exit 0, no sorry/axiom/admit, lines ≤ 100 after dropping the tmp marker block). Integrated into `VariableModel.lean` as `section OverlapGraph` with `omit [Fintype κ]` and `instDecidableRelAdj`; `SimpleGraph.Finite` import + module docstring updated; tmp deleted. `lake build StatsMLlib.Probability.MoserTardos.VariableModel` OK (1857 jobs) | `tmp_variable_model.lean` |

### 10.2. DeterminedBy

- **meta**
    - kind: def
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/VariableModel.lean`
- **informal**
    - statement: |
        Event determinism (survey B A2, notes §1; difficulty Easy, est. ~15 lines):
        ```lean
        def DeterminedBy (A : Set (Π j, Ω j)) (S : Finset κ) : Prop :=
          ∃ f : (Π j : S, Ω j) → Prop, ∀ σ, σ ∈ A ↔ f fun j => σ j
        ```
        Event `A` is determined by the variables in `S`: membership depends only on the
        restriction `fun j => σ j` to `S`, through a predicate `f` on `Π j : S, Ω j`.
        Design decision (survey B §4.6, proposal API question 3): the **∃-form** — exactly
        what the structural τ-check consumes (the coupling section picks witnesses once via
        `Classical.choose`, `noncomputable`); no coordinate completion, no
        `Nonempty (Ω j)`. Survey A §5.4's cylinder form
        (`∃ C, MeasurableSet C ∧ A = cylinder S C`) was rejected: its built-in measurability
        is redundant with the separate `hA` hypothesis and the algorithm evaluates `A`
        through `f`, not through cylinders. The data interface
        (`eval : ∀ i, (Π j : vbl i, Ω j) → Prop` + `hEval`) is a mechanical wrapper for
        applications (follow-up, out of scope).
    - proof: |
        Definition, no proof.
- **prep**
    - `SetLike.instCoeSortType` — `Mathlib/Data/SetLike/Basic.lean:125`
      (`instance (priority := 100) : CoeSort A (Type _)`): the CoeSort instance that makes
      the domain `Π j : S, Ω j` elaborate with `S : Finset κ`. Resolution verified via
      `trace.Meta.synthInstance` (`CoeSort (Finset κ) (Type _)` → `SetLike.instCoeSortType`,
      using Finset's `SetLike` instance `Finset.instSetLike`, `Mathlib/Data/Finset/Defs.lean:101`);
      the domain is the subtype `{x // x ∈ S}` (`↥S`).
    - Subtype coercion `(↑j : κ)` for `j : S` — `σ j` elaborates as `σ ↑j` (verified in the
      `#print` of the compiled def), i.e. `Subtype.val` / `SetLike` `↑`. Also `j.1` works,
      and `(fun j : S => σ j) = (fun j : S => σ j.1)` is `rfl`.
    - `Set` membership (`σ ∈ A`) — core. No imports beyond the file's current ones.
    - **Compile check (survey attempt 1):** the def compiles **verbatim** as written in the
      informal statement under the file's exact context (`import
      Mathlib.MeasureTheory.Constructions.Pi` + `Mathlib.Combinatorics.SimpleGraph.Finite`,
      `set_option autoImplicit false`, `open MeasureTheory`, namespace-level variable block
      incl. μ). `#print DeterminedBy` gives the clean signature
      `{κ : Type u} → {Ω : κ → Type v} → Set ((j : κ) → Ω j) → Finset κ → Prop` with body
      `∃ f, ∀ σ, σ ∈ A ↔ f fun j ↦ σ ↑j` — **no `[Fintype κ]`, no
      `[∀ j, MeasurableSpace (Ω j)]`, no μ binders, no linter warnings**. The 10.1
      `omit [Fintype κ]` auto-include issue is **theorem-only**: `def`s do not auto-include
      unused instance section variables (verified: `theorem foo (S : Finset κ) : True`
      gets `[Fintype κ]` + the `unusedSectionVars` warning; `def bar (S : Finset κ) : Prop`
      does not). Witness use as pinned by §4.6: `⟨f, h⟩` proves `DeterminedBy` from
      `h : ∀ σ, σ ∈ A ↔ f fun j => σ j`, and `Classical.choose h` recovers `f` with
      `Classical.choose_spec h σ : σ ∈ A ↔ Classical.choose h (fun j : S => σ j)`.
    - Placement: namespace level, after `μπ.instIsProbabilityMeasure` (main-file line 96)
      and before `section OverlapGraph` (line 98) — `DeterminedBy` is about events, not the
      overlap graph, and needs none of the OverlapGraph section variables.
    - Review integration: add a `DeterminedBy` bullet to the module docstring's "Main
      definitions" list.
    - Internal deps (survey B §5): none — leaf item.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `DeterminedBy` in `tmp_variable_model.lean` (pure def, verbatim from the blueprint informal statement; Setup writes it, no proof phase). Survey-verified: compiles with the file's current imports/options; clean signature with no auto-included `[Fintype κ]` / `[∀ j, MeasurableSpace (Ω j)]` (defs are exempt from theorem-style instance auto-inclusion); domain coercion via `SetLike.instCoeSortType` | pure def — written by Setup, no proof phase | Independently verified: tmp (32 lines) had 0 LSP diagnostics, no sorry/axiom/admit. Integrated into `VariableModel.lean` at namespace level after `μπ.instIsProbabilityMeasure` and before `section OverlapGraph`, docstring kept; `DeterminedBy` bullet added to the module docstring's "Main definitions" list. tmp deleted. Integrated file: 0 LSP diagnostics; `lake build StatsMLlib.Probability.MoserTardos.VariableModel` OK (1857 jobs) | `tmp_variable_model.lean` |

### 10.3. ΩN, μN

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/VariableModel.lean`
    - note: **ΩN is Sigma-indexed** (`Π p : Σ _ : κ, Fin (N + 1), Ω p.1`), not the curried
      `Π j : κ, Fin (N + 1) → Ω j` of the informal statement — required for defeq with
      `Measure.pi`'s domain; downstream item 20.1 must use `assign … j := ω ⟨j, c j⟩`
      (defeq: `⟨j, c j⟩.1 = j`); `ΩN.instMeasurableSpace` added (typeclass search does not
      unfold the semireducible `ΩN`).
- **informal**
    - statement: |
        The truncated resampling table and its law (survey B A3, notes §7; difficulty Easy,
        est. ~30 lines; critical path ★):
        ```lean
        def ΩN (N : ℕ) (Ω : κ → Type*) : Type* := Π j : κ, Fin (N + 1) → Ω j
        def μN (N : ℕ) (μ : ∀ j, Measure (Ω j)) : Measure (ΩN N Ω) :=
          Measure.pi (fun p : Σ j : κ, Fin (N + 1) => μ p.1)
        ```
        plus the inferable instance `IsProbabilityMeasure (μN N μ)` and the notation
        `μπ μ := Measure.pi μ` for the joint law on `Π j, Ω j` (used by `hLLL` and the
        τ-check).
        **PITFALL (survey B finding 1, load-bearing): the table MUST have `Fin (N+1)` rows,
        not `Fin N`.** The notes' convention is cumulative ("resampled s times ⟹ value is
        X^(s)"): an execution of up to `N` steps can resample one variable `N` times,
        reaching row `N`. With `Fin N` rows a variable resampled at every step would
        overflow at the last step, and the coupling identity (14.5) is provably
        incompatible with any "step t uses row t" convention. `Fin (N+1)` fixes this with
        zero other changes.
        Cosmetic note (survey A §2.1.1): write the Sigma binder `(_ : κ) × Fin (N+1)` — a
        named binder `(j : κ)` triggers an unused-variable warning.
    - proof: |
        Definition, no proof. `IsProbabilityMeasure (μN N μ)` is
        `Measure.pi.instIsProbabilityMeasure` (survey A compile test (5), 2 lines);
        `Fintype (Σ j, Fin (N+1))` is automatic from `[Fintype κ]`; `Measure.pi` needs no
        `DecidableEq` on the index type (survey A §2.1.1).
- **prep**
    - `Measure.pi` — `Mathlib/MeasureTheory/Constructions/Pi.lean:210`; signature verified in
      v4.32.0 via LSP:
      `{ι} {α} [Fintype ι] [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) : Measure (∀ i, α i)`.
      **`[Fintype ι]` IS required** (no `DecidableEq ι`, no `SigmaFinite` needed). It is an
      `irreducible_def`, so `dsimp` stops at `Measure.pi` — harmless, instance synthesis
      matches by head constant.
    - `Measure.pi.instIsProbabilityMeasure` — `Mathlib/MeasureTheory/Constructions/Pi.lean:310`
      (`[∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (Measure.pi μ)`).
    - `Sigma.instFintype` — `Mathlib/Data/Fintype/Sigma.lean:43`: `Fintype (Σ j, Fin (N+1))`
      from `[Fintype κ]` (no `DecidableEq` needed) — satisfies `Measure.pi`'s `[Fintype ι]`
      for the index type `Σ j, Fin (N+1)`.
    - `Pi.instFintype` — `Mathlib/Data/Fintype/Pi.lean:134` (requires `[DecidableEq α]
      [Fintype α] [∀ a, Fintype (β a)]`; NOT needed for 10.3 — only for downstream
      `State`/`𝒯_i(N)` finiteness).
    - `IsProbabilityMeasure` — `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:64`.
    - **API decision (pinned by Survey, attempt 1):** declare the section variables with
      braces — `variable {κ : Type u} [Fintype κ]`, `variable {Ω : κ → Type v}
      [∀ j, MeasurableSpace (Ω j)]`, `variable {μ : ∀ j, Measure (Ω j)}
      [∀ j, IsProbabilityMeasure (μ j)]`. Auto-bound section variables inherit the declared
      binder implicitness (verified: mathlib's `Subgroup.center` under `variable (G : Type u)`
      elaborates to `(G : Type u) → …`), so braces make `Ω` an **implicit** auto-bound argument
      of `μN`/`μπ` — use sites `μN N μ` and `μπ μ` as pinned by the main theorem statements and
      `hLLL` (Overview). `ΩN` keeps its **explicit** header binder
      `def ΩN (N : ℕ) (Ω : κ → Type v) : Type (max u v) := Π j : κ, Fin (N + 1) → Ω j`
      (use site `ΩN N Ω`, Overview line 100); the header binder shadows the brace variable.
    - Internal deps (survey B §5): none — leaf item.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | create ΩN/μN/μπ + probability instances | pure defs — written by Setup, no proof phase | Verified independently: LSP 0 diagnostics + `lake build StatsMLlib.Probability.MoserTardos.VariableModel` success (1845/1845). No sorry/axiom/admit, no `#`-commands, no unused vars, all lines ≤ 100 chars. Integrated into `VariableModel.lean` (first module of the new folder; tmp marker header dropped, one docstring line rewrapped); tmp file deleted. Sigma-indexed `ΩN` deviation recorded in meta note — downstream 20.1 must use `assign … j := ω ⟨j, c j⟩`. | `tmp_variable_model.lean` |

---
## 20. Algorithm

### 20.1. State, assign, Avail, step

- **meta**
    - kind: def
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Algorithm.lean`
- **informal**
    - statement: |
        The availability-carrying one-step algorithm (survey B B4, notes §4; difficulty
        Easy–Med, est. ~90 lines; prototype-compiled in `/tmp/mt_proto_run.lean`):
        - `State (N : ℕ) := κ → Fin (N + 1)` — rows consumed per variable.
        - `assign (ω : ΩN N Ω) (c : State N) : Π j, Ω j` with `(assign ω c) j = ω ⟨j, c j⟩`
          — total because `c j : Fin (N+1)`. The Sigma-pair index is the 10.3 integration
          note: `ΩN` is Sigma-indexed and `⟨j, c j⟩.1 = j` definitionally (the informal
          `ω j (c j)` form was written against the pre-10.3 curried table).
        - `Avail (ω : ΩN N Ω) (c : State N) : Set ι :=
          {i | assign ω c ∈ A i ∧ ∀ j ∈ vbl i, (c j : ℕ) < N}` — violated AND rows
          available (the availability guard exists only to make `step` total; it never
          bites before `N` steps — see `run_count_le` in 20.2). The explicit `ℕ` coercion
          is mandatory: mathlib v4.32.0 has no heterogeneous `LT (Fin n) ℕ` instance and
          `NatCast (Fin n)` is a bare `def` with `[NeZero n]` (core
          `Init/Data/Fin/Lemmas.lean:127`), so `(c j) < N` does not elaborate.
        - `Payload` — the certificate-carrying subtype
          `{e : ι // assign ω c ∈ A e ∧ ∀ j ∈ vbl e, (c j : ℕ) < N}`.
        - `step (ω : ΩN N Ω) (c : State N) : State N × Option (Payload ω c)` — if
          `Avail ω c` is nonempty, pick `pick ⟨Avail ω c, h⟩` (via `hpick`), advance
          `c j ↦ c j + 1` for `j ∈ vbl e` using the certificate in the `Fin` proof term
          `⟨(c j : ℕ) + 1, Nat.succ_lt_succ (cert j hj)⟩`, and return `(c', some ⟨e, …⟩)`;
          else `(c, none)`. `noncomputable`, with `classical` in the body (prototype-
          proven; no `[DecidableEq ι]`/`[DecidableEq κ]` hypotheses).
        - `step_fst_val_eq_of_mem {e : Payload vbl A ω c}
          (h : (step vbl A pick hpick ω c).2 = some e) {j : κ} (hj : j ∈ vbl e.1) :
          ((step vbl A pick hpick ω c).1 j : ℕ) = (c j : ℕ) + 1` and
          `step_fst_eq_of_not_mem (h : (step vbl A pick hpick ω c).2 = some e) {j : κ}
          (hj : j ∉ vbl e.1) : (step vbl A pick hpick ω c).1 j = c j` — the step-advance
          spec: given the payload, the state advanced exactly on `vbl e` (value + 1) and
          is unchanged elsewhere. `if`-free conclusions, so the statements need no
          `Decidable` hypotheses (a combined `… = if hj : j ∈ vbl e.1 then ⟨…⟩ else c j`
          form is optional and needs `open scoped Classical`).
        - `step_fst_eq_of_none (h : (step vbl A pick hpick ω c).2 = none) :
          (step vbl A pick hpick ω c).1 = c` — the freeze branch (20.2's run does not
          step once `none` appears).
        **Keep the certificate in the run state — never project it away before 20.4**
        (survey B risk 6: forgetting the certificate when threading `run` would silently
        weaken `log`).
    - proof: |
        Definitional glue; the only proof content is the `Fin` successor term (from the
        certificate) and `hpick` totality. The spec lemmas by `unfold step` +
        `split_ifs at h ⊢ with hAv`: the `none` branch contradicts `some e = none`
        (`simp at h` / `Option.noConfusion` closes); in the `some` branch `simp at h`
        gives `⟨pick ⟨Avail vbl A ω c, hAv⟩, hpick ⟨Avail vbl A ω c, hAv⟩⟩ = e`, `subst e`
        makes the dite condition match `hj`, and `simp [hj]` closes (the `Fin.val`
        projection of the `⟨(c j : ℕ) + 1, …⟩` term is `rfl`).
- **prep**
    - `Nat.succ_lt_succ` — core `Init/Data/Nat/Basic.lean:262` (v4.32.0): `n < m →
      succ n < succ m` — the `Fin` proof term of `step`:
      `⟨(c j : ℕ) + 1, Nat.succ_lt_succ (cert j hj)⟩ : Fin (N + 1)`; the
      `(c j : ℕ) + 1 = Nat.succ (c j : ℕ)` and `N + 1 = Nat.succ N` conversions are
      definitional (`Nat.add` computation rules) — prototype-compiled verbatim.
    - `Fin.coeToNat` — core `Init/Data/Fin/Basic.lean:21`:
      `instance coeToNat : CoeOut (Fin n) Nat := ⟨fun v => v.val⟩` — makes the
      `(c j : ℕ)` coercion elaborate. **mathlib v4.32.0 has NO heterogeneous
      `LT (Fin n) ℕ` instance** (Survey grep of `Mathlib/Data/Fin/` — none;
      `NatCast (Fin n)` exists only as a bare `def instNatCast` with `[NeZero n]`, core
      `Init/Data/Fin/Lemmas.lean:127`), so the guard MUST be `(c j : ℕ) < N`, not
      `(c j) < N` as the original informal statement wrote.
    - `Set.Nonempty` — `Mathlib/Data/Set/Defs.lean:275` — the `step` branch condition.
    - `Classical.propDecidable` — core `Init/Classical.lean:81` — `noncomputable scoped
      instance (priority := low) propDecidable (a : Prop) : Decidable a`, opened by the
      `classical` tactic — supplies `Decidable ((Avail …).Nonempty)` and
      `Decidable (j ∈ vbl e.1)` with NO `[DecidableEq ι]`/`[DecidableEq κ]` hypotheses
      (prototype-proven minimal-assumption route; `noncomputable def step … := by
      classical exact if h : …`). Computable alternative if Proof prefers:
      `Finset.decidableMem` — `Mathlib/Data/Finset/Defs.lean:117`
      (`[DecidableEq α]` instance).
    - `Fin.succ` / `Fin.castSucc` — core `Init/Data/Fin/Basic.lean:43/:326` — NOT used by
      20.1 (`Fin n → Fin (n+1)`; `step` instead holds `c j : Fin (N+1)` plus a
      certificate `(c j : ℕ) < N`, so the inline `⟨…⟩` term is the pinned construction);
      listed because 20.2's `run` recursion (`castSucc i`, `i.succ`) must stay
      definitionally compatible with `step`'s output.
    - `Fin.induction` — core `Init/Data/Fin/Lemmas.lean:909` (verified v4.32.0 signature
      `{motive : Fin (n + 1) → Sort _} (zero : motive 0) (succ : ∀ i : Fin n,
      motive (castSucc i) → motive i.succ) : ∀ i, motive i`; `Fin.induction_zero` @[simp]
      at :918; the prototype compiled both the term form `Fin.induction ⟨…⟩
      (fun _ rec => …)` and `induction t using Fin.induction with | zero => … |
      succ i ih => …`) — context for 20.2, which consumes `step`.
    - `Option` / `Option.some.injEq` / `Option.noConfusion` — core — the certificate-
      carrying `Option (Payload …)` pattern and the spec lemmas' case analysis.
    - `Function.update` — NOT needed: the prototype's pointwise
      `fun j => if hj : j ∈ vbl e.1 then ⟨(c j : ℕ) + 1, Nat.succ_lt_succ (e.2.2 j hj)⟩
      else c j` dite is the pinned advance (an `update` would need a default row value;
      the dite is what 20.2 unfolds).
    - Adaptations from the compiled prototype `/tmp/mt_proto_run.lean`: (i) the
      prototype's `Table`/`State` take `κ` explicitly and `assign` reads the curried
      table `ω j (c j)` — the integrated defs take `κ` from the file's brace
      `variable {κ : Type u}` block (10.3 API decision) and `assign` reads the
      Sigma-indexed `ΩN`: `fun j => ω ⟨j, c j⟩` (10.3 meta note; `⟨j, c j⟩.1 = j`
      definitionally); (ii) `State` as the blueprint's `def` (the prototype's `abbrev`
      also works); (iii) the prototype's `e : {e : ι // e ∈ Avail vbl ω c}` is defeq to
      `Payload` (the `Avail` membership predicate IS the `Payload` predicate) — write
      `let e : Payload vbl A ω c := ⟨pick ⟨Avail vbl A ω c, h⟩,
      hpick ⟨Avail vbl A ω c, h⟩⟩` directly; no `Classical.choose` needed anywhere; (iv)
      explicit argument order `(vbl) (A) (pick) (hpick) (ω) (c)` — `A` explicit to match
      60.2's pinned use sites (`log vbl A pick hpick ω`); the prototype had `{A}`
      implicit — deliberate deviation.
    - Internal deps (corrected): only item 10.3 (`ΩN` — the type of `ω`). `vbl`/`A`/
      `pick`/`hpick` are free parameters of the defs; `DeterminedBy` (10.2) is first
      consumed by the coupling (40.x) and Γ⁺ (10.1) by the tree items (30.x/50.x) —
      survey B's A1–A3 entry for B4 is file-order, not direct reference.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `State`/`assign`/`Avail`/`Payload`/`step` in `tmp_step.lean` (prototype-adapted: Sigma-indexed `assign … j := ω ⟨j, c j⟩`, guard `(c j : ℕ) < N` — mathlib has no heterogeneous `LT (Fin n) ℕ` — noncomputable `classical` step, no DecidableEq hypotheses); prove the step-advance spec `step_fst_val_eq_of_mem` (`.2 = some e` + `j ∈ vbl e.1` ⟹ `((step …).1 j : ℕ) = (c j : ℕ) + 1`), `step_fst_eq_of_not_mem` (unchanged outside `vbl e`), `step_fst_eq_of_none` (`.2 = none` freezes the state) | All 5 defs + 3 spec lemmas proved; defs are pure glue (the only proof content is the `Fin` successor term from the certificate and `hpick` totality). Spec lemmas by `unfold step` + `split_ifs at h ⊢ with hAv` in single-bullet form: `split_ifs` auto-closes the contradictory branch (`some e = none` in `step_fst_val_eq_of_mem`/`step_fst_eq_of_not_mem`, and in `step_fst_eq_of_none` the `none` case is `rfl`); in the `some` branch `simp at h` + `subst e` + `simp [hj]` closes, the `Fin.val` projection being `rfl` | Verified independently: LSP 0 diagnostics + `lake build StatsMLlib.Probability.MoserTardos.Algorithm` success (1858/1858); no sorry/axiom/admit, all lines ≤ 100 chars (one 105-char line rewrapped at integration). Integrated into `Algorithm.lean` (new module: copyright header + `/-!` docstring with Main definitions/results/References, imports `VariableModel`); tmp file deleted. For 20.2: `State`'s `κ` is an implicit auto-bound section variable — use-site headers write `State (κ := κ) N` (Setup deviation 1), and the section `omit`s `[Fintype κ]`/`[∀ j, MeasurableSpace (Ω j)]` (Setup deviation 3) | `tmp_step.lean` |

### 20.2. run, count, run_count_le

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Algorithm.lean`
- **informal**
    - statement: |
        The truncated run and its rows-never-run-out invariant (survey B B5, notes §4;
        difficulty Medium, est. ~80 lines; critical path ★):
        - `run (ω : ΩN N Ω) :
          Fin (N + 1) → Σ c : State (κ := κ) N, Option (Payload vbl A ω c)` —
          `Fin.induction` over `Fin (N+1)`: entry `t` = (counts *before* step `t`, event of
          step `t` as the certificate-carrying `Option`). Once the option is `none` the
          recursion freezes (the match keeps the same `c`) — exactly "the algorithm stops".
          The codomain is the **dependent Sigma** `Σ c, Option (Payload vbl A ω c)`, not
          `State N × Option Payload`: `Payload` is indexed by the state `c`, so the plain
          product does not typecheck, and the certificate is KEPT (20.1 review note — never
          project it away before 20.4). `noncomputable`, `classical` in the body (the
          `if hj : j ∈ vbl e.1` dite needs `Decidable (j ∈ vbl e.1)` and the section carries
          no `[DecidableEq κ]` — the prototype instead relied on its own `[DecidableEq κ]`).
        - `count (ω : ΩN N Ω) (t : Fin (N + 1)) : State (κ := κ) N` — first component of
          `run ω t`. **Fin-indexed** (`t : Fin (N+1)`), per the prototype — not ℕ-indexed.
        - `run_count_le (ω : ΩN N Ω) (t : Fin (N + 1)) (j : κ) :
          ((count vbl A pick hpick ω t) j : ℕ) ≤ t.val` — hence at any time `t < N` *every*
          violated event is available (its variables have `c j ≤ t < N`), so **the
          availability guard never bites before `N` steps** and the guarded `step` is
          definitionally the honest algorithm on the relevant prefix. The log (20.4) is
          therefore well-defined for all `t < R` (since `t < R ≤ N` gives `t < N`).
    - proof: |
        `Fin.induction`; the zero case is `simp [count, run]`. The invariant is preserved
        by the step logic (only resampled variables advance, each by exactly 1, and at most
        `t.val` steps have happened). The inductive step unfolds `run`'s `Fin.induction`
        term with two Survey-verified refinements over the prototype skeleton:
        (1) the rcases MUST be the `h :` form —
        `rcases h : (run vbl A pick hpick ω i.castSucc).2 with _ | ⟨e, he⟩` — the bare
        prototype form discards the equality and the `match` inside `run`'s successor stays
        irreducible;
        (2) `simp [count, run, h]` alone does NOT reduce that match (simp will not rewrite
        the match discriminant with `h` — the arg is reported unused) — the working
        sequence is `simp [count, run] at h ⊢` (unfold `run` in hypothesis and goal in one
        call) + `rw [h]` (rewrite the scrutinee) + `simp` / `simp [hj]`; then
        `simp [count] at ih` turns `ih` into `((run … i.castSucc).fst j : ℕ) ≤ ↑i`. The
        `none` case closes with `Nat.le_trans ih (by simp)` (the `by simp` is
        `Nat.le_add_right`), the `j ∈ vbl e` case collapses to exactly `ih` (simp cancels
        the `+ 1 ≤ + 1`), and the `j ∉ vbl e` case closes like the `none` case. Full
        skeleton Survey-compiled in the integrated section context (scratch file, 0 errors
        on the skeleton).
- **prep**
    - `Fin.induction` — the `Fin (N+1)` recursion principle — core
      `Init/Data/Fin/Lemmas.lean:909` (Survey-verified v4.32.0 signature:
      `@[elab_as_elim] def induction {motive : Fin (n + 1) → Sort _} (zero : motive 0)
      (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) :
      ∀ i : Fin (n + 1), motive i` — motive first (implicit, inferred from the result
      type), then `zero`, then `succ`; the term form
      `Fin.induction ⟨zero-term⟩ (fun _ rec => …)` needs no `(motive := …)` named arg).
    - `Fin.induction_zero` / `Fin.induction_succ` — `@[simp, grind =]`, core
      `Init/Data/Fin/Lemmas.lean:919/:923` (line numbers corrected from the 20.1 prep's
      :918/:922): `(induction zero hs) 0 = zero` and
      `induction zero succ i.succ = succ i (induction zero succ (castSucc i))` — both
      `rfl`.
    - `Fin.succ` — core `Init/Data/Fin/Basic.lean:43` — `Fin n → Fin (n + 1)`.
    - `Fin.castSucc` — core `Init/Data/Fin/Basic.lean:326` — `castAdd 1` (the induction's
      `castSucc i` target; `Fin.last` (Basic.lean:279) is NOT used).
    - `Fin.val_succ` — `@[simp]`, core `Init/Data/Fin/Lemmas.lean:403` —
      `(j.succ : Nat) = j + 1 := rfl` (reduces the goal RHS `↑i.succ` to `↑i + 1`).
    - `Fin.val_castSucc` — `@[simp, grind =]`, core `Init/Data/Fin/Lemmas.lean:572` —
      `(i.castSucc : Nat) = i := rfl` (reduces `ih`'s RHS `↑i.castSucc` to `↑i`).
    - `Fin.coeToNat` — core `Init/Data/Fin/Basic.lean:21` — the `(x : ℕ)` coercion in the
      statement (20.1 prep).
    - `Nat.le_trans` — core — chains `ih` with the `≤ ↑i + 1` pad in the none/neg cases.
    - `Nat.le_add_right` — `@[simp]`, core `Init/Data/Nat/Basic.lean:374` — `n ≤ n + k`
      (closes the `↑i ≤ ↑i + 1` pad via `by simp`).
    - `Nat.succ_lt_succ` — core `Init/Data/Nat/Basic.lean:262` — already used by 20.1's
      `step`; reappears in `run`'s advance term.
    - `Nat.succ_le_succ` / `omega` — fallbacks for the arithmetic tails if the
      simp-collapse route is not taken (the `j ∈ vbl e` case's `+ 1 ≤ + 1` cancellation
      seen in the scratch is done by simp's add-monotonicity lemmas — no explicit cite
      needed).
    - **Header caveat (20.1 Review note, Setup deviation 1):** `State`'s `κ` is an implicit
      auto-bound section variable — write `State (κ := κ) N` in 20.2's def headers (run's
      Sigma, count's return type), matching `assign`/`Avail`/`step` in the integrated file.
      Survey scratch: the plain `State N` form ALSO elaborated in the Sigma binder position
      (the only errors were the expected noncomputable flags on the scratch test defs) —
      the named-arg form is the pinned house style.
    - **Adaptations from the prototype `/tmp/mt_proto_run.lean`:** (i) the prototype's
      `Table κ N Ω`/`State κ N` become the integrated `ΩN N Ω`/`State N` (section
      variables); (ii) the prototype compiles the dites via its own `[DecidableEq κ]` — the
      integrated section has none, so `run` wraps the `Fin.induction` term in `by
      classical` (same pattern as `step`); (iii) `A` is now an explicit section variable,
      so the prototype's `Payload (A := A)` named arg disappears; (iv) the
      `run_count_le` proof needs the `h :` rcases + `rw [h]` refinements (see
      informal.proof) — Survey-compiled in the integrated section context.
    - Placement: same `section Step` in `Algorithm.lean`, after `step_fst_eq_of_none`
      (line 140) and before `end Step` (line 142); the section's existing `omit`s cover the
      new decls (run/count/run_count_le need no `[Fintype κ]` / `[∀ j, MeasurableSpace
      (Ω j)]`).
    - Internal deps (survey B §5): item 20.1 (`State`/`assign`/`Avail`/`Payload`/`step`).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `run`/`count` via `Fin.induction` (prototype-adapted to the integrated `section Step`: Sigma codomain `Σ c : State (κ := κ) N, Option (Payload vbl A ω c)`, `by classical` body — no `[DecidableEq κ]` in the section) and prove `run_count_le : ((count vbl A pick hpick ω t) j : ℕ) ≤ t.val` — Survey-verified skeleton: zero case `simp [count, run]`; succ case `rcases h : (run … i.castSucc).2 with _ | ⟨e, he⟩` (the bare prototype rcases drops the equality and the match stays irreducible — refinement 1), then `simp [count, run] at h ⊢` + `rw [h]` + `simp`/`simp [hj]` (refinement 2) and close with `Nat.le_trans ih (by simp)` / `exact ih` | Proved `run`/`count` (pinned bodies: `Fin.induction` term form, dependent Sigma codomain, `by classical`) and `run_count_le` by `induction t using Fin.induction`; both Survey refinements applied (the `h :` rcases form; `simp [count, run] at h ⊢` + `rw [h]` + `simp`/`simp [hj]`); one minor deviation: the by_cases splits on `j ∈ vbl e` directly — the `h :` rcases destructures `e : ι` so no `.1` needed. tmp compiled 0 errors/warnings | Independently verified: tmp (84 lines) 0 LSP diagnostics + `lake env lean` exit 0; no sorry/axiom/admit; all lines ≤ 100. Integrated into `Algorithm.lean` as a **new `section Run` after `section Step`** (kept the tmp's layout incl. its `omit`s — the blueprint prep's "inside `section Step`" placement would also work since the variable blocks match; new section is cleaner and review-preferred). Module docstring updated (`run`/`count` in "Main definitions", `run_count_le` in "Main results"). tmp deleted. Integrated file: 0 LSP diagnostics; `lake build StatsMLlib.Probability.MoserTardos.Algorithm` OK (1858 jobs) | `tmp_run.lean` |

### 20.3. Violated, NoViolation, R, R_le

- **meta**
    - kind: def
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Algorithm.lean`
- **informal**
    - statement: |
        The stopping time (survey B B6, notes §4; difficulty Easy–Med, est. ~60 lines).
        Pinned signatures (Survey-compiled 0 errors/0 warnings in the integrated section
        context — a new `section Stopping` with the `section Run` variable block + omits):
        - `Violated (ω : ΩN N Ω) (c : State (κ := κ) N) : Prop := ∃ i, assign ω c ∈ A i`
          — state-indexed "some event is violated at `c`". **Form decision (orchestrator
          pin, deviating from both earlier drafts):** NOT the `Set ι := {i | …}` form of
          the earlier informal and NOT the prototype's time-indexed per-event
          `Violated ω t i` Prop. The per-event predicate `assign ω c ∈ A i` stays the
          workhorse used directly everywhere (Avail, step, 20.4's proof, 20.5's sets);
          `Violated` is the compressed concept, consumed by 20.5's prose and by
          `¬ Violated … ↔ ∀ i, …` (`simpa`/`push_neg` via `not_exists` — Survey-verified
          classical-free).
        - `NoViolation (ω : ΩN N Ω) (t : ℕ) : Prop :=
          ∃ ht : t < N + 1, ∀ i, assign ω (count vbl A pick hpick ω ⟨t, ht⟩) ∉ A i`
          — ℕ-typed ∃-ht form, prototype-exact. **Form decision:** kept over the
          `(t : Fin (N+1))`-typed `∀ i` form because (i) `R`'s `Nat.find` predicate must
          be a ℕ-predicate and this form IS that predicate — the `ht` witness carries
          `t ≤ N`, so `∃ t, NoViolation ω t` is exactly "some `t ≤ N` has no violated
          event"; (ii) 20.4's `log`/`run_step_of_lt_R` are ℕ-typed (`t < R ω`, with
          `ht : t < N + 1` from `t < R ≤ N` via `R_le`); (iii) 20.5's finitary needs are
          served by the glue lemmas below, whose RHS is the Fin-indexed finite boolean
          combination — no pollution of the definition.
        - `noncomputable def R (ω : ΩN N Ω) : ℕ :=
          if h : ∃ t : ℕ, NoViolation vbl A pick hpick ω t then Nat.find h else N`
          — `by classical` body (prototype-exact). The predicate is `NoViolation ω t`
          itself, not literally `t ≤ N ∧ …`: the `t ≤ N` is the `ht` witness inside
          `NoViolation` (equivalent formulations; the ∃-ht predicate makes
          `Nat.find_spec h` unpack to exactly `⟨hlt, hv⟩`). The fallback `N` covers both
          "still violated at N" and the row-exhausted-at-N state (an always-violated
          single-variable event exhausts its rows exactly at time N).
        - `theorem R_le (ω : ΩN N Ω) : R vbl A pick hpick ω ≤ N` (prototype-compiled).
        - Glue for 20.5 (finitary characterizations, RHS free of `Nat.find`/classical):
          `lemma NoViolation_fin_iff {t : Fin (N + 1)} :
          NoViolation vbl A pick hpick ω t.val ↔
          ∀ i, assign ω (count vbl A pick hpick ω t) ∉ A i`;
          `lemma R_lt_N_iff (ω : ΩN N Ω) :
          R vbl A pick hpick ω < N ↔ ∃ t : Fin N, NoViolation vbl A pick hpick ω t.val`
          — the finite boolean combination 20.5 makes measurable (`{R = N} = {R < N}ᶜ`
          via `R_le`).
    - proof: |
        `R_le`: `by_cases h : ∃ t : ℕ, NoViolation vbl A pick hpick ω t` —
        - find branch: `simp [R, h]` unfolds `R` (if_pos) and the `@[simp]`
          `Nat.find_le_iff` fires, rewriting the goal `Nat.find h ≤ N` to
          `∃ m ≤ N, NoViolation … m`; `rcases Nat.find_spec h with ⟨hlt, hv⟩`;
          `exact ⟨Nat.find h, Nat.le_of_lt_succ hlt, ⟨hlt, hv⟩⟩` — the 3-tuple is the
          flattened `⟨m, ⟨m ≤ N, ⟨ht, ∀-witness⟩⟩⟩` witness (this is why the prototype's
          odd-looking exact line typechecks: it closes `∃ m ≤ N, …`, not
          `Nat.find h ≤ N` directly — Survey-traced via `trace_state`).
        - else branch: `simp [R, h]` (if_neg; goal `N ≤ N`).
        Glue: `NoViolation_fin_iff` by `constructor` — forward
        `rintro ⟨ht, hnv⟩; simpa using hnv` (`count ω ⟨t.val, ht⟩` and `count ω t` are
        defeq: the `Fin.isLt` proofs are proof-irrelevant), backward
        `exact ⟨t.isLt, by simpa using hnv⟩`. `R_lt_N_iff` by `constructor` — forward
        `unfold R at hR; split_ifs at hR with h` (positive branch
        `exact ⟨⟨Nat.find h, hR⟩, Nat.find_spec h⟩`; negative branch `simp at hR` closes
        the `N < N` contradiction); backward `unfold R; split_ifs with h` (positive
        branch `exact Nat.lt_of_le_of_lt (Nat.find_min' h hnv) t.isLt`; negative branch
        `exfalso; exact h ⟨t.val, hnv⟩`).
- **prep**
    - `Nat.find` — `Mathlib/Data/Nat/Find.lean:72` — `{p : ℕ → Prop} [DecidablePred p]
      (H : ∃ n, p n) : ℕ`; `[DecidablePred p]` supplied by `classical`. **No new
      imports** (Survey-verified: the full pinned block compiles against
      `import StatsMLlib.Probability.MoserTardos.Algorithm` alone — `Mathlib.Data.Nat.Find`
      is already transitive through `VariableModel`).
    - `Nat.find_spec` — Find.lean:75 — `p (Nat.find H)`.
    - `Nat.find_min'` — Find.lean:83 — `{m : ℕ} (h : p m) : Nat.find H ≤ m`
      (used in `R_lt_N_iff` backward).
    - `Nat.find_min` — Find.lean:80 — `m < Nat.find H → ¬ p m` (backup for 20.4's
      minimality step in `run_step_of_lt_R`).
    - `Nat.find_le_iff` — Find.lean:97, `@[simp]` — `Nat.find h ≤ n ↔ ∃ m ≤ n, p m` —
      **load-bearing**: fires inside `simp [R, h]` and turns `R_le`'s positive branch
      into the ∃-witness goal.
    - `Nat.find_lt_iff` — Find.lean:93, `@[simp]` — `Nat.find h < n ↔ ∃ m < n, p m`
      (alternative route for the `R < N` glue).
    - `Nat.find_eq_iff` — Find.lean:86 — `Nat.find h = m ↔ p m ∧ ∀ n < m, ¬ p n`
      (20.5's `{R = N}` route option; 20.5 also has the `{R < N}ᶜ` route via `R_le`).
    - `Nat.le_of_lt_succ` — core `Init/Prelude.lean:1971` — `m < n.succ → m ≤ n`.
    - `Nat.lt_of_le_of_lt` — core `Init/Data/Nat/Basic.lean` (the `Trans (≤) (<) (<)`
      instance, :311) — transitivity, `R_lt_N_iff` backward.
    - `split_ifs at … with h` — `Mathlib.Tactic.SplitIfs` — `R_lt_N_iff` both directions.
    - `dite`/`ite` + `by classical` — core.
    - **Placement:** new `section Stopping` in `Algorithm.lean` after `end Run`
      (line 214), same variable block + both `omit`s as `section Run` (review-preferred
      over extending `section Run` — matches the 20.2 review's section preference).
      Module docstring additions at integration (Review).
    - Internal deps (survey B §5): item 20.2 (`run`/`count`/`run_count_le`) — the defs
      reference only `count`; `run_count_le` first bites in 20.4.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `Violated` (state-indexed Prop-∃: `∃ i, assign ω c ∈ A i` — orchestrator pin, replaces the earlier `Set ι` draft and the prototype's time-indexed per-event Prop), `NoViolation` (ℕ-typed ∃-ht form, prototype-exact — chosen over the `Fin (N+1)` form since `R`'s `Nat.find` predicate must be ℕ-typed and 20.4's `log` is ℕ-typed; 20.5 gets its finitary form from the glue), `R` (prototype-exact: `if h : ∃ t : ℕ, NoViolation … then Nat.find h else N`, `by classical`), prove `R_le` (prototype-exact skeleton: `by_cases h` + `simp [R, h]` — `Nat.find_le_iff` [simp] rewrites `Nat.find h ≤ N` to `∃ m ≤ N, NoViolation … m` — + `rcases Nat.find_spec h` + the `⟨Nat.find h, Nat.le_of_lt_succ hlt, ⟨hlt, hv⟩⟩` witness tuple), plus the 20.5-serving glue `NoViolation_fin_iff` and `R_lt_N_iff` (whole block Survey-compiled in the integrated section context, 0 errors/warnings) | Pinned defs `Violated`/`NoViolation`/`R` written with the Survey bodies verbatim; `R_le`, `NoViolation_fin_iff`, `R_lt_N_iff` proved following the Survey proof sequences verbatim, with one adaptation: `classical` added to the two `Nat.find`-using proofs (`R_le`, `R_lt_N_iff`) to supply the `[DecidablePred]` instance (`NoViolation_fin_iff` stayed classical-free). tmp compiled 0 errors/0 warnings | Independently verified: tmp (97 lines) 0 LSP diagnostics + `lake env lean` exit 0; no sorry/axiom/admit; all lines ≤ 100; `#print axioms` shows only propext/Classical.choice/Quot.sound. Integrated into `Algorithm.lean` as a new `section Stopping` after `end Run` (tmp layout kept: variable block, both `omit`s, docstrings). Module docstring updated: `Violated`/`NoViolation`/`R` in "Main definitions"; `R_le`/`NoViolation_fin_iff`/`R_lt_N_iff` in "Main results"; intro sentence extended. tmp deleted. Integrated file: 0 LSP diagnostics; `lake build StatsMLlib.Probability.MoserTardos.Algorithm` OK (1858 jobs) | `tmp_stopping.lean` |

### 20.4. log, countLog, run_step_of_lt_R, log_eq_none_of_R_le

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Algorithm.lean`
- **informal**
    - statement: |
        The padded execution log and the count (survey B B7, notes §6; difficulty Medium,
        est. ~80 lines; critical path ★). Pinned signatures — the whole block is
        Survey-compiled (scratch, 0 errors/0 warnings) in a `section Log` mirroring the
        integrated file's sections (same variable block + both `omit`s):
        - `run_snd_eq_step (ω : ΩN N Ω) (t : Fin (N + 1)) :
          (run vbl A pick hpick ω t).2 =
          (step vbl A pick hpick ω (count vbl A pick hpick ω t)).2` — the defeq glue: the
          run's option at `t` is the step at the run's state before `t`. NOT `rfl` for a
          variable `t` (the `Fin.induction` match is stuck — Survey-traced: `change`
          fails), but each case is `rfl` after unfolding, so `induction t using
          Fin.induction` + `simp [count, run]` closes both. Keep it a lemma, NOT `@[simp]`
          (do not unfold run/step in the default simplifier).
        - `run_snd_eq_some_of_Avail_ne (ω : ΩN N Ω) {t : Fin (N + 1)} {i : ι}
          (hi : i ∈ Avail vbl A ω (count vbl A pick hpick ω t)) :
          ∃ e, (run vbl A pick hpick ω t).2 = some e` — an available event makes the
          option `some`. Proof: `hne := ⟨i, hi⟩`; witness
          `⟨pick ⟨Avail vbl A ω (count vbl A pick hpick ω t), hne⟩, hpick ⟨…, hne⟩⟩`
          (typechecks because `count ω t` is definitionally `(run ω t).1`); then
          `rw [run_snd_eq_step vbl A pick hpick]` (the rw motive lines up since the
          witness's Payload is `count`-indexed — Survey-compiled), `unfold step`,
          `rw [dif_pos hne]`, `rfl` (the payloads differ only in the `Nonempty` proof —
          proof irrelevance).
        - `run_step_of_lt_R (ω : ΩN N Ω) {t : ℕ} (ht : t < R vbl A pick hpick ω) :
          ∃ e, (run vbl A pick hpick ω ⟨t, Nat.lt_of_lt_of_le ht
          (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))⟩).2 = some e` — the
          genuine-step lemma (prototype-exact statement; the inline `Fin` proof term is
          the derived `t < N + 1`).
        - `noncomputable def log (ω : ΩN N Ω) (t : ℕ) : Option ι := by classical; exact
          if h : t < R vbl A pick hpick ω then
          some ((Classical.choose (run_step_of_lt_R vbl A pick hpick ω h)).1) else none`
          — the padded log. **Form decision (load-bearing): the `if t < R` form, NOT the
          "read the run's option" form.** Survey B §3.1's equivalence claim ("the run's
          option is itself none exactly at/after the first violated-free time") is FALSE
          at `t = R = N` in the fallback branch: when `¬ ∃ t, NoViolation ω t`, the state
          at time `N` can still have a violated event with all rows available (the
          availability guard only bites when a variable reaches `N` rows), so
          `(run ω ⟨N, hN⟩).2 = some e` while `R = N`. Survey-compiled counterexample
          (scratch, 0 errors): `κ = ι = Fin 2`, `vbl i = {i}`, `A i = {σ | σ i = 1}`, all
          table entries 1, `N = 1`, `pick` preferring 0 — Lean proves
          `(∃ e, (run … ⟨1, by decide⟩).2 = some e) ∧ R … = 1`. With the option-reading
          log, `log_eq_none_of_R_le` would be unprovable (`log ω N = some e` with
          `R = N ≤ N`); with the `if`-log it is the trivial `dif_neg` branch, and
          `log ω t ≠ none ↔ t < R ω` holds for ALL `t` (60.1's counting identity needs
          exactly this). Side note (settles survey B open question 6): with the if-log,
          `{ω | log ω N = none}` is the WHOLE space (always `R ≤ N`), so 60.4's
          `{R = N}` form is the only honest "did not finish" event. The
          `Classical.choose` makes the `t < R` branch syntactically `some _`, so the pad
          lemmas are one `rw` each (the `.map`-form alternative
          `(run ω ⟨t, ht'⟩).2.map (fun e => e.1)` in the then-branch avoids the choose
          but makes `log_ne_none_iff_lt_R`'s backward direction need `run_step_of_lt_R` +
          `Option.map_some` — the choose form is pinned).
        - `log_eq_none_of_R_le (ω : ΩN N Ω) {t : ℕ} (ht : R vbl A pick hpick ω ≤ t) :
          log vbl A pick hpick ω t = none` — `unfold log;
          rw [dif_neg (Nat.not_lt_of_le ht)]` (rw auto-closes the `none = none` goal).
        - `log_ne_none_iff_lt_R (ω : ΩN N Ω) {t : ℕ} :
          log vbl A pick hpick ω t ≠ none ↔ t < R vbl A pick hpick ω` — the counting glue
          for 60.1/60.3 (forward: `by_contra` + `log_eq_none_of_R_le` +
          `Nat.le_of_not_gt`; backward: `unfold log; rw [dif_pos ht];
          exact Option.some_ne_none _`). NOT marked `@[simp]` (deliberate — keep the
          classical `R` out of the default simplifier; 60.1 rewrites explicitly).
        - `def countLog [DecidableEq ι] (Λ : ΩN N Ω → ℕ → Option ι) (ω : ΩN N Ω)
          (i : ι) : ℕ := ((Finset.range N).filter fun t => Λ ω t = some i).card` — survey
          B §1.1-exact. The `[DecidableEq ι]` is an explicit binder (Algorithm.lean's
          sections carry none; survey B §1.1's Basic.lean context has it as a namespace
          variable, so `countLog (log vbl A pick hpick) ω i` elaborates in 60.2).
          Judgment call (Planner): `countLog` lives here with the log API rather than in
          `Basic.lean` — it is a pure function of the log.
        **No freezing lemma needed** (`(run ω t).2 = none → (run ω t.succ).2 = none`): the
        `if`-log makes the pad trivial, and no downstream item (30.x/40.x/60.x) consumes
        such a lemma — do not add it (if 20.5's measurability later needs it, it goes in
        20.5). For `R < N` the run's option IS none at/after `R` (freezing holds), but the
        fallback boundary `t = R = N` breaks the equivalence — hence the `if`-log.
        **PITFALL (survey B finding 2, load-bearing): the log is `Option`-valued** — no
        `[Nonempty ι]` padding dummy; padded entries are structurally excluded from witness
        trees (a `none` never creates a vertex), so Prop 12.1 (30.6) is stated for `t < R`
        only, and the count `#{t < N : Λ t = some i}` automatically equals
        `#{t < R ω : Λ t = some i}`.
    - proof: |
        `run_snd_eq_step` by `induction t using Fin.induction`: both cases
        `simp [count, run]` (in the succ case both sides reduce to the same stuck match
        term). `run_snd_eq_some_of_Avail_ne` as above. `run_step_of_lt_R`:
        (1) `¬ NoViolation ω t` from `unfold R at ht; split_ifs at ht with h` — find
        branch `Nat.find_min h ht`, fallback branch `intro hn; exact h ⟨t, hn⟩`;
        (2) `unfold NoViolation at hnv; push Not at hnv; exact hnv ht'` gives
        `∃ i, assign ω (count ω ⟨t, ht'⟩) ∈ A i` (`ht'` the inline `t < N + 1` term);
        (3) availability: `run_count_le` at `⟨t, ht'⟩` gives `(count … j : ℕ) ≤ t`, and
        `t < N` from `ht` + `R_le`, so `⟨hi, hAvail⟩ : i ∈ Avail …`;
        (4) `exact run_snd_eq_some_of_Avail_ne vbl A pick hpick ω ⟨hi, hAvail⟩`.
        `log_eq_none_of_R_le`/`log_ne_none_iff_lt_R` by `dif_neg`/`dif_pos` (one rw each —
        no `split_ifs`, no branch-name linter warnings). All Survey-compiled (scratch, 0
        errors/0 warnings).
- **prep**
    - `Fin.induction` — core `Init/Data/Fin/Lemmas.lean:909` — `run_snd_eq_step`'s
      induction.
    - `Fin.induction_zero` / `Fin.induction_succ` — `@[simp, grind =]`, core
      `Init/Data/Fin/Lemmas.lean:919/:923` — reduce `run` at concrete `Fin` indices.
      **Caveat (Survey-verified):** the DEFAULT simp set rewrites `(0 : Fin n).succ` to
      `1`, which then blocks `Fin.induction_succ` on concrete indices — in computations
      rw `Fin.induction_succ` BEFORE simp (matters for the counterexample-style
      reductions only, not the item's statements).
    - `run_count_le` — 20.2, `Algorithm.lean:205` — the availability step of
      `run_step_of_lt_R`.
    - `R_le` — 20.3, `Algorithm.lean:265` — the `t < R ≤ N` chains (`t < N`, `t < N + 1`).
    - `Nat.find_min` — `Mathlib/Data/Nat/Find.lean:80` — `m < Nat.find H → ¬ p m` —
      `run_step_of_lt_R` step (1) (the 20.3-prep backup, now consumed).
    - `Nat.find_spec` — Find.lean:75 — only the counterexample's `R = 1` proof.
    - `Nat.lt_of_lt_of_le` — core `Init/Data/Nat/Basic.lean:311` — the `t < N + 1`/`t < N`
      derivations.
    - `Nat.le_trans` / `Nat.le_succ` — core — the inline `Fin` proof term.
    - `Nat.not_lt_of_le` — core `Init/Data/Nat/Basic.lean` — `log_eq_none_of_R_le` via
      `dif_neg`.
    - `Nat.le_of_not_gt` — core `Init/Data/Nat/Basic.lean` — `log_ne_none_iff_lt_R`
      forward.
    - `dif_pos` / `dif_neg` — core `Init/Core.lean` (`dite` elimination) — the pad lemmas
      (one rw each; avoids `split_ifs` branch-name linter warnings and the auto-closed
      `rfl` branches).
    - `Classical.choose` — core — `log`'s `t < R` branch (`Classical.choose_spec` ties
      `log ω t` to `(run …).2` — the hook 40.3's coupling reads the log through).
    - `Option.some_ne_none` — core — `log_ne_none_iff_lt_R` backward.
    - `Option.some.inj` — core — uniqueness of the genuine-step event (60.3's "exactly
      one `e`").
    - `push Not` — mathlib v4.32.0 tactic — **`push_neg` is DEPRECATED in v4.32.0**
      ("Prefer using `push Not`"); `push Not at hnv` is the working spelling for
      `¬ NoViolation …` → `∀ ht', ∃ i, assign … ∈ A i` (Survey-compiled; the deprecation
      message includes a macro shim if the old spelling is preferred).
    - `Finset.range` / `Finset.filter` / `Finset.card` — basic Finset API
      (`Mathlib/Data/Finset/…`) — `countLog` (filter decidability from the explicit
      `[DecidableEq ι]` binder).
    - `Option` — core.
    - Internal deps (survey B §5): items 20.2 (`run`/`count`/`run_count_le`), 20.3
      (`R`/`R_le`/`NoViolation`).
    - **Placement:** new `section Log` in `Algorithm.lean` after `end Stopping`
      (line 304), same variable block + both `omit`s (review-preferred per-item section
      style); `countLog` takes its own `[DecidableEq ι]`. Module docstring additions at
      integration (Review).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `log` (`if t < R` form — Survey-verified counterexample: the option-reading log fails `log_eq_none_of_R_le` at `t = R = N` fallback, where the run's option at time N can be `some`), `countLog` (survey B §1.1-exact, explicit `[DecidableEq ι]`), and prove `run_snd_eq_step` (Fin.induction + simp glue), `run_snd_eq_some_of_Avail_ne`, `run_step_of_lt_R` (R-unfolding + `Nat.find_min` + `push Not` + `run_count_le`), `log_eq_none_of_R_le` and `log_ne_none_iff_lt_R` (one rw each via `dif_neg`/`dif_pos`) — whole block Survey-compiled 0 errors/0 warnings in the integrated section context | All five lemmas proved Survey-exact in the tmp `section Log` (mirroring the integrated context): `run_snd_eq_step` (`induction t using Fin.induction <;> simp [count, run]`), `run_snd_eq_some_of_Avail_ne` (let-Nonempty witness + `rw [run_snd_eq_step]` + `unfold step` + `dif_pos`), `run_step_of_lt_R` (`unfold R`/`split_ifs` + `Nat.find_min` + `push Not` + `run_count_le` availability), `log_eq_none_of_R_le` (`dif_neg`), `log_ne_none_iff_lt_R` (`by_contra` + `log_eq_none_of_R_le` forward / `dif_pos` + `Option.some_ne_none` backward) — one adaptation: the explicit `vbl A pick hpick` arguments passed at the `log_eq_none_of_R_le` call in the forward direction. tmp compiled 0 errors/0 warnings | Independently verified: tmp (124 lines) 0 LSP diagnostics + `lake env lean` exit 0; no sorry/axiom/admit; all lines ≤ 100. Integrated into `Algorithm.lean` as a new `section Log` after `end Stopping` (tmp layout kept: variable block, both `omit`s, docstrings; no `@[simp]` as pinned). Module docstring updated: `log`/`countLog` in "Main definitions"; the five lemmas in "Main results"; intro sentence extended. tmp deleted. Integrated file: 0 LSP diagnostics; `lake build StatsMLlib.Probability.MoserTardos.Algorithm` OK (1858 jobs) | `tmp_log.lean` |

### 20.5. measurable_run, measurable_count, measurableSet_R_eq

- **meta**
    - kind: lemma
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Algorithm.lean`
- **informal**
    - statement: |
        Measurability of the algorithm (survey B B8; difficulty Medium, est. ~100 lines):
        - `measurable_run` / `measurable_count` — `run ω t` / `count ω t` as functions of
          `ω` are measurable: structural induction over the algorithm definition (each step
          is an `if` over a measurable condition — `assign ω c ∈ A i`, measurable from
          `hA` — composed with measurable maps).
        - `measurableSet_R_eq` — `{ω | R … ω = N}` (and the `R < N` variant) is measurable:
          `R = N ⟺ ¬ R < N` (via `R_le`, 20.3) and `R < N ⟺ ∃ t : Fin N,
          NoViolation … t.val` (20.3's `R_lt_N_iff`); each `{ω | NoViolation … t.val}`
          unfolds by 20.3's `NoViolation_fin_iff` to `∀ i, assign ω (count ω t) ∉ A i` —
          a finite boolean combination of `assign … ∈ A i` tests, measurable from `hA`
          (survey B §3.5). **Flag (20.3 survey):** the intersection over all `i : ι`
          needs a finiteness/countability hypothesis on 20.5's theorem headers — the
          `section Run` block carries no `[Fintype ι]` (survey B §1.1's context for 60.x
          does); verify against `Basic.lean`'s section variables when it exists.
        **Gap note (survey A §2.3):** mathlib has NO codomain-countable "fiber" lemma
        (`Measurable f ↔ ∀ i, MeasurableSet (f ⁻¹' {i})`); `measurable_of_countable` /
        `measurable_of_finite` (`MeasurableSpace/Basic.lean:287/:291`) cover only the
        domain-countable direction. Route: put the discrete `MeasurableSpace` on `ι` and
        prove measurability structurally, or state the needed facts directly about the sets
        `{ω | Λ t ω = i}`. **Scope (survey B open question 7): keep this item to exactly
        what 60.1–60.4 consume** — fallback is the set-monotonicity route (bound `∫⁻ N_i`
        by `Σ_τ μN{…}` through set monotonicity, needing only measurability of the sets
        `{∃t < R, T = τ}`, which uses the same ingredients).
    - proof: |
        Induction over the `Fin.induction` structure of `run`, using `MeasurableSet`
        closure under `∩`/`ᶜ`/finite intersections and the measurable-if/measurable-pair
        lemmas; the `R` characterization as a finite boolean combination from 20.3.
- **prep**
    - Section contexts (pinned 2026-08-17, both Survey-compiled as statement shapes via a
      `lake env lean` probe, 0 shape errors): **Block A** in `Algorithm.lean` — new
      `section Measurability` after `section Log`: `{ι} [Fintype ι]`, `{κ} [Fintype κ]`,
      `{Ω} [∀ j, MeasurableSpace (Ω j)]` (NOT omitted — the section's lemmas need it),
      `{N}`, `(vbl)`, `(A)`, `(hA : ∀ i, MeasurableSet (A i))`, `(pick)`, `(hpick)`;
      `[DecidableEq ι]` only as an explicit binder on the two countLog lemmas (matching
      `countLog`); `classical` in bodies. **Block B** in `Basic.lean` — new
      `section MeasurableOccurrence` after CountLogIdentity; Basic.lean gains
      `open scoped ENNReal` at the top (Coupling.lean:66 precedent): `{ι} [DecidableEq ι]
      [Inhabited ι] [Fintype ι]`, `{κ} [DecidableEq κ] [Fintype κ]`, `{Ω} [∀ j,
      MeasurableSpace (Ω j)]`, `{N}`, `(vbl)`, `(A)`, `(hA)`, `(pick)`, `(hpick)`. Import
      chain acyclic: Basic → WitnessTree → Algorithm → VariableModel, so Block B can call
      Block A.
    - NEW instance (probe-verified required): `State.instMeasurableSpace (N : ℕ) :
      MeasurableSpace (State (κ := κ) N)` — `dsimp [State]; infer_instance`, mirroring
      `ΩN.instMeasurableSpace` (VariableModel.lean:78); TC search does not unfold the
      semireducible `def State`, so `Measurable (fun ω => count … ω t)` does not elaborate
      without it.
    - `Measurable` / `MeasurableSet` / `MeasurableSet.compl` / `MeasurableSet.inter` /
      `MeasurableSet.preimage` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`
      (probe-verified).
    - `Finset.measurableSet_biUnion` / `Finset.measurableSet_biInter` — Defs.lean:149
      (probe-verified).
    - `Measurable.ite` (takes a `[DecidablePred p]` instance argument) /
      `Measurable.indicator` — `MeasurableSpace/Basic.lean` (probe-verified).
    - `measurable_pi_lambda` / `measurable_pi_apply` / `measurable_pi_iff` —
      `MeasurableSpace/Constructions.lean` (in-repo precedent: Coupling.lean's
      `measurableSet_witness`).
    - `Finset.measurable_sum` (needs `MeasurableAdd₂ M` — ℕ and ℝ≥0∞ both have it) and
      `Finset.card_filter` (`(s.filter p).card = ∑ a ∈ s, if p a then 1 else 0`) —
      probe-verified (`Finset.measurable_sum` is missed by local search but exists).
    - `MeasurableSingletonClass.measurableSet_singleton` — ℕ/Fin singletons measurable
      because `Nat.instMeasurableSpace := ⊤` / `Fin.instMeasurableSpace := ⊤`
      (MeasurableSpace/Instances.lean:30/34 — DISCRETE, not Borel) — feeds the
      `measurableSet_countLog_eq` preimage route.
    - `lintegral_finsetSum'` (`Integral/Lebesgue/Add.lean:341`; the old
      `lintegral_finset_sum` names are deprecated) / `lintegral_indicator_const` /
      `lintegral_mono` / `lintegral_congr` — the 60.2 consumption facts (probe-verified
      signatures; `lintegral_congr` here is the pointwise form, but `∫⁻` elaboration
      itself demands AEMeasurable — exactly why `measurable_countLog` and
      `aemeasurable_card_fiber` are mandatory, cf. 60.2 prep (4)).
    - NEW lemmas to prove inside 20.5 (flagged MISSING — none exist yet):
      `NoViolation_mono` (the freeze lemma: `NoViolation … t → t ≤ s → s ≤ N →
      NoViolation … s`, via `(run ω ⟨t⟩).2 = none → run freezes` Fin.induction) —
      load-bearing for `lt_R_iff`'s backward direction; `count_succ_eq_step_fst`
      (`count ω t.succ = (step ω (count ω t.castSucc)).1` — statement probe-verified);
      private `treeAt`-prefix congruence (Block B — `treeAt` depends only on `Λ s`, `s ≤ t`,
      ~12 lines over the foldr).
    - REMOVED from prep: `measurable_of_countable` / `measurable_of_finite` — domain-
      countable only (gap note); the pinned route needs neither (Fintype unions +
      structural induction). Also superseded: 60.2 log (4)'s `cylinder_witness` /
      `measurableSet_witness` route for the single-vertex cylinders (needs `hdet` +
      `Nonempty (Ω j)`) — 20.5 uses the direct `assign`-preimage route (needs only `hA`).
    - Original-scope note: the full-Sigma `measurable_run` (option component) is DROPPED —
      `Payload`'s dependent Sigma has no natural `MeasurableSpace` and no 60.x consumer;
      `measurable_count` (the state component) covers it. The 20.3 flag is CONFIRMED:
      `[Fintype ι]` is required (the `∀ i` / `∃ i` over ι in the NoViolation/lt_R sets).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-17 | 1 / 15 | done | Full two-block delivery (both sections Survey-compiled as statement shapes, `lake env lean` probe, 0 shape errors). **Block A — Algorithm.lean, new `section Measurability`**: NEW instance `State.instMeasurableSpace` (dsimp-infer_instance, ΩN precedent); `measurable_assign c` (measurable_pi_lambda/apply); `measurableSet_assign_mem {i c} : MeasurableSet {ω | assign ω c ∈ A i}` (preimage + hA); `measurableSet_Avail_eq {c} (S : Finset ι)` (biInter over `i` + by_cases on `i ∈ S` and the ω-free guard `∀ j ∈ vbl i, (c j : ℕ) < N`); `measurableSet_Avail_nonempty {c}` (biUnion over `i`); `measurableSet_step_fst_eq {c c'}` (fiber over `S` + ω-free advance-if); helper `count_succ_eq_step_fst` (Fin.induction unfold + run_snd_eq_step); `measurableSet_count_eq {t c} : MeasurableSet {ω | count … ω t = c}` (Fin.induction: base constant, step = ⋃ over `c, S` of IH-fiber ∩ Avail-fiber); `measurable_count {t} : Measurable (fun ω => count … ω t)` (measurable_pi_iff + finite unions of fibers); NEW freeze lemma `NoViolation_mono {ω} {t s} (ht) (hts : t ≤ s) (hs : s ≤ N)` (run-freeze Fin.induction: Avail-empty → step-none → run_snd_eq_step); `lt_R_iff {ω} {t : Fin (N+1)} : t.val < R … ω ↔ t.val < N ∧ ∃ i, assign ω (count … ω t) ∈ A i` (forward: run_step_of_lt_R's hi'; backward: NoViolation_mono + unfold R/Nat.find_min — the `t.val < N` conjunct handles the `t = N = R` fallback corner where the equivalence fails); `measurableSet_NoViolation {t : Fin (N+1)}` (NoViolation_fin_iff + ⋃ over `c` ∩ ⋂ over `i` of complements); `measurableSet_lt_R {t : Fin (N+1)}` (via lt_R_iff + decomposition over `c`); `measurableSet_R_lt_N` (R_lt_N_iff + biUnion over Fin N of NoViolation sets); `measurableSet_R_eq : MeasurableSet {ω | R … ω = N}` (`{R = N} = {R < N}ᶜ` via R_le); `measurableSet_log_eq_some {t : Fin (N+1)} {i} : MeasurableSet {ω | log … ω t.val = some i}` — THE hard core: unfold log's dif → `{ω | t < R ω ∧ (Classical.choose (run_step_of_lt_R … h)).1 = i}` → finite union over `c : State N`, `S : Finset ι` of `{count ω t = c} ∩ {Avail ω c = ↑S} ∩ {t < R ω}` ∩ ω-free pick-condition `pick ⟨↑S, hS⟩ = i` (option-singleton + subtype ext for the choose equality); `measurable_countLog [DecidableEq ι] {i} : Measurable (fun ω => countLog (log …) ω i)` (Finset.card_filter + Measurable.ite + Finset.measurable_sum); `measurableSet_countLog_eq [DecidableEq ι] {i k}` (preimage of `{k}`, measurableSet_singleton). **Block B — Basic.lean, new `section MeasurableOccurrence`** (+ `[∀ j, MeasurableSpace (Ω j)]`, `[Fintype κ]`, `(hA)` on the CountLogIdentity context; `open scoped ENNReal` at file top): `measurableSet_occ_canon {t : ℕ} (σ) : MeasurableSet {ω | t < R … ω ∧ canon (T … ω t) = σ}` (by_cases `t ≤ N`; empty case; main case = FINITE union over log patterns `p : Fin (t+1) → Option ι` of `⋂_{s ≤ t} {ω | log … ω s = p s}` intersected with the ω-free `p t ≠ none ∧ canon (forgetTime (treeAt vbl pℕ t)) = σ` condition — `t < R ⟺ log ω t ≠ none` on the fiber (log_ne_none_iff_lt_R), per-s fibers from Block A's `measurableSet_log_eq_some` + `{log = none} = {s < R}ᶜ`, private treeAt-prefix congruence); `measurableSet_occ (σ) : MeasurableSet {ω | ∃ t < R …, canon (T … ω t) = σ}` — the 60.2 `E_σ` (biUnion over range N); `aemeasurable_card_fiber (μ : Measure (ΩN N Ω)) (σ) : AEMeasurable (fun ω => (card ((range (R … ω)).filter (fun t => canon (T … ω t) = σ)) : ℝ≥0∞)) μ` (indicator-sum identity over range N + Measurable.indicator + Finset.measurable_sum + Measurable.aemeasurable). Covers the 60.2 slice 1:1: `measurableSet_count_eq` ≙ `measurableSet_countLog_eq`/`measurable_countLog`, `measurableSet_lt_R` ✓, `measurableSet_occ_canon` ✓ (+ `measurableSet_occ` = the `E_σ` form), `aemeasurable_card_fiber` ✓. Contingency: if the Proof agent stalls, deliver Block A alone (60.2 keeps its private slice for Block B's three facts) and re-plan Block B as attempt 2. | Completed across the paused session + resume (the A4 chunk was resumed by the user mid-flight). Chunk-by-chunk: A1 (4 + helper): `State.instMeasurableSpace` (dsimp-infer_instance), `measurable_assign`, `measurableSet_assign_mem`, `measurableSet_Avail_eq`, `measurableSet_Avail_nonempty` + private `measurableSet_Avail_mem`; A2 (4): ω-free `advance` + `measurableSet_step_fst_eq` (⋃ over availability fibers `S` ∩ ω-free advance-if test; the fiber direction extracts the pick-vs-choose equality via `step_fst_val_eq_of_mem`/`step_fst_eq_of_not_mem` + Subtype.ext), `count_succ_eq_step_fst` (Fin.induction unfold + `run_snd_eq_step`), `measurableSet_count_eq` (Fin.induction: base = constant-state test; step = ⋃ over `c₀` of IH-fiber ∩ step-fiber), `measurable_count` (`measurable_pi_lambda` + `measurable_to_countable'` per-component fibers); A3 (6): `NoViolation_mono` (freeze: Avail-empty → step-none → `step_fst_eq_of_none`, iterated by induction on `t + k`), `lt_R_iff` (forward via `run_step_of_lt_R`; backward via `NoViolation_mono` + unfold R/`Nat.find_min`; the `t.val < N` conjunct handles the `t = N = R` fallback), `measurableSet_NoViolation` (`NoViolation_fin_iff` + ⋂ᵢ of (⋃c …)ᶜ), `measurableSet_lt_R` (`lt_R_iff` + ⋃c⋃i decomposition), `measurableSet_R_lt_N` (`R_lt_N_iff` + ⋃ over `Fin (N+1)`), `measurableSet_R_eq` (`{R = N} = {R < N}ᶜ` via `R_le`); A4 (3): `measurableSet_log_eq_some` — the hard core: `{log = some i}` = `{t < R}` ∩ ⋃c⋃S of `{count = c} ∩ {Avail = S}` ∩ ω-free pick test `pick ⟨↑S, hS⟩ = i` (choose-spec extraction via `run_snd_eq_step` + split_ifs + congrArg Subtype.val; Subtype.ext fiber coherence both directions), `measurable_countLog` (card_filter → indicator sum + `Finset.measurable_sum` + `Measurable.ite`), `measurableSet_countLog_eq` (preimage of singleton). Block B (3 + 2 private helpers): private `extendPattern`/`extendPattern_of_lt`/`treeAt_congr` (`List.foldr_ext` prefix congruence) + `measurableSet_occ_canon` (by_cases `t ≤ N`; main case = ⋃ over patterns `p : Fin (t+1) → Option ι` of ⋂s log-fibers ∩ ω-free `p t ≠ none ∧ canon (forgetTime (treeAt vbl pℕ t)) = σ`; per-s fibers from `measurableSet_log_eq_some` + `{log = none} = {s < R}ᶜ`), `measurableSet_occ` (⋃ over `Fin N` of occ_canon), `aemeasurable_card_fiber` (indicator-sum identity over `range N` vs `range (R ω)` via `Finset.sum_subset` + `R_le`; ℕ→ℝ≥0∞ cast measurable from the discrete instance). Final tmp: 0 sorries, 0 warnings, 0 errors. | Independently verified: tmp (1247 lines — over the 500-line tmp convention, but COMPLETE and every declaration load-bearing, so integrated whole rather than split) `lake env lean` exit 0 with 0 warnings/0 errors; grep clean (no sorry/axiom/admit/native_decide — the only sorry hits are the header docstring); `#print axioms` on `measurableSet_log_eq_some`/`aemeasurable_card_fiber`/`measurable_countLog` = propext/Classical.choice/Quot.sound only. 60.2 slice spot-checked: `measurableSet_countLog_eq`/`measurable_countLog`/`measurableSet_lt_R`/`measurableSet_occ`/`aemeasurable_card_fiber` all present with pinned shapes. Integrated as TWO files: Block A (instance + 17 theorems + private `measurableSet_Avail_mem` + ω-free `advance`) → `Algorithm.lean` new `section Measurability` after `end Log` (added `open scoped BigOperators`); Block B (3 theorems + 2 private helpers) → `Basic.lean` new `section MeasurableOccurrence` after `end CountLogIdentity` (added `open MeasureTheory` — probe-required for `Measure` — and `open scoped ENNReal` — probe-required for ℝ≥0∞). 18 >100-char lines rewrapped; tmp probe #checks dropped; privates private; docstrings kept; `include hA in`/`omit … in` annotations kept exactly. Both files `lake env lean` exit 0 / 0 warnings; `lake build …Algorithm …Basic` OK; full `lake build` OK (8751 jobs, 0 warnings — Coupling.lean unaffected). tmp deleted. | `tmp_measurability.lean` |

---
## 30. Witness Trees

### 30.1. WitnessTree, path API, Proper, IsGood, instDecidableEq

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/WitnessTree.lean`
- **informal**
    - statement: |
        The witness-tree type and its structural/path API (survey B C9, notes §8; difficulty
        Medium, est. ~200 lines; critical path ★). Custom inductive — mathlib's only tree,
        `BinaryTree` (`Mathlib/Data/Tree/Basic.lean:33`), is a binary storage tree with a
        nil node and no rooted-forest API, and `SimpleGraph.IsTree`
        (`Combinatorics/SimpleGraph/Acyclic.lean:60`) is a Prop with no data.
        **Signatures pinned at Survey (full block compile-tested 2026-08-16,
        `/tmp/mt_survey_301_final.lean`, `lake env lean` exit 0, 0 warnings):**
        ```lean
        inductive WitnessTree (ι : Type u) where
          | mk : (label : ι) → (children : List (WitnessTree ι)) → WitnessTree ι
        ```
        plus:
        - constructor `mk` — NOT `node` (`node` is a parser keyword; `mk` is
          prototype-compiled);
        - accessors `labelOf` / `childrenOf` (inductive fields generate NO projections —
          `c.label` is invalid; accessor defs required);
        - `size` / `height` — plain recursion, NO `termination_by`/`decreasing_by` needed
          in the current toolchain (survey A §3.2's annotation is **stale**; the default
          decreasing tactic closes `List.map`/`∀ ∈` recursion). WF defs give *theorem*
          equations: `size_mk`/`proper_mk` are `by simp [size]`, NOT `rfl`;
        - path API (paths as `List ℕ`):
          ```lean
          inductive ValidPath : WitnessTree ι → List ℕ → Type u where
            | root {τ : WitnessTree ι} : ValidPath τ []
            | cons {τ : WitnessTree ι} {p : List ℕ} (i : ℕ) (c : WitnessTree ι)
                (hc : τ.childrenOf[i]? = some c) :
                ValidPath c p → ValidPath τ (i :: p)
          def treeAt {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) : WitnessTree ι
          def labelAt {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) : ι
          def depth (_τ : WitnessTree ι) (p : List ℕ) : ℕ := p.length
          ```
          `ValidPath` is **data-valued** (Type): a Prop `ValidPath` cannot be eliminated
          into a tree (`Exists`-into-data needs choice). `treeAt` matches on the path `p`
          and `cases` the proof in the branch — recursing on `ValidPath` directly compiles
          to the codegen-unsupported indexed recursor, and matching the proof first gives
          non-rfl equations; this shape gives rfl round-trips.
          **Name collision pinned:** the accessor keeps the name `treeAt`, namespaced
          `WitnessTree.treeAt` (called as `treeAt hp`, one explicit arg); 30.3's
          construction is `MoserTardos.treeAt (Λ) (t)` (two explicit args) — different
          arity/shape, no practical ambiguity;
        - `Proper : WitnessTree ι → Prop | mk _ cs => (cs.map labelOf).Nodup ∧
          ∀ c ∈ cs, Proper c` — recursively per-parent (survey A's version only checked
          the root);
        - `IsGood (vbl : ι → Finset κ) (τ : WitnessTree ι) := Proper τ ∧
          ∀ p q (hp : ValidPath τ p) (hq : ValidPath τ q), p ≠ q → depth τ p = depth τ q →
          Disjoint (vbl (labelAt hp)) (vbl (labelAt hq))` — path-based, the coupling's
          hypothesis (survey B §4.3; explicit ValidPath hypotheses since `labelAt` is
          hp-parameterized);
        - round-trip lemmas (`@[simp]`, all `rfl`): `treeAt_nil`, `treeAt_cons`,
          `labelAt_nil`, `labelAt_cons`, `depth_nil`, `depth_cons`; plus `labelOf_mk`,
          `childrenOf_mk`, `size_mk` (`[simp]`, `by simp [size]`), `size_pos`,
          `proper_mk` (`[simp]`, `by simp [Proper]`). These are what 30.2-30.6 consume
          (depth comparisons, label extraction, size unfolding);
        - `instDecidableEq [DecidableEq ι] : DecidableEq (WitnessTree ι)` — **mutual
          structural recursion** `eqDecTree`/`eqDecList` (first-argument recursion, nested
          matches; ~35 lines): computable AND `decide`-friendly (smoke-tested). Alternatives
          compile-tested and rejected: `WellFounded.fix` versions compile but `decide`
          cannot reduce them (stuck at `Acc.rec`); `WitnessTree.rec` (the nested recursor,
          motives `motive_1`/`motive_2`) is not codegen-supported.
        **PITFALLS (survey A §2.5/§3.2, re-verified 2026-08-16):** (i) `node` is a Lean
        parser keyword → constructor is `mk`; (ii) `deriving DecidableEq` **FAILS**:
        "None of the deriving handlers for class `DecidableEq` applied to `WT`"; (iii)
        there is NO `List.get?` (and no `List.getElem?` constant) in v4.32.0 — child
        access is the notation `l[i]?` only; (iv) `List.mem_cons_self` is all-implicit
        (`{a} {l}`), `List.mem_cons_of_mem` takes the cons'd element explicitly; (v)
        multi-argument equation patterns are broken inside `mutual` blocks (compile-tested);
        (vi) `WellFounded.induction` has a Prop-only motive — use `WellFounded.fix` for
        Type motives.
    - proof: |
        Definition, no proof — but the recursion patterns are the load-bearing
        compile-test results: `/tmp/mt_survey_301_final.lean` (2026-08-16, `lake env
        lean` exit 0, 0 warnings; imports `StatsMLlib.Probability.MoserTardos.VariableModel`
        — the eventual file import, confirmed acyclic; `Finset`/`Disjoint` for `IsGood`
        come from there). The prototype `/tmp/mt_proto_trees.lean` core (lines 1-76)
        also compiles as-is in the current toolchain; its smoke-test tail (lines 78-107)
        does NOT — it sits after `end MTProto` with the namespace closed (`treeAt`/`.mk`
        out of scope) — move smoke tests inside the namespace when reusing them.
- **prep**
    - `l[i]?` — the `getElem?` notation (core `GetElem?` class); no `List.get?`/
      `List.getElem?` constant exists to name in v4.32.0.
    - `List.Nodup` / `List.map` / `List.sum` / `List.foldl` / `List.length` — core.
    - `List.mem_cons_self` — core, ALL-implicit binders `{a} {l} : a ∈ a :: l`.
    - `List.mem_cons_of_mem` — core, `(y : α) {a} {l} : a ∈ l → a ∈ y :: l`.
    - `List.cons.inj` — core, `head :: tail = head✝ :: tail✝ → head = head✝ ∧ tail = tail✝`
      (the `eqDecList` false-branch extraction).
    - `Finset` + `Disjoint` on Finsets — via `StatsMLlib.Probability.MoserTardos.VariableModel`
      (the eventual file import; `IsGood` needs `vbl : ι → Finset κ`).
    - (NOT needed — stale survey A §3.2 guidance) `termination_by`/`decreasing_by`/
      `List.sizeOf_lt_of_mem` (core `Init/Data/List/BasicAux.lean:295`, still exists):
      the current toolchain accepts `size`/`height`/`Proper` annotation-free. Keep as
      fallback if the equation compiler ever rejects them.
    - Internal deps (survey B §5): none — leaf item.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `WitnessTree` (constructor `mk`) + structural API (`labelOf`/`childrenOf`/`size`/`height`) + path API (data-valued `ValidPath`, `treeAt`/`labelAt` hp-parameterized, `depth` = path length, rfl round-trip lemmas) + `Proper`/`IsGood` (survey B §4.2-4.3) + mutual-structural `instDecidableEq` (decide-friendly), all compiling, in `tmp_witness_tree.lean` — the full block is pre-compiled at `/tmp/mt_survey_301_final.lean` (exit 0, 0 warnings) | pre-compiled by Survey (round-trips rfl/simp, mutual instDecidableEq); Proof phase skipped — nothing to prove | independently verified: MCP diagnostics 0 errors / 0 warnings, `lake env lean` exit 0; no sorry/axiom/admit; one kept line >100 chars (`childrenOf_mk`) rewrapped. Integrated as `WitnessTree.lean` with Apache-2.0 header + `/-!` module docstring in house style (as in `Algorithm.lean`); smoke tests (`t1` + six `example`s) dropped per house convention; all other content verbatim. New module: 0 diagnostics, `lake build StatsMLlib.Probability.MoserTardos.WitnessTree` succeeds. tmp deleted | `tmp_witness_tree.lean` |

### 30.2. deepestEligible, attachBelow, attachInFirst, fold spec lemma

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/WitnessTree.lean`
- **informal**
    - statement: |
        The reverse-scan insertion core (survey B C10, notes §9; difficulty **Hard**, est.
        ~200 lines; critical path ★; survey B risk 1 — the single hardest structural
        point). On time-labeled trees `WitnessTree (ℕ × ι)`:
        - `deepestEligible` — the max depth among vertices whose label is eligible for the
          new entry, with `Option ℕ` depth bookkeeping (root-eligible vs none; the
          prototype found one real bug — a `0`-ambiguity that broke parent→child depth
          transfer — before the `Option` fix);
        - `attachBelow` / `attachInFirst` — mutual recursion (prototype-compiled, accepted
          with plain structural termination; re-verified against the integrated API
          2026-08-16): attach a new leaf `(s, i)` below the deepest eligible vertex; ties
          broken deterministically (the notes allow *any* tie-break, §9 step 5);
        - **the fold spec lemma**: after one insertion, the new leaf sits below a
          max-depth eligible vertex; old vertices and depths are unchanged; properness is
          preserved. Eligibility of `(s,i)` below `(s',i')` is
          `i = i' ∨ (vbl i ∩ vbl i').Nonempty` — i.e. `i ∈ Γ⁺(i')` (item 10.1).
        This spec lemma is the single invariant that Prop 10.1 (30.4), Lemma 11.1/Cor 11.2
        (30.5) and Prop 12.1 (30.6) all consume; its statement is pinned, its proof is by
        tree induction once.
        **SURVEY ADAPTATION (pinned 2026-08-16; defs + statements compile-tested at
        `/tmp/mt_attach_survey.lean`, `lake env lean` exit 0, 0 errors).** One semantic
        change from the prototype: `attachBelow`'s root-attachment branch appends the new
        leaf (`mk a (cs ++ [mk i []])`) instead of prepending (`mk a (.mk i [] :: cs)`).
        Reason: the spec's clause (b) ("old vertices unchanged") is consumed downstream as
        PATH STABILITY — a vertex addressed by path `p` must keep path `p` through all
        later insertions so the 30.4–30.6 fold inductions can track vertices by their
        paths; prepend shifts every existing child index on each root attachment and would
        force path-shift bookkeeping through every downstream proof. The notes allow any
        tie-break, so this only changes WHICH of several tied max-depth vertices is chosen
        (leftmost = oldest-inserted instead of most-recently-inserted). Consequence: the
        slides' example tree changes — see `informal.proof`.
        **Pinned defs** (in `namespace WitnessTree`, adapted from
        `/tmp/mt_proto_trees.lean` lines 30–61; only the accessor names `labelOf`/
        `childrenOf` and the append differ from the prototype):
        ```lean
        private def maxOption (m o : Option ℕ) : Option ℕ :=
          match m, o with
          | none, o => o
          | m, none => m
          | some a, some b => some (max a b)

        mutual
          def deepestEligible (elig : ι → ι → Prop) [∀ a b, Decidable (elig a b)] (i : ι) :
              WitnessTree ι → Option ℕ
            | mk a cs =>
              let d := cs.foldl (fun m c => maxOption m ((deepestEligible elig i c).map (· + 1))) none
              if elig i a then some (d.getD 0) else d

          def attachBelow (elig : ι → ι → Prop) [∀ a b, Decidable (elig a b)] (i : ι) :
              WitnessTree ι → WitnessTree ι
            | mk a cs =>
              let d := cs.foldl (fun m c => maxOption m ((deepestEligible elig i c).map (· + 1))) none
              match d with
              | none => if elig i a then mk a (cs ++ [mk i []]) else mk a cs
              | some dd => mk a (attachInFirst elig i dd cs)

          def attachInFirst (elig : ι → ι → Prop) [∀ a b, Decidable (elig a b)] (i : ι) (dd : ℕ) :
              List (WitnessTree ι) → List (WitnessTree ι)
            | [] => []
            | c :: cs =>
              if deepestEligible elig i c = some (dd - 1) then
                attachBelow elig i c :: cs
              else c :: attachInFirst elig i dd cs
        end

        def labels : WitnessTree ι → List ι
          | mk a cs => a :: cs.flatMap labels
        ```
        Semantics (notes §9 steps 3–5): `deepestEligible elig i τ = none` iff NO vertex is
        eligible — then `attachBelow` leaves `τ` unchanged (the entry is ignored; in the
        forest view it would start a new tree). `= some d` iff `d` is the maximum eligible
        depth — then the new leaf is appended to the children of the leftmost depth-`d`
        eligible vertex (leftmost recursively).
        **The pinned spec family** (the sorry-stubbed statements that this item's proof
        fills; the single invariant 30.4–30.6 consume):
        ```lean
        -- S1: deepestEligible computes the maximum eligible depth
        theorem deepestEligible_eq_none (τ : WitnessTree ι) :
            deepestEligible elig i τ = none ↔ ∀ p, ∀ hp : ValidPath τ p, ¬ elig i (labelAt hp)

        theorem deepestEligible_eq_some (τ : WitnessTree ι) (d : ℕ) :
            deepestEligible elig i τ = some d ↔
              (∃ p, ∃ hp : ValidPath τ p, depth τ p = d ∧ elig i (labelAt hp)) ∧
              ∀ p, ∀ hp : ValidPath τ p, elig i (labelAt hp) → depth τ p ≤ d

        -- S2a: no eligible vertex → the tree is unchanged
        theorem attachBelow_eq_self_of_deepestEligible_none {τ : WitnessTree ι}
            (h : deepestEligible elig i τ = none) : attachBelow elig i τ = τ

        -- S2b (a): the new leaf `mk i []` is a child of a depth-d eligible vertex
        theorem attachBelow_spec {τ : WitnessTree ι} {d : ℕ}
            (h : deepestEligible elig i τ = some d) :
            ∃ p, ∃ hp : ValidPath (attachBelow elig i τ) p, ∃ k : ℕ,
              ∃ hk : (treeAt hp).childrenOf[k]? = some (mk i []),
                depth (attachBelow elig i τ) p = d ∧ elig i (labelAt hp)

        -- (c): the new vertex has depth d + 1 and label i
        theorem attachBelow_newVertex {τ : WitnessTree ι} {d : ℕ}
            (h : deepestEligible elig i τ = some d) :
            ∃ p, ∃ hp : ValidPath (attachBelow elig i τ) p, ∃ k : ℕ,
              ∃ hk : (treeAt hp).childrenOf[k]? = some (mk i []),
                ∃ hpk : ValidPath (attachBelow elig i τ) (p ++ [k]),
                  depth (attachBelow elig i τ) (p ++ [k]) = d + 1 ∧ labelAt hpk = i

        -- (b): old vertices keep their labels (depths are definitionally path lengths)
        theorem labelAt_attachBelow {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) :
            ∃ hp' : ValidPath (attachBelow elig i τ) p, labelAt hp' = labelAt hp

        -- (b): the attachment is a single new leaf
        theorem size_attachBelow (τ : WitnessTree ι) :
            size (attachBelow elig i τ) ≤ size τ + 1

        theorem labels_attachBelow {τ : WitnessTree ι} {d : ℕ}
            (h : deepestEligible elig i τ = some d) :
            (labels (attachBelow elig i τ) : Multiset ι) = insert i (labels τ : Multiset ι)

        -- (d): properness is preserved (self-eligibility holds for the fold's relation)
        theorem attachBelow_proper {τ : WitnessTree ι} (hii : elig i i) (hτ : Proper τ) :
            Proper (attachBelow elig i τ)
        ```
        plus the path-extension pair (the new vertex's path `p ++ [k]` is valid; `ValidPath`
        is Type-valued so `validPath_append` is a `def` — match on the PATH first, cf.
        30.1's `treeAt`, because recursing on `ValidPath` directly compiles to the
        codegen-unsupported indexed recursor):
        ```lean
        def validPath_append {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) {k : ℕ}
            {c : WitnessTree ι} (hk : (treeAt hp).childrenOf[k]? = some c) :
            ValidPath τ (p ++ [k])
        theorem treeAt_validPath_append {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p)
            {k : ℕ} {c : WitnessTree ι} (hk : (treeAt hp).childrenOf[k]? = some c) :
            treeAt (validPath_append hp hk) = c
        ```
        **Parse pitfall (verified 2026-08-16):** parenthesized `∃`-binders
        `∃ p (hp : ValidPath τ p), …` DO NOT PARSE when the binder type is Type-valued
        ("unexpected token '('") — use nested `∃ hp : ValidPath τ p, …`.
    - proof: |
        Prove the spec by tree induction once; every later structural lemma only cites the
        spec. The structural plan (survey B §3.2: "pinned statement, proved by tree
        induction once"):
        - **S1** (`deepestEligible_eq_some`/`eq_none`): prove the CONJUNCTION of both
          ↔-statements by one simultaneous tree induction (each direction uses the other's
          IH for the children). The recursive step goes through the children-fold, so
          first prove the two private fold-max lemmas by list induction:
          `foldl_maxOption_eq_none : cs.foldl (fun m c => maxOption m (g c)) none = none ↔
          ∀ c ∈ cs, g c = none` and `foldl_maxOption_eq_some : … = some d ↔ (∃ c ∈ cs,
          g c = some d) ∧ ∀ c ∈ cs, ∀ k, g c = some k → k ≤ d` (the `←` directions are
          used in the synthesis subcases). The `+1` shift goes through
          `Option.map_eq_some_iff` (private `Option_map_succ_eq_some : o.map (· + 1) =
          some d ↔ o = some (d - 1) ∧ 1 ≤ d`, via `Nat.succ_pred_eq_of_pos`).
        - **S2b/S2a** (`attachBelow_spec` + `eq_self`): cases on the tree and on the
          children-fold `d`. `d = none` + root eligible → `d = 0`, new leaf at
          `childrenOf[cs.length]?` via `List.getElem?_concat_length`; `d = none` + root
          not eligible contradicts `h`; `d = some dd` → the private
          `attachInFirst_spec : attachInFirst elig i dd cs` equals
          `cs₁ ++ attachBelow elig i c :: cs₂` with `deepestEligible c = some (dd - 1)`
          and no match in `cs₁`, or is the identity when nothing matches (the match
          witness comes from `foldl_maxOption_eq_some`), then the IH on `c` lifts the
          witness path by the position `cs₁.length`.
        - **(b)** `labelAt_attachBelow`: by induction on the `ValidPath` (Type-valued —
          fine), using the private `attachInFirst_childrenOf_eq` (the `k`-th child is kept
          or replaced by its `attachBelow`-image) and private `labelOf_attachBelow` (root
          labels preserved). The `d = none` + root-eligible branch uses
          `List.getElem?_append_left` (with `List.getElem?_eq_some_iff` giving
          `k < cs.length` from the old path's validity).
        - **(c)** `attachBelow_newVertex`: combine S2b with `validPath_append` +
          `treeAt_validPath_append` + `labelOf_mk` + `List.length_append`.
        - **(b)** `size_attachBelow` / `labels_attachBelow`: structural, via the
          `attachInFirst_spec` decomposition + `List.sum_append` / `List.flatMap_append`
          + `Multiset.insert_eq_cons`/`cons_add`.
        - **(d)** `attachBelow_proper`: tree induction; the some-branch keeps
          `(children.map labelOf).Nodup` via the private `attachInFirst_map_labelOf`
          (children's root labels preserved); the root-attach branch uses
          `List.Nodup.append` with the `Disjoint` witness from `hii` (a same-label sibling
          would be an eligible vertex one level deeper than the maximum — contradiction
          with S1).
        **Compile-test 2026-08-16** (`/tmp/mt_attach_survey.lean`, imports the integrated
        `WitnessTree.lean`): defs compile (mutual recursion accepted with plain structural
        termination), all statements typecheck (sorry-stubbed), 0 errors. **Reduction
        caveat (verified):** `native_decide` evaluates the mutual defs (smoke examples
        pass), but kernel reduction does NOT unfold them (`decide` and `rfl` both fail) —
        proofs unfold via the equation lemmas: `simp [deepestEligible]` /
        `simp [attachBelow]` work (compile-tested).
        **Smoke tests** (all `native_decide`, all pass; `#eval` unavailable — the
        integrated `WitnessTree` has no `Repr`): the slides' example log `D, C, E, D`
        (overlap graph A~{B,E}, B~{A,C}, C~{B,D}, D~{C,E}, E~{A,D}; 30.3's fold preview)
        produces `mk (3,D) [mk (2,E) [mk (0,D) []], mk (1,C) []]` — root D(3); E(2) and
        C(1) children of the root (both overlap D); D(0) attached below E(2) (C, E tied
        at depth 1, leftmost tie-break = oldest-inserted = E). **This supersedes the
        pre-append result `mk (3,D) [mk (1,C) [mk (0,D) []], mk (2,E) []]` recorded in
        survey B §3.0 and the prototype smoke tail `/tmp/mt_proto_trees.lean` lines
        98–103 (that tail never compiled — its RHS was stale and inconsistent, containing
        both `(1,D)` and `(1,C)` from an older log).** Also verified: `t = 2` drops C
        (C~E false — no eligible vertex, notes §9 step 4) giving
        `mk (2,E) [mk (0,D) []]`; `t = 1` gives `mk (1,C) [mk (0,D) []]`.
- **prep**
    - `Option` — core (the depth bookkeeping: `Option.getD`, `Option.map`).
    - `List` API — core/mathlib: `List.foldl`, `List.flatMap` + `flatMap_append`
      (`Init/Data/List/Basic.lean:692`), `getElem?_concat_length`
      (`Init/Data/List/Lemmas.lean:322`), `getElem?_append_left`/`getElem?_append_right`/
      `getElem?_append` (`:1626/:1632/:1639`), `getElem?_eq_some_iff` (`:229`),
      `getElem?_cons_zero`/`getElem?_cons_succ` (`:221/:223`), `mem_of_getElem?`/
      `mem_iff_getElem?` (`:479/:485`), `sum_append` (`:1864`), `length_append`
      (`Init/Data/List/Basic.lean:631`), `Nodup.append`
      (`Mathlib/Data/List/Nodup.lean:171` — takes `Disjoint l₁ l₂`).
    - `Option.map_eq_some_iff`/`Option.map_eq_none_iff` —
      `Init/Data/Option/Lemmas.lean:291/:294` (the `+1` depth shift).
    - `Nat.succ_pred_eq_of_pos` — `Init/Data/Nat/Basic.lean:928` (`d - 1 + 1 = d`).
    - `Multiset.insert_eq_cons` (`Mathlib/Data/Multiset/ZeroCons.lean:97`),
      `Multiset.cons_add` (`Mathlib/Data/Multiset/AddSub.lean:105`) — the `labels`
      multiset shuffle.
    - Internal deps (survey B §5): items 30.1 (`WitnessTree` + path API + `Proper` +
      `instDecidableEq` — decide-friendly, used by the smoke tests), 10.1
      (`gammaPlus`/`mem_gammaPlus_of_overlap` — the fold's eligibility is exactly Γ⁺
      membership).
    - (NOT needed — stale) `Nat.findGreatest`: the prototype uses `maxOption`/`foldl`,
      which stays.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `deepestEligible`/`attachBelow`/`attachInFirst` (adapted to the integrated tree API, compiling — the Survey adaptation is pinned: root-attach APPENDS instead of prepends so old paths stay valid; tie-break stays deterministic, the notes leave it arbitrary) and PROVE the pinned spec-lemma family: `deepestEligible_eq_none`/`deepestEligible_eq_some` (max computation), `attachBelow_eq_self_of_deepestEligible_none`, `attachBelow_spec` + `attachBelow_newVertex` (new leaf below a max-depth eligible vertex, depth d+1), `labelAt_attachBelow` (old paths/labels persist), `size_attachBelow`/`labels_attachBelow` (single new leaf), `attachBelow_proper` (properness under `elig i i`), plus the path-extension `validPath_append`/`treeAt_validPath_append` and the private helpers (`foldl_maxOption_eq_none`/`_eq_some`, `Option_map_succ_eq_some`, `attachInFirst_spec`, `labelOf_attachBelow`, `attachInFirst_childrenOf_eq`, `attachInFirst_map_labelOf`) — all pre-compiled at `/tmp/mt_attach_survey.lean` (exit 0; smoke tests pass via `native_decide`, `simp`-unfolding verified) | Continuation (3rd Proof run): fixed the 3 mid-file errors and proved the remaining 8 stubs per the pinned plan — all 17 spec-family stubs now proved (S1, S2a, S2b/(a)/(b)/(c), (d) + `validPath_append`/`treeAt_validPath_append`); linter cleanup; one cosmetic deviation kept: `∃ _ : (treeAt hp).childrenOf[k]? = some (mk i [])` (unnamed binder) in the two S2b/(c) statements where the plan names `∃ hk : …` — the binder is unused downstream, and the blueprint's Type-valued-binder parse pitfall is confirmed; smoke tests (`native_decide`, 30.3's fold preview) all pass. 0 errors, 0 warnings, 0 sorries | Independently verified: tmp `lean_diagnostic_messages` 0/0 and `lake env lean` exit 0; no sorry/axiom/admit; `native_decide` confined to the smoke tests. Integrated into `WitnessTree.lean` (whole attach block — defs + private helpers + spec family + path-extension pair — in the tmp's `AttachSpec` layout; smoke tests dropped; module docstring updated; every >100-char line rewrapped, final file has none). Integrated module: 0 diagnostics; `lake build StatsMLlib.Probability.MoserTardos.WitnessTree` succeeds. Note: tmp was 914 lines (> the 500-line tmp convention) — accepted as-is: the spec family + its private helpers form one indivisible pinned invariant block (the survey-B risk-1 structural point), not splittable. tmp deleted; integrated and committed | `tmp_attach.lean` |

### 30.3. treeAt, forgetTime, T

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/WitnessTree.lean`
- **informal**
    - statement: |
        The witness-tree construction (survey B C11, notes §9; difficulty Easy, est. ~50
        lines; critical path ★). **Pinned at Survey 2026-08-16 — the WHOLE block below is
        compile-tested with REAL proofs (no sorry) at `/tmp/mt_tree_at_survey.lean`,
        `lake env lean` exit 0, 0 warnings; smoke tests pass via `native_decide`** (imports
        the integrated `WitnessTree` + `Algorithm` and copies the 30.2 attach def block —
        see the 30.2-dependency handling in `prep`):
        ```lean
        abbrev treeElig (vbl : ι → Finset κ) (p q : ℕ × ι) : Prop :=
          p.2 = q.2 ∨ (vbl p.2 ∩ vbl q.2).Nonempty

        def treeAt [DecidableEq ι] [Inhabited ι] (vbl : ι → Finset κ) (Λ : ℕ → Option ι)
            (t : ℕ) : WitnessTree (ℕ × ι) :=
          (List.range t).foldr
            (fun s τ => match Λ s with
              | none => τ
              | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ)
            (match Λ t with
              | none => WitnessTree.mk (t, default) []
              | some i => WitnessTree.mk (t, i) [])

        def forgetTime : WitnessTree (ℕ × ι) → WitnessTree ι
          | WitnessTree.mk p cs => WitnessTree.mk p.2 (cs.map forgetTime)

        noncomputable def T [DecidableEq ι] [Inhabited ι] (ω : ΩN N Ω) (t : ℕ) :
            WitnessTree ι :=
          forgetTime (treeAt vbl (log vbl A pick hpick ω) t)
        ```
        Design decisions (pinned): (i) the reverse scan `s = t-1 … 0` is a **`foldr` over
        `List.range t`** — `range t = [0, …, t-1]` so `foldr` processes `t-1` first; the
        prototype's `(List.range t).reverse.foldl` form is rewritten to exactly this `foldr`
        by `simp` via `List.foldl_reverse`, so the fold lemmas are `foldr`-shaped anyway;
        (ii) the eligibility is the **`abbrev` `treeElig vbl`** — `i = i' ∨ (vbl i ∩
        vbl i').Nonempty`, the time-labeled lift of Γ⁺-membership — an `abbrev` (NOT a
        `def`) so typeclass synthesis can unfold it: `Decidable (treeElig vbl p q)`
        synthesizes from `[DecidableEq ι]` (the `p.2 = q.2` disjunct) + `[DecidableEq κ]`
        (the `∩`; `Finset.decidableNonempty` is unconditional), which is exactly 30.2's
        `[∀ a b, Decidable (elig a b)]` requirement — no `classical` needed, `treeAt` stays
        computable (`native_decide`-friendly); (iii) the **dummy root** `(t, default)` when
        `Λ t = none` keeps `treeAt` total with only `[Inhabited ι]` (explicit binder, house
        precedent: `countLog`'s `[DecidableEq ι]`, 20.4) — the dummy is never consumed
        (30.6/30.7/40.3/60.1 all carry `t < R`, where `Λ t = some _`); `none` entries
        create no vertices; (iv) `[DecidableEq ι]`/`[Inhabited ι]` are **explicit binders**
        on `treeAt`/`T` (not section variables — keeps the section clean and the downstream
        burden visible: 30.4–30.7/40.3/60.1 need `[Inhabited ι]` in scope, supplied at 60.2
        from the `i : ι` parameter via `letI`); (v) `T`'s argument order `(vbl) (A) (pick)
        (hpick) (ω) (t)` matches `log vbl A pick hpick ω t` (house style); `noncomputable`
        because `log` is; (vi) `treeAt` lives in `namespace MoserTardos` (NOT
        `namespace WitnessTree`) — the name is occupied there by the 30.1 accessor
        `WitnessTree.treeAt` (pinned 30.1 note; the construction now takes `(vbl) (Λ) (t)`).
        The small lemmas 30.3 carries (the root-label pair for 30.6's injectivity + the
        `forgetTime` transport API for 30.7 — all Survey-proven in the scratch):
        ```lean
        theorem treeAt_root_label [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ}
            {i : ι} (h : Λ t = some i) :
            WitnessTree.labelOf (treeAt vbl Λ t) = (t, i)

        theorem T_root_label [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ} {i : ι}
            (h : log vbl A pick hpick ω t = some i) :
            WitnessTree.labelOf (T vbl A pick hpick ω t) = i

        theorem labelOf_forgetTime (τ : WitnessTree (ℕ × ι)) :
            WitnessTree.labelOf (forgetTime τ) = (WitnessTree.labelOf τ).2

        theorem childrenOf_forgetTime (τ : WitnessTree (ℕ × ι)) :
            WitnessTree.childrenOf (forgetTime τ) = (WitnessTree.childrenOf τ).map forgetTime

        theorem size_forgetTime (τ : WitnessTree (ℕ × ι)) :
            WitnessTree.size (forgetTime τ) = WitnessTree.size τ

        theorem forgetTime_getElem? {τ : WitnessTree (ℕ × ι)} {i : ℕ} {c : WitnessTree (ℕ × ι)}
            (hc : τ.childrenOf[i]? = some c) : (forgetTime τ).childrenOf[i]? = some (forgetTime c)

        def validPath_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
            (hp : WitnessTree.ValidPath τ p) : WitnessTree.ValidPath (forgetTime τ) p

        theorem treeAt_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
            (hp : WitnessTree.ValidPath τ p) :
            WitnessTree.treeAt (validPath_forgetTime hp) = forgetTime (WitnessTree.treeAt hp)

        theorem labelAt_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
            (hp : WitnessTree.ValidPath τ p) :
            WitnessTree.labelAt (validPath_forgetTime hp) = (WitnessTree.labelAt hp).2
        ```
        plus two private helpers (`labelOf_attachBelow` — root labels survive `attachBelow`;
        `labelOf_foldr_treeAt` — the fold preserves the root label). **Deferred to 30.4+**
        (per the blueprint split): `treeAt_proper`/abstract properness (30.4 — see the 30.4
        meta note), the fold equations over `List.range_succ` (30.4/30.6), and the REVERSE
        path direction `ValidPath (forgetTime τ) p → ValidPath τ p` — 30.7's `IsGood`
        transport needs it to lift abstract paths back to the time-labeled tree (∃-data,
        classical; 30.7's Survey should pin it).
    - proof: |
        All Survey-proven in the scratch (routes compile as written): `labelOf_forgetTime`/
        `childrenOf_forgetTime` by `cases τ; simp [forgetTime]` (the structural defs have
        NO rfl equations in this toolchain — cf. 30.1's `size_mk` note — always
        `simp`/`rw` the def, never `rfl`). `size_forgetTime`: **`induction` REJECTS the
        nested inductive** ("does not support the type WitnessTree because it is a nested
        inductive type") — use `refine WitnessTree.rec (motive_1 := …) (motive_2 := fun cs
        => ∀ c ∈ cs, …) (fun p cs ih => ?_) (nil) (cons) τ` with `List.map_congr_left` for
        the pointwise step and `rw [List.mem_cons] at hc'` (the `rcases hc' with rfl | hc'`
        pattern FAILS on raw List membership — `subst` rejects the extracted equality).
        `validPath_forgetTime`: match the PATH first, then the proof (30.1's pattern), the
        child bridge factored through the THEOREM `forgetTime_getElem?` (an embedded
        `by rw […]` proof in the branch makes the equation lemma's RHS carry a proof to
        rebuild — the named theorem application keeps it clean). `treeAt_forgetTime` by
        induction on `p` + `rw [validPath_forgetTime, WitnessTree.treeAt_cons, ih,
        WitnessTree.treeAt_cons]`. Root-label chain: `labelOf_attachBelow` by `cases τ` +
        `cases hd : cs.foldl (…) none` (the internal children-fold scrutinee) +
        `simp [WitnessTree.attachBelow, hd]` (the `none` case needs `by_cases hE :
        treeElig vbl p a` to resolve the eligibility `if`); `labelOf_foldr_treeAt` by list
        induction with the SEED generalized (`∀ τ, …`) — with the seed fixed the IH no
        longer matches after one `foldr` step; `treeAt_root_label` by
        `simp [treeAt, h, labelOf_foldr_treeAt]`; `T_root_label` by `unfold T;
        rw [labelOf_forgetTime, treeAt_root_label vbl h]`. **rw pitfall:** an rw chain
        ending at `Option.map f (some x) = some (f x)` is NOT auto-closed by `rw` — add an
        explicit `rfl` (it IS definitional).
        Smoke tests (all `native_decide`, all pass — pinned 30.2-preview semantics
        confirmed): with `Ev` = the 5 events and the 5-cycle realized as variable overlap
        (`vbl X = {X, next X}`, κ = Ev; overlap(A,B) via shared variable), the log
        `D, C, E, D` gives `treeAt vbl theLog 3 = mk (3,D) [mk (2,E) [mk (0,D) []],
        mk (1,C) []]`, `t = 2` drops C, `t = 1` appends D below C, `t = 0` is the bare
        root, and a padded `Λ 1 = none` root is the dummy `mk (1, default) []`.
- **prep**
    - `List.getElem?_map` — `Init/Data/List/Lemmas` (loogle-verified):
      `(l.map f)[i]? = Option.map f l[i]?` — the `forgetTime_getElem?` bridge.
    - `List.map_congr_left` — `Init/Data/List/Lemmas` (loogle-verified):
      `(∀ a ∈ l, f a = g a) → l.map f = l.map g` — `size_forgetTime`'s pointwise step.
    - `List.range` / `List.foldr` / `List.foldr_cons` / `List.foldl_reverse` — core (the
      fold iterator; `foldl_reverse` is `@[simp]` — this is WHY the def is pinned as the
      `foldr` form, proofs would see `foldr` regardless).
    - `List.range_succ` — `Init/Data/List/Range.lean` (loogle-verified):
      `range n.succ = range n ++ [n]` — NOT needed by 30.3 itself; the fold-induction
      identity for 30.4/30.6 (with `List.reverse_append`, core, scratch-spot-checked).
    - `List.mem_cons` — core — decompose List membership BEFORE `rcases` (see proof note).
    - `Finset.decidableNonempty` — `Mathlib/Data/Finset/Empty.lean:50` (10.1 prep;
      scratch-spot-checked `inferInstance`) — the `.Nonempty` disjunct's decidability.
    - `Option.map` — core — the `forgetTime_getElem?` tail (`rfl`-closable).
    - `Inhabited` — core — the dummy root (explicit binder, see statement note (iii)).
    - **30.2-dependency handling (pinned plan):** 30.2 is being proved in parallel; its
      defs are NOT yet in `WitnessTree.lean`. 30.3's tmp (`tmp_tree_at.lean`) imports
      `WitnessTree` + `Algorithm` and COPIES the 30.2 attach def block verbatim from
      `/tmp/mt_attach_survey.lean` (lines 16-52: `maxOption` + the mutual
      `deepestEligible`/`attachBelow`/`attachInFirst`, in `namespace WitnessTree` with its
      `variable {ι} {κ}` block) until 30.2 integrates. At 30.3's Review integration: if
      30.2 has already integrated into `WitnessTree.lean`, DROP the copied block (the defs
      are then in the file; the private `labelOf_attachBelow` helper can also be replaced
      by 30.2's public spec (b) `labelAt_attachBelow` at the root path — optional, the
      self-contained proof works as-is); if not, 30.3's integration WAITS for 30.2's
      (integration-order dependency — flag to Review).
    - **Import change at integration:** `WitnessTree.lean` adds
      `import StatsMLlib.Probability.MoserTardos.Algorithm` (for `ΩN`/`log` in `T`);
      acyclic (Algorithm imports VariableModel only); the existing `VariableModel` import
      becomes transitive — Review may drop it. Placement: after `end WitnessTree`
      (line 206), still inside `namespace MoserTardos`, a new `section TreeAt` with
      `variable {ι : Type u}`, `{κ : Type u} [DecidableEq κ]`, `{Ω : κ → Type v}`,
      `{N : ℕ}`, `(vbl : ι → Finset κ)`, `(A …)`, `(pick)`, `(hpick)` (mirroring the
      Algorithm sections; NO `[DecidableEq ι]`/`[Inhabited ι]` section variables — those
      are the explicit binders of `treeAt`/`T`, keeping the forgetTime block instance-free).
    - Internal deps (survey B §5): items 30.2 (`attachBelow`/`attachInFirst`), 30.1
      (`WitnessTree` + path API), 20.4 (`log`), 10.3 (`ΩN`), 10.1 (Γ⁺ semantics — only via
      `treeElig`'s unfolding, first consumed by 30.4/30.5).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `treeAt` (reverse-scan fold — pinned as the `foldr` over `List.range t`, definitionally the prototype's `(range t).reverse.foldl` via `List.foldl_reverse`; eligibility `abbrev treeElig vbl := i = i' ∨ (vbl i ∩ vbl i').Nonempty` so the 30.2 `Decidable` instance synthesizes from `[DecidableEq ι] [DecidableEq κ]`; explicit `[Inhabited ι]` dummy root, only consumed at genuine `t`) + `forgetTime` + `T vbl A pick hpick ω t`; prove `treeAt_root_label`/`T_root_label` (30.6's injectivity inputs) and the forgetTime transport API `labelOf_forgetTime`/`childrenOf_forgetTime`/`size_forgetTime`/`forgetTime_getElem?`/`validPath_forgetTime`/`treeAt_forgetTime`/`labelAt_forgetTime` (30.7's transport) — the whole block Survey-compiled with REAL proofs at `/tmp/mt_tree_at_survey.lean` (exit 0, 0 warnings; smoke tests `native_decide` confirm the pinned 30.2-preview tree) | pre-proven by Survey; Setup adapted one private-lemma reference; Proof phase skipped | Independently verified: tmp `lean_diagnostic_messages` 0/0 and `lake env lean` exit 0; no sorry/axiom/admit; 6 lines >100 chars rewrapped at integration. Integrated into `WitnessTree.lean` as `section TreeAt` in the tmp's layout (top-level `MoserTardos`, after the AttachSpec section — outside `namespace WitnessTree`, so the construction `treeAt` does not clash with the path-API `WitnessTree.treeAt`); module docstring updated (`## Main definitions`/`## Main results`); new import `StatsMLlib.Probability.MoserTardos.Algorithm` added (needed for `log` in `T`; no import cycle — Algorithm imports only VariableModel; the VariableModel import stays). Integrated module: 0 diagnostics; `lake build StatsMLlib.Probability.MoserTardos.WitnessTree` succeeds. tmp deleted; integrated and committed | `tmp_tree_at.lean` |

### 30.4. treeAt_proper

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/WitnessTree.lean`
    - note: **Statement re-pinned at Survey (2026-08-16, attempt 1).** The original
      statement `Proper (treeAt Λ t)` is TRIVIALLY true at the pair level (every vertex
      has a distinct time — each reverse-scan step creates at most one vertex — so
      pair-label Nodup is automatic and the notes' self-loop argument never bites; the
      30.3 Survey's check, confirmed). The notes' Prop 10.1 is about the ABSTRACT tree,
      and the abstract form is what 30.7 consumes (`IsGood (T … ω t)` contains
      `Proper (T … ω t)` = `Proper (forgetTime (treeAt …))`, one `unfold T` away) and
      what 60.1 needs for `𝒯_i(N)` membership (via 30.7's `treeAt_isGood`); 50.2's
      subtype carries `Proper` only as a predicate. 30.4 now proves BOTH: the headline
      `treeAt_proper : Proper (forgetTime (treeAt vbl Λ t))` (re-pinned) and the
      pair-level `treeAt_pair_proper` as a ~10-line bonus (NOT consumed by 30.5/30.6 —
      those work directly with 30.2's spec and 10.1; the pair form is kept as a
      fallback for 30.6's Survey). 30.4 does NOT consume 10.1: the notes' `A ∈ Γ⁺(A)`
      self-loop is literally `treeElig`'s `p.2 = q.2` disjunct (`Or.inl rfl`) — no
      `gammaPlus` unfolding. **Name-clash flag (30.3 integration):** 30.2's private
      `labelOf_attachBelow` (abstract version) and 30.3's private `labelOf_attachBelow`
      (pair-level version) share the name
      `MoserTardos.WitnessTree.labelOf_attachBelow` — 30.4's proof avoids the name
      entirely; the 30.3 Review must rename or replace one of them.
    - note: Downstream items must NOT assume cross-file access to 30.2/30.4 private
      helpers (pattern confirmed: 30.2's `maxOption`/`foldl_maxOption_eq_none`/
      `attachInFirst_spec`/`attachInFirst_map_labelOf` are file-scoped, and 30.4's
      section privates live only inside `section TreeAt` of `WitnessTree.lean`);
      the 30.4 proof re-derived what it needed from the public API (a local
      `mtMaxOption` copy + equation-lemma restatements + local list inductions).
      30.5's plan already handles it (its prep lists the public spec only).
- **informal**
    - statement: |
        Prop 10.1 (survey B C12, notes §10; difficulty Medium, est. ~80 lines; critical
        path ★). Pinned statements (Survey-compiled 2026-08-16 at
        `/tmp/mt_tree_proper_survey.lean`, `lake env lean` exit 0 — 0 errors, the only
        warnings are the expected `sorry`s; environment mirror of `tmp_tree_proper.lean`:
        imports the integrated `WitnessTree` + `Algorithm`, copies the 30.2 attach def
        block + spec statements + private helpers as sorry stubs, and the 30.3
        treeAt/forgetTime/T block with real proofs):
        ```lean
        /-- One insertion step preserves abstract properness: if the `forgetTime`-image
        of `τ` is proper, so is that of `attachBelow (treeElig vbl) (s, i) τ`. This is
        where the notes' self-loop argument (Prop 10.1) lives. -/
        private theorem forgetTime_attachBelow_proper [DecidableEq ι] {s : ℕ} {i : ι}
            (τ : WitnessTree (ℕ × ι)) (hτ : WitnessTree.Proper (forgetTime τ)) :
            WitnessTree.Proper (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) τ))

        /-- The reverse-scan fold preserves abstract properness (list induction on the
        fold's range list, with the accumulated tree generalized). -/
        private theorem foldr_forgetTime_proper [DecidableEq ι] {Λ : ℕ → Option ι} :
            ∀ l : List ℕ, ∀ τ : WitnessTree (ℕ × ι), WitnessTree.Proper (forgetTime τ) →
              WitnessTree.Proper (forgetTime (l.foldr
                (fun s τ => match Λ s with
                  | none => τ
                  | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) τ))

        /-- **Prop 10.1** (abstract tree): the witness tree built from the log prefix is
        proper — for genuine `t` (where `Λ t = some _`) this is the occurring tree
        `T … ω t`. -/
        theorem treeAt_proper [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
            WitnessTree.Proper (forgetTime (treeAt vbl Λ t))

        /-- Bonus (not consumed by 30.5/30.6): the time-labeled tree is proper. -/
        theorem treeAt_pair_proper [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
            WitnessTree.Proper (treeAt vbl Λ t)
        ```
        plus (only for the pair bonus) a private `foldr_pair_proper` mirroring
        `foldr_forgetTime_proper` with the hypothesis `WitnessTree.Proper τ`.
        Placement: inside 30.3's `section TreeAt` (after its lemmas, before
        `end TreeAt`), with `vbl`/`[DecidableEq κ]` as section variables and
        `[DecidableEq ι] [Inhabited ι]` as explicit binders on the theorems (30.3's
        style); no `omit`s needed (compile-verified: no unusedSectionVars warnings for
        the section).
    - proof: |
        (survey B §3.2(i): "a consequence of the spec lemma C10, proved once by
        induction over the fold".) **`forgetTime_attachBelow_proper`** — tree induction
        via `refine WitnessTree.rec (motive_1 := the lemma) (motive_2 := fun cs =>
        ∀ c ∈ cs, lemma c) …` (the `induction` tactic REJECTS the nested inductive;
        cf. 30.3's `size_forgetTime`). Case `τ = mk a cs`: `cases hd : cs.foldl
        (fun m c => maxOption m ((deepestEligible (treeElig vbl) (s,i) c).map (· + 1)))
        none` + `simp [WitnessTree.attachBelow, hd]` (30.3's `labelOf_attachBelow`
        pattern — the mutual defs unfold only via their equation lemmas):
        - `hd = none`, root not eligible: tree unchanged — exact `hτ`.
        - `hd = none`, root eligible: leaf `(s,i)` appended to the root's children;
          the abstract children list is `((cs.map forgetTime).map labelOf) ++ [i]`.
          Nodup via `List.Nodup.append hnodup (List.nodup_singleton i) dj` with
          `dj : List.Disjoint …` (**spell `List.Disjoint`** — the batteries def; the
          bare class-based `Disjoint` fails synthesis, compile-verified) reducing to
          `i ∉ (cs.map forgetTime).map labelOf`. Suppose `c ∈ cs` with
          `(labelOf c).2 = i`: then `treeElig vbl (s,i) (labelOf c)` by `Or.inl rfl`
          at the root path (`ValidPath.root`, `labelAt_nil`), contradicting
          `deepestEligible (treeElig vbl) (s,i) c = none`, obtained from `hd` via
          30.2's private `foldl_maxOption_eq_none` + `Option.map_eq_none_iff` + 30.2's
          S1 `deepestEligible_eq_none`. Recursive part: the new leaf has no children
          (`simp [WitnessTree.Proper]`); the kept children from `hτ`'s second
          conjunct via `List.mem_map_of_mem`.
        - `hd = some dd`: children replaced by `attachInFirst`. Root-level Nodup:
          30.2's private `attachInFirst_map_labelOf` keeps the pair-label list, so the
          abstract child-label list is unchanged (via 30.3's `labelOf_forgetTime` +
          `childrenOf_forgetTime` + `List.map_map`/`List.map_congr_left`). Recursive
          properness via `attachInFirst_spec`'s decomposition
          `cs = cs₁ ++ c :: cs₂`, `attachInFirst … = cs₁ ++ attachBelow … c :: cs₂`:
          kept children from `hτ` (`List.mem_append` + `mem_map_of_mem`), the replaced
          child by the IH on `c`.
        **`foldr_forgetTime_proper`** — list induction with the tree generalized
        (30.3's `labelOf_foldr_treeAt` generalization pattern): nil `simpa using hτ`
        (`List.foldr_nil` @[simp]); cons `rw [List.foldr_cons]` + `cases Λ s` —
        `none`: `simpa`, `some i`: `forgetTime_attachBelow_proper`. **`treeAt_proper`**
        — `unfold treeAt; apply foldr_forgetTime_proper; cases h : Λ t <;>
        simp [forgetTime, WitnessTree.Proper, h]` (the seed is a leaf; `proper_mk`
        + `[]`-Nodup close it). **`treeAt_pair_proper`** — `foldr_pair_proper`
        (same list induction, pair level) with the `some i` step = 30.2's public
        `attachBelow_proper (elig := treeElig vbl) (i := (s,i)) (hii := Or.inl rfl)
        (ih …)` — the self-eligibility is the `p.2 = q.2` disjunct, and the
        `Decidable (treeElig vbl (s,i) (s,i))` instance synthesizes from
        `[DecidableEq ι] [DecidableEq κ]` (30.3-verified); no self-loop argument
        needed at the pair level. **Not consumed:** `List.range_succ` (the t-induction
        alternative breaks — the seed's root time changes from `t` to `t+1` across
        `treeAt Λ t`/`treeAt Λ (t+1)` — and the fold's list induction is the proof;
        `range_succ` remains 30.6's tool), 30.2's S2b `attachBelow_spec`,
        `labelAt_attachBelow`, `deepestEligible_eq_some`, `attachBelow_newVertex`,
        and 10.1's Γ⁺ lemmas (see meta note).
- **prep**
    - `List.foldr_cons` — core `Init/Data/List/Basic.lean:549`, `@[simp, grind =]` —
      the fold-step rewrite in both fold inductions.
    - `List.foldr_nil` — core `Init/Data/List/Basic.lean:548`, `@[simp, grind =]` —
      the nil case (`[].foldr f b = b`).
    - `List.Nodup.append` — `Mathlib/Data/List/Nodup.lean:171` —
      `(d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂) : Nodup (l₁ ++ l₂)`
      (the root-attach branch).
    - `List.nodup_append'` — `Mathlib/Data/List/Nodup.lean:162` — the iff-form with
      `Disjoint` (fallback if the constructor form fights back).
    - `List.nodup_singleton` — `Mathlib/Data/List/Nodup.lean:41` — `Nodup [a]`.
    - `List.Disjoint` — **batteries** `Batteries/Data/List/Basic.lean:544` —
      `def Disjoint (l₁ l₂ : List α) : Prop := ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False`.
      **PITFALL (compile-verified):** spell it `List.Disjoint` at use sites — inside
      `namespace List` the bare name resolves to this batteries def (that is what
      `Nodup.append`'s argument is), but OUTSIDE it resolves to the class-based order
      `Disjoint` (`Mathlib/Order/Disjoint.lean`), whose `PartialOrder (List ι)`
      instance does NOT exist in mathlib (synthesis failure without the prefix).
    - `List.mem_map` — core `Init/Data/List/Lemmas.lean:1124`, `@[simp 500,
      grind =]`; `List.mem_map_of_mem` — Lemmas.lean:1131.
    - `List.map_map` — core `Init/Data/List/Lemmas.lean:1251`, `@[simp]`;
      `List.map_congr_left` — Lemmas.lean:1163 — the label-list shuffles in the
      `some dd` branch.
    - `List.mem_singleton` — core `Init/Data/List/Lemmas.lean:418` (the
      `List.Disjoint l [i]` proof); `List.mem_append` / `List.map_append`
      (Lemmas.lean:1852, `@[simp]`) / `List.nodup_nil` — core, `@[simp]`.
    - `Option.map_eq_none_iff` — core `Init/Data/Option/Lemmas.lean:294`, `@[simp]` —
      the `hd = none` → children-fold-none step.
    - `WitnessTree.rec` — the nested-inductive recursor (30.1; `induction` REJECTS
      `WitnessTree` — the motives pattern from 30.3's `size_forgetTime`).
    - `WitnessTree.Proper` / `proper_mk` (@[simp]) / `ValidPath.root` / `labelAt_nil` /
      `depth` — 30.1's API.
    - 30.2 (same-file once integrated; sorry-stubbed + def-block copied in the tmp,
      per 30.3's pinned dependency handling): public `deepestEligible_eq_none` (S1) and
      `attachBelow_proper` (pair bonus); private helpers `foldl_maxOption_eq_none`,
      `attachInFirst_spec`, `attachInFirst_map_labelOf`. **Compile-verified:** the
      private helpers are usable at use sites WITHOUT naming their auto-bound `elig`/
      `i` section variables (probe theorems in the survey scratch compile).
    - 30.3: `treeElig`/`treeAt`/`forgetTime` + `labelOf_forgetTime`/
      `childrenOf_forgetTime` (the 30.3 block copied with real proofs).
    - **MISSING? no.** Everything above exists and compiles (survey scratch, exit 0).
    - Internal deps (survey B §5): items 30.2 (spec S1 + private helpers + defs), 30.3
      (`treeAt`/`forgetTime`/`treeElig`), 30.1 (`WitnessTree` + `Proper`). 10.1 NOT
      consumed (see meta note).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | working | Prove `treeAt_proper : Proper (forgetTime (treeAt vbl Λ t))` (re-pinned abstract form — the 30.7/60.1 consumer; the pair-level form is trivial by distinct times) + the pair-level bonus `treeAt_pair_proper` via 30.2's `attachBelow_proper`; workhorses: private `forgetTime_attachBelow_proper` (tree induction via `WitnessTree.rec`; the notes' self-loop argument through 30.2's S1 + private `foldl_maxOption_eq_none`/`attachInFirst_spec`/`attachInFirst_map_labelOf`) and private `foldr_forgetTime_proper` (fold list induction) — all 4 statements compile-verified at `/tmp/mt_tree_proper_survey.lean` | All 5 statements proved (245 lines, 0 errors/0 warnings/0 sorries). Forced deviation: 30.2's private helpers (`maxOption`, `foldl_maxOption_eq_none`, `attachInFirst_spec`, `attachInFirst_map_labelOf`) are file-scoped (`Unknown constant` cross-file), so the machinery was re-derived from the public API — a local `mtMaxOption` definitional copy of `maxOption`, equation-lemma restatements `attachBelow_mk_treeElig`/`deepestEligible_mk_treeElig` (`rw [..eq_1]; rfl`), and local list inductions `forgetTime_attachInFirst_map_labelOf`/`forgetTime_attachInFirst_proper`; the root-attach Nodup contradiction goes through 30.2's public S1 `deepestEligible_eq_some`. Foldr wrap-order fix: the fold lemmas are `foldr`-shaped to match `treeAt`'s `foldr` over `range t` (`t-1` wraps the seed first; per 30.3's note, no `reverse.foldl` form). Headlines close with `unfold treeAt; apply foldr_.._proper; cases h : Λ t <;> simp`. | Independently verified: tmp 0 LSP diagnostics + `lake env lean` exit 0; no sorry/axiom/admit/native_decide; 6 lines >100 rewrapped at integration. Integrated into `WitnessTree.lean` `section TreeAt` after the 30.3 declarations, helpers kept private; the tmp's `labelOf_attachBelow_root` dropped — 30.3's in-section private `labelOf_attachBelow` reused at its single use site (30.4's side of the name-clash flag resolved). Module docstring `## Main results` updated (`treeAt_proper`/`treeAt_pair_proper`). tmp deleted. Integrated file: 0 LSP diagnostics; `lake build StatsMLlib.Probability.MoserTardos.WitnessTree` OK (1859 jobs). | `tmp_tree_proper.lean` |

### 30.5. depth_gt_of_earlier_overlap, vbl_disjoint_of_same_depth

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/WitnessTree.lean`
    - note: **30.3 is now INTEGRATED into `WitnessTree.lean`** (its `section TreeAt` at
      line ~1098, incl. `treeElig`/`treeAt`/`forgetTime`/`T`) — the 30.5 tmp imports
      `WitnessTree` directly, NO copied def block (unlike 30.3's tmp, which copied 30.2's
      defs while 30.2 was unintegrated). **10.1 is NOT directly consumed**: the notes'
      `[u] ∈ Γ⁺([v])` step is literally `treeElig`'s second disjunct (`Or.inr` of the
      overlap — the same disjunction as `mem_gammaPlus_of_overlap`'s *hypothesis*), so no
      `gammaPlus` unfolding or citation is needed; the eligibility argument applies
      `treeElig vbl (s, i) (labelAt hv')` directly (cf. 30.4's meta note, same pattern).
      **Estimate grows to ~450–550 lines** (the 30.2-private helpers are inaccessible from
      the tmp, so the proof carries its own glue package — see prep; the 30.2 tmp precedent
      of a >500-line indivisible block applies).
- **informal**
    - statement: |
        Lemma 11.1 / Cor 11.2 (survey B C13, notes §11; difficulty Med–Hard, est. ~150
        lines; critical path ★), on the **time-labeled** constructed tree `treeAt vbl Λ t`
        (the log time `q(u)` is the label's first component). **Pinned at Survey
        (compile-tested 2026-08-16 at `/tmp/mt_depth_survey.lean`, `lake env lean` exit 0 —
        the only diagnostics are the expected `sorry`s; imports the integrated
        `WitnessTree` only):**
        ```lean
        /-- **Lemma 11.1**: an earlier entry sharing a variable with a later one is
        strictly deeper. -/
        theorem depth_gt_of_earlier_overlap [DecidableEq ι] [Inhabited ι]
            {Λ : ℕ → Option ι} {t : ℕ} {p q : List ℕ}
            (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p)
            (hq : WitnessTree.ValidPath (treeAt vbl Λ t) q)
            (ht : (WitnessTree.labelAt hp).1 < (WitnessTree.labelAt hq).1)
            (hov : (vbl (WitnessTree.labelAt hp).2 ∩ vbl (WitnessTree.labelAt hq).2).Nonempty) :
            WitnessTree.depth (treeAt vbl Λ t) p > WitnessTree.depth (treeAt vbl Λ t) q

        /-- Distinct vertices have distinct times (each reverse-scan step creates at most
        one vertex). The comparability input of Cor 11.2 — and of 40.2's backward
        direction (`q(u) ≠ q(v)` for distinct vertices). -/
        theorem treeAt_timeInject [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ}
            {p q : List ℕ} (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p)
            (hq : WitnessTree.ValidPath (treeAt vbl Λ t) q) (hne : p ≠ q) :
            (WitnessTree.labelAt hp).1 ≠ (WitnessTree.labelAt hq).1

        /-- **Cor 11.2**: vertices at the same depth have disjoint variable sets (distinct
        vertices have distinct times, so Lemma 11.1 applies symmetrically). -/
        theorem vbl_disjoint_of_same_depth [DecidableEq ι] [Inhabited ι]
            {Λ : ℕ → Option ι} {t : ℕ} {p q : List ℕ}
            (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p)
            (hq : WitnessTree.ValidPath (treeAt vbl Λ t) q)
            (hne : p ≠ q)
            (hdepth : WitnessTree.depth (treeAt vbl Λ t) p =
              WitnessTree.depth (treeAt vbl Λ t) q) :
            Disjoint (vbl (WitnessTree.labelAt hp).2) (vbl (WitnessTree.labelAt hq).2)
        ```
        All three sit in a `section TreeAtDepth` with 30.3's variable block
        (`{ι} {κ} [DecidableEq κ] {Ω} {N} (vbl) (A) (pick) (hpick)`) and explicit
        `[DecidableEq ι] [Inhabited ι]` binders (30.3's style — `treeAt` requires them).
        The private machinery (all statements compile-tested; proved in the tmp):
        - predicates `depthStrict vbl τ := ∀ p q (hp) (hq), (labelAt hp).1 <
          (labelAt hq).1 → (vbl (labelAt hp).2 ∩ vbl (labelAt hq).2).Nonempty →
          depth τ p > depth τ q` and `timeInject τ := ∀ p q (hp) (hq), p ≠ q →
          (labelAt hp).1 ≠ (labelAt hq).1`; plus `buildBelow Λ l σ` — the reverse-scan
          fold of `treeAt` with the seed generalized (defeq to `treeAt`'s fold term).
        - attach glue (pair level): `attachBelow_depthStrict_step` (one insertion preserves
          `depthStrict` when `s <` every time in `σ`) and `attachBelow_newVertex_unique`
          (two paths with time `s` in the attachment are equal).
        - labels-multiset bridge (the "one vertex per time" certificate):
          `mem_labels_of_labelAt` (a vertex's label occurs in the preorder `labels`),
          `time_gt_of_mem_labels` (all labels of a time-`>s` tree have time `> s`),
          `two_le_count_labels_of_two_paths` (distinct paths with one label give count
          `≥ 2`).
        - the fold induction: `foldr_time_gt` (times stay `> s` through the fold) and
          `foldr_depthStrict_timeInject` (both invariants preserved by the fold, under the
          side conditions `(∀ s₁ ∈ l, ∀ p (hp : ValidPath σ p), s₁ < (labelAt hp).1) ∧
          l.Pairwise (· < ·)`); then `treeAt_depthStrict`/`treeAt_timeInject'` from the
          leaf seed (vacuous base) + `List.mem_range` + `List.pairwise_lt_range`.
        - abstract-level glue (namespace `WitnessTree`, to integrate into/near
          `section AttachSpec`): `attachInFirst_childrenOf` (the `j`-th child is kept or
          replaced by its `attachBelow`-image), `attachInFirst_replaced` (a replaced child
          is a `some (dd - 1)`-match **or** the attachment was a no-op — the
          `attachBelow i c = c` disjunct is needed: the naive
          `deepestEligible … = some (dd - 1)` conclusion is FALSE when
          `deepestEligible … = none` and `c` coincides with its `attachBelow`-image), and
          `attachBelow_old_or_new {τ} {d} (h : deepestEligible elig i τ = some d) {q}
          (hq : ValidPath (attachBelow elig i τ) q) :
          (∃ hq' : ValidPath τ q, labelAt hq' = labelAt hq) ∨
          (labelAt hq = i ∧ depth (attachBelow elig i τ) q = d + 1)` — the workhorse
          converse of 30.2's `labelAt_attachBelow` (non-exclusive by design: an old
          vertex labeled `i` satisfies both).
    - proof: |
        (survey B §3.2(ii), Leanified.) The dependency graph IS the variable-overlap
        graph, so the eligibility step is definitional: overlap ⟹ `treeElig vbl (s, i) l`
        by `Or.inr` — no 10.1 citation (see meta note). The depth conclusion comes from
        30.2's spec: the new vertex is a child of a max-depth eligible vertex, hence
        deeper than *every* eligible vertex (`d(u) = d + 1 > d ≥ d(v)`).
        **`attachBelow_depthStrict_step`** (the core; hσ : `depthStrict vbl σ`, ht :
        `s <` every time in σ, τ' := `attachBelow (treeElig vbl) (s, i) σ`): take
        `p q hp hq hlt hov` in τ'. `by_cases hd : deepestEligible … = none` → τ' = σ by
        30.2 S2a, `hσ` applies. Else `rcases` some d; `by_cases hsu : (labelAt hp).1 = s`:
        - **u new**: `attachBelow_old_or_new` on `hp` — the old disjunct gives time `> s`
          (via ht), contradicting `hsu`; the new disjunct gives `labelAt hp = (s, i)` ∧
          `depth τ' p = d + 1`. For v: `s < (labelAt hq).1` (from `hlt` + `labelAt hp`),
          so the new disjunct of `attachBelow_old_or_new` on `hq` is impossible (time s);
          the old disjunct gives `hq' : ValidPath σ q` with the same label. v is eligible:
          `treeElig vbl (s, i) (labelAt hq')` by `Or.inr` (hov via `labelAt hp = (s,i)`
          and `labelAt hq' = labelAt hq`); 30.2 S1 (`deepestEligible_eq_some`) gives
          `depth σ q ≤ d`; `depth τ' q ≤ d < d + 1 = depth τ' p` (depths are path lengths,
          `omega`).
        - **u old** (`hsu` false): old disjunct on `hp` (the new disjunct contradicts
          `hsu`); then `s < (labelAt hp).1` (ht) and `s < (labelAt hq).1` (hlt), so `hq`
          is old too; `hσ p q hp' hq'` closes (same labels via the disjuncts).
        **`attachBelow_old_or_new`** (abstract level, by `WitnessTree.rec` with the
        motive-2 list pattern — 30.2's `attachBelow_spec` shape): cases on τ = `mk a cs`;
        `simp [WitnessTree.attachBelow]` + `split` (compile-verified from OUTSIDE the
        file: the match over the private `maxOption` fold splits, giving `hfold : … =
        some dd` — the private name is mangled `…maxOption✝` and cannot be NAMED from the
        tmp, only `split`/`cases`-reduced) + `split_ifs`; root-attach branch (`d = 0`):
        `q = []` → root label (old); `j < cs.length` → kept child (old, via
        `List.getElem?_append_left`); `j = cs.length` → the new leaf `mk i []`
        (`List.getElem?_concat_length`), label `i`, depth `1 = 0 + 1`. `some dd` branch:
        `dd = d` (from `h`'s unfolding); `attachInFirst_childrenOf` on `hq` — kept child →
        old; replaced child → `attachInFirst_replaced` — the `some (dd - 1)` disjunct
        gives the IH on the child (depth arithmetic `(dd - 1) + 1 = dd` needs
        `Nat.succ_pred_eq_of_pos` with `1 ≤ dd`, extracted inline from `hfold` by
        `cases`-reduction — no standalone statement possible since `maxOption` is
        unnameable), the self-disjunct gives `attachBelow i c = c` → old.
        **`attachBelow_newVertex_unique`** (pair level): by the multiset bridge —
        `labels_attachBelow` (30.2) gives `(labels τ' : Multiset _) = insert (s, i)
        (labels σ : Multiset _)`; `time_gt_of_mem_labels` gives `(s, i) ∉ labels σ`, so
        `(labels τ').count (s, i) = 1` (`Multiset.insert_eq_cons` +
        `Multiset.count_cons_self` + `Multiset.count_eq_zero_of_notMem` +
        `Multiset.coe_count` — probe-compiled). For each of `q₁, q₂` with time `s`:
        `mem_labels_of_labelAt` puts `labelAt hqᵢ ∈ labels τ'`; the multiset identity and
        the freshness force `labelAt hqᵢ = (s, i)`; if `q₁ ≠ q₂`,
        `two_le_count_labels_of_two_paths` gives `2 ≤ (labels τ').count (s, i) = 1` —
        contradiction. (`two_le_count_labels_of_two_paths` by `WitnessTree.rec` + cases
        on the two paths — nil/nil contradicts `hne`; nil/cons uses `Multiset.count_pos`
        for the child's occurrence; cons/cons recurses in the common child, and for
        distinct children sums the two child counts via the `List.flatMap` ↔
        `Multiset.sum` coercion bridge — no named mathlib lemma found for
        `coe_flatMap`, prove the small bridge inline by list induction with
        `Multiset.count_add`.)
        **`foldr_time_gt`** (list induction, seed-side conditions generalized): the
        `some i` step splits `deepestEligible` none/some — none: tree unchanged (S2a); some:
        old paths by `attachBelow_old_or_new` (first disjunct) + IH, the new vertex's time
        `s₁` via the `s < s₁` head condition.
        **`foldr_depthStrict_timeInject`** (list induction, `σ` generalized, side
        conditions `(∀ s₁ ∈ l, ∀ p hp, s₁ < (labelAt hp).1) ∧ l.Pairwise (· < ·)` —
        both hereditary under restriction, and the head gives the step's `s < s₁` and
        `s <` all σ-times): the `none` step is `simpa`; the `some i` step applies
        `attachBelow_depthStrict_step` (with `foldr_time_gt` for the time bound) and, for
        `timeInject`: old-old via the IH (same paths through the first disjunct),
        old-new/new-old by the strict time separation (`> s` vs `= s`),
        new-new by `attachBelow_newVertex_unique`.
        **Tree level**: `treeAt_depthStrict`/`treeAt_timeInject'` by
        `change depthStrict vbl (buildBelow vbl Λ (List.range t) (match Λ t with …))`
        (defeq) + the fold theorem with the leaf seed: the two invariants hold vacuously
        (the only path is `[]` — `cases p <;> cases hp` kills the cons case via
        `childrenOf = []`), the side condition by `List.mem_range` (times `< t`), and
        `List.pairwise_lt_range` (implicit `n` — no explicit argument).
        **Public theorems**: `depth_gt_of_earlier_overlap` = `treeAt_depthStrict` at the
        given paths; `treeAt_timeInject` = `treeAt_timeInject'`; `vbl_disjoint_of_same_depth`
        = `by_contra` + `Finset.not_disjoint_iff` (extract `x` from the overlap) +
        `treeAt_timeInject` + `Nat.lt_or_gt_of_ne` + `depth_gt_of_earlier_overlap` in
        both directions (the symmetric direction via `Finset.inter_comm`), closing with
        `Nat.ne_of_gt` against `hdepth`.
- **prep**
    - Internal deps (survey B §5, refined): 30.3 (`treeElig`/`treeAt` — INTEGRATED into
      `WitnessTree.lean`; the tmp imports them, no copied block); 30.2 public spec:
      `deepestEligible_eq_some` (S1 — the `≤ d` bound for the eligible `v`),
      `attachBelow_eq_self_of_deepestEligible_none` (S2a — the none-case reductions),
      `labelAt_attachBelow` (S2(b) — root-label preservation in the `q = []` case of
      `attachBelow_old_or_new`), `labels_attachBelow` (the multiset identity of the
      uniqueness proof). `attachBelow_spec`/`attachBelow_newVertex` are NOT consumed —
      `attachBelow_old_or_new` replaces the path-level spec (its induction is
      self-contained). **30.2's private helpers are file-scoped and INACCESSIBLE from the
      tmp** (`maxOption`, `attachInFirst_spec`, `attachInFirst_childrenOf_eq`, the private
      `foldl_maxOption_*`): the tmp proves its own mini `attachInFirst_*` lemmas (the
      *defs* are public and unfold from outside — compile-verified) and reduces the
      `maxOption` fold only via `split`/`cases` (the mangled `…maxOption✝` name appears in
      goals but cannot be written). 10.1 NOT consumed (meta note). Algorithm NOT needed
      (`treeAt` takes an abstract `Λ`).
    - `List.pairwise_lt_range` — core `Init/Data/List/Nat/Range.lean` — the
      `(List.range t).Pairwise (· < ·)` side condition; **`n` is implicit** — no explicit
      argument at the use site.
    - `List.Pairwise` — core — the fold's sortedness side condition; `List.pairwise_cons`
      (core) decomposes it at the induction step (`Pairwise R (a :: l) ↔
      (∀ b ∈ l, R a b) ∧ Pairwise R l`).
    - `List.mem_range` — core — the seed side condition (`s < t` from `s ∈ range t`).
    - `List.foldr_cons`/`List.foldr_nil`/`List.foldl_cons` — core — the fold reductions.
    - `List.getElem?_append_left` / `List.getElem?_concat_length` /
      `List.getElem?_cons_zero` / `List.getElem?_cons_succ` / `List.getElem?_eq_some_iff`
      / `List.mem_of_getElem?` / `List.mem_iff_getElem?` — the child-position analysis in
      the glue (`Init/Data/List/Lemmas`; the 30.2 prep's line numbers).
    - `List.mem_flatMap` — core (simp-normal) — the `mem_labels_of_labelAt` step;
      `List.mem_cons`/`List.mem_append`/`List.mem_singleton` — core.
    - `Option.map_eq_some_iff`/`Option.map_eq_none_iff`/`Option.some.inj`/`Option.getD` —
      core — the `+1` depth shifts and the `some`-injections in the glue.
    - `Nat.succ_pred_eq_of_pos` — core `Init/Data/Nat/Basic.lean:928` — the
      `(dd - 1) + 1 = dd` step (with `1 ≤ dd` extracted from `hfold` by `cases`).
    - `Nat.lt_or_gt_of_ne` / `Nat.lt_irrefl` / `Nat.ne_of_gt` / `Nat.lt_trans` — core —
      Cor 11.2's trichotomy and the strictness contradictions; `omega` for the depth
      arithmetic tails.
    - `Finset.not_disjoint_iff` — `Mathlib/Data/Finset/Disjoint.lean:69` —
      `¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t` (Cor 11.2's overlap extraction; the
      alternative `Finset.disjoint_left`/`disjoint_iff_ne` at :47/:59 exist too);
      `Finset.inter_comm` / `Finset.mem_inter` — the symmetric application.
    - `Multiset.insert_eq_cons` — `Mathlib/Data/Multiset/ZeroCons.lean:97` (`@[simp]`);
      `Multiset.count_cons_self` / `Multiset.count_eq_zero_of_notMem` (**takes `h`
      explicitly**) / `Multiset.count_pos` / `Multiset.count_add` / `Multiset.count_sum` /
      `Multiset.count_bind` / `Multiset.mem_coe` (Defs.lean:125) / `Multiset.coe_count`
      (Count.lean:127) — the uniqueness count arithmetic. **`Multiset.insert` is the
      `Insert` instance (= `cons`), not a named constant** — write `insert a m`, and
      `rw [Multiset.insert_eq_cons, …]` to make it explicit (probe-verified).
    - **PITFALL (compile-verified in the scratch):** `split <;> try split_ifs <;> simp`
      fails silently — `try` swallows the chained `simp`; use explicit bullets
      (`split; · split_ifs <;> simp; · simp`). `simp [WitnessTree.attachBelow]` + `split`
      + `split_ifs` DOES unfold the mutual defs from outside their file (equation
      lemmas); `unfold WitnessTree.attachInFirst; simp` (reduces the match-on-cons) +
      `split_ifs` + `simp [WitnessTree.attachInFirst]` handles `attachInFirst`.
    - `WitnessTree.rec` — the nested-inductive recursor (motive-2 list pattern, 30.2/30.4's
      form) for the glue inductions; `induction` REJECTS `WitnessTree` (30.3 note).
    - **MISSING? no.** All names above exist and are probe-compiled in
      `/tmp/mt_depth_survey.lean` (exit 0; the pinned statements typecheck with `sorry`
      stubs, and 9 probes cover the unfolding/split/count/disjoint/trichotomy mechanics).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Prove `depth_gt_of_earlier_overlap` + `vbl_disjoint_of_same_depth` on the time-labeled `treeAt vbl Λ t` (plus the comparability input `treeAt_timeInject`), via the fold induction `foldr_depthStrict_timeInject` over `buildBelow` (side conditions: seed times `> l` and `l.Pairwise (· < ·)`, closed by `List.mem_range` + `List.pairwise_lt_range`) with the one-insertion step `attachBelow_depthStrict_step` (30.2 S1 + S2a), the workhorse `attachBelow_old_or_new` (abstract glue in `namespace WitnessTree`, with the `attachInFirst_childrenOf`/`attachInFirst_replaced` minis — 30.2's privates are inaccessible, so `split`/`cases`-reduce the `maxOption` fold inline), and the labels-multiset bridge (`mem_labels_of_labelAt`/`time_gt_of_mem_labels`/`two_le_count_labels_of_two_paths` + 30.2 `labels_attachBelow`) for `attachBelow_newVertex_unique` — whole statement block Survey-compiled at `/tmp/mt_depth_survey.lean` (exit 0, sorry-stubbed) | All statements proved (888 lines, 0 errors / 0 warnings / 0 sorries). Two Proof agents stalled (same pattern as 30.2); the orchestrator completed the last mile: reordered the two private theorems above their users (Lean forward-reference), fixed three positional calls (vbl explicit, Λ inferred), 5 linter cleanups. | Independently verified: tmp 0/0 LSP diagnostics + `lake env lean` exit 0; no sorry/axiom/admit (the two grep hits are header comments). Integrated into `WitnessTree.lean` as `section TreeAtDepth` after `end TreeAtInjective`, tmp's internal ordering kept (WitnessTree-namespace glue → private machinery → public theorems at section end), private kept private; the tmp's `buildBelow` dropped — 30.6's same-file private `buildBelow` reused (identical fold; Lean rejects redeclaring a private name in the same namespace, per the 30.4 precedent); 34 lines >100 chars rewrapped; tmp markers removed; module docstring `## Main results` updated (the three public theorems). Integrated module: 0 diagnostics; `lake build StatsMLlib.Probability.MoserTardos.WitnessTree` OK (1859 jobs). tmp deleted; committed. | `tmp_tree_depth.lean` |

### 30.6. treeAt_injective

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/WitnessTree.lean`
    - note: **30.3 is INTEGRATED** — the tmp imports `WitnessTree` directly (same as 30.5).
      **30.4 and 30.5 are NOT consumed**: the A-count argument needs neither `treeAt_proper`
      nor `treeAt_timeInject`/depth lemmas — the count is a *label-multiset* count
      (`labels` visits each vertex exactly once, `labels_attachBelow` says one insertion adds
      exactly one copy), so vertex distinctness never enters. 30.6 is therefore INDEPENDENT
      of 30.5's completion (parallelizable). Survey compile test 2026-08-16 at
      `/tmp/mt_injective_survey.lean` (`lake env lean` exit 0 — only the expected `sorry`s;
      the ~120 lines of glue are REAL-proved) plus wiring smoke tests at
      `/tmp/test_wiring.lean` (exit 0: the two-case argument, the `lt_or_gt_of_ne` dispatch,
      the `T_injective` Algorithm glue, and the count-formula plug all typecheck against the
      stubs). Est. ~280–320 lines total.
- **informal**
    - statement: |
        Prop 12.1 (survey B C14, notes §12; difficulty Medium; critical path ★), pinned
        (all typecheck at `/tmp/mt_injective_survey.lean`, sorry-stubbed; instances are
        explicit `[DecidableEq ι] [Inhabited ι]` binders, 30.3's style):
        ```lean
        /-- The r-th occurrence A-count: when `Λ t = some a`, the occurring abstract tree
        `forgetTime (treeAt vbl Λ t)` contains exactly one `a`-labeled vertex per
        `a`-occurrence at or before `t`. -/
        theorem treeAt_count_label [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι}
            {t : ℕ} {a : ι} (ht : Λ t = some a) :
            (WitnessTree.labels (forgetTime (treeAt vbl Λ t)) : Multiset ι).count a =
              ((List.range t).filter (fun u => Λ u = some a)).length + 1

        /-- Prop 12.1: distinct genuine times give distinct occurring trees after
        forgetting the time (60.1's injectivity input, abstract-tree level). -/
        theorem treeAt_forgetTime_injective [DecidableEq ι] [Inhabited ι]
            {Λ : ℕ → Option ι} {s t : ℕ} (hne : s ≠ t) (hs : Λ s ≠ none) (ht : Λ t ≠ none) :
            forgetTime (treeAt vbl Λ s) ≠ forgetTime (treeAt vbl Λ t)

        /-- Bonus (trivial): the time-labeled `treeAt` itself is injective — the roots
        carry the times. -/
        theorem treeAt_injective [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {s t : ℕ}
            (hne : s ≠ t) : treeAt vbl Λ s ≠ treeAt vbl Λ t

        /-- Prop 12.1 (60.1's form): distinct stopping-time predecessors give distinct
        occurring (abstract) trees. -/
        theorem T_injective [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {s t : ℕ}
            (hne : s ≠ t) (hs : s < R vbl A pick hpick ω) (ht : t < R vbl A pick hpick ω) :
            T vbl A pick hpick ω s ≠ T vbl A pick hpick ω t
        ```
        All four sit in a `section TreeAtInjective` with 30.3's variable block
        (`{ι} {κ} [DecidableEq κ] {Ω} {N} (vbl) (A) (pick) (hpick)`) and explicit
        `[DecidableEq ι] [Inhabited ι]`. `treeAt_forgetTime_injective` is what 60.1
        consumes (its counting identity is on the abstract trees `T ω t`; the proof's
        counting argument runs on the time-labeled side, transported by `forgetTime`).
        Private machinery (statements compile-tested; the glue is real-proved in the
        survey scratch, the counting lemmas are the tmp's work):
        - `buildBelow Λ l σ` — the reverse-scan fold of `treeAt` with generalized seed
          (defeq to `treeAt`'s fold term; 30.5's tmp has its own copy).
        - root-label glue re-derived from public 30.2 specs (30.3's privates are
          file-scoped, inaccessible): `labelOf_attachBelow` (from `labelAt_attachBelow` at
          `[]`), `labelOf_foldr_treeAt`, `treeAt_root_label' : labelOf (treeAt vbl Λ t) =
          (t, (Λ t).getD default)` (the dummy-inclusive generalization of
          `treeAt_root_label`, for the unconditional `treeAt_injective`).
        - `coe_map_multiset : (l.map f : Multiset β) = (l : Multiset α).map f` (no
          `Multiset.coe_map` in mathlib; 4 lines by list induction).
        - `labels_forgetTime : labels (forgetTime τ) = (labels τ).map (fun p => p.2)` (by
          `WitnessTree.rec` with the list motive + `List.flatMap_map`/`List.map_flatMap`/
          `List.flatMap_congr` — the `size_forgetTime` pattern); multiset form
          `labels_forgetTime_multiset`.
        - `step_count_of_eq {u} (τ) (hA : ∃ p, ∃ hp : ValidPath τ p, (labelAt hp).2 = a)` —
          the `(u, a)`-insertion attaches (the `a`-vertex of `hA` is eligible via
          `treeElig`'s equality disjunct), keeps an `a`-vertex, count `+ 1`; and
          `step_count_of_ne (hi : i ≠ a)` — count unchanged (attach or not: S2a, or
          `labels_attachBelow` + `count_cons_of_ne`).
        - `foldr_count_label {a} (l) (σ)` — the fold invariant: `hA σ → (∃ a-vertex in
          buildBelow Λ l σ) ∧ count a (labels (forgetTime (buildBelow Λ l σ))) =
          count a (labels (forgetTime σ)) + (l.filter (fun u => Λ u = some a)).length`.
        - `length_filter_range_succ_lt`/`length_filter_range_mono`/`length_filter_range_lt
          (hst : s < t) (hΛs : Λ s = some a)` — the r-th-occurrence comparison (pure List
          facts, NO `vbl` argument).
    - proof: |
        (survey B §3.2(iii), the notes' two-case argument — the Option pad does not break
        it: the `t < R`/`Λ t ≠ none` guards make the scan see only genuine entries.)
        **`labels_forgetTime`** — `WitnessTree.rec` with motive-2 `∀ c ∈ cs, …`; root case:
        `simp [forgetTime, WitnessTree.labels]` then
        `rw [List.flatMap_map, List.map_flatMap]` + `List.flatMap_congr` pointwise.
        **`step_count_of_eq`** — the `a`-vertex of `hA` is eligible:
        `deepestEligible ≠ none` by `rw [WitnessTree.deepestEligible_eq_none]; push_neg`
        and `Or.inl hpA.symm` (unfolds `treeElig`'s equality disjunct — no 10.1 citation,
        same pattern as 30.4/30.5); `rcases Option.ne_none_iff_exists.mp` gives
        `⟨d, hd : some d = …⟩` — **note the reversed equality, use `hd.symm`** — then
        `labels_attachBelow hd.symm` (`(labels τ' : Multiset _) = insert (u, a)
        (labels τ : Multiset _)`), `Multiset.insert_eq_cons`, `Multiset.map_cons`,
        `labels_forgetTime_multiset`, `Multiset.count_cons_self`. Existence disjunct:
        `labelAt_attachBelow` on `hA`'s path. **`step_count_of_ne`** — `by_cases
        deepestEligible … = none`: none → `attachBelow_eq_self_of_deepestEligible_none`;
        some → same chain, `Multiset.count_cons_of_ne (Ne.symm hi)`.
        **`foldr_count_label`** — induction on `l` (seed generalized so the IH applies
        after one `foldr` step): `rw [buildBelow, List.foldr_cons]`, cases `Λ u`; `none` →
        `simpa` (tree + filter unchanged — `filter_cons_of_neg`); `some i` → `by_cases
        i = a`, apply the IH `hA` then `step_count_of_eq`/`step_count_of_ne` on
        `buildBelow Λ l σ`, and the filter RHS via `List.filter_cons_of_pos/neg`
        (`simpa [hΛu]` for the `pa : p u = true` argument — `List.filter` is
        Bool-valued); close with `omega`.
        **`treeAt_count_label`** — `unfold treeAt; simp only [ht]` (reduces the seed
        match; a bare `change`/`rw` cannot see through the unreduced match — pitfall
        below) + `change` to `buildBelow vbl Λ (List.range t) (WitnessTree.mk (t, a) [])`;
        `foldr_count_label` with `hA := ⟨[], .root, rfl⟩`; seed tail
        `simp [forgetTime, WitnessTree.labels]` + `omega`.
        **`treeAt_forgetTime_injective_of_lt`** (private, symmetric): `rcases
        Option.ne_none_iff_exists.mp hs/hs with ⟨i, hsi⟩ ⟨j, htj⟩`; `by_cases hij : i = j`:
        - `i ≠ j`: abstract roots differ — `labelOf_forgetTime` + `treeAt_root_label vbl
          hsi.symm` give `labelOf (forgetTime (treeAt vbl Λ s)) = i`, `= j` for `t`;
          `intro heq; exact hij (by rw [← hi', ← hj', heq])`.
        - `i = j` (`subst`): `intro heq`; count congruence `rw [heq]`, then
          `rw [treeAt_count_label vbl hsi.symm, treeAt_count_label vbl htj.symm]` and
          `length_filter_range_lt hst hsi.symm` + `omega` (the `r`-th vs `r'`-th
          occurrence counts differ).
        **`treeAt_forgetTime_injective`** — `Nat.lt_or_gt_of_ne hne`; the `t < s` case by
        `(…_of_lt … ht hs).symm`. **`treeAt_injective`** — `intro h`;
        `rw [treeAt_root_label' vbl Λ s, treeAt_root_label' vbl Λ t]` on the `labelOf`
        congruence; `hne (Prod.ext_iff.mp hl).1`. **`T_injective`** — `unfold T`; `exact
        treeAt_forgetTime_injective vbl hne ((log_ne_none_iff_lt_R vbl A pick hpick
        ω).2 hs) ((log_ne_none_iff_lt_R vbl A pick hpick ω).2 ht)` (the `{t}` of
        `log_ne_none_iff_lt_R` is implicit — do NOT pass it explicitly, infer from the
        expected type).
- **prep**
    - Internal deps (survey B §5, corrected): 30.3 (`treeElig`/`treeAt`/`forgetTime`/`T`
      INTEGRATED + `labelOf_forgetTime`/`treeAt_root_label`; its privates
      `labelOf_attachBelow`/`labelOf_foldr_treeAt` re-derived in-tmp from public 30.2
      specs); 30.2 public spec: `labels_attachBelow` (the insertion multiset identity),
      `attachBelow_eq_self_of_deepestEligible_none` (S2a), `deepestEligible_eq_none` (the
      `≠ none` contrapositive — `attachBelow_spec`/`attachBelow_newVertex`/
      `deepestEligible_eq_some` are NOT consumed); Algorithm: `log_ne_none_iff_lt_R`
      (`T_injective`'s guard lift). **NOT consumed: 30.4, 30.5** (meta note).
    - `Option.ne_none_iff_exists` — `(o ≠ none) ↔ ∃ x, some x = o` — **the `some x = o`
      direction is REVERSED**: the witness satisfies `hd : some d = …`, use `hd.symm`.
    - `Multiset.count_cons_self` / `Multiset.count_cons_of_ne` / `Multiset.map_cons` /
      `Multiset.insert_eq_cons` / `Multiset.coe_count` — the count arithmetic (probe-
      verified). **No `Multiset.coe_map`** — the private `coe_map_multiset` bridge.
    - `List.range_succ` (`range n.succ = range n ++ [n]`) / `List.filter_append` /
      `List.filter_cons_of_pos` (takes `pa : p a = true`) / `List.filter_cons_of_neg` /
      `List.length_append` — the occurrence-count comparison; `List.filter` is
      **Bool-valued** (`simpa using hΛs` for the `pa` arguments).
    - `List.flatMap_map` / `List.map_flatMap` / `List.flatMap_congr` — the
      `labels_forgetTime` rec step (probe-verified; `List.map_congr_left` not needed).
    - `Nat.lt_or_gt_of_ne` / `Nat.succ_le_of_lt` / `Prod.ext_iff` — the WLOG dispatch and
      the time-component extraction; `omega` for the count tails.
    - **PITFALL (compile-verified):** `rw`/`simp` cannot match `labelOf_foldr_treeAt`
      through the UNREDUCED seed `match` of `treeAt` — `change`-reduce the seed first
      (`treeAt_root_label'`'s proof pattern), or `unfold treeAt; simp only [ht]` +
      `change` (`treeAt_count_label`'s plug, wiring-tested).
    - **PITFALL (compile-verified):** `∃ p (hp : T), body` does NOT parse — write
      `∃ p, ∃ hp : T, body` (30.5's form).
    - **MISSING? no.** All names above probe-verified in `/tmp/mt_injective_survey.lean`
      (exit 0); the wiring tests `/tmp/test_wiring.lean` (exit 0) cover the two-case
      argument, the `Ne.symm` dispatch, the `T_injective` glue, and the count plug.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Prove `treeAt_forgetTime_injective` (+ the trivial time-labeled `treeAt_injective`, the 60.1-level `T_injective`, and the r-th-occurrence lemma `treeAt_count_label`) via the A-count argument: the fold invariant `foldr_count_label` (each `(u, a)`-entry attaches — the seed's `a`-vertex stays eligible via `treeElig`'s equality disjunct — and adds exactly one `a`-label by `labels_attachBelow`, `labels_forgetTime`, `count_cons_self/ne`) + the occurrence comparison `length_filter_range_lt`; whole statement block Survey-compiled at `/tmp/mt_injective_survey.lean` (exit 0, sorry-stubbed, ~120 lines glue real-proved) and wiring-tested at `/tmp/test_wiring.lean` | Proved all 4 pinned theorems by filling the sorry-stubbed statements per the two-case plan: private glue real-proved (`buildBelow`, the root-label glue `labelOf_attachBelow`/`labelOf_foldr_treeAt`/`treeAt_root_label'`, `coe_map_multiset`, `labels_forgetTime(_multiset)`, `step_count_of_eq/ne`, `foldr_count_label`) + occurrence comparison `length_filter_range_succ_lt`/`mono`/`lt`; structural fix: moved the private `treeAt_forgetTime_injective_of_lt` helper above its user `treeAt_forgetTime_injective`. tmp: 0 errors 0 warnings, axiom-clean (propext/Classical.choice/Quot.sound only) | Independently verified: tmp `lean_diagnostic_messages` 0/0 and `lake env lean` exit 0; no sorry/axiom/admit; 6 lines >100 chars rewrapped at integration. Integrated into `WitnessTree.lean` as a new `section TreeAtInjective` after `section TreeAt`, block layout kept (private glue private, the four public theorems as pinned, `_of_lt` above its user); the block's re-derivations of `labelOf_attachBelow`/`labelOf_foldr_treeAt` were dropped — Lean rejects redeclaring a private name in the same namespace — and the TreeAt section's private copies (identical statements) are reused instead; tmp-marker and tmp-referencing docstrings cleaned; module docstring `## Main results` updated. Integrated module: 0 diagnostics; `lake build StatsMLlib.Probability.MoserTardos.WitnessTree` succeeds; `#print axioms` on all four: propext/Classical.choice/Quot.sound only. tmp deleted; integrated and committed | `tmp_tree_injective.lean` |

### 30.7. treeAt_isGood, treeAt_size_le

- **meta**
    - kind: lemma
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/WitnessTree.lean`
    - note: **ALL deps INTEGRATED** — the tmp imports `WitnessTree` directly; 30.5's
      `vbl_disjoint_of_same_depth` was integrated before 30.7, so Setup dropped the
      Survey's mirror stub (statement-identical, zero adjustments — the integrated lemma
      is cited as-is in `treeAt_isGood`). **30.6 is NOT consumed** (correcting
      the survey B §5 listing): neither 30.7's statements nor its proofs use the
      injectivity lemmas — the IsGood transport needs only 30.4 (`treeAt_proper`) + 30.5's
      Cor 11.2, the size bound needs 30.2's `size_attachBelow`. **Statements re-pinned at
      Survey (2026-08-16): all UNCONDITIONAL** — no `t < R ω` anywhere: 30.4/30.5 hold for
      every `Λ : ℕ → Option ι` (the dummy root at `Λ t = none` breaks neither properness
      nor same-depth disjointness — it carries the fresh time `t`, so 30.5's
      time-trichotomy argument still applies to it), so the Λ-level statements carry no
      guard and the T-level ones get it for free via `unfold T`. The original informal had
      `IsGood (T … ω t)` *for `t < R ω`* — the guard is dropped (strictly stronger; 40.3's
      `t < R` serves other purposes — log genuineness). `treeAt_isGood` keeps the name on
      the Λ-level abstract form (30.4's pattern); the 40.3 consumer form is `T_isGood`.
      The 30.3 Survey's deferred "reverse path direction" is pinned here as
      `validPath_of_forgetTime` (**classical**: the child witness is `Classical.choose` —
      `ValidPath` is Type-valued and `Exists.casesOn` can only eliminate into Prop,
      compile-verified).
- **informal**
    - statement: |
        Occurring trees are good and small (survey B C15; difficulty Easy–Med, est. ~60
        lines). **The whole block below is compile-tested 2026-08-16 at
        `/tmp/mt_tree_good_survey.lean` (`lake env lean` exit 0; REAL proofs for everything
        except the 30.5 mirror stub — the only diagnostic is its expected `sorry`).** The
        mirror is a `section TreeAtDepthMirror` with 30.3's variable block copying 30.5's
        pinned `vbl_disjoint_of_same_depth` statement as a `sorry`; the 30.7 block itself
        sits in a new `section TreeAtGood` with 30.3's variable block
        (`{ι} {κ} [DecidableEq κ] {Ω} {N} (vbl) (A) (pick) (hpick)`) and explicit
        `[DecidableEq ι] [Inhabited ι]` binders on the treeAt/T-level theorems (30.5/30.6's
        style):
        ```lean
        /-- The reverse of 30.3's `forgetTime_getElem?`: an abstract child of the
        `forgetTime` image comes from a time-labeled child. -/
        theorem forgetTime_getElem?_of {τ : WitnessTree (ℕ × ι)} {i : ℕ} {c' : WitnessTree ι}
            (hc' : (forgetTime τ).childrenOf[i]? = some c') :
            ∃ c : WitnessTree (ℕ × ι), τ.childrenOf[i]? = some c ∧ forgetTime c = c' := by
          rw [childrenOf_forgetTime, List.getElem?_map, Option.map_eq_some_iff] at hc'
          exact hc'

        /-- A valid path in the `forgetTime` image lifts to a valid path in the time-labeled
        tree (the same child-index list). Match the PATH first (30.1's pattern). The child
        witness is `Classical.choose` INLINED (no wrapper def — a wrapper breaks defeq at
        the instances transparency, compile-verified); the recursive call receives the cast
        of `hvp` along `forgetTime c = c'` (explicit `cast (congrArg …)` — the `▸` notation
        fails to compute the motive in this position, compile-verified). -/
        noncomputable def validPath_of_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
            (hp : WitnessTree.ValidPath (forgetTime τ) p) : WitnessTree.ValidPath τ p :=
          match p with
          | [] => .root
          | i :: p' =>
              match hp with
              | .cons i _ hc' hvp =>
                  .cons i (Classical.choose (forgetTime_getElem?_of hc'))
                    (Classical.choose_spec (forgetTime_getElem?_of hc')).1
                    (validPath_of_forgetTime
                      (cast (congrArg (fun x => WitnessTree.ValidPath x p')
                        (Classical.choose_spec (forgetTime_getElem?_of hc')).2.symm) hvp))

        /-- Labels survive casts of the tree along an equality. Stated in the
        `cast (congrArg …)` form to match the lift's inner cast exactly (the `▸` form is
        not defeq — different motives). -/
        theorem labelAt_cast {τ τ' : WitnessTree ι} (h : τ = τ') {p : List ℕ}
            (hp : WitnessTree.ValidPath τ p) :
            WitnessTree.labelAt
                (cast (congrArg (fun x => WitnessTree.ValidPath x p) h) hp) =
              WitnessTree.labelAt hp := by
          subst h
          rfl

        /-- The lifted path carries the same label — the single transport lemma 30.7's
        `IsGood` proof consumes. -/
        theorem labelAt_of_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
            (hp : WitnessTree.ValidPath (forgetTime τ) p) :
            (WitnessTree.labelAt (validPath_of_forgetTime hp)).2 = WitnessTree.labelAt hp

        /-- **30.7 headline** (abstract, unconditional): the witness tree built from the log
        prefix is good — Prop 10.1 (30.4) + Cor 11.2 (30.5) transported through the path
        lift. -/
        theorem treeAt_isGood [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
            WitnessTree.IsGood vbl (forgetTime (treeAt vbl Λ t))

        /-- **The 40.3 form**: the occurring tree `T … ω t` is good. -/
        theorem T_isGood [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ} :
            WitnessTree.IsGood vbl (T vbl A pick hpick ω t)

        /-- The reverse-scan fold grows the size by at most the length of the scanned
        list (private). -/
        private theorem foldr_size_le [DecidableEq ι] {Λ : ℕ → Option ι} :
            ∀ l : List ℕ, ∀ τ : WitnessTree (ℕ × ι),
              WitnessTree.size (l.foldr (fun s τ => match Λ s with
                | none => τ
                | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) τ) ≤
                WitnessTree.size τ + l.length

        /-- **30.7 headline** (size): each reverse-scan step adds at most one vertex, the
        seed is a single root — `size (treeAt vbl Λ t) ≤ t + 1`. -/
        theorem treeAt_size_le [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
            WitnessTree.size (treeAt vbl Λ t) ≤ t + 1

        /-- The occurring tree `T … ω t` has at most `t + 1` vertices. -/
        theorem T_size_le [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ} :
            WitnessTree.size (T vbl A pick hpick ω t) ≤ t + 1

        /-- 40.3's `size τ ≤ N` input: for `t < R ω` the occurring tree fits the table
        (`t < R ≤ N` via 20.3's `R_le`). -/
        theorem T_size_le_N [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ}
            (ht : t < R vbl A pick hpick ω) :
            WitnessTree.size (T vbl A pick hpick ω t) ≤ N
        ```
        Design decisions (pinned): (i) the transport trio plus `labelAt_cast` carry no
        instance binders (they use no section variables — the section's `{ι}` is
        auto-included, the rest is not); (ii) `treeAt_size_le` is stated on the PAIR tree
        `treeAt vbl Λ t` (the natural fold-induction target), the abstract form being one
        `size_forgetTime` away; (iii) `foldr_size_le` keeps 30.4's private-fold style
        (`{Λ}` implicit, `∀ l, ∀ τ` body, seed generalized); (iv) the `T_size_le_N` glue
        is included here because 40.2's `check_probability` consumes exactly
        `size (T … ω t) ≤ N` with `ht : t < R ω` — the `R_le` citation is 30.7's only
        touch of 20.3.
    - proof: |
        (All routes REAL-proved in the scratch — the compile log above is the
        verification.)
        **`forgetTime_getElem?_of`** — one rw chain at `hc'`
        (`childrenOf_forgetTime`, `List.getElem?_map`, `Option.map_eq_some_iff`) +
        `exact hc'`.
        **`validPath_of_forgetTime`** — the pinned body; `match p` first (30.1's pattern,
        and the 30.3 forward def's shape).
        **`labelAt_cast`** — `subst h; rfl`.
        **`labelAt_of_forgetTime`** — `induction p generalizing τ` (**NOT** `induction
        hp`: the hp-induction IH is tied to the abstract child `c'` and cannot be
        instantiated at the preimage `Classical.choose …`). nil:
        `cases hp with | root => simp [validPath_of_forgetTime, labelOf_forgetTime]`;
        cons: `cases hp with | cons i _ hc' hvp => rw [validPath_of_forgetTime,
        WitnessTree.labelAt_cons, WitnessTree.labelAt_cons]` (**rw the def's equation
        lemmas, NOT `unfold`** — unfold exposes a stuck pair-match on `(i, hp)`), then
        `have hih := ih (τ := Classical.choose (forgetTime_getElem?_of hc')) (cast
        (congrArg (fun x => WitnessTree.ValidPath x p') (Classical.choose_spec
        (forgetTime_getElem?_of hc')).2.symm) hvp)`, `have hl := labelAt_cast
        (Classical.choose_spec (forgetTime_getElem?_of hc')).2.symm hvp`,
        `simpa [← hl] using hih` (simpa does NOT fire `labelAt_cast` from the simp set on
        the ih's conclusion — bind it as `hl` and rewrite explicitly, compile-verified).
        **`treeAt_isGood`** — `refine ⟨treeAt_proper vbl, ?_⟩; intro p q hp hq hne hd`;
        lift both paths (`validPath_of_forgetTime`), apply the mirror
        `vbl_disjoint_of_same_depth vbl (lift hp) (lift hq) hne hd` (the depth hypothesis
        transfers by defeq — `depth`'s tree argument is erased; `p ≠ q` is the same
        list inequality), then `rw [← labelAt_of_forgetTime hp,
        ← labelAt_of_forgetTime hq]` and close. **`T_isGood`** —
        `unfold T; exact treeAt_isGood vbl`.
        **`foldr_size_le`** — list induction, seed generalized; nil `simp`; cons:
        `rw [List.foldr_cons]` + `cases h : Λ s` — **note the fold-step order**: the cons
        step wraps the new entry OUTSIDE the accumulated fold (the goal is
        `size (attachBelow … (l.foldr f τ)) ≤ …`), so the `some i` branch applies
        `size_attachBelow` to the seed `l.foldr f τ` plus `ih τ`, then `omega`; the
        `none` branch is `ih τ` + `omega`. `cases h : Λ s` auto-reduces the goal's match
        (a following `simp` must NOT list `h` — unusedSimpArgs linter, compile-verified).
        **`treeAt_size_le`** — `unfold treeAt; refine Nat.le_trans (foldr_size_le vbl
        (List.range t) (match Λ t with | none => WitnessTree.mk (t, default) [] |
        some i => WitnessTree.mk (t, i) [])) ?_` (**Λ is implicit — do NOT pass it**),
        then `cases h : Λ t <;> simp [WitnessTree.size_mk, List.length_range] <;> omega`
        (the `<;> omega` closes BOTH branches — a bare `omega` leaves the second branch
        unsolved, compile-verified; the seed sizes reduce to `1` via `size_mk`).
        **`T_size_le`** — `unfold T; simpa [size_forgetTime] using treeAt_size_le vbl`.
        **`T_size_le_N`** — `refine Nat.le_trans (T_size_le vbl A pick hpick) ?_; exact
        Nat.le_trans (Nat.succ_le_of_lt ht) (R_le vbl A pick hpick ω)`.
- **prep**
    - `Option.map_eq_some_iff` — core `Init/Data/Option/Lemmas.lean:291` — the
      child-witness extraction in `forgetTime_getElem?_of` (the rw turns the `some c'`
      equality into the `∃ c`).
    - `List.getElem?_map` — core `Init/Data/List/Lemmas` — `(l.map f)[i]? =
      Option.map f l[i]?` (30.3 prep).
    - `Classical.choose` / `Classical.choose_spec` — core — the lift's child witness.
      **PITFALL (compile-verified):** `Exists.casesOn` can only eliminate into `Prop` —
      the Type-valued lift cannot case the `∃`; `by classical; rcases`/`Classical.choose`
      is mandatory (the 30.3 Survey's "∃-data, classical" flag confirmed).
    - `cast` / `congrArg` — core — the explicit preimage cast. **PITFALL
      (compile-verified):** the `▸` notation fails to compute the motive in the def's
      cons arm — write `cast (congrArg (fun x => WitnessTree.ValidPath x p') h) hvp`.
    - `Nat.succ_le_of_lt` — core — `T_size_le_N`'s `t + 1 ≤ R` step.
    - `List.length_range` — core, `@[simp]` — the seed bound `(List.range t).length = t`.
    - `omega` — the arithmetic tails of the fold and the seed bound.
    - Internal deps (survey B §5, corrected): 30.3 (INTEGRATED: `treeElig`/`treeAt`/
      `forgetTime`/`T` + `forgetTime_getElem?`/`validPath_forgetTime`/`labelAt_forgetTime`/
      `size_forgetTime`/`labelOf_forgetTime`/`childrenOf_forgetTime`), 30.4
      (`treeAt_proper`), 30.2 (`size_attachBelow` — the fold step), 30.5 (mirror:
      `vbl_disjoint_of_same_depth` ONLY — Lemma 11.1/`treeAt_timeInject` stay internal to
      30.5), 20.3 (`R_le`), 20.4 (`log`, via `T`'s body). **NOT consumed: 30.6**
      (survey B §5 listing corrected — see meta note), 10.1 (Γ⁺ not touched).
    - (REMOVED from the original prep) `List.length_le_sum_of_one_le` —
      `Mathlib/Algebra/BigOperators/Group/List/Basic.lean:518` (exists in v4.32.0,
      signature `(L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum`): NOT consumed by
      the pinned route — the size bound goes through 30.2's `size_attachBelow` + the fold
      induction; the `length_le_sum` machinery was survey A §3.2's 50.2-style alternative
      (still listed in 50.2's prep, where it belongs).
    - **PITFALLS (all compile-verified in the scratch):** (i) `WitnessTree.size_forgetTime`
      does NOT exist — `size_forgetTime` lives at top level `MoserTardos` (30.3's
      `section TreeAt`, outside `namespace WitnessTree`); (ii) a wrapper def around
      `Classical.choose` (e.g. a `forgetTime_preimage`) breaks defeq at the instances
      transparency in the lift's elaboration — inline the choose; (iii) rw the def via its
      equation lemmas, never `unfold` it in proofs; (iv) in `labelAt_of_forgetTime` bind
      the cast lemma as `have hl` + `simpa [← hl]`.
    - Placement: new `section TreeAtGood` in `WitnessTree.lean` after 30.6's section
      (integration order: 30.5 first — the mirror stub is dropped at integration), same
      variable block as 30.3, no `omit`s (compile-verified — the section's variables are
      all used by some declaration, 30.4's pattern). At Review's option the transport
      trio (`forgetTime_getElem?_of`/`validPath_of_forgetTime`/`labelAt_cast`/
      `labelAt_of_forgetTime`) may instead go inside 30.3's `section TreeAt` next to the
      forward API (thematically it completes 30.3's transport block); the treeAt/T-level
      theorems stay in `section TreeAtGood`. Module docstring additions at integration
      (Review).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Prove `treeAt_isGood` (unconditional Λ-level headline + the 40.3 form `T_isGood` — no `t < R` guard: 30.4/30.5 hold for every `Λ`, the dummy root breaks neither) + `treeAt_size_le`/`T_size_le`/`T_size_le_N` (fold induction over the reverse scan with 30.2's `size_attachBelow`) + the reverse path transport (`forgetTime_getElem?_of`, classical `validPath_of_forgetTime` with inlined choose and explicit `cast (congrArg …)`, `labelAt_cast`, `labelAt_of_forgetTime`) — the whole block Survey-compiled at `/tmp/mt_tree_good_survey.lean` (exit 0; the only sorry is the mirrored 30.5 statement) | pre-proven by Survey; Setup swapped the 30.5 mirror for the integrated lemma (statement-identical, zero adjustments); Proof phase skipped | Independently verified: tmp `lean_diagnostic_messages` 0/0 and `lake env lean` exit 0; no sorry/axiom/admit; no lines > 100 (175 total). Integrated into `WitnessTree.lean` as `section TreeAtGood` after `section TreeAtDepth` in the tmp's layout (transport trio in-section, `foldr_size_le` kept private); module docstring `## Main results` updated (`treeAt_isGood`/`T_isGood`/`treeAt_size_le`/`T_size_le`/`T_size_le_N`). Integrated module: 0 diagnostics; `lake build StatsMLlib.Probability.MoserTardos.WitnessTree` succeeds (1859 jobs). tmp deleted; integrated and committed | `tmp_tree_good.lean` |

---
## 40. Coupling (Core Lemmas)

### 40.1. treeProfile, check, profile inequality

- **meta**
    - kind: def
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Coupling.lean`
- **informal**
    - statement: |
        The structural τ-check (survey B D16, notes §14; difficulty Medium, est. ~120
        lines; survey B risk 2 — the index bookkeeping lives here). No sequential process,
        no vertex index type. **The whole block is Survey-compiled 2026-08-16 at
        `/tmp/mt_profile_survey.lean` (`lake env lean` exit 0; the defs and the two bound
        lemmas are REAL, the four inequality lemmas are sorry-stubbed) — imports
        `StatsMLlib.Probability.MoserTardos.WitnessTree` only (ΩN/DeterminedBy come
        transitively).** Everything sits in a new file `Coupling.lean`,
        `namespace MoserTardos`, `section TreeProfile` with the variable block
        `{ι : Type u} {κ : Type v} [DecidableEq κ] {Ω : κ → Type w} {N : ℕ}
        (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j))
        (hdet : ∀ i, DeterminedBy (A i) (vbl i))` — no `omit`s (compile-verified: every
        section variable is used by some declaration; the auto-inclusion is per-use, see
        pitfalls). Pinned signatures (`#check`-verified on the compiled scratch):
        ```lean
        def treeProfile {ι} {κ} [DecidableEq κ] (vbl : ι → Finset κ) :
            WitnessTree ι → κ → ℕ → ℕ
          | WitnessTree.mk a cs, j, 0 =>
              (if j ∈ vbl a then 1 else 0) + (cs.map (fun c => treeProfile vbl c j 0)).sum
          | WitnessTree.mk _ cs, j, d + 1 =>
              (cs.map (fun c => treeProfile vbl c j d)).sum

        def treeProfileAtDepth {ι} {κ} [DecidableEq κ] (vbl : ι → Finset κ) :
            WitnessTree ι → κ → ℕ → ℕ
          | WitnessTree.mk a _, j, 0 => if j ∈ vbl a then 1 else 0
          | WitnessTree.mk _ cs, j, d + 1 =>
              (cs.map (fun c => treeProfileAtDepth vbl c j d)).sum

        theorem treeProfile_le_size (τ : WitnessTree ι) (j : κ) (d : ℕ) :
            treeProfile vbl τ j d ≤ WitnessTree.size τ

        theorem treeProfile_lt_succ_of_size_le {τ : WitnessTree ι}
            (hN : WitnessTree.size τ ≤ N) {j : κ} {d : ℕ} :
            treeProfile vbl τ j (d + 1) < N + 1

        noncomputable def checkAux (whole : WitnessTree ι) (hN : WitnessTree.size whole ≤ N) :
            WitnessTree ι → ℕ → ΩN N Ω → Prop
          | WitnessTree.mk a cs, d, ω =>
              Classical.choose (hdet a)
                  (fun j => ω ⟨j, ⟨treeProfile vbl whole ↑j (d + 1),
                    treeProfile_lt_succ_of_size_le vbl hN⟩⟩) ∧
                ∀ c ∈ cs, checkAux whole hN c (d + 1) ω

        noncomputable def check {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N)
            (ω : ΩN N Ω) : Prop :=
          checkAux vbl A hdet τ hN τ 0 ω

        theorem treeProfile_add_succ (τ : WitnessTree ι) (j : κ) (d : ℕ) :
            treeProfile vbl τ j d =
              treeProfileAtDepth vbl τ j d + treeProfile vbl τ j (d + 1)

        theorem one_le_treeProfileAtDepth_of_mem {τ : WitnessTree ι} {p : List ℕ}
            (hp : WitnessTree.ValidPath τ p) {j : κ}
            (hj : j ∈ vbl (WitnessTree.labelAt hp)) :
            1 ≤ treeProfileAtDepth vbl τ j (WitnessTree.depth τ p)

        theorem treeProfile_le_of_le (τ : WitnessTree ι) (j : κ) {d d' : ℕ} (h : d ≤ d') :
            treeProfile vbl τ j d' ≤ treeProfile vbl τ j d

        theorem treeProfile_gt_of_depth_lt {τ : WitnessTree ι} {p q : List ℕ}
            (hq : WitnessTree.ValidPath τ q)
            (hdp : WitnessTree.depth τ p < WitnessTree.depth τ q) {j : κ}
            (hjq : j ∈ vbl (WitnessTree.labelAt hq)) :
            treeProfile vbl τ j (WitnessTree.depth τ q + 1) <
              treeProfile vbl τ j (WitnessTree.depth τ p + 1)
        ```
        (Lifted signatures: `treeProfile`/`treeProfileAtDepth` get the auto-included
        `{ι} {κ} [DecidableEq κ] (vbl)`; `checkAux`/`check` get `(vbl) (A) (hdet)` prepended
        — use site `check vbl A hdet hN ω`.)
        **Design decisions (pinned):**
        (i) `treeProfile`'s exact recursion: the `d = 0` / `d + 1` ℕ-pattern (NOT the
        `if d = 0 … else … (d - 1)` form — two equation lemmas instead of a dite; at
        `d = 0` the children enter at threshold `0` since every child vertex has depth
        ≥ 1 ≥ 0, at `d + 1` they enter at `d`, exactly `1 + depth-in-child ≥ d + 1 ⟺
        depth-in-child ≥ d`). Computable — the dites use `[DecidableEq κ]` via
        `Finset.decidableMem`, no `classical`.
        (ii) `check` carries the bound **`(hN : size τ ≤ N)` explicitly** — the Fin row
        index `⟨treeProfile vbl whole ↑j (d + 1), treeProfile_lt_succ_of_size_le hN⟩`
        needs it, and it cannot be conjured inside the def. Consumers provide it: 40.2's
        `check_probability` carries its own `size τ ≤ N` hypothesis (survey B D17), 40.3
        gets `size (T …) ≤ N` from 30.7's `T_size_le_N` (with `t < R`). This matches
        survey B's "the `|V τ| ≤ N` bound makes every `profile j (d+1) < N+1`".
        (iii) `checkAux` threads `(whole, hN)` unchanged through the recursion with a depth
        parameter — the profile of the WHOLE tree is read at every vertex (survey B's
        "threaded down unchanged"); the root of `cur` is checked at depth `d` on rows
        `treeProfile vbl whole j (d + 1)` for `j ∈ vbl (labelOf cur)`.
        (iv) `check` takes `(hdet : ∀ i, DeterminedBy (A i) (vbl i))` and picks the witness
        **per vertex** via `Classical.choose (hdet a)` (survey B §4.6: the coupling section
        picks witnesses once via `Classical.choose`, `noncomputable`) — 40.3's proof
        connects the check to the algorithm's `Classical.choose_spec (hdet a) σ` by defeq.
        No completion of coordinates outside `vbl`, no `Nonempty (Ω j)`.
        **Profile inequality (entry injectivity, deeper case) — survey B's chain has a
        typo, CORRECTED here:** the literal survey B/blueprint chain
        `profile j (d(v)+1) ≥ profile j (d(v')) + 1` is FALSE (counterexample: a root and
        one child sharing `j` — `profile j 1 = 1 ≱ 1 + 1`). The true chain decomposes at
        the DEEPER vertex's own depth:
        `treeProfile j (d(v)+1) ≥ treeProfile j (d(v')) ≥ treeProfile j (d(v')+1) + 1 >
        treeProfile j (d(v')+1)` — the first `≥` is antitone in the threshold
        (`d(v)+1 ≤ d(v')`), the `+ 1` is the deeper vertex `v'` itself (`depth = d(v')`,
        `j ∈ vbl`, so it is counted at threshold `d(v')` but not `d(v')+1`). The headline
        lemma states the end-to-end strict form `treeProfile_gt_of_depth_lt` above, which
        is exactly what 40.2 consumes for `profile j (d(v)+1) ≠ profile j (d(v')+1)`.
        **No `IsGood` hypothesis** (strengthening over the item text — the counting
        argument is universal; 40.2 uses `IsGood` only for the same-depth case via its own
        second conjunct). Also minimal: the shallow vertex's `ValidPath`/`vbl` membership
        are NOT needed — only `hq`, `hdp`, `hjq` (the deeper vertex's own path and
        membership; `p` enters only through `depth τ p`).
    - proof: |
        Recursive definitions (compiled); the inequality lemmas are the `Nat` counting
        argument. **`treeProfile_le_size`** (REAL-proved in the scratch): `WitnessTree.rec`
        with motive-1 `fun τ => ∀ d, treeProfile vbl τ j d ≤ size τ` and motive-2
        `fun cs => ∀ c ∈ cs, ∀ d, …` (**`induction τ` is REJECTED on the nested inductive**
        — 30.2/30.4's recursor form), `?_ ?_ ?_ τ d`; mk-case `cases d` + `List.sum_le_sum`
        (per-child IH `ih c hc d`) + `simp [treeProfile, WitnessTree.size_mk]` +
        `split_ifs with h <;> omega` (both branches, `hs` in context); nil-case `cases hc`
        (empty membership); cons-case `rw [List.mem_cons] at hc'` + `rcases rfl | hc'` +
        `exact ihc` / `exact ihcs c' hc'`.
        **`treeProfile_lt_succ_of_size_le`** (REAL-proved): one line —
        `exact Nat.lt_of_le_of_lt (Nat.le_trans (treeProfile_le_size vbl τ j (d + 1)) hN)
        (Nat.lt_succ_self N)`.
        **`treeProfile_add_succ`**: `WitnessTree.rec` (same motive-2 form); zero case
        `simp [treeProfile, treeProfileAtDepth]` (both sides reduce to the same term —
        the child threshold `0 + 1 - 1` computes to `0`); succ case `simp [treeProfile,
        treeProfileAtDepth, hmap]` with `hmap` the pointwise rewrite
        `congrArg List.sum (List.map_congr_left (by intro c hc; exact ih c hc d))`, then
        `rw [List.sum_map_add]` closes the split of the `f + g` sum.
        **`one_le_treeProfileAtDepth_of_mem`**: `induction p generalizing τ` (paths are
        plain Lists — list induction is fine); nil: `cases hp` (root) + `cases τ` +
        `simp [treeProfileAtDepth, WitnessTree.depth, hj]` (the `if` fires on `hj`,
        leaving `1 ≤ 1`); cons: `cases hp` (cons i c hc hvp) + `cases τ` — the goal after
        `depth_cons` is the d+1-equation sum; `have hmem : c ∈ τ.childrenOf :=
        List.mem_of_getElem? hc`, the c-summand membership via `List.mem_map.mpr ⟨c,
        hmem, rfl⟩`, then `exact le_trans ih (List.le_sum_of_mem …)` (IH's depth
        `depth c p'` is defeq `depth τ p'`).
        **`treeProfile_le_of_le`**: `Nat.le_induction` on `h` (motive
        `fun m _ => treeProfile vbl τ j m ≤ treeProfile vbl τ j d`); base refl; succ step
        `treeProfile vbl τ j (m + 1) ≤ treeProfile vbl τ j m` from
        `rw [treeProfile_add_succ]; omega`, then `le_trans` with the IH.
        **`treeProfile_gt_of_depth_lt`** (the headline): three ingredients + `omega` —
        `hle := treeProfile_le_of_le vbl τ j (Nat.succ_le_of_lt hdp)` (the `≥` across
        thresholds), `hsplit := treeProfile_add_succ vbl τ j (WitnessTree.depth τ q)` (the
        exact-depth decomposition at the deeper vertex), `hone :=
        one_le_treeProfileAtDepth_of_mem vbl hq hjq` (the deeper vertex contributes at its
        own depth); `omega` closes with `hle`, `hsplit`, `hone`.
- **prep**
    - `List.sum_le_sum` — `Mathlib/Algebra/Order/BigOperators/Group/List.lean` (probe-
      verified): `{ι} {M} [AddMonoid M] [Preorder M] [AddRightMono M] [AddLeftMono M]
      {l} {f g : ι → M} (h : ∀ i ∈ l, f i ≤ g i) : (l.map f).sum ≤ (l.map g).sum` —
      the child-sum step of `treeProfile_le_size`.
    - `List.le_sum_of_mem` — same file (probe-verified): `[AddMonoid M] [Preorder M]
      [CanonicallyOrderedAdd M] {xs : List M} {x : M} (h₁ : x ∈ xs) : x ≤ xs.sum` — the
      cons case of `one_le_treeProfileAtDepth_of_mem` (ℕ is canonically ordered).
    - `List.sum_map_add` — `Mathlib/Algebra/BigOperators/Group/List/Lemmas.lean`
      (probe-verified): `[AddCommMonoid M] {l : List ι} {f g : ι → M} :
      (l.map (fun i => f i + g i)).sum = (l.map f).sum + (l.map g).sum` — the succ case
      of `treeProfile_add_succ`.
    - `List.map_congr_left` — core (probe-verified): `{l} {f g}
      (h : ∀ a ∈ l, f a = g a) : List.map f l = List.map g l` — the pointwise IH rewrite
      in `treeProfile_add_succ`. **`List.map_congr` does NOT exist in v4.32.0**
      (probe: unknown constant), and neither does `List.sum_congr`.
    - `List.mem_of_getElem?` — core (probe-verified): `{l} {i} {a}
      (e : l[i]? = some a) : a ∈ l` — the `c ∈ τ.childrenOf` extraction from `hc` in
      `one_le_treeProfileAtDepth_of_mem`'s cons case. **`List.getElem?_mem` does NOT
      exist** (probe: unknown constant). `List.mem_map` / `List.mem_iff_getElem?` — core.
    - `Nat.le_induction` — core (probe-verified): `{m} {P : (n : ℕ) → m ≤ n → Prop}
      (base : P m …) (succ : ∀ n hmn, P n hmn → P (n + 1) …) : ∀ n hmn, P n hmn` —
      `treeProfile_le_of_le`'s induction over the threshold gap.
    - `Nat.lt_of_le_of_lt` / `Nat.lt_succ_self` / `Nat.succ_le_of_lt` /
      `Nat.add_le_add_right` / `Nat.add_le_add_left` / `le_trans` — core (probe-verified)
      — the Fin row certificate `treeProfile_lt_succ_of_size_le` and the headline's glue.
    - `Finset.decidableMem` — `Mathlib/Data/Finset/Defs.lean:117`: `[DecidableEq α]
      (a : α) (s : Finset α) : Decidable (a ∈ s)` — the dites in
      `treeProfile`/`treeProfileAtDepth` (computable — no `classical`; the section carries
      `[DecidableEq κ]`).
    - `WitnessTree.rec` — the nested-inductive recursor (motive-1/motive-2 list pattern,
      30.2/30.4's form; **`induction` REJECTS `WitnessTree`** — compile-verified again
      here: "nested inductive type") — `treeProfile_le_size` and
      `treeProfile_add_succ`'s inductions.
    - `Classical.choose` — core — `checkAux`'s per-vertex `DeterminedBy` witness
      (`Classical.choose_spec` is 40.3's hook).
    - `SetLike.instCoeSortType` — the `Π j : vbl a, Ω j` domain elaboration (10.2 prep;
      the lambda binder `fun j => ω ⟨j, ⟨…⟩⟩` coerces `j` to `κ` — the 10.2/20.1
      `assign` pattern, compile-verified in the scratch).
    - `omega` — the `Nat` tails.
    - Internal deps (survey B §5, corrected): items 30.1 (`WitnessTree` + `ValidPath`/
      `labelAt`/`depth`/`size` + the round-trip simp lemmas), 10.2 (`DeterminedBy`),
      10.3 (`ΩN` — the table type). **NOT 30.5/30.7**: the strict inequality is on
      abstract trees and needs no occurring-tree machinery (30.7's `T_size_le_N` is first
      consumed by 40.3, as the `hN` input of `check`).
    - **PITFALLS (compile-verified in the scratch):** (i) inside `checkAux`'s own body the
      recursive calls pass ONLY the header args (`checkAux whole hN c (d + 1) ω`) — the
      auto-included section variables are not yet part of the constant being defined; but
      at outer call sites they come FIRST: `check`'s body must be
      `checkAux vbl A hdet τ hN τ 0 ω` (`checkAux τ …` fails with "application type
      mismatch"). (ii) `d = 0`/`d + 1` pattern recursion generates TWO equation lemmas —
      simp unfolds them on constructor arguments (`simp [treeProfile, …]`). (iii) the
      `d + 1`-clause of `treeProfileAtDepth` must bind `_` for the unused root label
      (linter.unusedVariables).
    - Placement: new file `Coupling.lean` (Setup creates the skeleton — Apache header,
      `/-!` module docstring, imports `StatsMLlib.Probability.MoserTardos.WitnessTree`;
      `namespace MoserTardos`), first section `TreeProfile` with the variable block above.
      Module docstring additions at integration (Review).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `treeProfile`/`treeProfileAtDepth` (d-pattern recursion), the Fin-row-certified `checkAux`/`check` (per-vertex `Classical.choose (hdet a)`, whole-tree profile threaded down, explicit `hN : size τ ≤ N`), prove the bound lemmas `treeProfile_le_size`/`treeProfile_lt_succ_of_size_le` and the profile inequality (`treeProfile_add_succ`, `one_le_treeProfileAtDepth_of_mem`, `treeProfile_le_of_le`, headline `treeProfile_gt_of_depth_lt` — no `IsGood` needed, survey B's chain typo corrected) — whole block Survey-compiled at `/tmp/mt_profile_survey.lean` (exit 0; defs + 2 bound lemmas real, 4 inequality lemmas sorry-stubbed) | all four stubs REAL-proved per the plan, with 3 small deviations: explicit `have ha : j ∈ vbl a` for the root label in `one_le_treeProfileAtDepth_of_mem`'s nil case (`simp` fired on `ha` instead of the raw `hj`); defeq close in the cons case (dedicated `ih'` on `p'.length` + `le_trans ih' hsum` instead of the plan's direct `le_trans ih (List.le_sum_of_mem …)`); `refine Nat.le_induction (P := fun m _ => …)` for the explicit motive in `treeProfile_le_of_le`. tmp: 196 lines, all ≤ 100 chars, no sorry/axiom/admit | Independently verified: tmp `lean_diagnostic_messages` 0 errors 0 warnings (5 info `#check`s) and `lake env lean` exit 0. Integrated into the new module `Coupling.lean` (created — the 40.x home; Apache header + `/-!` docstring with `## Main definitions`/`## Main results`/`## References`; imports `WitnessTree` only) as `section TreeProfile` in the tmp's layout; dropped the 5 `#check` lines and the tmp-marker header; no lines > 100 (220 total). Integrated module: 0 diagnostics; `lake env lean` exit 0; `lake build StatsMLlib.Probability.MoserTardos.Coupling` succeeds (1860 jobs). tmp deleted; integrated and committed | `tmp_tree_profile.lean` |

### 40.2. check_probability

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 2 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Coupling.lean`
- **informal**
    - statement: |
        The τ-check measure factorization (survey B D17, notes §14 (14.2)+(c); difficulty
        **Hard**, est. ~200 lines; critical path ★; survey B risk 3). **Pinned at Survey
        2026-08-16 — the entire glue block below is REAL-proved at
        `/tmp/mt_survey_402.lean` (`lake env lean` exit 0, 251 lines; the only sorries are
        the two 40.1 mirror stubs and `check_probability` itself):**
        ```lean
        /-- The structural τ-product: the event probability at the root times the products
        over the children. -/
        noncomputable def treeProd : WitnessTree ι → ℝ≥0∞
          | WitnessTree.mk a cs => μπ μ (A a) * (cs.map (fun c => treeProd c)).prod

        /-- **40.2 headline**: the measure of the τ-check equals the product of the event
        probabilities. -/
        theorem check_probability {τ : WitnessTree ι} (hA : ∀ i, MeasurableSet (A i))
            (hgood : WitnessTree.IsGood vbl τ) (hN : WitnessTree.size τ ≤ N) :
            μN N μ {ω | check vbl A hdet hN ω} = treeProd (μ := μ) A τ
        ```
        `treeProd` is defined HERE (no earlier 40.x item pins it). Use site
        `treeProd (μ := μ) A τ` — μ is an implicit auto-bound section variable, `A`
        explicit (the def's body uses μ first, so the auto-include order is `{κ} {Ω} {μ}
        (A)`); inside `treeProd`'s own body the recursive calls pass ONLY the header arg
        (`treeProd c` — the auto-included section variables are not part of the constant
        being defined, 40.1's checkAux pitfall). `hA` is an explicit binder (the body needs
        it for the witness-set measurability; 40.1's section has no hA, 60.2 carries it).
        **Section requirements (compile-verified):** beyond 40.1's `section TreeProfile`
        block (`{ι} {κ} [DecidableEq κ] {Ω} {N} (vbl) (A) (hdet)`) the 40.2 block needs
        `[Fintype κ]` (μN/μπ elaborate `Measure.pi`), `{μ : ∀ j, Measure (Ω j)}` +
        `[∀ j, IsProbabilityMeasure (μ j)]`, `open scoped ENNReal` (the `ℝ≥0∞` notation is
        `scoped[ENNReal]`, `Mathlib/Data/ENNReal/Basic.lean:104` — without it `ℝ≥0∞` is a
        parse error), and `open ProbabilityTheory` (`iIndepFun`/`IndepFun` live there).
        **No `[DecidableEq ι]`** is needed (the child list is indexed by `Fin cs.length`,
        never `cs.toFinset`). `omit [DecidableEq κ]` / `omit [Fintype κ]` on the lemmas
        whose headers don't use them (the scratch showed unused-auto-include warnings on
        `μN_map_rowTuple`, `μπ_cylinder_eq`, `cylinder_witness`, `measurableSet_witness` —
        10.1/20.x's omit pattern). Theorem headers need the explicit `{τ : WitnessTree ι}`
        binder (`autoImplicit false`).
    - proof: |
        **Phase A — per-vertex measure (the marginal-of-restriction, survey B risk 3):**
        the single-vertex event `{ω | f_a (fun j => ω ⟨j, row j⟩)}` has measure
        `μπ μ (A a)` for ANY `row : vbl a → Fin (N + 1)` (`check_vertex_measure` below; the
        row map `j ↦ ⟨j, row j⟩` is always injective — first component — so no row
        hypothesis). Route: `μN_setOf_rowTuple` (the pushforward of μN along
        `ω ↦ fun s ↦ ω (row s)` is the restricted product, via `iIndepFun_pi →
        iIndepFun.precomp → iIndepFun.map_fun_eq_pi_map → measurePreserving_eval`) +
        `measurableSet_witness` (the `{σ | f_a σ}` set is measurable: it is the preimage of
        `A a` under the measurable completion map `e σ j := if j ∈ vbl a then σ ⟨j, hj⟩
        else Classical.choice (hΩ j)` — uses `hA` + `hΩ : ∀ j, Nonempty (Ω j)` derived
        once from `IsProbabilityMeasure (μ j)` via `nonempty_of_measure_ne_zero`) +
        `μπ_cylinder_eq` (the cylinder identity `A a = cylinder (vbl a) {σ | f σ}` by
        `Classical.choose_spec` + `infinitePi_cylinder`).
        **Phase B — disjoint-coordinate independence:** `indepFun_rowTuple` — two row
        families with `∀ s t, rowS s ≠ rowT t` give independent tuple maps (survey A test
        (2)'s chain: `iIndepFun_pi` on the Σ-coordinates →
        `iIndepFun.indepFun_finset₀` on the image finsets `I`/`J` → `IndepFun.comp` with
        the measurable reindex maps `x ↦ fun s ↦ x ⟨rowS s, mem⟩`); the factorization
        corollary is one line from `indepFun_iff_measure_inter_preimage_eq_mul.mp`.
        **Phase C — the tree induction:** by `WitnessTree.rec` over `cur` with
        `(whole, hN)` threaded unchanged (motive-1 = the per-tree claim, motive-2 the list
        form — 30.2/30.4's recursor pattern). The step for `mk a cs` splits the event into
        the root event (Phase A) ∩ the forest conjunction; the root-vs-forest factorization
        and the forest's own product factorization are Phase B applied along the children
        list, each child's event re-expressed as a preimage under its *family* tuple via
        `checkFamily`/`checkAuxT` (below). The freshness facts feeding Phase B's `hdisj` are
        the tree facts: same-depth pairs via `IsGood`'s second conjunct (overlapping `vbl`
        is impossible, so the Σ-pairs differ in the first component); different depths via
        40.1's strict inequality assembled with the depth shift (at the top call d = 0 use
        `treeProfile_gt_of_depth_lt` directly; at shifted depths compose
        `treeProfile_add_succ` + `one_le_treeProfileAtDepth_of_mem` +
        `treeProfile_le_of_le` as in 40.1's corrected chain) — packaged as the path-level
        `check_fresh` lemma. All three phases are compile-proven in the scratch.
    - **note**: no changes to 40.1's pinned defs; `treeProd`/`check_probability` sit in a
      new `section CheckProbability` after `section TreeProfile` in `Coupling.lean`.
- **prep**
    - `Measure.pi_pi_finset` — `Mathlib/MeasureTheory/Constructions/Pi.lean:315` — `@[simp]`
      measure of a finite box; NOT load-bearing for the pinned route (the per-vertex events
      are cylinders, not boxes) — kept as the survey B fallback.
    - `Measure.pi_map_pi` — `Mathlib/MeasureTheory/Constructions/Pi.lean:387` — the
      coordinatewise-map law (exact name; needs `[∀ i, SigmaFinite ((μ i).map (f i))]` +
      `hf : ∀ i, AEMeasurable (f i) (μ i)`; internal to `iIndepFun_pi`).
    - `measurePreserving_eval` — `Mathlib/MeasureTheory/Constructions/Pi.lean:404` —
      `[∀ i, IsProbabilityMeasure (μ i)] (i) : MeasurePreserving (Function.eval i)
      (Measure.pi μ) (μ i)` — the per-coordinate marginal of `μN_map_rowTuple`'s last step.
    - `Measure.pi_map_piCongrLeft` — `Mathlib/MeasureTheory/Constructions/Pi.lean:748` —
      `(e : ι ≃ ι') … : (Measure.pi fun i ↦ μ (e i)).map (MeasurableEquiv.piCongrLeft …)
      = Measure.pi μ` — reindexing a product measure along an equivalence (fallback for the
      forest-decomposition glue).
    - `pi_map_piOptionEquivProd` — `Pi.lean:451` — the `Option`-index cons decomposition of
      `Measure.pi` (fallback for the binary forest step).
    - `iIndepFun_pi` — `Mathlib/Probability/Independence/Basic.lean:892` (corrected from
      :893): `(mX : ∀ i, AEMeasurable (X i) (μ i)) : iIndepFun (fun i ω ↦ X i (ω i))
      (Measure.pi μ)` — with `X := id` this is the Σ-coordinate independence.
    - `iIndepFun.precomp` — `Independence/Basic.lean:324` —
      `(hg : g.Injective) (h : iIndepFun f μ) : iIndepFun (f ∘ g) μ` — reindexing the
      coordinate family along the injective row map (NOT in the old prep list; the key
      `μN_map_rowTuple` ingredient).
    - `iIndepFun.map_fun_eq_pi_map` — `Independence/Basic.lean:840` — `[Fintype ι]
      (hf) (h : iIndepFun f μ) : μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i))`
      — the tuple-map = product-measure law (the marginal-of-restriction in one shot).
    - `iIndepFun.indepFun_finset₀` — `Independence/Basic.lean:804` (corrected from :803).
    - `IndepFun.comp` — `Independence/Basic.lean:756` — `(hfg : f ⟂ᵢ[μ] g) (hφ : Measurable
      φ) (hψ : Measurable ψ) : (φ ∘ f) ⟂ᵢ[μ] ψ ∘ g`.
    - `indepFun_iff_measure_inter_preimage_eq_mul` — `Independence/Basic.lean:644` —
      `f ⟂ᵢ[μ] g ↔ ∀ s t, MeasurableSet s → MeasurableSet t → μ (f ⁻¹' s ∩ g ⁻¹' t) =
      μ (f ⁻¹' s) * μ (g ⁻¹' t)` — Phase B's factorization corollary.
    - `iIndepFun_iff_measure_inter_preimage_eq_mul` — `Independence/Basic.lean:654` — the
      Finset-family version (alternative full-factorization route).
    - `IndepSet.measure_inter_eq_mul` — `Independence/Basic.lean:584`; `Indep.indepSet_of_
      measurableSet` — :595 (kept as fallbacks).
    - `Measure.infinitePi_eq_pi` — `Mathlib/Probability/ProductMeasure.lean:510`;
      `Measure.infinitePi_map_restrict` — :375; `Measure.infinitePi_cylinder` — :~385
      (`infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S` for measurable S —
      the packaged cylinder identity the scratch uses).
    - `cylinder` / `mem_cylinder` — `Mathlib/MeasureTheory/Constructions/Cylinders.lean:159/
      163`; `Finset.restrict` — `Mathlib/Data/Finset/Pi.lean:161` (def `fun x ↦ f x` —
      `mem_cylinder` rewrites are rfl after a `change`).
    - `Finset.measurable_restrict` — `Mathlib/MeasureTheory/MeasurableSpace/Constructions.
      lean:657`.
    - `lintegral_indicator` — `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:496`
      (kept; not needed by the pinned map-apply route).
    - `nonempty_of_measure_ne_zero` — `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:
      189` — `(h : μ s ≠ 0) : s.Nonempty` — the `hΩ : ∀ j, Nonempty (Ω j)` derivation from
      `IsProbabilityMeasure.measure_univ : μ univ = 1` (`Typeclasses/Probability.lean:64`).
    - `Finset.disjUnionEquiv` — `Mathlib/Data/Finset/Basic.lean:610` — the disjoint-union
      equivalence for the forest-decomposition fallback.
    - `Finset.prod_biUnion` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:221` —
      `(hs : Set.PairwiseDisjoint (↑s) t) : ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i`
      — the treeProd bridge's child-image decomposition.
    - `Finset.prod_attach` — `Basic.lean:100` — `∏ x ∈ s.attach, f x = ∏ x ∈ s, f x`;
      `Finset.prod_insert` / `Finset.prod_image` — same file — the `{[]} ∪` split and the
      injective prefix-map product.
    - `List.mem_toFinset` — `Mathlib/Data/Finset/Dedup.lean` — `a ∈ l.toFinset ↔ a ∈ l`
      (converts the `∀ p ∈ vertices τ` comprehension to finset form; no nodup needed).
    - `List.toFinset_finRange` — `Mathlib/Data/Fintype/Basic.lean` —
      `(List.finRange n).toFinset = Finset.univ`.
    - `List.prod_ofFn` — `Mathlib/Algebra/BigOperators/Fin.lean` — `(List.ofFn f).prod =
      ∏ i : Fin n, f i`; `List.ofFn_getElem` — `Init/Data/List/OfFn.lean` — `ofFn
      (fun i => l[i]) = l` — together the bridge `∏ i : Fin cs.length, treeProd cs[i] =
      (cs.map treeProd).prod`.
    - `Measure.pi_pi_finset` — statement pinned: `[∀ i, IsProbabilityMeasure (μ i)] (f)
      (s : Finset ι) : Measure.pi μ ((s : Set ι).pi f) = ∏ i ∈ s, μ i (f i)` — the
      flat-route box measure (fallback if the per-step induction is replaced by a one-shot
      tuple map; `Measure.pi_eq` (Pi.lean:278) is the uniqueness characterization, only
      needed by option (b)'s architecture).
    - **MISSING glue (become 40.2's private helpers — all compile-proven in the scratch,**
      REAL proofs, statements below are the verified forms; the Proof agent writes them
      verbatim into the tmp):
      `μN_map_rowTuple {S} [Fintype S] (row : S → Σ _ : κ, Fin (N + 1))
      (hrow : Injective row) : (μN N μ).map (fun ω => fun s : S => ω (row s)) =
      Measure.pi (fun s : S => μ (row s).1)`;
      `μN_setOf_rowTuple` — the `map_apply` form:
      `… (hC : MeasurableSet C) : (μN N μ) {ω | (fun s : S => ω (row s)) ∈ C} =
      Measure.pi (fun s : S => μ (row s).1) C`;
      `indepFun_rowTuple {S T} [Fintype S] [Fintype T] (rowS) (rowT)
      (hdisj : ∀ s t, rowS s ≠ rowT t) : IndepFun (fun ω => fun s : S => ω (rowS s))
      (fun ω => fun t : T => ω (rowT t)) (μN N μ)`;
      `μπ_cylinder_eq (S : Finset κ) (C : Set (Π j : S, Ω j)) (hC : MeasurableSet C) :
      μπ μ (cylinder S C) = Measure.pi (fun j : S => μ j) C`;
      `cylinder_witness (a) : cylinder (vbl a) {σ : Π j : vbl a, Ω j |
      Classical.choose (hdet a) σ} = A a`;
      `measurableSet_witness (hA : ∀ i, MeasurableSet (A i)) (hΩ : ∀ j, Nonempty (Ω j))
      (a) : MeasurableSet {σ : Π j : vbl a, Ω j | Classical.choose (hdet a) σ}`;
      `check_vertex_measure (hA) (a) (row : vbl a → Fin (N + 1)) :
      (μN N μ) {ω | Classical.choose (hdet a) (fun j : vbl a => ω ⟨j, row j⟩)} =
      μπ μ (A a)`;
      `checkFamily (whole) (hN) : WitnessTree ι → ℕ → Finset (Σ _ : κ, Fin (N + 1))` — the
      recursive finset of coordinates read at depth d (`(vbl a).image (fun j => ⟨j, ⟨…⟩⟩)
      ∪ ((cs.map (fun c => checkFamily whole hN c (d + 1))).foldl (· ∪ ·) ∅)`) — compiles
      (scratch); plus DESIGN-level (not yet compile-tested — Proof pins the exact forms):
      the tuple-space check `checkAuxT` on `Π p : checkFamily …, Ω p.1` with
      `{ω | checkAux whole hN cur d ω} = g_cur ⁻¹' {t | checkAuxT … t}` (induction), the
      path-level freshness `check_fresh` (from IsGood + 40.1's
      `treeProfile_gt_of_depth_lt`/`add_succ`/`one_le_…_of_mem`/`le_of_le`), and the
      forest factorization (list induction over the children with `indepFun_rowTuple` +
      `indepFun_iff_measure_inter_preimage_eq_mul`).
    - **Compile-verified pitfalls (scratch, 2026-08-16):** (i) `rw [Measure.map_apply …]`
      FAILS on goals containing ΩN-applications or `Classical.choose (hdet a)` — the
      semireducible `ΩN`/`DeterminedBy` do not unfold at the instances transparency level
      ("function expected ω (row s)") — use exact-term forms
      (`exact (Measure.map_apply …).symm`, `exact μN_setOf_rowTuple …`) or `change` to the
      unfolded `Π p : Σ _ : κ, Fin (N + 1), Ω p.1` form first; (ii) `List.bind` does NOT
      exist in v4.32.0 — `cs.bind` fails; use `List.flatMap` for lists,
      `(cs.map f).foldl (· ∪ ·) ∅` for finset unions over lists (`bind_eq_flatMap`,
      `Mathlib/Data/List/Basic.lean:254`); (iii) section-variable pruning: a theorem body
      only sees section variables mentioned in its statement — `measurableSet_witness` and
      `check_vertex_measure` take `hA` (and `hΩ`) as EXPLICIT binders, and `hΩ` is derived
      inside μ-mentioning statements; (iv) `Σ _ : κ` anonymous-binder pairs need type
      ascriptions `(⟨j, r⟩ : Σ _ : κ, Fin (N + 1))` in lambda positions (expected-type
      metavar); (v) per-vertex row injectivity: `exact Subtype.ext (congrArg Sigma.fst h)`;
      (vi) `Fintype (vbl a)` / `Fintype (Σ j : vbl a, Fin (N+1))` / `DecidableEq (vbl a)`
      all synthesize from `[DecidableEq κ]` alone (scratch examples compiled);
      (vii) **attempt-2 tail repairs (Survey-verified 2026-08-16 at
      `/tmp/mt_diag_402.lean` — exit-0 modulo the `sorry`):** an `Eq.mp`-family cast whose
      argument is an application with a `have`-bound proof (`h (i :: p) hvp'`) does NOT
      typecheck against the motive's expected `labelAt (.cons i c hci hp)`-labelled type —
      the elaborator does not unfold the local def `hvp'` in the defeq check; INLINE the
      proof term (`h (i :: p) (WitnessTree.ValidPath.cons i c hci hp)`) so the labels are
      syntactically identical; (viii) a `convert … using 2` bullet's goal keeps the
      auto-named binder `a✝` (NOT the source's `p`/`hp`) and is an iff of foralls — fix:
      `rename_i p`, `constructor`, and per direction `intro h hp` + `let P2` +
      `Eq.mpr`/`Eq.mp (congrArg P2 (Nat.zero_add p.length)) (h hp)` (the `P2`-family
      congruence works here because both sides share the SAME `hp` fvar — unlike (vii));
      (ix) `labelAt` is semireducible — never rely on rfl/defeq through an opaque
      `Classical.choose` ValidPath; bridge labels via `labelAt_cons` + `cases hp`.
    - Internal deps (survey B §5): items 40.1 (`treeProfile`/`check`/profile inequality),
      10.3 (`μN`), 30.1 (`IsGood`). 30.7 is NOT consumed here (the abstract tree carries
      its own `IsGood`/`size` hypotheses; `T_size_le_N` is first consumed by 40.3).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 2 / 15 | done | **Option (a)** — finish `check_eq_allVertices`'s 3-error tail with the Survey-verified repairs, then prove `check_probability` from the glue. Tail: (1) INLINE the proof term at the Eq.mp argument — `(h (i :: p) (WitnessTree.ValidPath.cons i c hci hp))` instead of `(h (i :: p) hvp')` (the elaborator does not unfold the `have hvp'` local def in the defeq check against the `labelAt (.cons …)`-labelled motive; delete the then-unused `have hvp'`); (2) the `convert (hmain τ (Eq.refl _) 0) using 2` bullet: the goal is `a✝ : List ℕ ⊢ (∀ hp, C (a✝.length + 1)) ↔ (∀ hp, C (0 + a✝.length + 1))` (auto-named binder!) — `rename_i p`, `constructor`, per direction `intro h hp` + `let P2` + `Eq.mpr`/`Eq.mp (congrArg P2 (Nat.zero_add p.length)) (h hp)`. Both repairs compile-verified by Survey at `/tmp/mt_diag_402.lean` (exit 0, only the `sorry` + the 2 pre-existing warnings remain; also add the house `omit` on `checkAux_eq_checkAuxT`/`rows_disjoint_of_distinct`). Then `check_probability`: unfold `check` → `check_eq_allVertices` → `mem_vertices_iff` + a `labelAt_eq_of_path` 1-liner (`congrArg labelOf (treeAt_eq_of_path hp hp')`); measure side by `Finset.induction_on` over `(vertices τ).toFinset` — per-step `indepFun_rowTuple` (current vertex row vs the accumulated earlier-vertices row family; hdisj via `rows_disjoint_of_distinct` + the induction's `p ∉ s`, hgood available) + `indepFun_iff_measure_inter_preimage_eq_mul.mp` + accumulated-`biInter` measurability, per-vertex factor via `check_vertex_measure` (row `fun j => ⟨treeProfile vbl τ ↑j (p.length + 1), treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩` — exactly `check_eq_allVertices`'s RHS shape); product side `∏ p ∈ (vertices τ).toFinset, μπ μ (A (labelAt_p)) = treeProd (μ := μ) A τ` by `WitnessTree.rec` — `Finset.prod_insert` for the root, `Finset.prod_biUnion` over the `i`-prefixed child images (PairwiseDisjoint via prefix injectivity), `Finset.prod_image`, `labelAt_cons` + `cases hp` for the label bridge, outer bridge `∏ i ∈ (List.finRange cs.length).toFinset, treeProd cs[i] = (cs.map treeProd).prod` via `List.toFinset_finRange` + `List.prod_ofFn` + `List.ofFn_getElem`. **Option (b) (H4–H6 measure-split) rejected**: unnecessary rebuild — the tail repairs are localized and verified, and the flat vertex route consumes only already-REAL-proved glue. | Proved `check_probability` (option (a), flat-vertex route), micro-stepped: (1) repaired the `check_eq_allVertices` tail with the Survey-verified fixes (inlined `ValidPath.cons` proof term, `rename_i`/`constructor`/`P2`-congruence bullet, house `omit`s); (2) measure side by `Finset.induction_on` over `(vertices τ).toFinset` — per-step joint-tuple independence (`indepFun_rowTuple` on the current vertex row vs the accumulated `rowT` family, hdisj via `rows_disjoint_of_distinct`) + accumulated-`biInter` cylinder measurability (`measurableSet_witness` on the finite biInter preimage), via `checkSet_eq_vertices`/`checkSet_eq_iInter`/`iInter_insert_eq`/`μN_vertexCond`/`μN_vertexCond_inter_vertexCond`/`μN_iInter_eq_prod`; (3) product side via hand-proved `List_toFinset_append/_map/_flatMap` glue (absent from this mathlib), the certificate-independent `labelFactor` + `labelFactor_cons`, strong-induction `prod_labelFactor_eq_treeProd` (child-finset biUnion + `Finset.prod_biUnion`/`prod_image`/`prod_ofFn` bridges) and `prod_vertices_eq_treeProd`; (4) final 4-step calc (`checkSet_eq_vertices` → `checkSet_eq_iInter` → `μN_iInter_eq_prod` → `prod_vertices_eq_treeProd`). Model-switch note: the design-heavy micro-steps (the list-toFinset glue, `prod_labelFactor_eq_treeProd`) stalled the default model; the opus-model Proof agent completed them and the calc assembly. | Independently verified: tmp (996 lines) `lake env lean` exit 0, no sorry/axiom/admit/native_decide; one cosmetic `unnecessarySimpa` warning (the `childrenOf` simpa) — fixed at integration, the linter's suggested `simp [WitnessTree.childrenOf]` replacement compiles. `check_probability` matches the pinned statement exactly; all 4 calc steps match the helper signatures. Tmp-size rule: 996 > 500, but the item is COMPLETE and all code is load-bearing — correct action is integration, no split. Integrated into `StatsMLlib/Probability/MoserTardos/Coupling.lean`: new `section CheckProbability` after `end TreeProfile` (universes `{ι : Type u} {κ : Type v}`, `[Fintype κ] [DecidableEq κ]`, `[∀ j, MeasurableSpace (Ω j)]`, `[∀ j, IsProbabilityMeasure (μ j)]` per the pinned section requirements); imports `Mathlib.MeasureTheory.Constructions.Cylinders/Pi`, `Mathlib.Probability.Independence.Basic`, `Mathlib.Probability.ProductMeasure` added; `open MeasureTheory`/`open ProbabilityTheory`/`open scoped ENNReal` at file level (tmp mirror); module docstring extended (`treeProd`/`checkFamily`/`checkAuxT`, `check_probability`); 29 long lines rewrapped to ≤ 100; private helpers kept private; tmp deleted. `lake env lean` exit 0, zero warnings; `lake build StatsMLlib.Probability.MoserTardos.Coupling` OK (2993 jobs). | `tmp_check_prob.lean` |
    | 2026-08-16 | 1 / 15 | pending | Prove check_probability (tree induction over the check conjunction + the marginal-of-restriction glue + disjoint-coordinate independence) — **parked partial**: all G1–G6 glue, `checkFamily`, `checkAuxT`, `checkAux_eq_checkAuxT`, `vertices` + `mem_vertices_iff` REAL-proved; blocked on `check_eq_allVertices` (simp/instances-transparency wall); `check_probability` still stubbed. Next attempt: fresh-context return, per-child motive re-derivation or the H4–H6 measure-split architecture. | — | `tmp_check_prob.lean` |

### 40.3. occurrence_implies_check, coupling

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 2 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Coupling.lean`
- **informal**
    - statement: |
        The coupling lemma (survey B D18, notes §14 Lemma 14.1 — the heart of the proof;
        difficulty **Hard**, est. ~250 lines (Survey estimate: ~400 with the private glue);
        critical path ★; survey B risk 2). **Pinned at Survey 2026-08-16 — the WHOLE block
        below is compile-tested at `/tmp/mt_survey_403.lean` (`lake env lean` exit 0; the
        only diagnostics are the 17 expected `sorry`s — 15 private glue statements + the 2
        headlines; the 40.2 mirrors are included, to be dropped at integration once 40.2
        lands).** Sections: a new `section OccurrenceCheck` (the per-vertex/check glue, NO
        μ/Fintype κ) and a new `section CouplingLemma` (the measure side), after 40.2's
        `section CheckProbability`. **Universe note (compile-forced): both sections use
        `{ι : Type u} {κ : Type u}` — `treeElig`/`treeAt` are pinned at `κ : Type u` in
        `WitnessTree.lean`, so the same `vbl : ι → Finset κ` cannot serve them at
        `κ : Type v` (the TreeProfile section's universe).** `open MeasureTheory` required
        (the `Measure`/`IsProbabilityMeasure` names — probe-verified). Pinned statements:
        ```lean
        /-- **40.3 headline (a)**: if the occurring tree at time `t` is `τ`, then the
        structural τ-check passes on `ω`. `hN` is an EXPLICIT hypothesis (not derived from
        `T_size_le_N`): the coupling supplies it and it matches `check_probability`'s — the
        check's Fin rows carry the hN proof term, and two different hN's would need a congr
        glue through the whole recursion. -/
        theorem occurrence_implies_check [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ}
            (ht : t < R vbl A pick hpick ω) {τ : WitnessTree ι}
            (hT : T vbl A pick hpick ω t = τ) (hN : WitnessTree.size τ ≤ N) :
            check vbl A hdet hN ω

        /-- **40.3 headline (b), the coupling lemma**: `μN {∃ t < R, T = τ} ≤ treeProd τ`.
        NO `IsGood` hypothesis — see the 𝒯_i(N) design decision below. -/
        theorem coupling [DecidableEq ι] [Inhabited ι] (hA : ∀ i, MeasurableSet (A i))
            {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N) :
            μN N μ {ω | ∃ t < R vbl A pick hpick ω, T vbl A pick hpick ω t = τ} ≤
              treeProd (μ := μ) A τ
        ```
        **The 𝒯_i(N) design decision (resolved, records the orchestrator's open question
        — option (a)).** `coupling` takes ONLY `hN : size τ ≤ N` (plus `hA`); `IsGood vbl
        τ` is handled by an internal `by_cases`: good τ ⟹ occurrence ⊆ check +
        `check_probability`; non-good τ ⟹ the occurrence event is EMPTY (any occurrence
        gives `IsGood vbl τ` via 30.7's `T_isGood` + `hT`), so `μN = 0 ≤ treeProd`.
        Consequence: 𝒯_i(N) (50.2) STAYS "proper trees rooted at i with ≤ N vertices" —
        option (b) (good trees) was rejected because 50.3's height-induction reconstructs
        trees from child-label SETS `C ⊆ Γ⁺(i)`, which does not enforce the global
        same-depth disjointness (`IsGood`'s second conjunct) — the multinomial
        factorization would overcount against a good-tree domain. 60.2's chain then needs
        NO per-τ `by_cases`: `∑_{τ ∈ 𝒯_i(N)} μN{∃t, T=τ} ≤ ∑_τ treeProd τ` via
        `coupling` with `hN := τ.2.2.1` (the 𝒯_i(N) membership). The occurrence event form
        `∃ t < R …, T … t = τ` matches 60.1's counting-identity indicator exactly.
        **Private glue (all statements in the scratch; the proof plan below):**
        `truncLog` (abbrev — the log with entries below `q` dropped, the bridge between the
        drop-fold stage tree and `treeAt`); `treeProfile_eq_zero` (the recursive-vs-paths
        bridge: `treeProfile` is recursive, so "no counted vertex" facts need this); the
        step lemmas `attachBelow_treeProfile_add` /
        `attachBelow_treeProfile_of_not_mem`; the stability pair `labelAt_foldr` (forward)
        / `validPath_foldr_rev` (the peel, via 30.5's public `attachBelow_old_or_new`);
        the main fold induction `foldr_resample_profile_add` (**additive form, no side
        condition** — see the proof); the label facts `treeAt_label_of_lt` (genuineness),
        `treeAt_label_time_le`, `treeAt_truncLog_label_time_ge`,
        `treeAt_truncLog_eq_drop_fold`; the backward direction
        `treeProfile_zero_of_new_vertex`; the bijection `resample_count_eq_profile`; the
        Algorithm glue `count_eq_filter` (count = filter of genuine entries); the
        per-vertex check `check_vertex_of_occurring`.
    - proof: |
        (survey B §3.3(b), both directions audited — proved as ONE fold induction, the
        additive form, which is the bijection in induction form.)
        **`treeProfile_eq_zero`** — `WitnessTree.rec` (motive-2 list pattern): root from
        `h [] .root`, children via `List.sum_eq_zero_iff` + the shifted/restricted `h`.
        **The step lemmas** — `attachBelow_treeProfile_add` (tree induction over σ with
        the threshold generalized, so the child step recurses at threshold `d` with a
        witness at depth ≥ `d - 1`): unfold via `WitnessTree.attachBelow.eq_1` +
        `cases`/`split`-reduction of the internal `maxOption✝` fold (30.5's documented
        outside-file technique — the private name is unwritable) + PUBLIC S1
        (`deepestEligible_eq_some`/`eq_none`): `hd` ⟹ `≠ none` ⟹ `dmax` with `d ≤ dmax`;
        root-attach branch (fold = none + root eligible ⟹ `dmax = 0` ⟹ `d = 0`): the new
        leaf at depth 1 contributes `treeProfile leaf X 0 = 1` (`hX`); some-`dd` branch:
        `attachInFirst.eq_1/.eq_2` + `split_ifs` over the children list, the replaced
        child satisfies `deepestEligible = some (dd - 1)` ⟹ (S1's ∃-direction) an eligible
        witness at depth `dd - 1 ≥ d - 1` (`Nat.sub_le_sub_right`) ⟹ the tree-IH at
        threshold `d`; kept children unchanged. `attachBelow_treeProfile_of_not_mem` is the
        same induction without witnesses (~30 lines). **`foldr_resample_profile_add`** —
        list induction over the scan with the seed generalized; the step cases the match on
        `Λ s₁`: `none` ⟹ tree unchanged; `some i` with `X ∈ vbl i` ⟹ `attachBelow_treeProfile_add`
        with the hd witness = the σ-vertex u transported by `labelAt_foldr` (treeElig via
        `Or.inr` of the overlap through `X` — no 10.1 citation, the 30.4/30.5 pattern);
        `X ∉ vbl i` ⟹ `_of_not_mem`. **NO side condition is needed** (Survey finding): an
        entry whose event contains `X` always attaches below a max-eligible vertex — u is
        eligible whenever `X ∈ vbl i ∩ vbl [u]`, so the new vertex has depth ≥ d(u)+1 and
        contributes at threshold d(u)+1 regardless of times; the filter count matches
        exactly. **The label facts** — small fold inductions (seed label `(t, ·)`, inserted
        labels `(s, i)` from `Λ s = some i`). **`treeAt_truncLog_eq_drop_fold`** —
        `List.take_append_drop` + `List.take_range` (`(range t).take q = range (min q t) =
        range q` under `q ≤ t`) + `List.foldr_append` + a private no-op fold over the
        `take`-part (each `s < q` gives `truncLog q Λ s = none` ⟹ step = id) +
        `List.foldr_ext` for the drop-part step equality. **`treeProfile_zero_of_new_vertex`**
        (the backward direction at the vertex's creation) — `treeProfile_eq_zero` with:
        any abstract path `p'` at depth ≥ d+1 with `X ∈ vbl` lifts
        (`validPath_of_forgetTime`/`labelAt_of_forgetTime`); `p' ≠ p` (lengths);
        `treeAt_timeInject` ⟹ time ≠ q; `treeAt_truncLog_label_time_ge` + trichotomy ⟹
        q < time(p'); overlap through X ⟹ `depth_gt_of_earlier_overlap` gives
        depth p > depth p' — contradiction. **`resample_count_eq_profile`** — the peel
        `validPath_foldr_rev` (l = range q, hneq: `s₁ < q` via `List.mem_range`) lands
        u's path in the drop-fold stage tree σ_q with the same label; then
        `foldr_resample_profile_add` (σ := σ_q, l := range q) + the zero lemma
        (`σ_q = treeAt (truncLog q Λ) t`) + `omega`. **`count_eq_filter`** —
        `Fin.induction` over the run: zero = initial state `fun _ => 0`; succ: `rcases h :
        (run … i.castSucc).2 with _ | ⟨e, he⟩` — the none case contradicts `hgen i`
        (`log_ne_none_iff_lt_R` + `run_step_of_lt_R`); the some case: `count ω i.succ`'s
        advance (`step_fst_val_eq_of_mem`/`step_fst_eq_of_not_mem` via `simp [count, run] at
        h ⊢` + `rw [h]`, the 20.2 pattern) matches the filter's `i`-entry via the glue
        `log ω i = some e.1` (unfold `log` + `dif_pos` + `Option.some.inj` against
        `run_step_of_lt_R`'s payload). **`check_vertex_of_occurring`** — q := u's time ≤ t
        (`treeAt_label_time_le`), q < R; `log ω q = some a` (`treeAt_label_of_lt` for
        q < t; the q = t root case via `log_ne_none_iff_lt_R` + `Option.ne_none_iff_exists`
        + `treeAt_root_label`); the run's payload `e` at `⟨q, q < N + 1⟩`
        (`run_step_of_lt_R`, `e.1 = a` via the log unfolding); `e.2.1 : assign ω (count …
        ⟨q, ·⟩) ∈ A a`; the row equality `(count … X : ℕ) = treeProfile vbl τ X (d+1)`
        via `count_eq_filter` + `resample_count_eq_profile` + `simpa [T] using hT`;
        `Classical.choose_spec (hdet a) (assign ω c)` + the argument equality (`Fin.ext`
        on the row values — proof irrelevance) closes the witness proposition.
        **`occurrence_implies_check`** — let `τ̃ = treeAt vbl (log …) t`; path induction
        over `p` with the claim `∀ hp : ValidPath τ̃ p, checkAux vbl A hdet τ hN (forgetTime
        (treeAt hp)) (depth τ̃ p) ω` — the WHOLE is the given `τ` with the GIVEN `hN`
        (no congr glue anywhere); nil: `check_vertex_of_occurring` for the root +
        `∀ c ∈ childrenOf …` via the IH at `[k]` (`childrenOf_forgetTime` +
        `validPath_append`/`treeAt_validPath_append`); cons: the shifted-depth analog;
        close `simpa [check, T] using hcheck [] .root`. **`coupling`** — `by classical;
        by_cases hgood : IsGood vbl τ`: good ⟹
        `calc μN {∃t, T=τ} ≤ μN {check vbl A hdet hN} := MeasureTheory.measure_mono
        (subset via occurrence_implies_check) _ = treeProd := check_probability vbl A hdet
        hA hgood hN` — **`measure_mono` needs NO MeasurableSet hypothesis
        (probe-verified: `(h : s ⊆ t) : μ s ≤ μ t`), so `measurableSet_check` is DROPPED
        from the glue list**; non-good ⟹ the occurrence event is empty (T_isGood + hT
        contradicts hgood) ⟹ `rw [hempty, measure_empty]; exact zero_le _`.
- **prep**
    - `MeasureTheory.measure_mono` — probe-verified signature `(h : s ⊆ t) : μ s ≤ μ t`,
      NO measurability hypothesis — the coupling's only measure comparison;
      `MeasureTheory.measure_empty` — the non-good case.
    - 40.2 (INTEGRATED 2026-08-16, mirror dropped 2026-08-17): `treeProd`,
      `check_probability` — cited directly from `Coupling.lean`; the v2 scratch
      `/tmp/mt_survey_403_v2.lean` (mirror section deleted) recompiles exit 0 with the
      only sorries being the 16 of the 40.3 block (14 glue theorems + the 2 headlines;
      `truncLog` is an abbrev — the mirror's `check_probability` was the 17th, gone
      with the mirror). NO statement names changed by the integration; the integrated
      signatures match the mirror verbatim.
    - 40.1: `treeProfile`, `check`/`checkAux`, `treeProfile_lt_succ_of_size_le` (the
      per-vertex rows). NOT consumed: the 40.1 inequality lemmas.
    - 30.5 public: `depth_gt_of_earlier_overlap` (the zero lemma's contradiction),
      `treeAt_timeInject` (distinct paths ⟹ distinct times — the bijection's
      injectivity, both directions), `attachBelow_old_or_new` (the peel).
      **30.6 NOT consumed** (survey B §5 listing corrected — the injectivity used here
      is the per-tree time-injectivity, 30.5's; 30.6's `T_injective` is 60.1's).
    - 30.2 public: `deepestEligible_eq_some`/`deepestEligible_eq_none` (S1 — the step
      lemmas' dmax bookkeeping), `attachBelow_spec` (S2b — u's creation, used by the
      zero lemma's setup), `attachBelow_eq_self_of_deepestEligible_none` (S2a — the
      peel's none case), `labelAt_attachBelow` (b) (labelAt_foldr), `validPath_append`
      + `treeAt_validPath_append` (the check induction's child paths). Equation lemmas
      `WitnessTree.attachBelow.eq_1` / `attachInFirst.eq_1`/`.eq_2` /
      `deepestEligible.eq_1` — probe-verified accessible from outside the file; the
      RHS contains the mangled `maxOption✝` — reduce only via `cases`/`split`
      (30.5's documented technique).
    - 30.7: `validPath_of_forgetTime` + `labelAt_of_forgetTime` + `labelAt_cast` (the
      zero lemma's abstract transport), `T_isGood` (the coupling's non-good case).
      NOT consumed: `T_size_le_N` (the hN is explicit; 60.1 consumes it for the
      𝒯_i(N) membership).
    - 30.3: `treeElig`/`treeAt`/`forgetTime`/`T`; `childrenOf_forgetTime`,
      `labelOf_forgetTime`, `forgetTime_getElem?`, `validPath_forgetTime`,
      `treeAt_forgetTime`, `labelAt_forgetTime` (the check induction's subtree
      transport), `treeAt_root_label` (the root-case log genuineness), `size_forgetTime`.
    - 20.4: `log`, `log_ne_none_iff_lt_R`, `run_step_of_lt_R` (the per-vertex
      certificate); 20.3: `R_le` (the `q < N + 1` Fin terms); 20.2: `run`/`count`;
      20.1: `step_fst_val_eq_of_mem`/`step_fst_eq_of_not_mem` (count_eq_filter's
      advance). NOT consumed: `run_count_le` (no availability argument — the Fin rows
      match by `Fin.ext` on values).
    - 10.2: `DeterminedBy` + `Classical.choose`/`Classical.choose_spec` (the witness);
      10.3: `ΩN`/`μN` (the coupling's measure).
    - `Option.ne_none_iff_exists`, `Option.some.inj`, `Fin.ext`, `Nat.lt_or_eq_of_le`,
      `Nat.sub_le_sub_right`, `Nat.lt_of_lt_of_le`, `omega` — the row/time glue.
    - List glue (all probe-verified): `List.take_range`
      (`(range t).take q = range (min q t)`), `List.take_append_drop`,
      `List.foldr_append`, `List.foldr_ext` (**`List.foldr_congr` does NOT exist** —
      probe), `List.sum_eq_zero_iff`, `List.map_append`, `List.filter_cons_of_pos`,
      `List.mem_range`. (**`List.drop_range` does NOT exist** — probe; the drop-fold
      bridge goes through `take_append_drop` instead.)
    - `open MeasureTheory` required in the tmp (probe: `Measure`/`IsProbabilityMeasure`
      unresolved without it); `open scoped ENNReal` in the CouplingLemma section.
    - **PITFALL (compile-verified):** `List.filter` returns a LIST — `.card` fails,
      use `.length` (30.6's `treeAt_count_label` precedent); the filter predicates are
      Bool-valued via `decide (X ∈ vbl i)` ([DecidableEq κ] only — matching on
      `Option ι` needs no `[DecidableEq ι]`).
    - Internal deps (survey B §5, corrected): 40.2 (`treeProd`/`check_probability`),
      40.1 (`treeProfile`/`check`), 30.5 (`depth_gt_of_earlier_overlap`,
      `treeAt_timeInject`, `attachBelow_old_or_new`), 30.2 (S1/S2a/(b) spec),
      30.7 (`validPath_of_forgetTime`/`labelAt_of_forgetTime`/`T_isGood`), 30.3
      (the construction + transport), 20.4 (`log`/`run_step_of_lt_R`), 10.2
      (`DeterminedBy`). NOT: 30.6, `T_size_le_N`, `run_count_le` (see above).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-17 | 2 / 15 | done | Setup materializes the v2 scratch (`/tmp/mt_survey_403_v2.lean`, 40.2 mirror dropped — integrated `treeProd`/`check_probability` cited, recompile verified exit 0) into `tmp_coupling.lean` with the 16 pinned statements as sorries (14 glue + 2 headlines; `truncLog` abbrev), then Proof fills them in dependency order per the pinned proof plan | Three opus Proof launches filled the 16 stubs in dependency order: launch 1 proved the fold machinery 1–6 (`mtMaxOption` defeq copy + the `eq_1`-rewrite technique, `foldl_mtMaxOption_eq_some`, `Option_map_succ_eq_some`, `treeProfile_eq_zero` via `WitnessTree.rec`, the step lemmas `attachBelow_treeProfile_add`/`_of_not_mem`); launch 2 proved the glue 7–14 (`labelAt_foldr`, the peel `validPath_foldr_rev` via `attachBelow_old_or_new`, the additive fold induction `foldr_resample_profile_add` with NO side condition, `foldr_label_spec`, the label facts, the truncation bridge `treeAt_truncLog_eq_drop_fold` via `take_append_drop`+`foldr_ext`, the backward direction `treeProfile_zero_of_new_vertex` via `treeAt_timeInject`+`depth_gt_of_earlier_overlap`, the bijection `resample_count_eq_profile`, `count_eq_filter` via `Fin.induction`, `check_vertex_of_occurring`); launch 3 proved the headlines 15–16. Key deviations: 15 uses the PUBLIC `checkSet_eq_vertices` (the private `check_eq_allVertices` correctly avoided); 16 (coupling): the stub signature did not mention `hdet`, so it was not auto-included — fixed with `include hdet in`, and the integrated theorem carries an implicit `hdet` section-parameter (PRESERVE); house techniques: `let`-bound (not `have`) casts for definitional links, `erw` for run-unfolding matches, `Fin.induction_succ`, `Fin.ext rfl` + `change` at .default transparency | Independently verified: tmp (1361 lines) `lake env lean` exit 0, no sorry/axiom/admit/native_decide; `#print axioms` of both headlines = [propext, Classical.choice, Quot.sound]; both statements match the pinned 40.3 forms exactly. 6 cosmetic warnings found and ALL fixed (4 unnecessarySimpa — incl. `simp at hdepth'` closing the goal directly; the unused `hmem` simp argument; the auto-included-unused `[∀ j, MeasurableSpace (Ω j)]` on `count_eq_filter`/`check_vertex_of_occurring` via the Algorithm.lean-style bare `omit` — note `omit … in` rejects `private`, and a `/--` doc comment must immediately precede its declaration). Tmp-size rule: 1361 > 500, but the item is COMPLETE and all code load-bearing — integration, no split (40.2's ruling). Integrated into `Coupling.lean`: new `section OccurrenceCheck` + `section CouplingLemma` after `end CheckProbability` per the pinned layout; universe note honored (both `{ι : Type u} {κ : Type u}`); `include hdet in` preserved; privates private; probes dropped; 11 over-long lines rewrapped; module docstring extended. Integrated file: `lake env lean` exit 0 with ZERO warnings; `lake build StatsMLlib.Probability.MoserTardos.Coupling` OK (2993 jobs). tmp deleted | `tmp_coupling.lean` |
    | 2026-08-16 | 1 / 15 | working | Prove `occurrence_implies_check` (hN explicit — no congr glue; the per-vertex check `check_vertex_of_occurring` via the run's certificate + the row equality from `count_eq_filter` + `resample_count_eq_profile`) and `coupling` (internal `by_cases` on `IsGood` — no hgood hypothesis, 𝒯_i(N) stays proper trees; occurrence ⊆ check + 40.2's `check_probability` via `measure_mono`, empty event via `T_isGood`); the bijection as ONE fold induction: `foldr_resample_profile_add` (additive form, no side condition) with the step lemmas `attachBelow_treeProfile_add`/`_of_not_mem` (S1 + the equation lemmas), plus the peel `validPath_foldr_rev`, the truncation bridge `treeAt_truncLog_eq_drop_fold`, the backward direction `treeProfile_zero_of_new_vertex` (timeInject + `depth_gt_of_earlier_overlap`), and the bridge `treeProfile_eq_zero` — whole block Survey-compiled at `/tmp/mt_survey_403.lean` (exit 0, 17 expected sorries, 0 errors/warnings) | — | — | `tmp_coupling.lean` |

---
## 50. Galton–Watson (Core Lemmas)

### 50.1. x', gwWeight, gwWeight_telescope

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/GaltonWatson.lean`
    - note: orchestrator-pinned (2026-08-16, after an agent stall): `gwWeight`'s accepted
      child product is the **List** product `(cs.map (fun c => x (labelOf c))).prod` (NOT
      `List.prod`-with-a-function — that API does not exist in v4.32.0, use `.map …).prod`);
      the rejected product is the **Finset filter** `((gammaPlus vbl a).filter fun j => j ∉
      (cs.map labelOf)).prod (fun j => 1 - x j)` (no `Nodup`/`Proper` needed in the def); the
      def's section-variable auto-binding puts `(vbl)` first — `gwWeight (vbl) (x) τ`.
- **informal**
    - statement: |
        The Galton–Watson weight algebra (survey B E19, notes §17 Lemma 17.1; difficulty
        Medium, est. ~150 lines; critical path ★):
        - `x' (x) (vbl) (i) := x i * ∏_{B ∈ Γ(i)} (1 - x B)` — product over the OPEN
          neighborhood `(overlapGraph vbl).neighborFinset i`.
        - `gwWeight (vbl) (x) (τ : WitnessTree ι) : ℝ` — the genuine branching probability
          (17.3) as a structural fold:
          `gwWeight vbl x (mk a cs) := (cs.map (fun c => x (labelOf c))).prod *
            (((gammaPlus vbl a).filter (fun j => j ∉ cs.map labelOf)).prod (fun j => 1 - x j)) *
            (cs.map (gwWeight vbl x)).prod` — accepted-child **List** product (the
          Proper-hypothesis makes it equal to the set product), rejected **Finset filter**
          over `Γ⁺(a) \ C_τ(a)`. **No division in the def.**
        - `gwWeight_telescope (hxi : x i ≠ 0) :
          gwWeight τ = ((1 - x i) / x i) * ∏_{u ∈ V τ} x' ([u])` — the telescope to (17.2),
          for trees rooted at `i`.
    - proof: |
        (survey B §3.4) Tree induction using (a) the child-to-nonroot reindexing
        `∏_u ∏_{B ∈ C_τ(u)} x B = ∏_{v ≠ root} x ([v])` (each non-root is the child of
        exactly one parent) and (b) the rejection-product cancellation
        `∏_u ∏_{B ∈ W_u} (1 - x B) = (1 - x i) * ∏_u ∏_{B ∈ Γ([u])} (1 - x B)` via
        `Γ⁺([u]) = C_τ(u) ⊔ W_u` (child labels ⊆ Γ⁺(parent) — the witness-tree
        condition). Pure ℝ/Finset algebra; both identities audited against notes
        (17.4)–(17.2). GW algebra is entirely in ℝ; division only inside `ofReal` later.
    - **prep**
        - `Finset.prod_eq_mul_prod_diff_singleton` —
          `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:202` (survey A §4.7).
        - `Finset.prod_mul_distrib` / `Finset.prod` basics — basic Finset API.
        - ℝ field algebra (`field_simp`; the `x i ≠ 0` hypothesis).
        - Internal deps (survey B §5): items 30.1 (`WitnessTree` + `Proper`), 10.1 (Γ⁺).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | Define `x'` (neighborFinset form, matching 60.2's hLLL) and `gwWeight` (List-accepted + Finset-filter-rejected fold, no division); prove `gwWeight_telescope (hxi : x i ≠ 0) : gwWeight vbl x τ = ((1 - x i) / x i) * ∏ p ∈ vertices-ish (labels) — via the two identities (a) ∏_u acc_u = ∏_{v≠root} x[v] (List-join) and (b) ∏_u rej_u = (1-x i)·∏_u ∏_{Γ([u])}(1-x j) (filter-fold, NO division needed — the target's /x i cancels the root factor under hxi). | Defs `x'` (neighborFinset form), `x'Prod` (structural fold over all vertices — the definitional realization of the pinned `∏_{u ∈ V τ} x'([u])` RHS, avoiding 40.2's not-yet-integrated `vertices` machinery), `gwWeight` (List-accepted `(cs.map (fun c => x (labelOf c))).prod` + Finset-filter rejected `((gammaPlus vbl a).filter (fun j => j ∉ cs.map labelOf)).prod (fun j => 1 - x j)`, no division), `IsWitnessTree` (children labels in Γ⁺(parent), inclusive — the same-label treeElig disjunct is harmless); 5 helper lemmas (`labelOf_mem_labels`, `labelOf_mem_labels_of_mem_childrenOf`, `labels_subset_of_mem_childrenOf`, `x_labelOf_ne_zero_of_mem_childrenOf`, `hx0_transfer`). `gwWeight_telescope` proved by `WitnessTree.rec` (motive_1 per tree, motive_2 per child list): Step A child-product cancellation (`List.prod_map_mul` + `List.map_congr_left` + `field_simp` on hxc), Step B rejection-product telescope (`List.prod_toFinset` under the Proper nodup, the Γ⁺ filter decomposition via `Finset.prod_filter_mul_prod_filter_not`, `gammaPlus` = insert-i-neighborFinset via `mem_overlap_neighborFinset`), Step C root cancellation (`field_simp [hxi]`); closing calc chain. Deviation: the Survey subagent stalled and was killed; the orchestrator did the survey legwork and wrote the proof directly. | Independently verified: tmp (213 lines, ≤ 500) compiles clean (`lake env lean` exit 0, 0 warnings); no sorry/axiom/admit/native_decide. Proof correct and complete — properness (`hcnodup`) feeds `List.prod_toFinset` exactly where needed and `IsWitnessTree` (`hcwit`) feeds the filter-eq-finset step. Integrated into new `StatsMLlib/Probability/MoserTardos/GaltonWatson.lean` (copyright header, `/-!` docstring with Main definitions/results/References; `noncomputable section`, `namespace MoserTardos`, `open WitnessTree`, `open scoped BigOperators`; `universe u` + `variable {ι κ : Type u}` — the pinning required because VariableModel's overlapGraph pins κ to ι's universe, and the house `set_option autoImplicit false` made the tmp's implicit universe declaration fail — this surfaced at integration and was fixed); helper-lemma section kept instance-free before the `variable [DecidableEq ι] [DecidableEq κ] [Fintype ι]` line; one 109-char line rewrapped; tmp deleted. `lake build StatsMLlib.Probability.MoserTardos.GaltonWatson` OK (1860 jobs), LSP 0 diagnostics. Note: the pinned RHS `∏_{u ∈ V τ} x'([u])` is realized as `x'Prod` (definitionally the same fold). 50.2/50.3 will extend this module. | `tmp_gw_weight.lean` |

### 50.2. Fintype 𝒯_i(N)

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/GaltonWatson.lean`
    - note: **𝒯_i(N) stays PROPER trees — pinned by 40.3's design decision (option (a)).**
      The coupling takes no `IsGood` hypothesis (internal `by_cases`; non-good trees have
      an empty occurrence event), so the sum domain needs no goodness. Option (b) (good
      trees) is rejected: 50.3's multinomial factorization reconstructs trees from
      child-label sets `C ⊆ Γ⁺(i)`, which does not enforce `IsGood`'s global same-depth
      disjointness — the height-induction sum would overcount against a good-tree domain.
      See 40.3.
- **informal**
    - statement: |
        Finiteness of bounded witness trees (survey B E20; difficulty Medium, est. ~120
        lines; critical path ★): `treesFinset` / a Fintype instance for
        `𝒯_i(N) := {τ : WitnessTree ι // Proper τ ∧ size τ ≤ N ∧ labelOf τ = i}` — proper
        witness trees rooted at `i` with ≤ N vertices.
        **Mechanism compile-tested (survey A §3.2, 65 lines):** `Fintype.ofInjective` into
        `ι × (Fin n → Option T)` (children padded with `none`; `T = {t // t.size ≤ n}`)
        plus support lemmas `size_le_sum_of_mem`, `length_le_sizeSum`; the padded-list
        injectivity via `List.ext_getElem?'` + `Option.some.inj`; `Fintype.subtype` +
        `classical` for the `Proper ∧ size ≤ N ∧ rooted` subtype. **No
        `Fintype (List α)` / `Fintype (Multiset α)` exists in mathlib** (survey A §2.5 —
        only `fintypeNodupList`, `Mathlib/Data/Fintype/List.lean:58`); the encoding is
        mandatory. The height-bounded variant (for the GW induction, 50.3) uses the same
        mechanism (children of height ≤ h have height ≤ h−1; untested but low risk —
        budget for it).
    - proof: |
        Definition via the encoding; the injectivity proof is the compile-tested survey A
        §3.2 transcript. Iteration notes (all resolved there): `node` keyword patterns
        stay in a namespace; no field projections; `rw` on subtype equalities fails with
        motive errors — close with `Subtype.ext` + `congrArg (node l₁)`.
- **prep**
    - `Fintype.ofInjective` — `Mathlib/Data/Fintype/OfMap.lean:67` — VERIFIED
      (2026-08-16): `[Fintype β] (f : α → β) (H : Function.Injective f) : Fintype α`,
      noncomputable.
    - `Subtype.fintype` — `Mathlib/Data/Fintype/Sets.lean:260` — **NAME CORRECTION**
      (2026-08-16): the subtype-finiteness entry is the INSTANCE
      `Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype {x // p x}`.
      There is no `Fintype.subtype` in `Data/Fintype/Basic.lean` (the name exists at
      `Data/Fintype/Defs.lean:266` but takes a Finset + membership proof — not what is
      wanted here). Use `classical` + `inferInstance` (or `haveI := fintypeProperSizeLE N`).
    - `Option.fintype` — `Mathlib/Data/Fintype/Option.lean:29` — name corrected: an
      ANONYMOUS instance (auto-named `instFintypeOption`), requires only `[Fintype α]`;
      synthesized by typeclass, never referenced by name.
    - `Pi.instFintype` — `Mathlib/Data/Fintype/Pi.lean:134` — VERIFIED: needs
      `[DecidableEq α]` on the index type (fine for `Fin n`).
    - `Prod.fintype` — `Mathlib/Data/Fintype/Prod.lean:45` — name corrected: anonymous
      instance `instFintypeProd`, requires only `[Fintype α] [Fintype β]`.
    - `List.ext_getElem?'` — `Mathlib/Data/List/Basic.lean:623` — VERIFIED: binder is
      `∀ n < max l₁.length l₂.length, l₁[n]? = l₂[n]?` (the transcript's
      `lt_of_lt_of_le hi (max_le hlen₁ hlen₂)` matches exactly).
    - `List.getElem?_eq_getElem` — core List API — VERIFIED: `(h : i < l.length) :
      l[i]? = some l[i]`.
    - `List.attach_map_subtype_val` — core `Init/Data/List/Attach.lean` — VERIFIED:
      `List.map Subtype.val l.attach = l`.
    - `List.length_le_sum_of_one_le` —
      `Mathlib/Algebra/BigOperators/Group/List/Basic.lean:518` — VERIFIED:
      `(L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum`.
    - **Import trap (survey A risk 1) — RESOLVED (2026-08-16, compile probe
      `/tmp/mt_50.2_probe.lean`):** the existing import chain
      (GaltonWatson → WitnessTree/VariableModel → `MeasureTheory.Constructions.Pi` +
      `SimpleGraph.Finite`) already makes `Fintype (ι × (Fin n → Option T))` AND
      `Subtype.fintype` synthesize — the tmp needs NO extra
      `Mathlib.Data.Fintype.{Option,Pi,Prod}` imports.
    - **Item-local support lemmas (port from survey A §3.2 — do NOT exist in the repo):**
      `size_le_sum_of_mem` (`c ∈ cs → size c ≤ (cs.map size).sum`) and
      `length_le_sizeSum` (`cs.length ≤ (cs.map size).sum`, via
      `List.length_le_sum_of_one_le` + `WitnessTree.size_pos`, which exists).
    - `Subtype.val_injective` (core) — the embedding for `treesFinset`'s `Finset.map`.
    - Internal deps (survey B §5): item 30.1 (`WitnessTree` + `instDecidableEq`).
      Note: 30.7's `T_size_le_N` is NOT reusable here — it bounds the occurring tree of
      an execution (needs `log`/`R`/`hpick`); 50.2's Fintype must cover ALL proper trees
      with ≤ N vertices unconditionally.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-16 | 1 / 15 | done | In GaltonWatson.lean (inside the `[DecidableEq ι] [DecidableEq κ] [Fintype ι]` section, after `gwWeight_telescope`), define: (1) `fintypeProperSizeLE (N : ℕ) : Fintype {τ : WitnessTree ι // Proper τ ∧ size τ ≤ N}` — port of the survey A §3.2 compile-tested encoding (induction on N; succ case `Fintype.ofInjective` into `ι × (Fin n → Option T)` with children padded by `none`, injectivity via `List.ext_getElem?'` + `Option.some.inj`); (2) `treesFintype (i : ι) (N : ℕ) : Fintype {τ : WitnessTree ι // Proper τ ∧ size τ ≤ N ∧ labelOf τ = i}` — one `Subtype.fintype` step with `classical` on top of (1); (3) `treesFinset (i : ι) (N : ℕ) : Finset (WitnessTree ι) := (treesFintype i N).elems.map ⟨Subtype.val, Subtype.val_injective⟩`; plus the two support lemmas `size_le_sum_of_mem`/`length_le_sizeSum` ported verbatim from the transcript (using `size_mk`/`size_pos`). Porting deltas: `node`→`mk`, `IsProper`→`Proper` (rides along in the subtype, unused by the encoding; child properness via `proper_mk`), 3-field subtype so `ht₁`→`ht₁.2`, `simp [size]`→`simp [size_mk]`, `congrArg (node l₁)`→`congrArg (mk l₁)`; watch the `Subtype.mk`/`WitnessTree.mk` constructor-name collision in `cases` patterns (use `rcases` if ambiguous). No `T_size_le_N` reuse (execution-specific). | Setup completed the entire proof beyond its stub mandate (the Proof phase is skipped as redundant). Proved: `size_le_sum_of_mem`/`length_le_sizeSum` (verbatim ports of the survey A §3.2 support lemmas); `fintypeProperSizeLE` by induction on N with the pinned encoding (`Fintype.ofInjective` into `ι × (Fin n → Option T)`, injectivity via `List.ext_getElem?'` + `Option.some.inj`); `treesFintype` as one `Fintype.ofInjective` restriction step of the forgetful map — NOT `Subtype.fintype`, which would need a nonexistent `Fintype (WitnessTree ι)` (supersedes the Goal column's wording); `treesFinset` via `.elems.map ⟨Subtype.val, Subtype.val_injective⟩`. Both Fintype defs carry `@[implicit_reducible]` — required by Lean 4.32.0 core for defs of class type. tmp compiled: `lake env lean` exit 0, 0 warnings, no sorries. | Independently verified: `lake env lean` exit 0, no sorry/axiom/admit, all lines ≤ 100 chars, `@[implicit_reducible]` present on both Fintype defs. Proof correct and complete. Integrated into `GaltonWatson.lean`: support lemmas appended to the instance-free helper-lemmas section; `fintypeProperSizeLE`/`treesFintype`/`treesFinset` in a new `## Fintype of bounded proper trees` section after `gwWeight_telescope`; module docstring updated (3 bullets in Main definitions; intro sentence — only 50.3 remains). tmp deleted. Integrated file: `lake env lean` exit 0, 0 LSP diagnostics. | `tmp_trees_finset.lean` |

### 50.3. gwWeight_sum_le_one

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/GaltonWatson.lean`
- **informal**
    - statement: |
        The Galton–Watson sum bound (survey B E21, notes §16–18; difficulty Med–Hard, est.
        ~150 lines; critical path ★):
        `gwWeight_sum_le_one : ∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ 1` (ℝ sum — the `ofReal` form
        for the ENNReal chain in 60.2 is a one-line bridge).
    - proof: |
        (survey B §3.4) Height-`h` induction on
        `S_h(i) := ∑_{τ rooted at i, height τ ≤ h} gwWeight τ`. The recurrence
        `S_{h+1}(i) = ∏_{B ∈ Γ⁺(i)} [(1 - x B) + x B · S_h(B)]` comes from the multinomial
        factorization over child-label sets `C ⊆ Γ⁺(i)`
        (`∏_B (a_B + b_B) = ∑_{C ⊆ S} ∏_{B∈C} b_B · ∏_{B∉C} a_B`; mathlib `prod_sum`,
        `Mathlib/Algebra/BigOperators/Fin.lean` — exact application TBC at Survey).
        Subtree heights line up (`height ≤ h` in child coordinates ⟺ `height ≤ h+1`
        globally), and the sum ranges over proper trees automatically since `C` is a *set*.
        Then `0 ≤ x B ≤ 1` and `S_h(B) ≤ 1` give `(1 - x B) + x B · S_h(B) ≤ 1`; base
        `S_0(i) = ∏_{B ∈ Γ⁺(i)} (1 - x B) ≤ 1`. Since `height τ ≤ size τ - 1 ≤ N - 1`:
        `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ S_N(i) ≤ 1`.
- **prep**
    - `Finset.prod_add` — **the multinomial** (`Mathlib/Algebra/BigOperators/Ring/Finset.lean:172`;
      replaces the prep's old `Finset.prod_sum`-in-Fin.lean entry, which was mislocated):
      `∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i`.
      Applied with `s = gammaPlus vbl i`, `f B = x B * S_h(B)`, `g B = 1 - x B`.
    - `Finset.prod_sum` — the **dependent product-of-sums** (tuple factorization),
      `Mathlib/Algebra/BigOperators/Ring/Finset.lean:124`:
      `∏ a ∈ s, ∑ b ∈ t a, f a b = ∑ p ∈ s.pi t, ∏ x ∈ s.attach, f x.1 (p x.1 x.2)`.
      Applied with `s = C`, `t = fun B => gwFinsetHeight vbl B h`, `f _ τ = gwWeight vbl x τ`
      — the `s.pi t` domain matches the assemble domain exactly (no reindexing).
    - `Finset.pi` — `Mathlib/Data/Finset/Pi.lean:50`:
      `pi (s : Finset α) (t : ∀ a, Finset (β a)) : Finset (∀ a ∈ s, β a)` (partial
      functions); `mem_pi : f ∈ s.pi t ↔ ∀ a (h : a ∈ s), f a h ∈ t a`.
    - `Finset.prod_le_prod` — `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:38`
      `(h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i)` — **replaces**
      `Finset.prod_le_prod_of_subset_of_le_one'` (Group/Finset.lean:141), which needs
      `[MulLeftMono N]` — NOT available for ℝ (no global covariant multiplication), so it
      is unusable here. The `≤ 1` steps use `Finset.prod_le_prod` with `g := 1` +
      `prod_const_one`.
    - `Finset.toList` — `Mathlib/Data/Finset/Dedup.lean:163` (noncomputable ✓, file is
      `noncomputable section`): the canonical children list is
      `C.attach.toList.map (fun x => f x.1 x.2)` — pure `List.map` of the finset's internal
      order, avoiding `Multiset.toList`-vs-`map` alignment entirely (probe-compiled ✓).
    - `List.prod_toFinset` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:1048`
      (as used in 50.1): `(hl : l.Nodup) → l.toFinset.prod f = (l.map f).prod`.
    - `Finset.prod_filter_mul_prod_filter_not` — `Mathlib/Algebra/BigOperators/Fin.lean`
      (as used in 50.1, Step B): the rejection-filter decomposition `Γ⁺ \ C`.
    - `Finset.sum_biUnion` / `Finset.sum_image` — to_additive of `prod_biUnion`
      (Group/Finset/Basic.lean:221) / `prod_image` (:95); `sum_image` needs the injectivity
      of `(C, f) ↦ mk i (C.attach.toList.map f)` (recover `C` via labels-toFinset —
      needs `labelOf_mem_gwFinsetHeight` — and `f` via `List.getElem_map` + attach-nodup).
    - `Finset.prod_attach`, `Finset.sum_mul`, `Finset.prod_const_one`,
      `Finset.prod_nonneg` / `List.prod_nonneg` (GroupWithZero), `Finset.sum_nonneg`,
      `mul_le_of_le_one_left`, `add_le_add_left`, `mul_nonneg` — the `≤ 1` and `≥ 0`
      factor steps.
    - **Survey corrections (2026-08-17, critical — changes the item's shape):**
      (1) **The pinned statement `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ 1` is FALSE as written.**
      `WitnessTree` children are an ORDERED list; each unordered skeleton of branching `d`
      contributes `d!` trees with equal `gwWeight`. Counterexample: star graph — center `i`,
      leaves `j₁..j₅₀` each overlapping only `i`, all `x = 1/2`, `N = 52`:
      `∑_{τ witness, height ≤ 1, rooted i} gwWeight τ = 2⁻⁵¹ · Σ_k C(50,k) k! 4⁻ᵏ ≈ 10²⁰ > 1`.
      (Without the witness filter it also fails: chain `i→j→j→…` with `j ∉ Γ⁺(i)` gives
      `(1-x i)(1+x j)`.) The notes' 𝒯_A are the trees the Γ⁺-indexed GW process can
      PRODUCE — children indexed by labels, i.e. canonical order. (2) The multinomial over
      child-label SETS therefore requires a canonical-order domain. **Fix: the induction
      domain is the recursive finset `gwFinsetHeight vbl i h`** of canonical witness trees
      (children = `C.attach.toList.map f` for `C ⊆ Γ⁺(i)`, `f : ∀ B ∈ C, …`), so the
      bijection to `Σ_{C ⊆ Γ⁺(i)} Π_{B∈C} …` is BY CONSTRUCTION — no height/size lemmas
      needed inside 50.3 (the height function is not even used). (3) **Consequences for
      60.1/60.2 (flag for their Surveys):** the counting identity must partition by the
      canonical representative (`T(ω,t)` reordered), the coupling must bound
      `μN{∃t, T = reordering of σ} ≤ treeProd σ` (via check-event invariance under child
      reordering — new 40.3-side lemma), and `height τ ≤ size τ - 1` moves to 60.1's
      partition proof (`treeAt_size_le` ⇒ representative ∈ `gwFinsetHeight vbl i (N-1)`).
      The telescope (50.1) is applied to `σ ∈ gwFinsetHeight` with the domain invariants
      `labelOf_mem_gwFinsetHeight` / `proper_of_mem_gwFinsetHeight` /
      `witness_of_mem_gwFinsetHeight` (part of 50.3's statement set).
    - Internal deps (survey B §5): items 50.1 (`gwWeight`), 50.2 (`treesFinset` — only
      `gammaPlus`-side infrastructure is used; the `treesFinset` filter approach of the
      harness prompt is dropped — see the counterexample above).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-17 | 1 / 15 | done | Write the full corrected statement set in GaltonWatson.lean (probe-compiled ✓): `gwFinsetHeight vbl i : ℕ → Finset (WitnessTree ι)` — the recursive canonical-witness-tree finset, `| 0 => {mk i []} | h+1 => (gammaPlus vbl i).powerset.biUnion fun C => (C.pi (fun B => gwFinsetHeight vbl B h)).image (fun f => mk i (C.attach.toList.map fun x => f x.1 x.2))`; `gwSumHeight vbl x i h := ∑ τ ∈ gwFinsetHeight vbl i h, gwWeight vbl x τ`; the three domain invariants `labelOf_mem_gwFinsetHeight`/`proper_of_mem_gwFinsetHeight`/`witness_of_mem_gwFinsetHeight`; `gwWeight_nonneg (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j ≤ 1)`; base `gwSumHeight_zero : gwSumHeight vbl x i 0 = ∏ B ∈ gammaPlus vbl i, (1 - x B)`; the recurrence `gwSumHeight_succ : gwSumHeight vbl x i (h+1) = ∏ B ∈ gammaPlus vbl i, ((1 - x B) + x B * gwSumHeight vbl x B h)` — proved by `sum_biUnion` + `sum_image` (assemble injectivity via labels-toFinset + `List.getElem_map` + attach-nodup), per-`(C,f)` weight identity `gwWeight (mk i (C.attach.toList.map f)) = (∏ B ∈ C, x B * gwWeight (f B hB)) * ∏ B ∈ gammaPlus vbl i \ C, (1 - x B)` (`List.prod_toFinset` + `prod_filter_mul_prod_filter_not`), tuple factorization via `Finset.prod_sum` (Ring/Finset.lean:124) + `prod_attach` + `sum_mul`, multinomial via `Finset.prod_add` (Ring/Finset.lean:172); then `gwSumHeight_le_one` by induction on `h` (`Finset.prod_le_prod` with `g := 1`, factors nonneg via `gwWeight_nonneg`/`sum_nonneg`, factors ≤ 1 via `mul_le_of_le_one_left (hx0 B) (ih B)` + `add_le_add_left`); headline `gwWeight_sum_le_one : ∑ τ ∈ gwFinsetHeight vbl i h, gwWeight vbl x τ ≤ 1`. NOTE the correction: the original `∑_{τ ∈ 𝒯_i(N)}` statement is false for ordered trees (star counterexample in prep) — the bound is over the canonical finset; 60.1/60.2 adaptation flagged in prep. | All 8 pinned statements proved: `gwFinsetHeight`/`gwSumHeight` defs; domain invariants `labelOf_mem_gwFinsetHeight`/`proper_of_mem_gwFinsetHeight`/`witness_of_mem_gwFinsetHeight` (induction on h, `mem_biUnion`/`mem_image` rcases; properness via `proper_mk` + attach-nodup map); `gwWeight_nonneg` (`WitnessTree.rec`, motive_2 over child lists); `gwSumHeight_zero` (`sum_singleton` + `filter_true`); the multinomial `gwSumHeight_succ` — `sum_biUnion` over the powerset with a pairwise-disjointness proof (labels-toFinset recovery `hlabels₁/₂` + `toFinset_attach_map_val`), `sum_image` via `assemble_injective` (child-list equality via `congrArg childrenOf` + nodup-list induction `map_eq_of_mem_of_map_eq`), per-`(C,f)` weight identity `gwWeight_assemble` (`List.prod_toFinset` + filter-eq-sdiff via `mem_map_attach_val`), tuple factorization `sum_pi_gwWeight` (`Finset.prod_sum` + `prod_congr` + `mul_sum`), multinomial `Finset.prod_add` (after an `add_comm` pre-rewrite); `gwSumHeight_le_one` by induction via `Finset.prod_le_one` (base: `sub_nonneg.mpr (hx1 B)` + `sub_le_self`; succ: `add_nonneg` + `mul_nonneg`, then `mul_le_mul_of_nonneg_left (ih B) (hx0 B)` + nlinarith) — SIMPLER than the prep's `Finset.prod_le_prod` with `g := 1` route (both valid; `prod_le_one` hits the ≤ 1 target directly); headline `gwWeight_sum_le_one` by `simpa [gwSumHeight]`. 7 private helpers: `map_eq_of_mem_of_map_eq`, `mem_map_attach_val`, `toFinset_attach_map_val`, `toFinset_of_toList`, `assemble_injective`, `gwWeight_assemble`, `sum_pi_gwWeight` (with `omit`-annotated instance hygiene). 415 lines, ≤ 100 chars/line. | Independently verified: tmp compiles clean (`lake env lean` exit 0, 0 warnings; LSP 0 diagnostics), no sorry/axiom/admit/native_decide; `gwSumHeight_succ` statement and `gwWeight_sum_le_one` hypothesis shape match the Survey's pinned recurrence/shape exactly. Proof correct and complete. Integrated into `GaltonWatson.lean` as a new `## The canonical Galton–Watson tree domain and its sum (50.3)` section after `treesFinset` (same `[DecidableEq ι] [DecidableEq κ] [Fintype ι]` scope); privates stay private, docstrings kept, tmp header rationale condensed into the section docstring (counterexample detail stays in the blueprint prep); module docstring updated (2 new definition bullets, 1 new result bullet; intro now covers 50.1–50.3). Integrated file: `lake env lean` exit 0, 0 LSP diagnostics; nothing else imports GaltonWatson, so no downstream impact. tmp deleted. | `tmp_gw_sum.lean` |

---
## 60. Main Theorem and Corollaries

### 60.1. countLog_eq_sum_tree_indicators

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Basic.lean`
    - note: `Basic.lean` is created by Setup with the module `/-!` docstring
      (`## Main definitions` / `## Main results` / `## References`) and the public-API
      re-exports on first touch of this group.
- **informal**
    - statement: |
        The counting identity (survey B F22, notes §13; difficulty Medium, est. ~80 lines;
        critical path ★): pointwise,
        `countLog (log vbl A pick hpick) ω i = Σ_{τ ∈ 𝒯_i(N)}, (∃ t < R ω, T … ω t = τ)`
        — the indicator-sum form (sum of booleans as ℕ, or indicator functions — exact
        shape pinned at Survey). Via `treeAt_injective` (30.6) the map `t ↦ T(ω,t)` from
        `{t < N : log ω t = some i}` (equivalently `{t < R ω : …}`, 20.4) into `𝒯_i(N)`
        is injective, turning the count into a sum of indicators.
    - proof: |
        Finset card ↔ sum of booleans (`Finset.sum_boole`-style) + the injective
        correspondence (30.6) + `treeAt_size_le` (30.7) membership into `𝒯_i(N)`.
- **prep**
    - `Finset.card_eq_sum_card_fiberwise` —
      `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:979`
      (`[DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M}
      (H : (s : Set ι).MapsTo f t) : s.card = ∑ b ∈ t, (s.filter fun a => f a = b).card`)
      — the fiberwise partition step (applied with `f := fun t => canon (T … ω t)`,
      `s :=` the `t < R` log-filter, `t := gwFinsetHeight vbl i (N-1)`); **replaces**
      the informal's `Finset.sum_boole` route (superseded — `countLog` is already a card,
      and the fiber-card form needs NO injectivity).
    - `List.Perm.prod_eq` and its `to_additive` `List.Perm.sum_eq` —
      `Mathlib/Algebra/BigOperators/Group/List/Basic.lean:250` (`(h : Perm l₁ l₂) →
      l₁.prod = l₂.prod`) — the perm-invariance input for `size_canon` and (60.2-flagged)
      `treeProfile_canon`.
    - `List.find?_eq_none` / `List.find?_eq_some_iff_append` / `List.find?_some` — stdlib
      `Init/Data/List/Find.lean:239/242/297`; note the iff shape
      `xs.find? p = some b ↔ p b ∧ ∃ as bs, xs = as ++ b :: bs ∧ ∀ a ∈ as, !p a`
      (pattern `⟨hp, as, bs, hcs, hpc⟩`) — the `canon` child-selection lemmas.
    - `List.mem_toFinset` — the `x ∈ (cs.map labelOf).toFinset ↔ …` bridge (used in
      `canon`'s `decreasing_by` and in `canon_mem_gwFinsetHeight`'s `C ⊆ Γ⁺(a)` step).
    - `List.le_sum_of_mem` (as in Coupling.lean) + `Option.ne_none_iff_exists` +
      `Option.getD_some` — the `canon` termination/selection cases.
    - `List.foldl_max_eq_max` — stdlib `Init/Data/List/MinMax.lean:463`
      (`l.foldl (init := a) max = max a (l.max?.getD a)`) — for `height_le_size_pred`;
      the per-child bound `height c ≤ (cs.map height).foldl max 0` is a small local
      helper (list induction), also consumed by `canon_mem_gwFinsetHeight`'s induction.
    - `Nat.sub_le_sub_right` — `size (T … t) - 1 ≤ N - 1` from `T_size_le_N` (30.7).
    - `Finset.mem_biUnion` / `Finset.mem_image` / `Finset.mem_powerset` / `Finset.mem_pi` —
      the `gwFinsetHeight` membership decomposition in `canon_mem_gwFinsetHeight`
      (the `C := (cs.map labelOf).toFinset` image witness; the `pi`-tuple is
      `fun B hB => canon ((cs.find? (fun c => labelOf c = B)).getD (mk B []))`, matching
      `canon`'s def exactly — the C-subset step uses the `IsWitnessTree` hypothesis).
    - **Survey corrections (2026-08-17 — the 50.3 re-shaping applied; all statement
      shapes probe-compiled ✓):**
      (1) The RHS domain is the CANONICAL finset `gwFinsetHeight vbl i (N-1)` (NOT
      `treesFinset i N` — 50.3's counterexample: the ordered-tree sum is false), and the
      partition is by the canonical representative of the occurring tree.
      (2) NEW def `canon : WitnessTree ι → WitnessTree ι` with only `[DecidableEq ι]`
      (NO `[LinearOrder ι]` — pinned design decision (1)): children reordered into the
      internal order of their label finset — the SAME order `gwFinsetHeight` assembles
      with (`C.attach.toList.map f`), so membership matches by construction; the
      child-selection fallback `getD (mk B [])` is unreachable on proper trees; WF on
      `size` with a probe-verified decreasing proof. Section context for 60.1:
      `{ι κ : Type u} [DecidableEq ι] [DecidableEq κ] [Inhabited ι] [Fintype ι]`
      (`[Fintype ι]` for `gwFinsetHeight`/`gammaPlus`; `[Inhabited ι]` for `T`).
      (3) The pinned headline is the **fiber-card form** (see log row). Injective
      partition machinery (`treeAt_injective`, 30.6) is NOT consumed; the injectivity
      of `t ↦ canon (T … t)` on genuine times is free via `size (T t) = t + 1` — moved
      to 60.2's `T_size_eq` flag.
      (4) `size_canon` carries `(hprop : Proper τ)` — load-bearing: canon drops
      duplicate-label children, so the size/perm argument needs the label `Nodup`.
      `labelOf_canon` is unconditional.
      (5) `height_le_size_pred : height τ ≤ size τ - 1` is the 50.3-moved lemma, proved
      here in Basic.lean (tree induction; children bound via the foldl-max helper).
      (6) **FLAGS for 60.2's Survey (the 40.3-side re-shaping, pinned here):** (a) NEW
      coupling lemma `coupling_canon (hA : ∀ i, MeasurableSet (A i)) (hN : size σ ≤ N) :
      μN N μ {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ} ≤
      treeProd (μ := μ) A σ` — good branch: `occurrence_implies_check` (40.3) + NEW
      `check_canon {τ} (hprop : Proper τ) (hN : size τ ≤ N) (hNc : size (canon τ) ≤ N)
      (ω) : check vbl A hdet hNc ω ↔ check vbl A hdet hN ω` (needs NEW helper
      `treeProfile_canon (hprop : Proper τ) : treeProfile vbl (canon τ) j d =
      treeProfile vbl τ j d` via `List.Perm.sum_eq` — Proper needed, dropped
      duplicate-label children break profile equality) + `check_probability` (40.2);
      non-good branch: NEW `isGood_canon : IsGood vbl τ → IsGood vbl (canon τ)` (the
      path reindexing through the child reordering — the heavy piece) + the
      empty-event argument as in `coupling`. (b) `treeProd` and `gwWeight` need NO
      invariance lemmas — 60.2 applies hLLL and the telescope (50.1) directly to the
      canonical `σ` (with the three domain invariants from 50.3). (c) NEW
      `T_size_eq (ht : t < R …) : size (T … t) = t + 1` (fold induction +
      `size_attachBelow`) for the fiber-card ≤ 1 bound in 60.2's lintegral step.
    - Internal deps (survey B §5): items 30.7 (`T_isGood`, `T_size_le_N`), 50.3
      (`gwFinsetHeight` + `labelOf_mem_gwFinsetHeight`/`proper_of_mem_gwFinsetHeight`/
      `witness_of_mem_gwFinsetHeight`), 20.4 (`countLog`/`log`/`log_ne_none_iff_lt_R`),
      30.6's `T_root_label`. (30.6's `treeAt_injective` and 50.2's `treesFinset` are NOT
      consumed — superseded by the canon partition.)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-17 | 1 / 15 | done | Write the 50.3-re-shaped statement set in Basic.lean (probe-compiled ✓ — canon def + all 7 statement shapes type-check at `/tmp`): (1) `canon : WitnessTree ι → WitnessTree ι` — at every node the children reordered into the internal order of their label finset, `canon (mk a cs) = mk a (((cs.map labelOf).toFinset).attach.toList.map (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD (mk x.1 []))))` (only `[DecidableEq ι]`, NO `[LinearOrder ι]` — the order matches `gwFinsetHeight`'s `C.attach.toList.map f` assembly by construction; well-founded on `size`, decreasing proof probe-done via `mem_toFinset` + `find?_eq_some_iff_append` + `le_sum_of_mem`); (2) `labelOf_canon` (unconditional) + `size_canon (hprop : Proper τ)` (Proper load-bearing — canon drops duplicate-label children); (3) `height_le_size_pred : height τ ≤ size τ - 1` (the 50.3-moved lemma, tree induction + local foldl-max bound); (4) `treeAt_isWitnessTree`/`T_isWitnessTree` (NEW — treeElig attachment ⟹ `IsWitnessTree`; fold invariant via 30.2's `attachBelow_spec` + the edge-eligibility transport `treeElig (s,i) (s',i') ⟹ i ∈ gammaPlus vbl i'`); (5) `canon_mem_gwFinsetHeight (hprop : Proper τ) (hwit : IsWitnessTree vbl τ) (hheight : height τ ≤ h) : canon τ ∈ gwFinsetHeight vbl (labelOf τ) h` (induction on h; uniform `C := (cs.map labelOf).toFinset` image decomposition, no leaf case-split needed); (6) `log_eq_some_iff_labelOf_T (ht : t < R …) (i) : log … t = some i ↔ labelOf (T … t) = i` (T_root_label + unfold log); (7) headline `countLog_eq_sum_tree_indicators : countLog (log vbl A pick hpick) ω i = ∑ σ ∈ gwFinsetHeight vbl i (N - 1), ((Finset.range (R vbl A pick hpick ω)).filter (fun t => canon (T vbl A pick hpick ω t) = σ)).card` — proof via the filter-congr bridge (countLog = card of the `t < R` log-filter; per-`t`: `log t = some i ↔ t < R ∧ canon (T t) ∈ gwFinsetHeight vbl i (N-1)` — forward by T_root_label + (5) with hprop/hwit from `T_isGood`/`T_isWitnessTree` and hheight from (3) + `T_size_le_N`; backward by `labelOf_mem_gwFinsetHeight` + `labelOf_canon` + (6)) then `Finset.card_eq_sum_card_fiberwise` (fiber-card form — NO injectivity needed; injectivity of `t ↦ canon (T t)` on genuine times is free via `size (T t) = t + 1`, deferred to 60.2's `T_size_eq` flag) and the pointwise fiber-filter agreement. 60.2 re-shaping flags pinned in prep: `coupling_canon` / `check_canon` / `treeProfile_canon` / `isGood_canon` / `T_size_eq`; `treeProd`/`gwWeight` need NO invariance lemmas. | All 8 pinned statements proved: `canon` (real body, well-founded on `size`, decreasing via `mem_toFinset` + `mem_map` + `size_le_sum_of_mem`); `labelOf_canon` (`rw [canon.eq_1]; rfl`); `size_canon` (`WitnessTree.rec` with motive_2 over child lists; the canonical children list is a `List.Perm` of the original via `canonChildren_perm` under the Proper label-Nodup, sizes commute via `List.Perm.sum_eq` under `List.Perm.map size`); `height_le_size_pred` (tree induction + local foldl-max glue `foldl_max_succ_le_sum`); `treeAt_isWitnessTree`/`T_isWitnessTree` (fold invariant `foldr_forgetTime_isWitness` — list induction on the fold's range list with the accumulated tree generalized — over `forgetTime_attachBelow_isWitness` (tree induction) built on the equation-lemma restatement `attachBelow_mk_treeElig` (`rw [WitnessTree.attachBelow.eq_1]; rfl`, the 30.6/30.7 re-derivation precedent — 30.2's privates are file-scoped) + the pinned edge-eligibility transport `treeElig_gammaPlus`; `canon_mem_gwFinsetHeight` (induction on h, uniform `C := (cs.map labelOf).toFinset` image decomposition, child descent via `height_le_foldl_max` + the h₀ bound); `log_eq_some_iff_labelOf_T` (forward `T_root_label`; backward `log_ne_none_iff_lt_R` + `treeAt_root_label`); headline `countLog_eq_sum_card` (statement-exact to the pinned fiber-card form) via the filter-congr bridge + `Finset.card_eq_sum_card_fiberwise` + pointwise fiber-filter agreement. NOTE: the Proof agent was killed after completing all 8 sorries, mid-cosmetic-refactor — the on-disk tmp was left broken (27 errors: dropped `vbl` args on section-variable calls, dropped `(hp := .root)`, `and_assoc` removed from a `simp only`, an obsolete `unfold log` block, etc.); the Review repaired the cosmetic damage — the repaired state is the verified deliverable. | Independently verified. On receipt the tmp did NOT compile (`lake env lean` exit 1, 27 errors + 5 warnings — the interrupted cosmetic refactor, contradicting the orchestrator's pre-refactor check); all repaired by the Review (restored `vbl` arguments on `treeElig_gammaPlus`/`attachBelow_mk_treeElig`/`forgetTime_attachInFirst_*` calls, `(hp := .root)`, `List.mem_map.mp` wrappers, `rw [← hdl]`, `ih (τ := c')`, `and_assoc`; replaced the obsolete `unfold log` block by `congrArg some hj`; IsWitnessTree values constructed via the house `rw [IsWitnessTree]; constructor` pattern — projections/`⟨⟩` on `IsWitnessTree` values don't reduce in this toolchain, the GaltonWatson 50.3 idiom). Final tmp: `lake env lean` exit 0, 0 errors 0 warnings; no sorry/axiom/admit/native_decide; all lines ≤ 100. Statements spot-checked against the Survey pins: `countLog_eq_sum_card` matches the pinned fiber-card form exactly (named per the orchestrator; the Survey's name `countLog_eq_sum_tree_indicators` differs), `canon` matches its pinned equation; the two risk-flagged proofs are real — `size_canon`'s Perm argument goes through `List.Perm.sum_eq` (`canonChildren_perm` under Proper), `treeAt_isWitnessTree`'s fold invariant is the foldr list induction over the public attachBelow equations. Integrated: new module `Basic.lean` (house style: copyright header, module `/-!` docstring with `## Main definitions`/`## Main results`, `noncomputable section`, `namespace MoserTardos`, `universe u v`; privates kept private, docstrings kept, debug `#check canon.eq_1` dropped); `lake env lean` 0 diagnostics, `lake build StatsMLlib.Probability.MoserTardos.Basic` OK (1861 jobs). tmp deleted. | `tmp_count_identity.lean` |

### 60.2. moserTardos_bound

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Basic.lean`
- **informal**
    - statement: |
        **THE MAIN THEOREM** (survey B F23, notes §15–18 Thm 5.1 = arXiv:0903.0544 Thm 1.2;
        difficulty **Hard**, est. ~200 lines; critical path ★). Pinned shape (survey B
        §1.1 — full hypothesis block):
        ```lean
        theorem moserTardos_bound {N : ℕ} (Ω : κ → Type*) [∀ j, MeasurableSpace (Ω j)]
            (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
            (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
            (hdet : ∀ i, DeterminedBy (A i) (vbl i))
            (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
            (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
              (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
            (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1)
            (i : ι) :
            ∫⁻ ω : ΩN N Ω, (countLog (log vbl A pick hpick) ω i : ℝ≥0∞) ∂ μN N μ
              ≤ ENNReal.ofReal (x i / (1 - x i))
        ```
        The theorem holds for **every** `pick` — uniformity over the choice rule is free by
        parametricity (notes §4 "Fix any rule"). The `x i = 0` case needs no division; all
        arithmetic on the right is ℝ inside `ENNReal.ofReal` — **no ENNReal division occurs
        anywhere** (survey B §1.1; survey A: there is no unconditional
        `ENNReal.ofReal_div`, only `ofReal_div_of_pos`/`ofReal_div_le`).
    - proof: |
        (survey B §3.4 final chain)
        `E[N_i^{(N)}] = Σ_{τ ∈ 𝒯_i(N)} μN{∃t < R, T = τ}` (60.1, via lintegral of the
        indicator sum) `≤ Σ_τ treeProd τ` (coupling, 40.3 — applied per-τ via
        `Finset.sum_le_sum` with ONLY `hN := τ.2.2.1` from the 𝒯_i(N) membership and
        `hA`; NO `IsGood` by_cases here — 40.3 handles goodness internally, per its
        option-(a) design decision) `≤ Σ_τ ofReal (∏_u x'([u]))`
        (hLLL per node + product monotonicity; needs `0 ≤ x' i` — from `hx₀` and
        `1 - x B ≥ 0` via `hx₁`).
        **`by_cases h : x i = 0` enters exactly once, at the top of the assembly:**
        - `x i = 0` case (confirmed — no division, closes via the root factor): `hLLL`
          gives `μπ (A i) ≤ ofReal 0 = 0`, and every `τ ∈ 𝒯_i(N)` has root label `i`, so
          `treeProd τ ≤ μπ (A i) = 0`; the chain stops at
          `0 ≤ ofReal (x i/(1-x i)) = ofReal 0`. The GW block is never entered.
        - `x i > 0` case: `ofReal (∏_u x'([u])) = ofReal (x i/(1-x i)) * ofReal (gwWeight τ)`
          via the telescope (50.1) + `ENNReal.ofReal_mul`/`ofReal_div_of_pos` glue →
          `Σ_τ … ≤ ofReal (x i/(1-x i)) · 1` by the sum bound (50.3).
        Measurability obligations for the lintegral come from 20.5 (or the
        set-monotonicity alternative, survey B open question 7).
- **prep**
    - `ENNReal.ofReal_mul` — `Mathlib/Data/ENNReal/Real.lean:297` (`(hp : 0 ≤ p)`).
    - `ENNReal.ofReal_div_of_pos` — `Mathlib/Data/ENNReal/Inv.lean:952` (with `0 < 1 - x i`
      from `hx₁` — the `x i = 0` split must come first).
    - `ENNReal.ofReal_div_le` — `Mathlib/Data/ENNReal/Inv.lean:946` (inequality variant).
    - `ENNReal.ofReal_prod_of_nonneg` — `Mathlib/Data/ENNReal/BigOperators.lean:64`.
    - `lintegral_finsetSum'` — `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:341`
      (**renamed**; do NOT use the deprecated `lintegral_finset_sum` — survey A §2.3).
    - `lintegral_indicator` — `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:496`.
    - `lintegral_indicator_const` — `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:527`.
    - `Finset.sum_le_sum` — basic Finset API.
    - Internal deps (survey B §5): items 60.1 (counting identity), 40.3 (`coupling`), 50.3
      (`gwWeight_sum_le_one`), 50.1 (telescope — see correction (2), replaced by the
      multiplication bridge), 40.2 (`treeProd`), 20.5 (measurability — see correction (4),
      carried as a private slice), 10.3 (`ΩN`/`μN`/`μπ`).
    - **Survey corrections (2026-08-17 — attempt 1; the six 60.1 flags applied, three
      load-bearing corrections):**
      (1) **`T_size_eq` (60.1 flag (c)) is FALSE.** Counterexample: `ι = {a, b}` with
      `vbl a ∩ vbl b = ∅`, `A a = univ`, `A b` a non-full measurable set, `pick {a,b} = b`;
      a table ω with `b` violated at times 0,1 and `a` violated at time 2 (and `b` not
      violated at time 2 — fresh rows) gives `log = [b, b, a, …]`, `R ≥ 3`, and
      `T ω 2 = mk a []` — neither `b`-entry is `treeElig`-eligible below the `a`-root
      (`treeElig` carries no time condition; the entry only attaches in the FULL history,
      where the later `b`-entry provides the eligible vertex — the truncated tree drops
      entries whose chain runs past `t`). So `size (T ω 2) = 1 ≠ 3 = t + 1`.
      **Replacement:** `canon_T_injective {ω} {t₁ t₂} (ht₁ : t₁ < R …) (ht₂ : t₂ < R …)
      (h : canon (T … ω t₁) = canon (T … ω t₂)) : t₁ = t₂` — proved WITHOUT size
      arguments via 30.6's `treeAt_count_label`: canon-equality + `labelOf_canon` give
      `log t₁ = log t₂ = some a` (60.1's `log_eq_some_iff_labelOf_T`); the `a`-count of
      the label multiset of `T … t₂` strictly exceeds that of `T … t₁` (the occurrence at
      `t₁`; re-derive 30.6's private `length_filter_range_lt` — file-scoped), contradicting
      the multiset equality from canon-equality via new private `labels_canon
      (hprop : Proper τ) : (labels (canon τ) : Multiset ι) = labels τ` (through 60.1's
      private `canonChildren_perm`). Feeds the fiber-card ≤ 1 bound
      (`Finset.card_le_one.mpr`).
      (2) **50.1's division-form `gwWeight_telescope` is UNUSABLE here** — its
      `hx0 : ∀ j ∈ labels τ, j ≠ i → x j ≠ 0` is not derivable from the pinned block
      (hx₀ allows `x j = 0` for `j ≠ i`). **Replacement:** private no-division bridge
      `gwWeight_mul_x_eq (hroot : labelOf τ = i) (hprop : Proper τ)
      (hwit : IsWitnessTree vbl τ) : x i * gwWeight vbl x τ = (1 - x i) * x'Prod vbl x τ`
      (WitnessTree.rec mirroring 50.1's Steps A–C with the `field_simp` steps replaced by
      `ring` — a strict simplification), then the per-σ divided form
      `x'Prod vbl x σ = (x i/(1-x i)) * gwWeight vbl x σ` by dividing by `1 - x i ≠ 0`
      (hx₁) — **division only by `1 - x i`, never by `x i`** (probe-verified
      `field_simp [hne]; nlinarith`). Consequence: the informal's `by_cases x i = 0`
      becomes UNNECESSARY — the uniform chain subsumes both cases (`x i = 0` degenerates
      to `ofReal 0 * … = 0`; `ofReal_mul` only needs `0 ≤ x i/(1-x i)` from hx₀/hx₁ and
      `0 ≤ gwWeight σ` from 50.3's `gwWeight_nonneg`). `ENNReal.ofReal_div_of_pos` /
      `ofReal_div_le` / `ofReal_prod_of_nonneg` are NOT consumed (all division is ℝ).
      (3) **`coupling_canon`'s `hN : size σ ≤ N` is NOT available for
      `σ ∈ gwFinsetHeight vbl i (N-1)`** — a height-(N-1) canonical witness tree can have
      size up to ~(Fintype.card ι)^(N-1) (e.g. `ι = {i, j}`, `N = 3`: the size-7 tree
      `i → j → {i, j}` lies in `gwFinsetHeight i 2`). Pin the uniform wrapper
      `occurrence_canon_le_treeProd (hA) (σ) : μN N μ {ω | ∃ t < R …, canon (T … ω t) = σ}
      ≤ treeProd (μ := μ) A σ` — `by_cases hN : size σ ≤ N` inside: the coupling, or the
      empty event (`size σ = size (canon (T t)) = size (T t) ≤ N` via `T_size_le_N` +
      `size_canon` under `(T_isGood).1`).
      (4) **20.5 (measurability) is still pending** — 60.2 carries a private scoped slice
      (open-question-7 fallback): `measurableSet_count_eq` / `measurableSet_lt_R` and the
      pinned `measurableSet_occ_canon {t σ} : MeasurableSet {ω | t < R … ω ∧
      canon (T … ω t) = σ}` — finite-history decomposition (finite unions over `State N` /
      log patterns; each piece a finite boolean combination of
      `{ω | assign ω c ∈ A i}` cylinder preimages via Coupling.lean's `cylinder_witness` /
      `measurableSet_witness` + `fun_prop`; `[∀ j, Nonempty (Ω j)]` derived locally from
      `[IsProbabilityMeasure (μ j)]` where needed). Then `aemeasurable_card_fiber σ` via
      the pointwise indicator-sum identity `(card F_σ ω : ℝ≥0∞) = Σ_{t ∈ range N},
      (E_{t,σ}).indicator (fun _ => 1) ω` + `Finset.measurable_sum`
      (`MeasurableAdd₂ ℝ≥0∞` ✓) + `Measurable.indicator`; `MeasurableSet E_σ` via
      `Finset.measurableSet_biUnion` (feeds `lintegral_indicator_const`). Contingency:
      if the slice proves too heavy, deliver the stack minus the headline exchange and
      re-plan (or attempt 20.5 first).
      (5) The headline keeps the pinned lintegral form (60.3–60.5 consume exactly
      `moserTardos_bound` — 60.3 sums it via `lintegral_finsetSum'`; no expectation-form
      change). `hLLL` enters ONLY via `treeProd_le_ofReal_x'Prod`'s per-node step
      `μπ μ (A a) ≤ ENNReal.ofReal (x' vbl x a)` (definitional after `unfold x'`), which
      needs private `x'_nonneg` (from hx₀/hx₁ — the `x j ≤ 1` conjunct).
    - **Verified mathlib additions (lake-env-lean probed ✓):** `lintegral_mono`
      (pointwise `f ≤ g`, NO measurability hypothesis) / `lintegral_congr` (pointwise) /
      `lintegral_indicator_const` (`(hs : MeasurableSet s)`) / `lintegral_indicator₀`
      (`NullMeasurableSet`) / `ENNReal.ofReal_sum_of_nonneg` / `ENNReal.ofReal_le_ofReal` /
      `Finset.mul_sum` (`NonUnitalNonAssocSemiring ℝ≥0∞` ✓) / `mul_le_mul'`
      (`MulLeftMono`/`MulRightMono`/`PosMulMono`/`MulPosMono ℝ≥0∞` instances ✓) /
      `List.prod_le_prod'` (child-products step of `treeProd_le_ofReal_x'Prod`) /
      `List.prod_map` (List-level `ofReal`-product glue) / `map_sum` +
      `Nat.castAddMonoidHom ℝ≥0∞` (the ℕ-sum → ENNReal cast) / `Finset.card_le_one` /
      `Finset.measurableSet_biUnion` / `Measurable.indicator` / `Finset.measurable_sum` +
      `MeasurableAdd₂ ℝ≥0∞`. NOTE: `lintegral_indicator`/`lintegral_indicator_const` both
      require measurability of the set — the private slice (4) is mandatory, not optional.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-17 | 1 / 15 | done | In Basic.lean (new `section MainTheorem` after CountLogIdentity + `import …Coupling`; context `{ι} [DecidableEq ι] [Inhabited ι] [Fintype ι]` `{κ} [DecidableEq κ] [Fintype κ]` `{Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]` `(μ) [∀ j, IsProbabilityMeasure (μ j)]` `(vbl) (A) (hA) (hdet) (x) (hx₀) (hx₁) (hLLL) (pick) (hpick)` `(N)`) prove the full 60.2 statement set and close the headline. **(A) the 40.3-side re-shaping (60.1 flags):** `treeProfile_canon (hprop : Proper τ) (j) (d) : treeProfile vbl (canon τ) j d = treeProfile vbl τ j d` (WitnessTree.rec + `canonChildren_perm` + `List.Perm.sum_eq`); `check_canon (hprop : Proper τ) (hN : size τ ≤ N) (hNc : size (canon τ) ≤ N) (ω) : check vbl A hdet hNc ω ↔ check vbl A hdet hN ω` (unfold both sides via `checkSet_eq_vertices`; private path-correspondence lemmas `validPath_canon_of_valid`/`validPath_of_valid_canon`/injectivity — label- and length-preserving liftings between `ValidPath (canon τ)` and `ValidPath τ` — + `treeProfile_canon`); `isGood_canon (hgood : IsGood vbl τ) : IsGood vbl (canon τ)` (private `proper_canon` + the same path correspondence with the injectivity for the `p ≠ q` transport — the HEAVY piece); `coupling_canon (hA) (hN : size σ ≤ N) : μN N μ {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ} ≤ treeProd (μ := μ) A σ` (by_cases `IsGood vbl σ`: good — occurrence ⊆ `check`-event of σ via `occurrence_implies_check` + `check_canon` + `check_probability`; non-good — empty event via `T_isGood` + `isGood_canon`); uniform wrapper `occurrence_canon_le_treeProd (hA) (σ) : μN N μ {ω | ∃ t < R …, canon (T … ω t) = σ} ≤ treeProd (μ := μ) A σ` (by_cases `size σ ≤ N`: `coupling_canon` vs empty event via `T_size_le_N` + `size_canon`). **(B) `T_size_eq` is FALSE (counterexample in prep) — replaced by** `canon_T_injective {ω} {t₁ t₂} (ht₁ : t₁ < R …) (ht₂ : t₂ < R …) (h : canon (T … ω t₁) = canon (T … ω t₂)) : t₁ = t₂` via 30.6's `treeAt_count_label` + private `labels_canon` + `log_eq_some_iff_labelOf_T` + re-derived `length_filter_range_lt`; then private `fiber_card_le_one`. **(C) private ℝ/ENNReal bridges:** `x'_nonneg`; `gwWeight_mul_x_eq (hroot) (hprop) (hwit) : x i * gwWeight vbl x τ = (1 - x i) * x'Prod vbl x τ` (no-division telescope replacement — 50.1's division form needs unavailable `x j ≠ 0`; WitnessTree.rec, ring-only); `x'Prod_eq_div_mul_gwWeight` (÷ `1 - x i ≠ 0` from hx₁ — never ÷ `x i`); `treeProd_le_ofReal_x'Prod (hLLL) (hx'0) (σ) : treeProd (μ := μ) A σ ≤ ENNReal.ofReal (x'Prod vbl x σ)` (WitnessTree.rec + `mul_le_mul'` + `ENNReal.ofReal_mul` + `List.prod_le_prod'`/`List.prod_map`). **(D) private measurability slice (20.5-scoped, open-question-7 fallback — 20.5 still pending):** `measurableSet_count_eq` / `measurableSet_lt_R` / `measurableSet_occ_canon {t σ} : MeasurableSet {ω | t < R … ω ∧ canon (T … ω t) = σ}` (finite-history decomposition; single-vertex cylinder preimages via `cylinder_witness`/`measurableSet_witness`/`fun_prop`) + `aemeasurable_card_fiber σ` (indicator-sum identity + `Finset.measurable_sum` + `Measurable.indicator`). **(E) headline `moserTardos_bound`** (exact pinned shape, lintegral form — 60.3–60.5 consume it unchanged). Assembly chain (UNIFORM — the informal's `by_cases x i = 0` is subsumed, see prep (2)): `∫⁻ countLog = ∫⁻ (Σ σ ∈ gwFinsetHeight vbl i (N-1), (F_σ ω).card : ℝ≥0∞)` [60.1's `countLog_eq_sum_card` + `lintegral_congr` + `map_sum`/`Nat.castAddMonoidHom`] `= Σ σ ∈ gwFinsetHeight …, ∫⁻ ω, (F_σ ω).card` [`lintegral_finsetSum'` + the slice] `≤ Σ σ …, μN N μ E_σ` [per-σ: pointwise `(card F_σ ω : ℝ≥0∞) ≤ E_σ.indicator (fun _ => 1) ω` via `fiber_card_le_one` + `lintegral_mono` (no measurability needed) + `lintegral_indicator_const` (needs `MeasurableSet E_σ` from the slice)] `≤ Σ σ …, treeProd (μ := μ) A σ` [`occurrence_canon_le_treeProd`] `≤ Σ σ …, ENNReal.ofReal (x'Prod vbl x σ)` [`treeProd_le_ofReal_x'Prod` with hLLL-definitional `x'`] `= Σ σ …, ENNReal.ofReal (x i/(1-x i)) * ENNReal.ofReal (gwWeight vbl x σ)` [`x'Prod_eq_div_mul_gwWeight` + `ENNReal.ofReal_mul` (nonneg: `div_nonneg hx₀` + `gwWeight_nonneg`)] `= ENNReal.ofReal (x i/(1-x i)) * Σ σ …, ENNReal.ofReal (gwWeight vbl x σ)` [`Finset.mul_sum`] `= ENNReal.ofReal (x i/(1-x i)) * ENNReal.ofReal (Σ σ …, gwWeight vbl x σ)` [`ENNReal.ofReal_sum_of_nonneg`] `≤ ENNReal.ofReal (x i/(1-x i)) * ENNReal.ofReal 1` [50.3's `gwWeight_sum_le_one (hx₀) (hx₁)` + `ENNReal.ofReal_le_ofReal` + `mul_le_mul'`] `= ENNReal.ofReal (x i/(1-x i))` [`ENNReal.ofReal_one`, `mul_one`]. Contingency: if (D) proves too heavy, deliver (A)–(C) + the sum-level chain `Σ σ ∈ gwFinsetHeight vbl i (N-1), treeProd (μ := μ) A σ ≤ ENNReal.ofReal (x i/(1-x i))` (measurable-free) and re-plan the headline exchange (or attempt 20.5 first). | Three chunks, dependency order. **Chunk 1 (canon machinery):** `canonLiftCert` — the data-valued path-certificate lift (noncomputable; the child witness is `Classical.choose`, inlined because a wrapper breaks defeq at instances transparency; the recursive call receives the explicit `cast (congrArg …)`, cf. 30.1/30.7's `validPath_of_forgetTime`) + `validPath_canonLift`/`length_canonLift`/`labelAt_canonLift`/`canonLift_cert_cast`/`canonLift_injective` (per-node reindex injective via `List.idxOf_inj` + `canonChildren_nodup`), `treeProfile_canon` (WitnessTree.rec + `canonChildren_perm` + `List.Perm.sum_eq`), `mem_ccs_of_mem`, `checkAux_canon` (motive over `canon τ`/`τ`, `heq_of_eq` transports via `treeProfile_canon`), `check_canon`, `proper_canon`, `isGood_canon` — the HEAVY piece (lift both paths to `τ`, `IsGood vbl τ` transport via the lift's injectivity for the `p ≠ q` conjunct, labels/depths back via `labelAt_canonLift`/`length_canonLift`). **Chunk 2 (coupling/GW bridges):** `coupling_canon` (by_cases `IsGood vbl σ`: occurrence ⊆ check-event via `occurrence_implies_check` + `check_canon` + `check_probability`; non-good → empty event via `T_isGood` + `isGood_canon`) + uniform wrapper `occurrence_canon_le_treeProd` (by_cases `size σ ≤ N` inside — correction (3): `hN` is NOT available for `σ ∈ gwFinsetHeight vbl i (N-1)`); `canon_T_injective` — replaces the FALSE `T_size_eq` (correction (1)): canon-equality → `labelOf_canon` → `log_eq_some_iff_labelOf_T` both sides → `treeAt_count_label` count identities → contradiction via re-derived `length_filter_range_lt`, no size arguments — + private `fiber_card_le_one`; private ℝ/ENNReal bridges: `gwWeight_mul_x_eq` (WitnessTree.rec, ring-only — correction (2): 50.1's division telescope needs unavailable `x j ≠ 0`), `x'Prod_eq_div_mul_gwWeight` (divides ONLY by `1 - x i ≠ 0` from hx₁), `x'_nonneg`, `x'Prod_nonneg`, `ofReal_list_prod_eq`, `treeProd_le_ofReal_x'Prod` (hLLL enters only here, definitional after `unfold x'`). **Chunk 3 (headline):** `moserTardos_bound` — the uniform lintegral calc chain exactly per the pinned assembly (`lintegral_congr` + `countLog_eq_sum_card` → `lintegral_finsetSum'` + `aemeasurable_card_fiber` → per-σ `(card F_σ ω : ℝ≥0∞) ≤ E_σ.indicator 1 ω` via `fiber_card_le_one` + `lintegral_mono` + `lintegral_indicator_const` with `measurableSet_occ` → `occurrence_canon_le_treeProd` → `treeProd_le_ofReal_x'Prod` → `x'Prod_eq_div_mul_gwWeight` + `ENNReal.ofReal_mul` → `Finset.mul_sum` → `ENNReal.ofReal_sum_of_nonneg` → 50.3's `gwWeight_sum_le_one` + `mul_le_mul'` → `ofReal_one`/`mul_one`); explicit headline params per the Setup pin; the informal's `by_cases x i = 0` subsumed. **Deviations:** the measurability slice (D) NOT re-derived — 20.5 landed after the Survey ran, so Algorithm's `section Measurability` + Basic's `section MeasurableOccurrence` are imported instead (tmp header updated); the check/isGood path-correspondence privates were deliberately not stubbed — designed as the canonLift machinery (label- and length-preserving through the child permutation; same-path validity is FALSE in general). Final tmp: 0 sorries, 0 errors, 12 linter warnings (unused section vars on private lemmas — fixed at integration). | Independently verified: tmp (1281 lines — over the 500-line tmp convention, but the orchestrator pinned the full 16-declaration set plus private machinery, so integrated whole rather than split) `lake env lean` exit 0, 0 errors, exactly the 12 expected unused-section-variable linter warnings; grep clean (no sorry/axiom/admit/native_decide — the only sorry hit is the tmp header docstring prose); `#print axioms moserTardos_bound` = propext/Classical.choice/Quot.sound only; headline statement spot-checked against the Survey pin (exact lintegral form with hx₀/hx₁/hLLL, conclusion `≤ ENNReal.ofReal (x i / (1 - x i))`, explicit headline params). Integrated into Basic.lean as new `section MainTheorem` after `end MeasurableOccurrence` (+ `import …Coupling` — acyclic: Coupling imports WitnessTree only; module docstring gets 4 new result bullets). Integration deviations (reflected in the section docstring): the 4 re-derivations of Basic.lean's OWN file-scoped privates (`eq_of_labelOf_eq_of_nodup`/`canonChild_spec`/`nodup_map_of_labelOf_inj`/`canonChildren_perm` — same statements) are DROPPED — in-file privates are visible to later sections and keeping the duplicates collides on private-name mangling — the section uses the originals directly; `length_filter_range_lt` re-derived as a private (WitnessTree.lean file-scope). All linter warnings fixed with the house `omit … in` pattern; the omit cascade (dropping an instance from a lemma's signature re-flags its dependents) was iterated to convergence (7 rounds) — final: `lake env lean` exit 0, ZERO warnings, zero errors; 14 >100-char lines rewrapped; privates private; all `include … in` annotations kept exactly; headline untouched by the omits. `lake build StatsMLlib.Probability.MoserTardos.Basic` OK (2995 jobs). tmp deleted. | `tmp_main_theorem.lean` |

### 60.3. moserTardos_total

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Basic.lean`
- **informal**
    - statement: |
        Total expected resamplings (survey B F24, notes §18 (5.2); difficulty Easy, est.
        ~40 lines; critical path ★). Same hypotheses as 60.2:
        ```lean
        theorem moserTardos_total (…same hypotheses…) :
            ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
              ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))
        ```
    - proof: |
        (survey B §3.5) `R = Σ_i N_i^{(N)}` pointwise (each `t < R` has `Λ t = some e` for
        exactly one `e`), so `∫⁻ R = Σ_i ∫⁻ countLog` via `lintegral_finsetSum'` and the
        per-`i` bounds from 60.2 — no additional content beyond the `ofReal`-sum bridge
        (`∑_i ofReal (x i/(1-x i)) = ofReal (∑_i x i/(1-x i))`; exact lemma — e.g.
        `ENNReal.ofReal_sum_of_nonneg` — TBC at Survey).
    - **prep**
        - `lintegral_finsetSum'` — `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:341`.
          Survey-verified signature (2026-08-18): `(s : Finset β) {f : β → α → ℝ≥0∞}
          (hf : ∀ i ∈ s, AEMeasurable (f i) μ) : ∫⁻ a, ∑ i ∈ s, f i a ∂μ =
          ∑ i ∈ s, ∫⁻ a, f i a ∂μ`.
        - `lintegral_congr` — pointwise function equality, NO measurability hypothesis
          (60.2's headline uses it exactly this way, Basic.lean:2103).
        - `Nat.cast_sum` — `Mathlib/Algebra/BigOperators/Ring/Finset.lean:337` (the ℕ-sum
          → ℝ≥0∞ cast bridge; 60.2's step-1 pattern).
        - `Finset.card_eq_sum_card_fiberwise` —
          `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:979` (for the new private
          identity; call shape in-file at Basic.lean:702).
        - `ENNReal.ofReal_sum_of_nonneg` — `Mathlib/Data/ENNReal/BigOperators.lean:123`
          (the `ofReal`-sum bridge, survey-B §3.5's "exact lemma TBC"; 60.2's last step
          uses `rw [← …]`).
        - `Finset.sum_le_sum` — per-`i` step over `Finset.univ`.
        - `Finset.card_range` — card of `range (R … ω)` in the identity's glue (a).
        - Internal deps (survey B §5): item 60.2 (`moserTardos_bound`); item 20.5
          (`measurable_countLog`, Algorithm.lean:1303); `Algorithm.log_ne_none_iff_lt_R`
          (Algorithm.lean:401), `Algorithm.R_le` (Algorithm.lean:276).
        - NEW private intermediate (proved in-tmp, integrates into Basic.lean's
          `section MainTheorem`): `R_eq_sum_countLog (ω) : R vbl A pick hpick ω =
          ∑ i, countLog (log vbl A pick hpick) ω i` — the double-counting identity of
          survey B §3.5, the only non-mathlib content of the item.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-18 | 1 / 15 | done | Pin against the integrated 60.2 surface (survey-verified: `moserTardos_bound` Basic.lean:2075, explicit `{N} (Ω) [∀ j, MeasurableSpace (Ω j)] (μ) [∀ j, IsProbabilityMeasure (μ j)]` + section vars ι/κ/vbl/A/hA/hdet/x/hx₀/hx₁/hLLL/pick/hpick; hLLL is the integrated per-variable `∀ i, μπ μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j))` — exactly the `∀ i` form the univ-sum needs; survey-B F24 matches the blueprint informal, no hypothesis drift) and prove the whole item. **Statement (pinned, same hypotheses as 60.2, same explicit-binder pattern):** `theorem moserTardos_total {N : ℕ} (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)] (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)] : ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))`. RHS is the plain ℝ sum inside `ofReal` — the closed form is pinned by the informal + survey B F24, so NO `sum_x_div_le` intermediate is needed. **Private identity (the only new content):** `R_eq_sum_countLog (ω : ΩN N Ω) : R vbl A pick hpick ω = ∑ i, countLog (log vbl A pick hpick) ω i` — `Finset.card_eq_sum_card_fiberwise` with `s = (Finset.range N).filter (fun t => log … ω t ≠ none)`, `t = Finset.univ`, `f t = (log … ω t).getD default` (the `[Inhabited ι]` section var supplies the default); glue (a) `s = range (R … ω)` via `log_ne_none_iff_lt_R` + `R_le` + `Finset.card_range` (ext both directions), glue (b) per-`i` fiber equality `(s.filter (getD · = i)) = (range N).filter (log · = some i)` via `Option.some_ne_none` + `getD`/case-split simp; omit-style annotations: only `[DecidableEq ι] [Fintype ι] [Inhabited ι]` + vbl/A/pick/hpick. **Assembly (4 calc steps, mirrors 60.2's headline pattern):** (1) `∫⁻ R = ∫⁻ ∑ i, (countLog (log …) ω i : ℝ≥0∞)` — `lintegral_congr` (pointwise; NO AEMeasurable hypothesis — 60.2's Basic.lean:2103 usage) + `rw [R_eq_sum_countLog]` + `rw [Nat.cast_sum]`; (2) `∫⁻ ∑ = ∑ i, ∫⁻ …` — `rw [lintegral_finsetSum' Finset.univ (f := fun i ω => (countLog (log …) ω i : ℝ≥0∞))]` with `hf` from `(hcast.comp (measurable_countLog (N := N) (i := i))).aemeasurable` where `hcast : Measurable (fun n : ℕ => (n : ℝ≥0∞))` is the house one-liner (`intro s hs; change True; trivial`, Basic.lean:1032–1035); `∑ i ∈ univ` and `∑ i` are the same term so the calc step closes by `rfl`; (3) `∑ ∫⁻ ≤ ∑ i, ofReal (x i/(1-x i))` — `Finset.sum_le_sum` + `moserTardos_bound (N := N) (Ω := Ω) (μ := μ) (i := i)` (section vars auto-inferred); (4) `∑ ofReal … = ofReal (∑ i, x i/(1-x i))` — `rw [← ENNReal.ofReal_sum_of_nonneg]` + `div_nonneg (hx₀ i) (sub_nonneg.mpr (le_of_lt (hx₁ i)))` (60.2's hdiv_nonneg pattern, Basic.lean:2096–2097). Est. ~20 lines + ~40 for the identity; NO `N = 0` pitfall (filter-card arithmetic, no division). | Combined Setup+Proof launch proved both statements. `R_eq_sum_countLog`: `Finset.card_eq_sum_card_fiberwise` with `s = (range N).filter (log ≠ none)`, `t = univ`, `f = getD default`; glue (a) `s = range (R ω)` via `log_ne_none_iff_lt_R` + `R_le` + `Finset.card_range`, glue (b) per-`i` fiber equality via `Option` case-split (`cases hx : …` + `rw [hx] at hi` + `change` — `cases hx` does not substitute); annotations `include instInhabitedι in` + `omit [DecidableEq κ] [Fintype κ] in`. `moserTardos_total` mirrors `moserTardos_bound`'s explicit-binder pattern — ALL hypotheses bound explicitly (deviation (1): `include`d hypotheses cannot reference the shadowed section Ω/μ, so the pinned minimal statement does not elaborate); 4 calc steps: `lintegral_congr` + the identity + `Nat.cast_sum`; `lintegral_finsetSum' univ` (measurability via the house `hcast.comp measurable_countLog`); `Finset.sum_le_sum` + `moserTardos_bound`; `rw [← ENNReal.ofReal_sum_of_nonneg]` + `div_nonneg`. Section instances named `instDecidableEqι`/`instInhabitedι` (deviation (2): `include` rejects instance-bracket syntax, needs a name). Reported exit 0, zero warnings, no sorry/axiom/admit/native_decide. | Independently verified: tmp (146 lines, under the 500-line convention) `lake env lean` exit 0, zero warnings; grep clean (no sorry/axiom/admit/native_decide); `#print axioms moserTardos_total` = propext/Classical.choice/Quot.sound only (transitive, so the private lemma is clean too); statement spot-checked exact against the Survey pin. Integrated into Basic.lean `section MainTheorem` after `moserTardos_bound` (module docstring bullet added; section instances `[DecidableEq ι] [Inhabited ι]` named `instDecidableEqι`/`instInhabitedι` — semantically neutral renames needed for the `include`s; the private lemma gained one extra `omit [(j : κ) → MeasurableSpace (Ω j)]` — the section's MeasurableSpace var on Ω auto-includes with Ω). `lake env lean Basic.lean` exit 0, ZERO warnings; all lines ≤100 chars; privates private; `lake build StatsMLlib.Probability.MoserTardos.Basic` OK (2995 jobs). tmp deleted. | `tmp_total.lean` |

### 60.4. moserTardos_tail

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Basic.lean`
- **informal**
    - statement: |
        The Markov tail bound, multiplicative form (survey B F25, notes §19; difficulty
        Easy–Med, est. ~60 lines; critical path ★). Same hypotheses as 60.2:
        ```lean
        theorem moserTardos_tail (…same hypotheses…) :
            (N : ℝ≥0∞) * μN N μ {ω | R vbl A pick hpick ω = N}
              ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))
        ```
        **PITFALL (survey B §3.5, load-bearing): the divided form
        `μN(R = N) ≤ Σ x/(1-x)/N` is FALSE for `N = 0`** — then `R = 0` a.s. and the RHS
        is `x/0 = 0` in Lean's ℝ (`0/0 = 0`). The honest statement is the multiplicative
        one above (true for all `N`); the ε–N divided form (`μN(R = N) ≤ ε` for
        `N ≥ (Σ x/(1-x))/ε`, `ε > 0`) is a follow-up with `N ≠ 0` (proposal Future
        Extensions). Measurability of `{R = N}` comes from 20.5.
    - proof: |
        (survey B §3.5) Pointwise `N · 𝟙[R = N] ≤ R`: if `R = N`, `N ≤ R = N`; if
        `R ≠ N`, `0 ≤ R` (using `R ≤ N`, 20.3). Then lintegral both sides and apply 60.3:
        `N * μN{R = N} = ∫⁻ N · 𝟙[R=N] ≤ ∫⁻ R ≤ ofReal (∑ x i/(1-x i))`.
    - **prep** (survey 60.4 attempt 1, 2026-08-18 — verified against the integrated surface
      and mathlib by probe)
        - `MeasureTheory.lintegral_indicator_const` — `∫⁻ s.indicator (fun _ => c) = c * μ s`
          for `MeasurableSet s`; `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:527`
          (verified; matches the pinned line).
        - `MeasureTheory.lintegral_mono` — pointwise `f ≤ g` ⇒ `∫⁻ f ≤ ∫⁻ g`, no
          measurability hypothesis; used in 60.2.
        - `Set.indicator_of_mem` / `Set.indicator_of_notMem` — indicator case split
          (`Mathlib/Data/Set/Indicator.lean`); use a let-bound set
          (`let s : Set (ΩN N Ω) := {ω | R vbl A pick hpick ω = N}`, 60.2's `let E` pattern)
          so `h : ω ∈ s` matches the lemmas directly — a bare set-builder membership makes
          `rw [Set.indicator_of_mem h]` mis-infer `s`/`a`.
        - Internal deps (survey B §5): item 60.3 (`moserTardos_total`, integrated
          `Basic.lean` section MainTheorem — instance implicits `instDecidableEqι` /
          `instInhabitedι` must be named identically in the tmp section for the call to
          elaborate), item 20.5 (`measurableSet_R_eq`, `Algorithm.lean:1099`, section
          `Stopping`, `include hA in` — explicit args
          `(vbl := vbl) (A := A) (hA := hA) (pick := pick) (hpick := hpick) (N := N)`).
        - NOT needed: `lintegral_const` (superseded by `lintegral_indicator_const` — removed
          from prep) and item 20.3 `R_le` (the informal's parenthetical is stale: with the
          ENNReal cast, the `R ≠ N` branch is `0 ≤ ↑R`, automatic via `zero_le`).
        - Alternative route (verified as fallback, NOT pinned): Markov's inequality
          `MeasureTheory.mul_meas_ge_le_lintegral₀`
          (`Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:50`) gives
          `ε * μ {x | ε ≤ f x} ≤ ∫⁻ f` for `AEMeasurable f`; would additionally need
          AEMeasurable of `fun ω => (R … ω : ℝ≥0∞)` and the `{R = N} ⊆ {N ≤ R}` transfer
          (`measure_mono` + `mul_le_mul'`) — heavier than the pinned indicator route.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-18 | 1 / 15 | done | Pin against the integrated surface and prove the whole item (chain probe-verified end-to-end: `lake env lean` exit 0, zero warnings, axioms = propext/Classical.choice/Quot.sound only). **Statement (pinned, multiplicative form `{R = N}` per the blueprint informal — NOT the divided form, false at `N = 0`; true for all `N`):** `theorem moserTardos_tail {N : ℕ} (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)] (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)] (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i)) (hdet : ∀ i, DeterminedBy (A i) (vbl i)) (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1) (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j))) (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1) : (N : ℝ≥0∞) * μN N μ {ω : ΩN N Ω | R vbl A pick hpick ω = N} ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))`. Tmp section mirrors 60.3's: `{ι} [instDecidableEqι : DecidableEq ι] [instInhabitedι : Inhabited ι] [Fintype ι]`, `{κ} [DecidableEq κ] [Fintype κ]`; Ω/μ/vbl/A/… bound explicitly; needs `open scoped ENNReal` (the `ℝ≥0∞` notation). **Chain (3 calc steps, the blueprint informal's indicator route — NO general Markov lemma):** (1) `(N : ℝ≥0∞) * μN N μ s = ∫⁻ s.indicator (fun _ => (N : ℝ≥0∞))` — `rw [lintegral_indicator_const (hs := show MeasurableSet s from measurableSet_R_eq (vbl := vbl) (A := A) (hA := hA) (pick := pick) (hpick := hpick) (N := N)) (c := (N : ℝ≥0∞))]`; (2) `≤ ∫⁻ ↑(R …)` — `lintegral_mono` + pointwise `by_cases h : ω ∈ s`: `Set.indicator_of_mem h` + `change (N : ℝ≥0∞) ≤ (R vbl A pick hpick ω : ℝ≥0∞)` + `have hN : R vbl A pick hpick ω = N := h` + `rw [hN]` (the `change` beta-reduces the `(fun a => …) ω` goal), else `Set.indicator_of_notMem h` + `exact zero_le`; (3) `≤ ofReal (∑ i, x i/(1-x i))` — `moserTardos_total (N := N) (Ω := Ω) (μ := μ) (vbl := vbl) (A := A) (hA := hA) (hdet := hdet) (x := x) (hx₀ := hx₀) (hx₁ := hx₁) (hLLL := hLLL) (pick := pick) (hpick := hpick)`. NO `N = 0` pitfall, no ENNReal division, no ofReal arithmetic; 20.3 `R_le` unused. Est. ~45 lines. | Combined Setup+Proof launch (71-line tmp, 47-line proof): proved the pinned multiplicative `{R = N}` statement with the survey's 3-step calc — (1) `lintegral_indicator_const` with `measurableSet_R_eq` (20.5) converts `(N : ℝ≥0∞) * μN N μ s` into the indicator lintegral; (2) `lintegral_mono` + pointwise `by_cases h : ω ∈ s` (`indicator_of_mem` + `change`/`rw [hN]`, else `indicator_of_notMem` + `zero_le`); (3) `moserTardos_total` (60.3) closes. One deviation from pin: `exact zero_le` in place of the pin's `zero_le _`. Reported exit 0, zero sorries/warnings; axioms = propext/Classical.choice/Quot.sound only. | Independent re-verification: tmp compiles (`lake env lean` exit 0, zero warnings); no sorry/axiom/admit/native_decide; statement matches the pin exactly (multiplicative `{R = N}` form, true for all `N`); `#print axioms` = propext/Classical.choice/Quot.sound. Integrated verbatim into `Basic.lean` section `MainTheorem` after `moserTardos_total`; `lake env lean Basic.lean` exit 0 zero warnings; `lake build StatsMLlib.Probability.MoserTardos.Basic` OK (2995 jobs). Tmp deleted. | `tmp_tail.lean` |

### 60.5. moserTardos_exists

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Basic.lean`
- **informal**
    - statement: |
        The constructive LLL (survey B F26, notes §19; difficulty Medium, est. ~80 lines;
        critical path ★). Same hypotheses as 60.2:
        ```lean
        theorem moserTardos_exists (…same hypotheses…) :
            ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i
        ```
        The algorithm's output at time `R < N` avoids every bad event — making the
        variable-model LLL constructive, the companion of
        `LovaszLocal.lovaszLocalLemma_exists` (cross-link in the docstring; the definitional
        `IsDependencyGraph` bridge is a follow-up, proposal Future Extensions).
    - proof: |
        (survey B §3.5) Choose `N` with `Σ i, x i/(1-x i) < N` (e.g. `Nat.ceil … + 1`; the
        sum is finite because `ι` is `Fintype`); the tail bound (60.4) gives
        `μN (R = N) < 1`, so `μN {R < N} > 0`, hence (by
        `exists_mem_of_measure_ne_zero_of_ae`,
        `Mathlib/MeasureTheory/Measure/Restrict.lean:414`, or
        `nonempty_of_measure_ne_zero`-style glue — exact name TBC at Survey) some `ω` has
        `R ω < N`; then `assign ω (count ω ⟨R ω, …⟩) ∈ ⋂ i, (A i)ᶜ` by the definition of
        `R`. **No `Nonempty (Π j, Ω j)` hypothesis is needed** — `σ` is exhibited from `ω`.
    - **prep**
        - `exists_nat_gt` — `Mathlib/Algebra/Order/Archimedean/Defs.lean:76`
          (`∃ n : ℕ, x < n` for Archimedean ℝ; supplies the internal `N`, replacing the
          informal's `Nat.ceil … + 1` — probe-verified).
        - `ENNReal.ofReal_lt_natCast` — `Mathlib/Data/ENNReal/Real.lean:199`
          (`ofReal p < n ↔ p < n` for `n ≠ 0`; converts the strictness to ENNReal —
          probe-verified).
        - `measure_univ` — core simp lemma; fires via the instance
          `μN.instIsProbabilityMeasure` (`VariableModel.lean:87`) — probe-verified.
        - `lt_irrefl` / `lt_of_le_of_lt` / `div_nonneg` / `sub_nonneg` / `Finset.sum_nonneg` /
          `Nat.ne_of_gt` / `exact_mod_cast` — core lemmas.
        - `push Not` — replaces the deprecated `push_neg` tactic (push `Not` into the
          by-contradiction hypothesis).
        - Internal deps: item 60.4 (`moserTardos_tail`), Algorithm's `R`/`NoViolation`/
          `assign`/`count` surface (20.3, `Algorithm.lean:109/210/265/271`).
        - Dropped (route change): `exists_mem_of_measure_ne_zero_of_ae` — the pinned route is
          by-contradiction (no `{R < N}`-positivity step), so the informal's TBC glue
          (`Mathlib/MeasureTheory/Measure/Restrict.lean:414`) is not consumed.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-18 | 1 / 15 | done | In Basic.lean (new `section Exists` after `end MainTheorem`, re-declaring MainTheorem's context minus `{N : ℕ}`) prove `moserTardos_exists (Ω) [∀ j, MeasurableSpace (Ω j)] (μ) [∀ j, IsProbabilityMeasure (μ j)] (vbl) (A) (hA) (hdet) (x) (hx₀) (hx₁) (hLLL) (pick) (hpick) : ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i` — same explicit-binder pattern as `moserTardos_bound`; pick/hpick REQUIRED (the route consumes `moserTardos_tail`/`R`); NO `N` parameter and NO strictness hypothesis — the `Σ i, x i/(1-x i) < N` strictness is discharged INTERNALLY. **Pinned route (by-contradiction; probe-compiled end-to-end, exit 0):** `let s := ∑ i, x i / (1 - x i)`; `hs₀ : 0 ≤ s` (`Finset.sum_nonneg`, `div_nonneg hx₀`, `sub_nonneg`); `rcases exists_nat_gt s with ⟨N, hsN⟩` (Archimedean; replaces the informal's `Nat.ceil … + 1`); `hNpos : 0 < N` (`lt_of_le_of_lt hs₀ hsN`, `exact_mod_cast`); `hNlt : ENNReal.ofReal s < (N : ℝ≥0∞)` (`ENNReal.ofReal_lt_natCast (n := N) (Nat.ne_of_gt hNpos)`, `hsN`); `by_contra h; push Not at h` → `h : ∀ σ, ∃ i, σ ∈ A i`; `hR : ∀ ω : ΩN N Ω, R vbl A pick hpick ω = N` (`unfold R; split_ifs with hf`; the `hf` branch: `exfalso` + rcases `NoViolation` → `⟨htlt, hnv⟩` + `h (assign ω (count vbl A pick hpick ω ⟨t, htlt⟩))` vs `hnv i`; the else branch: `rfl`); `htail := moserTardos_tail (N := N) …`; `hset : {ω | R … ω = N} = Set.univ` (`ext ω; simp [hR ω]`); `rw [hset] at htail`; `simpa [s] using htail` gives `(N : ℝ≥0∞) ≤ ENNReal.ofReal s` (`measure_univ` via `μN.instIsProbabilityMeasure` + `mul_one`); close with `(lt_irrefl (N : ℝ≥0∞)) (lt_of_le_of_lt hle hNlt)`. Docstring cross-links `LovaszLocal.lovaszLocalLemma_exists` (prose only, no import). | Pinned by-contradiction route implemented verbatim and probe-compiled end-to-end on the first attempt (no deviations): `s := ∑ i, x i/(1-x i)` + `hs₀` (Finset.sum_nonneg/div_nonneg/sub_nonneg); `exists_nat_gt` supplies the internal `N`; `hNpos` (lt_of_le_of_lt + exact_mod_cast) and `hNlt` (ENNReal.ofReal_lt_natCast (n := N) (Nat.ne_of_gt hNpos)); `by_contra h; push Not at h`; `hR : ∀ ω, R vbl A pick hpick ω = N` via `unfold R; split_ifs` (the NoViolation branch refuted by `h (assign …)` vs `hnv i`, the else branch `rfl`); `moserTardos_tail (N := N) …` + `hset : {ω | R … ω = N} = Set.univ` + `simpa [s]` → `(N : ℝ≥0∞) ≤ ofReal s`, closed by `lt_irrefl`/`lt_of_le_of_lt`. Final tmp: 0 sorries, 0 errors, 0 warnings. | Independently verified: tmp (87 lines) `lake env lean` exit 0, zero warnings; grep clean (no sorry/axiom/admit/native_decide); `#print axioms moserTardos_exists` = propext/Classical.choice/Quot.sound only; statement spot-checked against the Survey pin (all 14 explicit binders incl. the two instance binders; conclusion `∃ σ : Π j, Ω j, ∀ i, σ ∉ A i`; NO `N` parameter, NO strictness hypothesis); proof matches the pinned route line-for-line. Integrated into Basic.lean as new `section Exists` after `end MainTheorem` (context = MainTheorem minus `{N : ℕ}`, named instances `instDecidableEqι`/`instInhabitedι`, `classical` inside the proof); module docstring gets the `moserTardos_exists` bullet. Post-integration `lake env lean` Basic.lean exit 0, zero warnings; `lake build StatsMLlib.Probability.MoserTardos.Basic` OK (2995 jobs). tmp deleted. | `tmp_exists.lean` |

---
## 70. Symmetric Form (Follow-up PR)

### 70.1. moserTardos_symmetric

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/MoserTardos/Symmetric.lean`
    - note: Follow-up PR (survey B §6: PR 2 = symmetric form + ε–N tail), out of the
      core PR 1; can be attempted only after the core lands.
- **informal**
    - statement: |
        The symmetric form (survey B F27, notes §20; difficulty Medium, est. ~150 lines):
        ```lean
        theorem moserTardos_symmetric (…framework…)
            {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ p)
            (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
            (hcond : Real.exp 1 * p * (d + 1) ≤ 1) (…pick…) :
            ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
              ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / d)
        ```
        via `x ≡ 1/(d+1)`. **Pitfall excluded by hypothesis (survey B §3.5): the `d = 0`
        case** — with `d = 0`, `x = 1` would violate `hx₁`; `hd1 : 1 ≤ d` rules it out
        (unlike the classical-LPP symmetric form, which needed a separate `d = 0` branch).
    - proof: |
        (survey B §3.5) Chain for `hLLL`: `p ≤ 1/(e(d+1))` (from `hcond` by `field_simp`,
        `0 < Real.exp 1`, `0 < d+1`) `≤ (1/(d+1)) · (d/(d+1))^d` (from `(1+1/d)^d ≤ e` via
        `Real.one_add_inv_pow_le_exp` — survey A verified,
        `Mathlib/Analysis/Complex/Exponential.lean:653`; alternative route
        `Real.add_one_le_exp`, `Mathlib/Analysis/SpecialFunctions/Exp.lean:211` — and
        `d/(d+1) = 1/(1+1/d)`, `d ≠ 0` from `hd1`) `≤ x · ∏_{j ∈ Γ(i)} (1 - x)` (via
        `|Γ(i)| ≤ d` = `hd` on `(overlapGraph vbl).degree i`, and `pow_le_pow_of_le_one`
        with `0 ≤ d/(d+1) ≤ 1`; `∏ = (d/(d+1))^{|Γ(i)|}` by `Finset.prod_const`). Then
        instantiate 60.2 with `x ≡ 1/(d+1)` and conclude
        `E[R] ≤ m/d`: `Σ_i ofReal(x/(1-x)) = ofReal(m · x/(1-x)) = ofReal(m/d)` via the
        `ofReal`-sum bridge / `ENNReal.ofReal_natCast` (`Mathlib/Data/ENNReal/Real.lean:311`)
        + `field_simp (d+1 ≠ 0)`; reuses `LovaszLocal.ofReal_one_sub`
        (`StatsMLlib/Probability/LovaszLocal.lean`, house lemma) for `1 - x` terms.
    - **prep** (Survey 2026-08-18, attempt 1 — all names probe-verified; see the log row
      for the full pinned chain)
        - `Real.one_add_inv_pow_le_exp` — `Mathlib/Analysis/Complex/Exponential.lean:653`
          (`(1 + (n : ℝ)⁻¹) ^ n ≤ exp 1`; `namespace Real` — CONFIRMED; the pinned lemma
          for `(1+1/d)^d ≤ e`). NOTE: `Real.one_sub_div_pow_le_exp_neg` (same file :641)
          gives the wrong direction (an upper bound) — do not use.
        - `Real.add_one_le_exp` — declared at `Mathlib/Analysis/Complex/Exponential.lean:631`
          (the pinned `SpecialFunctions/Exp.lean:211` is a usage site — location corrected).
          Alternative route only.
        - `pow_le_pow_of_le_one` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:393`
          (NOT `Algebra/Order/Ring/Pow.lean` — location corrected):
          `(ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hmn : m ≤ n) : a^n ≤ a^m` — exactly the
          `(d/(d+1))^d ≤ (d/(d+1))^{|Γ(i)|}` step.
        - `one_div_le_one_div_of_le` — `Mathlib/Algebra/Order/Field/Basic.lean:69`
          (`(ha : 0 < a) (h : a ≤ b) : 1/b ≤ 1/a` — the `(1+1/d)^d ≤ e ⟹ 1/e ≤ (d/(d+1))^d`
          reciprocal step).
        - `one_div_pow` — `Mathlib/Algebra/Group/Basic.lean` (`(1/a)^n = 1/a^n`; rewrite
          with `←`).
        - `one_div_mul_one_div` — `(1/a)·(1/b) = 1/(a·b)` (the `1/(e(d+1))` split).
        - `inv_lt_one_of_one_lt₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:943`
          (hx₁: `(d+1)⁻¹ < 1`). WARNING: the `₀`-less `inv_lt_one_of_one_lt`
          (Algebra/Order/Group/Defs.lean:143) is CommGroup-only and does NOT apply to ℝ
          (probe-verified failure).
        - `inv_nonneg` / `positivity` — hx₀ (`0 ≤ (d+1)⁻¹`).
        - `ENNReal.ofReal_le_ofReal` — `Mathlib/Data/ENNReal/Real.lean:137` (the ENNReal
          lift of the ℝ chain).
        - `SimpleGraph.degree` — `Mathlib/Combinatorics/SimpleGraph/Finite.lean:200`, def
          = `#(G.neighborFinset v)`; bridge `SimpleGraph.card_neighborFinset_eq_degree`
          (Finite.lean:203, rfl, @[simp]) — `simpa using (hd i)` gives the card bound.
        - `Finset.prod_const` — `(∏ _x ∈ s, b) = b ^ s.card`.
        - `le_div_iff₀` / `div_le_one` / `mul_le_mul_of_nonneg_right` / `Real.exp_pos` /
          `mul_pos` / `pow_pos` — the hcond and base-bound glue.
        - `field_simp` — core tactic (hdeq; needs `(d:ℝ) ≠ 0` from hd1).
        - Statement correction (probe-verified): `hp : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal p`
          — mathlib v4.32.0 has NO `Coe ℝ ℝ≥0∞`, so the informal's `≤ p` does not
          elaborate.
        - Dropped (route change): `ENNReal.ofReal_natCast` — the existence form has no
          m/d sum bridge; `LovaszLocal.ofReal_one_sub` — the `1 - x` terms stay in ℝ
          inside `ofReal`.
        - Internal deps: item 60.5 (`moserTardos_exists`, Basic.lean:2353 — integrated;
          the call REQUIRES `[Inhabited ι]` in the section context), 10.1
          (`overlapGraph`/degree surface, VariableModel.lean:121/138).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-18 | 1 / 15 | done | **EXISTENCE form** (Survey decision, probe-verified end-to-end): the informal's tail-bound statement (E[R] ≤ m/d via 60.2/60.3) is superseded — the hLLL instantiation chain is identical, but the conclusion instantiates the newly-integrated 60.5, dropping the `N` parameter and the m/d sum bridge. In the new file Symmetric.lean (section mirroring `section Exists`: `{ι} [DecidableEq ι] [Inhabited ι] [Fintype ι]`, `{κ} [DecidableEq κ] [Fintype κ]`, `{Ω} [∀ j, MeasurableSpace (Ω j)]`, `(μ) [∀ j, IsProbabilityMeasure (μ j)]`, `(vbl)`, `(A)`) prove `moserTardos_symmetric (Ω) [∀ j, MeasurableSpace (Ω j)] (μ) [∀ j, IsProbabilityMeasure (μ j)] (vbl) (A) (hA) (hdet) {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal p) (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d) (hcond : Real.exp 1 * p * (d + 1) ≤ 1) (pick) (hpick) : ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i` — `hp` MUST be the `ENNReal.ofReal p` form (mathlib v4.32.0 has NO `Coe ℝ ℝ≥0∞`; the informal's `≤ p` does not elaborate — probe-verified). **Pinned route:** `let x : ι → ℝ := fun _ => ((d : ℝ) + 1)⁻¹`; `hx₀` (`inv_nonneg.mpr (by positivity)`), `hx₁` (`inv_lt_one_of_one_lt₀` — the `₀` variant; the CommGroup `inv_lt_one_of_one_lt` does NOT apply to ℝ — on `(1 : ℝ) < d + 1` via `exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)` + `linarith`); per-`i` hLLL chain: `p ≤ 1/(Real.exp 1 * ((d:ℝ)+1))` (`rw [le_div_iff₀ (mul_pos (Real.exp_pos 1) (by positivity))]; nlinarith [hcond]`) `≤ ((d:ℝ)+1)⁻¹ * ((d:ℝ)/((d:ℝ)+1))^d` (probe-verified composite: `hdeq : d/(d+1) = 1/(1+d⁻¹)` by `field_simp [hd0]` with `hd0 : (d:ℝ) ≠ 0` from hd1; `Real.one_add_inv_pow_le_exp (n := d)` + `one_div_le_one_div_of_le (pow_pos hbase d)` + `rw [← one_div_pow, hdeq]`; then `mul_le_mul_of_nonneg_right` + `rw [← one_div_mul_one_div]; ring`) `≤ x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)` (`pow_le_pow_of_le_one` with base bounds `0 ≤ d/(d+1)` (positivity) and `d/(d+1) ≤ 1` (`(div_le_one …).2`), exponent bound `simpa using (hd i)` (degree = neighborFinset.card by rfl); `mul_le_mul_of_nonneg_left`; `Finset.prod_const`; `1 - ((d:ℝ)+1)⁻¹ = (d:ℝ)/((d:ℝ)+1)` by `field_simp`); ENNReal lift `(hp i).trans (ENNReal.ofReal_le_ofReal hchain)`; `exact moserTardos_exists Ω μ vbl A hA hdet x hx₀ hx₁ hLLL pick hpick` (call probe-compiled; requires `[Inhabited ι]` in the section context — 60.5's implicit binder). | Pinned existence-form route implemented verbatim and compiled on the first attempt (0 sorries, 0 errors, 0 warnings): `x ≡ ((d:ℝ)+1)⁻¹`; `hx₀` (inv_nonneg/positivity), `hx₁` (inv_lt_one_of_one_lt₀ — the ₀-variant — on `(1:ℝ) < d+1` via exact_mod_cast + linarith); per-`i` hLLL chain exactly as pinned (hstep1 le_div_iff₀ + nlinarith [hcond]; hstep2 hdeq/field_simp + Real.one_add_inv_pow_le_exp + one_div_le_one_div_of_le + ←one_div_pow + one_div_mul_one_div; hstep3 pow_le_pow_of_le_one with the degree bound `by simpa using (hd i)`, Finset.prod_const, hsub/field_simp); ENNReal lift `(hp i).trans (ENNReal.ofReal_le_ofReal hchain)`; `exact moserTardos_exists`. Three statement deviations vs the informal, all Survey-pinned and probe-verified: (1) `hp` as `≤ ENNReal.ofReal p` (mathlib v4.32.0 has no `Coe ℝ ℝ≥0∞`); (2) `[Inhabited ι]` in the section context (60.5's implicit binder); (3) existence form `∃ σ, ∀ i, σ ∉ A i` instead of the informal's tail bound `E[R] ≤ m/d` — the hLLL chain is identical, the 60.3 m/d sum bridge is dropped. | Independently verified: tmp (126 lines) `lake env lean` exit 0, zero warnings; grep clean (no sorry/axiom/admit/native_decide); `#print axioms moserTardos_symmetric` = propext/Classical.choice/Quot.sound only; statement spot-checked against the Survey pin (all binders incl. the ENNReal hp form; conclusion `∃ σ : Π j, Ω j, ∀ i, σ ∉ A i`; `[Inhabited ι]` present); sensitive `change` block kept verbatim; all lines ≤100 chars. Integrated as new module Symmetric.lean per meta.file (70.1 was a separate module in the proposal's file plan) — `section Symmetric` mirrors Basic's `section Exists` (named instances instDecidableEqι/instInhabitedι), module `/-!` docstring added. Post-integration `lake env lean` exit 0, zero warnings; `lake build StatsMLlib.Probability.MoserTardos.Symmetric` OK (2996 jobs). tmp deleted. | tmp_symmetric.lean |
