# PR: Moser–Tardos Algorithmic Lovász Local Lemma (TCSLean)

- **Target:** `hehepig166/TCSLean`, branch `zzk/moser-tardos` → `main`
- **File:** `TCSLean/MoserTardos/` (7 modules, namespace `TCSLean.MoserTardos`)

Formalizes the Moser–Tardos resampling algorithm for the asymmetric Lovász Local Lemma in
the variable framework (Moser & Tardos, arXiv:0903.0544, Thm 1.2): 7 modules, ≈ 10,200
lines, 27 blueprint items, all `done`. Planned in
[`docs/moser-tardos/01_proposal/proposal.md`](../01_proposal/proposal.md) and
[`docs/moser-tardos/02_blueprint/BLUEPRINT.md`](../02_blueprint/BLUEPRINT.md); the proof
audit and design decisions live in
[`01_proposal/survey/B_proof_strategy.md`](../01_proposal/survey/B_proof_strategy.md).

## What is formalized

The full chain, from the variable model to the constructive LLL:

- **Variable model** (`VariableModel`): finite event index `ι` and variable index `κ`;
  the variable-overlap dependency graph `overlapGraph` with inclusive neighborhood
  `gammaPlus`; the `DeterminedBy` relation; the truncated resampling table
  `ΩN N Ω := Π j, Fin (N + 1) → Ω j` (`N + 1` rows per variable) with product law
  `μN N μ` and the joint law `μπ μ` on full assignments.
- **Algorithm** (`Algorithm`): state, availability, and one resampling step; the
  `Fin.induction` run; the stopping time `R ≤ N`; the padded execution log and
  `countLog`; the complete measurability layer (`measurableSet_log_eq_some`,
  `measurable_countLog`, `measurableSet_R_eq`, and friends).
- **Witness trees** (`WitnessTree`): the custom rooted, ordered, labeled tree type with
  a data-valued path API; `Proper` and `IsGood`; the deepest-eligible reverse-scan
  construction (`attachBelow` and its fold spec); the time-labeled construction
  `treeAt`/`T`; the structural lemmas — properness (Prop 10.1), depth facts
  (Lemma 11.1 / Cor 11.2), injectivity (Prop 12.1), occurring trees are good.
- **Coupling** (`Coupling`): the structural τ-check, the profile inequality,
  `check_probability` (the measure of the check equals the structural product), and
  `occurrence_implies_check` + `coupling` — `μN N μ {ω | ∃ t < R, T ω t = τ} ≤ treeProd A τ`.
- **Galton–Watson weight algebra** (`GaltonWatson`): `gwWeight` and its telescope, the
  `Fintype` instance for the tree domain, the canonical-tree finset `gwFinsetHeight`,
  and `gwWeight_sum_le_one` over the canonical domain.
- **Main theorem and corollaries** (`Basic`): the canonical reordering `canon`, the
  counting identity `countLog_eq_sum_card`, the main bound `moserTardos_bound`
  (E[#resamplings of `i`] ≤ `x i / (1 - x i)`), and the corollaries `moserTardos_total`
  (≤ `∑ i, x i / (1 - x i)`), `moserTardos_tail` (multiplicative Markov tail),
  `moserTardos_exists` (constructive LLL: some full assignment avoids every bad event).
- **Symmetric form** (`Symmetric`): `moserTardos_symmetric` — under the uniform bound
  `μπ μ (A i) ≤ p`, degree bound `d`, and `e · p · (d + 1) ≤ 1`, the expected total
  resamplings is at most `|ι| / d`.

## Mathematical design decisions

- **Finite-truncation table.** Everything is stated on the truncated table `ΩN` with
  `N + 1` rows per variable, uniform in `N` — no infinite-product or martingale
  machinery anywhere.
- **The `if t < R` log.** The survey's proposed log — reading the run's option — is
  false at `t = R = N` in the fallback branch: with no violation-free time, the state
  at time `N` can still have an available violated event, so the run's option is `some`
  while `R = N`. The log is instead the padded
  `if t < R then some (choose …) else none`, for which `log ω t ≠ none ↔ t < R ω` holds
  for every `t` — exactly what the counting identity needs.
- **Canonical-tree domain.** The naive bound `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ 1` is false
  for ordered trees: in a star graph every ordering of the children is a distinct tree
  with the same weight — a `d!` overcount. The bound is proved over the canonical finset
  `gwFinsetHeight` (children in label order), and the counting identity and the coupling
  are routed through the canonical form `canon`.
- **`by_cases` on `IsGood` inside the coupling.** The coupling lemma takes no goodness
  hypothesis: good trees are bounded via occurrence ⊆ check, non-good trees have empty
  occurrence events (`T_isGood`).
- **No `[LinearOrder ι]`.** `canon` needs only `[DecidableEq ι]`: the children are
  reordered into the internal order of their label finset, which matches
  `gwFinsetHeight`'s assembly by construction.
- **hLLL shape.** The hypothesis is `μπ μ (A i) ≤ ENNReal.ofReal (x' i)` with
  `x' i = x i * ∏_{j ∈ Γ(i)} (1 - x j)` — all arithmetic is ℝ inside `ofReal`, no
  ENNReal division anywhere, and the `x i = 0` case is absorbed by the no-division
  telescope (`gwWeight_mul_x_eq` replaces the division form).

## Transfer from StatsMLlib

Faithful transfer of the formalization developed in `StatsMLlib` (branch
`zzk/moser-tardos`, commit `f2230a5`, itself stacked on the Lovász branch), with:

- module paths `StatsMLlib/Probability/MoserTardos/*.lean` → `TCSLean/MoserTardos/*.lean`,
  declarations wrapped in `namespace TCSLean.MoserTardos` (incl. the nested
  `WitnessTree` namespace);
- one fully-qualified `_root_.MoserTardos.WitnessTree.attachBelow_old_or_new` reference
  re-rooted to `_root_.TCSLean.MoserTardos.WitnessTree`;
- one unused simp argument (`Nat.add_left_comm` in `Coupling.lean`) removed — surfaced
  by the standalone-module build under default linter options;
- mathlib v4.32.0, unchanged from the source development (pinned since the Talagrand PR).
  `lake build` passes with 0 errors, 0 warnings.

The full statement review (docs/moser-tardos/04_pr/REVIEW.md, 2026-08-18) and its fixes
(`moserTardos_symmetric_total`, pick-free & Inhabited-free existence theorems, dead-chain
cleanup) are included in the transferred state.

## Engineering approach

Harness-driven per blueprint item — Survey → Setup → Proof → Review — against
[`docs/moser-tardos/02_blueprint/BLUEPRINT.md`](../02_blueprint/BLUEPRINT.md) (27 items,
all `done`). Two false statements were caught mid-project and corrected: the
run-option log equivalence (20.4, fixed by the `if t < R` log) and the ordered-tree sum
(50.3, fixed by the canonical domain); a third, `T_size_eq`, was caught in the 60.2
preparation and replaced by `canon_T_injective`. Every integration ran warning-free with
no `sorry`/`axiom`/`admit`/`native_decide`; `moserTardos_bound` uses only
`propext`/`Classical.choice`/`Quot.sound`.

Development commits in the source repo follow `feat(MT.<item>): attempt <n> — <summary>`
on `zzk/moser-tardos` (stacked on `zzk/lovasz-local-lemma-gptv2`), with outer-repo doc
commits `doc(MT.<item>)` bumping the StatsMLlib pointer. Newest first:

```text
feat(MT.70.1): attempt 1 — moserTardos_symmetric
feat(MT.60.5): attempt 1 — moserTardos_exists
feat(MT.60.4): attempt 1 — moserTardos_tail
feat(MT.60.3): attempt 1 — moserTardos_total
feat(MT.60.2): attempt 1 — moserTardos_bound
feat(MT.20.5): attempt 1 — measurability layer
feat(MT.60.1): attempt 1 — counting identity
feat(MT.40.3): attempt 2 — coupling lemma
feat(MT.50.3): attempt 1 — gwWeight sum ≤ 1
feat(MT.40.2): attempt 2 — check_probability
feat(MT.50.2): attempt 1 — Fintype 𝒯_i(N)
feat(MT.50.1): attempt 1 — gwWeight telescope
feat(MT.40.1): attempt 1 — τ-check machinery (treeProfile, check, profile inequality)
feat(MT.30.7): attempt 1 — occurring trees are good; size bounds
feat(MT.30.5): attempt 1 — depth lemmas (Lemma 11.1 / Cor 11.2)
feat(MT.30.6): attempt 1 — treeAt injectivity (Prop 12.1, A-count argument)
feat(MT.30.4): attempt 1 — treeAt_proper (Prop 10.1, abstract + pair forms)
feat(MT.30.3): attempt 1 — witness-tree construction treeAt/forgetTime/T
feat(MT.30.2): attempt 1 — attach spec family (deepest-eligible insertion invariant)
feat(MT.30.1): attempt 1 — witness tree type, path API, Proper/IsGood
feat(MT.20.4): attempt 1 — padded Option log + countLog + pad lemmas
feat(MT.20.3): attempt 1 — stopping time R + R_le + finitary glue
feat(MT.20.2): attempt 1 — Fin.induction run + run_count_le invariant
feat(MT.20.1): attempt 1 — resampling step with certificate-carrying payload
feat(MT.10.2): attempt 1 — DeterminedBy (event determined by vbl set)
feat(MT.10.1): attempt 1 — overlap graph + Γ⁺ membership lemmas
feat(MT.10.3): attempt 1 — truncated-table measure defs (Sigma-indexed ΩN)
```

## Files

| File | Contents |
| --- | --- |
| `TCSLean/MoserTardos/VariableModel.lean` | The variable model: `overlapGraph`/`gammaPlus`, `DeterminedBy`, truncated table `ΩN` with laws `μN`/`μπ`. |
| `TCSLean/MoserTardos/Algorithm.lean` | The resampling algorithm: state/step/run, stopping time `R`, padded log + `countLog`, measurability. |
| `TCSLean/MoserTardos/WitnessTree.lean` | Witness trees: tree type and path API, deepest-eligible construction, `treeAt`/`T`, structural lemmas. |
| `TCSLean/MoserTardos/Coupling.lean` | The τ-check, profile inequality, `check_probability`, and the coupling lemma. |
| `TCSLean/MoserTardos/GaltonWatson.lean` | Galton–Watson weight algebra: `gwWeight` telescope, tree-domain `Fintype`, canonical domain and `gwWeight_sum_le_one`. |
| `TCSLean/MoserTardos/Basic.lean` | The canonical form `canon`, the counting identity, `moserTardos_bound` and the total/tail/exists corollaries. |
| `TCSLean/MoserTardos/Symmetric.lean` | `moserTardos_symmetric` — the symmetric form of the LLL. |

🤖 Generated with [Claude Code](https://claude.com/claude-code)
