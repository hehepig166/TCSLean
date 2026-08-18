# PR Description: Lovász Local Lemma (TCSLean)

- **Target:** `hehepig166/TCSLean`, branch `zzk/lovasz-local-lemma` → `main`
- **Proposal:** [`docs/lovasz/01_proposal/proposal.md`](../01_proposal/proposal.md)
- **Blueprint:** [`docs/lovasz/02_blueprint/BLUEPRINT.md`](../02_blueprint/BLUEPRINT.md)
- **File:** `TCSLean/Lovasz/LovaszLocal.lean` (new, module `TCSLean.Lovasz.LovaszLocal`,
  namespace `TCSLean.Lovasz`)

## Summary

This PR formalizes the **Lovász local lemma** (Alon–Spencer ch. 5): a finite family of measurable
bad events on a probability space, equipped with a dependency graph `G` on the index type, can be
simultaneously avoided with positive probability, provided each bad event is sufficiently unlikely
relative to its neighborhood. Both the **asymmetric form** (per-event weights `x i ∈ [0, 1)`) and
the **symmetric forms** (`e·p·(d+1) ≤ 1`, the sharp `(d+1)^(d+1)·p ≤ d^d`, and `4·p·d ≤ 1`) are
covered, together with the existence-witness, ℝ-valued, and conditional-probability corollaries.

## Main declarations (all in `namespace TCSLean.Lovasz`)

- `bset`, `IsDependencyGraph`, `IsDependencyGraphStrong` (+ the bridge theorems
  `IsDependencyGraph.of_strong` / `IsDependencyGraph.strong` / `isDependencyGraph_iff_strong`) —
  the event "none of the bad events indexed by `S` occurs" and the two dependency-graph
  formulations: `IsDependencyGraph` (avoidance-event formulation) and `IsDependencyGraphStrong`
  (global generated-σ-algebra formulation, no `[Fintype ι]` needed), proven equivalent.
- `lovaszLocalLemma` — the asymmetric LLL (ENNReal form):
  `ENNReal.ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)`.
- `lovaszLocalLemma_pos`, `lovaszLocalLemma_exists`, `lovaszLocalLemma_probReal` — the existence
  form, the witness form `∃ ω, ∀ i, ω ∉ A i`, and the ℝ-valued corollary via `μ.real`.
- `lovaszLocalLemma_symmetric_optimalWeight`, `lovaszLocalLemma_symmetric`,
  `lovaszLocalLemma_4pd` — the symmetric forms.
- `lovaszLocalLemma_bset_pos`, `lovaszLocalLemma_cond` — positivity of `bset` events and the
  conditional-probability form of the key lemma (`μ[A i | bset A S] ≤ ofReal (x i)`).
- Supporting API: `bset_empty`, `bset_insert`, `bset_subset_bset_of_subset`, `bset_union`,
  `bset_univ_eq_iInter` (`@[simp]` where appropriate), `measurableSet_bset` (`[measurability]`),
  `ofReal_one_sub`, `measure_bset_insert`, `measure_bset_insert_le`, `prob_bset_inter_prod`,
  `lll_prob_bset`, and the `cond` glue lemmas `cond_eq_of_indepSet`, `cond_compl_eq_one_sub`,
  `cond_le_one`.

## Design decisions

- **Index type:** arbitrary `[Fintype ι] [DecidableEq ι]` — the proof is an order-free *peeling*
  strong induction (`Finset.strongInductionOn`) over subsets `S`, so no linear order on `ι` is
  needed and no conditional probability or division appears anywhere in the core proof
  (everything is multiplicative ENNReal).
- **Dependency graph:** `SimpleGraph ι` (loopless), with `[DecidableRel G.Adj]` as a theorem
  hypothesis; neighborhoods via `G.neighborFinset`.
- **Hypothesis form:** `IsDependencyGraph` — the avoidance-event formulation (exactly the
  independence fragment the proof consumes); the equivalence with the classical
  generated-σ-algebra formulation (`IsDependencyGraphStrong`, global form) is proved in the same
  file, including the explicit iff.
- **Weights:** flat `x : ι → ℝ` with `0 ≤ x i` and `x i < 1`; the LLL condition is bundled:
  `μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))`.

## Transfer from StatsMLlib

Faithful transfer of the formalization developed in `StatsMLlib` (branch
`zzk/lovasz-local-lemma-gptv2`, commit `c6e4461`), with:

- module path `StatsMLlib/Probability/LovaszLocal.lean`
  → `TCSLean/Lovasz/LovaszLocal.lean`, namespace wrapped as `TCSLean.Lovasz`;
- no proof changes (the source already builds on mathlib v4.32.0, which TCSLean is pinned to
  since the Talagrand PR).

## Verification

- All declarations `sorry`-free; axioms used: `propext`, `Classical.choice`, `Quot.sound` only.
- Warning-free under the project's lakefile linters; `lake build` passes with 0 errors,
  0 warnings (1923 jobs for this module).
- All 21 blueprint items `done`, every one on attempt 1; the proof was reviewed externally
  (docs/lovasz/03_gpt_review/2026_08_15.md + `_v2`) and its main suggestions (the strong-form
  bridge and the GPT-v2 follow-up items 80.25/90.5) are included.

## References

- [alonSpencer2016] N. Alon, J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016, ch. 5.
- [edmondsPaulson2024] C. Edmonds, L. C. Paulson, *Formal Probabilistic Methods for Combinatorial
  Structures using the Lovász Local Lemma*, CPP 2024.
- [erdosLovasz1975] P. Erdős, L. Lovász, *Problems and results on 3-chromatic hypergraphs and some
  related questions*, Infinite and Finite Sets, 1975.

## Follow-ups (out of scope for this PR)

- The constructive **Moser–Tardos** algorithmic LLL — arrives as a separate TCSLean PR
  (`TCSLean/MoserTardos/`).
- Variable model (events determined by disjoint independent-variable sets) via
  `Probability.Independence.FinsetPi`, then applications (bounded-dependency k-SAT, hypergraph
  coloring).
- Lopsided LLL; Shearer's bound.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
