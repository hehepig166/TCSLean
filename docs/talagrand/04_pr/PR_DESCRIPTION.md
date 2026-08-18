# PR: Talagrand's Convex-Distance Concentration Inequality (TCSLean)

**Branch:** `zzk/talagrand` (based on `main`)

## Summary

This PR transfers **Talagrand's convex-distance concentration inequality** on finite discrete
product probability spaces into the new module `TCSLean/Talagrand/TalagrandInequality.lean`
(~2540 lines, 0 `sorry`, full `lake build` passes with 0 warnings), namespace
`TCSLean.Talagrand`, mathlib v4.32.0.

Main theorem (`TCSLean.Talagrand.talagrand_convexDistance`):

```lean
μ(A) * ∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ) ≤ 1
```

for `A` nonempty in a product of finite probability spaces, together with its tail bounds and the
classical dual-form characterization of the convex distance. This matches Talagrand's original
result (constant 1/4, exponent d_A²) and the Pollard (2006) presentation.

## What's formalized

**Definitions**
- `mismatchVector` — coordinatewise {0,1} mismatch indicator `v(x,y)_i = 1[x_i ≠ y_i]`
- `convexMismatchSet` — `convexHull ℝ (mismatchVector x '' A)`
- `convexDistance` — `Metric.infDist 0 (convexMismatchSet x A)`
- `sectionSet` / `projectionSet` — sections and projection for the coordinate induction

**Core proof infrastructure**
- `convexDistance_recursion` — the key geometric recursion
  `d_A(x,ω)² ≤ (1−t)·d_B(x)² + t·d_{A_ω}(x)² + (1−t)²` (with the nonempty-section hypothesis;
  the empty-section case is covered exactly by `convexDistance_snoc_empty_section_eq`)
- `talagrand_real_variable_lemma` — the classical lemma
  `e^{(1−t)²/4}·r^(−t) ≤ 2−r` for `0 < r ≤ 1` with `t = max(0, 1+2·log r)`
- `talagrand_algebraic_assembly` — generic Fintype assembly closing the induction
- `exp_holder`, `measure_pi_snoc_decomposition`, `measure_decomposition_S` — Hölder/Fubini machinery

**Main theorem & corollaries**
- `talagrand_convexDistance` — the main exponential-moment inequality (induction on `n`)
- `talagrand_convexDistance_tail` — `μ(A)·μ{d_A ≥ t} ≤ e^(−t²/4)`
- `talagrand_convexDistance_tail_half` — `μ{d_A ≥ t} ≤ 2e^(−t²/4)` when `μ(A) ≥ 1/2`
- `talagrand_convexDistance_tail_neg` — the complement form
- `talagrand_convexDistance_two_sided` — set-level two-sided interface as a conjunction of two
  independent implications (each antecedent `μ(·) ≥ 1/2` implies its own tail bound)
- `talagrand_convexDistance_integral_le_one_div` — `∫ exp(d_A²/4) ≤ 1/μ(A)` under `μ(A) > 0`

**Classical equivalence (bridge theorem)** — `convexDistance_eq_dual`

```lean
convexDistance x A = sSup {r | ∃ w, ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧
  r = ⨅ y : A, w ⬝ᵥ mismatchVector x y}
```

i.e. `D(x,A) = sup_{w≥0, ‖w‖≤1} inf_{y∈A} Σᵢ wᵢ·1[xᵢ≠yᵢ]` (Pollard 2006), closing the interface
loop between our definition and the textbook weighted-Hamming/supremum form. Supported by:
- `iInf_inner_convexHull` — the convex hull does not change the infimum of a linear functional,
  in the subtype form `(⨅ z : convexHull ℝ M, w ⬝ᵥ z.1) = (⨅ v : M, w ⬝ᵥ v.1)` (nonneg
  hypotheses supply boundedness; see the conventions note on the ℝ iInf degeneracy)
- `convexMismatchSet_nearest_point` — compactness of the convex mismatch set (finite hull in
  finite dimension), nearest-point existence, the variational inequality `z ⬝ᵥ (u−z) ≥ 0`, and
  membership in the nonneg orthant

## Scope and conventions (important notes)

- **Scope:** finite discrete product spaces (`[∀ i, Fintype (Ω i)]`) — this is the finite version
  of the theorem, not the most general Talagrand statement for arbitrary measurable spaces.
- **Empty-set convention:** `convexDistance x ∅ = 0` because mathlib's `Metric.infDist` returns 0
  for the empty set (the classical convention is `+∞`). This is documented on the definition and
  proved as `convexDistance_empty`; all theorems that need the genuine distance assume
  `A.Nonempty`, so the convention never affects the main theorem.
- **`1/μ(A)` equivalence:** the statement `∫ exp(d_A²/4) ≤ 1/μ(A)` requires `μ(A) > 0`
  (in Lean reals `1/0 = 0`, so the unconditional form is false for nonempty null sets). It is
  formalized as `talagrand_convexDistance_integral_le_one_div`.
- **Two-sided bound:** the set-level `two_sided` theorem is an implication pair with no
  nonemptiness hypotheses (each antecedent `μ(·) ≥ 1/2` implies its own tail bound). The genuine
  median-based two-sided concentration `P(|f − med f| ≥ s) ≤ 4e^(−s²/(4L²))` (via the two
  different sets `{f ≤ m}`, `{f ≥ m}`) is reserved as future work — it additionally requires a
  hypothesis relating deviations of `f` from its median to the convex distance from the
  lower/upper median sets (e.g. `f(x) ≥ m + s ⟹ d_{A₋}(x) ≥ s/L`); it does not follow from the
  set-level implications alone.

## Transfer from StatsMLlib

This is a faithful transfer of the formalization developed in
`StatsMLlib` (branch `zzk/talagrand-gpt-review`, commit `fe81d29`), with:

- module path `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
  → `TCSLean/Talagrand/TalagrandInequality.lean` (file renamed from `ConvexDistance` to match
  the project name), declarations wrapped in
  `namespace TCSLean.Talagrand` (the original had no namespace);
- one syntax fix: the source file was missing the closing `end` of its top-level
  `noncomputable section` (the original built only because the file was elaborated through the
  old pipeline's partial-file workflow; the standalone module now closes both the section and
  the namespace);
- mathlib pinned to the same version as the source development (v4.32.0); the TCSLean
  `lakefile` adopts StatsMLlib's linter set (weak-form `hashCommand`/`missingEnd`/`cdot`/
  `dollarSyntax`/`lambdaSyntax`/`longLine`/`oldObtain`/`refine`/`setOption`).

## Verification

- `lake build` passes with 0 errors, 0 warnings.
- No `sorry`, `admit`, or custom `axiom` anywhere.
- `#print axioms` on every theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- All statements cross-checked against an independent review
  (docs/talagrand/03_gpt_review/2026_08_14.md + `_v2`); the review's findings are addressed
  (comment fixes, restructured two-sided theorem, the 1/μ(A) corollary, and the bridge theorem).
  Two statements that looked plausible but were false were caught and fixed during development:
  the naive empty-section recursion (now `convexDistance_snoc_empty_section_eq` with
  `A.Nonempty`) and the set-membership iInf form of the dual (degenerate on ℝ via `sInf ∅ = 0`;
  fixed with the subtype form `⨅ y : A, …`, and the corresponding `iInf_inner_convexHull` lemma
  was refactored to the subtype form as well).

## Files changed

- `TCSLean/Talagrand/TalagrandInequality.lean` — new module (all content)
- `lakefile.toml` — mathlib pinned to v4.32.0; linter set aligned with StatsMLlib
- `lake-manifest.json` — updated by `lake update`
- `docs/talagrand/` — full development record (proposal, surveys, blueprint with per-item logs,
  GPT review, PR description)

## References

- M. Talagrand, *Concentration of measure and isoperimetric inequalities in product spaces*
- D. Pollard, *A note on Talagrand's convex hull concentration inequality*,
  https://arxiv.org/abs/math/0611770
- T. Tao, *Talagrand's concentration inequality*,
  https://terrytao.wordpress.com/2009/06/09/talagrands-concentration-inequality/
- Blueprint and development log: docs/talagrand/02_blueprint/BLUEPRINT.md (all items done)
