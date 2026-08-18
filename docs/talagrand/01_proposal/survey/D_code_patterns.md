# D. Code Patterns & Conventions

Survey of `/Users/zhuzekai/workspace/StatsLean/StatsMLlib/StatsMLlib`, mathlib `v4.32.0`.

## 1. File Header Format

Every file opens with a mathlib-style block-comment header. Two "generations" of attribution exist (older 2024 files vs. newer 2026 files), but the format is identical:

```lean
/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
```

Newer files (Chernoff, SubGaussian, LipschitzConcentration, EfronStein, Symmetrization-era 2026 work): `Copyright (c) 2026 Yuanhe Zhang. All rights reserved.` / `Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu`. AUTHORS.md confirms the two-line split: `Copyright` line = copyright holder; `Authors` line = significant contributors; they are distinct claims.

**Import block.** Structure: StatsMLlib imports first (one per line, dot-separated paths), then Mathlib imports. Within a group, roughly alphabetical. Examples:

```lean
-- McDiarmid.lean
import StatsMLlib.Probability.Moments.Expectation
import StatsMLlib.Probability.Concentration.Hoeffding
import StatsMLlib.Probability.Independence.FinsetPi
import Mathlib.Tactic.Cases

-- Chernoff.lean (no StatsMLlib deps)
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Monotone
...
```

`Mathlib.Probability.Notation` (gives `μ[X]`, `∀ᵐ` etc.) is imported explicitly where needed (Symmetrization, Maximal, Moments/Expectation).

**Module docstring** (`/-! ... -/`), standardized section order:

```lean
/-!
# McDiarmid's Inequality

Martingale and independence machinery for bounded-difference concentration under product measures.

## Main definitions

This module formulates bounded differences directly as hypotheses on functions of independent
coordinates.

## Main results

* `mcdiarmid_inequality_pos`: upper-tail McDiarmid inequality.
* `mcdiarmid_inequality_neg`: lower-tail McDiarmid inequality.
* `bounded_difference_iff`: equivalent forms of the bounded-difference condition.
-/
```

Observed sections, in order of frequency: `## Main definitions` (always), `## Main results` (always, bulleted `` * `name`: description`` entries), `## References` (rare — only Hoeffding.lean and Statistics/Regression/LeastSquares/L1/CoveringBound.lean), `## Approach` (LipschitzConcentration, GaussianTensorization). Capitalization varies (`## Main Results` in EfronStein). In-body section headers use `/-! ### ... -/` (e.g. `/-! ### Hoeffding's lemma restricted to t ≥ 0-/`, `## Variance Decomposition` in EfronStein, `## Tail bounds for sub-Gaussian processes` in SubGaussian).

**`open` commands.** Immediately after the docstring, before namespace:
- Hoeffding/Maximal/Symmetrization: `open MeasureTheory ProbabilityTheory Real`
- McDiarmid: `open MeasureTheory ProbabilityTheory`
- Chernoff: `open MeasureTheory Set Real Filter Topology` + `open scoped ENNReal NNReal BigOperators`
- HansonWright: `open MeasureTheory ProbabilityTheory Real` + `open scoped BigOperators NNReal`
- SubGaussian: `open MeasureTheory ProbabilityTheory Real Set Metric Filter` + `open scoped ENNReal BigOperators NNReal Topology`
- LipschitzConcentration: `open MeasureTheory ProbabilityTheory Real Finset BigOperators Function GaussianMeasure GaussianSobolev` + `open scoped ENNReal`; a mid-file `open Filter Topology` + `open scoped NNReal Topology` at line 863.

**Namespace conventions** (mixed):
- `namespace ProbabilityTheory` — Hoeffding.lean, Maximal.lean (theorems then get fully-qualified names like `ProbabilityTheory.hoeffding`).
- Custom namespace — HansonWright.lean: `namespace HansonWright`; LipschitzConcentration.lean: `namespace GaussianLipConcen`.
- **No namespace** — McDiarmid.lean has no `namespace` at all; its declarations are top-level, with mathlib-style extensions written fully qualified (e.g. `theorem ProbabilityTheory.iIndepFun.comp_right`), and its docstring cites them as bare `` `mcdiarmid_inequality_pos` ``.

## 2. Proof Structure Patterns

**Variable introduction.** Universe + `variable` at top of namespace:

```lean
namespace ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω := by volume_tac)
```

Notable: Hoeffding gives `μ` a `:= by volume_tac` default; McDiarmid instead uses bare `variable {μ : Measure Ω} [IsProbabilityMeasure μ]` later in the file. Variables accumulate through the file (McDiarmid: `variable {𝓧 : Type*}`, then `variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]`, then `variable {μ : Measure Ω} [IsProbabilityMeasure μ]`, then `variable {X' : Fin m → Ω → 𝓧} {f' : (Fin m → 𝓧) → ℝ}`, then `variable [hnonempty𝓧 : Nonempty 𝓧]`). `omit [IsProbabilityMeasure μ] in` (McDiarmid, EfronStein, Maximal) is used to drop unused hypotheses on individual declarations.

**Theorem statement style.** Explicit named hypotheses, `[IsProbabilityMeasure μ]` as instance binder, noncomputable content implicit:

```lean
theorem hoeffding [IsProbabilityMeasure μ] (t a b : ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8) := by
```

**Auxiliary declarations.** Helper `lemma`s are plain (unqualified) with descriptive names; McDiarmid uses an `h`-prefix convention for its martingale machinery (`hAY`, `hBddAbove`, `hYB`, `hmeasurableY`, `hYbdd`, `hintegrablelefts`, `hintegrableAB`, `hAB`, `hmartingale`, `hhoeffding_V`, `heqind`). Maximal.lean uses `private theorem convexon_exp`. Numerical machinery is `noncomputable def`:

```lean
noncomputable def expressionY (μ : Measure Ω) (X' : Fin m → Ω → 𝓧) (f' : (Fin m → 𝓧) → ℝ) (k : Fin m.succ) (Xk : Fin k → 𝓧) : ℝ := ...
```

**`pos`/`neg` tail handling.** Two patterns:
1. Hoeffding: a restricted lemma `hoeffding_nonneg` (hypothesis `(ht : 0 ≤ t)`), and the full theorem branches:

```lean
  by_cases h' : 0 ≤ t
  case pos =>
    exact hoeffding_nonneg μ t a b h' hX h h0
  case neg =>
    simp only [not_le] at h'
    suffices ∫ ω, rexp (- t * - X ω) ∂μ ≤
      rexp ((- t) ^ 2 * ((- a) - (- b)) ^ 2 / 8) from by ...
    apply hoeffding_nonneg _ _ _ _ (by linarith : 0 ≤ - t) hX.neg
```

2. McDiarmid: the `neg` theorem reduces to `pos` applied to `-f` (via `rw [←abs_neg]`, `le_neg`); the `pos'` theorem reduces to `pos` by instantiating coordinates `X i ω := X' (ω i)` and using `pi_comp_eval_iIndepFun`.

**Proof tactics observed.** `calc` chains (often with `by ring` steps), `have` blocks with short names (`q`, `q0`–`q4`, `hlefteq`, `hrighteq`, `h1`, `hf`), `set`/`let` for definitions with `dsimp only [g, A]` unfolding, `filter_upwards with ω`, `obtain ⟨c, ⟨cq, cq'⟩⟩ := ...`, `by_cases` with `case pos/neg` or `if ... then ... else`, `constructor`, `apply` with `.comp`, `rw`/`simp only`, `linarith`, `ring`, `field_simp`, `grind only [cases Or]` (one use in Hoeffding), `measurability` (one use in McDiarmid `pos'`), `nth_rewrite`, `convert`, `simpa only [...] using ...`. `match n with | 0 => ... | 1 => ...` used in EfronStein's main theorem.

**Typeclass usage.**
- `[IsProbabilityMeasure μ]` — default for concentration theorems (Hoeffding, Chernoff subGaussian form, McDiarmid). EfronStein: `variable {μs : Fin n → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]` then `[NeZero n]` on lemmas.
- `[IsFiniteMeasure μ]` — the general Chernoff CGF form.
- `[Fintype ι]` (McDiarmid), `[DecidableEq ι]` (McDiarmid, Maximal, EfronStein), `[Nonempty 𝓧]`, `[NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]` for vector-valued integrals.
- Induction over `Fin` via `induction' k with k ih` + `Fin.sum_univ_castSucc`.

## 3. Naming Conventions

- **Theorems (public results):** snake_case, inequality-name-first or subject-first: `hoeffding`, `hoeffding_nonneg`, `mcdiarmid_inequality_pos`, `mcdiarmid_inequality_neg`, `mcdiarmid_inequality_pos'`, `chernoff_bound_cgf`, `chernoff_bound_subGaussian`, `maximal_inequality_finset`, `maximal_inequality_supR`. Exception: `efronStein` (proper noun, camelCase). `subGaussian_tail_bound_one_sided` / `subGaussian_tail_bound` follow the pos/neg split but as one-/two-sided.
- **Lemmas (auxiliary):** snake_case, descriptive: `bounded_difference_iff`, `double_integral_indep_eq_integral`, `expectation_const`, `Y_snoc_eq`, `bound_f'`, `condExpExceptCoord_stronglyMeasurable`, `variance_ge_two_cov_sub_variance`, `symmetric_inner_apply_eq_sum_eigenvalues_repr`. Local proofs-of-record often `h`-prefixed (`hAY`, `hBddAbove`, `hAB`, `hmartingale`, `h1`, `hlefteq`).
- **Definitions:** camelCase: `expressionY`, `expressionA`, `expressionB`, `expressionV`, `condExpExceptCoord`, `condVarExceptCoord`, `IsSubGaussian`, `HasSubGaussianPsi2Bound`, `subGaussianPsi2Norm`, `frobeniusNorm`, `randomQuadraticForm`. (Inherited mathlib names stay as-is: `cgf`, `mgf`, `variance`, `HasSubgaussianMGF`.)
- **Variable names:** `Ω` sample space, `ω` sample point, `μ` measure, `X : Ω → ℝ` random variable, `X' : ι → Ω → 𝓧` or `X' : Ω → 𝓧` coordinate variable, `f` / `f'` function (`f'` doubles as derivative in Hoeffding — context-disambiguated), `c` / `c' : ι → ℝ` bounded-difference coefficients, `t`, `t''` MGF parameters (`t'' := 4 * ε * t` in McDiarmid), `ε` tail threshold, `u` threshold in Chernoff, `𝓧` coordinate value type, `m`/`n` cardinalities, `ι` index type, `σ` variance proxy. Hypothesis names: `hX`/`hX'`/`hX''` (measurability), `hIndep'` (independence), `hf`/`hfι` (bounded difference), `hf'`/`hf''` (function measurability), `ht`, `hε`, `h0` (zero mean), `hμ` etc.

## 4. Reference Format

- **No `references.bib` in StatsMLlib.** Only `.lake/packages/mathlib/docs/references.bib` exists (mathlib's own). Do not expect to extend a project bib.
- Citations are inline docstring keys of the form `[authorYear]` (lowercase, no spaces): Hoeffding.lean:

```lean
## References

We follow [martin2019] and [mehryar2018] for the proof of Hoeffding's lemma.
```

- `## References` section is used sparingly (only 2 files project-wide). Most files rely solely on `## Main definitions`/`## Main results`. So for Talagrand, a `## References` section citing e.g. `[talagrand1996]` or `[bousquet2004]` would follow the Hoeffding precedent. AUTHORS.md and CONTRIBUTING.md (which requires "a Mathlib-style file header and module docstring") confirm attribution rules.

## 5. API Design Patterns (McDiarmid deep dive)

**Public-facing theorem names** (docstring-listed): `mcdiarmid_inequality_pos`, `mcdiarmid_inequality_neg`, `bounded_difference_iff`; a fourth variant `mcdiarmid_inequality_pos'` exists (product-measure form) but is not in the docstring. Internal `mcdiarmid_inequality_aux` is the Fin-indexed core.

**Signature of the main theorem:**

```lean
theorem mcdiarmid_inequality_pos
  (X : ι → Ω → 𝓧) (hX : ∀ i, Measurable (X i))
  (hX' : iIndepFun X μ) {f : (ι → 𝓧) → ℝ}
  {c : ι → ℝ}
  (hf : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f x - f (Function.update x i x')| ≤ c i)
  (hf' : Measurable f)
  {ε : ℝ} (hε : ε ≥ 0)
  {t : ℝ} (ht' : t * ∑ i, (c i) ^ 2 ≤ 1) :
  (μ (fun ω : Ω ↦ (f ∘ (Function.swap X)) ω - μ[f ∘ (Function.swap X)] ≥ ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp := by
```

Key design choices:
- **Independence:** `iIndepFun X μ` on a single space Ω (not a product-space model); the Fin-indexed core is reached via `Fintype.equivFinOfCardEq`.
- **Bounded-difference condition:** absolute-value coefficient form `∀ i x x', |f x - f (Function.update x i x')| ≤ c i`; `bounded_difference_iff` proves it equivalent to the one-sided form.
- **Normalization:** scale `t` with `t * ∑ i, (c i)^2 ≤ 1`, bound `exp (-2 * ε^2 * t)`; optimization occurs inside (`t'' := 4 * ε * t`).
- **Tail event:** written as set comprehension `{ω | ... ≥ ε}` with `.toReal` conversion, i.e. ENNReal measure coerced to ℝ.
- **`neg` variant:** same hypotheses, event `... ≤ -ε`, proven by applying `pos` to `-f`.
- **`pos'` variant (product measure):** `{X' : Ω → 𝓧} (hX'' : Measurable X')` on `ι → Ω` with product measure:

```lean
local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

theorem mcdiarmid_inequality_pos'
  {X' : Ω → 𝓧} (hX'' : Measurable X') {f' : (ι → 𝓧) → ℝ} {c' : ι → ℝ}
  (hfι : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f' x - f' (Function.update x i x')| ≤ c' i)
  (hf'' : Measurable f') {ε : ℝ} (hε : ε ≥ 0) {t : ℝ} (ht' : t * ∑ i, (c' i) ^ 2 ≤ 1) :
  (μⁿ (fun ω : ι → Ω ↦ (f' (X' ∘ ω)) - μⁿ[fun ω : ι → Ω ↦ f' (X' ∘ ω)] ≥ ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp
```

- **Product-measure notation precedent:** EfronStein uses `local notation "μˢ" => Measure.pi μs` (reused in Entropy/Conditional files with the comment "consistent with EfronStein.lean"). Local notations are declared near the theorem that needs them (line 1042 of McDiarmid).
- **Martingale machinery is by direct integration**, not condexp: a comment block documents `Y_k`, `A_k`, `B_k`, and the martingale identity is `hmartingale`, proved with `double_integral_indep_eq_integral` + `iIndepFun.indepFun_finset`.
- Hoeffding is the building block: `hhoeffding_V` applies `hoeffding μ t'' a b` to the martingale-difference variable.

## 6. Typeclass & Notation Patterns

- `[IsProbabilityMeasure μ]`: standard hypothesis on theorems, imported from `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` (also `MeasureTheory.Measure.Typeclasses.Finite` for `IsFiniteMeasure`). Constructed in proofs via `isProbabilityMeasure_tilted` / `isProbabilityMeasure_iff.mp`.
- `AEMeasurable X μ` vs `Measurable`: Hoeffding (MGF/integral-heavy, general measure) uses `AEMeasurable X μ` (4 occurrences); McDiarmid and EfronStein (finite independence model, `Function.swap`/`update` combinators) use `Measurable (X i)` and `Measurable f` (16 occurrences), converting `StronglyMeasurable f'` where needed. `hX.neg`, `hX.mono_ac`, `Measurable.aemeasurable`, `AEMeasurable.aestronglyMeasurable` are the conversion idioms.
- `∀ᵐ ω ∂μ` (from Mathlib.Probability.Notation) for a.e. statements, typically consumed with `filter_upwards [h] with ω hω` or `filter_upwards with ω`.
- `μ[X]` expectation notation (Mathlib.Probability.Notation, imported by Moments/Expectation.lean and used in Hoeffding `(h0 : μ[X] = 0)`, McDiarmid `μ[f ∘ (Function.swap X)]`, EfronStein `μˢ`-variants). Bare integrals `∫ x, f x ∂μ` coexist freely.
- `probReal`: not a StatsMLlib definition — comes from mathlib; the idiom `probReal_univ` appears in `simp only` blocks whenever `∫ (_ : Ω), c ∂μ` simplifies (Hoeffding, McDiarmid, EfronStein). Tail probabilities are stated as `(μ {ω | ε ≤ X ω}).toReal` (ENNReal-to-ℝ coercion), and `ENNReal.toReal_mono`/`ENNReal.one_ne_top` appear for the trivial case.
- Notation for product measures: `μⁿ`, `μˢ` (local), `𝔼 := EuclideanSpace ℝ (Fin n)` (LipschitzConcentration), `Ent[f; μ]` (Entropy/Basic).
- Scoping: `open scoped ENNReal NNReal BigOperators Topology` where those notations appear.

## 7. Linter Constraints

From `/Users/zhuzekai/workspace/StatsLean/StatsMLlib/lakefile.lean`:

```lean
abbrev linter : Array LeanOption := #[
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.missingEnd, true⟩,
  ⟨`linter.cdot, true⟩,
  ⟨`linter.dollarSyntax, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.longLine, true⟩,
  ⟨`linter.oldObtain, true,⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.setOption, true⟩
]

abbrev options := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ linter.map fun s ↦ { s with name := `weak ++ s.name }
```

Also: `require mathlib from git ... @ "v4.32.0"`; `lean_lib «StatsMLlib» where globs := #[.submodules `StatsMLlib]`; optional `doc-gen4` when `lake env dev`.

Consequences for new code (verified against mathlib's linter sources in `.lake/packages/mathlib/Mathlib/Tactic/Linter/`):
- **No `#`-commands** (`#check`, `#eval`, `#guard`, …) left in final code — `linter.hashCommand` (HashCommandLinter.lean: "commands starting with `#` ... are intended to be transient").
- **Every `namespace`/`section` needs its `end`** (`linter.missingEnd`).
- **Bullets must be `·`**, not `;` or other separators (`linter.cdot`; Style.lean checks the `·` atom).
- **No `$` notation** (`linter.dollarSyntax`).
- **Use `fun`, never `λ`** (`linter.style.lambdaSyntax`).
- **Lines ≤ 100 characters** (`linter.longLine`). The observed sources respect this (long hypotheses are wrapped at `(` with 4-space continuations).
- **`obtain` must use the modern pattern syntax** (`linter.oldObtain`).
- **Prefer `exact` over `refine` when it closes the goal** (`linter.refine`).
- **No `set_option` in files** (`linter.setOption`).
- **`autoImplicit := false`**: every variable must be explicitly declared — hence the pervasive `universe u` / `variable {Ω : Type u}` declarations and `{𝓧 : Type*}`-style binders.
- `pp.unicode.fun` means `fun a ↦ b` (arrow notation) is the printed style; sources consistently write `fun ω ↦ ...`.
- The same linters are registered as *weak* variants during `lake build` (warnings, not errors).

## Summary: Template for New File

A concrete header for `StatsMLlib/Probability/Concentration/ConvexDistance.lean` following every convention observed:

```lean
/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
import StatsMLlib.Probability.Concentration.Hoeffding
import StatsMLlib.Probability.Concentration.McDiarmid
import StatsMLlib.Probability.Independence.FinsetPi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.Tactic.Cases

/-!
# Talagrand's Convex-Distance Inequality

Concentration of convex Lipschitz functions under product measures via the
convex-distance decomposition.

## Main definitions

This module works with the bounded-difference and product-measure machinery from
`StatsMLlib.Probability.Concentration.McDiarmid`.

## Main results

* `convex_distance`: the convex-distance functional `d_C(x)`.
* `talagrand_convex_distance_pos`: upper-tail Talagrand inequality.
* `talagrand_convex_distance_neg`: lower-tail Talagrand inequality.
* `talagrand_convex_distance_pos'`: product-measure formulation.

## References

We follow [talagrand1996] for the proof of the convex-distance inequality.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {𝓧 : Type*}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

-- local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

theorem talagrand_convex_distance_pos
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {X : ι → Ω → 𝓧} (hX : ∀ i, Measurable (X i)) (hX' : iIndepFun X μ)
  {f : (ι → 𝓧) → ℝ} (hf' : Measurable f) {ε : ℝ} (hε : 0 ≤ ε) : ... := by
  -- following the McDiarmid structure: reduce to Fin, apply Hoeffding to martingale differences
  ...

end
```

Notes on the template: follow McDiarmid's namespace-less top-level style only if consistency with that file is preferred — otherwise use `namespace ProbabilityTheory` like Hoeffding/Maximal (the docstring bullet names must match the actual fully-qualified names, as Maximal does with `` `ProbabilityTheory.maximal_inequality_finset` ``). Keep the bounded-difference-style hypothesis shape, `(μ {ω | ... ≥ ε}).toReal` tail statements, `exp`-of-`-2*ε^2*t`-style bounds, `hX'`/`hX''`/`hfι`/`hε` hypothesis names, `·` bullets, `fun`/`↦` arrows, and ≤100-char lines.
