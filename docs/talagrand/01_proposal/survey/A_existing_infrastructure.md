# A. Existing Infrastructure Audit

## 1. Concentration Inequalities

All files in `/Users/zhuzekai/workspace/StatsLean/StatsMLlib/StatsMLlib/Probability/Concentration/`.

### Chernoff.lean (70 lines)
- **Main theorems:**
```lean
theorem chernoff_bound_cgf {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} {ε t : ℝ} (ht : 0 ≤ t)
    (h_int : Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (-t * ε + ProbabilityTheory.cgf X μ t)

theorem chernoff_bound_subGaussian {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ u : ℝ} (hσ : 0 < σ) (hu : 0 < u)
    (h_sgb : ∀ t : ℝ, ProbabilityTheory.cgf X μ t ≤ t^2 * σ^2 / 2)
    (h_int : ∀ t : ℝ, Integrable (fun ω => exp (t * X ω)) μ) :
    (μ {ω | u ≤ X ω}).toReal ≤ exp (-u^2 / (2 * σ^2))
```
- **Pattern:** Single variable; no product measures, no independence, no induction, no convexHull/infDist/EuclideanSpace.

### Hoeffding.lean (194 lines, `namespace ProbabilityTheory`)
- **Main theorems:**
```lean
theorem hoeffding [IsProbabilityMeasure μ] (t a b : ℝ) {X : Ω → ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    mgf X μ t ≤ exp (t^2 * (b - a)^2 / 8)
```
- **Pattern:** Taylor expansion of cgf via tilted measures; single variable; no product measures or induction.

### McDiarmid.lean (1057 lines, root namespace)
- **Main theorems:**
```lean
theorem mcdiarmid_inequality_pos
  (X : ι → Ω → 𝓧) (hX : ∀ i, Measurable (X i))
  (hX' : iIndepFun X μ) {f : (ι → 𝓧) → ℝ}
  {c : ι → ℝ}
  (hf : ∀ (i : ι) (x : ι → 𝓧) (x' : 𝓧), |f x - f (Function.update x i x')| ≤ c i)
  (hf' : Measurable f) {ε : ℝ} (hε : ε ≥ 0) {t : ℝ} (ht' : t * ∑ i, (c i) ^ 2 ≤ 1) :
  (μ (fun ω : Ω ↦ (f ∘ (Function.swap X)) ω - μ[f ∘ (Function.swap X)] ≥ ε)).toReal ≤
    (-2 * ε ^ 2 * t).exp

theorem mcdiarmid_inequality_neg  -- same hypotheses, tail {ω | ... ≤ -ε}

theorem mcdiarmid_inequality_pos'  -- i.i.d. product version with local notation "μⁿ"
```
- **Pattern:** Martingale by direct integration (not `condexp`); `Function.update` for bounded-difference condition; induction on `Fin m`; reduces general `Fintype ι` to `Fin m` via `Fintype.equivFinOfCardEq`. No convexHull/infDist/EuclideanSpace.

### EfronStein.lean (2067 lines, root namespace)
- **Setup:** Heterogeneous product measure `local notation "μˢ" => Measure.pi μs` where `μs : Fin n → Measure Ω`, all probability measures.
- **Main theorems:**
```lean
theorem efronStein (f : (Fin n → Ω) → ℝ) (hf : MemLp f 2 μˢ) :
    variance f μˢ ≤ ∑ i : Fin n, ∫ x, (f x - condExpExceptCoord (μs := μs) i f x)^2 ∂μˢ
```
- **Pattern:** `condExpExceptCoord` defined by direct integration; `induction n with` + `match n` on 0/1 base cases. No convexHull/infDist/EuclideanSpace.

### Maximal.lean (881 lines, `namespace ProbabilityTheory`)
- **Main theorems:** `maximal_inequality_finset`, `maximal_inequality_supR`
- **Pattern:** Soft-max `exp(sup) ≤ Σ exp` + Jensen; uses `iIndepFun` per column. No convexHull/infDist/EuclideanSpace.

### HansonWright.lean (4584 lines, root section)
- **Main theorems:** `hanson_wright_inequality`, `hasHansonWrightMGF_of_subgaussian`
- **Pattern:** Heavy use of `EuclideanSpace ℝ (Fin n)`, `inner`, `iIndepFun`; `induction s using Finset.induction_on`. **No convexHull/infDist.**

### LogSobolev/ (5 files)
- **TwoPoint.lean:** `two_point_inequality`, `rothaus_lemma` (pure real analysis)
- **Bernoulli.lean (1636 lines):** `bernoulli_logSobolev`, `han_inequality` — uniform Bernoulli cube `Fin n → Bool`; `induction n with`; uses `Fin.snoc`/`Fin.castSucc`; no convexHull/infDist
- **GaussianCompactSupport.lean:** 1-D Gaussian LSI via CLT limit from Bernoulli
- **GaussianOneDim.lean (943 lines):** Extension to W¹² via density argument
- **GaussianTensorization.lean (488 lines):** `gaussian_logSobolev_W12_pi` — tensorized LSI on `Fin n → ℝ` via slice functions + entropy subadditivity; no convexHull/infDist

## 2. Independence Infrastructure

`/Users/zhuzekai/workspace/StatsLean/StatsMLlib/StatsMLlib/Probability/Independence/FinsetPi.lean` (103 lines):
```lean
theorem pi_map_eval ... (k : ι) : (Measure.pi μ).map (Function.eval k) = (μ k)
theorem pi_eval_iIndepFun ... : iIndepFun Function.eval (Measure.pi fun _ ↦ μ : Measure (ι → Ω))
theorem pi_comp_eval_iIndepFun {X : Ω → 𝓧} (hX : Measurable X) : iIndepFun (fun (i : ι) ↦ X ∘ (Function.eval i)) (Measure.pi fun _ ↦ μ)
```

Plus repo-level additions in McDiarmid.lean (`iIndepFun.comp_right`) and HansonWright (`iIndepFun_centered_sq`, `coordinateMask_indepFun_compl`).

## 3. Moment / CGF Infrastructure

- **Cumulant.lean** (387 lines): `tilt_first_deriv`, `tilt_second_deriv`, `cgf_deriv_one`/`_two`, `tilt_var_bound`, `integral_tilted`
- **Expectation.lean** (45 lines): `norm_expectation_le_of_norm_le_const`, `abs_expectation_le_of_abs_le_const`
- **Exponential.lean** (73 lines): `jensen_exp`, `mean_le_log_mgf`

## 4. Process / Sub-Gaussian

- **SubGaussian.lean** (1041 lines): `IsSubGaussian`, `IsSubGaussianProcess`, `bernstein_one_sided_of_cgf_bound`, `bernstein_two_sided_of_cgf_bound`, `subGaussian_tail_bound`
- **FiniteMaximum.lean** (214 lines): `expected_max_subGaussian`
- **Dudley.lean** (2555 lines): `dudley` — chaining bound for sub-Gaussian processes
- **TruncatedDudley.lean** (2227 lines): `truncated_dudley_entropy_bound`

## 5. Measure Theory, Topology, Analysis

- **MeasureTheory/Integral/LayerCake.lean** (37 lines): `lintegral_eq_lintegral_tail`
- **MeasureTheory/Function/L1Subsequence.lean** (26 lines): `exists_seq_tendsto_ae_of_tendsto_eLpNorm_one`
- **Topology/SeparableSpace/Supremum.lean** (80 lines): `separableSpaceSup_eq_real`
- **Topology/MetricSpace/CoveringNumber/Basic.lean** (474 lines): `IsENet`, `coveringNumber`, `packingNumber`, optimal ε-net existence
- **Analysis/MetricEntropy/Basic.lean** (1516 lines): `metricEntropy`, `sqrtEntropy`, `entropyIntegral`
- **Analysis/MetricEntropy/Chaining.lean** (327 lines): `DyadicNets`, `projectToNet`, `transitiveProj`
- **Analysis/NormedSpace/CoveringNumber/Euclidean.lean** (424 lines): `coveringNumber_euclideanBall_le`
- **Analysis/NormedSpace/CoveringNumber/L1.lean** (674 lines): L1 covering numbers

## 6. Usage Patterns in Statistics

- Gaussian product measure `stdGaussianPi n` as noise space
- Sub-Gaussian empirical process + Dudley (`SubGaussianity.lean`, `LocalGaussianComplexity.lean`)
- `gaussian_lipschitz_concentration` as key tail bound in `MasterErrorBound.lean`
- `LearningTheory/UniformDeviation/BoundedDifference.lean` — bounded-difference pattern for McDiarmid

## Summary: What's Available, What's Missing

### Available (directly reusable for Talagrand):

1. **Gaussian LSI** — `gaussian_logSobolev_W12_pi` (tensorized, `Fin n → ℝ`, `stdGaussianPi n`), derived from Bernoulli LSI via CLT
2. **LSI → CGF → tail pipeline** — `gaussian_lipschitz_concentration` in `Probability/Gaussian/LipschitzConcentration.lean`
3. **MGF/cgf calculus** — `chernoff_bound_cgf`, `hoeffding`, `bernstein_*_of_cgf_bound`
4. **Product measures & independence** — `iIndepFun`, `pi_eval_iIndepFun`, `pi_comp_eval_iIndepFun`; heterogeneous `Measure.pi μs` from EfronStein
5. **Efron–Stein** — `efronStein` with `condExpExceptCoord`, `total_variance_identity`
6. **McDiarmid** — `mcdiarmid_inequality_pos/neg` (Fintype + iIndepFun) and `pos'` (product measure)
7. **Metric entropy / chaining** — complete covering-number + Dudley infrastructure
8. **Misc** — `lintegral_eq_lintegral_tail`, `separableSpaceSup_eq_real`, `mean_le_log_mgf`, `jensen_exp`

### Missing (gaps the proposal must fill):

1. **`convexHull`** — ZERO occurrences in the entire `StatsMLlib/StatsMLlib` tree (mathlib has it, but no local infrastructure)
2. **`Metric.infDist`** — ZERO occurrences. The "convex distance" function `d_A(x) = infDist x (convexHull ℝ A)` is entirely new.
3. **No convexity-aware concentration.** The only "star-shaped" notion is `LeastSquares.IsStarShaped` (function classes). No results relate convexity of a set to concentration.
4. **No Bernoulli-cube convex-isoperimetric / Talagrand-type result.** Bernoulli LSI exists but is never specialized to convex sets.
5. **No heteroscedastic non-Gaussian product-cube concentration** beyond McDiarmid (bounded differences) and the uniform Bernoulli LSI.
6. For the Gaussian form of Talagrand: the existing `gaussian_lipschitz_concentration` only covers linear `exp(-t²/(2L²))` bounds; nothing covers `exp(-t²)`-type bounds from `exp(λ‖X‖²)`-integrability.

**Bottom line:** The LSI machinery, cgf→tail pipeline, product-measure independence, covering numbers, and Efron–Stein are all production-quality. The genuinely new work is: (a) defining convex-hull-based convex distance and basic properties, (b) proving convexity/Lipschitz properties of `d_A`, and (c) the concentration step — either via LSI-based argument or a median-based martingale argument modeled on McDiarmid. No existing theorem in the repo states Talagrand's convex-distance inequality.
