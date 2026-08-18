# B. Mathlib API survey for Talagrand's convex-distance concentration inequality

Mathlib root: `StatsMLlib/.lake/packages/mathlib/Mathlib/`, Lean v4.32.0.

## 1. EuclideanSpace API

**Definition** — `Mathlib/Analysis/InnerProductSpace/PiL2.lean:113`
```lean
abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜
```
`PiLp` (at `Mathlib/Analysis/Normed/Lp/PiLp.lean:85`) is `WithLp p (∀ i : ι, α i)`. So `EuclideanSpace ℝ (Fin n)` is definitionally `WithLp 2 (Fin n → ℝ)` — a type synonym of the plain function type, with L² norm/inner product.

**Key API** (in `PiL2.lean` unless noted):
- `EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜` (line 278)
- `EuclideanSpace.projₗ (i)`, `EuclideanSpace.proj (i)` (284–287), `EuclideanSpace.single (i) (a)` (299), `EuclideanSpace.orthonormal_single` (332)
- `PiLp.inner_apply [Fintype ι] (x y : PiLp 2 f) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫` (line 103)

**The splitting equivalence the proposal needs exists** — `PiL2.lean:380`:
```lean
abbrev EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} :
    EuclideanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)
```
With `m = 1`: `EuclideanSpace ℝ (Fin (n+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ` — the induction step tool. It's a `ContinuousLinearEquiv` (`≃L`), not an isometry. Also `EuclideanSpace.sumEquivProd` (line 373) for `ι ⊕ κ`.

**Norm / distance API** — `PiLp.lean` (for p = 2):
- `norm_eq_of_L2 (x : PiLp 2 β) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)` (776)
- `norm_sq_eq_of_L2 (x) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2` (793)
- `dist_eq_of_L2 (x y : PiLp 2 β) : dist x y = √(∑ i, dist (x i) (y i) ^ 2)` (798)
- `dist_sq_eq_of_L2 (x y) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2` (802) — **key formula for convex distance computations**

**Volume structure**:
- `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)).symm` (`MeasureTheory/Measure/Haar/InnerProductSpace.lean:124`)
- `PiLp.volume_preserving_ofLp`/`toLp` (134, 137) — `volume` on `EuclideanSpace ℝ ι` equals pullback of Lebesgue volume on `ι → ℝ`
- `LinearIsometryEquiv.measurePreserving` (151)

**Gap**: No `Equiv.piFinSuccAboveEquiv` — use `Fin.succFunEquiv` (Section 6) to split tuples.

## 2. convexHull API

**Definition** — `Mathlib/Analysis/Convex/Hull.lean:46`:
```lean
def convexHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ => convex_sInter
```

Key lemmas (all in `Hull.lean`):
- `subset_convexHull` (50), `convex_convexHull` (53)
- `convexHull_eq_iInter` (55): `convexHull 𝕜 s = ⋂ (t : Set E) (_ : s ⊆ t) (_ : Convex 𝕜 t), t`
- `mem_convexHull_iff` (60), `convexHull_min` (63), `Convex.convexHull_subset_iff` (65), `convexHull_mono` (69), `convexHull_eq_self` (72), `convexHull_empty` (81), `convexHull_nonempty_iff` (94), `convexHull_singleton` (104), `convexHull_pair = segment` (122)

**Finite-set characterizations** — `Mathlib/Analysis/Convex/Combination.lean`:
- `Finset.convexHull_eq (s : Finset E)` (389)
- `Finset.mem_convexHull` (415), `Finset.mem_convexHull'` (422):
  `x ∈ convexHull R (s : Set E) ↔ ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x`
- `Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite)` (422)
- `convexHull_eq_union_convexHull_finite_subsets` (429)

**Topology** — `Mathlib/Analysis/Convex/Topology.lean`:
- `Set.Finite.isCompact_convexHull {s : Set E} (hs : s.Finite) : IsCompact (convexHull 𝕜 s)` (347) — needs finite-dimensional context
- `Set.Finite.isClosed_convexHull [T2Space E] (hs : s.Finite) : IsClosed (convexHull 𝕜 s)` (355)

**Gap**: **No lemma relating `convexHull` to `Metric.infDist`** in mathlib. Pipeline must be assembled: for finite `A ⊆ EuclideanSpace ℝ (Fin n)`, `convexHull ℝ A` is compact → closed → `Metric.infDist` is attained (`IsCompact.exists_infDist_eq_dist`) and `x ∈ convexHull ℝ A ↔ infDist x (convexHull ℝ A) = 0`.

## 3. Metric.infDist API

**Location**: `Mathlib/Topology/MetricSpace/HausdorffDistance.lean` (older `infEdist` deprecated since 2026-01-08).

```lean
def infDist (x : α) (s : Set α) : ℝ := ENNReal.toReal (infEDist x s)      -- line 573
def infEDist (x : α) (s : Set α) : ℝ≥0∞                                     -- line 74
```

Key lemmas:
- `infDist_eq_iInf : infDist x s = ⨅ y : s, dist x y` (578)
- `infDist_nonneg : 0 ≤ infDist x s` (585)
- `isGLB_infDist (hs : s.Nonempty) : IsGLB ((dist x ·) '' s) (infDist x s)` (594)
- `infDist_zero_of_mem` (611), `infDist_singleton : infDist x {y} = dist x y` (616)
- `infDist_le_dist_of_mem` (620), `infDist_le_infDist_of_subset` (623)
- **`le_infDist {r : ℝ} (hs : s.Nonempty) : r ≤ infDist x s ↔ ∀ ⦃y⦄, y ∈ s → r ≤ dist x y`** (626) — the workhorse lower-bound-via-all-points lemma
- `infDist_lt_iff (hs : s.Nonempty) : infDist x s < r ↔ ∃ y ∈ s, dist x y < r` (630)
- `infDist_le_infDist_add_dist` (634) — triangle inequality
- `lipschitz_infDist_pt : LipschitzWith 1 (infDist · s)` (652), `continuous_infDist_pt` (663)
- `infDist_closure : infDist x (closure s) = infDist x s` (668)
- `mem_closure_iff_infDist_zero (h : s.Nonempty) : x ∈ closure s ↔ infDist x s = 0` (689)
- `IsClosed.mem_iff_infDist_zero`, `IsClosed.notMem_iff_infDist_pos` (699, 702)
- **Attainment**: `IsCompact.exists_infDist_eq_dist (h : IsCompact s) (hne : s.Nonempty) (x : α) : ∃ y ∈ s, infDist x s = dist x y` (717)
- `infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t` (713) — isometry invariance

**Gap**: No `Metric.infDist_eq_iff` in this mathlib version — use `le_infDist` + `infDist_le_dist_of_mem`.

## 4. MeasureTheory.Measure.pi

**Location**: `Mathlib/MeasureTheory/Constructions/Pi.lean` (requires `[Fintype ι]`).

```lean
protected irreducible_def pi : Measure (∀ i, α i) := ...      -- line 210
```

Key lemmas:
- `pi_pi [∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)` (290)
- `pi_singleton [∀ i, SigmaFinite (μ i)] (f) : Measure.pi μ {f} = ∏ i, μ i {f i}` (298)
- **`instance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (Measure.pi μ)`** (310)
- `pi.instIsFiniteMeasure` (302), `pi.sigmaFinite` (333)
- `volume_pi [∀ i, MeasureSpace (α i)] : (volume : Measure (∀ i, α i)) = Measure.pi fun _ => volume` (662)
- `pi_map_eval` (376), `pi_map_pi` (387)

**Fubini** — `Mathlib/MeasureTheory/Integral/Prod.lean:443`:
```lean
theorem integral_prod (f : α × β → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ
```

**Finite-product Fubini** — `Mathlib/MeasureTheory/Integral/Pi.lean:106`:
```lean
theorem integral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → 𝕜)
    [∀ i, SigmaFinite (μ i)] :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫ x, f i x ∂(μ i)
```

## 5. Probability independence

**Location**: `Mathlib/Probability/Independence/Basic.lean`, namespace `ProbabilityTheory`.

```lean
def iIndepFun {_mΩ : MeasurableSpace Ω} {β : ι → Type*} [m : ∀ x : ι, MeasurableSpace (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) : Prop               -- line 136
def IndepFun {β γ} {_mΩ : MeasurableSpace Ω} [MeasurableSpace β] [MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) : Prop              -- line 144
```

Key lemmas:
- `iIndepFun_iff_measure_inter_preimage_eq_mul` (654) — finite-product characterization
- **`iIndepFun.map_fun_eq_pi_map [Fintype ι] (hf : ∀ i, AEMeasurable (f i) μ) (h : iIndepFun f μ) : μ.map (fun ω i ↦ f i ω) = Measure.pi (fun i ↦ μ.map (f i))`** (840) — **the bridge from independence to product measure**
- `iIndepFun_iff_map_fun_eq_pi_map [Fintype ι] [IsProbabilityMeasure μ]` (861)
- **`iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) : iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)`** (~900) — coordinate projections on product space are independent
- `iIndepFun.indepFun_finset` (796), `iIndepFun.indepFun_mul_left`/`_right` (~912)

**Integration of independent products** — `Mathlib/Probability/Independence/Integration.lean`:
- **`iIndepFun.integral_prod_eq_prod_integral (hX : iIndepFun X μ) (mX : ∀ i, AEStronglyMeasurable (X i) μ) : μ[∏ i, X i] = ∏ i, μ[X i]`** (476)
- `iIndepFun.integral_fun_prod_eq_prod_integral` (481)

## 6. Finite types & Fin

- **`Fin.succFunEquiv`** — `Mathlib/Logic/Equiv/Fin/Basic.lean:412`:
  `def Fin.succFunEquiv (α : Type*) (n : ℕ) : (Fin (n + 1) → α) ≃ (Fin n → α) × α` — the exact tuple-induction tool (delete/add last coordinate).
- `Fin.appendEquiv (m n) : (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α)` (line 425)
- `Fin.castLEquiv (h : n ≤ m) : Fin n ≃ { i : Fin m // (i : ℕ) < n }` (line 405)
- `finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n)` (line 58) with `finSuccEquiv'_at`/`_succAbove`/`_below`

**`Fin.induction`** — core Lean `Init/Data/Fin/Lemmas.lean:909`:
```lean
@[elab_as_elim] def induction {motive : Fin (n + 1) → Sort _}
  (zero : motive 0) (succ : ∀ i : Fin n, motive (castSucc i) → motive i.succ) : ∀ i : Fin (n + 1), motive i
```
**Caveat**: This inducts on the *index* `i : Fin (n+1)`, not on `n`. Dimension induction on `n` is ordinary `Nat` recursion.

## 7. Key inequalities already in mathlib

- **Hölder** — `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`:
  `integral_mul_norm_le_Lp_mul_Lq {f g : α → E} {p q : ℝ} (hpq : p.HolderConjugate q) ... : ∫ a, ‖f a‖ * ‖g a‖ ∂μ ≤ (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q)` (1144)
  Plus `integral_mul_le_Lp_mul_Lq_of_nonneg` (1191) for ℝ-valued nonneg functions

- **Markov** — `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:50`:
  `mul_meas_ge_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (ε : ℝ≥0∞) : ε * μ {x | ε ≤ f x} ≤ ∫⁻ x, f x ∂μ`

- **Chebyshev–Markov (Lp)** — `Mathlib/MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean:26`:
  `pow_mul_meas_ge_le_eLpNorm`

- **Jensen** — `Mathlib/Analysis/Convex/Integral.lean`:
  **`ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ`** (199)
  Also `ConvexOn.map_centerMass_le` for finite-sum version

- **Fubini** — Section 4 (`integral_prod`, `lintegral_prod`, `integral_fintype_prod_eq_prod`)

- **Cauchy–Schwarz** — via Hölder with `p = q = 2`; on `EuclideanSpace` via `PiLp.inner_apply` + `norm_inner_le_norm`

## 8. Discrete measurable spaces

- **Product measurable space**: `instance MeasurableSpace.pi [m : ∀ a, MeasurableSpace (X a)] : MeasurableSpace (∀ a, X a)` — `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:568`
- **Finite/discrete**: `MeasurableSingletonClass` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:240`; for finite `Ω` every subset is measurable
- **Borel**: `instance DiscreteMeasurableSpace.toBorelSpace {α} [TopologicalSpace α] [DiscreteTopology α]` — `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:673`
- Measurability into products: `aemeasurable_pi_lambda`, `aemeasurable_pi`
- Product measure marginals: `measurePreserving_eval`, `Measure.quasiMeasurePreserving_eval`

## Cross-cutting gaps / notes for the proposal

1. **No `Metric.infDist_eq_iff`** in this mathlib version — use `Metric.le_infDist` together with `Metric.infDist_le_dist_of_mem`. Attainment for convex hull of finite set: `Set.Finite.isCompact_convexHull` → `IsCompact.exists_infDist_eq_dist` (finite dim).
2. **No lemma connecting `convexHull` and `dist`/`infDist`** — must be built from `Finset.mem_convexHull'` (weight characterizations) + `PiLp.dist_sq_eq_of_L2` coordinate formula; these are new project-level lemmas.
3. **`EuclideanSpace.finAddEquivProd` is `≃L` (normed equivalence), not an isometry** — for measure/volume purposes fine (`LinearIsometryEquiv.measurePreserving`), but distance statements on the RHS need care; use `dist_sq_eq_of_L2` on the original `EuclideanSpace`.
4. **`Fin.induction` is index induction** (core), not dimension induction — dimension induction must be plain `Nat` recursion; `Fin.succFunEquiv` is the right splitting equivalence.
5. **`Measure.pi` needs `[Fintype ι]`** (fine for `Fin n`); `pi_pi` etc. additionally need `[∀ i, SigmaFinite (μ i)]`, automatic for probability measures.
6. **Independence-integration results require `AEStronglyMeasurable`/`AEMeasurable`** — for finite discrete codomains these are cheap (`measurable` → `aemeasurable`).
