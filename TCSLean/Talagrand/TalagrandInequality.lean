import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Talagrand's Convex-Distance Inequality

Definitions and theorems for Talagrand's convex-distance concentration inequality
on finite discrete product probability spaces.

## Main definitions

* `mismatchVector` — the coordinate-wise mismatch indicator between two points
  in a product space, as an `EuclideanSpace ℝ (Fin n)` value.
* `convexMismatchSet` — the convex hull of mismatch vectors from a point to a set.
-/

open Set
open MeasureTheory
open ENNReal

namespace TCSLean.Talagrand

noncomputable section

/-- The mismatch vector `v(x,y) ∈ EuclideanSpace ℝ (Fin n)` defined coordinate-wise by
`v(x,y)_i = 0` if `x_i = y_i`, and `1` otherwise. -/
def mismatchVector {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω i) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if x i = y i then (0 : ℝ) else (1 : ℝ))

@[simp]
theorem mismatchVector_self {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) : mismatchVector x x = 0 := by
  ext i
  simp [mismatchVector]

/-- The i-th coordinate of `mismatchVector x y` is 0 iff `x_i = y_i`, and 1 iff `x_i ≠ y_i`. -/
@[simp]
theorem mismatchVector_apply {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω i) (i : Fin n) : mismatchVector x y i = if x i = y i then (0 : ℝ) else (1 : ℝ) := by
  simp [mismatchVector, PiLp.toLp_apply]

/-- The squared Euclidean norm of `mismatchVector` equals the count of mismatches. -/
theorem norm_sq_mismatchVector {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω i) : ‖mismatchVector x y‖ ^ 2 = ∑ i, (if x i = y i then 0 else 1) := by
  simp [mismatchVector_apply, EuclideanSpace.real_norm_sq_eq]

/-- `Fin.snoc` lemma for `mismatchVector` at a non-last coordinate.
The mismatch vector at `Fin.castSucc i` of the snoc-ed vectors equals
the mismatch vector at `i` of the original vectors. -/
@[simp]
theorem mismatchVector_snoc_castSucc {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω (Fin.castSucc i)) (ω ω' : Ω (Fin.last n)) (i : Fin n) :
    (mismatchVector (Fin.snoc x ω) (Fin.snoc y ω')) (Fin.castSucc i) =
    (mismatchVector x y) i := by
  simp [mismatchVector]

/-- `Fin.snoc` lemma for `mismatchVector` at the last coordinate.
The mismatch vector at `Fin.last n` of the snoc-ed vectors is `0` if `ω = ω'`, `1` otherwise. -/
@[simp]
theorem mismatchVector_snoc_last {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω (Fin.castSucc i)) (ω ω' : Ω (Fin.last n)) :
    (mismatchVector (Fin.snoc x ω) (Fin.snoc y ω')) (Fin.last n) =
    if ω = ω' then (0 : ℝ) else (1 : ℝ) := by
  simp [mismatchVector]

/-- Combined `Fin.snoc` lemma for `mismatchVector` using `EuclideanSpace.equiv`.
Under the identification `EuclideanSpace ℝ (Fin (n+1)) ≃ (Fin (n+1)) → ℝ`,
the mismatch vector of snoc-ed vectors decomposes as the snoc of
the mismatch vector of the prefix with the last-coordinate mismatch indicator. -/
theorem mismatchVector_snoc {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω (Fin.castSucc i)) (ω ω' : Ω (Fin.last n)) :
    EuclideanSpace.equiv (Fin (n+1)) ℝ (mismatchVector (Fin.snoc x ω) (Fin.snoc y ω')) =
    Fin.snoc (EuclideanSpace.equiv (Fin n) ℝ (mismatchVector x y))
      (if ω = ω' then (0 : ℝ) else (1 : ℝ)) := by
  ext i; induction i using Fin.lastCases <;> simp [mismatchVector]

/-- The convex hull of mismatch vectors from `x` to points in `A`. -/
def convexMismatchSet {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) : Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ (mismatchVector x '' A)

/-- The convex distance from `x` to `A`.
Defined as the infimum distance from the origin to the convex hull
of mismatch vectors from `x` to points in `A`.
When `A` is empty, `convexMismatchSet x A` is empty and
`Metric.infDist` returns `0` (mathlib convention: infimum over empty set is 0). -/
def convexDistance {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) : ℝ :=
  Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (convexMismatchSet x A)

/-- The convex distance is always nonnegative. -/
theorem convexDistance_nonneg {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) : 0 ≤ convexDistance x A :=
  Metric.infDist_nonneg

/-- If `x ∈ A`, then `convexDistance x A = 0`. -/
theorem convexDistance_zero_of_mem {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) (h : x ∈ A) : convexDistance x A = 0 := by
  rw [convexDistance]
  apply Metric.infDist_zero_of_mem
  apply subset_convexHull ℝ
  exact ⟨x, h, mismatchVector_self x⟩

/-- Monotonicity of convex distance: if `A ⊆ B` and `A` is nonempty, then
`convexDistance x B ≤ convexDistance x A`. The `A.Nonempty` hypothesis is required
because `Metric.infDist_le_infDist_of_subset` requires the smaller set to be nonempty. -/
theorem convexDistance_mono {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A B : Set ((i : Fin n) → Ω i)) (h : A ⊆ B) (hA : A.Nonempty) :
    convexDistance x B ≤ convexDistance x A := by
  rw [convexDistance, convexDistance]
  refine Metric.infDist_le_infDist_of_subset ?_ ?_
  · apply convexHull_mono
    exact Set.image_mono h
  · rcases hA with ⟨y, hy⟩
    refine ⟨mismatchVector x y, subset_convexHull ℝ _ ?_⟩
    exact ⟨y, hy, rfl⟩

/-- The convex distance to the empty set is 0 (by mathlib convention for `Metric.infDist`). -/
@[simp]
theorem convexDistance_empty {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) : convexDistance x (∅ : Set ((i : Fin n) → Ω i)) = 0 := by
  simp [convexDistance, convexMismatchSet, Metric.infDist_empty]

/-- The convex distance to a singleton `{y}` equals the norm of the mismatch vector `v(x,y)`.
This follows because the mismatch set for a singleton is just that single mismatch vector,
whose convex hull is itself. -/
@[simp]
theorem convexDistance_singleton {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω i) : convexDistance x {y} = ‖mismatchVector x y‖ := by
  simp [convexDistance, convexMismatchSet, Set.image_singleton, convexHull_singleton,
    Metric.infDist_singleton, dist_zero_left]

/-- The ω-section of A: `{x | Fin.snoc x ω ∈ A}`.

For `A ⊆ Ω^{(n+1)}` and `ω` in the last coordinate, the ω-section `A_ω` consists of
all prefix vectors `x ∈ Ω^{(n)}` such that the snoc-ed vector `(x, ω)` belongs to `A`. -/
def sectionSet {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (A : Set ((i : Fin (n+1)) → Ω i)) (ω : Ω (Fin.last n)) :
    Set ((i : Fin n) → Ω (Fin.castSucc i)) :=
  {x | Fin.snoc x ω ∈ A}

/-- The projection of A: `{x | ∃ ω, Fin.snoc x ω ∈ A}`.

For `A ⊆ Ω^{(n+1)}`, the projection `B = π(A)` consists of all prefix vectors
`x ∈ Ω^{(n)}` such that there exists some `ω` in the last coordinate
with the snoc-ed vector `(x, ω) ∈ A`. -/
def projectionSet {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (A : Set ((i : Fin (n+1)) → Ω i)) :
    Set ((i : Fin n) → Ω (Fin.castSucc i)) :=
  {x | ∃ ω, Fin.snoc x ω ∈ A}

/-- Pointwise equality: `A.indicator 1 (Fin.snoc x ω) = (sectionSet A ω).indicator 1 x`.
Blueprint item 60.12 prep (indicator_snoc lemma). -/
lemma indicator_snoc {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (A : Set ((i : Fin (n+1)) → Ω i)) (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n)) :
    (A.indicator (fun _ => (1 : ℝ))) (Fin.snoc x ω) =
    ((sectionSet A ω).indicator (fun _ => (1 : ℝ))) x := by
  simp [sectionSet, Set.indicator]

/-! ## Core Lemmas (Blueprint Item 40.5): Convex Distance Recursion
  t=0 and t=1 cases proved; general t deferred.
-/

/-- The norm squared of a `Fin.snoc` vector in EuclideanSpace decomposes as
the sum of the norm squared of the prefix and the absolute value squared of the last coordinate. -/
lemma norm_sq_snoc {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    ‖(EuclideanSpace.equiv (Fin (n+1)) ℝ).symm (Fin.snoc (EuclideanSpace.equiv (Fin n) ℝ z) a)‖ ^ 2 =
    ‖z‖ ^ 2 + ‖a‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]

/-- Convexity inequality for squared Euclidean norm.
For t ∈ [0,1] and any vectors a, b in an inner product space:
‖(1-t)·a + t·b‖² ≤ (1-t)·‖a‖² + t·‖b‖².
This follows from the parallelogram law / inner product expansion. -/
lemma convexity_norm_sq {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ‖(1 - t) • a + t • b‖ ^ 2 ≤ (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 := by
  have h1mt_nonneg : 0 ≤ 1 - t := by linarith
  have h_diff_nonneg : 0 ≤ t * (1 - t) * ‖a - b‖ ^ 2 := by
    have h_sq_nonneg : 0 ≤ ‖a - b‖ ^ 2 := pow_two_nonneg _
    have h_factor_nonneg : 0 ≤ t * (1 - t) := mul_nonneg ht₀ h1mt_nonneg
    nlinarith
  have h_eq : (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 - ‖(1 - t) • a + t • b‖ ^ 2 = t * (1 - t) * ‖a - b‖ ^ 2 := by
    let u := (1 - t) • a
    let v := t • b
    have h_norm_add : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * inner ℝ u v + ‖v‖ ^ 2 := by
      simpa using norm_add_sq (𝕜 := ℝ) u v
    have h_norm_sq_u : ‖u‖ ^ 2 = (1 - t) ^ 2 * ‖a‖ ^ 2 := by
      dsimp [u]
      calc
        ‖(1 - t) • a‖ ^ 2 = (‖(1 - t)‖ * ‖a‖) ^ 2 := by rw [norm_smul]
        _ = (|1 - t| * ‖a‖) ^ 2 := by rw [Real.norm_eq_abs]
        _ = |1 - t| ^ 2 * ‖a‖ ^ 2 := by ring
        _ = (1 - t) ^ 2 * ‖a‖ ^ 2 := by rw [abs_of_nonneg h1mt_nonneg]
    have h_norm_sq_v : ‖v‖ ^ 2 = t ^ 2 * ‖b‖ ^ 2 := by
      dsimp [v]
      calc
        ‖t • b‖ ^ 2 = (‖t‖ * ‖b‖) ^ 2 := by rw [norm_smul]
        _ = (|t| * ‖b‖) ^ 2 := by rw [Real.norm_eq_abs]
        _ = |t| ^ 2 * ‖b‖ ^ 2 := by ring
        _ = t ^ 2 * ‖b‖ ^ 2 := by rw [abs_of_nonneg ht₀]
    have h_inner_uv : inner ℝ u v = (1 - t) * t * inner ℝ a b := by
      simp [u, v, inner_smul_right, inner_smul_left]
      ring
    rw [h_norm_add, h_norm_sq_u, h_norm_sq_v, h_inner_uv]
    calc
      (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 - ((1 - t) ^ 2 * ‖a‖ ^ 2 + 2 * ((1 - t) * t * inner ℝ a b) + t ^ 2 * ‖b‖ ^ 2)
          = t * (1 - t) * (‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * inner ℝ a b) := by ring
      _ = t * (1 - t) * (‖a‖ ^ 2 - 2 * inner ℝ a b + ‖b‖ ^ 2) := by ring
      _ = t * (1 - t) * ‖a - b‖ ^ 2 := by rw [norm_sub_sq_real]
  linarith

/-- If a real number a satisfies a ≤ b + ε for all ε > 0, then a ≤ b. -/
lemma le_of_le_add_epsilon {a b : ℝ} (h : ∀ ε > 0, a ≤ b + ε) : a ≤ b := by
  by_contra! hlt
  have hpos : (a - b) / 2 > 0 := by linarith
  have h' := h ((a - b) / 2) hpos
  linarith

/- The map `f ↦ Fin.snoc f 0` as a linear map from `Fin n → ℝ` to `Fin (n+1) → ℝ`. -/
def finSnocZeroLM {n : ℕ} : (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun f := Fin.snoc f 0
  map_add' f g := by
    funext i
    refine Fin.lastCases (by simp) (fun j => by simp) i
  map_smul' c f := by
    funext i
    refine Fin.lastCases (by simp) (fun j => by simp) i

/-- Helper: linear isometric embedding appending 0 as last coordinate.
    Maps EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1)).
    Defined as the composition of three linear maps. -/
def embedWithZeroLM {n : ℕ} : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm.toLinearMap ∘ₗ
  finSnocZeroLM ∘ₗ
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap

/-- The underlying function of `embedWithZeroLM`. -/
def embedWithZero {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+1)) :=
  embedWithZeroLM v

lemma embedWithZero_norm_sq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ‖embedWithZero v‖ ^ 2 = ‖v‖ ^ 2 := by
  dsimp [embedWithZero, embedWithZeroLM, finSnocZeroLM]
  simpa using norm_sq_snoc v 0

lemma embedWithZero_norm_eq {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    ‖embedWithZero v‖ = ‖v‖ := by
  have h_sq := embedWithZero_norm_sq v
  have h_nonneg₁ : 0 ≤ ‖embedWithZero v‖ := norm_nonneg _
  have h_nonneg₂ : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith

lemma embedWithZero_mismatchVector {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x y : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n)) :
    embedWithZero (mismatchVector x y) =
    mismatchVector (Fin.snoc x ω) (Fin.snoc y ω) := by
  dsimp [embedWithZero, embedWithZeroLM, finSnocZeroLM]
  have h := mismatchVector_snoc x y ω ω
  calc
    (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm
        (Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) (mismatchVector x y)) 0)
        = (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm
          (Fin.snoc ((EuclideanSpace.equiv (Fin n) ℝ) (mismatchVector x y))
            (if ω = ω then (0 : ℝ) else 1)) := by simp
    _ = (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm
          ((EuclideanSpace.equiv (Fin (n+1)) ℝ) (mismatchVector (Fin.snoc x ω) (Fin.snoc y ω))) := by
      rw [← h]
    _ = mismatchVector (Fin.snoc x ω) (Fin.snoc y ω) := by simp

lemma embedWithZero_zero {n : ℕ} : embedWithZero (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  simp [embedWithZero, embedWithZeroLM]

lemma embedWithZero_isometry {n : ℕ} : Isometry (embedWithZero : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1))) := by
  -- embedWithZeroLM is an AddMonoidHom, and its norm is preserved
  have h : Isometry (embedWithZeroLM (n := n)) :=
    (AddMonoidHomClass.isometry_iff_norm (embedWithZeroLM (n := n))).mpr embedWithZero_norm_eq
  -- embedWithZero is definitionally equal to embedWithZeroLM
  exact h

/-- t=1 case of convex distance recursion: when the section A_ω is nonempty,
  d_A(snoc x ω)² ≤ d_{A_ω}(x)². Uses the `embedWithZero` linear isometric embedding. -/
lemma convexDistance_snoc_section_nonempty_le {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) (h_sec_nonempty : (sectionSet A ω).Nonempty) :
    (convexDistance (Fin.snoc x ω) A) ^ 2 ≤
    (convexDistance x (sectionSet A ω)) ^ 2 := by
  let B := {Fin.snoc y ω | y ∈ sectionSet A ω}
  have hB_sub_A : B ⊆ A := by rintro z ⟨y, hy, rfl⟩; exact hy
  have hB_nonempty : B.Nonempty := by
    rcases h_sec_nonempty with ⟨y, hy⟩
    exact ⟨Fin.snoc y ω, y, hy, rfl⟩
  have h_mono : convexDistance (Fin.snoc x ω) A ≤ convexDistance (Fin.snoc x ω) B :=
    convexDistance_mono (Fin.snoc x ω) B A hB_sub_A hB_nonempty
  have h_eq : convexDistance (Fin.snoc x ω) B = convexDistance x (sectionSet A ω) := by
    dsimp [convexDistance, convexMismatchSet]
    let M_sec := mismatchVector x '' sectionSet A ω
    have h_image_eq : mismatchVector (Fin.snoc x ω) '' B = embedWithZero '' M_sec := by
      ext z; constructor
      · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨mismatchVector x y, ⟨y, hy, rfl⟩, embedWithZero_mismatchVector x y ω⟩
      · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨Fin.snoc y ω, ⟨y, hy, rfl⟩, (embedWithZero_mismatchVector x y ω).symm⟩
    rw [h_image_eq]
    -- convexHull(embedWithZero '' M_sec) = embedWithZero '' convexHull(M_sec) (linear map)
    have h_convHull_eq : convexHull ℝ (embedWithZero '' M_sec) =
        embedWithZero '' (convexHull ℝ M_sec) := by
      calc
        convexHull ℝ (embedWithZero '' M_sec) = convexHull ℝ ((embedWithZeroLM (n := n)) '' M_sec) := by
          simp [embedWithZero, embedWithZeroLM]
        _ = (embedWithZeroLM (n := n)) '' (convexHull ℝ M_sec) := by
          rw [embedWithZeroLM.image_convexHull]
        _ = embedWithZero '' (convexHull ℝ M_sec) := by simp [embedWithZero, embedWithZeroLM]
    rw [h_convHull_eq]
    -- Metric.infDist 0 (embedWithZero '' C_sec) = Metric.infDist 0 C_sec (isometry)
    calc
      Metric.infDist (0 : EuclideanSpace ℝ (Fin (n+1))) (embedWithZero '' (convexHull ℝ M_sec))
          = Metric.infDist (embedWithZero (0 : EuclideanSpace ℝ (Fin n)))
            (embedWithZero '' (convexHull ℝ M_sec)) := by rw [embedWithZero_zero]
      _ = Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (convexHull ℝ M_sec) :=
        Metric.infDist_image embedWithZero_isometry
  rw [h_eq] at h_mono
  have h_nonneg_dA : 0 ≤ convexDistance (Fin.snoc x ω) A := convexDistance_nonneg _ _
  have h_nonneg_dsec : 0 ≤ convexDistance x (sectionSet A ω) := convexDistance_nonneg _ _
  nlinarith

/-- Linear map restricting `Fin (n+1) → ℝ` to `Fin n → ℝ` by dropping the last coordinate. -/
def restrictCastSuccLM {n : ℕ} : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun f i := f (Fin.castSucc i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Linear projection: EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n) dropping the last coordinate. -/
def projectLastLM {n : ℕ} : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap ∘ₗ
  restrictCastSuccLM ∘ₗ
  (EuclideanSpace.equiv (Fin (n+1)) ℝ).toLinearMap

/-- The underlying function of `projectLastLM`. -/
def projectLast {n : ℕ} (z : EuclideanSpace ℝ (Fin (n+1))) : EuclideanSpace ℝ (Fin n) :=
  projectLastLM z

lemma Fin_snoc_eta {n : ℕ} {α : Fin (n+1) → Type*} (y : (i : Fin (n+1)) → α i) :
    y = Fin.snoc (fun i => y (Fin.castSucc i)) (y (Fin.last n)) := by
  ext i
  refine Fin.lastCases (by simp) (fun j => by simp) i

lemma projectLast_mismatchVector {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω ω' : Ω (Fin.last n))
    (y : (i : Fin n) → Ω (Fin.castSucc i)) :
    projectLast (mismatchVector (Fin.snoc x ω) (Fin.snoc y ω')) = mismatchVector x y := by
  dsimp [projectLast, projectLastLM, restrictCastSuccLM]
  ext i
  simp

lemma norm_sq_projectLast_add_last_sq {n : ℕ} (z : EuclideanSpace ℝ (Fin (n+1))) :
    ‖z‖ ^ 2 = ‖projectLastLM z‖ ^ 2 + ((EuclideanSpace.equiv (Fin (n+1)) ℝ) z (Fin.last n)) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, projectLastLM, restrictCastSuccLM,
    Fin.sum_univ_castSucc]

/-- Linear map extracting the last coordinate of a `Fin (n+1)` vector. -/
def lastCoordLM {n : ℕ} : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ where
  toFun z := z (Fin.last n)
  map_add' x y := by simp
  map_smul' c x := by simp

/-- For any z in the convex mismatch set, the squared last coordinate is at most 1.
This is because each mismatch vector has last coordinate 0 or 1,
so their convex hull has last coordinates in [0,1]. -/
lemma last_coord_sq_le_one {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) (z : EuclideanSpace ℝ (Fin (n+1)))
    (hz : z ∈ convexMismatchSet (Fin.snoc x ω) A) :
    (lastCoordLM z) ^ 2 ≤ 1 := by
  let S := mismatchVector (Fin.snoc x ω) '' A
  have hz' : z ∈ convexHull ℝ S := hz
  -- Each generator has last coordinate 0 or 1
  have h_S_last : lastCoordLM '' S ⊆ ({0, 1} : Set ℝ) := by
    rintro t ⟨v, ⟨y, hy, rfl⟩, rfl⟩
    have hy_eta := Fin_snoc_eta y
    rw [hy_eta]
    dsimp [lastCoordLM]
    rw [mismatchVector_snoc_last]
    split <;> simp
  -- The convex hull of {0,1} is contained in [0,1]
  have h_convHull_01_sub : convexHull ℝ ({0, 1} : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1 :=
    convexHull_min (by
      intro x hx
      simp at hx
      rcases hx with (rfl | rfl)
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩) (convex_Icc 0 1)
  -- lastCoordLM is linear, so image commutes with convex hull
  have h_last_convHull : lastCoordLM '' (convexHull ℝ S) = convexHull ℝ (lastCoordLM '' S) := by
    rw [lastCoordLM.image_convexHull]
  -- Thus lastCoordLM '' (convexHull ℝ S) ⊆ [0,1]
  have h_last_range : lastCoordLM '' (convexHull ℝ S) ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [h_last_convHull]
    exact Subset.trans (convexHull_mono h_S_last) h_convHull_01_sub
  -- Since z ∈ convexHull ℝ S, we have lastCoordLM z ∈ [0,1]
  have hz_in : lastCoordLM z ∈ Set.Icc (0 : ℝ) 1 :=
    h_last_range ⟨z, hz', rfl⟩
  have hz0 : 0 ≤ lastCoordLM z := hz_in.1
  have hz1 : lastCoordLM z ≤ 1 := hz_in.2
  nlinarith

/-- If a < (b + ε)² + 1 for all ε > 0 and b ≥ 0, then a ≤ b² + 1. -/
lemma le_of_lt_add_sq_epsilon {a b : ℝ} (hb : 0 ≤ b) (h : ∀ ε > 0, a < (b + ε) ^ 2 + 1) : a ≤ b ^ 2 + 1 := by
  have h' : ∀ δ > 0, a < b ^ 2 + δ + 1 := by
    intro δ hδ
    by_cases hb0 : b = 0
    · subst hb0
      let ε := min 1 δ
      have hεpos : 0 < ε := lt_min_iff.mpr ⟨by norm_num, hδ⟩
      have hεsq : ε ^ 2 ≤ δ := by
        have hεle1 : ε ≤ 1 := min_le_left _ _
        have hεleδ : ε ≤ δ := min_le_right _ _
        nlinarith
      have hε := h ε hεpos
      simp at hε
      nlinarith
    · have hpos : 0 < 2 * b + 1 := by nlinarith
      let ε := min 1 (δ / (2 * b + 1))
      have hεpos : 0 < ε := lt_min_iff.mpr ⟨by norm_num, div_pos hδ hpos⟩
      have hεle1 : ε ≤ 1 := min_le_left _ _
      have hε_div : ε ≤ δ / (2 * b + 1) := min_le_right _ _
      have hε_bound : ε * (2 * b + 1) ≤ δ := by
        calc
          ε * (2 * b + 1) ≤ (δ / (2 * b + 1)) * (2 * b + 1) :=
            mul_le_mul_of_nonneg_right hε_div (by nlinarith)
          _ = δ := by field_simp [hpos.ne.symm]
      have h_quad : 2 * b * ε + ε ^ 2 ≤ ε * (2 * b + 1) := by
        nlinarith
      have hε_main := h ε hεpos
      have h_sq_expand : (b + ε) ^ 2 = b ^ 2 + 2 * b * ε + ε ^ 2 := by ring
      rw [h_sq_expand] at hε_main
      nlinarith
  exact le_of_le_add_epsilon (fun δ hδ => by
    have hlt := h' δ hδ
    linarith)

/-- t=0 case of convex distance recursion: d_A(snoc x ω)² ≤ d_B(x)² + 1.
  Uses the `projectLastLM` linear projection and ε-approximate minimizers
  from the projection side. -/
lemma convexDistance_snoc_le_projection_add_one {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) :
    (convexDistance (Fin.snoc x ω) A) ^ 2 ≤
    (convexDistance x (projectionSet A)) ^ 2 + 1 := by
  let C_A := convexMismatchSet (Fin.snoc x ω) A
  let C_proj := convexMismatchSet x (projectionSet A)
  let π := projectLastLM (n := n)
  have h_mismatch_image : π '' (mismatchVector (Fin.snoc x ω) '' A) ⊆
      mismatchVector x '' (projectionSet A) := by
    rintro z ⟨v, ⟨y, hy, rfl⟩, rfl⟩
    let y_pref : (i : Fin n) → Ω (Fin.castSucc i) := fun i => y (Fin.castSucc i)
    let y_last : Ω (Fin.last n) := y (Fin.last n)
    have hy_eq' : y = Fin.snoc y_pref y_last := Fin_snoc_eta y
    have hy_proj : y_pref ∈ projectionSet A := by
      dsimp [projectionSet, y_pref]
      have hy_snoc : Fin.snoc y_pref y_last ∈ A := by
        rwa [← hy_eq']
      exact ⟨y_last, hy_snoc⟩
    have hπ : π (mismatchVector (Fin.snoc x ω) y) = mismatchVector x y_pref := by
      rw [hy_eq']
      exact projectLast_mismatchVector x ω y_last y_pref
    rw [hπ]
    exact ⟨y_pref, hy_proj, rfl⟩
  have h_convexHull_image : π '' C_A ⊆ C_proj := by
    calc
      π '' C_A = π '' (convexHull ℝ (mismatchVector (Fin.snoc x ω) '' A)) := rfl
      _ = convexHull ℝ (π '' (mismatchVector (Fin.snoc x ω) '' A)) := by
        rw [π.image_convexHull]
      _ ⊆ convexHull ℝ (mismatchVector x '' (projectionSet A)) :=
        convexHull_mono h_mismatch_image
      _ = C_proj := rfl
  -- Key equality: π(C_A) = C_proj (projection of the convex mismatch set equals the convex mismatch set of the projection)
  have h_image_eq : π '' C_A = C_proj := by
    calc
      π '' C_A = π '' (convexHull ℝ (mismatchVector (Fin.snoc x ω) '' A)) := rfl
      _ = convexHull ℝ (π '' (mismatchVector (Fin.snoc x ω) '' A)) := by
        rw [π.image_convexHull]
      _ = convexHull ℝ (mismatchVector x '' (projectionSet A)) := by
        apply congrArg (convexHull ℝ)
        apply Set.Subset.antisymm
        · exact h_mismatch_image
        · intro w hw
          rcases hw with ⟨y, hy, rfl⟩
          rcases hy with ⟨ω', hy'⟩
          refine ⟨mismatchVector (Fin.snoc x ω) (Fin.snoc y ω'), ?_, ?_⟩
          · exact ⟨Fin.snoc y ω', hy', rfl⟩
          · exact projectLast_mismatchVector x ω ω' y
      _ = C_proj := rfl
  let dA := convexDistance (Fin.snoc x ω) A
  let dproj := convexDistance x (projectionSet A)
  have h_nonneg_dA : 0 ≤ dA := convexDistance_nonneg _ _
  have h_nonneg_dproj : 0 ≤ dproj := convexDistance_nonneg _ _
  -- If C_proj is empty, then C_A is also empty (since π '' C_A = C_proj), both distances are 0
  by_cases h_empty_Cproj : C_proj = ∅
  · have h_empty_CA : C_A = ∅ := by
      by_contra hne
      have h_nonempty_CA : C_A.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
      rcases h_nonempty_CA with ⟨z, hz⟩
      have hπz : π z ∈ π '' C_A := ⟨z, hz, rfl⟩
      rw [h_image_eq, h_empty_Cproj] at hπz
      simp at hπz
    have hdA_zero : dA = 0 := by
      dsimp [dA, convexDistance, C_A] at *
      rw [h_empty_CA]
      simp
    have hdproj_zero : dproj = 0 := by
      dsimp [dproj, convexDistance, C_proj] at *
      rw [h_empty_Cproj]
      simp
    dsimp [dA, dproj] at hdA_zero hdproj_zero ⊢
    rw [hdA_zero, hdproj_zero]
    norm_num
  · -- C_proj is nonempty
    have h_nonempty_Cproj : C_proj.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty_Cproj
    -- Goal: dA ^ 2 ≤ dproj ^ 2 + 1
    -- For any ε > 0, get w ∈ C_proj with ‖w‖ < dproj + ε
    have h_approx : ∀ ε > 0, ∃ w ∈ C_proj, ‖w‖ < dproj + ε := by
      intro ε hε
      have h_lt : dproj < dproj + ε := by nlinarith
      -- dproj = Metric.infDist 0 C_proj
      have hdproj_def : dproj = Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) C_proj := rfl
      rw [hdproj_def] at h_lt
      rcases (Metric.infDist_lt_iff h_nonempty_Cproj).mp h_lt with ⟨w, hw, hdist⟩
      -- hdist : dist 0 w < dproj + ε
      -- dist 0 w = ‖w‖ in a seminormed group
      rw [dist_zero_left] at hdist
      exact ⟨w, hw, hdist⟩
    -- For each ε > 0, get the corresponding z ∈ C_A
    have h_bound : ∀ ε > 0, dA ^ 2 < (dproj + ε) ^ 2 + 1 := by
      intro ε hε
      rcases h_approx ε hε with ⟨w, hw, hw_norm⟩
      -- Since π '' C_A = C_proj, there exists z ∈ C_A with π z = w
      rcases (Set.mem_image _ _ _).mp (by rw [h_image_eq]; exact hw) with ⟨z, hz, hπz⟩
      -- dA ≤ ‖z‖ (since dA = inf, and z ∈ C_A)
      have hdA_le_norm_z : dA ≤ ‖z‖ := by
        dsimp [dA, convexDistance, C_A]
        have h := Metric.infDist_le_dist_of_mem (x := 0) hz
        simpa [dist_zero_left] using h
      -- ‖z‖² = ‖π z‖² + lastCoord(z)² ≤ ‖w‖² + 1
      have h_norm_sq_decomp : ‖z‖ ^ 2 = ‖π z‖ ^ 2 + (lastCoordLM (n := n) z) ^ 2 := by
        dsimp [π, lastCoordLM]
        exact norm_sq_projectLast_add_last_sq z
      rw [hπz] at h_norm_sq_decomp
      have h_last_sq_le_one : (lastCoordLM (n := n) z) ^ 2 ≤ 1 :=
        last_coord_sq_le_one x ω A z hz
      have h_norm_sq_le : ‖z‖ ^ 2 ≤ ‖w‖ ^ 2 + 1 := by nlinarith
      have h_norm_w_lt : ‖w‖ ^ 2 < (dproj + ε) ^ 2 := by
        have h_nonneg_w : 0 ≤ ‖w‖ := norm_nonneg _
        nlinarith
      -- Put everything together
      nlinarith
    -- Now use le_of_lt_add_sq_epsilon to conclude
    exact le_of_lt_add_sq_epsilon h_nonneg_dproj h_bound

/-!
# Blueprint Item 40.7: `convexDistance_snoc_empty_section_eq`

When the ω-section of A is empty (and A is nonempty), the convex distance has the
exact form

  d_A(x, ω)² = d_B(x)² + 1,  where B = projectionSet A

because every mismatch vector from (x, ω) to a point of A has last coordinate
exactly 1, so the whole convex mismatch set lies in the hyperplane {last = 1}.
-/

/-- If a < (b + ε)² for all ε > 0 and 0 ≤ b, then a ≤ b². -/
lemma le_of_lt_add_sq_eps {a b : ℝ} (hb : 0 ≤ b) (h : ∀ ε > 0, a < (b + ε) ^ 2) :
    a ≤ b ^ 2 := by
  have h' : ∀ δ > 0, a < b ^ 2 + δ := by
    intro δ hδ
    have hpos : 0 < 2 * b + 1 := by nlinarith
    let ε := min 1 (δ / (2 * b + 1))
    have hεpos : 0 < ε := lt_min_iff.mpr ⟨by norm_num, div_pos hδ hpos⟩
    have hεle1 : ε ≤ 1 := min_le_left _ _
    have hε_div : ε ≤ δ / (2 * b + 1) := min_le_right _ _
    have hε_bound : ε * (2 * b + 1) ≤ δ := by
      calc
        ε * (2 * b + 1) ≤ (δ / (2 * b + 1)) * (2 * b + 1) :=
          mul_le_mul_of_nonneg_right hε_div (by nlinarith)
        _ = δ := by field_simp [hpos.ne.symm]
    have h_quad : 2 * b * ε + ε ^ 2 ≤ ε * (2 * b + 1) := by nlinarith
    have hε_main := h ε hεpos
    have h_sq_expand : (b + ε) ^ 2 = b ^ 2 + 2 * b * ε + ε ^ 2 := by ring
    rw [h_sq_expand] at hε_main
    nlinarith
  exact le_of_le_add_epsilon (fun δ hδ => (h' δ hδ).le)

/-- When the ω-section of A is empty, every mismatch vector from `(x, ω)` to a point of
A has last coordinate exactly 1. -/
lemma mismatchVector_last_eq_one_of_empty_section {n : ℕ} {Ω : Fin (n+1) → Type*}
    [∀ i, DecidableEq (Ω i)] (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) (h_empty : sectionSet A ω = ∅)
    (y : (i : Fin (n+1)) → Ω i) (hy : y ∈ A) :
    (mismatchVector (Fin.snoc x ω) y) (Fin.last n) = 1 := by
  have hy_last_ne : ω ≠ y (Fin.last n) := by
    intro h_eq
    have h_mem_sec : (fun i => y (Fin.castSucc i)) ∈ sectionSet A ω := by
      dsimp [sectionSet]
      rw [h_eq, ← Fin_snoc_eta y]
      exact hy
    rw [h_empty] at h_mem_sec
    simp at h_mem_sec
  rw [Fin_snoc_eta y]
  rw [mismatchVector_snoc_last]
  rw [if_neg hy_last_ne]

/-- When the ω-section of A is empty, every element of the convex mismatch set
`convexMismatchSet (Fin.snoc x ω) A` has last coordinate exactly 1.
(All generators have last coordinate 1, and the hyperplane {last = 1} is convex.) -/
lemma lastCoord_eq_one_of_empty_section {n : ℕ} {Ω : Fin (n+1) → Type*}
    [∀ i, DecidableEq (Ω i)] (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) (h_empty : sectionSet A ω = ∅)
    (z : EuclideanSpace ℝ (Fin (n+1))) (hz : z ∈ convexMismatchSet (Fin.snoc x ω) A) :
    lastCoordLM z = 1 := by
  have h_gen : mismatchVector (Fin.snoc x ω) '' A ⊆ {z | lastCoordLM z = 1} := by
    rintro z ⟨y, hy, rfl⟩
    dsimp [lastCoordLM]
    exact mismatchVector_last_eq_one_of_empty_section x ω A h_empty y hy
  have h_conv : Convex ℝ {z : EuclideanSpace ℝ (Fin (n+1)) | lastCoordLM z = 1} := by
    intro u hu v hv s hs0 t ht0 hsum
    dsimp at hu hv ⊢
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hu, hv]
    nlinarith [hsum]
  exact (convexHull_min h_gen h_conv) hz

/-- Blueprint Item 40.7: when the ω-section of A is empty (and A is nonempty),
the convex distance satisfies the exact recursion

  d_A(x, ω)² = d_B(x)² + 1,  where B = projectionSet A.

The hypothesis `A.Nonempty` is needed: if `A = ∅` the identity reads `0 = 1`.
Proof: every mismatch vector from (x, ω) to A has last coordinate 1 (the section is
empty), so the convex mismatch set lies in the hyperplane {last = 1}. Hence for every
w ∈ C_A, ‖w‖² = ‖projectLastLM w‖² + 1, and projecting w gives an element of C_B,
so ‖w‖² ≥ d_B² + 1. Taking the infimum gives d_A² ≥ d_B² + 1; the reverse inequality
is `convexDistance_snoc_le_projection_add_one`. -/
theorem convexDistance_snoc_empty_section_eq {n : ℕ} {Ω : Fin (n+1) → Type*}
    [∀ i, DecidableEq (Ω i)] (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) (h_empty : sectionSet A ω = ∅)
    (h_nonempty : A.Nonempty) :
    (convexDistance (Fin.snoc x ω) A) ^ 2 =
    (convexDistance x (projectionSet A)) ^ 2 + 1 := by
  let dA := convexDistance (Fin.snoc x ω) A
  let dproj := convexDistance x (projectionSet A)
  let π := projectLastLM (n := n)
  let C_A := convexMismatchSet (Fin.snoc x ω) A
  let C_proj := convexMismatchSet x (projectionSet A)
  have h_image_sub : π '' C_A ⊆ C_proj := by
    have h_mismatch_image : π '' (mismatchVector (Fin.snoc x ω) '' A) ⊆
        mismatchVector x '' (projectionSet A) := by
      rintro z ⟨v, ⟨y, hy, rfl⟩, rfl⟩
      let y_pref : (i : Fin n) → Ω (Fin.castSucc i) := fun i => y (Fin.castSucc i)
      let y_last : Ω (Fin.last n) := y (Fin.last n)
      have hy_eq' : y = Fin.snoc y_pref y_last := Fin_snoc_eta y
      have hy_proj : y_pref ∈ projectionSet A := by
        dsimp [projectionSet, y_pref]
        have hy_snoc : Fin.snoc y_pref y_last ∈ A := by rwa [← hy_eq']
        exact ⟨y_last, hy_snoc⟩
      have hπ : π (mismatchVector (Fin.snoc x ω) y) = mismatchVector x y_pref := by
        rw [hy_eq']
        exact projectLast_mismatchVector x ω y_last y_pref
      rw [hπ]
      exact ⟨y_pref, hy_proj, rfl⟩
    calc
      π '' C_A = π '' (convexHull ℝ (mismatchVector (Fin.snoc x ω) '' A)) := rfl
      _ = convexHull ℝ (π '' (mismatchVector (Fin.snoc x ω) '' A)) := by
        rw [π.image_convexHull]
      _ ⊆ convexHull ℝ (mismatchVector x '' (projectionSet A)) :=
        convexHull_mono h_mismatch_image
      _ = C_proj := rfl
  -- The ≤ direction: already proved (t=0 case of the recursion).
  have h_le : dA ^ 2 ≤ dproj ^ 2 + 1 := by
    dsimp [dA, dproj]
    exact convexDistance_snoc_le_projection_add_one x ω A
  -- The ≥ direction: every w ∈ C_A has last coordinate 1, so
  -- ‖w‖² = ‖π w‖² + 1 ≥ dproj² + 1.
  have h_ge : dproj ^ 2 + 1 ≤ dA ^ 2 := by
    apply le_of_lt_add_sq_eps (a := dproj ^ 2 + 1) (b := dA)
    · exact convexDistance_nonneg (Fin.snoc x ω) A
    · intro ε hε
      have h_CA_nonempty : C_A.Nonempty := by
        rcases h_nonempty with ⟨y, hy⟩
        exact ⟨mismatchVector (Fin.snoc x ω) y, subset_convexHull ℝ
          (mismatchVector (Fin.snoc x ω) '' A) ⟨y, hy, rfl⟩⟩
      have h_lt : dA < dA + ε := by linarith
      have h_lt' : Metric.infDist (0 : EuclideanSpace ℝ (Fin (n+1))) C_A < dA + ε := h_lt
      rcases (Metric.infDist_lt_iff h_CA_nonempty).mp h_lt' with ⟨w, hw, hw_lt⟩
      rw [dist_zero_left] at hw_lt
      -- w ∈ C_A and ‖w‖ < dA + ε
      have hw_sq_ge : dproj ^ 2 + 1 ≤ ‖w‖ ^ 2 := by
        have h_last : lastCoordLM w = 1 :=
          lastCoord_eq_one_of_empty_section x ω A h_empty w hw
        have h_decomp : ‖w‖ ^ 2 = ‖π w‖ ^ 2 + 1 := by
          have h := norm_sq_projectLast_add_last_sq w
          have hlast : (EuclideanSpace.equiv (Fin (n+1)) ℝ) w (Fin.last n) = 1 := by
            simpa [lastCoordLM] using h_last
          rw [hlast] at h
          simpa [π] using h
        have hπw : π w ∈ C_proj := h_image_sub ⟨w, hw, rfl⟩
        have hπw_norm_ge : dproj ^ 2 ≤ ‖π w‖ ^ 2 := by
          have hπw_dist : dproj ≤ ‖π w‖ := by
            dsimp [dproj, convexDistance, C_proj]
            have hd := Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ (Fin n))) hπw
            simpa [dist_zero_left] using hd
          have h_nonneg_dproj : 0 ≤ dproj := convexDistance_nonneg _ _
          have h_nonneg_πw : 0 ≤ ‖π w‖ := norm_nonneg _
          nlinarith
        calc
          dproj ^ 2 + 1 ≤ ‖π w‖ ^ 2 + 1 := by nlinarith
          _ = ‖w‖ ^ 2 := by rw [← h_decomp]
      have hw_sq_lt : ‖w‖ ^ 2 < (dA + ε) ^ 2 := by
        have h_nonneg_w : 0 ≤ ‖w‖ := norm_nonneg _
        nlinarith
      exact lt_of_le_of_lt hw_sq_ge hw_sq_lt
  dsimp [dA, dproj] at h_le h_ge ⊢
  linarith

/-- `scalar_optimization_two_valued` (Blueprint Item 40.10).
Combines the t=0 (`convexDistance_snoc_le_projection_add_one`) and t=1
(`convexDistance_snoc_section_nonempty_le`) cases with `Real.exp` monotonicity.

Returns a pair of bounds:
1. A universal bound: `exp(d_A²/4) ≤ exp(1/4) * exp(d_proj²/4)` (always holds, from t=0).
2. A conditional bound: if the ω-section is nonempty, then the tighter bound
   `exp(d_A²/4) ≤ exp(d_sec²/4)` holds (from t=1). -/
lemma scalar_optimization_two_valued {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) :
    (Real.exp ((convexDistance (Fin.snoc x ω) A) ^ 2 / 4) ≤
      Real.exp (1/4) * Real.exp ((convexDistance x (projectionSet A)) ^ 2 / 4)) ∧
    ((sectionSet A ω).Nonempty →
      Real.exp ((convexDistance (Fin.snoc x ω) A) ^ 2 / 4) ≤
        Real.exp ((convexDistance x (sectionSet A ω)) ^ 2 / 4)) :=
by
  constructor
  · -- First bound: from t=0 lemma (d_A² ≤ d_proj² + 1)
    have h_sq : (convexDistance (Fin.snoc x ω) A) ^ 2 ≤
        (convexDistance x (projectionSet A)) ^ 2 + 1 :=
      convexDistance_snoc_le_projection_add_one x ω A
    have h_nonneg : 0 ≤ (convexDistance x (projectionSet A)) ^ 2 := by
      have h := convexDistance_nonneg x (projectionSet A)
      nlinarith
    have h_exp_sq : Real.exp ((convexDistance (Fin.snoc x ω) A) ^ 2 / 4) ≤
        Real.exp (((convexDistance x (projectionSet A)) ^ 2 + 1) / 4) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      Real.exp ((convexDistance (Fin.snoc x ω) A) ^ 2 / 4) ≤
          Real.exp (((convexDistance x (projectionSet A)) ^ 2 + 1) / 4) := h_exp_sq
      _ = Real.exp (((convexDistance x (projectionSet A)) ^ 2) / 4 + 1/4) := by ring_nf
      _ = Real.exp (((convexDistance x (projectionSet A)) ^ 2) / 4) * Real.exp (1/4) := by
        rw [Real.exp_add]
      _ = Real.exp (1/4) * Real.exp ((convexDistance x (projectionSet A)) ^ 2 / 4) := mul_comm _ _
  · -- Second bound: from t=1 lemma (d_A² ≤ d_sec²) when the section is nonempty
    intro h_nonempty
    have h_sq : (convexDistance (Fin.snoc x ω) A) ^ 2 ≤
        (convexDistance x (sectionSet A ω)) ^ 2 :=
      convexDistance_snoc_section_nonempty_le x ω A h_nonempty
    have h_exp : Real.exp ((convexDistance (Fin.snoc x ω) A) ^ 2 / 4) ≤
        Real.exp ((convexDistance x (sectionSet A ω)) ^ 2 / 4) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact h_exp

/-- Key geometric recursion for Talagrand's convex distance (Blueprint Item 40.5).

For any `t ∈ [0,1]`, `x` in the prefix product, `ω` in the last coordinate, and `A ⊆ Ω^{(n+1)}`
with nonempty ω-section:

  d_A(x,ω)² ≤ (1-t)·d_proj(x)² + t·d_sec(x)² + (1-t)²

where d_proj is the convex distance to `projectionSet A` and d_sec is the
convex distance to `sectionSet A ω`.

The hypothesis `(sectionSet A ω).Nonempty` is essential: the empty-section case is false
for t ∈ (0,1] in general (e.g. Ω={0,1}, A={(1,1)}, x=0, ω=0, t=1 gives 2 ≤ 0), so it is
handled separately by `convexDistance_snoc_empty_section_eq` (Item 40.7), which gives the
exact identity d_A(x,ω)² = d_proj(x)² + 1. -/
theorem convexDistance_recursion {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω (Fin.castSucc i)) (ω : Ω (Fin.last n))
    (A : Set ((i : Fin (n+1)) → Ω i)) (h_sec : (sectionSet A ω).Nonempty) (t : ℝ)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (convexDistance (Fin.snoc x ω) A) ^ 2 ≤
    (1 - t) * (convexDistance x (projectionSet A)) ^ 2 +
    t * (convexDistance x (sectionSet A ω)) ^ 2 +
    (1 - t) ^ 2 := by
  by_cases ht1 : t = 1
  · subst ht1; simp
    exact convexDistance_snoc_section_nonempty_le x ω A h_sec
  · by_cases ht0 : t = 0
    · subst ht0; simp
      exact convexDistance_snoc_le_projection_add_one x ω A
    · -- General t ∈ (0,1), section is nonempty.
      -- Use epsilon-approximate minimizers in the convex hulls.
      -- Key insight: projectLastLM : C_A -> C_proj is surjective,
      -- so we can lift z_proj in C_proj to w_proj in C_A with projectLastLM(w_proj) = z_proj.
      -- Then w = (1-t)*w_proj + t*embedWithZero(z_sec) in C_A gives the bound.
      let dproj := convexDistance x (projectionSet A)
      let dsec := convexDistance x (sectionSet A ω)
      have h_nonneg_dproj : 0 ≤ dproj := convexDistance_nonneg _ _
      have h_nonneg_dsec : 0 ≤ dsec := convexDistance_nonneg _ _
      -- A is nonempty (since the ω-section is nonempty)
      have hA_nonempty : A.Nonempty := by
        rcases h_sec with ⟨y, hy⟩
        exact ⟨Fin.snoc y ω, hy⟩
      -- projectionSet A is nonempty (since A is nonempty)
      have h_proj_nonempty : (projectionSet A).Nonempty := by
        rcases hA_nonempty with ⟨a, ha⟩
        have ha_eta := Fin_snoc_eta a
        refine ⟨fun i => a (Fin.castSucc i), a (Fin.last n), ?_⟩
        rw [ha_eta] at ha; exact ha
      -- If projectionSet = sectionSet, use the t=1 bound directly
      by_cases h_proj_eq_sec : projectionSet A = sectionSet A ω
      · have h_dA_sq_le : convexDistance (Fin.snoc x ω) A ^ 2 ≤ dsec ^ 2 :=
          convexDistance_snoc_section_nonempty_le x ω A h_sec
        rw [h_proj_eq_sec]
        nlinarith
      · -- General case: projectionSet ≠ sectionSet. Use surjectivity lift.
        let π := projectLastLM (n := n)
        let C_A := convexMismatchSet (Fin.snoc x ω) A
        let C_proj := convexMismatchSet x (projectionSet A)
        let C_sec := convexMismatchSet x (sectionSet A ω)
        -- Surjectivity: pi  C_A = C_proj
        have h_surj : π '' C_A = C_proj := by
          dsimp [π, C_A, C_proj, convexMismatchSet]
          have h_img : projectLastLM '' (mismatchVector (Fin.snoc x ω) '' A) =
              mismatchVector x '' (projectionSet A) := by
            apply Set.Subset.antisymm
            · rintro z ⟨v, ⟨y, hy, rfl⟩, rfl⟩
              let y_pref : (i : Fin n) → Ω (Fin.castSucc i) := fun i => y (Fin.castSucc i)
              let y_last : Ω (Fin.last n) := y (Fin.last n)
              have hy_eq : y = Fin.snoc y_pref y_last := Fin_snoc_eta y
              have hy_proj : y_pref ∈ projectionSet A := by
                dsimp [projectionSet, y_pref]
                refine ⟨y_last, ?_⟩
                rw [← hy_eq]; exact hy
              have hπ : projectLastLM (mismatchVector (Fin.snoc x ω) y) = mismatchVector x y_pref := by
                rw [hy_eq]
                exact projectLast_mismatchVector x ω y_last y_pref
              rw [hπ]
              exact ⟨y_pref, hy_proj, rfl⟩
            · rintro w ⟨y, hy, rfl⟩
              rcases hy with ⟨ω', hy'⟩
              refine ⟨mismatchVector (Fin.snoc x ω) (Fin.snoc y ω'), ?_, ?_⟩
              · exact ⟨Fin.snoc y ω', hy', rfl⟩
              · exact projectLast_mismatchVector x ω ω' y
          calc
            projectLastLM '' (convexHull ℝ (mismatchVector (Fin.snoc x ω) '' A)) =
                convexHull ℝ (projectLastLM '' (mismatchVector (Fin.snoc x ω) '' A)) :=
              by rw [π.image_convexHull]
            _ = convexHull ℝ (mismatchVector x '' (projectionSet A)) := by rw [h_img]
        -- For any η > 0, prove the bound dA^2 < RHS + η
        have h_bound : ∀ η > 0, convexDistance (Fin.snoc x ω) A ^ 2 <
            (1 - t) * dproj ^ 2 + t * dsec ^ 2 + (1 - t) ^ 2 + η := by
          intro η hη_pos
          -- Set up δ = min(1, η/(2*C)) for epsilon scaling
          let C := (1 - t) * dproj + t * dsec + 1
          have hC_pos : 0 < C := by
            have hC_nonneg : 0 ≤ (1 - t) * dproj + t * dsec := by
              apply add_nonneg (mul_nonneg (by linarith) h_nonneg_dproj)
                (mul_nonneg ht₀ h_nonneg_dsec)
            nlinarith
          let δ := min 1 (η / (2 * C))
          have hδ_pos : 0 < δ := by
            refine lt_min_iff.mpr ⟨by norm_num, ?_⟩
            exact div_pos hη_pos (by nlinarith)
          have hδ_bound : δ * (2 * ((1 - t) * dproj + t * dsec) + δ) < η := by
            have hδ_le_one : δ ≤ 1 := min_le_left _ _
            have hδ_le_div : δ ≤ η / (2 * C) := min_le_right _ _
            have h_factor_nonneg : 0 ≤ 2 * ((1 - t) * dproj + t * dsec) + 1 := by
              have h_nonneg : 0 ≤ (1 - t) * dproj + t * dsec :=
                add_nonneg (mul_nonneg (by linarith) h_nonneg_dproj) (mul_nonneg ht₀ h_nonneg_dsec)
              nlinarith
            have h_aux : δ * (2 * ((1 - t) * dproj + t * dsec) + 1) < η := by
              calc
                δ * (2 * ((1 - t) * dproj + t * dsec) + 1) ≤
                    (η / (2 * C)) * (2 * ((1 - t) * dproj + t * dsec) + 1) :=
                  mul_le_mul_of_nonneg_right hδ_le_div h_factor_nonneg
                _ = (η / (2 * C)) * (2 * C - 1) := by
                  dsimp [C]; ring
                _ < (η / (2 * C)) * (2 * C) := by
                  refine mul_lt_mul_of_pos_left (by nlinarith) (div_pos hη_pos (by nlinarith))
                _ = η := by field_simp [show 2 * C ≠ 0 from by nlinarith]
            have hδ_sq_le_δ : δ ^ 2 ≤ δ := by
              nlinarith
            calc
              δ * (2 * ((1 - t) * dproj + t * dsec) + δ) =
                  δ * (2 * ((1 - t) * dproj + t * dsec) + 1) + (δ ^ 2 - δ) := by ring
              _ ≤ δ * (2 * ((1 - t) * dproj + t * dsec) + 1) := by
                nlinarith
              _ < η := h_aux
          -- Get δ-approximate minimizer in C_proj
          have h_nonempty_Cproj : C_proj.Nonempty := by
            rcases h_proj_nonempty with ⟨y, hy⟩
            refine ⟨mismatchVector x y, subset_convexHull ℝ
              (mismatchVector x '' (projectionSet A)) ⟨y, hy, rfl⟩⟩
          have h_proj_lt : Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) C_proj <
              Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) C_proj + δ := by nlinarith
          rcases (Metric.infDist_lt_iff h_nonempty_Cproj).mp h_proj_lt with ⟨z_proj, hz_proj, hz_proj_dist⟩
          rw [dist_zero_left] at hz_proj_dist
          have hz_proj_sq_bound : ‖z_proj‖ ^ 2 < (dproj + δ) ^ 2 := by
            have h_nonneg : 0 ≤ ‖z_proj‖ := norm_nonneg _
            have hdproj_def : dproj = Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) C_proj := rfl
            rw [← hdproj_def] at hz_proj_dist
            nlinarith
          -- Lift z_proj to C_A via surjectivity of pi
          rcases (Set.mem_image _ _ _).mp (by rw [h_surj]; exact hz_proj) with ⟨w_proj, hw_proj, hπ_eq⟩
          -- hπ_eq : pi w_proj = z_proj, hw_proj : w_proj in C_A
          -- Get δ-approximate minimizer in C_sec
          have h_nonempty_Csec : C_sec.Nonempty := by
            rcases h_sec with ⟨y, hy⟩
            refine ⟨mismatchVector x y, subset_convexHull ℝ
              (mismatchVector x '' (sectionSet A ω)) ⟨y, hy, rfl⟩⟩
          have h_sec_lt : Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) C_sec <
              Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) C_sec + δ := by nlinarith
          rcases (Metric.infDist_lt_iff h_nonempty_Csec).mp h_sec_lt with ⟨z_sec, hz_sec, hz_sec_dist⟩
          rw [dist_zero_left] at hz_sec_dist
          have hz_sec_sq_bound : ‖z_sec‖ ^ 2 < (dsec + δ) ^ 2 := by
            have h_nonneg : 0 ≤ ‖z_sec‖ := norm_nonneg _
            have hdsec_def : dsec = Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) C_sec := rfl
            rw [← hdsec_def] at hz_sec_dist
            nlinarith
          -- Embed z_sec into C_A with last coord 0
          let w_sec := embedWithZeroLM z_sec
          have h_w_sec_mem : w_sec ∈ C_A := by
            dsimp [w_sec, C_A, convexMismatchSet, embedWithZero]
            have hmem : embedWithZeroLM z_sec ∈ embedWithZeroLM '' C_sec :=
              ⟨z_sec, hz_sec, rfl⟩
            have h_eq : embedWithZeroLM '' C_sec =
                convexHull ℝ (embedWithZeroLM '' (mismatchVector x '' (sectionSet A ω))) := by
              dsimp [C_sec, convexMismatchSet]
              rw [embedWithZeroLM.image_convexHull]
            rw [h_eq] at hmem
            refine convexHull_mono ?_ hmem
            rintro u ⟨v, ⟨y, hy, rfl⟩, rfl⟩
            have h_eq' : embedWithZeroLM (mismatchVector x y) = mismatchVector (Fin.snoc x ω) (Fin.snoc y ω) := by
              simpa [embedWithZero] using embedWithZero_mismatchVector x y ω
            rw [h_eq']
            exact ⟨Fin.snoc y ω, hy, rfl⟩
          -- Form w = (1-t)*w_proj + t*w_sec
          let w := (1 - t) • w_proj + t • w_sec
          have h_w_mem : w ∈ C_A := by
            dsimp [C_A, convexMismatchSet]
            have h_conv : Convex ℝ (convexHull ℝ (mismatchVector (Fin.snoc x ω) '' A)) :=
              convex_convexHull ℝ _
            have hpos1 : 0 ≤ 1 - t := by linarith
            have hsum : (1 - t) + t = 1 := by ring
            exact h_conv hw_proj h_w_sec_mem hpos1 ht₀ hsum
          -- Properties of w
          have h_projectLast_w : projectLastLM w = (1 - t) • z_proj + t • z_sec := by
            dsimp [w, w_sec]
            rw [map_add, map_smul, map_smul, hπ_eq]
            have hπ_embedZero : projectLastLM (n := n) (embedWithZeroLM z_sec) = z_sec := by
              dsimp [embedWithZeroLM, finSnocZeroLM, projectLastLM, restrictCastSuccLM]
              ext i; simp
            rw [hπ_embedZero]
          have h_lastCoord_w : lastCoordLM w = (1 - t) * lastCoordLM w_proj := by
            dsimp [w, w_sec]
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
            have h_last_embedZero : lastCoordLM (n := n) (embedWithZeroLM z_sec) = 0 := by
              dsimp [embedWithZeroLM, finSnocZeroLM, lastCoordLM]
              simp
            rw [h_last_embedZero]; ring
          -- Norm squared decomposition
          have h_norm_sq_w : ‖w‖ ^ 2 = ‖projectLastLM w‖ ^ 2 + (lastCoordLM w) ^ 2 := by
            have h := norm_sq_projectLast_add_last_sq w
            simpa [lastCoordLM] using h
          rw [h_projectLast_w, h_lastCoord_w] at h_norm_sq_w
          -- Convexity of squared norm
          have h_convex_norm : ‖(1 - t) • z_proj + t • z_sec‖ ^ 2 ≤
              (1 - t) * ‖z_proj‖ ^ 2 + t * ‖z_sec‖ ^ 2 := by
            simpa using convexity_norm_sq z_proj z_sec t ht₀ ht₁
          -- Bound lastCoord term: |(1-t)*lastCoord(w_proj)| ≤ 1-t
          have h_lastCoord_proj_sq_le_one : (lastCoordLM w_proj) ^ 2 ≤ 1 :=
            last_coord_sq_le_one x ω A w_proj hw_proj
          have h_last_sq_bound : ((1 - t) * lastCoordLM w_proj) ^ 2 ≤ (1 - t) ^ 2 := by
            calc
              ((1 - t) * lastCoordLM w_proj) ^ 2 = (1 - t) ^ 2 * (lastCoordLM w_proj) ^ 2 := by ring
              _ ≤ (1 - t) ^ 2 * 1 := mul_le_mul_of_nonneg_left h_lastCoord_proj_sq_le_one
                (by nlinarith [ht₀, ht₁])
              _ = (1 - t) ^ 2 := by ring
          -- dA ≤ ||w|| since w in C_A
          have h_dA_sq_le_norm_sq_w : convexDistance (Fin.snoc x ω) A ^ 2 ≤ ‖w‖ ^ 2 := by
            have h_dA_le : convexDistance (Fin.snoc x ω) A ≤ ‖w‖ := by
              dsimp [convexDistance]
              have h_infDist_le :
                  Metric.infDist (0 : EuclideanSpace ℝ (Fin (n+1))) C_A ≤ dist 0 w :=
                Metric.infDist_le_dist_of_mem h_w_mem
              simpa [dist_zero_left] using h_infDist_le
            have h_nonneg_dA : 0 ≤ convexDistance (Fin.snoc x ω) A := convexDistance_nonneg _ _
            nlinarith
          -- Chain all inequalities
          calc
            convexDistance (Fin.snoc x ω) A ^ 2 ≤ ‖w‖ ^ 2 := h_dA_sq_le_norm_sq_w
            _ = ‖(1 - t) • z_proj + t • z_sec‖ ^ 2 + ((1 - t) * lastCoordLM w_proj) ^ 2 := h_norm_sq_w
            _ ≤ ((1 - t) * ‖z_proj‖ ^ 2 + t * ‖z_sec‖ ^ 2) + (1 - t) ^ 2 := by nlinarith [h_convex_norm, h_last_sq_bound]
            _ < ((1 - t) * (dproj + δ) ^ 2 + t * (dsec + δ) ^ 2) + (1 - t) ^ 2 := by
              have h1mt_pos : 0 < 1 - t := by
                have : t < 1 := by
                  by_contra! hge; apply ht1; linarith
                linarith
              have ht_pos : 0 < t := by
                by_contra! hle; apply ht0; linarith
              have h_term1 : (1 - t) * ‖z_proj‖ ^ 2 < (1 - t) * (dproj + δ) ^ 2 := by
                nlinarith
              have h_term2 : t * ‖z_sec‖ ^ 2 < t * (dsec + δ) ^ 2 := by
                nlinarith
              have h_base : (1 - t) * ‖z_proj‖ ^ 2 + t * ‖z_sec‖ ^ 2 <
                  (1 - t) * (dproj + δ) ^ 2 + t * (dsec + δ) ^ 2 :=
                add_lt_add h_term1 h_term2
              linarith
            _ = ((1 - t) * dproj ^ 2 + t * dsec ^ 2 + (1 - t) ^ 2) +
                δ * (2 * ((1 - t) * dproj + t * dsec) + δ) := by
              ring
            _ < ((1 - t) * dproj ^ 2 + t * dsec ^ 2 + (1 - t) ^ 2) + η := by
              linarith
        -- Since bound holds for all η > 0, the inequality holds
        apply le_of_le_add_epsilon
        intro ε hε
        have hlt := h_bound ε hε
        simpa [dproj, dsec] using hlt.le

/-! ## Main Theorem: Measure Decomposition (Blueprint Item 60.1) -/

/-- `(last_coord, prefix) ↦ Fin.snoc prefix last_coord` as a `MeasurableEquiv`. -/
def snocME {n : ℕ} (Ω : Fin (n+1) → Type*) [∀ i, MeasurableSpace (Ω i)] :
    (Ω (Fin.last n) × ((i : Fin n) → Ω (Fin.castSucc i))) ≃ᵐ ((i : Fin (n+1)) → Ω i) where
  toFun := fun ⟨ω, x⟩ => Fin.snoc x ω
  invFun := fun f => (f (Fin.last n), fun i => f (Fin.castSucc i))
  left_inv := by intro ⟨ω, x⟩; ext <;> simp
  right_inv := by
    intro f; ext i
    refine Fin.lastCases (by simp) (fun j => by simp) i
  measurable_toFun := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp; exact measurable_fst
    · simp; exact (measurable_pi_apply j).comp measurable_snd
  measurable_invFun := by
    refine Measurable.prod ?_ ?_
    · exact measurable_pi_apply (Fin.last n)
    · exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (Fin.castSucc i))

/-- Fubini for product measures under `Fin.snoc` decomposition.
For a product measure `μ = ⊗_{i=0}^n μ_i`, integration against `μ` equals
iterated integration: first over the prefix (first n coordinates) with respect to
the product of the first n marginals, then over the last coordinate. -/
theorem measure_pi_snoc_decomposition {n : ℕ} {Ω : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : (i : Fin (n+1)) → Measure (Ω i))
    [∀ i, SigmaFinite (μ i)]
    (f : ((i : Fin (n+1)) → Ω i) → ℝ) (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂(Measure.pi μ) =
    ∫ ω, ∫ x, f (Fin.snoc x ω) ∂(Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) ∂(μ (Fin.last n)) := by
  let e := snocME Ω
  let ν := (μ (Fin.last n)).prod (Measure.pi (fun i : Fin n => μ (Fin.castSucc i)))
  -- Step 1: e is measure-preserving from ν to Measure.pi μ
  have h_map_eq : Measure.map e ν = Measure.pi μ := by
    apply (Measure.pi_eq (fun s hs => ?_)).symm
    have h_preimage : e ⁻¹' (pi univ s) = (s (Fin.last n)) ×ˢ (pi univ (fun i : Fin n => s (Fin.castSucc i))) := by
      ext ⟨ω, x⟩
      dsimp [e, snocME]
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · simpa [Fin.snoc_last] using h (Fin.last n)
        · intro i; simpa [Fin.snoc_castSucc] using h (Fin.castSucc i)
      · intro ⟨h_last, h_cast⟩ i
        refine Fin.lastCases (by simpa [Fin.snoc_last] using h_last)
          (fun j => by simpa [Fin.snoc_castSucc] using h_cast j) i
    rw [Measure.map_apply e.measurable (MeasurableSet.univ_pi (fun i => hs i)), h_preimage]
    rw [Measure.prod_prod (s (Fin.last n)) (pi univ (fun i : Fin n => s (Fin.castSucc i)))]
    rw [show (Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) (pi univ (fun i : Fin n => s (Fin.castSucc i))) =
      ∏ i : Fin n, (μ (Fin.castSucc i)) (s (Fin.castSucc i)) from
      Measure.pi_pi (fun i : Fin n => μ (Fin.castSucc i)) (fun i : Fin n => s (Fin.castSucc i))]
    rw [Fin.prod_univ_castSucc, mul_comm]
  have h_mp : MeasurePreserving e ν (Measure.pi μ) := ⟨e.measurable, h_map_eq⟩
  -- Step 2: Rewrite integral using integral_map_equiv (which does the change-of-variables)
  calc
    ∫ x, f x ∂(Measure.pi μ) = ∫ x, f x ∂(Measure.map e ν) := by rw [h_map_eq]
    _ = ∫ p, f (e p) ∂ν := by rw [integral_map_equiv e f]
    _ = ∫ p : Ω (Fin.last n) × ((i : Fin n) → Ω (Fin.castSucc i)),
          f (Fin.snoc p.2 p.1) ∂ν := by simp [e, snocME]
    _ = ∫ ω, ∫ x, f (Fin.snoc x ω) ∂(Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) ∂(μ (Fin.last n)) := by
      have h_int : Integrable (fun (p : Ω (Fin.last n) × ((i : Fin n) → Ω (Fin.castSucc i))) =>
          f (Fin.snoc p.2 p.1)) ν := by
        -- h_mp.integrable_comp_of_integrable hf : Integrable (f ∘ e) ν
        have h_int' := h_mp.integrable_comp_of_integrable hf
        simpa [e, snocME, Function.comp_def] using h_int'
      rw [integral_prod _ h_int]

/-! ## Main Theorem: Holder Interpolation (Blueprint Item 60.5) -/

/-- Holder inequality for nonnegative integrable functions with
exponents interpolating between L^1 norms. For f, g ≥ 0 a.e.
and t ∈ [0,1], we have ∫ f^{1-t} g^{t} ≤ (∫ f)^{1-t} (∫ g)^{t}.

This is a direct application of `integral_mul_le_Lp_mul_Lq_of_nonneg`
with p = 1/(1-t) and q = 1/t, where the `MemLp` conditions are
derived from integrability via `memLp_norm_rpow_iff`. -/
theorem exp_holder {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : α → ℝ) (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (∫ x, (f x) ^ (1 - t) * (g x) ^ t ∂μ) ≤
    (∫ x, f x ∂μ) ^ (1 - t) * (∫ x, g x ∂μ) ^ t := by
  rcases eq_or_lt_of_le ht₁ with (rfl | ht_lt_one)
  · -- t = 1: ∫ f^0 * g^1 ≤ (∫ f)^0 * (∫ g)^1, both sides equal ∫ g
    simp
  rcases eq_or_lt_of_le ht₀ with (rfl | ht_pos)
  · -- t = 0: ∫ f^1 * g^0 ≤ (∫ f)^1 * (∫ g)^0, both sides equal ∫ f
    simp
  -- Now 0 < t < 1
  have hpos_1mt : 0 < 1 - t := by linarith
  have hpos_t : 0 < t := ht_pos
  have hconj : ((1 - t)⁻¹).HolderConjugate (t⁻¹) :=
    Real.HolderConjugate.one_sub_inv_inv hpos_t ht_lt_one
  set p := (1 - t)⁻¹ with hp_def
  set q := t⁻¹ with hq_def
  have h_ae_f : AEStronglyMeasurable f μ := hf_int.aestronglyMeasurable
  have h_ae_g : AEStronglyMeasurable g μ := hg_int.aestronglyMeasurable
  have hf_memLp_one : MemLp f (1 : ℝ≥0∞) μ :=
    memLp_one_iff_integrable.mpr hf_int
  have hg_memLp_one : MemLp g (1 : ℝ≥0∞) μ :=
    memLp_one_iff_integrable.mpr hg_int
  have hp_ne_zero : ENNReal.ofReal (1 - t) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpos_1mt
  have hp_ne_top : ENNReal.ofReal (1 - t) ≠ ∞ := ENNReal.ofReal_ne_top
  have hq_ne_zero : ENNReal.ofReal t ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hpos_t
  have hq_ne_top : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  -- MemLp condition for f^{1-t} at exponent p = 1/(1-t)
  have hf_memLp : MemLp (fun x => (f x) ^ (1 - t)) (ENNReal.ofReal p) μ := by
    have h := ((memLp_norm_rpow_iff (p := 1) h_ae_f hp_ne_zero hp_ne_top).mpr hf_memLp_one)
    have h_one_div : (1 : ℝ≥0∞) / ENNReal.ofReal (1 - t) = ENNReal.ofReal p := by
      calc
        (1 : ℝ≥0∞) / ENNReal.ofReal (1 - t) = (ENNReal.ofReal (1 - t))⁻¹ := by simp
        _ = ENNReal.ofReal ((1 - t)⁻¹) := by rw [ENNReal.ofReal_inv_of_pos hpos_1mt]
        _ = ENNReal.ofReal p := by rw [hp_def]
    have h_norm : ∀ x, ‖f x‖ = f x := fun x => abs_of_nonneg (hf_nonneg x)
    simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - t), h_one_div, h_norm] using h
  -- MemLp condition for g^{t} at exponent q = 1/t
  have hg_memLp : MemLp (fun x => (g x) ^ t) (ENNReal.ofReal q) μ := by
    have h := ((memLp_norm_rpow_iff (p := 1) h_ae_g hq_ne_zero hq_ne_top).mpr hg_memLp_one)
    have h_one_div : (1 : ℝ≥0∞) / ENNReal.ofReal t = ENNReal.ofReal q := by
      calc
        (1 : ℝ≥0∞) / ENNReal.ofReal t = (ENNReal.ofReal t)⁻¹ := by simp
        _ = ENNReal.ofReal (t⁻¹) := by rw [ENNReal.ofReal_inv_of_pos hpos_t]
        _ = ENNReal.ofReal q := by rw [hq_def]
    have h_norm : ∀ x, ‖g x‖ = g x := fun x => abs_of_nonneg (hg_nonneg x)
    simpa [ENNReal.toReal_ofReal ht₀, h_one_div, h_norm] using h
  -- Apply Holder's inequality
  have h_holder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (ae_of_all μ (fun x => Real.rpow_nonneg (hf_nonneg x) _))
    (ae_of_all μ (fun x => Real.rpow_nonneg (hg_nonneg x) _))
    hf_memLp hg_memLp
  -- h_holder : ∫ f^{1-t} * g^{t} ≤ (∫ (f^{1-t})^p)^(1/p) * (∫ (g^{t})^q)^(1/q)
  -- Note: the lemma writes (…)^(1/p) as (…)^(p⁻¹) in ℝ
  -- Simplify (f^{1-t})^p = f and p⁻¹ = 1-t, similarly for g
  have h_eq_f : (fun x : α => ((f x) ^ (1 - t)) ^ p) =ᵐ[μ] f := by
    refine ae_of_all μ (fun x => ?_)
    calc
      ((f x) ^ (1 - t)) ^ p = (f x) ^ ((1 - t) * p) := by
        rw [Real.rpow_mul (hf_nonneg x) (1 - t) p]
      _ = (f x) ^ (1 : ℝ) := by
        have hcalc : (1 - t) * p = (1 : ℝ) := by
          rw [hp_def]
          field_simp [hpos_1mt.ne.symm]
        rw [hcalc]
      _ = f x := by simp
  have h_int_f : (∫ x, ((f x) ^ (1 - t)) ^ p ∂μ) = (∫ x, f x ∂μ) :=
    integral_congr_ae h_eq_f
  have h_inv_p : p⁻¹ = 1 - t := by
    rw [hp_def, inv_inv]
  have h_eq_g : (fun x : α => ((g x) ^ t) ^ q) =ᵐ[μ] g := by
    refine ae_of_all μ (fun x => ?_)
    calc
      ((g x) ^ t) ^ q = (g x) ^ (t * q) := by
        rw [Real.rpow_mul (hg_nonneg x) t q]
      _ = (g x) ^ (1 : ℝ) := by
        have hcalc : t * q = (1 : ℝ) := by
          rw [hq_def]
          field_simp [hpos_t.ne.symm]
        rw [hcalc]
      _ = g x := by simp
  have h_int_g : (∫ x, ((g x) ^ t) ^ q ∂μ) = (∫ x, g x ∂μ) :=
    integral_congr_ae h_eq_g
  have h_inv_q : q⁻¹ = t := by
    rw [hq_def, inv_inv]
  -- Assemble the result
  simpa [h_int_f, h_int_g, h_inv_p, h_inv_q] using h_holder

/-! ## Talagrand Real-Variable Lemma (Blueprint Item 60.7) -/

/-- The function `u ↦ exp (u - u²) + exp (-u)` appearing in the case-2 inequality
of Talagrand's real-variable lemma. -/
noncomputable def talagrandCase2Fun (x : ℝ) : ℝ :=
  Real.exp (x - x^2) + Real.exp (-x)

/-- For `0 ≤ u ≤ 1/2`, `exp (u - u²) + exp (-u) ≤ 2`.
This is the key case-2 inequality of the real-variable lemma, proved via
`antitoneOn_of_deriv_nonpos` applied to `talagrandCase2Fun`:
`h'(u) = (1-2u)·exp(u-u²) - exp(-u) ≤ 0` since `log(1-2u) ≤ -2u ≤ u² - 2u`. -/
lemma talagrand_real_variable_case2 {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.exp (u - u^2) + Real.exp (-u) ≤ 2 := by
  have hconv : Convex ℝ (Icc (0:ℝ) (1/2:ℝ)) := convex_Icc (0:ℝ) (1/2:ℝ)
  have hdiff_all : Differentiable ℝ talagrandCase2Fun := by
    unfold talagrandCase2Fun
    exact (Real.differentiable_exp.comp (differentiable_id.sub (differentiable_pow 2))).add
      (Real.differentiable_exp.comp differentiable_neg)
  have hcont : ContinuousOn talagrandCase2Fun (Icc (0:ℝ) (1/2:ℝ)) :=
    hdiff_all.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ talagrandCase2Fun (interior (Icc (0:ℝ) (1/2:ℝ))) :=
    hdiff_all.differentiableOn
  have hderiv : ∀ x ∈ interior (Icc (0:ℝ) (1/2:ℝ)), deriv talagrandCase2Fun x ≤ 0 := by
    intro x hx
    have hx1 : x < 1/2 := by
      have hx' : x ∈ Ioo (0:ℝ) (1/2:ℝ) := by
        simpa [interior_Icc] using hx
      exact hx'.2
    have hinner : HasDerivAt (fun y : ℝ => y - y^2) (1 - 2*x) x := by
      have hpow : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
        simpa using (hasDerivAt_pow 2 x)
      exact (hasDerivAt_id' x).sub hpow
    have h1 := HasDerivAt.exp hinner
    have h2 := HasDerivAt.exp (hasDerivAt_neg' (x := x))
    have hderiv_eq : deriv talagrandCase2Fun x =
        (1 - 2*x) * Real.exp (x - x^2) - Real.exp (-x) := by
      unfold talagrandCase2Fun
      have hfeq : (fun y : ℝ => Real.exp (y - y^2) + Real.exp (-y)) =
          (fun y : ℝ => Real.exp (y - y^2)) + (fun y : ℝ => Real.exp (-y)) := by
        ext y
        simp
      rw [hfeq]
      simpa [sub_eq_add_neg, mul_comm, mul_neg] using (h1.add h2).deriv
    have hpos : 0 < 1 - 2*x := by nlinarith [hx1]
    have hlog1 : Real.log (1 - 2*x) ≤ -2*x := by
      simpa using Real.log_le_sub_one_of_pos hpos
    have hlog2 : Real.log (1 - 2*x) ≤ x^2 - 2*x := by nlinarith [hlog1, sq_nonneg x]
    have hexp : (1 - 2*x) * Real.exp (x - x^2) ≤ Real.exp (-x) := by
      have h' : Real.exp (Real.log (1 - 2*x) + (x - x^2)) ≤ Real.exp (-x) :=
        Real.exp_le_exp.mpr (by nlinarith [hlog2])
      rwa [Real.exp_add, Real.exp_log hpos] at h'
    nlinarith [hderiv_eq, hexp]
  have hanti : AntitoneOn talagrandCase2Fun (Icc (0:ℝ) (1/2:ℝ)) :=
    antitoneOn_of_deriv_nonpos hconv hcont hdiff hderiv
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) (1/2:ℝ) := ⟨by norm_num, by norm_num⟩
  have humem : u ∈ Icc (0:ℝ) (1/2:ℝ) := ⟨hu0, hu1⟩
  have hle := hanti h0mem humem hu0
  change Real.exp (u - u^2) + Real.exp (-u) ≤ Real.exp (0 - 0^2) + Real.exp (-0) at hle
  norm_num [Real.exp_zero] at hle
  exact hle

/-- Talagrand's real-variable lemma (Blueprint item 60.7):
for `0 < r ≤ 1` there exists `t ∈ [0,1]` such that
`exp ((1-t)²/4) · r^(-t) ≤ 2 - r`. -/
lemma talagrand_real_variable_lemma {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ t ∈ Icc (0:ℝ) 1, Real.exp ((1 - t)^2 / 4) * r ^ (-t) ≤ 2 - r := by
  let t : ℝ := max 0 (1 + 2 * Real.log r)
  refine ⟨t, ?_, ?_⟩
  · constructor
    · exact le_max_left 0 (1 + 2 * Real.log r)
    · rw [max_le_iff]
      exact ⟨by norm_num, by
        have hlog : Real.log r ≤ 0 := (Real.log_le_iff_le_exp hr0).2 (by simpa using hr1)
        nlinarith⟩
  · by_cases hcase : r ≤ Real.exp (-(1/2:ℝ))
    · -- Case 1: r ≤ e^(-1/2), so t = 0 and it suffices to show exp(1/4) ≤ 2 - r
      have ht0 : t = 0 := by
        dsimp [t]
        have hlog : Real.log r ≤ -(1/2:ℝ) := (Real.log_le_iff_le_exp hr0).2 hcase
        exact max_eq_left (by nlinarith [hlog] : 1 + 2 * Real.log r ≤ 0)
      have h_exp_quarter : Real.exp ((1:ℝ)/4) < (4/3:ℝ) := by
        have := Real.exp_bound_div_one_sub_of_interval' (x := (1/4:ℝ)) (by norm_num) (by norm_num)
        norm_num at this
        exact this
      have h_exp_neg_half : Real.exp (-(1/2:ℝ)) ≤ (2/3:ℝ) := by
        have h := Real.add_one_le_exp (1/2 : ℝ)
        have hmul : Real.exp (-(1/2:ℝ)) * (3/2:ℝ) ≤ 1 := by
          calc
            Real.exp (-(1/2:ℝ)) * (3/2:ℝ) ≤ Real.exp (-(1/2:ℝ)) * Real.exp (1/2) := by
              exact mul_le_mul_of_nonneg_left (by norm_num at h ⊢; exact h) (Real.exp_pos _).le
            _ = 1 := by
              rw [← Real.exp_add]
              norm_num
        nlinarith [hmul]
      have h_main : (4/3:ℝ) ≤ 2 - r := by nlinarith [h_exp_neg_half, hcase]
      calc
        Real.exp ((1 - t)^2 / 4) * r ^ (-t) = Real.exp ((1:ℝ)/4) := by
          rw [ht0]
          norm_num
        _ ≤ 2 - r := by nlinarith [h_exp_quarter, h_main]
    · -- Case 2: r > e^(-1/2), so t = 1 + 2·log r; set u = -log r ∈ [0, 1/2]
      have hlog_ge : -(1/2:ℝ) ≤ Real.log r := by
        have h' : ¬ Real.log r ≤ -(1/2:ℝ) := by
          intro hh
          exact hcase ((Real.log_le_iff_le_exp hr0).1 hh)
        exact le_of_lt (lt_of_not_ge h')
      have hteq : t = 1 + 2 * Real.log r := by
        dsimp [t]
        rw [max_comm]
        exact max_eq_left (by nlinarith [hlog_ge] : 0 ≤ 1 + 2 * Real.log r)
      let u : ℝ := -Real.log r
      have hu0 : 0 ≤ u := by
        dsimp [u]
        have hlog : Real.log r ≤ 0 := (Real.log_le_iff_le_exp hr0).2 (by simpa using hr1)
        nlinarith
      have hu1 : u ≤ 1/2 := by
        dsimp [u]
        nlinarith [hlog_ge]
      have haux : Real.exp (u - u^2) + Real.exp (-u) ≤ 2 :=
        talagrand_real_variable_case2 hu0 hu1
      calc
        Real.exp ((1 - t)^2 / 4) * r ^ (-t)
            = Real.exp ((Real.log r)^2) * Real.exp (Real.log r * -t) := by
          have hsq : (1 - t)^2 / 4 = (Real.log r)^2 := by
            rw [hteq]
            ring_nf
          rw [hsq, Real.rpow_def_of_pos hr0]
        _ = Real.exp ((Real.log r)^2 + Real.log r * -t) := by rw [Real.exp_add]
        _ = Real.exp (u - u^2) := by
          dsimp [u]
          rw [hteq]
          congr 1
          ring
        _ ≤ 2 - Real.exp (-u) := by nlinarith [haux]
        _ = 2 - r := by
          rw [← Real.exp_log hr0]
          congr 1
          dsimp [u]
          congr 1
          ring

/-! ## Algebraic Assembly (Blueprint Item 60.8) -/

/-- Generic algebraic assembly for the induction step; works for any finite index type `ι`.
Given:
- `q ω ≥ 0` with `∑ ω, q ω = 1`,
- `0 ≤ x ω ≤ Y` (with `0 < Y`), and `S = ∑ ω, q ω * x ω`,
- per-`ω` bounds:
  - (interpolation) if `0 < x ω`, then for every `t ∈ [0,1]`,
    `I ω ≤ exp((1-t)²/4) · Y^(t-1) · (x ω)^(-t)`;
  - (null section) if `x ω = 0`, then `I ω ≤ exp(1/4) / Y`.

Then `S · (∑ ω, q ω * I ω) ≤ 1`. -/
lemma talagrand_algebraic_assembly {ι : Type*} [Fintype ι] (q x I : ι → ℝ) (Y : ℝ)
    (hY : 0 < Y) (hq : ∀ ω, 0 ≤ q ω) (hqsum : ∑ ω, q ω = 1)
    (hx : ∀ ω, 0 ≤ x ω) (hxY : ∀ ω, x ω ≤ Y)
    (hI_pos : ∀ ω, 0 < x ω → ∀ t ∈ Icc (0:ℝ) 1,
      I ω ≤ Real.exp ((1 - t)^2 / 4) * Y ^ (t - 1) * (x ω) ^ (-t))
    (hI_zero : ∀ ω, x ω = 0 → I ω ≤ Real.exp (1/4) / Y) :
    (∑ ω, q ω * x ω) * (∑ ω, q ω * I ω) ≤ 1 := by
  -- Step 1: per-ω bound `I ω ≤ (2 - x ω / Y) / Y`
  have hIbound : ∀ ω, I ω ≤ (2 - x ω / Y) / Y := by
    intro ω
    by_cases hx0 : x ω = 0
    · -- x ω = 0: `I ω ≤ exp(1/4)/Y ≤ 2/Y = (2 - 0)/Y`
      have h_exp_quarter : Real.exp ((1:ℝ)/4) < (4/3:ℝ) := by
        have h := Real.exp_bound_div_one_sub_of_interval' (x := (1/4:ℝ))
          (by norm_num) (by norm_num)
        norm_num at h
        exact h
      have h_exp_le_two : Real.exp ((1:ℝ)/4) ≤ (2:ℝ) := by nlinarith
      calc
        I ω ≤ Real.exp ((1:ℝ)/4) / Y := hI_zero ω hx0
        _ ≤ (2:ℝ) / Y := div_le_div_of_nonneg_right h_exp_le_two (le_of_lt hY)
        _ = (2 - x ω / Y) / Y := by simp [hx0]
    · -- x ω > 0: interpolation via `talagrand_real_variable_lemma` with r = x ω / Y
      have hxpos : 0 < x ω := lt_of_le_of_ne' (hx ω) hx0
      let r : ℝ := x ω / Y
      have hr0 : 0 < r := by dsimp [r]; exact div_pos hxpos hY
      have hr1 : r ≤ 1 := by
        dsimp [r]
        exact (div_le_one hY).2 (hxY ω)
      rcases talagrand_real_variable_lemma (r := r) hr0 hr1 with ⟨t, htIcc, ht⟩
      have hI' : I ω ≤ Real.exp ((1 - t)^2 / 4) * Y ^ (t - 1) * (x ω) ^ (-t) :=
        hI_pos ω hxpos t htIcc
      have hx_eq : x ω = Y * r := by
        dsimp [r]
        exact (mul_div_cancel₀ (x ω) hY.ne').symm
      have hpow : Y ^ (t - 1) * (x ω) ^ (-t) = Y ^ (-1 : ℝ) * r ^ (-t) := by
        calc
          Y ^ (t - 1) * (x ω) ^ (-t) = Y ^ (t - 1) * (Y * r) ^ (-t) := by rw [hx_eq]
          _ = Y ^ (t - 1) * (Y ^ (-t) * r ^ (-t)) := by
            rw [Real.mul_rpow (le_of_lt hY) (le_of_lt hr0)]
          _ = (Y ^ (t - 1) * Y ^ (-t)) * r ^ (-t) := by ring
          _ = Y ^ ((t - 1) + (-t)) * r ^ (-t) := by rw [← Real.rpow_add hY]
          _ = Y ^ (-1 : ℝ) * r ^ (-t) := by
            rw [show (t - 1) + (-t) = (-1 : ℝ) by ring]
      have hmain : Real.exp ((1 - t)^2 / 4) * (Y ^ (t - 1) * (x ω) ^ (-t)) ≤
          (2 - x ω / Y) / Y := by
        calc
          Real.exp ((1 - t)^2 / 4) * (Y ^ (t - 1) * (x ω) ^ (-t)) =
              Real.exp ((1 - t)^2 / 4) * (Y ^ (-1 : ℝ) * r ^ (-t)) := by rw [hpow]
          _ = (Real.exp ((1 - t)^2 / 4) * r ^ (-t)) * Y ^ (-1 : ℝ) := by ring
          _ ≤ (2 - r) * Y ^ (-1 : ℝ) := by
            exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (le_of_lt hY) _)
          _ = (2 - x ω / Y) / Y := by
            dsimp [r]
            calc
              (2 - x ω / Y) * Y ^ (-1 : ℝ) = (2 - x ω / Y) * Y⁻¹ := by
                rw [Real.rpow_neg_one]
              _ = (2 - x ω / Y) / Y := (div_eq_mul_inv _ _).symm
      calc
        I ω ≤ Real.exp ((1 - t)^2 / 4) * Y ^ (t - 1) * (x ω) ^ (-t) := hI'
        _ = Real.exp ((1 - t)^2 / 4) * (Y ^ (t - 1) * (x ω) ^ (-t)) := by ring
        _ ≤ (2 - x ω / Y) / Y := hmain
  -- Step 2: sum over ω
  have hsum_bound : (∑ ω, q ω * I ω) ≤ (2 - (∑ ω, q ω * x ω) / Y) / Y := by
    calc
      (∑ ω, q ω * I ω) ≤ ∑ ω, q ω * ((2 - x ω / Y) / Y) := by
        exact Finset.sum_le_sum (fun ω hω => mul_le_mul_of_nonneg_left (hIbound ω) (hq ω))
      _ = (2 - (∑ ω, q ω * x ω) / Y) / Y := by
        calc
          (∑ ω, q ω * ((2 - x ω / Y) / Y)) = (∑ ω, (q ω * (2 - x ω / Y)) / Y) := by
            apply Finset.sum_congr rfl
            intro ω hω
            rw [mul_div_assoc]
          _ = (∑ ω, q ω * (2 - x ω / Y)) / Y := by rw [← Finset.sum_div]
          _ = (2 - (∑ ω, q ω * x ω) / Y) / Y := by
            have hsum1 : (∑ ω, q ω * (2 - x ω / Y)) = 2 - (∑ ω, q ω * x ω) / Y := by
              calc
                (∑ ω, q ω * (2 - x ω / Y)) = (∑ ω, (q ω * 2 - q ω * (x ω / Y))) := by
                  apply Finset.sum_congr rfl
                  intro ω hω
                  ring
                _ = (∑ ω, q ω * 2) - (∑ ω, q ω * (x ω / Y)) := by
                  rw [Finset.sum_sub_distrib]
                _ = 2 - (∑ ω, q ω * (x ω / Y)) := by
                  have h2 : (∑ ω, q ω * 2) = 2 := by
                    rw [← Finset.sum_mul, hqsum]
                    norm_num
                  rw [h2]
                _ = 2 - (∑ ω, q ω * x ω) / Y := by
                  have hdiv : (∑ ω, q ω * (x ω / Y)) = (∑ ω, q ω * x ω) / Y := by
                    calc
                      (∑ ω, q ω * (x ω / Y)) = (∑ ω, (q ω * x ω) / Y) := by
                        apply Finset.sum_congr rfl
                        intro ω hω
                        rw [mul_div_assoc]
                      _ = (∑ ω, q ω * x ω) / Y := by rw [← Finset.sum_div]
                  rw [hdiv]
            rw [hsum1]
  -- Step 3: close
  have hS_nonneg : 0 ≤ ∑ ω, q ω * x ω := by
    exact Finset.sum_nonneg (fun ω hω => mul_nonneg (hq ω) (hx ω))
  have hclose : (∑ ω, q ω * x ω) * ((2 - (∑ ω, q ω * x ω) / Y) / Y) ≤ 1 := by
    have hdiff : 1 - (∑ ω, q ω * x ω) * ((2 - (∑ ω, q ω * x ω) / Y) / Y) =
        (1 - (∑ ω, q ω * x ω) / Y) ^ 2 := by
      field_simp [hY.ne']
      ring
    rw [← sub_nonneg, hdiff]
    exact sq_nonneg _
  calc
    (∑ ω, q ω * x ω) * (∑ ω, q ω * I ω) ≤
        (∑ ω, q ω * x ω) * ((2 - (∑ ω, q ω * x ω) / Y) / Y) := by
      exact mul_le_mul_of_nonneg_left hsum_bound hS_nonneg
    _ ≤ 1 := hclose

/-! ## Main Theorem: Measure Decomposition (Blueprint Item 60.12) -/

/-- Measure decomposition of A via Fin.snoc:
`S = Σ ω, q ω * x_sec ω` where S = μ(A).toReal, q ω = μ_last({ω}).toReal,
x_sec ω = P(A_ω).toReal. (Blueprint 60.12) -/
theorem measure_decomposition_S {n : ℕ} {Ω : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, DecidableEq (Ω i)]
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (μ : (i : Fin (n+1)) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin (n+1)) → Ω i)) :
    let S := (Measure.pi μ A).toReal
    let q (ω : Ω (Fin.last n)) := (μ (Fin.last n) {ω}).toReal
    let x_sec (ω : Ω (Fin.last n)) :=
      ((Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) (sectionSet A ω)).toReal
    S = ∑ ω, q ω * x_sec ω := by
  intro S q x_sec
  set f := A.indicator (1 : ((i : Fin (n+1)) → Ω i) → ℝ) with hf_def
  -- Step 1: f is integrable (finite discrete probability space → all functions integrable)
  have hf_int : Integrable f (Measure.pi μ) :=
    Integrable.of_finite (f := f) (μ := Measure.pi μ)
  -- Step 2: apply snoc decomposition theorem (Blueprint 60.1)
  have h_decomp := measure_pi_snoc_decomposition μ f hf_int
  -- Step 3: LHS simplifies to S via integral_indicator_one
  have hLHS : ∫ x, f x ∂(Measure.pi μ) = S := by
    dsimp [S, f]
    simpa [measureReal_def] using integral_indicator_one (MeasurableSet.of_discrete (s := A))
  -- Step 4: inner integrand simplifies to x_sec ω via indicator_snoc + integral_indicator_one
  have hInner : ∀ ω, ∫ x, f (Fin.snoc x ω) ∂(Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) = x_sec ω := by
    intro ω
    dsimp [f, x_sec]
    have hmeas : MeasurableSet (sectionSet A ω) :=
      MeasurableSet.of_discrete (s := sectionSet A ω)
    calc
      ∫ x, (A.indicator 1) (Fin.snoc x ω) ∂(Measure.pi (fun i : Fin n => μ (Fin.castSucc i)))
          = ∫ x, ((sectionSet A ω).indicator 1) x ∂(Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) := by
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        simp [sectionSet, Set.indicator]
      _ = ((Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) (sectionSet A ω)).toReal := by
        simpa [measureReal_def] using integral_indicator_one hmeas
  -- Step 5: outer integral = sum via integral_fintype
  have hOuter : ∫ ω, x_sec ω ∂(μ (Fin.last n)) = ∑ ω, q ω * x_sec ω := by
    dsimp [q]
    have h_int_outer : Integrable x_sec (μ (Fin.last n)) :=
      Integrable.of_finite (f := x_sec) (μ := μ (Fin.last n))
    simpa [measureReal_def, smul_eq_mul] using integral_fintype h_int_outer
  -- Combine
  calc
    S = ∫ x, f x ∂(Measure.pi μ) := by rw [hLHS]
    _ = ∫ ω, ∫ x, f (Fin.snoc x ω) ∂(Measure.pi (fun i : Fin n => μ (Fin.castSucc i))) ∂(μ (Fin.last n)) := h_decomp
    _ = ∫ ω, x_sec ω ∂(μ (Fin.last n)) := by
      refine integral_congr_ae (ae_of_all (μ (Fin.last n)) hInner)
    _ = ∑ ω, q ω * x_sec ω := hOuter

/-! ## Main Theorem: Talagrand's Convex-Distance Inequality (Blueprint Item 60.10) -/

/-- Exponent algebra for the real exponential: `(exp a) ^ C = exp (C * a)`. -/
lemma Real.exp_rpow (a : ℝ) (C : ℝ) : (Real.exp a) ^ C = Real.exp (C * a) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos a) C, Real.log_exp a, mul_comm]

/-- The singleton masses of a probability measure on a finite type sum to one:
`∑ x, (μ {x}).toReal = 1`. -/
lemma sum_pointMasses_eq_one {α : Type*} [MeasurableSpace α] [Fintype α]
    [MeasurableSingletonClass α] {μ : Measure α} [IsProbabilityMeasure μ] :
    ∑ x : α, (μ {x}).toReal = 1 := by
  calc
    ∑ x : α, (μ {x}).toReal = ∑ x : α, μ.real {x} := by simp [MeasureTheory.measureReal_def]
    _ = μ.real ((Finset.univ : Finset α) : Set α) := by
      simp [MeasureTheory.sum_measureReal_singleton]
    _ = (μ Set.univ).toReal := by simp [MeasureTheory.measureReal_def]
    _ = 1 := by simp

/-- **Talagrand's convex-distance inequality** — the main theorem of the project
(Blueprint item 60.10).

Let `Ω = ∏ᵢ Ωᵢ` be a finite product of finite probability spaces `(Ωᵢ, μᵢ)` with
product measure `μ = Measure.pi μi`. For any nonempty set `A ⊆ Ω`,

`μ(A) * ∫_Ω exp(d_A(x)² / 4) dμ(x) ≤ 1`,

where `d_A(x) = convexDistance x A` is the convex distance from `x` to `A`
(the distance from the origin to the convex hull of the mismatch vectors `v(x, y)`
for `y ∈ A`). Equivalently, when `0 < μ(A)`,
`∫_Ω exp(d_A(x)² / 4) dμ(x) ≤ 1 / μ(A)`
(see `talagrand_convexDistance_integral_le_one_div`, item 80.20).

The proof is by induction on the dimension `n`:

* **Base case `n = 0`:** the product space is a subsingleton, `d_A(x) = 0` at its
  unique point (by `convexDistance_zero_of_mem`), so the integral equals `1` and
  the claim reduces to `μ(A) ≤ 1`.
* **Inductive step `n → n + 1`:** write `Ω ≃ Ω_prefix × Ω_last` via `Fin.snoc`, with
  prefix measure `P` and last-coordinate measure `μ_last`. Let `B = projectionSet A`
  be the projection of `A` onto `Ω_prefix` and `A_ω = sectionSet A ω` the section
  over `ω : Ω_last`. Fubini (`measure_pi_snoc_decomposition`, item 60.1) rewrites
  the integral over `Ω` as a weighted sum `∑_ω q ω * I ω` of the inner integrals
  `I ω = ∫_x exp(d_A(snoc x ω)² / 4) dP`, with `q ω = (μ_last {ω}).toReal`.
  For each `ω` with nonempty section and each `t ∈ [0, 1]`, the geometric recursion
  (`convexDistance_recursion`, item 40.5) gives the pointwise bound

  `exp(d_A(x, ω)² / 4) ≤ exp((1-t)² / 4) * exp(d_B(x)²/4)^(1-t) * exp(d_{A_ω}(x)²/4)^t`,

  which is integrated (Hölder interpolation, `exp_holder`, item 60.5) to

  `I ω ≤ exp((1-t)² / 4) * J_B^(1-t) * J_{A_ω}^t`,

  where `J_B ≤ 1/Y` and `J_{A_ω} ≤ 1/x_ω` by the induction hypothesis applied to
  `B` and to `A_ω` (here `Y = (P B).toReal` and `x_ω = (P A_ω).toReal`). Since the
  choice of `t ∈ [0, 1]` is free, this yields

  `I ω ≤ exp((1-t)² / 4) * Y^(t-1) * x_ω^(-t)` whenever `x_ω > 0`,

  while the two-valued bound `scalar_optimization_two_valued` covers the empty
  sections: `I ω ≤ exp(1/4) / Y` whenever `x_ω = 0`. The final algebraic assembly
  (`talagrand_algebraic_assembly`, item 60.8, which internally optimizes over `t`
  via `talagrand_real_variable_lemma`, item 60.7), combined with the measure
  decomposition `S = μ(A).toReal = ∑_ω q ω * x_ω` (`measure_decomposition_S`,
  item 60.12) and the monotonicity `S ≤ Y`, closes the induction:
  `S * ∑_ω q ω * I ω ≤ 1`. -/
theorem talagrand_convexDistance {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    [∀ i, DecidableEq (Ω i)]
    {μ : (i : Fin n) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin n) → Ω i)) (hA : A.Nonempty) :
    (Measure.pi μ A).toReal * (∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ)) ≤ 1 := by
  induction n with
  | zero =>
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    have h_cd_zero : ∀ x : ((i : Fin 0) → Ω i), convexDistance x A = 0 := by
      intro x
      have hx : x = hA.some := Subsingleton.elim _ _
      rw [hx]; exact convexDistance_zero_of_mem hA.some A hA.choose_spec
    have h_int : (∫ x : ((i : Fin 0) → Ω i), Real.exp ((convexDistance x A) ^ 2 / 4)
        ∂(Measure.pi μ)) = 1 := by
      calc
        (∫ x : ((i : Fin 0) → Ω i), Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ))
            = (∫ x : ((i : Fin 0) → Ω i), (1 : ℝ) ∂(Measure.pi μ)) := by
          refine integral_congr_ae (ae_of_all _ (fun x => ?_)); simp [h_cd_zero x]
        _ = (Measure.pi μ Set.univ).toReal := by simp [integral_const]
        _ = 1 := by
          have h_prob : IsProbabilityMeasure (Measure.pi μ) := by infer_instance
          simp [h_prob.measure_univ]
    have h_probA_le_one : (Measure.pi μ A).toReal ≤ 1 := by
      have h_prob : IsProbabilityMeasure (Measure.pi μ) := by infer_instance
      have h_le_one : Measure.pi μ A ≤ (1 : ENNReal) :=
        (measure_mono (Set.subset_univ _)).trans_eq h_prob.measure_univ
      simpa [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top h_le_one
    calc
      (Measure.pi μ A).toReal *
          (∫ x : ((i : Fin 0) → Ω i), Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ))
          = (Measure.pi μ A).toReal * (1 : ℝ) := by rw [h_int]
      _ = (Measure.pi μ A).toReal := by simp
      _ ≤ 1 := h_probA_le_one
  | succ n ih =>
    -- Decompose Ω^{(n+1)} ≃ Ω_prefix × Ω_last
    let Ω_prefix : Type _ := (i : Fin n) → Ω (Fin.castSucc i)
    let Ω_last := Ω (Fin.last n)
    let P : Measure Ω_prefix := Measure.pi (fun i : Fin n => μ (Fin.castSucc i))
    let μ_last := μ (Fin.last n)

    haveI : SigmaFinite P := by
      haveI : IsProbabilityMeasure P := by infer_instance
      infer_instance
    haveI : SigmaFinite μ_last := by
      haveI : IsProbabilityMeasure μ_last := by infer_instance
      infer_instance

    let f : ((i : Fin (n+1)) → Ω i) → ℝ := fun z =>
      Real.exp ((convexDistance z A) ^ 2 / 4)
    have hf_int : Integrable f (Measure.pi μ) := Integrable.of_finite

    -- Fubini (Blueprint 60.1)
    have h_fubini : (∫ z : ((i : Fin (n+1)) → Ω i), f z ∂(Measure.pi μ)) =
        ∫ ω : Ω_last, ∫ x : Ω_prefix, f (Fin.snoc x ω) ∂P ∂μ_last := by
      rw [measure_pi_snoc_decomposition μ f hf_int]

    -- Projection B (Blueprint 20.40)
    let B : Set Ω_prefix := projectionSet A
    have hB_nonempty : B.Nonempty := by
      rcases hA with ⟨z, hz⟩
      refine ⟨fun i => z (Fin.castSucc i), z (Fin.last n), ?_⟩
      have hz_snoc : Fin.snoc (fun i => z (Fin.castSucc i)) (z (Fin.last n)) = z := by
        ext i; refine Fin.lastCases (by simp) (fun j => by simp) i
      rw [hz_snoc]; exact hz

    -- IH applied to B
    let J_B := ∫ x : Ω_prefix, Real.exp ((convexDistance x B) ^ 2 / 4) ∂P
    let Y := (P B).toReal
    have h_ih_B : Y * J_B ≤ 1 := by
      simpa [Y, J_B, P] using ih B hB_nonempty
    have hY_nonneg : 0 ≤ Y := ENNReal.toReal_nonneg
    have hJ_B_nonneg : 0 ≤ J_B := by
      dsimp [J_B]
      exact integral_nonneg (fun x => le_of_lt (Real.exp_pos ((convexDistance x B) ^ 2 / 4)))

    -- Total mass S = μ(A).toReal
    let S := (Measure.pi μ A).toReal
    have hS_nonneg : 0 ≤ S := ENNReal.toReal_nonneg

    -- Per-ω constants
    let q (ω : Ω_last) : ℝ := (μ_last {ω}).toReal
    let x_sec (ω : Ω_last) : ℝ := (P (sectionSet A ω)).toReal
    have hq_nonneg (ω : Ω_last) : 0 ≤ q ω := ENNReal.toReal_nonneg
    have hx_sec_nonneg (ω : Ω_last) : 0 ≤ x_sec ω := ENNReal.toReal_nonneg
    have hx_sec_le_Y (ω : Ω_last) : x_sec ω ≤ Y := by
      dsimp [x_sec, Y]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      dsimp [sectionSet, B, projectionSet]
      intro x hx
      exact ⟨ω, hx⟩

    -- Per-ω inner integrals I ω = ∫_x f(snoc x ω) dP
    let I (ω : Ω_last) : ℝ := ∫ x : Ω_prefix, f (Fin.snoc x ω) ∂P
    have hI_nonneg (ω : Ω_last) : 0 ≤ I ω := by
      dsimp [I]
      exact integral_nonneg (fun x =>
        le_of_lt (Real.exp_pos ((convexDistance (Fin.snoc x ω) A) ^ 2 / 4)))

    -- Section integrals J_ω and IH for sections
    let J_sec (ω : Ω_last) : ℝ :=
      ∫ x : Ω_prefix, Real.exp ((convexDistance x (sectionSet A ω)) ^ 2 / 4) ∂P
    have hJ_sec_nonneg (ω : Ω_last) : 0 ≤ J_sec ω := by
      dsimp [J_sec]
      exact integral_nonneg (fun x =>
        le_of_lt (Real.exp_pos ((convexDistance x (sectionSet A ω)) ^ 2 / 4)))
    have h_ih_sec (ω : Ω_last) (h_sec : (sectionSet A ω).Nonempty) :
        x_sec ω * J_sec ω ≤ 1 := by
      simpa [x_sec, J_sec, P] using ih (sectionSet A ω) h_sec

    -- Integral over ω as finite sum (Fintype)
    have h_integral_eq_sum :
        (∫ ω : Ω_last, (∫ x : Ω_prefix, f (Fin.snoc x ω) ∂P) ∂μ_last) =
          ∑ ω : Ω_last, q ω * (∫ x : Ω_prefix, f (Fin.snoc x ω) ∂P) := by
      simpa [q, smul_eq_mul, MeasureTheory.measureReal_def, mul_comm] using
        integral_fintype (μ := μ_last)
          (f := fun (ω : Ω_last) => (∫ x : Ω_prefix, f (Fin.snoc x ω) ∂P))

    -- Rewrite the Fubini result using the sum representation
    have h_integral : (∫ x : ((i : Fin (n+1)) → Ω i), f x ∂(Measure.pi μ)) =
        ∑ ω : Ω_last, q ω * I ω := by
      rw [h_fubini, h_integral_eq_sum]

    -- q_ω sum to 1 (probability measure)
    have hq_sum : ∑ ω : Ω_last, q ω = 1 := by
      simpa [q] using (sum_pointMasses_eq_one (μ := μ_last))

    -- S = Σ_ω q_ω · x_ω (measure decomposition, Blueprint 60.12)
    have hS_eq_sum : S = ∑ ω : Ω_last, q ω * x_sec ω := by
      simpa [S, q, x_sec, P, μ_last] using measure_decomposition_S μ A

    -- From S = Σ q_ω·x_ω and x_ω ≤ Y, we get S ≤ Y
    have hSY : S ≤ Y := by
      calc
        S = ∑ ω : Ω_last, q ω * x_sec ω := hS_eq_sum
        _ ≤ ∑ ω : Ω_last, q ω * Y := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          have hq := hq_nonneg ω
          have hx := hx_sec_le_Y ω
          nlinarith
        _ = (∑ ω : Ω_last, q ω) * Y := by exact Eq.symm (Finset.sum_mul Finset.univ q Y)
        _ = 1 * Y := by rw [hq_sum]
        _ = Y := by simp

    -- ═════════════════════════════════════════════════════════════
    -- ALGEBRAIC ASSEMBLY: Show S · Σ_ω q_ω · I_ω ≤ 1
    -- ═════════════════════════════════════════════════════════════
    have h_total_bound : S * (∑ ω : Ω_last, q ω * I ω) ≤ 1 := by
      by_cases hS0 : S = 0
      · -- degenerate case: S = 0
        rw [hS0]
        norm_num
      · -- main case: S > 0, hence Y > 0
        have hS_pos : 0 < S := lt_of_le_of_ne' hS_nonneg hS0
        have hY_pos : 0 < Y := lt_of_lt_of_le hS_pos hSY

        -- Per-ω interpolation bound (Blueprint 40.5 + 60.5 + IH)
        have hI_pos : ∀ ω : Ω_last, 0 < x_sec ω → ∀ t ∈ Icc (0:ℝ) 1,
            I ω ≤ Real.exp ((1 - t)^2 / 4) * Y ^ (t - 1) * (x_sec ω) ^ (-t) := by
          intro ω hxpos t ht
          have ht0 : 0 ≤ t := ht.1
          have ht1 : t ≤ 1 := ht.2
          have h1mt : 0 ≤ 1 - t := by linarith
          -- the section is nonempty (positive mass)
          have h_sec : (sectionSet A ω).Nonempty := by
            by_contra hne
            have h_empty : sectionSet A ω = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
            have hx0 : x_sec ω = 0 := by
              dsimp [x_sec]
              rw [h_empty]
              simp
            exact (ne_of_gt hxpos) hx0
          let fB : Ω_prefix → ℝ := fun x => Real.exp ((convexDistance x B) ^ 2 / 4)
          let fSec : Ω_prefix → ℝ :=
            fun x => Real.exp ((convexDistance x (sectionSet A ω)) ^ 2 / 4)
          -- pointwise bound from the recursion (40.5) and exp arithmetic
          have h_pointwise (x : Ω_prefix) :
              f (Fin.snoc x ω) ≤
                Real.exp ((1 - t)^2 / 4) * ((fB x) ^ (1 - t) * (fSec x) ^ t) := by
            dsimp [f, fB, fSec]
            have hrec := convexDistance_recursion x ω A h_sec t ht0 ht1
            have h_exp_le : Real.exp ((convexDistance (Fin.snoc x ω) A) ^ 2 / 4) ≤
                Real.exp (((1 - t) * (convexDistance x B) ^ 2 +
                  t * (convexDistance x (sectionSet A ω)) ^ 2 + (1 - t) ^ 2) / 4) := by
              apply Real.exp_le_exp.mpr
              nlinarith [hrec]
            have h_exp_eq : Real.exp (((1 - t) * (convexDistance x B) ^ 2 +
                  t * (convexDistance x (sectionSet A ω)) ^ 2 + (1 - t) ^ 2) / 4) =
                Real.exp ((1 - t)^2 / 4) *
                  ((Real.exp ((convexDistance x B) ^ 2 / 4)) ^ (1 - t) *
                    (Real.exp ((convexDistance x (sectionSet A ω)) ^ 2 / 4)) ^ t) := by
              calc
                Real.exp (((1 - t) * (convexDistance x B) ^ 2 +
                    t * (convexDistance x (sectionSet A ω)) ^ 2 + (1 - t) ^ 2) / 4)
                    = Real.exp (((1 - t) * (convexDistance x B) ^ 2 +
                        t * (convexDistance x (sectionSet A ω)) ^ 2) / 4 + (1 - t) ^ 2 / 4) := by
                      congr 1; ring_nf
                _ = Real.exp (((1 - t) * (convexDistance x B) ^ 2 +
                      t * (convexDistance x (sectionSet A ω)) ^ 2) / 4) *
                    Real.exp ((1 - t) ^ 2 / 4) := by
                  rw [Real.exp_add]
                _ = Real.exp ((1 - t) * ((convexDistance x B) ^ 2 / 4) +
                      t * ((convexDistance x (sectionSet A ω)) ^ 2 / 4)) *
                    Real.exp ((1 - t) ^ 2 / 4) := by
                  congr 1; ring_nf
                _ = (Real.exp ((1 - t) * ((convexDistance x B) ^ 2 / 4)) *
                      Real.exp (t * ((convexDistance x (sectionSet A ω)) ^ 2 / 4))) *
                    Real.exp ((1 - t) ^ 2 / 4) := by
                  rw [Real.exp_add]
                _ = Real.exp ((1 - t) ^ 2 / 4) *
                    ((Real.exp ((convexDistance x B) ^ 2 / 4)) ^ (1 - t) *
                      (Real.exp ((convexDistance x (sectionSet A ω)) ^ 2 / 4)) ^ t) := by
                  rw [(Real.exp_rpow ((convexDistance x B) ^ 2 / 4) (1 - t)).symm,
                    (Real.exp_rpow ((convexDistance x (sectionSet A ω)) ^ 2 / 4) t).symm]
                  ring
            calc
              f (Fin.snoc x ω) ≤
                  Real.exp (((1 - t) * (convexDistance x B) ^ 2 +
                    t * (convexDistance x (sectionSet A ω)) ^ 2 + (1 - t) ^ 2) / 4) :=
                h_exp_le
              _ = Real.exp ((1 - t)^2 / 4) * ((fB x) ^ (1 - t) * (fSec x) ^ t) :=
                h_exp_eq
          -- integrate the pointwise bound
          have h_int_le : I ω ≤ Real.exp ((1 - t)^2 / 4) *
              (∫ x : Ω_prefix, (fB x) ^ (1 - t) * (fSec x) ^ t ∂P) := by
            dsimp [I]
            calc
              (∫ x : Ω_prefix, f (Fin.snoc x ω) ∂P) ≤
                  ∫ x : Ω_prefix, Real.exp ((1 - t)^2 / 4) *
                    ((fB x) ^ (1 - t) * (fSec x) ^ t) ∂P := by
                refine integral_mono (Integrable.of_finite) (Integrable.of_finite)
                  (fun x => h_pointwise x)
              _ = Real.exp ((1 - t)^2 / 4) *
                  (∫ x : Ω_prefix, (fB x) ^ (1 - t) * (fSec x) ^ t ∂P) := by
                rw [integral_const_mul]
          -- Holder (60.5)
          have h_holder := exp_holder (α := Ω_prefix) (μ := P) fB fSec
            (fun x => le_of_lt (Real.exp_pos ((convexDistance x B) ^ 2 / 4)))
            (fun x => le_of_lt (Real.exp_pos ((convexDistance x (sectionSet A ω)) ^ 2 / 4)))
            (Integrable.of_finite (f := fB)) (Integrable.of_finite (f := fSec)) t ht0 ht1
          -- IH bounds on the two integrals
          have h_JB_le : J_B ≤ (1 / Y : ℝ) := by
            exact (le_div_iff₀ hY_pos).mpr (by simpa [mul_comm] using h_ih_B)
          have h_Jsec_le : J_sec ω ≤ (1 / (x_sec ω) : ℝ) := by
            exact (le_div_iff₀ hxpos).mpr (by simpa [mul_comm] using (h_ih_sec ω h_sec))
          -- combine the rpow bounds
          have h_Jpow : J_B ^ (1 - t) * (J_sec ω) ^ t ≤
              Y ^ (t - 1) * (x_sec ω) ^ (-t) := by
            have h1a : J_B ^ (1 - t) ≤ (1 / Y) ^ (1 - t) := by
              exact Real.rpow_le_rpow hJ_B_nonneg h_JB_le h1mt
            have h1b : (1 / Y) ^ (1 - t) = Y ^ (t - 1) := by
              calc
                (1 / Y) ^ (1 - t) = Y⁻¹ ^ (1 - t) := by rw [one_div]
                _ = (Y ^ (-1 : ℝ)) ^ (1 - t) := by rw [← Real.rpow_neg_one]
                _ = Y ^ ((-1 : ℝ) * (1 - t)) := by
                  rw [← Real.rpow_mul (le_of_lt hY_pos)]
                _ = Y ^ (t - 1) := by congr 1; ring
            have h1 : J_B ^ (1 - t) ≤ Y ^ (t - 1) := by
              rw [← h1b]
              exact h1a
            have h2a : (J_sec ω) ^ t ≤ (1 / (x_sec ω)) ^ t := by
              exact Real.rpow_le_rpow (hJ_sec_nonneg ω) h_Jsec_le ht0
            have h2b : (1 / (x_sec ω)) ^ t = (x_sec ω) ^ (-t) := by
              calc
                (1 / (x_sec ω)) ^ t = (x_sec ω)⁻¹ ^ t := by rw [one_div]
                _ = ((x_sec ω) ^ (-1 : ℝ)) ^ t := by rw [← Real.rpow_neg_one]
                _ = (x_sec ω) ^ ((-1 : ℝ) * t) := by
                  rw [← Real.rpow_mul (le_of_lt hxpos)]
                _ = (x_sec ω) ^ (-t) := by congr 1; ring
            have h2 : (J_sec ω) ^ t ≤ (x_sec ω) ^ (-t) := by
              rw [← h2b]
              exact h2a
            have hposJ : 0 ≤ J_B ^ (1 - t) := Real.rpow_nonneg hJ_B_nonneg _
            have hposY : 0 ≤ Y ^ (t - 1) := Real.rpow_nonneg (le_of_lt hY_pos) _
            have hposSec : 0 ≤ (J_sec ω) ^ t := Real.rpow_nonneg (hJ_sec_nonneg ω) _
            exact mul_le_mul h1 h2 hposSec hposY
          have h_combined : Real.exp ((1 - t)^2 / 4) *
              (J_B ^ (1 - t) * (J_sec ω) ^ t) ≤
              Real.exp ((1 - t)^2 / 4) * (Y ^ (t - 1) * (x_sec ω) ^ (-t)) := by
            exact mul_le_mul_of_nonneg_left h_Jpow
              (le_of_lt (Real.exp_pos ((1 - t)^2 / 4)))
          have h_main :
              I ω ≤ Real.exp ((1 - t)^2 / 4) * (Y ^ (t - 1) * (x_sec ω) ^ (-t)) := by
            calc
              I ω ≤ Real.exp ((1 - t)^2 / 4) *
                  (∫ x : Ω_prefix, (fB x) ^ (1 - t) * (fSec x) ^ t ∂P) := h_int_le
              _ ≤ Real.exp ((1 - t)^2 / 4) *
                  ((∫ x : Ω_prefix, fB x ∂P) ^ (1 - t) *
                    (∫ x : Ω_prefix, fSec x ∂P) ^ t) := by
                exact mul_le_mul_of_nonneg_left h_holder
                  (le_of_lt (Real.exp_pos ((1 - t)^2 / 4)))
              _ = Real.exp ((1 - t)^2 / 4) * (J_B ^ (1 - t) * (J_sec ω) ^ t) := by
                simp [fB, fSec, J_B, J_sec]
              _ ≤ Real.exp ((1 - t)^2 / 4) * (Y ^ (t - 1) * (x_sec ω) ^ (-t)) := h_combined
          simpa [mul_assoc] using h_main

        -- Per-ω bound when the section has mass zero (universal t=0 bound)
        have hI_zero : ∀ ω : Ω_last, x_sec ω = 0 → I ω ≤ Real.exp (1/4) / Y := by
          intro ω hx0
          have h_JB_le : J_B ≤ (1 / Y : ℝ) := by
            exact (le_div_iff₀ hY_pos).mpr (by simpa [mul_comm] using h_ih_B)
          calc
            I ω = ∫ x : Ω_prefix, f (Fin.snoc x ω) ∂P := rfl
            _ ≤ ∫ x : Ω_prefix, Real.exp (1/4) * Real.exp ((convexDistance x B) ^ 2 / 4) ∂P := by
              refine integral_mono (Integrable.of_finite) (Integrable.of_finite) (fun x => ?_)
              dsimp [f, B]
              exact (scalar_optimization_two_valued x ω A).1
            _ = Real.exp (1/4) * J_B := by
              simp [J_B, integral_const_mul]
            _ ≤ Real.exp (1/4) * (1 / Y) := by
              exact mul_le_mul_of_nonneg_left h_JB_le (le_of_lt (Real.exp_pos (1/4)))
            _ = Real.exp (1/4) / Y := by ring

        -- Final algebraic assembly (60.8)
        calc
          S * (∑ ω : Ω_last, q ω * I ω)
              = (∑ ω : Ω_last, q ω * x_sec ω) * (∑ ω : Ω_last, q ω * I ω) := by
            rw [hS_eq_sum]
          _ ≤ 1 := talagrand_algebraic_assembly (ι := Ω_last) q x_sec I Y
              hY_pos hq_nonneg hq_sum hx_sec_nonneg hx_sec_le_Y hI_pos hI_zero

    -- Final assembly
    calc
      (Measure.pi μ A).toReal * (∫ x : ((i : Fin (n+1)) → Ω i), f x ∂(Measure.pi μ))
          = S * (∑ ω : Ω_last, q ω * I ω) := by rw [h_integral]
      _ ≤ 1 := h_total_bound

/-!
# Talagrand Convex Distance: Tail Corollaries (Blueprint Items 80.1, 80.5, 80.10, 80.15, 80.16, 80.20, 80.25)

## Main theorem

`talagrand_convexDistance` (Item 60.10):

  `μ(A) · ∫ exp(d_A(x)² / 4) dμ(x) ≤ 1`

## Tail corollaries

* `talagrand_convexDistance_tail` (Item 80.1) — Markov tail bound
  `μ(A) · μ({x : d_A(x) ≥ t}) ≤ exp(-t²/4)`.
* `talagrand_convexDistance_tail_half` (Item 80.5) — when `μ(A) ≥ 1/2`
  `μ({x : d_A(x) ≥ t}) ≤ 2 exp(-t²/4)`.
* `talagrand_convexDistance_tail_neg` (Item 80.10) — complement form: apply 80.5 to `Aᶜ`.
* `talagrand_convexDistance_two_sided` (Item 80.25; restructured from 80.16) —
  pair of independent implications: `μ(A) ≥ 1/2` yields the `d_A` tail bound and
  `μ(Aᶜ) ≥ 1/2` yields the `d_{Aᶜ}` tail bound, with nonemptiness derived from
  the antecedents (no explicit `hA`/`hAc` hypotheses); both antecedents together
  force `μ(A) = μ(Aᶜ) = 1/2`.
* `talagrand_convexDistance_integral_le_one_div` (Item 80.20) — conditional form
  `∫ exp(d_A²/4) dμ ≤ 1 / μ(A)` under `0 < μ(A)`.
-/

/-- **Talagrand tail bound** (Blueprint Item 80.1).

Under the hypotheses of the main theorem, for any `t ≥ 0`:

  `μ(A) · μ({x | d_A(x) ≥ t}) ≤ exp(-t²/4)`.

Proof (Markov / exponential Chebyshev): on `{x | t ≤ d_A(x)}` we have
`exp(t²/4) ≤ exp(d_A(x)²/4)` (exp is monotone and `t, d_A(x) ≥ 0`). Multiplying by
the indicator and integrating gives `exp(t²/4) · μ({d_A ≥ t}) ≤ ∫ exp(d_A²/4) dμ`,
and the main theorem `talagrand_convexDistance` gives `μ(A) · ∫ exp(d_A²/4) dμ ≤ 1`.
Dividing by `exp(t²/4) > 0` yields the claim. -/
theorem talagrand_convexDistance_tail {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    [∀ i, DecidableEq (Ω i)]
    {μ : (i : Fin n) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin n) → Ω i)) (hA : A.Nonempty) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ A).toReal * (Measure.pi μ {x | t ≤ convexDistance x A}).toReal ≤
      Real.exp (-(t ^ 2) / 4) := by
  let ν := Measure.pi μ
  let B := {x : (i : Fin n) → Ω i | t ≤ convexDistance x A}
  have h_main := talagrand_convexDistance (μ := μ) A hA
  have h_exp_pos : 0 < Real.exp (t ^ 2 / 4) := Real.exp_pos _
  -- Pointwise bound on B: exp(t²/4) ≤ exp(d_A(x)²/4)
  have h_pointwise (x : (i : Fin n) → Ω i) (hx : x ∈ B) :
      Real.exp (t ^ 2 / 4) ≤ Real.exp ((convexDistance x A) ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    dsimp [B] at hx
    have hsq : t ^ 2 ≤ (convexDistance x A) ^ 2 := by
      rw [sq_le_sq]
      rwa [abs_of_nonneg ht, abs_of_nonneg (convexDistance_nonneg x A)]
    nlinarith
  -- Markov step: exp(t²/4) · ν B ≤ ∫ exp(d_A²/4) dν
  have h_int_le : Real.exp (t ^ 2 / 4) * (ν B).toReal ≤
      ∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂ν := by
    calc
      Real.exp (t ^ 2 / 4) * (ν B).toReal
          = ∫ x, (B.indicator (fun _ => Real.exp (t ^ 2 / 4))) x ∂ν := by
        rw [integral_indicator_const (Real.exp (t ^ 2 / 4)) (Set.toFinite B).measurableSet]
        simp [measureReal_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂ν := by
        refine integral_mono (Integrable.of_finite) (Integrable.of_finite) (fun x => ?_)
        by_cases hx : x ∈ B
        · rw [Set.indicator_of_mem hx]
          exact h_pointwise x hx
        · rw [Set.indicator_of_notMem hx]
          exact le_of_lt (Real.exp_pos ((convexDistance x A) ^ 2 / 4))
  -- Combine with the main theorem
  have h_prod : (Measure.pi μ A).toReal * (ν B).toReal * Real.exp (t ^ 2 / 4) ≤ 1 := by
    calc
      (Measure.pi μ A).toReal * (ν B).toReal * Real.exp (t ^ 2 / 4)
          = (Measure.pi μ A).toReal * (Real.exp (t ^ 2 / 4) * (ν B).toReal) := by ring
      _ ≤ (Measure.pi μ A).toReal *
          (∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂ν) := by
        exact mul_le_mul_of_nonneg_left h_int_le ENNReal.toReal_nonneg
      _ ≤ 1 := by simpa [ν] using h_main
  -- Divide by exp(t²/4) > 0
  have h_div : (Measure.pi μ A).toReal * (ν B).toReal ≤
      1 / Real.exp (t ^ 2 / 4) := (le_div_iff₀ h_exp_pos).mpr (by simpa [mul_assoc] using h_prod)
  calc
    (Measure.pi μ A).toReal * (Measure.pi μ {x | t ≤ convexDistance x A}).toReal
        ≤ 1 / Real.exp (t ^ 2 / 4) := by simpa [ν, B] using h_div
    _ = Real.exp (-(t ^ 2) / 4) := by
      rw [neg_div, Real.exp_neg, one_div]

/-- **Talagrand tail bound, half-measure form** (Blueprint Item 80.5).

When `μ(A) ≥ 1/2`, the tail bound simplifies to:

  `μ({x | d_A(x) ≥ t}) ≤ 2 exp(-t²/4)`.

Proof: from `talagrand_convexDistance_tail` (Item 80.1),
`μ(A) · μ({d_A ≥ t}) ≤ exp(-t²/4)`. Since `μ(A) ≥ 1/2 > 0`:

  `μ({d_A ≥ t}) ≤ μ({d_A ≥ t}) · (2 μ(A)) = 2 (μ(A) · μ({d_A ≥ t})) ≤ 2 exp(-t²/4)`. -/
theorem talagrand_convexDistance_tail_half {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    [∀ i, DecidableEq (Ω i)]
    {μ : (i : Fin n) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin n) → Ω i)) (hA : A.Nonempty)
    (h_half : 1 / 2 ≤ (Measure.pi μ A).toReal) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ {x | t ≤ convexDistance x A}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
  let pA := (Measure.pi μ A).toReal
  let pB := (Measure.pi μ {x | t ≤ convexDistance x A}).toReal
  have h_tail := talagrand_convexDistance_tail (μ := μ) A hA ht
  have h_two_pA : 1 ≤ 2 * pA := by nlinarith [h_half]
  have h_pB_nonneg : 0 ≤ pB := ENNReal.toReal_nonneg
  calc
    pB ≤ pB * (2 * pA) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left h_two_pA h_pB_nonneg
    _ = 2 * (pA * pB) := by ring
    _ ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
      exact mul_le_mul_of_nonneg_left (by simpa [pA, pB, mul_comm] using h_tail) (by norm_num)

/-- **Talagrand tail bound, complement form** (Blueprint Item 80.10).

Apply `talagrand_convexDistance_tail_half` (Item 80.5) to the complement set `Aᶜ`:

when `μ(Aᶜ) ≥ 1/2`:

  `μ({x | d_{Aᶜ}(x) ≥ t}) ≤ 2 exp(-t²/4)`.

(The un-simplified complement form `μ(Aᶜ) · μ({d_{Aᶜ} ≥ t}) ≤ exp(-t²/4)` follows
directly from `talagrand_convexDistance_tail` (Item 80.1) applied to `Aᶜ`.) -/
theorem talagrand_convexDistance_tail_neg {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    [∀ i, DecidableEq (Ω i)]
    {μ : (i : Fin n) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin n) → Ω i)) (hAc : Aᶜ.Nonempty)
    (h_half : 1 / 2 ≤ (Measure.pi μ Aᶜ).toReal) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi μ {x | t ≤ convexDistance x Aᶜ}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
  exact talagrand_convexDistance_tail_half (μ := μ) Aᶜ hAc h_half ht

/-- **Talagrand integral bound** (Blueprint Item 80.20).

Under the hypotheses of the main theorem, if `0 < μ(A)`:

  `∫_Ω exp(d_A(x)² / 4) dμ(x) ≤ 1 / μ(A)`.

This is the correct conditional form of the "`1 / μ(A)`" equivalence claimed in
the main theorem's docstring: without the positivity
condition the claim is false, since in Lean's reals `1 / 0 = 0` and the integral
is not `≤ 0` in general. Proof: the main theorem `talagrand_convexDistance`
(Item 60.10) gives `μ(A) · ∫ exp(d_A²/4) dμ ≤ 1`; dividing by `μ(A) > 0` via
`le_div_iff₀` yields the claim. -/
theorem talagrand_convexDistance_integral_le_one_div {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    [∀ i, DecidableEq (Ω i)]
    {μ : (i : Fin n) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin n) → Ω i)) (hA : A.Nonempty)
    (hμ : 0 < (Measure.pi μ A).toReal) :
    ∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ) ≤ 1 / (Measure.pi μ A).toReal := by
  exact (le_div_iff₀ hμ).2 (by simpa [mul_comm] using talagrand_convexDistance (μ := μ) A hA)

/-- **Talagrand two-sided tail bound** (Blueprint Item 80.25; restructured from 80.16).

Each side is an independent implication:

  `1/2 ≤ μ(A)` implies `μ({x | d_A(x) ≥ t}) ≤ 2 exp(-t²/4)`, and
  `1/2 ≤ μ(Aᶜ)` implies `μ({x | d_{Aᶜ}(x) ≥ t}) ≤ 2 exp(-t²/4)`.

The explicit nonemptiness hypotheses of Item 80.16 are not needed here: each
antecedent forces nonemptiness by contradiction, since an empty set has
measure `0`, contradicting `1/2 ≤ μ(∅).toReal`.

If both antecedents hold, then `μ(A) = μ(Aᶜ) = 1/2` (a "balanced" set), since
`μ(A) + μ(Aᶜ) = 1`.

A genuine median-based two-sided concentration theorem
`P(|f - med f| ≥ s) ≤ 4 exp(-s²/(4L²))` additionally requires a hypothesis
relating deviations of `f` from its median to the convex distance from the
lower/upper median sets (e.g. `f(x) ≥ m + s ⟹ d_{A₋}(x) ≥ s/L` for
`A₋ = {f ≤ m}`, and analogously for `A₊ = {f ≥ m}`); it does NOT follow from
the two set implications alone. Only in the case `L = 1` does this give
`4 exp(-s²/4)`. This is reserved as future work. -/
theorem talagrand_convexDistance_two_sided {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    [∀ i, DecidableEq (Ω i)]
    {μ : (i : Fin n) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin n) → Ω i)) {t : ℝ} (ht : 0 ≤ t) :
    (1 / 2 ≤ (Measure.pi μ A).toReal →
      (Measure.pi μ {x | t ≤ convexDistance x A}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4))
    ∧
    (1 / 2 ≤ (Measure.pi μ Aᶜ).toReal →
      (Measure.pi μ {x | t ≤ convexDistance x Aᶜ}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4)) := by
  exact ⟨fun hh =>
    let hA' : A.Nonempty := by
      by_contra hne
      have hAeq : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hμ : (Measure.pi μ A).toReal = 0 := by simp [hAeq]
      nlinarith
    talagrand_convexDistance_tail_half (μ := μ) A hA' hh ht,
    fun hh =>
    let hAc' : Aᶜ.Nonempty := by
      by_contra hne
      have hAeq : Aᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hμ : (Measure.pi μ Aᶜ).toReal = 0 := by simp [hAeq]
      nlinarith
    talagrand_convexDistance_tail_neg (μ := μ) A hAc' hh ht⟩

/-! # Classical Dual Form (Blueprint Items 90.2, 90.3, 90.5) -/

section ClassicalDualForm

local notation "⟪" x ", " y "⟫_ℝ" => inner ℝ x y

/-- The dot product `w ⬝ᵥ x` equals the real inner product `⟪x, w⟫`. -/
private lemma dot_eq_inner {n : ℕ} (w x : EuclideanSpace ℝ (Fin n)) :
    w ⬝ᵥ x = ⟪x, w⟫_ℝ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- Linearity of the inner product `⟪·, w⟫` through a finite convex combination. -/
private lemma inner_sum_smul {n : ℕ} {ι : Type*} [Fintype ι] (w : EuclideanSpace ℝ (Fin n))
    (a : ι → ℝ) (z : ι → EuclideanSpace ℝ (Fin n)) :
    ⟪∑ i, a i • z i, w⟫_ℝ = ∑ i, a i * ⟪z i, w⟫_ℝ := by
  calc
    ⟪∑ i, a i • z i, w⟫_ℝ = ∑ i, ⟪a i • z i, w⟫_ℝ := by
      simpa using sum_inner Finset.univ (fun i => a i • z i) w
    _ = ∑ i, a i * ⟪z i, w⟫_ℝ := by
      simp_rw [inner_smul_left]
      simp

/-- Blueprint 90.2(a): the convex hull of the finite set of mismatch vectors is compact. -/
theorem convexMismatchSet_isCompact {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    [∀ i, Fintype (Ω i)] (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) :
    IsCompact (convexMismatchSet x A) := by
  unfold convexMismatchSet
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ)
    (Set.Finite.image (mismatchVector x) (Set.Finite.subset Set.finite_univ A.subset_univ))

/-- Blueprint 90.2(a'): in particular the set is closed. -/
theorem convexMismatchSet_isClosed {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    [∀ i, Fintype (Ω i)] (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) :
    IsClosed (convexMismatchSet x A) :=
  (convexMismatchSet_isCompact x A).isClosed

/-- Blueprint 90.2(b): a compact nonempty set contains a point of minimal norm
attaining `Metric.infDist 0 K`. -/
theorem exists_norm_eq_infDist_zero {E : Type*} [NormedAddCommGroup E] (K : Set E)
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ z ∈ K, ‖z‖ = Metric.infDist (0 : E) K := by
  rcases hK.exists_infDist_eq_dist hne (0 : E) with ⟨z, hzK, hz⟩
  refine ⟨z, hzK, ?_⟩
  rw [hz, dist_zero_left]

/-- Blueprint 90.2(c): the variational inequality for the nearest point to `0` in a
closed (convex) set. -/
theorem variational_inequality_nearest_point {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (K : Set E) (hKconv : Convex ℝ K) (z : E) (hz : z ∈ K)
    (hzmin : ∀ u ∈ K, ‖z‖ ≤ ‖u‖) :
    ∀ u ∈ K, 0 ≤ inner ℝ z (u - z) := by
  intro u hu
  -- For every t ∈ (0, 1], `z + t • (u - z) ∈ K` by convexity, so `‖z‖ ≤ ‖z + t • (u - z)‖`;
  -- expanding the squared norms gives `0 ≤ 2⟪z, u - z⟫ + t ‖u - z‖²`.
  have hstep (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
      0 ≤ 2 * inner ℝ z (u - z) + t * ‖u - z‖ ^ 2 := by
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht0, ht1⟩
    have hmem : z + t • (u - z) ∈ K := Convex.add_smul_sub_mem hKconv hz hu ht
    have hle : ‖z‖ ≤ ‖z + t • (u - z)‖ := hzmin (z + t • (u - z)) hmem
    have hsq : ‖z‖ ^ 2 ≤ ‖z + t • (u - z)‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z + t • (u - z)))).mpr hle
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul_of_nonneg (le_of_lt ht0)] at hsq
    have hmul : 0 ≤ t * (2 * inner ℝ z (u - z) + t * ‖u - z‖ ^ 2) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul ht0
  -- Take the sequence t_k = 1 / (k + 1) → 0 and pass to the limit.
  have hlim : Filter.Tendsto
      (fun k : ℕ => 2 * inner ℝ z (u - z) + (1 / ((k : ℝ) + 1)) * ‖u - z‖ ^ 2)
      Filter.atTop (nhds (2 * inner ℝ z (u - z))) := by
    simpa using (tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖u - z‖ ^ 2)))
  have hge : 0 ≤ 2 * inner ℝ z (u - z) := by
    refine ge_of_tendsto hlim ?_
    refine Filter.mem_of_superset (Filter.univ_mem : (Set.univ : Set ℕ) ∈ Filter.atTop) ?_
    intro k hk
    have hk' : (0 : ℝ) ≤ k := by positivity
    exact hstep (1 / ((k : ℝ) + 1)) (by positivity)
      ((div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr (by linarith))
  exact nonneg_of_mul_nonneg_right hge (by positivity)

/-- Blueprint 90.2(d): the mismatch set lies in the nonnegative orthant. -/
theorem convexMismatchSet_subset_nonneg {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) :
    convexMismatchSet x A ⊆ {v : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ v i} := by
  unfold convexMismatchSet
  apply convexHull_min
  · -- every generator has {0,1}-valued coordinates, hence nonnegative coordinates
    intro v hv
    rcases hv with ⟨y, hy, rfl⟩
    intro i
    by_cases h : x i = y i <;> simp [h]
  · -- the orthant is convex (direct check)
    intro x hx y hy a b ha hb hab i
    have hi : (a • x + b • y) i = a * x i + b * y i := by simp
    rw [hi]
    nlinarith [mul_nonneg ha (hx i), mul_nonneg hb (hy i)]

/-- Blueprint 90.2: the nearest-point package for `K = convexMismatchSet x A`. -/
theorem convexMismatchSet_nearest_point {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    [∀ i, Fintype (Ω i)] (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) (hA : A.Nonempty) :
    ∃ z ∈ convexMismatchSet x A,
      ‖z‖ = Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (convexMismatchSet x A) ∧
      (∀ u ∈ convexMismatchSet x A, 0 ≤ z ⬝ᵥ (u - z)) ∧ ∀ i, 0 ≤ z i := by
  let K := convexMismatchSet x A
  have hK : IsCompact K := by
    simpa [K] using convexMismatchSet_isCompact (Ω := Ω) x A
  have hne : K.Nonempty := by
    rcases hA with ⟨y, hy⟩
    refine ⟨mismatchVector x y, ?_⟩
    dsimp [K, convexMismatchSet]
    exact subset_convexHull ℝ (mismatchVector x '' A) ⟨y, hy, rfl⟩
  have hKconv : Convex ℝ K := by
    dsimp [K, convexMismatchSet]
    exact convex_convexHull ℝ (mismatchVector x '' A)
  rcases exists_norm_eq_infDist_zero K hK hne with ⟨z, hzK, hznorm⟩
  have hzmin : ∀ u ∈ K, ‖z‖ ≤ ‖u‖ := by
    intro u hu
    have hle : Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) K ≤ ‖u‖ := by
      calc
        Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) K ≤
            dist (0 : EuclideanSpace ℝ (Fin n)) u := Metric.infDist_le_dist_of_mem hu
        _ = ‖u‖ := by rw [dist_zero_left]
    rw [hznorm]
    exact hle
  have hzv : ∀ u ∈ K, 0 ≤ inner ℝ z (u - z) :=
    variational_inequality_nearest_point K hKconv z hzK hzmin
  refine ⟨z, hzK, hznorm, ?_, ?_⟩
  · -- variational inequality, converted from the inner product to the dot product
    intro u hu
    have h : 0 ≤ inner ℝ z (u - z) := hzv u hu
    rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa using h
  · -- coordinatewise nonnegativity
    exact convexMismatchSet_subset_nonneg x A hzK

/-- The dot product of two coordinatewise nonnegative vectors is nonnegative. -/
private lemma dot_nonneg {n : ℕ} {w v : EuclideanSpace ℝ (Fin n)} (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, 0 ≤ v i) :
    0 ≤ w ⬝ᵥ v := by
  calc
    0 ≤ ∑ i : Fin n, w i * v i := by
      refine Finset.sum_nonneg ?_
      intro i _
      exact mul_nonneg (hw i) (hv i)
    _ = w ⬝ᵥ v := by
      rfl

/-- Blueprint 90.3 / 90.5 helper: the core convex-combination bound, with a
subtype-iInf LHS instead of the degenerate set-membership form (no `sInf ∅ = 0`
fallback). It is the per-hull-point step used by the (≥) direction of the refactored
`iInf_inner_convexHull` (Item 90.5) and by `convexDistance_eq_dual` (Item 90.3).

If `w` is coordinatewise nonnegative and `M` lies in the nonnegative orthant, then for
any `z` in the convex hull of `M` the infimum of `w ⬝ᵥ ·` over `M` is at most `w ⬝ᵥ z`.

Note: unlike the blueprint's sketch, no `M.Nonempty` hypothesis is needed — the
`BddBelow`-by-`0` argument holds without it (and the linter would flag the binder as
unused). -/
theorem iInf_subtype_dot_le_of_mem_convexHull {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (hMnn : M ⊆ {v | ∀ i, 0 ≤ v i}) (hw : ∀ i, 0 ≤ w i) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ convexHull ℝ M) :
    (⨅ v : M, w ⬝ᵥ v.1) ≤ w ⬝ᵥ z := by
  rcases (mem_convexHull_iff_exists_fintype (R := ℝ) (E := EuclideanSpace ℝ (Fin n))
      (s := M) (x := z)).mp hz with ⟨ι, _hι, a, z', ha₀, ha₁, hz', hz_eq⟩
  have hB : BddBelow (Set.range (fun v : M => w ⬝ᵥ v.1)) := by
    refine ⟨0, ?_⟩
    intro b hb
    rcases hb with ⟨v, rfl⟩
    exact dot_nonneg hw (fun i => hMnn v.2 i)
  calc
    (⨅ v : M, w ⬝ᵥ v.1) = (∑ i, a i) * (⨅ v : M, w ⬝ᵥ v.1) := by rw [ha₁, one_mul]
    _ = ∑ i, a i * (⨅ v : M, w ⬝ᵥ v.1) := by rw [Finset.sum_mul]
    _ ≤ ∑ i, a i * (w ⬝ᵥ z' i) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_left (ciInf_le hB ⟨z' i, hz' i⟩) (ha₀ i)
    _ = ⟪∑ i, a i • z' i, w⟫_ℝ := by
      calc
        ∑ i, a i * (w ⬝ᵥ z' i) = ∑ i, a i * ⟪z' i, w⟫_ℝ := by
          simp_rw [dot_eq_inner w]
        _ = ⟪∑ i, a i • z' i, w⟫_ℝ := by rw [← inner_sum_smul w a z']
    _ = w ⬝ᵥ z := by
      rw [hz_eq]
      exact (dot_eq_inner w z).symm

/-- **Blueprint Items 90.1 / 90.5** (GPT-v2 refactor): taking the convex hull does
not change the infimum of the linear functional `w ⬝ᵥ ·`, in the *subtype* form:

  `(⨅ z : convexHull ℝ M, w ⬝ᵥ z.1) = ⨅ v : M, w ⬝ᵥ v.1`

for `w : EuclideanSpace ℝ (Fin n)` coordinatewise nonnegative and nonempty
`M ⊆ {v | ∀ i, 0 ≤ v i}`. This replaces the degenerate set-membership form
`(⨅ z ∈ convexHull ℝ M, w ⬝ᵥ z) = ⨅ v ∈ M, w ⬝ᵥ v` of the original Item 90.1: on ℝ
the latter elaborates to pointwise `iInf`s over the membership propositions, where
the inner `iInf` over a false proposition collapses to `sInf ∅ = 0`
(`Real.sInf_empty`), forcing the old proof to split on `BddBelow` and special-case
the fallback value `0`. The subtype form needs no such fallback.

The nonnegativity hypotheses (`hMnn`, `hw`) supply the `BddBelow`-by-`0` bound for
free (via `dot_nonneg`) — the general form without them would need an explicit
`BddBelow` hypothesis, as in the bounded branch of the old proof. `hM` provides the
`Nonempty` instances for both subtype `iInf`s. The (≥) direction is exactly
`iInf_subtype_dot_le_of_mem_convexHull` applied per hull point; the (≤) direction
embeds each `v ∈ M` into the hull subtype. -/
theorem iInf_inner_convexHull {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (hMnn : M ⊆ {v | ∀ i, 0 ≤ v i}) (hw : ∀ i, 0 ≤ w i) (hM : M.Nonempty) :
    (⨅ z : convexHull ℝ M, w ⬝ᵥ z.1) = (⨅ v : M, w ⬝ᵥ v.1) := by
  haveI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  haveI : Nonempty (convexHull ℝ M) :=
    ⟨⟨hM.choose, subset_convexHull ℝ M hM.choose_spec⟩⟩
  -- (≥) pointwise: the M-iInf lower-bounds every hull value (90.3 helper)
  have hp : ∀ z : convexHull ℝ M, (⨅ v : M, w ⬝ᵥ v.1) ≤ w ⬝ᵥ z.1 :=
    fun z => iInf_subtype_dot_le_of_mem_convexHull w M hMnn hw z.2
  -- hull-range BddBelow derived from hp (bound = the M-iInf)
  have hB_hull : BddBelow (Set.range (fun z : convexHull ℝ M => w ⬝ᵥ z.1)) := by
    refine ⟨⨅ v : M, w ⬝ᵥ v.1, ?_⟩
    intro b hb
    rcases hb with ⟨z, rfl⟩
    exact hp z
  refine le_antisymm ?_ ?_
  · -- (≤): each v ∈ M embeds into the hull subtype
    refine le_ciInf ?_
    intro v
    exact ciInf_le hB_hull ⟨v.1, subset_convexHull ℝ M v.2⟩
  · -- (≥): le_ciInf over the hull subtype with the pointwise bound
    refine le_ciInf hp

/-- **Blueprint Item 90.3**: the classical dual form of Talagrand's convex distance
(Pollard 2006):

  `convexDistance x A = sSup {r | ∃ w : EuclideanSpace ℝ (Fin n),
    ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧ r = ⨅ y : A, w ⬝ᵥ mismatchVector x y}`

**Statement corrections** (from the 90.2/90.3 surveys):

(i) `0 ≤ w` must be coordinatewise — `EuclideanSpace ℝ (Fin n)` has no order instance;
(ii) the theorem carries `[∀ i, Fintype (Ω i)]` (compactness of `convexMismatchSet x A`,
needed for the (≥) direction via 90.2);
(iii) the iInf must be the *subtype* form `⨅ y : A, …`, NOT the set-membership form
`⨅ y ∈ A, …`. On ℝ the latter elaborates to `⨅ y, ⨅ _ : y ∈ A, …`, and for `y ∉ A` the
inner iInf is `sInf ∅ = 0` (`Real.sInf_empty`), so with `w ⬝ᵥ v(x,y) ≥ 0` the whole
expression collapses to `0` for any proper nonempty `A` (counterexample: `n = 1`,
`A = {0} ⊊ Ω`, `x ≠ 0` gives `convexDistance x A = 1` but RHS = `sSup {0} = 0`). This
is exactly the pitfall motivating the subtype-form refactor of `iInf_inner_convexHull`
(Blueprint Item 90.5), which replaced the degenerate set-membership form and its
`sInf ∅ = 0` fallback. The subtype iInf is the true infimum over `A` and matches
`Metric.infDist_eq_iInf`'s subtype form directly.

Proof outline: let `K = convexMismatchSet x A` (so `d = convexDistance x A = infDist 0 K`
by rfl).
(≤): for admissible `w` and any `z ∈ K`,
`r ≤ w ⬝ᵥ z` via `iInf_subtype_dot_le_of_mem_convexHull`, and
`w ⬝ᵥ z ≤ ‖z‖ * ‖w‖ ≤ ‖z‖` (Cauchy–Schwarz), so `r ≤ ⨅ z : K, ‖z‖ = d`
(`le_ciInf` + `dist_zero_left` + `Metric.infDist_eq_iInf`); hence `sSup S ≤ d` via
`csSup_le` (`S.Nonempty` from the `w = 0` candidate: `zero_dotProduct` + `ciInf_const`).
(≥): the 90.2 nearest point `z ∈ K` of `0` satisfies `‖z‖ = d`, the variational
inequality `0 ≤ z ⬝ᵥ (u − z)` on `K`, and `z ≥ 0` coordinatewise. If `z = 0` then
`d = 0` and the `w = 0` candidate gives `0 ∈ S`. If `z ≠ 0`, take `w = ‖z‖⁻¹ • z`
(admissible: `‖w‖ = 1`, `w ≥ 0`); for `u = v(x,y) ∈ K` the variational inequality
gives `‖z‖² ≤ z ⬝ᵥ u`, whence `d = ‖z‖ ≤ w ⬝ᵥ u` (`smul_dotProduct` +
`‖z‖⁻¹ * ‖z‖² = ‖z‖`), so `d ≤ ⨅ y : A, w ⬝ᵥ mismatchVector x y` and `d ∈ S`; hence
`d ≤ sSup S` via `le_csSup` (BddAbove first). Close with `le_antisymm`. -/
theorem convexDistance_eq_dual {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    [∀ i, Fintype (Ω i)] (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i))
    (hA : A.Nonempty) :
    convexDistance x A = sSup {r | ∃ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧ r = ⨅ y : A, w ⬝ᵥ mismatchVector x y} := by
  let S : Set ℝ := {r | ∃ w : EuclideanSpace ℝ (Fin n),
    ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧ r = ⨅ y : A, w ⬝ᵥ mismatchVector x y}
  change convexDistance x A = sSup S
  haveI hAnon : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  haveI hMnon : Nonempty (mismatchVector x '' A) :=
    ⟨⟨mismatchVector x hA.choose, ⟨hA.choose, hA.choose_spec, rfl⟩⟩⟩
  haveI hKnon : Nonempty (convexMismatchSet x A) :=
    ⟨⟨mismatchVector x hA.choose,
      subset_convexHull ℝ (mismatchVector x '' A) ⟨hA.choose, hA.choose_spec, rfl⟩⟩⟩
  -- The (≤) direction: every element of S is bounded above by the convex distance.
  have hforall : ∀ b ∈ S, b ≤ convexDistance x A := by
    intro b hb
    dsimp [S] at hb
    rcases hb with ⟨w, hwnorm, hw, rfl⟩
    have hz_le (z : convexMismatchSet x A) :
        (⨅ y : A, w ⬝ᵥ mismatchVector x y) ≤ ‖z.1‖ := by
      have hreindex :
          (⨅ y : A, w ⬝ᵥ mismatchVector x y) ≤ ⨅ v : mismatchVector x '' A, w ⬝ᵥ v.1 := by
        refine le_ciInf ?_
        intro v
        rcases v.2 with ⟨y, hyA, hyv⟩
        have hB : BddBelow (Set.range (fun y : A => w ⬝ᵥ mismatchVector x y)) := by
          refine ⟨0, ?_⟩
          intro c hc
          rcases hc with ⟨y, rfl⟩
          exact dot_nonneg hw (fun i => by
            rw [mismatchVector_apply]
            by_cases h : x i = y.1 i <;> simp [h])
        calc
          (⨅ y : A, w ⬝ᵥ mismatchVector x y) ≤ w ⬝ᵥ mismatchVector x y := ciInf_le hB ⟨y, hyA⟩
          _ = w ⬝ᵥ v.1 := by rw [hyv]
      have hMnn : mismatchVector x '' A ⊆ {v | ∀ i, 0 ≤ v i} := by
        intro v hv
        rcases hv with ⟨y, hyA, rfl⟩
        intro i
        rw [mismatchVector_apply]
        by_cases h : x i = y i <;> simp [h]
      have hcs : w ⬝ᵥ z.1 ≤ ‖z.1‖ := by
        calc
          w ⬝ᵥ z.1 = ⟪z.1, w⟫_ℝ := dot_eq_inner w z.1
          _ ≤ ‖z.1‖ * ‖w‖ := real_inner_le_norm z.1 w
          _ ≤ ‖z.1‖ * 1 := mul_le_mul_of_nonneg_left hwnorm (norm_nonneg z.1)
          _ = ‖z.1‖ := mul_one _
      calc
        (⨅ y : A, w ⬝ᵥ mismatchVector x y) ≤ ⨅ v : mismatchVector x '' A, w ⬝ᵥ v.1 := hreindex
        _ ≤ w ⬝ᵥ z.1 :=
          iInf_subtype_dot_le_of_mem_convexHull w (mismatchVector x '' A) hMnn hw z.2
        _ ≤ ‖z.1‖ := hcs
    have hle : (⨅ y : A, w ⬝ᵥ mismatchVector x y) ≤ convexDistance x A := by
      calc
        (⨅ y : A, w ⬝ᵥ mismatchVector x y) ≤ ⨅ z : convexMismatchSet x A, ‖z.1‖ := by
          refine le_ciInf ?_
          intro z
          exact hz_le z
        _ = ⨅ z : convexMismatchSet x A, dist (0 : EuclideanSpace ℝ (Fin n)) z.1 := by
          simp_rw [dist_zero_left]
        _ = Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (convexMismatchSet x A) :=
          (Metric.infDist_eq_iInf (s := convexMismatchSet x A) (x := (0 : EuclideanSpace ℝ (Fin n)))).symm
        _ = convexDistance x A := rfl
    exact hle
  have hBdd : BddAbove S := ⟨convexDistance x A, hforall⟩
  -- The w = 0 candidate shows S is nonempty (and is the z = 0 witness below).
  have h0mem : (0 : ℝ) ∈ S := by
    dsimp [S]
    refine ⟨0, ?_, ?_, ?_⟩
    · simp
    · intro i
      simp
    · have h : (⨅ y : A, (0 : EuclideanSpace ℝ (Fin n)) ⬝ᵥ mismatchVector x y) = (0 : ℝ) := by
        simp [zero_dotProduct, ciInf_const]
      exact h.symm
  have hSne : S.Nonempty := ⟨0, h0mem⟩
  have hle_sup : sSup S ≤ convexDistance x A := csSup_le hSne hforall
  -- The (≥) direction: exhibit an admissible w with dual value ≥ the convex distance.
  have hge : convexDistance x A ≤ sSup S := by
    rcases convexMismatchSet_nearest_point x A hA with ⟨z, _hzK, hznorm, hzv, hznn⟩
    by_cases hz0 : z = 0
    · calc
        convexDistance x A = 0 := by
          change Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (convexMismatchSet x A) = 0
          rw [← hznorm, hz0, norm_zero]
        _ ≤ sSup S := le_csSup hBdd h0mem
    · let w : EuclideanSpace ℝ (Fin n) := ‖z‖⁻¹ • z
      have hwnorm : ‖w‖ = 1 := by
        change ‖‖z‖⁻¹ • z‖ = 1
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg_of_nonneg (norm_nonneg z))]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)
      have hw_le : ‖w‖ ≤ 1 := by
        rw [hwnorm]
      have hw_nn : ∀ i, 0 ≤ w i := by
        intro i
        change 0 ≤ (‖z‖⁻¹ • z) i
        rw [PiLp.smul_apply]
        exact mul_nonneg (inv_nonneg_of_nonneg (norm_nonneg z)) (hznn i)
      have hper (y : A) : ‖z‖ ≤ w ⬝ᵥ mismatchVector x y := by
        let u : EuclideanSpace ℝ (Fin n) := mismatchVector x y
        have hu : u ∈ convexMismatchSet x A := by
          dsimp [u, convexMismatchSet]
          exact subset_convexHull ℝ (mismatchVector x '' A) ⟨y.1, y.2, rfl⟩
        have hzz : z ⬝ᵥ z = ‖z‖ ^ 2 := by
          calc
            z ⬝ᵥ z = ⟪z, z⟫_ℝ := dot_eq_inner z z
            _ = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq z
        have hzu : ‖z‖ ^ 2 ≤ z ⬝ᵥ u := by
          have h1 : 0 ≤ z ⬝ᵥ (u - z) := hzv u hu
          rw [dotProduct_sub] at h1
          rw [hzz] at h1
          nlinarith
        calc
          ‖z‖ = ‖z‖⁻¹ * ‖z‖ ^ 2 := by
            rw [sq, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0), one_mul]
          _ ≤ ‖z‖⁻¹ * (z ⬝ᵥ u) :=
            mul_le_mul_of_nonneg_left hzu (inv_nonneg_of_nonneg (norm_nonneg z))
          _ = (‖z‖⁻¹ • z) ⬝ᵥ u := by
            exact (smul_dotProduct ‖z‖⁻¹ z u).symm
          _ = w ⬝ᵥ u := rfl
      have hr : ‖z‖ ≤ ⨅ y : A, w ⬝ᵥ mismatchVector x y := by
        refine le_ciInf ?_
        intro y
        exact hper y
      let r : ℝ := ⨅ y : A, w ⬝ᵥ mismatchVector x y
      have hd_le_r : convexDistance x A ≤ r := by
        dsimp [r]
        change Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (convexMismatchSet x A) ≤
          ⨅ y : A, w ⬝ᵥ mismatchVector x y
        calc
          Metric.infDist (0 : EuclideanSpace ℝ (Fin n)) (convexMismatchSet x A) = ‖z‖ := hznorm.symm
          _ ≤ ⨅ y : A, w ⬝ᵥ mismatchVector x y := hr
      have hr_mem : r ∈ S := by
        dsimp [r, S]
        refine ⟨w, hw_le, hw_nn, rfl⟩
      calc
        convexDistance x A ≤ r := hd_le_r
        _ ≤ sSup S := le_csSup hBdd hr_mem
  exact le_antisymm hge hle_sup

end ClassicalDualForm
end
end TCSLean.Talagrand
