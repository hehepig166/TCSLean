/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
import TCSLean.MoserTardos.Basic

/-!
# The symmetric form of the Moser–Tardos Lovász Local Lemma

This file proves the symmetric form of the constructive Lovász Local Lemma
(`moserTardos_symmetric`, blueprint item 70.1): if every bad event has probability at
most `p`, every event has overlap-graph degree at most `d ≥ 1`, and
`e * p * (d + 1) ≤ 1`, then some full assignment avoids every bad event, and the
expected number of resamplings is at most `card ι / d` (`moserTardos_symmetric_total`,
notes Cor 20.1 / arXiv Thm 1.3). The proof instantiates `moserTardos_exists` (60.5)
with the constant Moser–Tardos vector `x i = 1 / (d + 1)`, discharging its LLL
condition from the symmetric bound `p ≤ (1 / (d + 1)) * (d / (d + 1)) ^ d`.

## Main results

* `moserTardos_symmetric`: the symmetric form — under `hp`, `hd`, `hd1` and `hcond`
  above, there exists an assignment `σ : Π j, Ω j` avoiding every bad event `A i`.
* `moserTardos_symmetric_total`: the quantitative symmetric form — the expected number
  of resamplings is at most `card ι / d`.
-/

set_option autoImplicit false
set_option pp.unicode.fun true

-- The `noncomputable section` is load-bearing: the pick-free wrapper
-- `moserTardos_symmetric` instantiates `pick := fun S => Classical.choose S.2` (the
-- conclusion is tie-breaking-independent, but exhibiting it still uses classical
-- choice), and `moserTardos_symmetric_total`/`symmetric_hLLL` reason `classical`-ly.
noncomputable section

namespace TCSLean.MoserTardos

universe u v

open scoped BigOperators
open MeasureTheory
open scoped ENNReal

/-! ## The symmetric form (70.1) -/

section Symmetric

variable {ι : Type u} [instDecidableEqι : DecidableEq ι] [instInhabitedι : Inhabited ι]
  [Fintype ι]
variable {κ : Type u} [DecidableEq κ] [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hA : ∀ i, MeasurableSet (A i))
variable (hdet : ∀ i, DeterminedBy (A i) (vbl i))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

omit instInhabitedι in
/-- The LLL condition for the constant Moser–Tardos vector `x i = 1 / (d + 1)`: the
symmetric bound `e * p * (d + 1) ≤ 1` implies `μπ μ (A i) ≤ ofReal (x' i)` for every
`i`, via `p ≤ 1 / (e * (d + 1)) ≤ (1 / (d + 1)) * (d / (d + 1)) ^ d ≤
x i * ∏_{j ∈ Γ(i)} (1 - x j)` (the non-strict version of the symmetric bound). -/
private lemma symmetric_hLLL (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j))
    {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal p)
    (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∀ i, μπ μ (A i) ≤ ENNReal.ofReal (x' vbl (fun _ => ((d : ℝ) + 1)⁻¹) i) := by
  classical
  intro i
  let x : ι → ℝ := fun _ => ((d : ℝ) + 1)⁻¹
  change μπ μ (A i) ≤ ENNReal.ofReal
    (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j))
  have hchain : p ≤ x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j) := by
    have hstep1 : p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by
      rw [le_div_iff₀ (mul_pos (Real.exp_pos 1) (by positivity))]
      nlinarith [hcond]
    have hd0 : (d : ℝ) ≠ 0 := by
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
      exact ne_of_gt hdpos
    have hdeq : (d : ℝ) / ((d : ℝ) + 1) = 1 / (1 + (d : ℝ)⁻¹) := by
      field_simp [hd0]
    have hbase : 0 < 1 + (d : ℝ)⁻¹ := by positivity
    have hstep2 : 1 / (Real.exp 1 * ((d : ℝ) + 1)) ≤
        ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^ d := by
      have hrecip : 1 / Real.exp 1 ≤ ((d : ℝ) / ((d : ℝ) + 1)) ^ d := by
        calc
          1 / Real.exp 1 ≤ 1 / (1 + (d : ℝ)⁻¹) ^ d :=
            one_div_le_one_div_of_le (pow_pos hbase d)
              (Real.one_add_inv_pow_le_exp (n := d))
          _ = ((d : ℝ) / ((d : ℝ) + 1)) ^ d := by
            rw [← one_div_pow, hdeq]
      calc
        1 / (Real.exp 1 * ((d : ℝ) + 1)) = ((d : ℝ) + 1)⁻¹ * (1 / Real.exp 1) := by
          rw [← one_div_mul_one_div]
          ring
        _ ≤ ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^ d :=
          mul_le_mul_of_nonneg_left hrecip (inv_nonneg.mpr (by positivity))
    have hstep3 : ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^ d ≤
        x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j) := by
      have hbase0 : 0 ≤ (d : ℝ) / ((d : ℝ) + 1) := by positivity
      have hbase1 : (d : ℝ) / ((d : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have hpow : ((d : ℝ) / ((d : ℝ) + 1)) ^ d ≤
          ((d : ℝ) / ((d : ℝ) + 1)) ^ ((overlapGraph vbl).neighborFinset i).card :=
        pow_le_pow_of_le_one hbase0 hbase1 (by simpa using (hd i))
      have hmul : ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^ d ≤
          ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^
            ((overlapGraph vbl).neighborFinset i).card :=
        mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr (by positivity))
      have hsub : 1 - ((d : ℝ) + 1)⁻¹ = (d : ℝ) / ((d : ℝ) + 1) := by
        field_simp
        ring
      calc
        ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^ d
            ≤ ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^
              ((overlapGraph vbl).neighborFinset i).card := hmul
        _ = x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j) := by
          change ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^
              ((overlapGraph vbl).neighborFinset i).card =
            ((d : ℝ) + 1)⁻¹ * ∏ j ∈ (overlapGraph vbl).neighborFinset i,
              (1 - ((d : ℝ) + 1)⁻¹)
          rw [Finset.prod_const, hsub]
    calc
      p ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := hstep1
      _ ≤ ((d : ℝ) + 1)⁻¹ * ((d : ℝ) / ((d : ℝ) + 1)) ^ d := hstep2
      _ ≤ x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j) := hstep3
  exact (hp i).trans (ENNReal.ofReal_le_ofReal hchain)

omit instInhabitedι in
/-- The symmetric form of the constructive Lovász Local Lemma, pick-carrying variant:
if every bad event has probability at most `p`, every event has overlap-graph degree at
most `d ≥ 1`, and `e * p * (d + 1) ≤ 1`, then some full assignment avoids every bad
event. The Moser–Tardos vector is the constant vector `1 / (d + 1)`. (No `[Inhabited ι]`
carried: the route ends at the inhabitant-free `moserTardos_exists`.) -/
private lemma moserTardos_symmetric_pick (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal p)
    (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1)
    (pick : {S : Set ι // S.Nonempty} → ι) (_hpick : ∀ S, pick S ∈ S.1) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i := by
  classical
  let x : ι → ℝ := fun _ => ((d : ℝ) + 1)⁻¹
  have hx₀ : ∀ i, 0 ≤ x i := by
    intro i
    exact inv_nonneg.mpr (by positivity)
  have hx₁ : ∀ i, x i < 1 := by
    intro i
    exact inv_lt_one_of_one_lt₀ (by
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
      linarith)
  have hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)) := by
    intro i
    simpa [x, x'] using symmetric_hLLL Ω μ vbl A hp hd hd1 hcond i
  exact moserTardos_exists Ω μ vbl A hA hdet x hx₀ hx₁ hLLL

omit instInhabitedι in
/-- The symmetric form of the constructive Lovász Local Lemma: if every bad event has
probability at most `p`, every event has overlap-graph degree at most `d ≥ 1`, and
`e * p * (d + 1) ≤ 1`, then some full assignment avoids every bad event. The
Moser–Tardos vector is the constant vector `1 / (d + 1)`. The conclusion is
tie-breaking-independent, so no `pick`/`hpick` choice function is required.

No `[Inhabited ι]` is required: the nonempty case instantiates the (inhabitant-free)
`moserTardos_symmetric_pick` with `Classical.choose`, and at empty `ι` the conclusion
is vacuous (`∀ i, σ ∉ A i` holds for any `σ`), with `σ` built from the nonemptiness of
each `Ω j` (`μ j` is a probability measure, so `μ j Set.univ = 1 > 0`). -/
theorem moserTardos_symmetric (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal p)
    (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i := by
  classical
  by_cases hι : Nonempty ι
  · exact moserTardos_symmetric_pick Ω μ vbl A hA hdet hp hd hd1 hcond
      (fun S => Classical.choose S.2) (fun S => Classical.choose_spec S.2)
  · have hΩ : ∀ j, Nonempty (Ω j) := by
      intro j
      have h1 : (μ j) Set.univ = 1 :=
        (show IsProbabilityMeasure (μ j) from inferInstance).measure_univ
      have huniv : (Set.univ : Set (Ω j)).Nonempty :=
        nonempty_of_measure_ne_zero (μ := μ j) (s := Set.univ) (by simp [h1])
      exact Nonempty.intro (Classical.choose huniv)
    refine ⟨fun j => Classical.choice (hΩ j), fun i => (hι ⟨i⟩).elim⟩

/-- The quantitative symmetric form (notes Cor 20.1 / arXiv Thm 1.3): the expected
number of resamplings of the Moser–Tardos algorithm is at most `card ι / d`, for every
truncation level `N`. The RHS simplification: with `x i = 1 / (d + 1)`,
`x i / (1 - x i) = 1 / d`, so the LLL sum `∑ i, x i / (1 - x i)` is `card ι / d`. -/
theorem moserTardos_symmetric_total {N : ℕ} (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal p)
    (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1)
    (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1) :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / d) := by
  classical
  let x : ι → ℝ := fun _ => ((d : ℝ) + 1)⁻¹
  have hx₀ : ∀ i, 0 ≤ x i := by
    intro i
    exact inv_nonneg.mpr (by positivity)
  have hx₁ : ∀ i, x i < 1 := by
    intro i
    exact inv_lt_one_of_one_lt₀ (by
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
      linarith)
  have hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)) := by
    intro i
    simpa [x, x'] using symmetric_hLLL Ω μ vbl A hp hd hd1 hcond i
  have hsum : ∑ i, x i / (1 - x i) = (Fintype.card ι : ℝ) / d := by
    have hquot : ∀ i, x i / (1 - x i) = 1 / (d : ℝ) := by
      intro i
      have hsub : 1 - x i = (d : ℝ) / ((d : ℝ) + 1) := by
        change 1 - ((d : ℝ) + 1)⁻¹ = (d : ℝ) / ((d : ℝ) + 1)
        field_simp
        ring
      rw [hsub]
      change ((d : ℝ) + 1)⁻¹ / ((d : ℝ) / ((d : ℝ) + 1)) = 1 / (d : ℝ)
      grind
    calc
      ∑ i, x i / (1 - x i) = ∑ i, (1 / (d : ℝ)) := by
          exact Finset.sum_congr rfl (fun i _ => hquot i)
      _ = (Fintype.card ι : ℝ) / d := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div, ← Finset.card_univ]
  calc
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
        ≤ ENNReal.ofReal (∑ i, x i / (1 - x i)) := by
          exact moserTardos_total (N := N) (Ω := Ω) (μ := μ) (vbl := vbl) (A := A)
            (hA := hA) (hdet := hdet) (x := x) (hx₀ := hx₀) (hx₁ := hx₁)
            (hLLL := hLLL) (pick := pick) (hpick := hpick)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) / d) := by
        rw [hsum]

end Symmetric

end TCSLean.MoserTardos

end
