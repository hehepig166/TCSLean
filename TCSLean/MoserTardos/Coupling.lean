/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure
import TCSLean.MoserTardos.WitnessTree

/-!
# The τ-check, the profile inequality, the check probability, and the coupling

This file defines the structural τ-check used by the Moser–Tardos witness-tree coupling: the
depth-thresholded profile counts `treeProfile`/`treeProfileAtDepth`, the Fin-row-certified
`checkAux`/`check`, and the profile inequality making the check's table indices injective
across different depths (40.1); the τ-check measure factorization (40.2): the structural
τ-product `treeProd` and `check_probability` — the measure of the τ-check equals the product
of the event probabilities; and the coupling inequality (40.3): `occurrence_implies_check`
and `coupling`.

## Main definitions

* `treeProfile`: the number of vertices of a witness tree at depth at least `d` whose label's
  variable set contains `j` (the notes' `|S_X(u)|`).
* `treeProfileAtDepth`: the same count at depth exactly `d`.
* `checkAux`/`check`: the structural τ-check — at every vertex `v`, the `DeterminedBy` witness
  of `label v` holds of the table entries `(j, treeProfile j (d(v) + 1))` for
  `j ∈ vbl (label v)` — exactly the notes' `(X, |S_X(u)|)` indices (14.4).
* `treeProd`: the structural τ-product: the event probability at the root times the products
  over the children.
* `checkFamily`/`checkAuxT`: the recursive family of coordinates read at each depth, and the
  tuple-space form of the check.

## Main results

* `treeProfile_le_size`/`treeProfile_lt_succ_of_size_le`: the profile is bounded by the tree
  size, so `size τ ≤ N` puts the check's row indices below `N + 1`.
* `treeProfile_add_succ`: the threshold-`d` profile splits as exact-depth-`d` plus threshold
  `d + 1`.
* `one_le_treeProfileAtDepth_of_mem`: a vertex at a valid path whose label contains `j`
  contributes to the exact-depth count at its own depth.
* `treeProfile_le_of_le`: the profile is antitone in the threshold.
* `treeProfile_gt_of_depth_lt`: the profile inequality (deeper case) — for valid-path vertices
  at `depth p < depth q` sharing `j`, the shallow vertex's index is strictly larger.
* `μN_map_rowTuple`/`μN_setOf_rowTuple`/`indepFun_rowTuple`/`μπ_cylinder_eq`/
  `cylinder_witness`/`measurableSet_witness`/`check_vertex_measure`: the 40.2 glue
  (G1–G6) — the marginal-of-restriction pushforward of `μN N μ` under an injective row
  selection (G1) and its preimage-measure form (G3), the binary independence of two
  disjoint row families (G2), the cylinder identity `μπ μ (cylinder S C) =
  Measure.pi … C` (G6), the witness-set/cylinder agreement with `A a` and its
  measurability (G5), and the per-vertex measure `μN N μ {vertex condition} =
  μπ μ (A a)` (G4).
* `checkSet_eq_vertices`: the τ-check set rewrites to the all-vertices conjunction —
  `{ω | check vbl A hdet hN ω} = {ω | ∀ p, vertex condition at p}` (the first step of
  the factorization).
* `check_probability`: the measure of the τ-check equals the product of the event
  probabilities — `μN N μ {ω | check vbl A hdet hN ω} = treeProd (μ := μ) A τ` for
  good `τ` with `size τ ≤ N`.
* `occurrence_implies_check`: if the occurring tree at time `t` is `τ` (with
  `size τ ≤ N`), then the structural τ-check passes on `ω`.
* `coupling`: the coupling lemma — `μN N μ {ω | ∃ t < R …, T … t = τ} ≤
  treeProd (μ := μ) A τ` for `τ` with `size τ ≤ N` (no `IsGood` hypothesis; a non-good
  `τ` has an empty occurrence event).

## References

The τ-check follows the Moser–Tardos notes, §14 ([moserTardos2010]).
-/

set_option autoImplicit false
set_option pp.unicode.fun true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace TCSLean.MoserTardos

universe u v w

/-! ## The structural τ-check (40.1): treeProfile / treeProfileAtDepth / checkAux / check -/

section TreeProfile

variable {ι : Type u} {κ : Type v} [DecidableEq κ]
variable {Ω : κ → Type w}
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hdet : ∀ i, DeterminedBy (A i) (vbl i))

/-- `treeProfile vbl τ j d` — the number of vertices of `τ` at depth at least `d` whose
label's variable set contains `j` (the notes' `|S_X(u)|` read at `d = depth u + 1`). -/
def treeProfile (vbl : ι → Finset κ) : WitnessTree ι → κ → ℕ → ℕ
  | WitnessTree.mk a cs, j, 0 =>
      (if j ∈ vbl a then 1 else 0) + (cs.map (fun c => treeProfile vbl c j 0)).sum
  | WitnessTree.mk _ cs, j, d + 1 =>
      (cs.map (fun c => treeProfile vbl c j d)).sum

/-- `treeProfileAtDepth vbl τ j d` — the number of vertices of `τ` at depth exactly `d`
whose label's variable set contains `j`. -/
def treeProfileAtDepth (vbl : ι → Finset κ) : WitnessTree ι → κ → ℕ → ℕ
  | WitnessTree.mk a _, j, 0 => if j ∈ vbl a then 1 else 0
  | WitnessTree.mk _ cs, j, d + 1 => (cs.map (fun c => treeProfileAtDepth vbl c j d)).sum

/-- The profile counts a subset of the vertices. -/
theorem treeProfile_le_size (τ : WitnessTree ι) (j : κ) (d : ℕ) :
    treeProfile vbl τ j d ≤ WitnessTree.size τ := by
  refine WitnessTree.rec
      (motive_1 := fun τ => ∀ d, treeProfile vbl τ j d ≤ WitnessTree.size τ)
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ d, treeProfile vbl c j d ≤ WitnessTree.size c)
      ?_ ?_ ?_ τ d
  · intro a cs ih d
    cases d with
    | zero =>
        have hs : (cs.map (fun c => treeProfile vbl c j 0)).sum ≤
            (cs.map WitnessTree.size).sum := by
          exact List.sum_le_sum (by intro c hc; exact ih c hc 0)
        simp [treeProfile, WitnessTree.size_mk]
        split_ifs with h <;> omega
    | succ d =>
        have hs : (cs.map (fun c => treeProfile vbl c j d)).sum ≤
            (cs.map WitnessTree.size).sum := by
          exact List.sum_le_sum (by intro c hc; exact ih c hc d)
        simp [treeProfile, WitnessTree.size_mk]
        omega
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- The bound making the check's row index a valid `Fin (N + 1)`: the check reads rows
`treeProfile vbl τ j (d + 1)`, and `size τ ≤ N` puts them below `N + 1`. -/
theorem treeProfile_lt_succ_of_size_le {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N)
    {j : κ} {d : ℕ} :
    treeProfile vbl τ j (d + 1) < N + 1 := by
  exact Nat.lt_of_le_of_lt (Nat.le_trans (treeProfile_le_size vbl τ j (d + 1)) hN)
    (Nat.lt_succ_self N)

/-- The τ-check at the root of the current subtree `cur`, viewed at depth `d` inside the
whole tree `whole`: the `DeterminedBy` witness of the root's label holds of the table
entries `(j, treeProfile vbl whole j (d + 1))` for `j ∈ vbl (label)`, and the children are
checked at depth `d + 1`. The profile of the WHOLE tree is threaded down unchanged. -/
noncomputable def checkAux (whole : WitnessTree ι) (hN : WitnessTree.size whole ≤ N) :
    WitnessTree ι → ℕ → ΩN N Ω → Prop
  | WitnessTree.mk a cs, d, ω =>
      Classical.choose (hdet a)
          (fun j => ω ⟨j, ⟨treeProfile vbl whole ↑j (d + 1),
            treeProfile_lt_succ_of_size_le vbl hN⟩⟩) ∧
        ∀ c ∈ cs, checkAux whole hN c (d + 1) ω

/-- The structural τ-check: the check succeeds iff for every vertex `v` at depth `d(v)`,
the `DeterminedBy` witness of `label v` holds of the table entries
`(j, treeProfile vbl τ j (d(v) + 1))` for `j ∈ vbl (label v)` — exactly the notes'
`(X, |S_X(u)|)` indices (14.4). -/
noncomputable def check {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N) (ω : ΩN N Ω) :
    Prop :=
  checkAux vbl A hdet τ hN τ 0 ω

/-- Profile at threshold `d` splits as exact-depth-`d` plus threshold `d + 1`. -/
theorem treeProfile_add_succ (τ : WitnessTree ι) (j : κ) (d : ℕ) :
    treeProfile vbl τ j d =
      treeProfileAtDepth vbl τ j d + treeProfile vbl τ j (d + 1) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => ∀ j d, treeProfile vbl τ j d =
        treeProfileAtDepth vbl τ j d + treeProfile vbl τ j (d + 1))
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ j d, treeProfile vbl c j d =
        treeProfileAtDepth vbl c j d + treeProfile vbl c j (d + 1))
      ?_ ?_ ?_ τ j d
  · intro a cs ih j d
    cases d with
    | zero => simp [treeProfile, treeProfileAtDepth]
    | succ d =>
        have hmap : (cs.map (fun c => treeProfile vbl c j d)).sum =
            (cs.map (fun c => treeProfileAtDepth vbl c j d + treeProfile vbl c j (d + 1))).sum :=
          congrArg List.sum (List.map_congr_left (fun c hc => ih c hc j d))
        simp [treeProfile, treeProfileAtDepth, hmap, List.sum_map_add]
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- A vertex at path `p` whose label's variable set contains `j` contributes to the
exact-depth count at its own depth. -/
theorem one_le_treeProfileAtDepth_of_mem {τ : WitnessTree ι} {p : List ℕ}
    (hp : WitnessTree.ValidPath τ p) {j : κ} (hj : j ∈ vbl (WitnessTree.labelAt hp)) :
    1 ≤ treeProfileAtDepth vbl τ j (WitnessTree.depth τ p) := by
  induction p generalizing τ with
  | nil =>
      cases hp with
      | root =>
          cases τ with
          | mk a cs =>
              have ha : j ∈ vbl a := by simpa using hj
              simp [treeProfileAtDepth, WitnessTree.depth, ha]
  | cons i p' ih =>
      cases hp with
      | cons i c hc hvp =>
          cases τ with
          | mk a cs =>
              have hmem : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
              have hsum : treeProfileAtDepth vbl c j p'.length ≤
                  (cs.map (fun c' => treeProfileAtDepth vbl c' j p'.length)).sum :=
                List.le_sum_of_mem (List.mem_map.mpr ⟨c, hmem, rfl⟩)
              have ih' : 1 ≤ treeProfileAtDepth vbl c j p'.length :=
                ih (τ := c) hvp (by simpa [WitnessTree.labelAt_cons] using hj)
              exact le_trans ih' hsum

/-- The profile is antitone in the threshold: `d ≤ d'` gives
`treeProfile vbl τ j d' ≤ treeProfile vbl τ j d`. -/
theorem treeProfile_le_of_le (τ : WitnessTree ι) (j : κ) {d d' : ℕ} (h : d ≤ d') :
    treeProfile vbl τ j d' ≤ treeProfile vbl τ j d := by
  refine Nat.le_induction
      (P := fun m _ => treeProfile vbl τ j m ≤ treeProfile vbl τ j d) ?_ ?_ d' h
  · exact le_rfl
  · intro m _hm ih
    have hstep : treeProfile vbl τ j (m + 1) ≤ treeProfile vbl τ j m := by
      rw [treeProfile_add_succ vbl τ j m]
      omega
    exact le_trans hstep ih

/-- The profile inequality (40.2's different-depth injectivity case): for vertices at
paths `p` and `q` with `depth p < depth q` and shared variable `j` (in the deeper vertex's
`vbl`), the shallow vertex's index is strictly larger — `treeProfile j (depth q + 1) <
treeProfile j (depth p + 1)`. No `IsGood` needed: the deeper vertex `q` itself lies in
`{depth ≥ depth q}` but not `{depth ≥ depth q + 1}`, and `{depth ≥ depth p + 1}` contains
`{depth ≥ depth q}`. -/
theorem treeProfile_gt_of_depth_lt {τ : WitnessTree ι} {p q : List ℕ}
    (hq : WitnessTree.ValidPath τ q) (hdp : WitnessTree.depth τ p < WitnessTree.depth τ q)
    {j : κ} (hjq : j ∈ vbl (WitnessTree.labelAt hq)) :
    treeProfile vbl τ j (WitnessTree.depth τ q + 1) <
      treeProfile vbl τ j (WitnessTree.depth τ p + 1) := by
  have hle : treeProfile vbl τ j (WitnessTree.depth τ q) ≤
      treeProfile vbl τ j (WitnessTree.depth τ p + 1) :=
    treeProfile_le_of_le vbl τ j (Nat.succ_le_of_lt hdp)
  have hsplit : treeProfile vbl τ j (WitnessTree.depth τ q) =
      treeProfileAtDepth vbl τ j (WitnessTree.depth τ q) +
        treeProfile vbl τ j (WitnessTree.depth τ q + 1) :=
    treeProfile_add_succ vbl τ j (WitnessTree.depth τ q)
  have hone : 1 ≤ treeProfileAtDepth vbl τ j (WitnessTree.depth τ q) :=
    one_le_treeProfileAtDepth_of_mem vbl hq hjq
  omega

end TreeProfile

/-! ## The τ-check measure factorization (40.2): treeProd / check_probability

This section carries the 40.2 block on top of the 40.1 content above: the
marginal-of-restriction glue, the disjoint-coordinate independence, the cylinder identity,
the witness-set measurability, the per-vertex measure, the check family, and the pinned
`treeProd`/`check_probability`. -/

section CheckProbability

variable {ι : Type u} {κ : Type v} [Fintype κ] [DecidableEq κ]
variable {Ω : κ → Type w} [∀ j, MeasurableSpace (Ω j)]
variable {μ : ∀ j, Measure (Ω j)} [∀ j, IsProbabilityMeasure (μ j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j))
variable (hdet : ∀ i, DeterminedBy (A i) (vbl i))

/-! ## G1: marginal-of-restriction (the survey B risk-3 glue) -/

-- `[DecidableEq κ]` is auto-included but unused (house omit pattern, cf. `VariableModel`).
omit [DecidableEq κ] in
lemma μN_map_rowTuple {S : Type*} [Fintype S] (row : S → Σ _ : κ, Fin (N + 1))
    (hrow : Function.Injective row) :
    (μN N μ).map (fun ω : ΩN N Ω => fun s : S => ω (row s)) =
      Measure.pi (fun s : S => μ (row s).1) := by
  have hcoord : iIndepFun
      (fun p : Σ _ : κ, Fin (N + 1) => fun ω : ΩN N Ω => ω p) (μN N μ) := by
    change iIndepFun (fun p : Σ _ : κ, Fin (N + 1) => fun ω : ΩN N Ω => ω p)
      (Measure.pi (fun p : Σ _ : κ, Fin (N + 1) => μ p.1))
    exact iIndepFun_pi (μ := fun p : Σ _ : κ, Fin (N + 1) => μ p.1)
      (X := fun p => (id : Ω p.1 → Ω p.1)) (mX := fun p => aemeasurable_id)
  have hS : iIndepFun (fun s : S => fun ω : ΩN N Ω => ω (row s)) (μN N μ) :=
    hcoord.precomp hrow
  have hmap : (μN N μ).map (fun ω => fun s : S => ω (row s)) =
      Measure.pi (fun s : S => (μN N μ).map (fun ω : ΩN N Ω => ω (row s))) :=
    hS.map_fun_eq_pi_map (fun s => (measurable_pi_apply (row s)).aemeasurable)
  have hmarg (s : S) : (μN N μ).map (fun ω : ΩN N Ω => ω (row s)) = μ (row s).1 := by
    change (Measure.pi (fun p : Σ _ : κ, Fin (N + 1) => μ p.1)).map (Function.eval (row s)) =
      μ (row s).1
    exact (measurePreserving_eval (μ := fun p : Σ _ : κ, Fin (N + 1) => μ p.1) (row s)).map_eq
  simpa [hmarg] using hmap

/-! ## G3: preimage-measure form of G1 -/

-- `[DecidableEq κ]` is auto-included but unused (house omit pattern).
omit [DecidableEq κ] in
lemma μN_setOf_rowTuple {S : Type*} [Fintype S] (row : S → Σ _ : κ, Fin (N + 1))
    (hrow : Function.Injective row) {C : Set (Π s : S, Ω (row s).1)} (hC : MeasurableSet C) :
    (μN N μ) {ω | (fun s : S => ω (row s)) ∈ C} =
      Measure.pi (fun s : S => μ (row s).1) C := by
  calc
    (μN N μ) {ω | (fun s : S => ω (row s)) ∈ C}
        = (μN N μ) ((fun ω : ΩN N Ω => fun s : S => ω (row s)) ⁻¹' C) := rfl
    _ = (μN N μ).map (fun ω : ΩN N Ω => fun s : S => ω (row s)) C := by
      exact (Measure.map_apply (μ := μN N μ) (f := fun ω : ΩN N Ω => fun s : S => ω (row s))
        (measurable_pi_lambda _ (fun s => measurable_pi_apply (row s))) hC).symm
    _ = Measure.pi (fun s : S => μ (row s).1) C := by
      rw [μN_map_rowTuple row hrow]

/-! ## G2: binary independence of two disjoint row families -/

lemma indepFun_rowTuple {S T : Type*} [Fintype S] [Fintype T]
    (rowS : S → Σ _ : κ, Fin (N + 1)) (rowT : T → Σ _ : κ, Fin (N + 1))
    (hdisj : ∀ s t, rowS s ≠ rowT t) :
    IndepFun (fun ω : ΩN N Ω => fun s : S => ω (rowS s))
      (fun ω : ΩN N Ω => fun t : T => ω (rowT t)) (μN N μ) := by
  have hcoord : iIndepFun
      (fun p : Σ _ : κ, Fin (N + 1) => fun ω : ΩN N Ω => ω p) (μN N μ) := by
    change iIndepFun (fun p : Σ _ : κ, Fin (N + 1) => fun ω : ΩN N Ω => ω p)
      (Measure.pi (fun p : Σ _ : κ, Fin (N + 1) => μ p.1))
    exact iIndepFun_pi (μ := fun p : Σ _ : κ, Fin (N + 1) => μ p.1)
      (X := fun p => (id : Ω p.1 → Ω p.1)) (mX := fun p => aemeasurable_id)
  let I : Finset (Σ _ : κ, Fin (N + 1)) := Finset.univ.image rowS
  let J : Finset (Σ _ : κ, Fin (N + 1)) := Finset.univ.image rowT
  have hIJ : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_image] at hp hq
    rcases hp with ⟨s, -, hps⟩
    rcases hq with ⟨t, -, hqt⟩
    exact hdisj s t (hps.trans hqt.symm)
  have htuples : IndepFun (fun ω : ΩN N Ω => fun p : I => ω (↑p : Σ _ : κ, Fin (N + 1)))
      (fun ω : ΩN N Ω => fun p : J => ω (↑p : Σ _ : κ, Fin (N + 1))) (μN N μ) :=
    hcoord.indepFun_finset₀ I J hIJ (fun p => (measurable_pi_apply p).aemeasurable)
  let φ : (Π p : I, Ω p.1.1) → (Π s : S, Ω (rowS s).1) :=
    fun x s => x ⟨rowS s, by simp [I]⟩
  let ψ : (Π p : J, Ω p.1.1) → (Π t : T, Ω (rowT t).1) :=
    fun x t => x ⟨rowT t, by simp [J]⟩
  have hφ : Measurable φ := by fun_prop
  have hψ : Measurable ψ := by fun_prop
  have hcomp : IndepFun (fun ω : ΩN N Ω =>
      (φ ∘ fun ω : ΩN N Ω => fun p : I => ω (↑p : Σ _ : κ, Fin (N + 1))) ω)
      (fun ω : ΩN N Ω =>
        (ψ ∘ fun ω : ΩN N Ω => fun p : J => ω (↑p : Σ _ : κ, Fin (N + 1))) ω)
          (μN N μ) :=
    htuples.comp hφ hψ
  simpa [φ, ψ] using hcomp

/-! ## G6: cylinder identity in the project's exact context -/

-- `[DecidableEq κ]` is auto-included but unused (house omit pattern).
omit [DecidableEq κ] in
lemma μπ_cylinder_eq (S : Finset κ) (C : Set (Π j : S, Ω j)) (hC : MeasurableSet C) :
    μπ μ (cylinder S C) = Measure.pi (fun j : S => μ j) C := by
  calc
    μπ μ (cylinder S C) = Measure.infinitePi μ (cylinder S C) := by
      change Measure.pi μ (cylinder S C) = Measure.infinitePi μ (cylinder S C)
      rw [Measure.infinitePi_eq_pi]
    _ = Measure.pi (fun j : S => μ j) C := by
      exact Measure.infinitePi_cylinder (μ := μ) hC

/-! ## G5: the witness set is measurable (completion map + hA) -/

-- Auto-included but unused: `[Fintype κ] [DecidableEq κ] [(j : κ) → MeasurableSpace (Ω j)]`.
omit [Fintype κ] [DecidableEq κ] [(j : κ) → MeasurableSpace (Ω j)] in
lemma cylinder_witness (a : ι) :
    cylinder (vbl a) {σ : Π j : vbl a, Ω j | Classical.choose (hdet a) σ} = A a := by
  ext σ
  rw [mem_cylinder]
  change (Classical.choose (hdet a) (fun j : vbl a => σ j)) ↔ σ ∈ A a
  exact (Classical.choose_spec (hdet a) σ).symm

-- `[Fintype κ]` is auto-included but unused (house omit pattern).
omit [Fintype κ] in
lemma measurableSet_witness (hA : ∀ i, MeasurableSet (A i)) (hΩ : ∀ j, Nonempty (Ω j))
    (a : ι) :
    MeasurableSet {σ : Π j : vbl a, Ω j | Classical.choose (hdet a) σ} := by
  classical
  let e : (Π j : vbl a, Ω j) → Π j, Ω j := fun σ j =>
    if hj : j ∈ vbl a then σ ⟨j, hj⟩ else Classical.choice (hΩ j)
  have he : Measurable e := by
    refine measurable_pi_lambda _ (fun j => ?_)
    by_cases hj : j ∈ vbl a
    · suffices Measurable (fun σ : Π j : vbl a, Ω j => σ ⟨j, hj⟩) by
        simpa [e, hj] using this
      exact measurable_pi_apply (⟨j, hj⟩ : vbl a)
    · suffices Measurable (fun σ : Π j : vbl a, Ω j => Classical.choice (hΩ j)) by
        simp [e, hj]
      exact measurable_const
  have hpre : {σ : Π j : vbl a, Ω j | Classical.choose (hdet a) σ} = e ⁻¹' (A a) := by
    ext σ
    rw [Set.mem_preimage]
    rw [Classical.choose_spec (hdet a) (e σ)]
    simp [e]
  simpa [hpre] using he (hA a)

/-! ## G4: the per-vertex measure equals the event probability -/

lemma check_vertex_measure (hA : ∀ i, MeasurableSet (A i)) (a : ι)
    (row : vbl a → Fin (N + 1)) :
    (μN N μ) {ω | Classical.choose (hdet a) (fun j : vbl a => ω ⟨j, row j⟩)} =
      μπ μ (A a) := by
  have hΩ : ∀ j, Nonempty (Ω j) := fun j => by
    have h1 : (μ j) Set.univ = 1 :=
      (show IsProbabilityMeasure (μ j) from inferInstance).measure_univ
    have huniv : (Set.univ : Set (Ω j)).Nonempty :=
      nonempty_of_measure_ne_zero (μ := μ j) (s := Set.univ) (by simp [h1])
    exact Nonempty.intro (Classical.choose huniv)
  have hrow : Function.Injective (fun j : vbl a => (⟨j, row j⟩ : Σ _ : κ, Fin (N + 1))) := by
    intro j j' h
    exact Subtype.ext (congrArg Sigma.fst h)
  calc
    (μN N μ) {ω | Classical.choose (hdet a) (fun j : vbl a => ω ⟨j, row j⟩)}
        = Measure.pi (fun j : vbl a => μ j)
            {σ : Π j : vbl a, Ω j | Classical.choose (hdet a) σ} := by
      exact μN_setOf_rowTuple
        (row := fun j : vbl a => (⟨j, row j⟩ : Σ _ : κ, Fin (N + 1))) hrow
        (hC := measurableSet_witness vbl A hdet hA hΩ a)
    _ = μπ μ (A a) := by
      rw [← μπ_cylinder_eq (vbl a) {σ : Π j : vbl a, Ω j | Classical.choose (hdet a) σ}
        (measurableSet_witness vbl A hdet hA hΩ a)]
      exact congrArg (μπ μ) (cylinder_witness vbl A hdet a)

/-! ## Pinned: treeProd + check_probability -/

/-- The structural τ-product: the event probability at the root times the products over the
children. -/
noncomputable def treeProd : WitnessTree ι → ℝ≥0∞
  | WitnessTree.mk a cs => μπ μ (A a) * (cs.map (fun c => treeProd c)).prod

/-! ## The recursive check family: the coordinates read at depth d -/

noncomputable def checkFamily (whole : WitnessTree ι) (hN : WitnessTree.size whole ≤ N) :
    WitnessTree ι → ℕ → Finset (Σ _ : κ, Fin (N + 1))
  | WitnessTree.mk a cs, d =>
      (vbl a).image (fun j => ⟨j, ⟨treeProfile vbl whole ↑j (d + 1),
        treeProfile_lt_succ_of_size_le vbl hN⟩⟩) ∪
        ((cs.map (fun c => checkFamily whole hN c (d + 1))).foldl (· ∪ ·) ∅)

/-! ## H1a: membership in the forest union -/

omit [Fintype κ] in
private lemma mem_foldl_union {F : WitnessTree ι → Finset (Σ _ : κ, Fin (N + 1))}
    {cs : List (WitnessTree ι)} {r : Σ _ : κ, Fin (N + 1)} :
    r ∈ (cs.map (fun c => F c)).foldl (· ∪ ·) ∅ ↔ ∃ c ∈ cs, r ∈ F c := by
  have hgen : ∀ b, r ∈ (cs.map (fun c => F c)).foldl (· ∪ ·) b ↔
      r ∈ b ∨ ∃ c ∈ cs, r ∈ F c := by
    intro b
    induction cs generalizing b with
    | nil => simp
    | cons c cs ih =>
        rw [List.map_cons, List.foldl_cons]
        simpa [Finset.mem_union, or_assoc] using ih (b ∪ F c)
  simpa using hgen ∅

/-! ## H0: compose a valid path into a subtree with a valid path of the subtree -/

private def validPath_append_multi {τ : WitnessTree ι} {p₀ p : List ℕ}
    (hp₀ : WitnessTree.ValidPath τ p₀)
      (hp : WitnessTree.ValidPath (WitnessTree.treeAt hp₀) p) :
    WitnessTree.ValidPath τ (p₀ ++ p) :=
  match p₀ with
  | [] => by simpa using hp
  | i :: p₀' =>
      match hp₀ with
      | WitnessTree.ValidPath.cons _ cj hcj hvp =>
          by
            simpa [List.cons_append, WitnessTree.treeAt_cons] using
              (WitnessTree.ValidPath.cons i cj hcj
                (validPath_append_multi hvp (by simpa [WitnessTree.treeAt_cons] using hp)))

/-! ## H2: the τ-check re-expressed on the tuple over its coordinate family -/

/-- The same check as `checkAux`, read from a tuple indexed by the coordinate family
`checkFamily τ hN σ d` instead of the whole table. -/
noncomputable def checkAuxT (τ : WitnessTree ι) (hN : WitnessTree.size τ ≤ N)
    (σ : WitnessTree ι)
    (d : ℕ) : (Π r : checkFamily vbl τ hN σ d, Ω r.1.1) → Prop :=
  match σ with
  | WitnessTree.mk a cs =>
      fun x =>
        Classical.choose (hdet a)
            (fun j : vbl a => x ⟨⟨j, ⟨treeProfile vbl τ ↑j (d + 1),
              treeProfile_lt_succ_of_size_le vbl hN⟩⟩, by
              unfold checkFamily
              exact Finset.mem_union.mpr
                (Or.inl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩))⟩) ∧
          ∀ (c : WitnessTree ι) (hc : c ∈ cs), checkAuxT τ hN c (d + 1)
            (fun r : checkFamily vbl τ hN c (d + 1) => x ⟨r.1, by
              unfold checkFamily
              exact Finset.mem_union.mpr (Or.inr (mem_foldl_union.mpr ⟨c, hc, r.2⟩))⟩)

/-! ## H3: the two checks agree -/

-- `[Fintype κ]` and the measurable-space instance are auto-included but unused (house
-- omit pattern).
omit [Fintype κ] [(j : κ) → MeasurableSpace (Ω j)] in
private lemma checkAux_eq_checkAuxT (τ : WitnessTree ι) (hN : WitnessTree.size τ ≤ N)
    (σ : WitnessTree ι) (d : ℕ) (ω : ΩN N Ω) :
    checkAux vbl A hdet τ hN σ d ω ↔
      checkAuxT vbl A hdet τ hN σ d (fun r : checkFamily vbl τ hN σ d => ω r.1) := by
  refine WitnessTree.rec (motive_1 := fun σ => ∀ d ω, checkAux vbl A hdet τ hN σ d ω ↔
      checkAuxT vbl A hdet τ hN σ d (fun r : checkFamily vbl τ hN σ d => ω r.1))
    (motive_2 := fun cs => ∀ d ω, (∀ c ∈ cs, checkAux vbl A hdet τ hN c d ω) ↔
      ∀ c ∈ cs, checkAuxT vbl A hdet τ hN c d (fun r : checkFamily vbl τ hN c d => ω r.1))
    (fun a cs ih => ?mk) (fun _ => ?nil) (fun c cs ihc ihcs => ?cons) σ d ω
  · intro d ω
    simp only [checkAux, checkAuxT]
    exact and_congr_right (fun _ => ih (d + 1) ω)
  · simp
  · intro d ω
    simp [ihc d ω, ihcs d ω]

/-! ## V1: the preorder vertex list (all paths) -/

/-- All paths of the tree, in preorder. -/
def vertices : WitnessTree ι → List (List ℕ)
  | WitnessTree.mk _ cs =>
      [] :: (List.finRange cs.length).flatMap (fun i => (vertices cs[i]).map (fun q => i.1 :: q))
termination_by τ => WitnessTree.size τ
decreasing_by
  simp_wf
  have hmem : WitnessTree.size cs[i] ∈ cs.map WitnessTree.size :=
    List.mem_map.mpr ⟨cs[i], List.getElem_mem i.2, rfl⟩
  exact Nat.lt_of_le_of_lt (List.le_sum_of_mem hmem) (by simp)

private lemma mem_vertices_iff {τ : WitnessTree ι} {p : List ℕ} :
    p ∈ vertices τ ↔ Nonempty (WitnessTree.ValidPath τ p) := by
  refine WitnessTree.rec
    (motive_1 := fun σ => ∀ p : List ℕ, p ∈ vertices σ ↔
      Nonempty (WitnessTree.ValidPath σ p))
    (motive_2 := fun cs => ∀ p : List ℕ, ∀ c ∈ cs, p ∈ vertices c ↔
      Nonempty (WitnessTree.ValidPath c p))
    (fun a cs ih => ?mk) (fun _ => ?nil) (fun c cs ihc ihcs => ?cons) τ p
  · intro p
    constructor
    · intro hp
      rw [vertices, List.mem_cons] at hp
      rcases hp with h | h
      · subst p
        exact ⟨WitnessTree.ValidPath.root⟩
      · rw [List.mem_flatMap] at h
        rcases h with ⟨i, hi, hmem⟩
        rw [List.mem_map] at hmem
        rcases hmem with ⟨q, hq, rfl⟩
        exact ⟨WitnessTree.ValidPath.cons i.1 cs[i] (by
          rw [WitnessTree.childrenOf, List.getElem?_eq_some_iff]
          exact ⟨i.2, rfl⟩) ((ih q cs[i] (List.getElem_mem i.2)).mp hq).some⟩
    · intro hp
      rcases hp with ⟨hpv⟩
      cases p with
      | nil => simp [vertices]
      | cons i p' =>
          cases hpv with
          | cons j cj hcj hvp =>
              rw [vertices]
              apply List.mem_cons.mpr (Or.inr ?_)
              rw [List.mem_flatMap]
              have hci' : cs[i]? = some cj := by simpa [WitnessTree.childrenOf] using hcj
              refine ⟨⟨i, (List.getElem?_eq_some_iff.mp hci').1⟩,
                List.mem_finRange ⟨i, (List.getElem?_eq_some_iff.mp hci').1⟩, ?_⟩
              rw [List.mem_map]
              refine ⟨p', ?_, by simp⟩
              have hci'1 : i < cs.length := (List.getElem?_eq_some_iff.mp hci').1
              have hcjc : cs[i]'hci'1 = cj := by simpa using (List.getElem?_eq_some_iff.mp hci').2
              simpa [hcjc] using (ih p' cj (List.mem_of_getElem? hci')).mpr ⟨hvp⟩
  · simp
  · intro p c₁ hc
    rcases List.mem_cons.mp hc with hcc | hcm
    · subst c₁
      exact ihc p
    · exact ihcs p c₁ hcm

/-! ## V3: rows of distinct vertices are disjoint (IsGood + strict profile inequality) -/

-- `[Fintype κ]` is auto-included but unused (house omit pattern).
omit [Fintype κ] in
private lemma rows_disjoint_of_distinct (τ : WitnessTree ι) (hN : WitnessTree.size τ ≤ N)
    (hgood : WitnessTree.IsGood vbl τ) {p q : List ℕ} (hp : WitnessTree.ValidPath τ p)
    (hq : WitnessTree.ValidPath τ q) (hne : p ≠ q) {j j' : κ}
    (hpv : j ∈ vbl (WitnessTree.labelAt hp)) (hqv : j' ∈ vbl (WitnessTree.labelAt hq))
    (heq : (⟨j, ⟨treeProfile vbl τ j (p.length + 1),
        treeProfile_lt_succ_of_size_le vbl hN⟩⟩ :
        Σ _ : κ, Fin (N + 1)) = ⟨j', ⟨treeProfile vbl τ j' (q.length + 1),
          treeProfile_lt_succ_of_size_le vbl hN⟩⟩) : False := by
  have hj : j = j' := Sigma.mk.inj_iff.mp heq |>.1
  have hk : treeProfile vbl τ j (p.length + 1) = treeProfile vbl τ j' (q.length + 1) :=
    congrArg Fin.val (congrArg Sigma.snd heq)
  subst j'
  by_cases hd : p.length = q.length
  · have hdisj : Disjoint (vbl (WitnessTree.labelAt hp)) (vbl (WitnessTree.labelAt hq)) :=
      hgood.2 p q hp hq hne hd
    exact Finset.disjoint_left.mp hdisj hpv hqv
  · have hlt : p.length < q.length ∨ q.length < p.length := Nat.lt_or_gt_of_ne hd
    rcases hlt with hlt | hgt
    · have hstrict : treeProfile vbl τ j (q.length + 1) < treeProfile vbl τ j (p.length + 1) :=
        treeProfile_gt_of_depth_lt (τ := τ) (vbl := vbl) hq
          (by simpa [WitnessTree.depth] using hlt) hqv
      omega
    · have hstrict : treeProfile vbl τ j (p.length + 1) < treeProfile vbl τ j (q.length + 1) :=
        treeProfile_gt_of_depth_lt (τ := τ) (vbl := vbl) hp
          (by simpa [WitnessTree.depth] using hgt) hpv
      omega

/-! ## The check is the conjunction over all vertices -/

private lemma treeAt_eq_of_path {τ : WitnessTree ι} {p : List ℕ}
    (hp hp' : WitnessTree.ValidPath τ p) : WitnessTree.treeAt hp = WitnessTree.treeAt hp' := by
  induction p generalizing τ with
  | nil =>
      cases hp with
      | root => cases hp' with
        | root => rfl
  | cons i p' ih =>
      cases hp with
      | cons j cj hcj hvp =>
          cases hp' with
          | cons j' cj' hcj' hvp' =>
              have hcc' : cj = cj' := Option.some.inj (hcj.symm.trans hcj')
              subst cj'
              rw [WitnessTree.treeAt_cons, WitnessTree.treeAt_cons]
              exact ih hvp hvp'

-- `[Fintype κ]` and the measurable-space instance are auto-included but unused (house
-- omit pattern).
omit [Fintype κ] [(j : κ) → MeasurableSpace (Ω j)] in
private lemma check_eq_allVertices (τ : WitnessTree ι) (hN : WitnessTree.size τ ≤ N)
    (ω : ΩN N Ω) :
    checkAux vbl A hdet τ hN τ 0 ω ↔
      ∀ p (hp : WitnessTree.ValidPath τ p),
        Classical.choose (hdet (WitnessTree.labelAt hp)) (fun j : vbl (WitnessTree.labelAt hp) =>
          ω ⟨j, ⟨treeProfile vbl τ ↑j (p.length + 1),
            treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩⟩) := by
  have hmain : ∀ τ' : WitnessTree ι, WitnessTree.size τ' = WitnessTree.size τ →
      ∀ d : ℕ, checkAux vbl A hdet τ hN τ' d ω ↔
      ∀ p (hp : WitnessTree.ValidPath τ' p),
        Classical.choose (hdet (WitnessTree.labelAt hp)) (fun j : vbl (WitnessTree.labelAt hp) =>
          ω ⟨j, ⟨treeProfile vbl τ ↑j (d + p.length + 1),
            treeProfile_lt_succ_of_size_le (d := d + p.length) vbl hN⟩⟩) := by
    refine @Nat.strong_induction_on
      (p := fun m => ∀ τ' : WitnessTree ι, WitnessTree.size τ' = m →
        ∀ d : ℕ, checkAux vbl A hdet τ hN τ' d ω ↔
        ∀ p (hp : WitnessTree.ValidPath τ' p),
          Classical.choose (hdet (WitnessTree.labelAt hp)) (fun j : vbl (WitnessTree.labelAt hp) =>
            ω ⟨j, ⟨treeProfile vbl τ ↑j (d + p.length + 1),
              treeProfile_lt_succ_of_size_le (d := d + p.length) vbl hN⟩⟩))
      (WitnessTree.size τ) ?step
    · intro m ihm τ' hτ'
      cases τ' with
      | mk a cs =>
          intro d
          simp only [checkAux]
          constructor
          · intro h p hp
            cases p with
            | nil => simpa using h.1
            | cons i p' =>
                cases hp with
                | cons j cj hcj hvp =>
                    have hmem : cj ∈ cs := List.mem_of_getElem? (by
                      simpa [WitnessTree.childrenOf] using hcj)
                    have hsize : WitnessTree.size cj < WitnessTree.size (WitnessTree.mk a cs) := by
                      exact Nat.lt_of_le_of_lt (List.le_sum_of_mem
                        (List.mem_map.mpr ⟨cj, hmem, rfl⟩)) (by simp)
                    have hindex' : (d + 1) + p'.length = d + (i :: p').length := by
                      change (d + 1) + p'.length = d + (p'.length + 1)
                      omega
                    simp only [WitnessTree.labelAt_cons]
                    let P : ℕ → Prop := fun idx =>
                      Classical.choose (hdet (WitnessTree.labelAt hvp))
                        (fun j : vbl (WitnessTree.labelAt hvp) => ω ⟨j,
                          ⟨treeProfile vbl τ ↑j (idx + 1),
                            treeProfile_lt_succ_of_size_le (d := idx) vbl hN⟩⟩)
                    exact Eq.mpr (congrArg P hindex'.symm)
                      ((ihm (WitnessTree.size cj) (by simpa [hτ'] using hsize) cj rfl
                        (d + 1)).mp (h.2 cj hmem) p' hvp)
          · intro h
            refine ⟨h [] WitnessTree.ValidPath.root, ?_⟩
            intro c hc
            rcases List.mem_iff_getElem?.mp hc with ⟨i, hi⟩
            have hsize : WitnessTree.size c < WitnessTree.size (WitnessTree.mk a cs) := by
              exact Nat.lt_of_le_of_lt (List.le_sum_of_mem
                (List.mem_map.mpr ⟨c, hc, rfl⟩)) (by simp)
            exact (ihm (WitnessTree.size c) (by simpa [hτ'] using hsize) c rfl (d + 1)).mpr (by
                intro p hp
                have hindex' : (d + 1) + p.length = d + (i :: p).length := by
                  change (d + 1) + p.length = d + (p.length + 1)
                  omega
                let P2 : ι → ℕ → Prop := fun L idx =>
                  Classical.choose (hdet L)
                    (fun j : vbl L => ω ⟨j,
                      ⟨treeProfile vbl τ ↑j (idx + 1),
                        treeProfile_lt_succ_of_size_le (d := idx) vbl hN⟩⟩)
                have hci : (WitnessTree.mk a cs).childrenOf[i]? = some c := by
                  simpa [WitnessTree.childrenOf] using hi
                exact Eq.mpr (congrArg (P2 (WitnessTree.labelAt hp)) hindex')
                  (Eq.mp (congrArg (fun L => P2 L (d + (i :: p).length))
                    (WitnessTree.labelAt_cons (WitnessTree.mk a cs) i p c hci hp))
                    (h (i :: p) (WitnessTree.ValidPath.cons i c hci hp))))
  convert (hmain τ (Eq.refl _) 0) using 2
  · rename_i p
    constructor
    · intro h hp
      let P2 : ℕ → Prop := fun idx =>
        Classical.choose (hdet (WitnessTree.labelAt hp))
          (fun j : vbl (WitnessTree.labelAt hp) => ω ⟨j,
            ⟨treeProfile vbl τ ↑j (idx + 1),
              treeProfile_lt_succ_of_size_le (d := idx) vbl hN⟩⟩)
      exact Eq.mpr (congrArg P2 (Nat.zero_add p.length)) (h hp)
    · intro h hp
      let P2 : ℕ → Prop := fun idx =>
        Classical.choose (hdet (WitnessTree.labelAt hp))
          (fun j : vbl (WitnessTree.labelAt hp) => ω ⟨j,
            ⟨treeProfile vbl τ ↑j (idx + 1),
              treeProfile_lt_succ_of_size_le (d := idx) vbl hN⟩⟩)
      exact Eq.mp (congrArg P2 (Nat.zero_add p.length)) (h hp)

/-! ## Step 1: the LHS set rewrites to the all-vertices conjunction -/

-- `[Fintype κ]` and the measurable-space instance are auto-included but unused (house omit
-- pattern).
omit [Fintype κ] [(j : κ) → MeasurableSpace (Ω j)] in
lemma checkSet_eq_vertices {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N) :
    {ω : ΩN N Ω | check vbl A hdet hN ω} =
      {ω : ΩN N Ω | ∀ p (hp : WitnessTree.ValidPath τ p),
        Classical.choose (hdet (WitnessTree.labelAt hp)) (fun j : vbl (WitnessTree.labelAt hp) =>
          ω ⟨j, ⟨treeProfile vbl τ ↑j (p.length + 1),
            treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩⟩)} := by
  ext ω
  simp only [Set.mem_setOf_eq, check]
  exact check_eq_allVertices vbl A hdet τ hN ω

/-- The row read at a vertex: coordinate `j` of the label's variable set, at depth + 1. -/
private def vertexRow {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N) {p : List ℕ}
    (hp : WitnessTree.ValidPath τ p) : vbl (WitnessTree.labelAt hp) → Fin (N + 1) :=
  fun j => ⟨treeProfile vbl τ ↑j (p.length + 1),
    treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩

/-- The vertex condition at path `p` (certificate-independent by `treeAt_eq_of_path`). -/
private def vertexCond {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N) (p : List ℕ) :
    Set (ΩN N Ω) :=
  {ω | ∀ (hp : WitnessTree.ValidPath τ p),
      Classical.choose (hdet (WitnessTree.labelAt hp)) (fun j : vbl (WitnessTree.labelAt hp) =>
        ω ⟨j, vertexRow vbl hN hp j⟩)}

-- `[Fintype κ]` and the measurable-space instance are auto-included but unused (house
-- omit pattern).
omit [Fintype κ] [(j : κ) → MeasurableSpace (Ω j)] in
/-- The per-vertex conjunction is the finset intersection over the vertices. -/
private lemma checkSet_eq_iInter {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N) :
    {ω : ΩN N Ω | ∀ p (hp : WitnessTree.ValidPath τ p),
        Classical.choose (hdet (WitnessTree.labelAt hp)) (fun j : vbl (WitnessTree.labelAt hp) =>
          ω ⟨j, ⟨treeProfile vbl τ ↑j (p.length + 1),
            treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩⟩)} =
      ⋂ p : {p // p ∈ (vertices τ).toFinset}, vertexCond vbl A hdet hN p.1 := by
  ext ω
  constructor
  · intro h p hp_mem
    rcases hp_mem with ⟨q, rfl⟩
    intro hp
    exact h q.1 hp
  · intro h p hp
    have hp_mem : p ∈ (vertices τ).toFinset :=
      List.mem_toFinset.mpr (mem_vertices_iff.mpr ⟨hp⟩)
    exact (h (vertexCond vbl A hdet hN p) ⟨⟨p, hp_mem⟩, rfl⟩) hp

/-- The measure of the vertex condition equals the event probability. -/
private lemma μN_vertexCond {τ : WitnessTree ι} (hA : ∀ i, MeasurableSet (A i))
    (hN : WitnessTree.size τ ≤ N) {p : List ℕ} (hp : WitnessTree.ValidPath τ p) :
    μN N μ (vertexCond vbl A hdet hN p) = μπ μ (A (WitnessTree.labelAt hp)) := by
  have hset : vertexCond vbl A hdet hN p =
      {ω : ΩN N Ω | Classical.choose (hdet (WitnessTree.labelAt hp))
        (fun j : vbl (WitnessTree.labelAt hp) => ω ⟨j, vertexRow vbl hN hp j⟩)} := by
    ext ω
    constructor
    · intro h
      exact h hp
    · intro h hp'
      let P : ι → Prop := fun L => Classical.choose (hdet L) (fun j : vbl L => ω ⟨j,
        ⟨treeProfile vbl τ ↑j (p.length + 1),
          treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩⟩)
      exact Eq.mp (congrArg P (congrArg WitnessTree.labelOf (treeAt_eq_of_path hp hp'))) h
  calc
    μN N μ (vertexCond vbl A hdet hN p)
        = μN N μ {ω | Classical.choose (hdet (WitnessTree.labelAt hp))
            (fun j : vbl (WitnessTree.labelAt hp) => ω ⟨j, vertexRow vbl hN hp j⟩)} := by
      rw [hset]
    _ = μπ μ (A (WitnessTree.labelAt hp)) :=
      check_vertex_measure vbl A hdet hA (WitnessTree.labelAt hp) (vertexRow vbl hN hp)

/-- The subtype of elements of the empty finset is empty. -/
private lemma isEmpty_subtype_emptyFinset :
    IsEmpty {p : List ℕ // p ∈ (∅ : Finset (List ℕ))} :=
  ⟨fun p => List.not_mem_nil (List.mem_toFinset.mp p.2)⟩

omit [Fintype κ] [(j : κ) → MeasurableSpace (Ω j)] in
/-- The intersection over the insert-subtype splits as the new vertex intersected with
the accumulated intersection. -/
private lemma iInter_insert_eq {τ : WitnessTree ι} (hN : WitnessTree.size τ ≤ N)
    (p : List ℕ) (s : Finset (List ℕ)) :
    (⋂ q : {q // q ∈ insert p s}, vertexCond vbl A hdet hN q.1) =
      vertexCond vbl A hdet hN p ∩ ⋂ q : {q // q ∈ s}, vertexCond vbl A hdet hN q.1 := by
  ext ω
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact h (vertexCond vbl A hdet hN p) ⟨⟨p, Finset.mem_insert_self p s⟩, rfl⟩
    · intro q hq
      rcases hq with ⟨r, rfl⟩
      exact h (vertexCond vbl A hdet hN r.1) ⟨⟨r.1, Finset.mem_insert_of_mem r.2⟩, rfl⟩
  · intro h q hq
    rcases hq with ⟨r, rfl⟩
    rcases r with ⟨r', hr'⟩
    rcases Finset.mem_insert.mp hr' with rfl | hr
    · exact h.1
    · exact h.2 (vertexCond vbl A hdet hN r') ⟨⟨r', hr⟩, rfl⟩

/-- The measure of two distinct vertex conditions factors (independent rows). -/
private lemma μN_vertexCond_inter_vertexCond {τ : WitnessTree ι}
    (hA : ∀ i, MeasurableSet (A i))
    (hgood : WitnessTree.IsGood vbl τ) (hN : WitnessTree.size τ ≤ N) {p q : List ℕ}
    (hp : WitnessTree.ValidPath τ p) (hq : WitnessTree.ValidPath τ q) (hne : p ≠ q) :
    μN N μ (vertexCond vbl A hdet hN p ∩ vertexCond vbl A hdet hN q) =
      μN N μ (vertexCond vbl A hdet hN p) * μN N μ (vertexCond vbl A hdet hN q) := by
  have hp_set : vertexCond vbl A hdet hN p =
      (fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hp) =>
        ω ⟨j, vertexRow vbl hN hp j⟩) ⁻¹'
        {σ : Π j : vbl (WitnessTree.labelAt hp), Ω j |
          Classical.choose (hdet (WitnessTree.labelAt hp)) σ} := by
    ext ω
    constructor
    · intro h
      exact h hp
    · intro h hp'
      let P : ι → Prop := fun L => Classical.choose (hdet L) (fun j : vbl L => ω ⟨j,
        ⟨treeProfile vbl τ ↑j (p.length + 1),
          treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩⟩)
      exact Eq.mp (congrArg P (congrArg WitnessTree.labelOf (treeAt_eq_of_path hp hp'))) h
  have hq_set : vertexCond vbl A hdet hN q =
      (fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hq) =>
        ω ⟨j, vertexRow vbl hN hq j⟩) ⁻¹'
        {σ : Π j : vbl (WitnessTree.labelAt hq), Ω j |
          Classical.choose (hdet (WitnessTree.labelAt hq)) σ} := by
    ext ω
    constructor
    · intro h
      exact h hq
    · intro h hq'
      let P : ι → Prop := fun L => Classical.choose (hdet L) (fun j : vbl L => ω ⟨j,
        ⟨treeProfile vbl τ ↑j (q.length + 1),
          treeProfile_lt_succ_of_size_le (d := q.length) vbl hN⟩⟩)
      exact Eq.mp (congrArg P (congrArg WitnessTree.labelOf (treeAt_eq_of_path hq hq'))) h
  have hindep : IndepFun (fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hp) =>
      ω (⟨j, vertexRow vbl hN hp j⟩ : Σ _ : κ, Fin (N + 1)))
      (fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hq) =>
        ω (⟨j, vertexRow vbl hN hq j⟩ : Σ _ : κ, Fin (N + 1))) (μN N μ) :=
    indepFun_rowTuple (rowS := fun j : vbl (WitnessTree.labelAt hp) =>
        (⟨j, vertexRow vbl hN hp j⟩ : Σ _ : κ, Fin (N + 1)))
      (rowT := fun j : vbl (WitnessTree.labelAt hq) =>
        (⟨j, vertexRow vbl hN hq j⟩ : Σ _ : κ, Fin (N + 1)))
      (hdisj := by
        intro j j' heq
        exact rows_disjoint_of_distinct vbl τ hN hgood hp hq hne j.2 j'.2 heq)
  have hΩ : ∀ j, Nonempty (Ω j) := fun j => by
    have h1 : (μ j) Set.univ = 1 :=
      (show IsProbabilityMeasure (μ j) from inferInstance).measure_univ
    have huniv : (Set.univ : Set (Ω j)).Nonempty :=
      nonempty_of_measure_ne_zero (μ := μ j) (s := Set.univ) (by simp [h1])
    exact Nonempty.intro (Classical.choose huniv)
  have hmS : MeasurableSet {σ : Π j : vbl (WitnessTree.labelAt hp), Ω j |
      Classical.choose (hdet (WitnessTree.labelAt hp)) σ} :=
    measurableSet_witness vbl A hdet hA hΩ (WitnessTree.labelAt hp)
  have hmT : MeasurableSet {σ : Π j : vbl (WitnessTree.labelAt hq), Ω j |
      Classical.choose (hdet (WitnessTree.labelAt hq)) σ} :=
    measurableSet_witness vbl A hdet hA hΩ (WitnessTree.labelAt hq)
  rw [hp_set, hq_set]
  exact hindep.measure_inter_preimage_eq_mul
    (s := {σ : Π j : vbl (WitnessTree.labelAt hp), Ω j |
      Classical.choose (hdet (WitnessTree.labelAt hp)) σ})
    (t := {σ : Π j : vbl (WitnessTree.labelAt hq), Ω j |
      Classical.choose (hdet (WitnessTree.labelAt hq)) σ})
    hmS hmT

/-- The measure of the per-vertex conjunction factors over the vertices finset. -/
private lemma μN_iInter_eq_prod {τ : WitnessTree ι} (hA : ∀ i, MeasurableSet (A i))
    (hgood : WitnessTree.IsGood vbl τ) (hN : WitnessTree.size τ ≤ N) :
    μN N μ (⋂ p : {p // p ∈ (vertices τ).toFinset}, vertexCond vbl A hdet hN p.1) =
      ∏ p ∈ (vertices τ).toFinset, μN N μ (vertexCond vbl A hdet hN p) := by
  classical
  have hmain : ∀ s : Finset (List ℕ), s ⊆ (vertices τ).toFinset →
      μN N μ (⋂ p : {p // p ∈ s}, vertexCond vbl A hdet hN p.1) =
        ∏ p ∈ s, μN N μ (vertexCond vbl A hdet hN p) := by
    intro s
    refine Finset.induction_on s ?h₁ ?h₂
    · intro hs
      have hInter : (⋂ p : {p // p ∈ (∅ : Finset (List ℕ))}, vertexCond vbl A hdet hN p.1) =
          (Set.univ : Set (ΩN N Ω)) := by
        ext ω
        constructor
        · intro hω
          trivial
        · intro hω s₀ hs₀
          rcases hs₀ with ⟨p, rfl⟩
          rcases p with ⟨q, hq⟩
          exact (List.not_mem_nil (List.mem_toFinset.mp hq)).elim
      rw [hInter]
      simp
    · intro p s hp_notmem ih hs
      have hp_mem : p ∈ (vertices τ).toFinset := hs (Finset.mem_insert_self p s)
      have hs_sub : s ⊆ (vertices τ).toFinset := fun q hq => hs (Finset.mem_insert_of_mem hq)
      have hp : WitnessTree.ValidPath τ p :=
        Classical.choice ((mem_vertices_iff).mp (List.mem_toFinset.mp hp_mem))
      let hq_of : (q : {q // q ∈ s}) → WitnessTree.ValidPath τ q.1 :=
        fun q => Classical.choice ((mem_vertices_iff).mp (List.mem_toFinset.mp (hs_sub q.2)))
      let rowT : (Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q))) →
          Σ _ : κ, Fin (N + 1) :=
        fun t => (⟨t.2, vertexRow vbl hN (hq_of t.1) t.2⟩ : Σ _ : κ, Fin (N + 1))
      let C_p : Set (Π j : vbl (WitnessTree.labelAt hp), Ω j) :=
        {σ | Classical.choose (hdet (WitnessTree.labelAt hp)) σ}
      let C_flat : Set (Π t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)),
          Ω (rowT t).1) :=
        {σ | ∀ q : {q // q ∈ s}, Classical.choose (hdet (WitnessTree.labelAt (hq_of q)))
          (fun j : vbl (WitnessTree.labelAt (hq_of q)) => σ ⟨q, j⟩)}
      have hp_set : vertexCond vbl A hdet hN p =
          (fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hp) =>
            ω ⟨j, vertexRow vbl hN hp j⟩) ⁻¹' C_p := by
        ext ω
        constructor
        · intro h
          exact h hp
        · intro h hp'
          let P : ι → Prop := fun L => Classical.choose (hdet L) (fun j : vbl L => ω ⟨j,
            ⟨treeProfile vbl τ ↑j (p.length + 1),
              treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩⟩)
          exact Eq.mp (congrArg P (congrArg WitnessTree.labelOf (treeAt_eq_of_path hp hp'))) h
      have hacc : (⋂ q : {q // q ∈ s}, vertexCond vbl A hdet hN q.1) =
          (fun ω : ΩN N Ω =>
            fun t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)) =>
              ω (rowT t)) ⁻¹'
            C_flat := by
        ext ω
        constructor
        · intro h q
          exact (h (vertexCond vbl A hdet hN q.1) ⟨q, rfl⟩) (hq_of q)
        · intro h s₀ hs₀
          rcases hs₀ with ⟨q, rfl⟩
          intro hp'
          let P : ι → Prop := fun L => Classical.choose (hdet L) (fun j : vbl L => ω ⟨j,
            ⟨treeProfile vbl τ ↑j (q.1.length + 1),
              treeProfile_lt_succ_of_size_le (d := q.1.length) vbl hN⟩⟩)
          exact Eq.mpr (congrArg P (congrArg WitnessTree.labelOf
            (treeAt_eq_of_path hp' (hq_of q)))) (h q)
      have hindep : IndepFun (fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hp) =>
          ω (⟨j, vertexRow vbl hN hp j⟩ : Σ _ : κ, Fin (N + 1)))
          (fun ω : ΩN N Ω =>
            fun t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)) => ω (rowT t))
          (μN N μ) :=
        indepFun_rowTuple (rowS := fun j : vbl (WitnessTree.labelAt hp) =>
            (⟨j, vertexRow vbl hN hp j⟩ : Σ _ : κ, Fin (N + 1)))
          (rowT := fun t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)) =>
            (⟨t.2, vertexRow vbl hN (hq_of t.1) t.2⟩ : Σ _ : κ, Fin (N + 1)))
          (hdisj := by
            intro j t heq
            exact rows_disjoint_of_distinct vbl τ hN hgood hp (hq_of t.1)
              (by intro hpq; exact hp_notmem (hpq.symm ▸ t.1.2)) j.2 t.2.2 heq)
      have hΩ : ∀ j, Nonempty (Ω j) := fun j => by
        have h1 : (μ j) Set.univ = 1 :=
          (show IsProbabilityMeasure (μ j) from inferInstance).measure_univ
        have huniv : (Set.univ : Set (Ω j)).Nonempty :=
          nonempty_of_measure_ne_zero (μ := μ j) (s := Set.univ) (by simp [h1])
        exact Nonempty.intro (Classical.choose huniv)
      have hm_p : MeasurableSet C_p :=
        measurableSet_witness vbl A hdet hA hΩ (WitnessTree.labelAt hp)
      have hm_T : MeasurableSet C_flat := by
        let W : (q : {q // q ∈ s}) → Set (Π j : vbl (WitnessTree.labelAt (hq_of q)), Ω j) :=
          fun q => {t | Classical.choose (hdet (WitnessTree.labelAt (hq_of q))) t}
        let φ : (q : {q // q ∈ s}) →
            (Π t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)), Ω (rowT t).1) →
              Π j : vbl (WitnessTree.labelAt (hq_of q)), Ω j :=
          fun q σ j => σ ⟨q, j⟩
        have hset : C_flat = ⋂ q : {q // q ∈ s}, (φ q) ⁻¹' (W q) := by
          ext σ
          constructor
          · intro hσ s₀ hs₀
            rcases hs₀ with ⟨q, rfl⟩
            exact hσ q
          · intro hσ q
            exact hσ ((φ q) ⁻¹' (W q)) ⟨q, rfl⟩
        have hW : ∀ q : {q // q ∈ s}, MeasurableSet (W q) := by
          intro q
          exact measurableSet_witness vbl A hdet hA hΩ (WitnessTree.labelAt (hq_of q))
        have hφ : ∀ q : {q // q ∈ s}, Measurable (φ q) := by
          intro q
          exact measurable_pi_lambda
            (fun σ : Π t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)),
              Ω (rowT t).1 => fun j : vbl (WitnessTree.labelAt (hq_of q)) => σ ⟨q, j⟩)
            (fun j => measurable_pi_apply
              (⟨q, j⟩ : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q))))
        rw [hset]
        rw [← Set.biInter_univ (fun q : {q // q ∈ s} => (φ q) ⁻¹' (W q))]
        refine Set.finite_univ.measurableSet_biInter (fun q _ => ?_)
        exact (hφ q) (hW q)
      rw [iInter_insert_eq vbl A hdet hN p s]
      calc
        μN N μ (vertexCond vbl A hdet hN p ∩
          ⋂ q : {q // q ∈ s}, vertexCond vbl A hdet hN q.1)
            = μN N μ ((fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hp) =>
                ω ⟨j, vertexRow vbl hN hp j⟩) ⁻¹' C_p ∩
              (fun ω : ΩN N Ω =>
                fun t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)) =>
                  ω (rowT t)) ⁻¹' C_flat) := by
          rw [hp_set, hacc]
        _ = μN N μ ((fun ω : ΩN N Ω => fun j : vbl (WitnessTree.labelAt hp) =>
            ω ⟨j, vertexRow vbl hN hp j⟩) ⁻¹' C_p) *
          μN N μ ((fun ω : ΩN N Ω =>
            fun t : Σ q : {q // q ∈ s}, vbl (WitnessTree.labelAt (hq_of q)) =>
              ω (rowT t)) ⁻¹' C_flat) :=
          hindep.measure_inter_preimage_eq_mul (s := C_p) (t := C_flat) hm_p hm_T
        _ = μN N μ (vertexCond vbl A hdet hN p) *
            ∏ q ∈ s, μN N μ (vertexCond vbl A hdet hN q) := by
          rw [← hp_set, ← hacc, ih hs_sub]
        _ = ∏ q ∈ insert p s, μN N μ (vertexCond vbl A hdet hN q) := by
          rw [Finset.prod_insert hp_notmem]
  exact hmain (vertices τ).toFinset (by intro p hp; exact hp)

/-! ## 40.2 machinery: the vertex-condition induction

The induction scaffolding `check_probability` rests on: the List-to-Finset glue, the
forest enumeration of the children's vertices, the per-vertex label factor, and the
two-fold rewrite of the tree product over the vertex list. -/

/-! ### List-to-Finset glue (hand-proved; `List.toFinset_flatMap` is absent from this mathlib) -/

private lemma List_toFinset_append {α : Type*} [DecidableEq α] {l l' : List α} :
    (l ++ l').toFinset = l.toFinset ∪ l'.toFinset := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma List_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {l : List α} {f : α → β} :
    (l.map f).toFinset = l.toFinset.image f := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma List_toFinset_flatMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    {l : List α} {f : α → List β} :
    (l.flatMap f).toFinset = l.toFinset.biUnion (fun a => (f a).toFinset) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-! ### The forest enumeration of the children's vertices -/

/-- The child-vertex paths of a child list: `i :: q` for `q` a vertex of the `i`-th child. -/
private def childVertices (cs : List (WitnessTree ι)) : List (List ℕ) :=
  (List.finRange cs.length).flatMap (fun i => (vertices cs[i]).map (fun q => i.1 :: q))

/-- The child-vertex paths of the `i`-th child, as a finset. -/
private def childFinset (cs : List (WitnessTree ι)) (i : Fin cs.length) : Finset (List ℕ) :=
  ((vertices cs[i]).toFinset).image (fun q => i.1 :: q)

/-! ### The per-vertex label factor (certificate-independent) -/

/-- The event probability of the label at a path, if the path is valid. -/
private noncomputable def labelFactor (τ : WitnessTree ι) (p : List ℕ) : ℝ≥0∞ := by
  classical
  exact if hp : Nonempty (WitnessTree.ValidPath τ p) then
    μπ μ (A (WitnessTree.labelAt (Classical.choice hp))) else 0

-- Descending one level along a valid child link preserves the label factor.
-- Auto-included but unused: `[DecidableEq κ]`, `[∀ (j : κ), IsProbabilityMeasure (μ j)]`
-- (house omit pattern).
omit [DecidableEq κ] [∀ (j : κ), IsProbabilityMeasure (μ j)] in
private lemma labelFactor_cons {τ c : WitnessTree ι} {i : ℕ}
    (hc : τ.childrenOf[i]? = some c) (q : List ℕ) :
    labelFactor (μ := μ) A τ (i :: q) = labelFactor (μ := μ) A c q := by
  classical
  by_cases hq : Nonempty (WitnessTree.ValidPath c q)
  · have hτ : Nonempty (WitnessTree.ValidPath τ (i :: q)) :=
      ⟨WitnessTree.ValidPath.cons i c hc (Classical.choice hq)⟩
    unfold labelFactor
    rw [dif_pos hq, dif_pos hτ]
    change (μπ μ) (A (WitnessTree.labelAt (Classical.choice hτ))) =
      (μπ μ) (A (WitnessTree.labelAt (Classical.choice hq)))
    congr 1
    congr 1
    trans WitnessTree.labelAt (WitnessTree.ValidPath.cons i c hc (Classical.choice hq))
    · exact congrArg WitnessTree.labelOf
        (treeAt_eq_of_path (Classical.choice hτ)
          (WitnessTree.ValidPath.cons i c hc (Classical.choice hq)))
    · exact WitnessTree.labelAt_cons τ i q c hc (Classical.choice hq)
  · have hτ' : ¬ Nonempty (WitnessTree.ValidPath τ (i :: q)) := by
      rintro ⟨hp⟩
      cases hp with
      | cons j c' hc' hvp =>
          have hcc' : c = c' := Option.some.inj (hc.symm.trans hc')
          subst c'
          exact hq ⟨hvp⟩
    unfold labelFactor
    rw [dif_neg hq, dif_neg hτ']

-- The product of the per-vertex label factors equals the tree product.
-- Auto-included but unused: `[DecidableEq κ]`, `[∀ (j : κ), IsProbabilityMeasure (μ j)]`
-- (house omit pattern).
omit [DecidableEq κ] [∀ (j : κ), IsProbabilityMeasure (μ j)] in
private lemma prod_labelFactor_eq_treeProd : ∀ τ : WitnessTree ι,
    (∏ p ∈ (vertices τ).toFinset, labelFactor (μ := μ) A τ p) =
      treeProd (μ := μ) A τ := by
  intro τ
  refine @Nat.strong_induction_on (p := fun m => ∀ τ' : WitnessTree ι,
      WitnessTree.size τ' = m →
        (∏ p ∈ (vertices τ').toFinset, labelFactor (μ := μ) A τ' p) =
          treeProd (μ := μ) A τ')
    (WitnessTree.size τ) ?step τ rfl
  · intro m ihm τ' hτ'
    cases τ' with
    | mk a cs =>
        have hnotmem : [] ∉ (childVertices cs).toFinset := by
          intro h
          have hm : [] ∈ childVertices cs := List.mem_toFinset.mp h
          rw [childVertices, List.mem_flatMap] at hm
          rcases hm with ⟨i, hi, hm⟩
          rw [List.mem_map] at hm
          rcases hm with ⟨q, hq, hnil⟩
          cases hnil
        have hroot : labelFactor (μ := μ) A (WitnessTree.mk a cs) [] = μπ μ (A a) := by
          unfold labelFactor
          rw [dif_pos ⟨WitnessTree.ValidPath.root⟩]
          simp
        have hforest : (∏ p ∈ (childVertices cs).toFinset,
              labelFactor (μ := μ) A (WitnessTree.mk a cs) p) =
            (cs.map (fun c => treeProd (μ := μ) A c)).prod := by
          have hcv : (childVertices cs).toFinset =
              Finset.univ.biUnion (fun i => childFinset cs i) := by
            unfold childVertices childFinset
            rw [List_toFinset_flatMap, List.toFinset_finRange]
            congr 1
            funext i
            rw [List_toFinset_map]
          have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin cs.length)))
              (fun i => childFinset cs i) := by
            intro i hi j hj hij
            change Disjoint (childFinset cs i) (childFinset cs j)
            rw [Finset.disjoint_left]
            intro p hp hq
            unfold childFinset at hp hq
            rw [Finset.mem_image] at hp hq
            rcases hp with ⟨q, hqmem, hpq⟩
            rcases hq with ⟨q', hq'mem, hqp⟩
            have hcons : i.1 :: q = j.1 :: q' := hpq.trans hqp.symm
            have hhead : i.1 = j.1 := Option.some.inj (by simpa using congrArg List.head? hcons)
            exact hij (Fin.ext hhead)
          have hper : ∀ i : Fin cs.length,
              (∏ p ∈ childFinset cs i, labelFactor (μ := μ) A (WitnessTree.mk a cs) p) =
                treeProd (μ := μ) A cs[i] := by
            intro i
            unfold childFinset
            rw [Finset.prod_image]
            · have hfac : ∀ q ∈ (vertices cs[i]).toFinset,
                  labelFactor (μ := μ) A (WitnessTree.mk a cs) (i.1 :: q) =
                    labelFactor (μ := μ) A cs[i] q := by
                intro q hq
                have hc : (WitnessTree.mk a cs).childrenOf[i.1]? = some cs[i] := by
                  simp [WitnessTree.childrenOf]
                exact labelFactor_cons (μ := μ) A hc q
              refine (Finset.prod_congr rfl (fun q hq => hfac q hq)).trans ?_
              have hsize : WitnessTree.size cs[i] < WitnessTree.size (WitnessTree.mk a cs) := by
                exact Nat.lt_of_le_of_lt (List.le_sum_of_mem
                  (List.mem_map.mpr ⟨cs[i], List.getElem_mem i.2, rfl⟩)) (by simp)
              exact ihm (WitnessTree.size cs[i]) (by simpa [hτ'] using hsize) cs[i] rfl
            · subst hτ'
              simp_all only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists,
                Finset.coe_univ, WitnessTree.size_mk, Fin.getElem_fin, List.coe_toFinset,
                List.cons.injEq, implies_true, Set.injOn_of_eq_iff_eq]
          rw [hcv]
          rw [Finset.prod_biUnion hdisj]
          rw [Finset.prod_congr rfl (fun i hi => hper i)]
          rw [← Fin.prod_ofFn (f := fun i : Fin cs.length => treeProd (μ := μ) A cs[i])]
          exact congrArg List.prod
            (List.ofFn_getElem_eq_map cs (fun c => treeProd (μ := μ) A c))
        rw [treeProd.eq_1]
        rw [vertices]
        change (∏ p ∈ ([] :: childVertices cs).toFinset,
            labelFactor (μ := μ) A (WitnessTree.mk a cs) p) =
          (μπ μ) (A a) * (cs.map (fun c => treeProd (μ := μ) A c)).prod
        rw [List.toFinset_cons]
        rw [Finset.prod_insert hnotmem]
        rw [hroot, hforest]

/-- The product of the vertex-condition measures over the vertices is the tree product. -/
private lemma prod_vertices_eq_treeProd {τ : WitnessTree ι} (hA : ∀ i, MeasurableSet (A i))
    (hN : WitnessTree.size τ ≤ N) :
    (∏ p ∈ (vertices τ).toFinset, μN N μ (vertexCond vbl A hdet hN p)) =
      treeProd (μ := μ) A τ := by
  classical
  have hfac : (∏ p ∈ (vertices τ).toFinset, μN N μ (vertexCond vbl A hdet hN p)) =
      ∏ p ∈ (vertices τ).toFinset, labelFactor (μ := μ) A τ p := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hcert : WitnessTree.ValidPath τ p :=
      Classical.choice ((mem_vertices_iff).mp (List.mem_toFinset.mp hp))
    rw [μN_vertexCond vbl A hdet hA hN hcert]
    change (μπ μ) (A (WitnessTree.labelAt hcert)) = labelFactor (μ := μ) A τ p
    unfold labelFactor
    rw [dif_pos ((mem_vertices_iff).mp (List.mem_toFinset.mp hp))]
    congr 1
    congr 1
    exact congrArg WitnessTree.labelOf
      (treeAt_eq_of_path hcert (Classical.choice ((mem_vertices_iff).mp (List.mem_toFinset.mp hp))))
  rw [hfac]
  exact prod_labelFactor_eq_treeProd (μ := μ) A τ

/-! ## 40.2: the measure of the τ-check equals the product of the event probabilities -/

theorem check_probability {τ : WitnessTree ι} (hA : ∀ i, MeasurableSet (A i))
    (hgood : WitnessTree.IsGood vbl τ) (hN : WitnessTree.size τ ≤ N) :
    μN N μ {ω | check vbl A hdet hN ω} = treeProd (μ := μ) A τ := by
  calc
    μN N μ {ω | check vbl A hdet hN ω}
        = μN N μ {ω | ∀ p (hp : WitnessTree.ValidPath τ p), Classical.choose
            (hdet (WitnessTree.labelAt hp)) (fun j : vbl (WitnessTree.labelAt hp) =>
              ω ⟨j, ⟨treeProfile vbl τ ↑j (p.length + 1),
                treeProfile_lt_succ_of_size_le (d := p.length) vbl hN⟩⟩)} := by
          rw [checkSet_eq_vertices vbl A hdet hN]
    _ = μN N μ (⋂ p : {p // p ∈ (vertices τ).toFinset}, vertexCond vbl A hdet hN p.1) := by
          rw [checkSet_eq_iInter vbl A hdet hN]
    _ = ∏ p ∈ (vertices τ).toFinset, μN N μ (vertexCond vbl A hdet hN p) :=
          μN_iInter_eq_prod vbl A hdet hA hgood hN
    _ = treeProd (μ := μ) A τ := prod_vertices_eq_treeProd vbl A hdet hA hN

end CheckProbability

/-! ## 40.3: occurrence_implies_check + coupling (the coupling lemma, survey B D18) -/

section OccurrenceCheck

variable {ι : Type u} {κ : Type u} [DecidableEq κ]
variable {Ω : κ → Type w} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hdet : ∀ i, DeterminedBy (A i) (vbl i))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-- The truncated log: entries below `q` are dropped (the bridge between the drop-fold
stage tree and `treeAt`). -/
private abbrev truncLog (q : ℕ) (Λ : ℕ → Option ι) (s : ℕ) : Option ι :=
  if q ≤ s then Λ s else none

/-! ## Fold-reduction glue (30.2's private `maxOption` is not writable from this file:
local defeq copies + the documented `eq_1`-rewrite technique) -/

/-- Local copy of 30.2's private `maxOption` (defeq; the private name does not resolve
across the file boundary). -/
private def mtMaxOption (m o : Option ℕ) : Option ℕ :=
  match m, o with
  | none, o => o
  | m, none => m
  | some a, some b => some (max a b)

/-- The `attachBelow` equation, re-expressed with the local `mtMaxOption` (definitionally
equal to 30.2's private `maxOption`, so `rfl` closes after the equation-lemma rewrite). -/
private lemma attachBelow_mk_treeElig [DecidableEq ι] (a : ℕ × ι) {s : ℕ} {i : ι}
    (cs : List (WitnessTree (ℕ × ι))) :
    WitnessTree.attachBelow (treeElig vbl) (s, i) (WitnessTree.mk a cs) =
      (let d := cs.foldl (fun m c => mtMaxOption m
        ((WitnessTree.deepestEligible (treeElig vbl) (s, i) c).map (· + 1))) none
      match d with
      | none =>
          if treeElig vbl (s, i) a then
            WitnessTree.mk a (cs ++ [WitnessTree.mk (s, i) []])
          else WitnessTree.mk a cs
      | some dd => WitnessTree.mk a (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs)) := by
  rw [WitnessTree.attachBelow.eq_1]
  rfl

/-- The `deepestEligible` equation, re-expressed with the local `mtMaxOption`. -/
private lemma deepestEligible_mk_treeElig [DecidableEq ι] (a : ℕ × ι) {s : ℕ} {i : ι}
    (cs : List (WitnessTree (ℕ × ι))) :
    WitnessTree.deepestEligible (treeElig vbl) (s, i) (WitnessTree.mk a cs) =
      (let d := cs.foldl (fun m c => mtMaxOption m
        ((WitnessTree.deepestEligible (treeElig vbl) (s, i) c).map (· + 1))) none
      if treeElig vbl (s, i) a then some (d.getD 0) else d) := by
  rw [WitnessTree.deepestEligible.eq_1]
  rfl

private theorem mtMaxOption_eq_none {m o : Option ℕ} :
    mtMaxOption m o = none ↔ m = none ∧ o = none := by
  cases m <;> cases o <;> simp [mtMaxOption]

private theorem mtMaxOption_eq_some {m o : Option ℕ} {d : ℕ} :
    mtMaxOption m o = some d ↔
      (m = some d ∨ o = some d) ∧ (∀ k, m = some k → k ≤ d) ∧
        (∀ k, o = some k → k ≤ d) := by
  cases m <;> cases o <;> simp [mtMaxOption] <;> omega

private theorem mtMaxOption_bound {m o : Option ℕ} {d : ℕ} :
    (∀ k, mtMaxOption m o = some k → k ≤ d) ↔
      (∀ k, m = some k → k ≤ d) ∧ (∀ k, o = some k → k ≤ d) := by
  cases m <;> cases o <;> simp [mtMaxOption]

private theorem exists_eq_or_imp_swap {α : Type*} {p q : α → Prop} {a : α} :
    (∃ x, (x = a ∨ p x) ∧ q x) ↔ q a ∨ ∃ x, p x ∧ q x := by
  constructor
  · rintro ⟨x, hx | hx, hq⟩
    · exact Or.inl (hx ▸ hq)
    · exact Or.inr ⟨x, hx, hq⟩
  · rintro (ha | ⟨x, hp, hq⟩)
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨x, Or.inr hp, hq⟩

private theorem forall_eq_or_imp_swap {α : Type*} {p q : α → Prop} {a : α} :
    (∀ x, (x = a ∨ p x) → q x) ↔ q a ∧ ∀ x, p x → q x := by
  constructor
  · intro h
    exact ⟨h a (Or.inl rfl), by intro x hp; exact h x (Or.inr hp)⟩
  · rintro ⟨ha, hp⟩ x (hx | hx)
    · simpa [hx] using ha
    · exact hp x hx

/-- The fold computes the maximum option: `some d` iff `d` is attained and bounds all. -/
private theorem foldl_mtMaxOption_eq_some {α : Type*} (g : α → Option ℕ) (cs : List α)
    (d : ℕ) :
    cs.foldl (fun m c => mtMaxOption m (g c)) none = some d ↔
      (∃ c ∈ cs, g c = some d) ∧ ∀ c ∈ cs, ∀ k, g c = some k → k ≤ d := by
  have hgen : ∀ m : Option ℕ, cs.foldl (fun m c => mtMaxOption m (g c)) m = some d ↔
      (m = some d ∨ ∃ c ∈ cs, g c = some d) ∧
      (∀ k, m = some k → k ≤ d) ∧
      (∀ c ∈ cs, ∀ k, g c = some k → k ≤ d) := by
    intro m
    induction cs generalizing m with
    | nil =>
        simp
        intro h k hk
        have hd : d = k := by simpa [h] using hk
        omega
    | cons c cs ih =>
        simp only [List.foldl_cons, List.mem_cons]
        rw [ih (mtMaxOption m (g c))]
        rw [mtMaxOption_eq_some, mtMaxOption_bound, exists_eq_or_imp_swap,
          forall_eq_or_imp_swap]
        tauto
  constructor
  · intro h
    rcases (hgen none).mp h with ⟨hmd, _, hcs⟩
    rcases hmd with h₁ | h₂
    · cases h₁
    · exact ⟨h₂, hcs⟩
  · intro h
    refine (hgen none).mpr ⟨Or.inr h.1, ?_, h.2⟩
    intro k hk
    cases hk

/-- The `+1` shift between a subtree's deepest eligible depth and its parent's. -/
private theorem Option_map_succ_eq_some {o : Option ℕ} {d : ℕ} :
    o.map (· + 1) = some d ↔ o = some (d - 1) ∧ 1 ≤ d := by
  cases o with
  | none =>
      constructor
      · intro h; cases h
      · intro h; cases h.1
  | some n =>
      simp
      omega

/-- The profile is zero when no counted vertex exists (the recursive-vs-paths bridge:
`treeProfile` is defined by recursion, not as a path cardinality). -/
private theorem treeProfile_eq_zero {τ : WitnessTree ι} {X : κ} {d : ℕ}
    (h : ∀ p, ∀ hp : WitnessTree.ValidPath τ p, d ≤ WitnessTree.depth τ p →
      X ∉ vbl (WitnessTree.labelAt hp)) :
    treeProfile vbl τ X d = 0 := by
  refine WitnessTree.rec
      (motive_1 := fun σ => ∀ d, (∀ p, ∀ hp : WitnessTree.ValidPath σ p,
        d ≤ WitnessTree.depth σ p → X ∉ vbl (WitnessTree.labelAt hp)) →
          treeProfile vbl σ X d = 0)
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ d, (∀ p, ∀ hp : WitnessTree.ValidPath c p,
        d ≤ WitnessTree.depth c p → X ∉ vbl (WitnessTree.labelAt hp)) →
          treeProfile vbl c X d = 0)
      ?_ ?_ ?_ τ d h
  · intro a cs ih d h
    cases d with
    | zero =>
        have hroot : X ∉ vbl a := by
          have h' := h [] .root
          simpa using h' (by simp)
        simp [treeProfile, hroot, List.sum_eq_zero_iff]
        intro c hc
        rcases List.mem_iff_getElem?.mp hc with ⟨i, hi⟩
        exact ih c hc 0 (fun p hp hle => by
          have h' := h (i :: p) (.cons i c (by simpa using hi) hp) (Nat.zero_le _)
          simpa using h')
    | succ d =>
        simp [treeProfile, List.sum_eq_zero_iff]
        intro c hc
        rcases List.mem_iff_getElem?.mp hc with ⟨i, hi⟩
        exact ih c hc d (fun p hp hle => by
          have h' := h (i :: p) (.cons i c (by simpa using hi) hp) (Nat.succ_le_succ hle)
          simpa using h')
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc' d hc''
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc d hc''
    · exact ihcs c' hc' d hc''

/-- The `attachInFirst` list step for the add lemma: with a child whose subtree contains
an eligible vertex at depth `dd - 1` (the hit), replacing it by its `attachBelow`-image
raises the summed profile at threshold `u` by exactly one (`u - 1 ≤ dd - 1` makes the hit
child's deepest witness serve the child IH at `u`). -/
private lemma attachInFirst_treeProfile_add [DecidableEq ι]
    (cs : List (WitnessTree (ℕ × ι))) (s : ℕ) (i : ι) (X : κ) (dd u : ℕ) :
    (∀ c ∈ cs, (∃ p, ∃ hp : WitnessTree.ValidPath c p,
        treeElig vbl (s, i) (WitnessTree.labelAt hp) ∧ u - 1 ≤ WitnessTree.depth c p) →
          treeProfile vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c)) X u =
            treeProfile vbl (forgetTime c) X u + 1) →
    (∃ c ∈ cs, WitnessTree.deepestEligible (treeElig vbl) (s, i) c = some (dd - 1)) →
    u - 1 ≤ dd - 1 →
      ((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map
        (fun c => treeProfile vbl (forgetTime c) X u)).sum =
        (cs.map (fun c => treeProfile vbl (forgetTime c) X u)).sum + 1 := by
  induction cs with
  | nil =>
      intro _ hE _
      rcases hE with ⟨c, hc, _⟩
      cases hc
  | cons c cs ih =>
      intro hIH hE hu
      by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s, i) c = some (dd - 1)
      · have hwit : ∃ p, ∃ hp : WitnessTree.ValidPath c p,
            treeElig vbl (s, i) (WitnessTree.labelAt hp) ∧ u - 1 ≤ WitnessTree.depth c p := by
          rcases ((WitnessTree.deepestEligible_eq_some (τ := c) (d := dd - 1)).mp hd).1 with
            ⟨p, hp, hdp, hpelig⟩
          exact ⟨p, hp, hpelig, by simpa [hdp] using hu⟩
        have hstep := hIH c (by simp) hwit
        simp [WitnessTree.attachInFirst, hd, hstep, List.sum_cons, Nat.add_assoc,
          Nat.add_comm]
      · have hE' : ∃ c' ∈ cs, WitnessTree.deepestEligible (treeElig vbl) (s, i) c' =
            some (dd - 1) := by
          rcases hE with ⟨c', hc', hdeep⟩
          rw [List.mem_cons] at hc'
          rcases hc' with rfl | hc'
          · exact (hd hdeep).elim
          · exact ⟨c', hc', hdeep⟩
        have hrec := ih (fun c' hc' => hIH c' (by simp [hc'])) hE' hu
        simp [WitnessTree.attachInFirst, hd, hrec, List.sum_cons, Nat.add_comm,
          Nat.add_left_comm]

/-- One insertion step: an entry whose event contains `X` attaches below a max-depth
eligible vertex — with an eligible vertex at depth ≥ `d`, the new vertex has depth ≥ d + 1
and raises the profile at threshold `d + 1` by exactly one. -/
private theorem attachBelow_treeProfile_add [DecidableEq ι] {σ : WitnessTree (ℕ × ι)}
    {s : ℕ} {i : ι} {X : κ} {d : ℕ}
    (hd : ∃ p, ∃ hp : WitnessTree.ValidPath σ p,
      treeElig vbl (s, i) (WitnessTree.labelAt hp) ∧ d ≤ WitnessTree.depth σ p)
    (hX : X ∈ vbl i) :
    treeProfile vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) σ)) X (d + 1) =
      treeProfile vbl (forgetTime σ) X (d + 1) + 1 := by
  refine WitnessTree.rec
      (motive_1 := fun σ => ∀ t, (∃ p, ∃ hp : WitnessTree.ValidPath σ p,
        treeElig vbl (s, i) (WitnessTree.labelAt hp) ∧ t - 1 ≤ WitnessTree.depth σ p) →
          treeProfile vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) σ)) X t =
            treeProfile vbl (forgetTime σ) X t + 1)
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ t, (∃ p, ∃ hp : WitnessTree.ValidPath c p,
        treeElig vbl (s, i) (WitnessTree.labelAt hp) ∧ t - 1 ≤ WitnessTree.depth c p) →
          treeProfile vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c)) X t =
            treeProfile vbl (forgetTime c) X t + 1)
      ?_ ?_ ?_ σ (d + 1) (by
        rcases hd with ⟨p, hp, hpelig, hdep⟩
        exact ⟨p, hp, hpelig, by simpa using hdep⟩)
  · intro a cs ih t h
    cases hfold : cs.foldl (fun m c => mtMaxOption m
        ((WitnessTree.deepestEligible (treeElig vbl) (s, i) c).map (· + 1))) none with
    | none =>
        rw [attachBelow_mk_treeElig (a := a) (cs := cs)]
        simp only [hfold]
        by_cases ha : treeElig vbl (s, i) a
        · simp [ha]
          have hdeep : WitnessTree.deepestEligible (treeElig vbl) (s, i) (WitnessTree.mk a cs) =
              some 0 := by
            rw [deepestEligible_mk_treeElig (a := a) (cs := cs)]
            simp [hfold, ha]
          have ht01 : t = 0 ∨ t = 1 := by
            rcases ((WitnessTree.deepestEligible_eq_some (τ := WitnessTree.mk a cs) (d := 0)).mp
              hdeep).2 with hmax
            rcases h with ⟨p, hp, hpelig, hdep⟩
            have hle : t - 1 ≤ 0 := le_trans hdep (hmax p hp hpelig)
            omega
          rcases ht01 with rfl | rfl
          · simp [forgetTime, treeProfile, List.map_append, List.sum_append, hX,
              Nat.add_assoc]
          · simp [forgetTime, treeProfile, List.map_append, List.sum_append, hX]
        · rcases h with ⟨p, hp, hpelig, _⟩
          have hnone : WitnessTree.deepestEligible (treeElig vbl) (s, i) (WitnessTree.mk a cs) =
              none := by
            rw [deepestEligible_mk_treeElig (a := a) (cs := cs)]
            simp [hfold, ha]
          have hnone' := (WitnessTree.deepestEligible_eq_none (τ := WitnessTree.mk a cs)).mp hnone
          exact (hnone' p hp hpelig).elim
    | some dd =>
        rw [attachBelow_mk_treeElig (a := a) (cs := cs)]
        simp only [hfold]
        have hdeep : WitnessTree.deepestEligible (treeElig vbl) (s, i) (WitnessTree.mk a cs) =
            some dd := by
          rw [deepestEligible_mk_treeElig (a := a) (cs := cs)]
          simp [hfold]
        have hdd_ge : t - 1 ≤ dd := by
          rcases ((WitnessTree.deepestEligible_eq_some (τ := WitnessTree.mk a cs) (d := dd)).mp
            hdeep).2 with hmax
          rcases h with ⟨p, hp, hpelig, hdep⟩
          exact le_trans hdep (hmax p hp hpelig)
        have hEligChild : ∃ c ∈ cs, WitnessTree.deepestEligible (treeElig vbl) (s, i) c =
            some (dd - 1) := by
          have hfold' := (foldl_mtMaxOption_eq_some
            (fun c => (WitnessTree.deepestEligible (treeElig vbl) (s, i) c).map (· + 1))
            cs dd).mp hfold
          rcases hfold'.1 with ⟨c, hc, hm⟩
          rcases (Option_map_succ_eq_some
            (o := WitnessTree.deepestEligible (treeElig vbl) (s, i) c) (d := dd)).mp hm with
            ⟨hdeep', _⟩
          exact ⟨c, hc, hdeep'⟩
        cases t with
        | zero =>
            have hsum : (List.map ((fun c => treeProfile vbl c X 0) ∘ forgetTime)
                (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs)).sum =
                (List.map ((fun c => treeProfile vbl c X 0) ∘ forgetTime) cs).sum + 1 := by
              exact attachInFirst_treeProfile_add vbl cs s i X dd 0
                (fun c hc => ih c hc 0) hEligChild (by omega)
            simp [forgetTime, treeProfile, hsum, Nat.add_assoc]
        | succ t =>
            have hsum : (List.map ((fun c => treeProfile vbl c X t) ∘ forgetTime)
                (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs)).sum =
                (List.map ((fun c => treeProfile vbl c X t) ∘ forgetTime) cs).sum + 1 := by
              exact attachInFirst_treeProfile_add vbl cs s i X dd t
                (fun c hc => ih c hc t) hEligChild (by omega)
            simp [forgetTime, treeProfile, hsum]
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc' t hc''
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc t hc''
    · exact ihcs c' hc' t hc''

/-- The `attachInFirst` list step for the not-mem lemma: replacing one child by its
`attachBelow`-image (with the same profile, by hypothesis) leaves the summed profile
unchanged — no side condition on the fold. -/
private lemma attachInFirst_treeProfile_of_not_mem [DecidableEq ι]
    (cs : List (WitnessTree (ℕ × ι))) (s : ℕ) (i : ι) (X : κ) (dd u : ℕ) :
    (∀ c ∈ cs, treeProfile vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c))
      X u = treeProfile vbl (forgetTime c) X u) →
      ((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map
        (fun c => treeProfile vbl (forgetTime c) X u)).sum =
        (cs.map (fun c => treeProfile vbl (forgetTime c) X u)).sum := by
  induction cs with
  | nil => intro _; simp [WitnessTree.attachInFirst]
  | cons c cs ih =>
      intro hIH
      by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s, i) c = some (dd - 1)
      · simp [WitnessTree.attachInFirst, hd, hIH c (by simp)]
      · simp [WitnessTree.attachInFirst, hd, ih (fun c' hc' => hIH c' (by simp [hc']))]

/-- One insertion step: an entry whose event does not contain `X` leaves the profile at
threshold `d + 1` unchanged. -/
private theorem attachBelow_treeProfile_of_not_mem [DecidableEq ι] {σ : WitnessTree (ℕ × ι)}
    {s : ℕ} {i : ι} {X : κ} {d : ℕ} (hX : X ∉ vbl i) :
    treeProfile vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) σ)) X (d + 1) =
      treeProfile vbl (forgetTime σ) X (d + 1) := by
  refine WitnessTree.rec
      (motive_1 := fun σ => ∀ t, treeProfile vbl
        (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) σ)) X t =
          treeProfile vbl (forgetTime σ) X t)
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ t, treeProfile vbl
        (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c)) X t =
          treeProfile vbl (forgetTime c) X t)
      ?_ ?_ ?_ σ (d + 1)
  · intro a cs ih t
    cases hfold : cs.foldl (fun m c => mtMaxOption m
        ((WitnessTree.deepestEligible (treeElig vbl) (s, i) c).map (· + 1))) none with
    | none =>
        rw [attachBelow_mk_treeElig (a := a) (cs := cs)]
        simp only [hfold]
        by_cases ha : treeElig vbl (s, i) a
        · simp [ha]
          cases t with
          | zero =>
              simp [forgetTime, treeProfile, List.map_append, List.sum_append, hX]
          | succ t =>
              have hleaf : treeProfile vbl (WitnessTree.mk i []) X t = 0 := by
                cases t with
                | zero => simp [treeProfile, hX]
                | succ t => simp [treeProfile]
              simp [forgetTime, treeProfile, List.map_append, List.sum_append, hleaf]
        · simp [ha]
    | some dd =>
        rw [attachBelow_mk_treeElig (a := a) (cs := cs)]
        simp only [hfold]
        cases t with
        | zero =>
            have hsum : (List.map ((fun c => treeProfile vbl c X 0) ∘ forgetTime)
                (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs)).sum =
                (List.map ((fun c => treeProfile vbl c X 0) ∘ forgetTime) cs).sum := by
              exact attachInFirst_treeProfile_of_not_mem vbl cs s i X dd 0 (fun c hc => ih c hc 0)
            simp [forgetTime, treeProfile, hsum]
        | succ t =>
            have hsum : (List.map ((fun c => treeProfile vbl c X t) ∘ forgetTime)
                (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs)).sum =
                (List.map ((fun c => treeProfile vbl c X t) ∘ forgetTime) cs).sum := by
              exact attachInFirst_treeProfile_of_not_mem vbl cs s i X dd t (fun c hc => ih c hc t)
            simp [forgetTime, treeProfile, hsum]
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc' t
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc t
    · exact ihcs c' hc' t

/-- Path/label stability through the reverse-scan fold (forward direction): old vertices
keep their paths and labels through all later insertions (30.2's (b)). -/
private theorem labelAt_foldr [DecidableEq ι] (Λ : ℕ → Option ι) (l : List ℕ)
    (σ : WitnessTree (ℕ × ι)) {p : List ℕ} (hp : WitnessTree.ValidPath σ p) :
    ∃ hp' : WitnessTree.ValidPath (l.foldr (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ) p,
      WitnessTree.labelAt hp' = WitnessTree.labelAt hp := by
  let g : ℕ → WitnessTree (ℕ × ι) → WitnessTree (ℕ × ι) :=
    fun s τ => match Λ s with
      | none => τ
      | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
  change ∃ hp' : WitnessTree.ValidPath (l.foldr g σ) p,
    WitnessTree.labelAt hp' = WitnessTree.labelAt hp
  induction l with
  | nil => exact ⟨hp, rfl⟩
  | cons s l ih =>
      rcases ih with ⟨hp₁, hl₁⟩
      cases hΛ : Λ s with
      | none =>
          have heq : (s :: l).foldr g σ = l.foldr g σ := by
            simp [g, List.foldr_cons, hΛ]
          refine ⟨cast (congrArg (fun x => WitnessTree.ValidPath x p) heq.symm) hp₁, ?_⟩
          exact (labelAt_cast (τ := l.foldr g σ) (τ' := (s :: l).foldr g σ)
            (h := heq.symm) (p := p) hp₁).trans hl₁
      | some i =>
          rcases WitnessTree.labelAt_attachBelow (elig := treeElig vbl) (i := (s, i))
              (τ := l.foldr g σ) (p := p) hp₁ with ⟨hp₂, hl₂⟩
          have heq : (s :: l).foldr g σ =
              WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ) := by
            simp [g, List.foldr_cons, hΛ]
          refine ⟨cast (congrArg (fun x => WitnessTree.ValidPath x p) heq.symm) hp₂, ?_⟩
          exact (labelAt_cast (τ := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
            (τ' := (s :: l).foldr g σ) (h := heq.symm) (p := p) hp₂).trans (hl₂.trans hl₁)

/-- The reverse-stability (peel): a path whose label time differs from every scanned entry
survives the fold backwards. -/
private theorem validPath_foldr_rev [DecidableEq ι] (Λ : ℕ → Option ι) (l : List ℕ)
    (σ : WitnessTree (ℕ × ι)) {p : List ℕ}
    (hp : WitnessTree.ValidPath (l.foldr (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ) p)
    (hneq : ∀ s₁ ∈ l, s₁ ≠ (WitnessTree.labelAt hp).1) :
    ∃ hp' : WitnessTree.ValidPath σ p, WitnessTree.labelAt hp' = WitnessTree.labelAt hp := by
  let g : ℕ → WitnessTree (ℕ × ι) → WitnessTree (ℕ × ι) :=
    fun s τ => match Λ s with
      | none => τ
      | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
  change WitnessTree.ValidPath (l.foldr g σ) p at hp
  change ∀ s₁ ∈ l, s₁ ≠ (WitnessTree.labelAt hp).1 at hneq
  induction l with
  | nil => exact ⟨hp, rfl⟩
  | cons s l ih =>
      cases hΛ : Λ s with
      | none =>
          have heq : (s :: l).foldr g σ = l.foldr g σ := by
            simp [g, List.foldr_cons, hΛ]
          let hp' : WitnessTree.ValidPath (l.foldr g σ) p :=
            cast (congrArg (fun x => WitnessTree.ValidPath x p) heq) hp
          have hneq' : ∀ s₁ ∈ l, s₁ ≠ (WitnessTree.labelAt hp').1 := by
            intro s₁ hs₁ h
            exact hneq s₁ (by simp [hs₁])
              (h.trans (congrArg Prod.fst (labelAt_cast (τ := (s :: l).foldr g σ)
                (τ' := l.foldr g σ) (h := heq) (p := p) hp)))
          rcases ih hp' hneq' with ⟨hp'', hl⟩
          refine ⟨hp'', hl.trans (labelAt_cast (τ := (s :: l).foldr g σ)
            (τ' := l.foldr g σ) (h := heq) (p := p) hp)⟩
      | some i =>
          by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s, i) (l.foldr g σ) = none
          · have hab : WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ) =
                l.foldr g σ :=
              WitnessTree.attachBelow_eq_self_of_deepestEligible_none hd
            have heq : (s :: l).foldr g σ = l.foldr g σ := by
              simp [g, List.foldr_cons, hΛ, hab]
            let hp' : WitnessTree.ValidPath (l.foldr g σ) p :=
              cast (congrArg (fun x => WitnessTree.ValidPath x p) heq) hp
            have hneq' : ∀ s₁ ∈ l, s₁ ≠ (WitnessTree.labelAt hp').1 := by
              intro s₁ hs₁ h
              exact hneq s₁ (by simp [hs₁])
                (h.trans (congrArg Prod.fst (labelAt_cast (τ := (s :: l).foldr g σ)
                  (τ' := l.foldr g σ) (h := heq) (p := p) hp)))
            rcases ih hp' hneq' with ⟨hp'', hl⟩
            refine ⟨hp'', hl.trans (labelAt_cast (τ := (s :: l).foldr g σ)
              (τ' := l.foldr g σ) (h := heq) (p := p) hp)⟩
          · rcases Option.ne_none_iff_exists.mp hd with ⟨dd, hdd⟩
            have heqA : (s :: l).foldr g σ =
                WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ) := by
              simp [g, List.foldr_cons, hΛ]
            let hpA : WitnessTree.ValidPath
                (WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ)) p :=
              cast (congrArg (fun x => WitnessTree.ValidPath x p) heqA) hp
            rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s, i))
                (τ := l.foldr g σ) (h := hdd.symm) (q := p) hpA with hOld | hNew
            · rcases hOld with ⟨hp₀, hl₀⟩
              have hneq' : ∀ s₁ ∈ l, s₁ ≠ (WitnessTree.labelAt hp₀).1 := by
                intro s₁ hs₁ h
                exact hneq s₁ (by simp [hs₁])
                  (h.trans (congrArg Prod.fst (hl₀.trans (labelAt_cast (τ := (s :: l).foldr g σ)
                    (τ' := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
                    (h := heqA) (p := p) hp))))
              rcases ih hp₀ hneq' with ⟨hp'', hl⟩
              refine ⟨hp'', hl.trans (hl₀.trans (labelAt_cast (τ := (s :: l).foldr g σ)
                (τ' := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
                (h := heqA) (p := p) hp))⟩
            · exfalso
              have hltime : (WitnessTree.labelAt hpA).1 = s := congrArg Prod.fst hNew.1
              have hlA : WitnessTree.labelAt hpA = WitnessTree.labelAt hp :=
                labelAt_cast (τ := (s :: l).foldr g σ)
                  (τ' := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
                  (h := heqA) (p := p) hp
              exact hneq s (by simp) (hltime.symm.trans (congrArg Prod.fst hlA))

/-- The main fold induction (both directions of the bijection at once, additive form): for
a vertex of `σ`, the number of scanned genuine entries whose event contains `X` plus the
profile of `σ` at the vertex's threshold equals the profile of the scanned tree. -/
private theorem foldr_resample_profile_add [DecidableEq ι] (Λ : ℕ → Option ι) :
    ∀ l : List ℕ, ∀ σ : WitnessTree (ℕ × ι),
      ∀ p, ∀ hp : WitnessTree.ValidPath σ p, ∀ X : κ,
        X ∈ vbl (WitnessTree.labelAt hp).2 →
        (((l.filter (fun s₁ => match Λ s₁ with
            | none => false
            | some i => decide (X ∈ vbl i))).length +
              treeProfile vbl (forgetTime σ) X (WitnessTree.depth σ p + 1) : ℕ) =
          treeProfile vbl (forgetTime (l.foldr (fun s τ => match Λ s with
            | none => τ
            | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ)) X
            (WitnessTree.depth σ p + 1)) := by
  let g : ℕ → WitnessTree (ℕ × ι) → WitnessTree (ℕ × ι) :=
    fun s τ => match Λ s with
      | none => τ
      | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
  change ∀ l : List ℕ, ∀ σ : WitnessTree (ℕ × ι),
      ∀ p, ∀ hp : WitnessTree.ValidPath σ p, ∀ X : κ,
        X ∈ vbl (WitnessTree.labelAt hp).2 →
        (((l.filter (fun s₁ => match Λ s₁ with
            | none => false
            | some i => decide (X ∈ vbl i))).length +
              treeProfile vbl (forgetTime σ) X (WitnessTree.depth σ p + 1) : ℕ) =
          treeProfile vbl (forgetTime (l.foldr g σ)) X (WitnessTree.depth σ p + 1))
  intro l
  induction l with
  | nil =>
      intro σ p hp X hX
      simp
  | cons s l ih =>
      intro σ p hp X hX
      cases hΛ : Λ s with
      | none =>
          rw [List.foldr_cons]
          simp [g, hΛ, ih σ p hp X hX]
      | some i =>
          by_cases hXi : X ∈ vbl i
          · have hprof : treeProfile vbl (forgetTime
                  (WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))) X
                (WitnessTree.depth σ p + 1) =
                treeProfile vbl (forgetTime (l.foldr g σ)) X (WitnessTree.depth σ p + 1) + 1 :=
              attachBelow_treeProfile_add vbl
                (by
                  rcases labelAt_foldr vbl Λ l σ hp with ⟨hp', hl⟩
                  refine ⟨p, hp', ?_, ?_⟩
                  · simpa [hl] using (Or.inr ⟨X, Finset.mem_inter.mpr ⟨hXi, hX⟩⟩ :
                      treeElig vbl (s, i) (WitnessTree.labelAt hp))
                  · simp [WitnessTree.depth])
                hXi
            rw [List.foldr_cons]
            simp [g, hΛ, hXi]
            have hih := ih σ p hp X hX
            calc
              (l.filter (fun s₁ => match Λ s₁ with
                  | none => false
                  | some i => decide (X ∈ vbl i))).length + 1 +
                    treeProfile vbl (forgetTime σ) X (WitnessTree.depth σ p + 1) =
                  (l.filter (fun s₁ => match Λ s₁ with
                    | none => false
                    | some i => decide (X ∈ vbl i))).length +
                    treeProfile vbl (forgetTime σ) X (WitnessTree.depth σ p + 1) + 1 := by
                    omega
              _ = treeProfile vbl (forgetTime (l.foldr g σ)) X
                    (WitnessTree.depth σ p + 1) + 1 := by
                    rw [hih]
              _ = treeProfile vbl (forgetTime
                    (WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))) X
                    (WitnessTree.depth σ p + 1) := by
                    rw [hprof]
          · have hprof : treeProfile vbl (forgetTime
                  (WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))) X
                (WitnessTree.depth σ p + 1) =
                treeProfile vbl (forgetTime (l.foldr g σ)) X (WitnessTree.depth σ p + 1) :=
              attachBelow_treeProfile_of_not_mem vbl hXi
            rw [List.foldr_cons]
            simp [g, hΛ, hXi, hprof, ih σ p hp X hX]

/-- The fold invariant for the genuineness/time facts (7–9): every vertex of the folded
tree either was inserted by the fold at its label time `s` (so `Λ s` is genuine and
`s ∈ l`), or is an old vertex of the seed `σ` with the same label. -/
private theorem foldr_label_spec [DecidableEq ι] (Λ : ℕ → Option ι) (l : List ℕ)
    (σ : WitnessTree (ℕ × ι)) :
    ∀ p, ∀ hp : WitnessTree.ValidPath
        (l.foldr (fun s τ => match Λ s with
          | none => τ
          | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ) p,
      (Λ (WitnessTree.labelAt hp).1 = some (WitnessTree.labelAt hp).2 ∧
          (WitnessTree.labelAt hp).1 ∈ l) ∨
        ∃ hp₀ : WitnessTree.ValidPath σ p,
          WitnessTree.labelAt hp₀ = WitnessTree.labelAt hp := by
  let g : ℕ → WitnessTree (ℕ × ι) → WitnessTree (ℕ × ι) :=
    fun s τ => match Λ s with
      | none => τ
      | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
  change ∀ p, ∀ hp : WitnessTree.ValidPath (l.foldr g σ) p,
      (Λ (WitnessTree.labelAt hp).1 = some (WitnessTree.labelAt hp).2 ∧
          (WitnessTree.labelAt hp).1 ∈ l) ∨
        ∃ hp₀ : WitnessTree.ValidPath σ p, WitnessTree.labelAt hp₀ = WitnessTree.labelAt hp
  intro p hp
  induction l generalizing p with
  | nil =>
      right
      exact ⟨hp, rfl⟩
  | cons s l ih =>
      cases hΛ : Λ s with
      | none =>
          have heq : (s :: l).foldr g σ = l.foldr g σ := by
            simp [g, List.foldr_cons, hΛ]
          let hp₁ : WitnessTree.ValidPath (l.foldr g σ) p :=
            cast (congrArg (fun x => WitnessTree.ValidPath x p) heq) hp
          rcases ih p hp₁ with hG | hS
          · left
            constructor
            · have h' := hG.1
              have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                labelAt_cast (τ := (s :: l).foldr g σ) (τ' := l.foldr g σ)
                  (h := heq) (p := p) hp
              simpa [hc] using h'
            · have h' := hG.2
              have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                labelAt_cast (τ := (s :: l).foldr g σ) (τ' := l.foldr g σ)
                  (h := heq) (p := p) hp
              have h'₁ : (WitnessTree.labelAt hp).1 ∈ l := by simpa [hc] using h'
              exact List.mem_cons_of_mem s h'₁
          · right
            rcases hS with ⟨hp₀, hl₀⟩
            refine ⟨hp₀, ?_⟩
            have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
              labelAt_cast (τ := (s :: l).foldr g σ) (τ' := l.foldr g σ)
                (h := heq) (p := p) hp
            exact hl₀.trans hc
      | some i =>
          by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s, i) (l.foldr g σ) = none
          · have hab : WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ) =
                l.foldr g σ :=
              WitnessTree.attachBelow_eq_self_of_deepestEligible_none hd
            have heq : (s :: l).foldr g σ = l.foldr g σ := by
              simp [g, List.foldr_cons, hΛ, hab]
            let hp₁ : WitnessTree.ValidPath (l.foldr g σ) p :=
              cast (congrArg (fun x => WitnessTree.ValidPath x p) heq) hp
            rcases ih p hp₁ with hG | hS
            · left
              constructor
              · have h' := hG.1
                have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                  labelAt_cast (τ := (s :: l).foldr g σ) (τ' := l.foldr g σ)
                    (h := heq) (p := p) hp
                simpa [hc] using h'
              · have h' := hG.2
                have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                  labelAt_cast (τ := (s :: l).foldr g σ) (τ' := l.foldr g σ)
                    (h := heq) (p := p) hp
                have h'₁ : (WitnessTree.labelAt hp).1 ∈ l := by simpa [hc] using h'
                exact List.mem_cons_of_mem s h'₁
            · right
              rcases hS with ⟨hp₀, hl₀⟩
              refine ⟨hp₀, ?_⟩
              have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                labelAt_cast (τ := (s :: l).foldr g σ) (τ' := l.foldr g σ)
                  (h := heq) (p := p) hp
              exact hl₀.trans hc
          · rcases Option.ne_none_iff_exists.mp hd with ⟨dd, hdd⟩
            have heqA : (s :: l).foldr g σ =
                WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ) := by
              simp [g, List.foldr_cons, hΛ]
            let hpA : WitnessTree.ValidPath
                (WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ)) p :=
              cast (congrArg (fun x => WitnessTree.ValidPath x p) heqA) hp
            rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s, i))
                (τ := l.foldr g σ) (h := hdd.symm) (q := p) hpA with hOld | hNew
            · rcases hOld with ⟨hp₁, hl₁⟩
              rcases ih p hp₁ with hG | hS
              · left
                constructor
                · have h' := hG.1
                  have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                    hl₁.trans (labelAt_cast (τ := (s :: l).foldr g σ)
                      (τ' := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
                      (h := heqA) (p := p) hp)
                  simpa [hc] using h'
                · have h' := hG.2
                  have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                    hl₁.trans (labelAt_cast (τ := (s :: l).foldr g σ)
                      (τ' := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
                      (h := heqA) (p := p) hp)
                  have h'₁ : (WitnessTree.labelAt hp).1 ∈ l := by simpa [hc] using h'
                  exact List.mem_cons_of_mem s h'₁
              · right
                rcases hS with ⟨hp₀, hl₀⟩
                refine ⟨hp₀, ?_⟩
                have hc : WitnessTree.labelAt hp₁ = WitnessTree.labelAt hp :=
                  hl₁.trans (labelAt_cast (τ := (s :: l).foldr g σ)
                    (τ' := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
                    (h := heqA) (p := p) hp)
                exact hl₀.trans hc
            · left
              have hlA : WitnessTree.labelAt hpA = WitnessTree.labelAt hp :=
                labelAt_cast (τ := (s :: l).foldr g σ)
                  (τ' := WitnessTree.attachBelow (treeElig vbl) (s, i) (l.foldr g σ))
                  (h := heqA) (p := p) hp
              have hlab : WitnessTree.labelAt hp = (s, i) := hlA.symm.trans hNew.1
              constructor
              · have htime : (WitnessTree.labelAt hp).1 = s := congrArg Prod.fst hlab
                have hidx : (WitnessTree.labelAt hp).2 = i := congrArg Prod.snd hlab
                rw [htime, hidx]
                exact hΛ
              · have htime : (WitnessTree.labelAt hp).1 = s := congrArg Prod.fst hlab
                rw [htime]
                exact List.mem_cons_self

/-- Non-root vertices of a constructed tree come from genuine entries. -/
private theorem treeAt_label_of_lt [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι}
    {t : ℕ}
    {p : List ℕ} (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p)
    (hlt : (WitnessTree.labelAt hp).1 < t) :
    Λ (WitnessTree.labelAt hp).1 = some (WitnessTree.labelAt hp).2 := by
  let σ : WitnessTree (ℕ × ι) := match Λ t with
    | none => WitnessTree.mk (t, default) []
    | some i => WitnessTree.mk (t, i) []
  have htree : treeAt vbl Λ t =
      (List.range t).foldr (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ := by
    unfold treeAt
    rfl
  have hc : WitnessTree.labelAt
      (cast (congrArg (fun x => WitnessTree.ValidPath x p) htree) hp) =
      WitnessTree.labelAt hp :=
    labelAt_cast (τ := treeAt vbl Λ t) (τ' := (List.range t).foldr
      (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ) (h := htree) (p := p) hp
  rcases foldr_label_spec vbl Λ (List.range t) σ p
      (cast (congrArg (fun x => WitnessTree.ValidPath x p) htree) hp) with hG | hS
  · have h' := hG.1
    simpa [hc] using h'
  · rcases hS with ⟨hp₀, hl⟩
    cases hp₀ with
    | root =>
        have h0 : (WitnessTree.labelAt (.root : WitnessTree.ValidPath σ [])).1 = t := by
          unfold σ
          cases hΛt : Λ t <;> simp
        have htime : (WitnessTree.labelAt hp).1 = t := by simpa only [hl, hc] using h0
        omega
    | cons j c hcvp hvp =>
        unfold σ at hcvp
        cases hΛt : Λ t <;> simp [hΛt] at hcvp

/-- All vertex times of a constructed tree are at most `t`. -/
private theorem treeAt_label_time_le [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι}
    {t : ℕ}
    {p : List ℕ} (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p) :
    (WitnessTree.labelAt hp).1 ≤ t := by
  let σ : WitnessTree (ℕ × ι) := match Λ t with
    | none => WitnessTree.mk (t, default) []
    | some i => WitnessTree.mk (t, i) []
  have htree : treeAt vbl Λ t =
      (List.range t).foldr (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ := by
    unfold treeAt
    rfl
  have hc : WitnessTree.labelAt
      (cast (congrArg (fun x => WitnessTree.ValidPath x p) htree) hp) =
      WitnessTree.labelAt hp :=
    labelAt_cast (τ := treeAt vbl Λ t) (τ' := (List.range t).foldr
      (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ) (h := htree) (p := p) hp
  rcases foldr_label_spec vbl Λ (List.range t) σ p
      (cast (congrArg (fun x => WitnessTree.ValidPath x p) htree) hp) with hG | hS
  · have h' := hG.2
    have hmem : (WitnessTree.labelAt hp).1 ∈ List.range t := by simpa [hc] using h'
    exact Nat.le_of_lt ((List.mem_range.mp hmem))
  · rcases hS with ⟨hp₀, hl⟩
    cases hp₀ with
    | root =>
        have h0 : (WitnessTree.labelAt (.root : WitnessTree.ValidPath σ [])).1 = t := by
          unfold σ
          cases hΛt : Λ t <;> simp
        have htime : (WitnessTree.labelAt hp).1 = t := by simpa only [hl, hc] using h0
        omega
    | cons j c hcvp hvp =>
        unfold σ at hcvp
        cases hΛt : Λ t <;> simp [hΛt] at hcvp

/-- For the truncated log, all vertex times are at least `q`. -/
private theorem treeAt_truncLog_label_time_ge [DecidableEq ι] [Inhabited ι]
    {Λ : ℕ → Option ι} {q t : ℕ} (hq : q ≤ t) {p : List ℕ}
    (hp : WitnessTree.ValidPath (treeAt vbl (truncLog q Λ) t) p) :
    q ≤ (WitnessTree.labelAt hp).1 := by
  let σ : WitnessTree (ℕ × ι) := match truncLog q Λ t with
    | none => WitnessTree.mk (t, default) []
    | some i => WitnessTree.mk (t, i) []
  have htree : treeAt vbl (truncLog q Λ) t =
      (List.range t).foldr (fun s τ => match truncLog q Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ := by
    unfold treeAt
    rfl
  have hc : WitnessTree.labelAt
      (cast (congrArg (fun x => WitnessTree.ValidPath x p) htree) hp) =
      WitnessTree.labelAt hp :=
    labelAt_cast (τ := treeAt vbl (truncLog q Λ) t) (τ' := (List.range t).foldr
      (fun s τ => match truncLog q Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ) (h := htree) (p := p) hp
  rcases foldr_label_spec vbl (truncLog q Λ) (List.range t) σ p
      (cast (congrArg (fun x => WitnessTree.ValidPath x p) htree) hp) with hG | hS
  · have hg := hG.1
    have hg' : truncLog q Λ (WitnessTree.labelAt hp).1 = some (WitnessTree.labelAt hp).2 := by
      simpa [hc] using hg
    by_cases hqe : q ≤ (WitnessTree.labelAt hp).1
    · exact hqe
    · have hnone : truncLog q Λ (WitnessTree.labelAt hp).1 = none := by
        unfold truncLog
        rw [if_neg hqe]
      rw [hnone] at hg'
      exact (Option.some_ne_none _ hg'.symm).elim
  · rcases hS with ⟨hp₀, hl⟩
    cases hp₀ with
    | root =>
        have h0 : (WitnessTree.labelAt (.root : WitnessTree.ValidPath σ [])).1 = t := by
          unfold σ
          cases hΛt : truncLog q Λ t <;> simp
        have htime : (WitnessTree.labelAt hp).1 = t := by simpa only [hl, hc] using h0
        omega
    | cons j c hcvp hvp =>
        unfold σ at hcvp
        cases hΛt : truncLog q Λ t <;> simp [hΛt] at hcvp

/-- Membership in a dropped prefix of `range t` is at least the drop index. -/
private lemma mem_drop_range {t q s : ℕ} (h : s ∈ (List.range t).drop q) : q ≤ s := by
  rcases List.mem_iff_getElem?.mp h with ⟨j, hj⟩
  have hj' : (List.range t)[q + j]? = some s := by
    simpa [List.getElem?_drop] using hj
  rcases (List.getElem?_eq_some_iff.mp hj') with ⟨hlt, hget⟩
  have hval : q + j = s := by
    simpa using hget
  omega

/-- The fold over `range q` of the truncated-log step is the identity: every scanned entry
is below `q`, so its truncation is `none`. -/
private lemma foldr_range_truncLog_id [DecidableEq ι] [Inhabited ι] (Λ : ℕ → Option ι)
    (q : ℕ) :
    ∀ X : WitnessTree (ℕ × ι),
      (List.range q).foldr (fun s τ => match truncLog q Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) X = X := by
  intro X
  induction q with
  | zero => simp
  | succ q ih =>
      rw [List.range_succ, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      have hstep : (match truncLog (q + 1) Λ q with
          | none => X
          | some i => WitnessTree.attachBelow (treeElig vbl) (q, i) X) = X := by
        unfold truncLog
        rw [if_neg (show ¬ q + 1 ≤ q from by omega)]
      rw [hstep]
      have hext : (List.range q).foldr (fun s τ => match truncLog (q + 1) Λ s with
          | none => τ
          | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) X =
          (List.range q).foldr (fun s τ => match truncLog q Λ s with
            | none => τ
            | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) X := by
        refine List.foldr_ext _ _ X ?_
        intro s hs τ
        have hs' : s < q := (List.mem_range.mp hs)
        have h1 : truncLog (q + 1) Λ s = none := by
          unfold truncLog
          rw [if_neg (show ¬ q + 1 ≤ s from by omega)]
        have h2 : truncLog q Λ s = none := by
          unfold truncLog
          rw [if_neg (show ¬ q ≤ s from by omega)]
        simp [h1, h2]
      rw [hext]
      exact ih

/-- The stage tree after processing the entries ≥ q is the tree built from the truncated
log (entries below `q` are no-ops in the fold). -/
private theorem treeAt_truncLog_eq_drop_fold [DecidableEq ι] [Inhabited ι]
    {Λ : ℕ → Option ι}
    {q t : ℕ} (hq : q ≤ t) :
    treeAt vbl (truncLog q Λ) t =
      ((List.range t).drop q).foldr (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ)
        (match Λ t with
          | none => WitnessTree.mk (t, default) []
          | some i => WitnessTree.mk (t, i) []) := by
  let g : ℕ → WitnessTree (ℕ × ι) → WitnessTree (ℕ × ι) := fun s τ => match Λ s with
    | none => τ
    | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
  let g' : ℕ → WitnessTree (ℕ × ι) → WitnessTree (ℕ × ι) :=
    fun s τ => match truncLog q Λ s with
    | none => τ
    | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
  let seed : WitnessTree (ℕ × ι) := match Λ t with
    | none => WitnessTree.mk (t, default) []
    | some i => WitnessTree.mk (t, i) []
  let seed' : WitnessTree (ℕ × ι) := match truncLog q Λ t with
    | none => WitnessTree.mk (t, default) []
    | some i => WitnessTree.mk (t, i) []
  have hseed : seed' = seed := by
    unfold seed seed' truncLog
    rw [if_pos hq]
  calc
    treeAt vbl (truncLog q Λ) t = (List.range t).foldr g' seed' := by
      unfold treeAt
      rfl
    _ = (List.range t).foldr g' seed := by
      exact congrArg (fun x => (List.range t).foldr g' x) hseed
    _ = ((List.range t).take q ++ (List.range t).drop q).foldr g' seed := by
      exact congrArg (fun l => l.foldr g' seed) (List.take_append_drop q (List.range t)).symm
    _ = (List.range (min q t)).foldr g' (((List.range t).drop q).foldr g' seed) := by
      rw [List.foldr_append, List.take_range]
    _ = (List.range q).foldr g' (((List.range t).drop q).foldr g' seed) := by
      rw [Nat.min_eq_left hq]
    _ = ((List.range t).drop q).foldr g' seed := by
      rw [foldr_range_truncLog_id vbl Λ q]
    _ = ((List.range t).drop q).foldr g seed := by
      refine List.foldr_ext g' g seed ?_
      intro s hs τ
      have hqs : q ≤ s := mem_drop_range hs
      have hts : truncLog q Λ s = Λ s := by
        unfold truncLog
        rw [if_pos hqs]
      change (match truncLog q Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) =
        match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
      simp [hts]

/-- The backward direction of the bijection at the vertex's creation: no vertex of the
truncated stage tree with `X` in its variable set lies at depth ≥ d + 1, so the stage
profile is zero. -/
private theorem treeProfile_zero_of_new_vertex [DecidableEq ι] [Inhabited ι]
    {Λ : ℕ → Option ι} {q t : ℕ} {p : List ℕ}
    (hp : WitnessTree.ValidPath (treeAt vbl (truncLog q Λ) t) p)
    (hpt : (WitnessTree.labelAt hp).1 = q) {X : κ}
    (hX : X ∈ vbl (WitnessTree.labelAt hp).2) :
    treeProfile vbl (forgetTime (treeAt vbl (truncLog q Λ) t)) X
      (WitnessTree.depth (treeAt vbl (truncLog q Λ) t) p + 1) = 0 := by
  have hqle : q ≤ t := by
    have h := treeAt_label_time_le vbl (Λ := truncLog q Λ) hp
    simpa [hpt] using h
  refine treeProfile_eq_zero vbl (h := ?_)
  intro p' hp' hdepth hX'
  let hpL : WitnessTree.ValidPath (treeAt vbl (truncLog q Λ) t) p' :=
    validPath_of_forgetTime hp'
  have hlab : (WitnessTree.labelAt hpL).2 = WitnessTree.labelAt hp' :=
    labelAt_of_forgetTime hp'
  have hdepth' : WitnessTree.depth (treeAt vbl (truncLog q Λ) t) p + 1 ≤
      WitnessTree.depth (treeAt vbl (truncLog q Λ) t) p' := by
    simpa [WitnessTree.depth] using hdepth
  have hpne : p ≠ p' := by
    intro hpp'
    subst p'
    have hc : WitnessTree.depth (treeAt vbl (truncLog q Λ) t) p + 1 ≤
        WitnessTree.depth (treeAt vbl (truncLog q Λ) t) p := by
      simp at hdepth'
    simp [WitnessTree.depth] at hc
  have hXv : X ∈ vbl (WitnessTree.labelAt hpL).2 := by
    simpa [hlab] using hX'
  have htime : q ≠ (WitnessTree.labelAt hpL).1 := by
    have htinj := treeAt_timeInject vbl hp hpL hpne
    simpa [hpt] using htinj
  have hge : q ≤ (WitnessTree.labelAt hpL).1 :=
    treeAt_truncLog_label_time_ge vbl hqle hpL
  have hqlt : (WitnessTree.labelAt hp).1 < (WitnessTree.labelAt hpL).1 := by omega
  have hov : (vbl (WitnessTree.labelAt hp).2 ∩ vbl (WitnessTree.labelAt hpL).2).Nonempty := by
    exact ⟨X, Finset.mem_inter.mpr ⟨hX, hXv⟩⟩
  have hdgt : WitnessTree.depth (treeAt vbl (truncLog q Λ) t) p >
      WitnessTree.depth (treeAt vbl (truncLog q Λ) t) p' :=
    depth_gt_of_earlier_overlap vbl hp hpL hqlt hov
  omega

/-- **The coupling's bijection** (survey B §3.3(b), both directions via the fold
induction): the number of genuine entries before a vertex's time whose event contains `X`
equals the abstract profile of `X` at the vertex's depth + 1. -/
private theorem resample_count_eq_profile [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι}
    {t : ℕ} {p : List ℕ} (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p) {X : κ}
    (hX : X ∈ vbl (WitnessTree.labelAt hp).2) :
    ((List.range (WitnessTree.labelAt hp).1).filter (fun s => match Λ s with
        | none => false
        | some i => decide (X ∈ vbl i))).length =
      treeProfile vbl (forgetTime (treeAt vbl Λ t)) X
        (WitnessTree.depth (treeAt vbl Λ t) p + 1) := by
  let q : ℕ := (WitnessTree.labelAt hp).1
  let σ : WitnessTree (ℕ × ι) := treeAt vbl (truncLog q Λ) t
  let g : ℕ → WitnessTree (ℕ × ι) → WitnessTree (ℕ × ι) := fun s τ => match Λ s with
    | none => τ
    | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ
  have hqle : q ≤ t := by
    have h := treeAt_label_time_le vbl hp
    simpa [q] using h
  have hdrop : treeAt vbl (truncLog q Λ) t =
      ((List.range t).drop q).foldr g (match Λ t with
        | none => WitnessTree.mk (t, default) []
        | some i => WitnessTree.mk (t, i) []) :=
    treeAt_truncLog_eq_drop_fold vbl hqle
  have hmain : treeAt vbl Λ t = (List.range q).foldr g σ := by
    calc
      treeAt vbl Λ t = (List.range t).foldr g (match Λ t with
          | none => WitnessTree.mk (t, default) []
          | some i => WitnessTree.mk (t, i) []) := by
        unfold treeAt
        rfl
      _ = ((List.range t).take q ++ (List.range t).drop q).foldr g
            (match Λ t with
              | none => WitnessTree.mk (t, default) []
              | some i => WitnessTree.mk (t, i) []) := by
        exact congrArg (fun l => l.foldr g (match Λ t with
          | none => WitnessTree.mk (t, default) []
          | some i => WitnessTree.mk (t, i) []))
          (List.take_append_drop q (List.range t)).symm
      _ = (List.range q).foldr g (((List.range t).drop q).foldr g (match Λ t with
          | none => WitnessTree.mk (t, default) []
          | some i => WitnessTree.mk (t, i) [])) := by
        rw [List.foldr_append, List.take_range, Nat.min_eq_left hqle]
      _ = (List.range q).foldr g σ := by
        rw [← hdrop]
  let hp' : WitnessTree.ValidPath ((List.range q).foldr g σ) p :=
    cast (congrArg (fun x => WitnessTree.ValidPath x p) hmain) hp
  have hneq : ∀ s₁ ∈ List.range q, s₁ ≠ (WitnessTree.labelAt hp').1 := by
    intro s₁ hs₁ h
    have hs₁lt : s₁ < q := (List.mem_range.mp hs₁)
    have hq' : (WitnessTree.labelAt hp').1 = q := by
      have hc := labelAt_cast (τ := treeAt vbl Λ t) (τ' := (List.range q).foldr g σ)
        (h := hmain) (p := p) hp
      have h' : (WitnessTree.labelAt hp).1 = q := rfl
      simpa [hp', hc] using h'
    omega
  rcases validPath_foldr_rev vbl Λ (List.range q) σ hp' hneq with ⟨hpσ, hlab⟩
  have hlab' : WitnessTree.labelAt hpσ = WitnessTree.labelAt hp :=
    hlab.trans (labelAt_cast (τ := treeAt vbl Λ t) (τ' := (List.range q).foldr g σ)
      (h := hmain) (p := p) hp)
  have hXσ : X ∈ vbl (WitnessTree.labelAt hpσ).2 := by simpa [hlab'] using hX
  have hpt : (WitnessTree.labelAt hpσ).1 = q := by
    have h' : (WitnessTree.labelAt hp).1 = q := rfl
    simpa [hlab'] using h'
  have hzero : treeProfile vbl (forgetTime σ) X (WitnessTree.depth σ p + 1) = 0 :=
    treeProfile_zero_of_new_vertex vbl hpσ hpt hXσ
  have hadd := foldr_resample_profile_add vbl Λ (List.range q) σ p hpσ X hXσ
  calc
    ((List.range (WitnessTree.labelAt hp).1).filter (fun s => match Λ s with
        | none => false
        | some i => decide (X ∈ vbl i))).length
        = ((List.range q).filter (fun s => match Λ s with
            | none => false
            | some i => decide (X ∈ vbl i))).length := by
          simp [q]
    _ = ((List.range q).filter (fun s => match Λ s with
          | none => false
          | some i => decide (X ∈ vbl i))).length + 0 := by omega
    _ = ((List.range q).filter (fun s => match Λ s with
          | none => false
          | some i => decide (X ∈ vbl i))).length +
          treeProfile vbl (forgetTime σ) X (WitnessTree.depth σ p + 1) := by
        rw [hzero]
    _ = treeProfile vbl (forgetTime ((List.range q).foldr g σ)) X
          (WitnessTree.depth σ p + 1) := hadd
    _ = treeProfile vbl (forgetTime (treeAt vbl Λ t)) X
          (WitnessTree.depth (treeAt vbl Λ t) p + 1) := by
        simp [hmain, WitnessTree.depth]

-- The algorithm-level count/check glue never reads the coordinate σ-algebras, so omit
-- the instance for clean signatures (the Algorithm.lean house pattern).
omit [∀ j, MeasurableSpace (Ω j)]

/-- The algorithm-level count glue: when every entry before `t` is genuine, the row count
of `X` before time `t` is the number of genuine entries whose event contains `X`. -/
private theorem count_eq_filter {ω : ΩN N Ω} {t : Fin (N + 1)}
    (hgen : ∀ s < t.val, log vbl A pick hpick ω s ≠ none) (X : κ) :
    ((count vbl A pick hpick ω t) X : ℕ) =
      ((List.range t.val).filter (fun s => match log vbl A pick hpick ω s with
        | none => false
        | some i => decide (X ∈ vbl i))).length := by
  induction t using Fin.induction with
  | zero => simp [count, run]
  | succ i ih =>
      have hR : i.val < R vbl A pick hpick ω :=
        (log_ne_none_iff_lt_R vbl A pick hpick ω).mp
          (hgen i.val (Nat.lt_succ_self i.val))
      let e : Payload vbl A ω (run vbl A pick hpick ω i.castSucc).fst :=
        Classical.choose (run_step_of_lt_R vbl A pick hpick ω hR)
      have hfin : (⟨i.val, Nat.lt_of_lt_of_le hR
          (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))⟩ : Fin (N + 1)) =
          i.castSucc := Fin.ext rfl
      have hrun' : (run vbl A pick hpick ω i.castSucc).2 = some e := by
        change (run vbl A pick hpick ω ⟨i.val, Nat.lt_of_lt_of_le hR
          (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))⟩).2 = some e
        exact Classical.choose_spec (run_step_of_lt_R vbl A pick hpick ω hR)
      have hlog : log vbl A pick hpick ω i.val = some e.1 := by
        unfold log
        rw [dif_pos hR]
        rfl
      have hdec : (if decide (X ∈ vbl e.1) then 1 else 0) =
          (if X ∈ vbl e.1 then 1 else 0) := by
        by_cases h : X ∈ vbl e.1 <;> simp [h]
      have hcount_step : ((count vbl A pick hpick ω i.succ) X : ℕ) =
          ((count vbl A pick hpick ω i.castSucc) X : ℕ) +
            (if decide (X ∈ vbl e.1) then 1 else 0) := by
        simp only [count, run]
        rw [Fin.induction_succ]
        erw [hrun']
        simp only []
        rw [hdec]
        split_ifs <;> simp
      have hfilter : ([i.val].filter (fun s => match log vbl A pick hpick ω s with
          | none => false
          | some i => decide (X ∈ vbl i))).length =
          (if X ∈ vbl e.1 then 1 else 0) := by
        by_cases h : X ∈ vbl e.1 <;> simp [hlog, h]
      have hmain : ((count vbl A pick hpick ω i.succ) X : ℕ) =
          ((List.range i.val).filter (fun s => match log vbl A pick hpick ω s with
            | none => false
            | some i => decide (X ∈ vbl i))).length +
            (if X ∈ vbl e.1 then 1 else 0) := by
        rw [hcount_step]
        rw [ih (fun s hs => hgen s (Nat.lt_trans hs (Nat.lt_succ_self i.val)))]
        rw [show List.range ↑i.castSucc = List.range i.val from rfl]
        rw [hdec]
      change ↑(count vbl A pick hpick ω i.succ X) =
        ((List.range (i.val + 1)).filter (fun s => match log vbl A pick hpick ω s with
          | none => false
          | some i => decide (X ∈ vbl i))).length
      rw [hmain]
      rw [show List.range (i.val + 1) = List.range i.val ++ [i.val] from List.range_succ]
      rw [List.filter_append, List.length_append]
      rw [hfilter]

/-- The per-vertex check: at a genuine vertex of the occurring tree, the `DeterminedBy`
witness of the vertex's event holds of the table entries the τ-check reads — the algorithm
resampled an occurring event, and the rows agree via `resample_count_eq_profile`. -/
private theorem check_vertex_of_occurring [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ}
    (ht : t < R vbl A pick hpick ω) {τ : WitnessTree ι}
    (hT : T vbl A pick hpick ω t = τ) (hN : WitnessTree.size τ ≤ N) {p : List ℕ}
    (hp : WitnessTree.ValidPath (treeAt vbl (log vbl A pick hpick ω) t) p) :
    Classical.choose (hdet (WitnessTree.labelAt hp).2)
        (fun X => ω ⟨X, ⟨treeProfile vbl τ X
          (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1),
          treeProfile_lt_succ_of_size_le vbl hN⟩⟩) := by
  let Λ : ℕ → Option ι := log vbl A pick hpick ω
  let q : ℕ := (WitnessTree.labelAt hp).1
  have hqle : q ≤ t := by
    have h := treeAt_label_time_le vbl (Λ := Λ) hp
    simpa [Λ, q] using h
  have hqR : q < R vbl A pick hpick ω := Nat.lt_of_le_of_lt hqle ht
  let e : Payload vbl A ω (run vbl A pick hpick ω ⟨q, Nat.lt_of_lt_of_le hqR
      (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))⟩).fst :=
    Classical.choose (run_step_of_lt_R vbl A pick hpick ω hqR)
  have hlogq : log vbl A pick hpick ω q = some e.1 := by
    unfold log
    rw [dif_pos hqR]
  have hlabel : (WitnessTree.labelAt hp).2 = e.1 := by
    by_cases hqt : q = t
    · have hlt : log vbl A pick hpick ω t = some e.1 := by simpa [hqt] using hlogq
      have hroot : WitnessTree.labelOf (treeAt vbl (log vbl A pick hpick ω) t) = (t, e.1) :=
        treeAt_root_label vbl hlt
      have hp' : p = [] := by
        by_contra hne
        have htime := treeAt_timeInject vbl hp (.root) hne
        have hroot' : (WitnessTree.labelAt (.root : WitnessTree.ValidPath
            (treeAt vbl (log vbl A pick hpick ω) t) [])).1 = t := by
          simpa using (congrArg Prod.fst hroot)
        have hq' : (WitnessTree.labelAt hp).1 = t := by simp [q, hqt]
        exact htime (hq'.trans hroot'.symm)
      subst p
      have hl : WitnessTree.labelAt hp = (t, e.1) := by simpa using hroot
      exact congrArg Prod.snd hl
    · have hqlt : q < t := Nat.lt_of_le_of_ne hqle hqt
      have hgen : log vbl A pick hpick ω q = some (WitnessTree.labelAt hp).2 := by
        simpa [Λ, q] using treeAt_label_of_lt vbl hp hqlt
      exact Option.some.inj (hgen.symm.trans hlogq)
  let tf : Fin (N + 1) := ⟨q, Nat.lt_of_lt_of_le hqR
    (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))⟩
  have hwit : Classical.choose (hdet e.1) (fun X : vbl e.1 =>
      ω ⟨X, count vbl A pick hpick ω tf X⟩) := by
    exact ((Classical.choose_spec (hdet e.1)
      (assign ω (count vbl A pick hpick ω tf))).mp (by simpa [count, tf] using e.2.1))
  have hτ : forgetTime (treeAt vbl (log vbl A pick hpick ω) t) = τ := by
    unfold T at hT
    exact hT
  have hgenq : ∀ s < q, log vbl A pick hpick ω s ≠ none := by
    intro s hs
    exact (log_ne_none_iff_lt_R vbl A pick hpick ω).mpr (Nat.lt_trans hs hqR)
  have hval : ∀ X : vbl e.1,
      treeProfile vbl τ X (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1) =
        ((count vbl A pick hpick ω tf) X : ℕ) := by
    intro X
    have hX' : X.val ∈ vbl (WitnessTree.labelAt hp).2 := by
      simp [hlabel]
    have hc := resample_count_eq_profile vbl (Λ := log vbl A pick hpick ω) (hp := hp) hX'
    have hcf := count_eq_filter vbl A pick hpick (ω := ω) (t := tf) (hgen := hgenq) (X := X.val)
    calc
      treeProfile vbl τ X.val (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1)
          = treeProfile vbl (forgetTime (treeAt vbl (log vbl A pick hpick ω) t)) X.val
              (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1) := by
            rw [hτ]
      _ = ((List.range q).filter (fun s => match log vbl A pick hpick ω s with
          | none => false
          | some i => decide (X.val ∈ vbl i))).length := by
          simpa [q] using hc.symm
      _ = ((count vbl A pick hpick ω tf) X.val : ℕ) := by
        simpa [q] using hcf.symm
  have hrow : ∀ X : vbl e.1,
      (⟨X, ⟨treeProfile vbl τ X
        (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1),
        treeProfile_lt_succ_of_size_le vbl hN⟩⟩ : Σ _ : κ, Fin (N + 1)) =
        ⟨X, count vbl A pick hpick ω tf X⟩ := by
    intro X
    have hfin : (⟨treeProfile vbl τ X
        (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1),
        treeProfile_lt_succ_of_size_le vbl hN⟩ : Fin (N + 1)) =
        count vbl A pick hpick ω tf X := by
      exact Fin.ext (by simpa using hval X)
    exact congrArg (Sigma.mk (↑X : κ)) hfin
  have htuples : (fun X : vbl e.1 => ω ⟨X, ⟨treeProfile vbl τ X
      (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1),
      treeProfile_lt_succ_of_size_le vbl hN⟩⟩) =
      (fun X : vbl e.1 => ω ⟨X, count vbl A pick hpick ω tf X⟩) := by
    funext X
    congr 1
    exact hrow X
  have hfinal : Classical.choose (hdet e.1) (fun X : vbl e.1 => ω ⟨X, ⟨treeProfile vbl τ X
      (WitnessTree.depth (treeAt vbl (log vbl A pick hpick ω) t) p + 1),
      treeProfile_lt_succ_of_size_le vbl hN⟩⟩) := by
    have hcong := congrArg (fun f : (j : vbl e.1) → Ω ↑j => Classical.choose (hdet e.1) f)
      htuples
    exact hcong.symm ▸ hwit
  rw [hlabel]
  exact hfinal

/-- **40.3 headline (a)**: if the occurring tree at time `t` is `τ`, then the structural
τ-check passes on `ω`. The `hN` hypothesis is explicit (the coupling supplies it, matching
`check_probability`'s). -/
theorem occurrence_implies_check [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ}
    (ht : t < R vbl A pick hpick ω) {τ : WitnessTree ι}
    (hT : T vbl A pick hpick ω t = τ) (hN : WitnessTree.size τ ≤ N) :
    check vbl A hdet hN ω := by
  have hmem : ω ∈ ({ω' : ΩN N Ω | check vbl A hdet hN ω'} : Set (ΩN N Ω)) := by
    rw [checkSet_eq_vertices vbl A hdet hN]
    intro p hp
    have hτ : forgetTime (treeAt vbl (log vbl A pick hpick ω) t) = τ := by
      unfold T at hT
      exact hT
    let hp'' : WitnessTree.ValidPath (forgetTime (treeAt vbl (log vbl A pick hpick ω) t)) p :=
      cast (congrArg (fun x => WitnessTree.ValidPath x p) hτ.symm) hp
    let hp' : WitnessTree.ValidPath (treeAt vbl (log vbl A pick hpick ω) t) p :=
      validPath_of_forgetTime hp''
    have h14 := check_vertex_of_occurring vbl A hdet pick hpick ht hT hN hp'
    have hlabel : (WitnessTree.labelAt hp').2 = WitnessTree.labelAt hp := by
      exact (labelAt_of_forgetTime hp'').trans (labelAt_cast hτ.symm hp)
    rw [hlabel] at h14
    exact h14
  exact hmem

end OccurrenceCheck

/-! ## 40.3 headline (b): the coupling -/

section CouplingLemma

variable {ι : Type u} {κ : Type u} [DecidableEq κ] [Fintype κ]
variable {Ω : κ → Type w} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable {μ : ∀ j, Measure (Ω j)} [∀ j, IsProbabilityMeasure (μ j)]
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hdet : ∀ i, DeterminedBy (A i) (vbl i))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

open scoped ENNReal

include hdet in
/-- **40.3 headline (b), the coupling lemma**: `μN {∃ t < R, T = τ} ≤ treeProd τ`.
Assembly: occurrence ⊆ check (`occurrence_implies_check`) + `check_probability` (40.2) in
the good case; a non-good `τ` never occurs (`T_isGood`), so the event is empty. No `IsGood`
hypothesis: 60.2 supplies only the `𝒯_i(N)` membership (`size τ ≤ N`) — good trees come
from `T_isGood` on the event, non-good trees have an empty occurrence event. -/
theorem coupling [DecidableEq ι] [Inhabited ι] (hA : ∀ i, MeasurableSet (A i))
    {τ : WitnessTree ι}
    (hN : WitnessTree.size τ ≤ N) :
    μN N μ {ω | ∃ t < R vbl A pick hpick ω, T vbl A pick hpick ω t = τ} ≤
      treeProd (μ := μ) A τ := by
  by_cases hgood : WitnessTree.IsGood vbl τ
  · have hsub : {ω : ΩN N Ω | ∃ t < R vbl A pick hpick ω, T vbl A pick hpick ω t = τ} ⊆
        {ω : ΩN N Ω | check vbl A hdet hN ω} := by
      intro ω hω
      rcases hω with ⟨t, ht, hT⟩
      exact occurrence_implies_check (vbl := vbl) (A := A) (hdet := hdet) (pick := pick)
        (hpick := hpick) ht hT hN
    calc
      μN N μ {ω | ∃ t < R vbl A pick hpick ω, T vbl A pick hpick ω t = τ}
          ≤ μN N μ {ω | check vbl A hdet hN ω} := measure_mono hsub
      _ = treeProd (μ := μ) A τ := check_probability (vbl := vbl) (A := A) (hdet := hdet)
        hA hgood hN
  · have hempty : ({ω : ΩN N Ω | ∃ t < R vbl A pick hpick ω,
        T vbl A pick hpick ω t = τ}) = ∅ := by
      ext ω
      constructor
      · rintro ⟨t, ht, hT⟩
        have hgood' : WitnessTree.IsGood vbl τ := by
          rw [← hT]
          exact T_isGood (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
        exact (hgood hgood').elim
      · intro h
        exact h.elim
    calc
      μN N μ {ω | ∃ t < R vbl A pick hpick ω, T vbl A pick hpick ω t = τ}
          = μN N μ (∅ : Set (ΩN N Ω)) := by rw [hempty]
      _ = 0 := measure_empty
      _ ≤ treeProd (μ := μ) A τ := by positivity

end CouplingLemma

end TCSLean.MoserTardos
