/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
import TCSLean.MoserTardos.WitnessTree
import TCSLean.MoserTardos.VariableModel

/-!
# Galton–Watson weight algebra

This file develops the Galton–Watson weight of a witness tree used in the proof of the
Moser–Tardos resampling bound: the per-label LLL multiplier `x'`, the structural vertex fold
`x'Prod`, the branching weight `gwWeight` of (17.3), and the telescope identity collapsing it
to the `x'`-fold (Lemma 17.1). It hosts items 50.1 and 50.3: the telescope and the
canonical-tree sum bound `gwWeight_sum_le_one`. The 50.2 bounded-tree finiteness was
superseded by the canonical domain `gwFinsetHeight` and removed (see the 50.3 section note).

## Main definitions

* `x' vbl x i`: the notes' (17.1) multiplier `x i * ∏_{j ∈ Γ(i)} (1 - x j)` — the product
  over the open neighborhood `(overlapGraph vbl).neighborFinset i`.
* `x'Prod vbl x`: the structural fold realizing `∏_{u ∈ V τ} x' ([u])` — a recursion over
  all vertices of the tree.
* `gwWeight vbl x`: the (17.3) branching weight — at each vertex the accepted child labels
  `C_τ(u)` contribute `x j` each (a `List` product, equal to the Finset product by
  `Proper`) and the rejected labels `Γ⁺([u]) \ C_τ(u)` contribute `1 - x j` each (a Finset
  filter). No division anywhere in the definition.
* `IsWitnessTree vbl`: every child label lies in `Γ⁺(parent)` (inclusive — the same-label
  `treeElig` disjunct lands in the `i ∈ insert i …` piece and is harmless for the
  telescope).
* `gwFinsetHeight vbl i h`: the finite set of canonical witness trees of height ≤ `h`
  rooted at `i` — children assembled from a child-label set `C ⊆ Γ⁺(i)` in `attach` order.
  This is the canonical Galton–Watson domain every downstream item (60.1's counting
  identity) sums over; it supersedes the 50.2 bounded-tree finset (removed).
* `gwSumHeight vbl x i h`: the partial sum of `gwWeight` over `gwFinsetHeight vbl i h`.

## Main results

* `gwWeight_telescope`: for a proper witness tree rooted at `i` with `x i ≠ 0` and all
  non-root labels nonzero, `gwWeight vbl x τ = ((1 - x i) / x i) * x'Prod vbl x τ`.
* `gwWeight_nonneg`: the branching weight is nonnegative under `0 ≤ x j ≤ 1`.
* `gwSumHeight_zero`: the height-0 sum is the rejected-neighbor product
  `∏_{B ∈ Γ⁺(i)} (1 - x B)`.
* `gwSumHeight_succ`: the height recurrence (the multinomial identity) —
  `gwSumHeight vbl x i (h + 1) = ∏_{B ∈ Γ⁺(i)} ((1 - x B) + x B * gwSumHeight vbl x B h)`.
* `gwSumHeight_le_one`: the height-`h` sum is at most 1 under the box bounds.
* `labelOf_mem_gwFinsetHeight`/`proper_of_mem_gwFinsetHeight`/
  `witness_of_mem_gwFinsetHeight`: the domain invariants — every member of
  `gwFinsetHeight vbl i h` is rooted at `i`, proper, and a witness tree.
* `gwWeight_sum_le_one`: under `0 ≤ x j ≤ 1`, the canonical Galton–Watson sum
  `∑_{τ ∈ gwFinsetHeight vbl i h} gwWeight vbl x τ` is at most 1 (via the height
  recurrence `gwSumHeight_succ` and the induction `gwSumHeight_le_one`).

## References

The weight algebra follows the Moser–Tardos notes, §17 ([moserTardos2010]).
-/

set_option autoImplicit false
set_option pp.unicode.fun true

namespace TCSLean.MoserTardos

universe u

open WitnessTree
open scoped BigOperators

variable {ι κ : Type u}

/-! ## Helper lemmas (instance-free) -/

/-- The root label occurs in `labels`. -/
@[simp]
lemma labelOf_mem_labels (τ : WitnessTree ι) : labelOf τ ∈ labels τ := by
  cases τ with
  | mk a cs => simp [labels]

/-- A child's label occurs in the parent's `labels`. -/
lemma labelOf_mem_labels_of_mem_childrenOf {τ : WitnessTree ι} {c : WitnessTree ι}
    (hc : c ∈ childrenOf τ) : labelOf c ∈ labels τ := by
  cases τ with
  | mk a cs =>
      rw [childrenOf_mk] at hc
      simp only [labels, List.mem_cons]
      exact Or.inr (List.mem_flatMap.mpr ⟨c, hc, labelOf_mem_labels c⟩)

/-- `labels` of a child are contained in the parent's `labels`. -/
lemma labels_subset_of_mem_childrenOf {τ : WitnessTree ι} {c : WitnessTree ι}
    (hc : c ∈ childrenOf τ) : labels c ⊆ labels τ := by
  cases τ with
  | mk a cs =>
      rw [childrenOf_mk] at hc
      intro j hj
      simp only [labels, List.mem_cons]
      exact Or.inr (List.mem_flatMap.mpr ⟨c, hc, hj⟩)

/-- The hypothesis transfer to a child: `hx0` for the parent plus `hxi` (when the
child's label equals the root `i`) yield `x (labelOf c) ≠ 0`. -/
lemma x_labelOf_ne_zero_of_mem_childrenOf {x : ι → ℝ} {i : ι} (hxi : x i ≠ 0)
    {τ : WitnessTree ι} (hx0 : ∀ ⦃j⦄, j ∈ labels τ → j ≠ i → x j ≠ 0)
    {c : WitnessTree ι} (hc : c ∈ childrenOf τ) : x (labelOf c) ≠ 0 := by
  by_cases h : labelOf c = i
  · rwa [h]
  · exact hx0 (labelOf_mem_labels_of_mem_childrenOf hc) h

/-- The `hx0` transfer to a child (with the child's own root excluded instead of `i`). -/
lemma hx0_transfer {x : ι → ℝ} {i : ι} (hxi : x i ≠ 0) {τ : WitnessTree ι}
    (hx0 : ∀ ⦃j⦄, j ∈ labels τ → j ≠ i → x j ≠ 0) {c : WitnessTree ι}
    (hc : c ∈ childrenOf τ) : ∀ ⦃j⦄, j ∈ labels c → j ≠ labelOf c → x j ≠ 0 := by
  intro j hj _hjl
  by_cases hji : j = i
  · subst j
    exact hxi
  · exact hx0 (labels_subset_of_mem_childrenOf hc hj) hji

/-- A child has size at most the size-sum of the children list. -/
lemma size_le_sum_of_mem {cs : List (WitnessTree ι)} {c : WitnessTree ι}
    (hc : c ∈ cs) : size c ≤ (cs.map size).sum := by
  induction cs generalizing c with
  | nil => cases hc
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons, List.mem_cons] at hc ⊢
    rcases hc with rfl | hc
    · exact Nat.le_add_right _ _
    · exact le_trans (ih hc) (Nat.le_add_left _ _)

variable [DecidableEq ι] [DecidableEq κ] [Fintype ι]

/-! ## The LLL multiplier, the vertex fold, and the branching weight -/

/-- The notes' (17.1) multiplier `x' B := x B · ∏_{C ∈ Γ(B)} (1 - x C)`. -/
def x' (vbl : ι → Finset κ) (x : ι → ℝ) (i : ι) : ℝ :=
  x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)

/-- The structural form of `∏_{u ∈ V τ} x' ([u])`: a fold over all vertices. -/
def x'Prod (vbl : ι → Finset κ) (x : ι → ℝ) : WitnessTree ι → ℝ
  | WitnessTree.mk a cs => x' vbl x a * (cs.map (x'Prod vbl x)).prod

/-- The Galton–Watson weight (17.3): the genuine branching probability of the tree
`τ`. At each vertex the accepted child labels `C_τ(u)` contribute `x B` each and the
rejected labels `Γ⁺([u]) \ C_τ(u)` contribute `(1 - x B)` each. The accepted product is
the **List** product over the children (equal to the Finset product by `Proper`), the
rejected product is a Finset filter — no division anywhere. -/
def gwWeight (vbl : ι → Finset κ) (x : ι → ℝ) : WitnessTree ι → ℝ
  | WitnessTree.mk a cs =>
      (cs.map (fun c => x (labelOf c))).prod *
        (((gammaPlus vbl a).filter (fun j => j ∉ cs.map labelOf)).prod (fun j => 1 - x j)) *
        (cs.map (gwWeight vbl x)).prod

/-- The (17.3) witness condition: every child label lies in `Γ⁺(parent)` (inclusive —
the same-label `treeElig` disjunct lands in the `i ∈ insert i …` piece and is harmless
for the telescope). -/
def IsWitnessTree (vbl : ι → Finset κ) : WitnessTree ι → Prop
  | WitnessTree.mk a cs =>
      (∀ c ∈ cs, labelOf c ∈ gammaPlus vbl a) ∧
        ∀ c ∈ cs, IsWitnessTree vbl c

/-! ## The telescope -/

/-- (17.3)→(17.2): the branching weight telescopes to the `x'`-fold. The hypotheses are
the notes' assumptions: `τ` is proper and a witness tree (`C_τ(u) ⊆ Γ⁺([u])`), `x i ≠ 0`
(the division on the RHS), and `x j ≠ 0` for the non-root labels (the divisions in the
inductive cancellation). `hx0` is a proof-artifact hypothesis: notes Lemma 17.1 needs
only `hxi`, and the stronger division-free identity `gwWeight_mul_x_eq` (Basic.lean,
hypotheses `hroot`/`hprop`/`hwit` only) is the form the assembly in Basic.lean uses. -/
theorem gwWeight_telescope {vbl : ι → Finset κ} {x : ι → ℝ} {i : ι} (hxi : x i ≠ 0)
    {τ : WitnessTree ι} (hroot : labelOf τ = i) (hprop : Proper τ) (hwit : IsWitnessTree vbl τ)
    (hx0 : ∀ ⦃j⦄, j ∈ labels τ → j ≠ i → x j ≠ 0) :
    gwWeight vbl x τ = ((1 - x i) / x i) * x'Prod vbl x τ := by
  refine WitnessTree.rec
    (motive_1 := fun τ => ∀ ⦃i⦄, x i ≠ 0 → labelOf τ = i → Proper τ →
      IsWitnessTree vbl τ → (∀ ⦃j⦄, j ∈ labels τ → j ≠ i → x j ≠ 0) →
      gwWeight vbl x τ = ((1 - x i) / x i) * x'Prod vbl x τ)
    (motive_2 := fun cs => ∀ c ∈ cs, ∀ ⦃i⦄, x i ≠ 0 → labelOf c = i → Proper c →
      IsWitnessTree vbl c → (∀ ⦃j⦄, j ∈ labels c → j ≠ i → x j ≠ 0) →
      gwWeight vbl x c = ((1 - x i) / x i) * x'Prod vbl x c)
    (fun a cs ih => ?mk) (by intro c hc; cases hc) (fun c cs ihc ihcs => ?cons) τ
    hxi hroot hprop hwit hx0
  · intro i hxi hroot hprop hwit hx0
    have hia : i = a := by simpa using hroot.symm
    subst hia
    rcases (proper_mk i cs).mp hprop with ⟨hcnodup, hcprop⟩
    have hcwit_and : (∀ c ∈ cs, labelOf c ∈ gammaPlus vbl i) ∧
        ∀ c ∈ cs, IsWitnessTree vbl c := by simpa [IsWitnessTree] using hwit
    rcases hcwit_and with ⟨hcwit, hcwit'⟩
    have hxc : ∀ c ∈ cs, x (labelOf c) ≠ 0 := fun c hc =>
      x_labelOf_ne_zero_of_mem_childrenOf hxi hx0 hc
    have ihc : ∀ c ∈ cs, gwWeight vbl x c =
        ((1 - x (labelOf c)) / x (labelOf c)) * x'Prod vbl x c :=
      fun c hc => ih c hc (hxc c hc) rfl (hcprop c hc) (hcwit' c hc)
        (hx0_transfer hxi hx0 hc)
    let rej : ℝ := ((gammaPlus vbl i).filter (fun j => j ∉ cs.map labelOf)).prod
      (fun j => 1 - x j)
    -- Step A: the child products cancel: `∏_c x[c'] · ∏_c gwWeight c =
    -- ∏_c (1 - x[c']) · ∏_c x'Prod c`.
    have hA : (cs.map (fun c => x (labelOf c))).prod *
        (cs.map (gwWeight vbl x)).prod =
        (cs.map (fun c => 1 - x (labelOf c))).prod *
          (cs.map (x'Prod vbl x)).prod := by
      rw [← List.prod_map_mul, ← List.prod_map_mul]
      refine congrArg List.prod (List.map_congr_left ?_)
      intro c hc
      rw [ihc c hc]
      field_simp [hxc c hc]
    -- Step B: `∏_c (1 - x[c']) · rej = (1 - x i) · ∏_{j ∈ Γ(i)} (1 - x j)` via the
    -- filter decomposition of Γ⁺ over the child-label finset.
    have hB : (cs.map (fun c => 1 - x (labelOf c))).prod * rej =
        (1 - x i) * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j) := by
      have hprodC : (cs.map (fun c => 1 - x (labelOf c))).prod =
          ∏ j ∈ (cs.map labelOf).toFinset, (1 - x j) := by
        calc
          (cs.map (fun c => 1 - x (labelOf c))).prod
              = (cs.map (fun c => (fun j => 1 - x j) (labelOf c))).prod := by
                refine congrArg List.prod (List.map_congr_left ?_)
                intro c _hc
                rfl
          _ = ((cs.map labelOf).map (fun j => 1 - x j)).prod := by
            rw [List.map_map]
            rfl
          _ = ∏ j ∈ (cs.map labelOf).toFinset, (1 - x j) :=
            (List.prod_toFinset (fun j => 1 - x j) hcnodup).symm
      have hs : (gammaPlus vbl i).filter (fun j => j ∈ cs.map labelOf) =
          (cs.map labelOf).toFinset := by
        ext j
        constructor
        · intro hj
          exact List.mem_toFinset.mpr (Finset.mem_filter.mp hj).2
        · intro hj
          refine Finset.mem_filter.mpr ⟨?_, List.mem_toFinset.mp hj⟩
          rcases List.mem_map.mp (List.mem_toFinset.mp hj) with ⟨c, hc, rfl⟩
          exact hcwit c hc
      have hsplit : (∏ j ∈ (cs.map labelOf).toFinset, (1 - x j)) * rej =
          ∏ j ∈ gammaPlus vbl i, (1 - x j) := by
        rw [← hs]
        rw [← Finset.prod_filter_mul_prod_filter_not (gammaPlus vbl i)
          (fun j => j ∈ cs.map labelOf) (fun j => 1 - x j)]
      have hgamma : ∏ j ∈ gammaPlus vbl i, (1 - x j) =
          (1 - x i) * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j) := by
        unfold gammaPlus
        rw [Finset.prod_insert]
        intro h
        exact ((mem_overlap_neighborFinset vbl).mp h).1 rfl
      calc
        (cs.map (fun c => 1 - x (labelOf c))).prod * rej
            = (∏ j ∈ (cs.map labelOf).toFinset, (1 - x j)) * rej := by rw [hprodC]
        _ = ∏ j ∈ gammaPlus vbl i, (1 - x j) := hsplit
        _ = (1 - x i) * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j) := hgamma
    -- Step C: the RHS unfolds and the `x i` cancels.
    have hC : (1 - x i) * (∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)) *
        (cs.map (x'Prod vbl x)).prod =
        ((1 - x i) / x i) * x'Prod vbl x (mk i cs) := by
      unfold x'Prod x'
      field_simp [hxi]
    calc
      gwWeight vbl x (mk i cs)
          = (cs.map (fun c => x (labelOf c))).prod * rej *
              (cs.map (gwWeight vbl x)).prod := by rw [gwWeight]
      _ = (cs.map (fun c => 1 - x (labelOf c))).prod * rej *
              (cs.map (x'Prod vbl x)).prod := by
        rw [show (cs.map (fun c => x (labelOf c))).prod * rej *
            (cs.map (gwWeight vbl x)).prod =
            (cs.map (fun c => x (labelOf c))).prod *
            (cs.map (gwWeight vbl x)).prod * rej by ring]
        rw [hA]
        ring
      _ = ((1 - x i) * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)) *
              (cs.map (x'Prod vbl x)).prod := by
        rw [hB]
      _ = ((1 - x i) / x i) * x'Prod vbl x (mk i cs) := hC
  · intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-! ## The canonical Galton–Watson tree domain and its sum (50.3)

The bound `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ 1` is false over *all* ordered witness trees (each
unordered skeleton of branching `d` contributes `d!` trees of equal weight — star-graph
counterexample in the blueprint, 50.3 prep), so the sum ranges over `gwFinsetHeight`, the
recursive finset of the trees the Γ⁺-indexed Galton–Watson process can produce: children
assembled from a child-label set `C ⊆ Γ⁺(i)` in canonical `attach` order. The multinomial
factorization of the height recurrence then holds by construction.

This canonical domain supersedes the 50.2 bounded-tree finset (`fintypeProperSizeLE` /
`treesFintype` / `treesFinset`, the finite set `𝒯_i(N) := {τ // Proper τ ∧ size τ ≤ N ∧
labelOf τ = i}`): the sum bound is false over `𝒯_i(N)` and no downstream item consumed
it once the counting identity was re-shaped over `gwFinsetHeight` (60.1), so the 50.2
chain was removed. -/

/-- The canonical witness trees of height ≤ h rooted at i: one tree per child-label SET
(children assembled from C ⊆ Γ⁺(i), ordered by `attach`). Noncomputable via
`Finset.toList` (the canonical child order). -/
noncomputable def gwFinsetHeight (vbl : ι → Finset κ) (i : ι) : ℕ → Finset (WitnessTree ι)
  | 0 => {WitnessTree.mk i []}
  | h + 1 => (gammaPlus vbl i).powerset.biUnion (fun C =>
      (C.pi (fun B => gwFinsetHeight vbl B h)).image
        (fun f : ∀ B, B ∈ C → WitnessTree ι =>
          WitnessTree.mk i (C.attach.toList.map (fun x => f x.1 x.2))))

/-- The Galton–Watson height-h partial sum (noncomputable via `gwFinsetHeight`). -/
noncomputable def gwSumHeight (vbl : ι → Finset κ) (x : ι → ℝ) (i : ι) (h : ℕ) : ℝ :=
  ∑ τ ∈ gwFinsetHeight vbl i h, gwWeight vbl x τ

/-- Domain invariant: every member is rooted at i. -/
lemma labelOf_mem_gwFinsetHeight (vbl : ι → Finset κ) (i : ι) (h : ℕ) {τ : WitnessTree ι}
    (hτ : τ ∈ gwFinsetHeight vbl i h) : WitnessTree.labelOf τ = i := by
  induction h generalizing τ with
  | zero =>
    simp only [gwFinsetHeight, Finset.mem_singleton] at hτ
    subst τ
    rfl
  | succ h _ih =>
    simp only [gwFinsetHeight, Finset.mem_biUnion, Finset.mem_image] at hτ
    rcases hτ with ⟨C, _hC, f, _hf, rfl⟩
    rfl

/-- Domain invariant: every member is proper. -/
lemma proper_of_mem_gwFinsetHeight (vbl : ι → Finset κ) (i : ι) (h : ℕ) {τ : WitnessTree ι}
    (hτ : τ ∈ gwFinsetHeight vbl i h) : WitnessTree.Proper τ := by
  induction h generalizing i τ with
  | zero =>
    simp only [gwFinsetHeight, Finset.mem_singleton] at hτ
    subst τ
    simp
  | succ h ih =>
    simp only [gwFinsetHeight, Finset.mem_biUnion, Finset.mem_image] at hτ
    rcases hτ with ⟨C, _hC, f, hf, rfl⟩
    rw [proper_mk]
    constructor
    · rw [List.map_map]
      change (C.attach.toList.map (fun x => labelOf (f x.1 x.2))).Nodup
      rw [show C.attach.toList.map (fun x => labelOf (f x.1 x.2)) =
          C.attach.toList.map (fun x => x.1) by
        refine List.map_congr_left ?_
        intro y _hy
        exact labelOf_mem_gwFinsetHeight vbl y.1 h (Finset.mem_pi.mp hf y.1 y.2)]
      exact (Finset.nodup_toList C.attach).map Subtype.coe_injective
    · intro c hc
      rcases List.mem_map.mp hc with ⟨y, _hy, rfl⟩
      exact ih y.1 (Finset.mem_pi.mp hf y.1 y.2)

/-- Domain invariant: every member satisfies the witness condition (children in Γ⁺). -/
lemma witness_of_mem_gwFinsetHeight (vbl : ι → Finset κ) (i : ι) (h : ℕ)
    {τ : WitnessTree ι} (hτ : τ ∈ gwFinsetHeight vbl i h) : IsWitnessTree vbl τ := by
  induction h generalizing i τ with
  | zero =>
    simp only [gwFinsetHeight, Finset.mem_singleton] at hτ
    subst τ
    simp [IsWitnessTree]
  | succ h ih =>
    simp only [gwFinsetHeight, Finset.mem_biUnion, Finset.mem_image] at hτ
    rcases hτ with ⟨C, hC, f, hf, rfl⟩
    rw [IsWitnessTree]
    constructor
    · intro c hc
      rcases List.mem_map.mp hc with ⟨y, _hy, rfl⟩
      rw [labelOf_mem_gwFinsetHeight vbl y.1 h (Finset.mem_pi.mp hf y.1 y.2)]
      exact (Finset.mem_powerset.mp hC) y.2
    · intro c hc
      rcases List.mem_map.mp hc with ⟨y, _hy, rfl⟩
      exact ih y.1 (Finset.mem_pi.mp hf y.1 y.2)

/-- The gwWeight is nonnegative under the box bounds. -/
lemma gwWeight_nonneg (vbl : ι → Finset κ) (x : ι → ℝ) (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j ≤ 1) (τ : WitnessTree ι) : 0 ≤ gwWeight vbl x τ := by
  refine WitnessTree.rec (motive_1 := fun τ => 0 ≤ gwWeight vbl x τ)
    (motive_2 := fun cs => ∀ c ∈ cs, 0 ≤ gwWeight vbl x c)
    (fun a cs ih => ?_) (by intro c hc; cases hc) (fun c cs ihc ihcs => ?_) τ
  · rw [gwWeight]
    apply mul_nonneg
    · apply mul_nonneg
      · exact List.prod_nonneg (fun y hy => by
          rcases List.mem_map.mp hy with ⟨c, _hc, rfl⟩
          exact hx0 (labelOf c))
      · exact Finset.prod_nonneg (fun j _hj => sub_nonneg.mpr (hx1 j))
    · exact List.prod_nonneg (fun y hy => by
        rcases List.mem_map.mp hy with ⟨c, hc, rfl⟩
        exact ih c hc)
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ihc
    · exact ihcs c hc

/-- The height-0 sum is the rejected-neighbor product. -/
lemma gwSumHeight_zero (vbl : ι → Finset κ) (x : ι → ℝ) (i : ι) :
    gwSumHeight vbl x i 0 = ∏ B ∈ gammaPlus vbl i, (1 - x B) := by
  unfold gwSumHeight
  change (∑ τ ∈ ({WitnessTree.mk i []} : Finset (WitnessTree ι)), gwWeight vbl x τ) =
    ∏ B ∈ gammaPlus vbl i, (1 - x B)
  rw [Finset.sum_singleton]
  rw [gwWeight]
  simp [Finset.filter_true]

/-! ### 50.3 support lemmas for the recurrence -/

private lemma map_eq_of_mem_of_map_eq {α β : Type u} {l : List α} {g₁ g₂ : α → β}
    (h : l.map g₁ = l.map g₂) : ∀ x ∈ l, g₁ x = g₂ x := by
  induction l with
  | nil => intro x hx; cases hx
  | cons a t ih =>
    intro x hx
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa using congrArg List.head? h
    · exact ih (by simpa using congrArg List.tail h) x hx

omit [DecidableEq ι] [Fintype ι] in
private lemma mem_map_attach_val (C : Finset ι) {j : ι} :
    j ∈ C.attach.toList.map (fun x => x.1) ↔ j ∈ C := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact x.2
  · intro hj
    refine ⟨⟨j, hj⟩, ?_, rfl⟩
    simp

omit [DecidableEq κ] [Fintype ι] in
private lemma toFinset_attach_map_val (C : Finset ι) :
    (C.attach.toList.map (fun x => x.1)).toFinset = C := by
  ext j
  rw [List.mem_toFinset]
  exact mem_map_attach_val C

omit [Fintype ι] in
private lemma toFinset_of_toList (s : Finset ι) : s.toList.toFinset = s := by
  ext j
  rw [List.mem_toFinset, Finset.mem_toList]

omit [DecidableEq ι] [DecidableEq κ] [Fintype ι] in
/-- The assemble map `(C, f) ↦ mk i (C.attach.toList.map f)` is injective in `f` for each
fixed `C`: the child list equality `l₁ = l₂` forces `f₁ = f₂` on every element of
`C.attach.toList` (an easy induction over the nodup list). -/
private lemma assemble_injective (i : ι) (C : Finset ι) :
    Function.Injective (fun f : ∀ B, B ∈ C → WitnessTree ι =>
      WitnessTree.mk i (C.attach.toList.map (fun x => f x.1 x.2))) := by
  intro f₁ f₂ hf
  have hl : C.attach.toList.map (fun x => f₁ x.1 x.2) =
      C.attach.toList.map (fun x => f₂ x.1 x.2) := by
    simpa using congrArg WitnessTree.childrenOf hf
  funext B hB
  exact map_eq_of_mem_of_map_eq hl ⟨B, hB⟩
    (Finset.mem_toList.mpr (Finset.mem_attach C ⟨B, hB⟩))

/-- The per-`(C, f)` weight identity: the assembled tree's weight factors into the
accepted-child product over `C` and the rejected product over `Γ⁺(i) \ C`. -/
private lemma gwWeight_assemble (vbl : ι → Finset κ) (x : ι → ℝ) (i : ι) (h : ℕ)
    (C : Finset ι) (f : ∀ B, B ∈ C → WitnessTree ι)
    (hf : f ∈ C.pi (fun B => gwFinsetHeight vbl B h)) :
    gwWeight vbl x (WitnessTree.mk i (C.attach.toList.map (fun y => f y.1 y.2))) =
      (∏ y ∈ C.attach, x y.1 * gwWeight vbl x (f y.1 y.2)) *
        ∏ B ∈ gammaPlus vbl i \ C, (1 - x B) := by
  rw [gwWeight]
  have hmap : (C.attach.toList.map (fun y => f y.1 y.2)).map
      (fun c => x (labelOf c) * gwWeight vbl x c) =
      C.attach.toList.map (fun y => x y.1 * gwWeight vbl x (f y.1 y.2)) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro y _hy
    change x (labelOf (f y.1 y.2)) * gwWeight vbl x (f y.1 y.2) =
      x y.1 * gwWeight vbl x (f y.1 y.2)
    rw [labelOf_mem_gwFinsetHeight vbl y.1 h (Finset.mem_pi.mp hf y.1 y.2)]
  have hlabels : (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf =
      C.attach.toList.map (fun x => x.1) := by
    rw [List.map_map]
    refine List.map_congr_left ?_
    intro y _hy
    exact labelOf_mem_gwFinsetHeight vbl y.1 h (Finset.mem_pi.mp hf y.1 y.2)
  have hprod : (C.attach.toList.map (fun y => x y.1 * gwWeight vbl x (f y.1 y.2))).prod =
      ∏ y ∈ C.attach, x y.1 * gwWeight vbl x (f y.1 y.2) := by
    rw [← List.prod_toFinset (f := fun y => x y.1 * gwWeight vbl x (f y.1 y.2))
      (l := C.attach.toList) (Finset.nodup_toList C.attach)]
    rw [toFinset_of_toList C.attach]
  have hrej : ((gammaPlus vbl i).filter (fun j => j ∉
      (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf)).prod (fun j => 1 - x j) =
      ∏ B ∈ gammaPlus vbl i \ C, (1 - x B) := by
    rw [show (gammaPlus vbl i).filter (fun j => j ∉
        (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf) = gammaPlus vbl i \ C by
      rw [hlabels]
      ext j
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      rw [mem_map_attach_val C]]
  rw [show ((C.attach.toList.map (fun y => f y.1 y.2)).map (fun c => x (labelOf c))).prod *
      (((gammaPlus vbl i).filter (fun j => j ∉
        (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf)).prod (fun j => 1 - x j)) *
      ((C.attach.toList.map (fun y => f y.1 y.2)).map (gwWeight vbl x)).prod =
      ((C.attach.toList.map (fun y => f y.1 y.2)).map
        (fun c => x (labelOf c) * gwWeight vbl x c)).prod *
        (((gammaPlus vbl i).filter (fun j => j ∉
          (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf)).prod (fun j => 1 - x j)) from by
    calc
      ((C.attach.toList.map (fun y => f y.1 y.2)).map (fun c => x (labelOf c))).prod *
          (((gammaPlus vbl i).filter (fun j => j ∉
            (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf)).prod (fun j => 1 - x j)) *
          ((C.attach.toList.map (fun y => f y.1 y.2)).map (gwWeight vbl x)).prod
          = ((C.attach.toList.map (fun y => f y.1 y.2)).map (fun c => x (labelOf c))).prod *
              ((C.attach.toList.map (fun y => f y.1 y.2)).map (gwWeight vbl x)).prod *
              (((gammaPlus vbl i).filter (fun j => j ∉
                (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf)).prod
                (fun j => 1 - x j)) := by
        ring
      _ = ((C.attach.toList.map (fun y => f y.1 y.2)).map
          (fun c => x (labelOf c) * gwWeight vbl x c)).prod *
              (((gammaPlus vbl i).filter (fun j => j ∉
                (C.attach.toList.map (fun y => f y.1 y.2)).map labelOf)).prod
                (fun j => 1 - x j)) := by
        rw [List.prod_map_mul]]
  rw [hmap, hprod, hrej]

/-- The tuple factorization: summing the accepted-child product over all assemble functions
is the product over `C` of the per-label height-`h` sums. -/
private lemma sum_pi_gwWeight (vbl : ι → Finset κ) (x : ι → ℝ) (h : ℕ) (C : Finset ι) :
    (∑ f ∈ C.pi (fun B => gwFinsetHeight vbl B h),
        ∏ y ∈ C.attach, x y.1 * gwWeight vbl x (f y.1 y.2))
      = ∏ B ∈ C, x B * gwSumHeight vbl x B h := by
  rw [← Finset.prod_sum (s := C) (t := fun B => gwFinsetHeight vbl B h)
    (f := fun B τ => x B * gwWeight vbl x τ)]
  apply Finset.prod_congr rfl
  intro B _hB
  rw [← Finset.mul_sum]
  rfl

/-- The height recurrence (the multinomial identity). -/
lemma gwSumHeight_succ (vbl : ι → Finset κ) (x : ι → ℝ) (i : ι) (h : ℕ) :
    gwSumHeight vbl x i (h + 1) =
      ∏ B ∈ gammaPlus vbl i, ((1 - x B) + x B * gwSumHeight vbl x B h) := by
  let assemble : (C : Finset ι) → (∀ B, B ∈ C → WitnessTree ι) → WitnessTree ι :=
    fun C f => WitnessTree.mk i (C.attach.toList.map (fun x => f x.1 x.2))
  unfold gwSumHeight
  change (∑ τ ∈ (gammaPlus vbl i).powerset.biUnion (fun C : Finset ι =>
      (C.pi (fun B => gwFinsetHeight vbl B h)).image (assemble C)), gwWeight vbl x τ) =
    ∏ B ∈ gammaPlus vbl i, ((1 - x B) + x B * gwSumHeight vbl x B h)
  have hdisj : Set.PairwiseDisjoint (↑(gammaPlus vbl i).powerset)
      (fun C : Finset ι => (C.pi (fun B => gwFinsetHeight vbl B h)).image (assemble C)) := by
    intro C₁ _hC₁ C₂ _hC₂ hne
    change Disjoint ((C₁.pi (fun B => gwFinsetHeight vbl B h)).image (assemble C₁))
      ((C₂.pi (fun B => gwFinsetHeight vbl B h)).image (assemble C₂))
    rw [Finset.disjoint_left]
    intro τ hτ₁ hτ₂
    rcases Finset.mem_image.mp hτ₁ with ⟨f₁, hf₁, h₁⟩
    rcases Finset.mem_image.mp hτ₂ with ⟨f₂, hf₂, h₂⟩
    have hl : C₁.attach.toList.map (fun x => f₁ x.1 x.2) =
        C₂.attach.toList.map (fun x => f₂ x.1 x.2) := by
      have h₁' : WitnessTree.mk i (C₁.attach.toList.map (fun x => f₁ x.1 x.2)) = τ := by
        simpa [assemble] using h₁
      have h₂' : WitnessTree.mk i (C₂.attach.toList.map (fun x => f₂ x.1 x.2)) = τ := by
        simpa [assemble] using h₂
      simpa using congrArg WitnessTree.childrenOf (h₁'.trans h₂'.symm)
    have hlabels₁ : (C₁.attach.toList.map (fun x => f₁ x.1 x.2)).map labelOf =
        C₁.attach.toList.map (fun x => x.1) := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro y _hy
      exact labelOf_mem_gwFinsetHeight vbl y.1 h (Finset.mem_pi.mp hf₁ y.1 y.2)
    have hlabels₂ : (C₂.attach.toList.map (fun x => f₂ x.1 x.2)).map labelOf =
        C₂.attach.toList.map (fun x => x.1) := by
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro y _hy
      exact labelOf_mem_gwFinsetHeight vbl y.1 h (Finset.mem_pi.mp hf₂ y.1 y.2)
    exact hne (calc
      C₁ = (C₁.attach.toList.map (fun x => x.1)).toFinset := (toFinset_attach_map_val C₁).symm
      _ = (C₂.attach.toList.map (fun x => x.1)).toFinset := by
        rw [← hlabels₁, ← hlabels₂, hl]
      _ = C₂ := toFinset_attach_map_val C₂)
  calc
    (∑ τ ∈ (gammaPlus vbl i).powerset.biUnion (fun C : Finset ι =>
        (C.pi (fun B => gwFinsetHeight vbl B h)).image (assemble C)), gwWeight vbl x τ)
        = ∑ C ∈ (gammaPlus vbl i).powerset, ∑ f ∈ C.pi (fun B => gwFinsetHeight vbl B h),
            gwWeight vbl x (assemble C f) := by
      rw [Finset.sum_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro C _hC
      rw [Finset.sum_image]
      exact (assemble_injective i C).injOn
    _ = ∑ C ∈ (gammaPlus vbl i).powerset,
        (∑ f ∈ C.pi (fun B => gwFinsetHeight vbl B h),
          ∏ y ∈ C.attach, x y.1 * gwWeight vbl x (f y.1 y.2)) *
          ∏ B ∈ gammaPlus vbl i \ C, (1 - x B) := by
      apply Finset.sum_congr rfl
      intro C _hC
      calc
        (∑ f ∈ C.pi (fun B => gwFinsetHeight vbl B h), gwWeight vbl x (assemble C f))
            = ∑ f ∈ C.pi (fun B => gwFinsetHeight vbl B h),
                (∏ y ∈ C.attach, x y.1 * gwWeight vbl x (f y.1 y.2)) *
                  ∏ B ∈ gammaPlus vbl i \ C, (1 - x B) := by
          apply Finset.sum_congr rfl
          intro f hf
          rw [gwWeight_assemble vbl x i h C f hf]
        _ = (∑ f ∈ C.pi (fun B => gwFinsetHeight vbl B h),
                ∏ y ∈ C.attach, x y.1 * gwWeight vbl x (f y.1 y.2)) *
              ∏ B ∈ gammaPlus vbl i \ C, (1 - x B) := by
          rw [Finset.sum_mul]
    _ = ∑ C ∈ (gammaPlus vbl i).powerset,
        (∏ B ∈ C, x B * gwSumHeight vbl x B h) * ∏ B ∈ gammaPlus vbl i \ C, (1 - x B) := by
      apply Finset.sum_congr rfl
      intro C _hC
      rw [sum_pi_gwWeight vbl x h C]
    _ = ∏ B ∈ gammaPlus vbl i, ((1 - x B) + x B * gwSumHeight vbl x B h) := by
      rw [show (∏ B ∈ gammaPlus vbl i, ((1 - x B) + x B * gwSumHeight vbl x B h)) =
          (∏ B ∈ gammaPlus vbl i, ((x B * gwSumHeight vbl x B h) + (1 - x B))) by
        apply Finset.prod_congr rfl
        intro B _hB
        rw [add_comm]]
      rw [Finset.prod_add (fun B => x B * gwSumHeight vbl x B h) (fun B => 1 - x B)
        (gammaPlus vbl i)]

/-- The height-h Galton–Watson sum is ≤ 1 under the box bounds. -/
lemma gwSumHeight_le_one (vbl : ι → Finset κ) (x : ι → ℝ) (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j ≤ 1) (i : ι) (h : ℕ) : gwSumHeight vbl x i h ≤ 1 := by
  induction h generalizing i with
  | zero =>
    rw [gwSumHeight_zero]
    exact Finset.prod_le_one (fun B _hB => sub_nonneg.mpr (hx1 B))
      (fun B _hB => sub_le_self _ (hx0 B))
  | succ h ih =>
    rw [gwSumHeight_succ]
    exact Finset.prod_le_one (fun B _hB => add_nonneg (sub_nonneg.mpr (hx1 B))
      (mul_nonneg (hx0 B) (by
        unfold gwSumHeight
        exact Finset.sum_nonneg (fun τ _hτ => gwWeight_nonneg vbl x hx0 hx1 τ))))
      (fun B _hB => by
        have hmul : x B * gwSumHeight vbl x B h ≤ x B := by
          simpa using mul_le_mul_of_nonneg_left (ih B) (hx0 B)
        nlinarith [sub_nonneg.mpr (hx1 B)])

/-- **50.3 headline**: the canonical Galton–Watson sum is ≤ 1. -/
lemma gwWeight_sum_le_one (vbl : ι → Finset κ) (x : ι → ℝ) (hx0 : ∀ j, 0 ≤ x j)
    (hx1 : ∀ j, x j ≤ 1) (i : ι) (h : ℕ) :
    ∑ τ ∈ gwFinsetHeight vbl i h, gwWeight vbl x τ ≤ 1 := by
  simpa [gwSumHeight] using gwSumHeight_le_one vbl x hx0 hx1 i h

end TCSLean.MoserTardos
