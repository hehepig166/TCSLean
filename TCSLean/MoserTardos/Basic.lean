/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
import TCSLean.MoserTardos.WitnessTree
import TCSLean.MoserTardos.GaltonWatson
import TCSLean.MoserTardos.Coupling

/-!
# The canonical witness tree and the counting identity

This file defines the canonical form of a witness tree — at every node the children
reordered into the internal order of their label finset, the same order `gwFinsetHeight`
assembles with (60.1) — and proves the counting identity: the number of resamplings of
event `i` equals the sum over the canonical Galton–Watson domain
`gwFinsetHeight vbl i (N - 1)` of the fiber sizes of `t ↦ canon (T ω t)` over
`t < R ω` (the fiber-card form — no injectivity machinery needed).

## Main definitions

* `canon`: the canonical form of a witness tree (only `[DecidableEq ι]`; well-founded
  on `size`).

## Main results

* `labelOf_canon`: the canonical form preserves the root label (unconditional).
* `size_canon`: the canonical form preserves the size on proper trees (`Proper` is
  load-bearing: `canon` drops duplicate-label children).
* `height_le_size_pred`: the height of a tree is bounded by its size minus one.
* `treeAt_isWitnessTree`/`T_isWitnessTree`: the time-labeled witness tree and the
  occurring tree of the execution table satisfy the witness condition.
* `canon_mem_gwFinsetHeight`: the canonical form of a proper witness tree of height at
  most `h` lies in `gwFinsetHeight vbl (labelOf τ) h`.
* `log_eq_some_iff_labelOf_T`: before the stopping time, the log resampled `i` exactly
  when the witness tree is rooted at `i`.
* `countLog_eq_sum_card`: the counting identity (fiber-card form) — (60.1).
* `canonLiftCert`: the path-certificate lift — a valid path in `canon τ` lifts to a
  valid path in `τ` (the reindexed preimage; data-valued so the preservation lemmas
  unfold it).
* `check_canon` / `isGood_canon`: the τ-check and `IsGood` are invariant under the
  canonical form (properness is load-bearing — `canon` drops duplicate-label children).
* `measurableSet_occ_canon`/`measurableSet_occ`/`aemeasurable_card_fiber`: the
  measurable-occurrence block (`section MeasurableOccurrence`) — the per-time
  canonical-occurrence set `{ω | t < R ω ∧ canon (T ω t) = σ}`, the occurrence event
  `E_σ = {ω | ∃ t < R ω, canon (T ω t) = σ}`, and the a.e.-measurability of the fiber
  size `#{t < R ω | canon (T ω t) = σ}` in the table — the surface the 60.2 lintegral
  consumes.
* `coupling_canon` / `occurrence_canon_le_treeProd`: the canonical coupling — the
  canonical occurrence event is bounded by `treeProd A σ` (`coupling_canon` carries
  `hN : size σ ≤ N`; `occurrence_canon_le_treeProd` is the uniform wrapper absorbing
  `hN`).
* `canon_T_injective`: two occurring trees with equal canonical forms have equal times.
* `moserTardos_bound`: the main theorem (60.2) — the expected number of resamplings of
  `i` in the first `N` steps is at most `x i / (1 - x i)` under the LLL condition.
* `moserTardos_total` (60.3) / `moserTardos_tail` (60.4): the total expected number of
  resamplings is at most the LLL sum `∑ i, x i / (1 - x i)`, and the multiplicative
  tail `(N : ℝ≥0∞) * μN N μ {R = N} ≤ ofReal (∑ i, x i / (1 - x i))`. Both live in
  `section MainTheorem` with `moserTardos_bound`; the tail is the input of
  `moserTardos_exists`.
* `moserTardos_exists`: the constructive LLL (60.5, pick-free) — under the LLL
  condition some full assignment avoids every bad event.
-/

set_option autoImplicit false
set_option pp.unicode.fun true

noncomputable section

namespace TCSLean.MoserTardos

universe u v

open WitnessTree
open scoped List
open scoped BigOperators
open MeasureTheory
open scoped ENNReal

/-! ## The canonical form of a witness tree -/

/-- The canonical form of a witness tree: at every node the children are reordered into
the internal order of their label finset, each child replaced by its own canonical form;
the duplicate-label fallback `getD (mk x.1 [])` is unreachable on proper trees.
Well-founded on `size`. -/
noncomputable def canon {ι : Type u} [DecidableEq ι] : WitnessTree ι → WitnessTree ι
  | WitnessTree.mk a cs =>
      WitnessTree.mk a
        (((cs.map labelOf).toFinset).attach.toList.map
          (fun x =>
            canon ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 []))))
termination_by τ => size τ
decreasing_by
  simp_wf
  have hle :
      size ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) ≤
        (cs.map size).sum := by
    cases hf : cs.find? (fun c => labelOf c = x.1) with
    | none =>
        simp
        rcases List.mem_map.mp (List.mem_toFinset.mp x.2) with ⟨c, hc, _⟩
        exact le_trans (Nat.succ_le_of_lt (size_pos c)) (size_le_sum_of_mem hc)
    | some c =>
        simp
        exact size_le_sum_of_mem (List.mem_of_find?_eq_some hf)
  exact Nat.lt_of_le_of_lt hle (by omega)

/-- On a nodup list of child labels, two members of `cs` with the same label are
equal (the child-label Nodup that `Proper` provides). -/
private lemma eq_of_labelOf_eq_of_nodup {ι : Type u} {cs : List (WitnessTree ι)} :
    (cs.map labelOf).Nodup → ∀ c₁ ∈ cs, ∀ c₂ ∈ cs, labelOf c₁ = labelOf c₂ →
      c₁ = c₂ := by
  intro h
  induction cs with
  | nil => intro c₁ hc₁; cases hc₁
  | cons c cs ih =>
      intro c₁ hc₁ c₂ hc₂ hlab
      rw [List.mem_cons] at hc₁ hc₂
      rcases hc₁ with rfl | hc₁ <;> rcases hc₂ with rfl | hc₂
      · rfl
      · have hnot : labelOf c₁ ∉ cs.map labelOf := (List.nodup_cons.mp (by simpa using h)).1
        exact (hnot (by rw [hlab]; exact List.mem_map_of_mem hc₂)).elim
      · have hnot : labelOf c₂ ∉ cs.map labelOf := (List.nodup_cons.mp (by simpa using h)).1
        exact (hnot (by rw [← hlab]; exact List.mem_map_of_mem hc₁)).elim
      · exact ih ((List.nodup_cons.mp (by simpa using h)).2) c₁ hc₁ c₂ hc₂ hlab

/-- The canonical child selection: each selected child lies in `cs` and carries the
label it was selected for. -/
private lemma canonChild_spec {ι : Type u} [DecidableEq ι] {cs : List (WitnessTree ι)} {B : ι}
    (hB : B ∈ (cs.map labelOf).toFinset) :
    ((cs.find? (fun c => labelOf c = B)).getD (WitnessTree.mk B [])) ∈ cs ∧
      labelOf ((cs.find? (fun c => labelOf c = B)).getD (WitnessTree.mk B [])) = B := by
  have hf : cs.find? (fun c => labelOf c = B) ≠ none := by
    intro hf
    rw [List.find?_eq_none] at hf
    rcases List.mem_map.mp (List.mem_toFinset.mp hB) with ⟨c, hc, hcl⟩
    exact False.elim (by simpa [hcl] using hf c hc)
  cases hfind : cs.find? (fun c => labelOf c = B) with
  | none => exact (hf hfind).elim
  | some c =>
      refine ⟨?_, ?_⟩
      · simpa [hfind] using List.mem_of_find?_eq_some hfind
      · have hcl : labelOf c = B := by simpa using List.find?_some hfind
        simpa [hfind] using hcl

/-- A list of trees whose labels mirror a nodup list is nodup. -/
private lemma nodup_map_of_labelOf_inj {ι : Type u} {α : Type u} {f : α → ι}
    {g : ι → WitnessTree ι} {l : List α}
    (hgl : ∀ x ∈ l, labelOf (g (f x)) = f x) (hfl : (l.map f).Nodup) :
    (l.map (fun x => g (f x))).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (fun y hy => hgl y (by simp [hy])) ((List.nodup_cons.mp hfl).2)⟩
      intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨y, hy, hxy⟩
      have hx : f x ∉ l.map f := (List.nodup_cons.mp hfl).1
      have hxy' : f x = f y := by
        have h₁ := hgl x (by simp)
        have h₂ := hgl y (by simp [hy])
        rw [← hxy] at h₁
        simpa [h₂] using h₁.symm
      exact hx (by simpa [hxy'] using List.mem_map_of_mem hy)

/-- The canonical children of a proper tree form a permutation of the original
children (the label Nodup makes the label-set selection a bijection). -/
private lemma canonChildren_perm {ι : Type u} [DecidableEq ι] {cs : List (WitnessTree ι)}
    (hnodup : (cs.map labelOf).Nodup) :
    ((cs.map labelOf).toFinset).attach.toList.map
      (fun x => (cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) ~ cs := by
  let C : Finset ι := (cs.map labelOf).toFinset
  let g : ι → WitnessTree ι :=
    fun B => (cs.find? (fun c => labelOf c = B)).getD (WitnessTree.mk B [])
  have hnod1 : (C.attach.toList.map (fun x => g x.1)).Nodup := by
    apply nodup_map_of_labelOf_inj (f := fun x : {y // y ∈ C} => x.1) (g := g)
    · intro x hx
      exact (canonChild_spec x.2).2
    · exact List.Nodup.map Subtype.coe_injective (Finset.nodup_toList C.attach)
  have htoFinset : (C.attach.toList.map (fun x => g x.1)).toFinset = cs.toFinset := by
    ext a
    rw [List.mem_toFinset, List.mem_toFinset]
    constructor
    · intro hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨x, hx, ha⟩
      have hs := canonChild_spec x.2
      simpa [g, ha] using hs.1
    · intro ha
      rw [List.mem_map]
      refine ⟨⟨labelOf a, List.mem_toFinset.mpr (List.mem_map_of_mem ha)⟩, ?_, ?_⟩
      · exact Finset.mem_toList.mpr (Finset.mem_attach C
          ⟨labelOf a, List.mem_toFinset.mpr (List.mem_map_of_mem ha)⟩)
      · cases hfind : cs.find? (fun c => labelOf c = labelOf a) with
        | none =>
            rw [List.find?_eq_none] at hfind
            exact False.elim (by simpa using hfind a ha)
        | some c =>
            have hcl : labelOf c = labelOf a := by simpa using List.find?_some hfind
            have hca : c = a := eq_of_labelOf_eq_of_nodup hnodup c
              (List.mem_of_find?_eq_some hfind) a ha hcl
            simp [g, hfind, hca]
  exact List.perm_of_nodup_nodup_toFinset_eq hnod1 (List.Nodup.of_map labelOf hnodup) htoFinset

/-- The canonical form preserves the root label. -/
lemma labelOf_canon {ι : Type u} [DecidableEq ι] (τ : WitnessTree ι) :
    labelOf (canon τ) = labelOf τ := by
  cases τ with
  | mk a cs => rw [canon.eq_1]; rfl

/-- The canonical form preserves the size on proper trees (`Proper` is load-bearing:
canon drops duplicate-label children). -/
lemma size_canon {ι : Type u} [DecidableEq ι] {τ : WitnessTree ι} (hprop : Proper τ) :
    size (canon τ) = size τ := by
  refine WitnessTree.rec
      (motive_1 := fun τ => Proper τ → size (canon τ) = size τ)
      (motive_2 := fun cs => ∀ c ∈ cs, Proper c → size (canon c) = size c)
      ?_ ?_ ?_ τ hprop
  · intro a cs ih hprop
    have hnodup : (cs.map labelOf).Nodup := ((WitnessTree.proper_mk a cs).mp hprop).1
    have hproper : ∀ c ∈ cs, Proper c := ((WitnessTree.proper_mk a cs).mp hprop).2
    have hperm := canonChildren_perm hnodup
    have hsum :
        ((((cs.map labelOf).toFinset).attach.toList.map
          (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
            (WitnessTree.mk x.1 [])))).map size).sum = (cs.map size).sum := by
      have hmap :
          ((((cs.map labelOf).toFinset).attach.toList.map
            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
              (WitnessTree.mk x.1 [])))).map size) =
          ((((cs.map labelOf).toFinset).attach.toList.map
            (fun x => (cs.find? (fun c => labelOf c = x.1)).getD
              (WitnessTree.mk x.1 []))).map size) := by
        rw [List.map_map, List.map_map]
        refine List.map_congr_left ?_
        intro x hx
        have hs := canonChild_spec x.2
        exact ih ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1
          (hproper ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1)
      rw [hmap]
      exact List.Perm.sum_eq (List.Perm.map size hperm)
    rw [canon.eq_1]
    rw [WitnessTree.size_mk, WitnessTree.size_mk]
    rw [hsum]
  · intro c hc; cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc' <;> [exact ihc; exact ihcs c' hc']

/-- A `foldl max` accumulator is bounded by the accumulator plus the sum. -/
private lemma foldl_max_le_add_sum {α : Type u} {f : α → ℕ} {l : List α} :
    ∀ m : ℕ, (l.map f).foldl max m ≤ m + (l.map f).sum := by
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
      intro m
      simp only [List.map_cons, List.foldl_cons, List.sum_cons]
      have h₁ := ih (max m (f a))
      have hm : max m (f a) ≤ m + f a :=
        Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
      omega

/-- Pointwise smaller functions give pointwise smaller sums. -/
private lemma sum_le_sum_of_pointwise {α : Type u} {f g : α → ℕ} {l : List α}
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : f a ≤ g a := h a (by simp)
      have ih' : (l.map f).sum ≤ (l.map g).sum :=
        ih (fun a' ha' => h a' (List.mem_cons_of_mem a ha'))
      simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add ha ih'

/-- The max of a `foldl max` is bounded by the sum of a pointwise-larger list. -/
private lemma foldl_max_le_sum {α : Type u} {f g : α → ℕ} {l : List α}
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).foldl max 0 ≤ (l.map g).sum := by
  have h₁ : (l.map f).foldl max 0 ≤ 0 + (l.map f).sum := foldl_max_le_add_sum (f := f) 0
  have h₂ : (l.map f).sum ≤ (l.map g).sum := sum_le_sum_of_pointwise h
  omega

/-- `sum + 1 ≤` the sum of a pointwise `+1`-larger list. -/
private lemma sum_succ_le_sum {α : Type u} {f g : α → ℕ} {a : α} {l : List α}
    (h : ∀ b ∈ a :: l, f b + 1 ≤ g b) :
    ((a :: l).map f).sum + 1 ≤ ((a :: l).map g).sum := by
  induction l with
  | nil => simpa using h a (by simp)
  | cons b l ih =>
      have ha : f a + 1 ≤ g a := h a (by simp)
      have hb : f b + 1 ≤ g b := h b (by simp)
      have ih' : ((a :: l).map f).sum + 1 ≤ ((a :: l).map g).sum :=
        ih (fun b' hb' => h b' (by
          rcases (List.mem_cons.mp hb') with hEq | hIn
          · simp [hEq]
          · exact List.mem_cons_of_mem a (List.mem_cons_of_mem b hIn)))
      simp only [List.map_cons, List.sum_cons] at ih' ⊢
      omega

/-- The foldl-max of a nonempty child list plus one is bounded by the size sum. -/
private lemma foldl_max_succ_le_sum {ι : Type u} {cs : List (WitnessTree ι)} {c : WitnessTree ι}
    (h : ∀ d ∈ c :: cs, height d + 1 ≤ size d) :
    ((c :: cs).map height).foldl max 0 + 1 ≤ ((c :: cs).map size).sum := by
  have hfold : ((c :: cs).map height).foldl max 0 ≤ ((c :: cs).map height).sum :=
    foldl_max_le_sum (f := height) (g := height) (by intro a ha; rfl)
  have hsum : ((c :: cs).map height).sum + 1 ≤ ((c :: cs).map size).sum :=
    sum_succ_le_sum (f := height) (g := size) h
  omega

/-- The `foldl max` accumulator is a lower bound of the fold result. -/
private lemma le_foldl_max {α : Type u} {f : α → ℕ} {l : List α} :
    ∀ m : ℕ, m ≤ (l.map f).foldl max m := by
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
      intro m
      simp only [List.map_cons, List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _) (ih (max m (f a)))

/-- Each child's height is bounded by the children-height foldl-max. -/
private lemma height_le_foldl_max {ι : Type u} {cs : List (WitnessTree ι)} {c : WitnessTree ι}
    (hc : c ∈ cs) :
    height c ≤ (cs.map height).foldl max 0 := by
  have h : ∀ m : ℕ, height c ≤ (cs.map height).foldl max m := by
    induction cs with
    | nil => cases hc
    | cons d ds ih =>
        intro m
        rw [List.mem_cons] at hc
        rcases hc with rfl | hc
        · rw [List.map_cons, List.foldl_cons]
          exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max (f := height) (max m (height c)))
        · rw [List.map_cons, List.foldl_cons]
          exact ih hc (max m (height d))
  exact h 0

/-- The children-height foldl-max is bounded by the tree height. -/
private lemma foldl_max_height_le {ι : Type u} {a : ι} {cs : List (WitnessTree ι)} :
    (cs.map height).foldl max 0 ≤ height (WitnessTree.mk a cs) := by
  cases cs with
  | nil => simp [height]
  | cons c cs' => simp [height]

/-- The height of a tree is bounded by its size minus one. -/
lemma height_le_size_pred {ι : Type u} (τ : WitnessTree ι) :
    height τ ≤ size τ - 1 := by
  refine WitnessTree.rec
      (motive_1 := fun τ => height τ ≤ size τ - 1)
      (motive_2 := fun cs => ∀ c ∈ cs, height c ≤ size c - 1)
      ?_ ?_ ?_ τ
  · intro a cs ih
    cases cs with
    | nil => simp [height]
    | cons c cs' =>
        have hb : ((c :: cs').map height).foldl max 0 + 1 ≤ ((c :: cs').map size).sum := by
          apply foldl_max_succ_le_sum
          intro d hd
          have hpos : 0 < size d := size_pos d
          have hih := ih d hd
          omega
        simp [height] at hb ⊢
        omega
  · intro c hc; cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc' <;> [exact ihc; exact ihcs c' hc']

/-! ## The statement set of the counting identity -/

section CountLogIdentity

variable {ι : Type u} [DecidableEq ι] [Inhabited ι] [Fintype ι]
variable {κ : Type u} [DecidableEq κ]
variable {Ω : κ → Type v}
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-! ## Witness condition of the construction -/

/-- Definitional copy of 30.2's `maxOption` (namespace-private). -/
private def mtMaxOption (m o : Option ℕ) : Option ℕ :=
  match m, o with
  | none, o => o
  | m, none => m
  | some a, some b => some (max a b)

omit [Inhabited ι] [Fintype ι] in
/-- The `attachBelow` equation, re-expressed with the local `mtMaxOption` (definitionally
equal to 30.2's private `maxOption`, so `rfl` closes it after the equation-lemma rewrite). -/
private lemma attachBelow_mk_treeElig (a : ℕ × ι) {s : ℕ} {i : ι}
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

omit [Inhabited ι] in
/-- Eligibility transport: `treeElig (s,i) (s',i')` implies `i ∈ gammaPlus vbl i'`. -/
private lemma treeElig_gammaPlus {s s' : ℕ} {i i' : ι} (h : treeElig vbl (s, i) (s', i')) :
    i ∈ gammaPlus vbl i' := by
  unfold treeElig at h
  rcases h with rfl | h
  · simp [gammaPlus]
  · by_cases hii : i = i'
    · simp [gammaPlus, hii]
    · have : i ∈ insert i' ((overlapGraph vbl).neighborFinset i') := by
        rw [Finset.mem_insert]
        right
        rw [mem_overlap_neighborFinset]
        exact ⟨by intro h; exact hii h.symm, by simpa [Finset.inter_comm] using h⟩
      simpa [gammaPlus] using this

omit [Inhabited ι] [Fintype ι] in
/-- `attachBelow` preserves the root label (re-derived: 30.3's in-section version is
private). -/
private lemma labelOf_attachBelow_treeElig (p : ℕ × ι) (τ : WitnessTree (ℕ × ι)) :
    WitnessTree.labelOf (WitnessTree.attachBelow (treeElig vbl) p τ) =
      WitnessTree.labelOf τ := by
  rcases WitnessTree.labelAt_attachBelow (elig := treeElig vbl) (i := p) (τ := τ) (p := [])
      (hp := .root) with ⟨hp', h⟩
  simpa using h

omit [Inhabited ι] [Fintype ι] in
/-- The abstract child-label list is unchanged under the `attachInFirst` step. -/
private lemma forgetTime_attachInFirst_map_labelOf {s : ℕ} {i : ι}
    {dd : ℕ} (cs : List (WitnessTree (ℕ × ι))) :
    ((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime).map
        WitnessTree.labelOf = (cs.map forgetTime).map WitnessTree.labelOf := by
  induction cs with
  | nil => simp [WitnessTree.attachInFirst]
  | cons c cs ih =>
      by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s, i) c = some (dd - 1)
      · simp [WitnessTree.attachInFirst, hd, labelOf_forgetTime, labelOf_attachBelow_treeElig]
      · simp [WitnessTree.attachInFirst, hd, ih, labelOf_forgetTime]

omit [Inhabited ι] in
/-- Recursive witness condition of the `attachInFirst` step at the abstract level: the
kept children are witnesses by hypothesis, the replaced child by the induction hypothesis. -/
private lemma forgetTime_attachInFirst_isWitness {s : ℕ} {i : ι}
    {dd : ℕ} (cs : List (WitnessTree (ℕ × ι)))
    (hih : ∀ c ∈ cs, IsWitnessTree vbl (forgetTime c) →
      IsWitnessTree vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c)))
    (hwit : ∀ c ∈ cs, IsWitnessTree vbl (forgetTime c)) :
    ∀ c' ∈ (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime,
      IsWitnessTree vbl c' := by
  induction cs with
  | nil => simp [WitnessTree.attachInFirst]
  | cons c cs ih =>
      by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s, i) c = some (dd - 1)
      · simp only [WitnessTree.attachInFirst, hd, if_true]
        intro c' hc'
        rw [List.mem_map] at hc'; rcases hc' with ⟨d, hdmem, rfl⟩
        rw [List.mem_cons] at hdmem
        rcases hdmem with hEq | hdmem
        · subst d
          exact hih c (by simp) (hwit c (by simp))
        · exact hwit d (by simp [hdmem])
      · simp only [WitnessTree.attachInFirst, hd, if_false]
        intro c' hc'
        rw [List.mem_map] at hc'; rcases hc' with ⟨d, hdmem, rfl⟩
        rw [List.mem_cons] at hdmem
        rcases hdmem with hEq | hdmem
        · subst d
          exact hwit c (by simp)
        · exact ih (fun c₀ hc₀ => hih c₀ (by simp [hc₀]))
            (fun c₀ hc₀ => hwit c₀ (by simp [hc₀])) (forgetTime d)
            (by rw [List.mem_map]; exact ⟨d, hdmem, rfl⟩)

omit [Inhabited ι] in
/-- One insertion step preserves the witness condition: if the `forgetTime`-image of `τ`
is a witness tree, so is that of `attachBelow (treeElig vbl) (s, i) τ`. -/
private theorem forgetTime_attachBelow_isWitness {s : ℕ} {i : ι}
    (τ : WitnessTree (ℕ × ι)) (hτ : IsWitnessTree vbl (forgetTime τ)) :
    IsWitnessTree vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) τ)) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => IsWitnessTree vbl (forgetTime τ) →
        IsWitnessTree vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) τ)))
      (motive_2 := fun cs => ∀ c ∈ cs, IsWitnessTree vbl (forgetTime c) →
        IsWitnessTree vbl (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c)))
      ?_ ?_ ?_ τ hτ
  · intro a cs ih hτ
    cases hd : cs.foldl (fun m c => mtMaxOption m
        ((WitnessTree.deepestEligible (treeElig vbl) (s, i) c).map (· + 1))) none with
    | none =>
        by_cases ha : treeElig vbl (s, i) a
        · have hτ' : (∀ c ∈ cs.map forgetTime, labelOf c ∈ gammaPlus vbl a.2) ∧
              ∀ c ∈ cs.map forgetTime, IsWitnessTree vbl c := by
            simpa [forgetTime, IsWitnessTree] using hτ
          have hlabels : ∀ c ∈ cs.map forgetTime ++ [WitnessTree.mk i []],
              labelOf c ∈ gammaPlus vbl a.2 := by
            intro c hc
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · exact hτ'.1 c hc
            · rw [List.mem_singleton] at hc; subst c
              simpa [WitnessTree.labelOf] using treeElig_gammaPlus vbl ha
          have hwits : ∀ c ∈ cs.map forgetTime ++ [WitnessTree.mk i []],
              IsWitnessTree vbl c := by
            intro c hc
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · exact hτ'.2 c hc
            · rw [List.mem_singleton] at hc; subst c
              simp [IsWitnessTree]
          have hgoal : IsWitnessTree vbl (WitnessTree.mk a.2
              (cs.map forgetTime ++ [WitnessTree.mk i []])) := by
            rw [IsWitnessTree]
            constructor
            · exact hlabels
            · exact hwits
          simpa [attachBelow_mk_treeElig vbl a cs, hd, ha, forgetTime] using hgoal
        · simpa [attachBelow_mk_treeElig vbl a cs, hd, ha] using hτ
    | some dd =>
        have hτ' : (∀ c ∈ cs.map forgetTime, labelOf c ∈ gammaPlus vbl a.2) ∧
            ∀ c ∈ cs.map forgetTime, IsWitnessTree vbl c := by
          simpa [forgetTime, IsWitnessTree] using hτ
        have hlabels :
            ∀ c' ∈ (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime,
            labelOf c' ∈ gammaPlus vbl a.2 := by
          intro c' hc'
          have hmem : labelOf c' ∈ (((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map
              forgetTime).map WitnessTree.labelOf) := by
            rw [List.mem_map]
            exact ⟨c', hc', rfl⟩
          rw [forgetTime_attachInFirst_map_labelOf vbl cs] at hmem
          rw [List.mem_map] at hmem
          rcases hmem with ⟨d, hd, hdl⟩
          rw [← hdl]
          exact hτ'.1 d hd
        have hwits_all : ∀ c ∈ cs, IsWitnessTree vbl (forgetTime c) := by
          intro c hc
          exact hτ'.2 (forgetTime c) (by rw [List.mem_map]; exact ⟨c, hc, rfl⟩)
        have hwits :
            ∀ c' ∈ (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime,
            IsWitnessTree vbl c' := forgetTime_attachInFirst_isWitness vbl cs ih hwits_all
        have hgoal : IsWitnessTree vbl (WitnessTree.mk a.2
            ((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime)) := by
          rw [IsWitnessTree]
          constructor
          · exact hlabels
          · exact hwits
        simpa [attachBelow_mk_treeElig vbl a cs, hd, forgetTime] using hgoal
  · intro c hc; cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc' <;> [exact ihc; exact ihcs c' hc']

omit [Inhabited ι] in
/-- The reverse-scan fold preserves the witness condition (list induction on the fold's
range list, with the accumulated tree generalized). -/
private theorem foldr_forgetTime_isWitness {Λ : ℕ → Option ι} :
    ∀ l : List ℕ, ∀ τ : WitnessTree (ℕ × ι), IsWitnessTree vbl (forgetTime τ) →
      IsWitnessTree vbl (forgetTime (l.foldr
        (fun s τ => match Λ s with
          | none => τ
          | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) τ)) := by
  intro l
  induction l with
  | nil => intro τ hτ; simpa using hτ
  | cons s l ih =>
      intro τ hτ
      rw [List.foldr_cons]
      cases h : Λ s with
      | none => simpa using ih τ hτ
      | some i => apply forgetTime_attachBelow_isWitness; exact ih τ hτ

/-- The time-labeled witness tree satisfies the witness condition. -/
lemma treeAt_isWitnessTree {Λ : ℕ → Option ι} {t : ℕ} :
    IsWitnessTree vbl (forgetTime (treeAt vbl Λ t)) := by
  unfold treeAt
  apply foldr_forgetTime_isWitness
  cases h : Λ t <;> simp [forgetTime, IsWitnessTree]

/-- The witness tree of the execution table satisfies the witness condition. -/
lemma T_isWitnessTree {ω : ΩN N Ω} {t : ℕ} :
    IsWitnessTree vbl (T vbl A pick hpick ω t) := by
  unfold T
  exact treeAt_isWitnessTree vbl

omit [Inhabited ι] in
/-- The canonical form of a proper witness tree of height at most `h` lies in
`gwFinsetHeight vbl (labelOf τ) h`. -/
lemma canon_mem_gwFinsetHeight {τ : WitnessTree ι} {h : ℕ} (hprop : Proper τ)
    (hwit : IsWitnessTree vbl τ) (hheight : height τ ≤ h) :
    canon τ ∈ gwFinsetHeight vbl (labelOf τ) h := by
  induction h generalizing τ with
  | zero =>
      cases τ with
      | mk a cs =>
          cases cs with
          | nil =>
              have hcanon : canon (WitnessTree.mk a []) = WitnessTree.mk a [] := by
                rw [canon.eq_1]
                simp
              rw [hcanon, WitnessTree.labelOf_mk]
              exact Finset.mem_singleton_self _
          | cons c cs' =>
              have hh : height (WitnessTree.mk a (c :: cs')) ≤ 0 := by simpa using hheight
              simp [height] at hh
  | succ h₀ ih =>
      cases τ with
      | mk a cs =>
          refine Finset.mem_biUnion.mpr ⟨(cs.map labelOf).toFinset, ?_, ?_⟩
          · rw [Finset.mem_powerset]
            intro B hB
            rw [List.mem_toFinset] at hB
            rcases List.mem_map.mp hB with ⟨c, hc, rfl⟩
            have hw : ∀ c ∈ cs, labelOf c ∈ gammaPlus vbl a := by
              have hwit_and : (∀ c ∈ cs, labelOf c ∈ gammaPlus vbl a) ∧
                  ∀ c ∈ cs, IsWitnessTree vbl c := by
                simpa [IsWitnessTree] using hwit
              exact hwit_and.1
            exact hw c hc
          · refine Finset.mem_image.mpr ⟨
              (fun B _hB => canon ((cs.find? (fun c => labelOf c = B)).getD (WitnessTree.mk B []))),
              ?_, ?_⟩
            · rw [Finset.mem_pi]
              intro B hB
              have hf : cs.find? (fun c => labelOf c = B) ≠ none := by
                intro hnone
                rw [List.find?_eq_none] at hnone
                rcases List.mem_map.mp (List.mem_toFinset.mp hB) with ⟨c, hc, hcl⟩
                exact False.elim (by simpa [hcl] using hnone c hc)
              rcases hfind : cs.find? (fun c => labelOf c = B) with _ | c'
              · exact (hf hfind).elim
              · have hc' : c' ∈ cs := List.mem_of_find?_eq_some hfind
                have hcl' : labelOf c' = B := by simpa using List.find?_some hfind
                have hprop' : Proper c' := ((WitnessTree.proper_mk a cs).mp hprop).2 c' hc'
                have hwit' : IsWitnessTree vbl c' := by
                  have hw : (∀ c ∈ cs, labelOf c ∈ gammaPlus vbl a) ∧
                      ∀ c ∈ cs, IsWitnessTree vbl c := by
                    simpa [IsWitnessTree] using hwit
                  exact hw.2 c' hc'
                have hheight' : height c' ≤ h₀ := by
                  have hle : height c' ≤ (cs.map height).foldl max 0 := height_le_foldl_max hc'
                  have hcons : ∃ c₀ cs₀, cs = c₀ :: cs₀ := by
                    rcases List.mem_iff_append.mp hc' with ⟨as, bs, hcs⟩
                    rw [hcs]
                    cases as with
                    | nil => exact ⟨c', bs, rfl⟩
                    | cons c₀ as' => exact ⟨c₀, as' ++ c' :: bs, rfl⟩
                  rcases hcons with ⟨c₀, cs₀, hcons⟩
                  rw [hcons] at hle
                  have hh : ((c₀ :: cs₀).map height).foldl max 0 ≤ h₀ := by
                    have hh' : height (WitnessTree.mk a (c₀ :: cs₀)) ≤ h₀ + 1 := by
                      simpa [hcons] using hheight
                    have hh'' : ((c₀ :: cs₀).map height).foldl max 0 + 1 ≤ h₀ + 1 := by
                      simpa [WitnessTree.height] using hh'
                    omega
                  exact Nat.le_trans hle hh
                have hmem : canon c' ∈ gwFinsetHeight vbl (labelOf c') h₀ :=
                  ih (τ := c') hprop' hwit' hheight'
                simpa [hfind, hcl'] using hmem
            · change WitnessTree.mk a (((cs.map labelOf).toFinset).attach.toList.map
                (fun x =>
                  canon ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])))) =
                canon (WitnessTree.mk a cs)
              simp [canon]

omit [Fintype ι] in
/-- Before the stopping time, the log resampled `i` exactly when the witness tree is
rooted at `i`. -/
lemma log_eq_some_iff_labelOf_T {ω : ΩN N Ω} {t : ℕ}
    (ht : t < R vbl A pick hpick ω) (i : ι) :
    log vbl A pick hpick ω t = some i ↔ labelOf (T vbl A pick hpick ω t) = i := by
  constructor
  · intro h
    exact T_root_label vbl A pick hpick h
  · intro h
    have hne : log vbl A pick hpick ω t ≠ none :=
      (log_ne_none_iff_lt_R vbl A pick hpick ω).mpr ht
    rcases hlog : log vbl A pick hpick ω t with _ | j
    · exact (hne hlog).elim
    · have hroot : labelOf (treeAt vbl (log vbl A pick hpick ω) t) = (t, j) :=
        treeAt_root_label vbl hlog
      have hj : j = i := by
        have hL : (labelOf (treeAt vbl (log vbl A pick hpick ω) t)).2 = i := by
          simpa [T, labelOf_forgetTime] using h
        simpa [hroot] using hL
      exact congrArg some hj

/-- The counting identity (fiber-card form): the number of resamplings of event `i`
equals the sum over the canonical Galton–Watson domain of the fiber sizes of
`t ↦ canon (T ω t)`. -/
lemma countLog_eq_sum_card {ω : ΩN N Ω} (i : ι) :
    countLog (log vbl A pick hpick) ω i =
      ∑ σ ∈ gwFinsetHeight vbl i (N - 1),
        ((Finset.range (R vbl A pick hpick ω)).filter
          (fun t => canon (T vbl A pick hpick ω t) = σ)).card := by
  let Rω := R vbl A pick hpick ω
  let S := (Finset.range Rω).filter (fun t => log vbl A pick hpick ω t = some i)
  have hcount : countLog (log vbl A pick hpick) ω i = S.card := by
    unfold countLog
    apply congrArg Finset.card
    apply Finset.ext; intro t
    simp only [S, Rω, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      rcases h with ⟨htN, hlog⟩
      have htR : t < R vbl A pick hpick ω :=
        (log_ne_none_iff_lt_R vbl A pick hpick ω).mp (by
          intro hnone
          rw [hnone] at hlog
          cases hlog)
      exact ⟨htR, hlog⟩
    · intro h
      rcases h with ⟨htR, hlog⟩
      exact ⟨Nat.lt_of_lt_of_le htR (R_le vbl A pick hpick ω), hlog⟩
  have hfib : S.card = ∑ σ ∈ gwFinsetHeight vbl i (N - 1),
      (S.filter (fun t => canon (T vbl A pick hpick ω t) = σ)).card := by
    refine Finset.card_eq_sum_card_fiberwise (s := S) (t := gwFinsetHeight vbl i (N - 1))
      (f := fun t => canon (T vbl A pick hpick ω t)) ?_
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨htR, hlog⟩
    have htR' : t < R vbl A pick hpick ω := by simpa [Rω] using (Finset.mem_range.mp htR)
    have hroot : labelOf (T vbl A pick hpick ω t) = i := T_root_label vbl A pick hpick hlog
    have hproper : Proper (T vbl A pick hpick ω t) := (T_isGood vbl A pick hpick).1
    have hwit : IsWitnessTree vbl (T vbl A pick hpick ω t) := T_isWitnessTree vbl A pick hpick
    have hh : height (T vbl A pick hpick ω t) ≤ N - 1 :=
      Nat.le_trans (height_le_size_pred (T vbl A pick hpick ω t))
        (Nat.sub_le_sub_right (T_size_le_N vbl A pick hpick htR') 1)
    have hmem : canon (T vbl A pick hpick ω t) ∈
        gwFinsetHeight vbl (labelOf (T vbl A pick hpick ω t)) (N - 1) :=
      canon_mem_gwFinsetHeight vbl hproper hwit hh
    simpa [hroot] using hmem
  have hfiber : ∀ σ ∈ gwFinsetHeight vbl i (N - 1),
      (S.filter (fun t => canon (T vbl A pick hpick ω t) = σ)) =
        ((Finset.range Rω).filter (fun t => canon (T vbl A pick hpick ω t) = σ)) := by
    intro σ hσ
    apply Finset.ext; intro t
    simp only [S, Finset.mem_filter, Finset.mem_range, and_assoc]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      refine ⟨h.1, ?_, h.2⟩
      have hσl : labelOf σ = i := labelOf_mem_gwFinsetHeight vbl i (N - 1) hσ
      have hT : labelOf (T vbl A pick hpick ω t) = i := by
        rw [← hσl, ← labelOf_canon (T vbl A pick hpick ω t)]
        exact congrArg labelOf h.2
      exact (log_eq_some_iff_labelOf_T vbl A pick hpick h.1 i).mpr hT
  rw [hcount]
  calc
    S.card = ∑ σ ∈ gwFinsetHeight vbl i (N - 1),
        (S.filter (fun t => canon (T vbl A pick hpick ω t) = σ)).card := hfib
    _ = ∑ σ ∈ gwFinsetHeight vbl i (N - 1),
        ((Finset.range Rω).filter (fun t => canon (T vbl A pick hpick ω t) = σ)).card := by
        refine Finset.sum_congr rfl ?_
        intro σ hσ
        rw [hfiber σ hσ]

end CountLogIdentity

section MeasurableOccurrence

variable {ι : Type u} [DecidableEq ι] [Inhabited ι] [Fintype ι]
variable {κ : Type u} [DecidableEq κ] [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hA : ∀ i, MeasurableSet (A i))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-- Lift a finite log pattern `p : Fin (t + 1) → Option ι` to the ℕ-indexed log
`treeAt` consumes (`treeAt … t` only scans `range t` plus the seed at `t`, so the `none`
pad beyond `t + 1` is never read). -/
private def extendPattern {t : ℕ} (p : Fin (t + 1) → Option ι) : ℕ → Option ι :=
  fun u => if hu : u < t + 1 then p ⟨u, hu⟩ else none

omit [DecidableEq ι] [Inhabited ι] [Fintype ι] in
/-- `extendPattern` at times below `t + 1` recovers the pattern entry. -/
private lemma extendPattern_of_lt {t : ℕ} (p : Fin (t + 1) → Option ι) {u : ℕ}
    (hu : u < t + 1) : extendPattern p u = p ⟨u, hu⟩ := by
  unfold extendPattern
  rw [dif_pos hu]

omit [Fintype ι] [Fintype κ] in
/-- `treeAt` depends on the log only through its values at times `≤ t` (the fold over
`List.range t` is congruent pointwise via `List.foldr_ext`; the seed at `t` via `h`). -/
private lemma treeAt_congr {Λ₁ Λ₂ : ℕ → Option ι} {t : ℕ}
    (h : ∀ s, s ≤ t → Λ₁ s = Λ₂ s) :
    treeAt vbl Λ₁ t = treeAt vbl Λ₂ t := by
  unfold treeAt
  rw [h t (Nat.le_refl t)]
  refine List.foldr_ext _ _ _ ?_
  intro s hs b
  change (match Λ₁ s with
    | none => b
    | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) b) =
    (match Λ₂ s with
    | none => b
    | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) b)
  rw [h s (Nat.le_of_lt (List.mem_range.mp hs))]

include hA in
/-- The set of tables where at time `t < R` the canonical occurring tree is `σ` is
measurable: by_cases `t ≤ N` (empty beyond `N`); the main case is a finite union over log
patterns `p : Fin (t + 1) → Option ι` of `⋂_{s ≤ t} {ω | log … ω s = p s}` intersected
with the ω-free condition `p t ≠ none ∧ canon (forgetTime (treeAt vbl pℕ t)) = σ` (on the
fiber `t < R ⟺ log ω t ≠ none` via `log_ne_none_iff_lt_R`; per-`s` fibers from
`measurableSet_log_eq_some` and `{log = none} = {s < R}ᶜ`, plus the private
treeAt-prefix congruence). -/
theorem measurableSet_occ_canon {t : ℕ} (σ : WitnessTree ι) :
    MeasurableSet {ω : ΩN N Ω |
      t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ} := by
  classical
  by_cases htN : t ≤ N
  · have htN1 : t < N + 1 := Nat.lt_succ_of_le htN
    have hset : {ω : ΩN N Ω |
        t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ} =
        ⋃ p : Fin (t + 1) → Option ι,
          (⋂ s : Fin (t + 1), {ω : ΩN N Ω | log vbl A pick hpick ω s.1 = p s}) ∩
          (if p ⟨t, Nat.lt_succ_self t⟩ ≠ none ∧
              canon (forgetTime (treeAt vbl (extendPattern p) t)) = σ then
            (Set.univ : Set (ΩN N Ω)) else ∅) := by
      ext ω
      constructor
      · intro hω
        rcases hω with ⟨hR, hcan⟩
        rw [Set.mem_iUnion]
        refine ⟨fun s : Fin (t + 1) => log vbl A pick hpick ω s.1, ?_⟩
        rw [Set.mem_inter_iff]
        constructor
        · rw [Set.mem_iInter]
          intro s
          change log vbl A pick hpick ω s.1 = log vbl A pick hpick ω s.1
          rfl
        · have hcond :
              (fun s : Fin (t + 1) => log vbl A pick hpick ω s.1)
                ⟨t, Nat.lt_succ_self t⟩ ≠ none ∧
              canon (forgetTime (treeAt vbl
                (extendPattern (fun s : Fin (t + 1) => log vbl A pick hpick ω s.1)) t)) = σ := by
            constructor
            · change log vbl A pick hpick ω t ≠ none
              exact (log_ne_none_iff_lt_R (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω
                (t := t)).mpr hR
            · have hcongr : treeAt vbl
                  (extendPattern (fun s : Fin (t + 1) => log vbl A pick hpick ω s.1)) t =
                treeAt vbl (log vbl A pick hpick ω) t := by
                apply treeAt_congr
                intro u hu
                have hu' : u < t + 1 := Nat.lt_succ_of_le hu
                rw [extendPattern_of_lt (fun s : Fin (t + 1) => log vbl A pick hpick ω s.1) hu']
              calc
                canon (forgetTime (treeAt vbl
                    (extendPattern (fun s : Fin (t + 1) => log vbl A pick hpick ω s.1)) t))
                    = canon (forgetTime (treeAt vbl (log vbl A pick hpick ω) t)) := by
                      exact congrArg canon (congrArg forgetTime hcongr)
                _ = canon (T vbl A pick hpick ω t) := rfl
                _ = σ := hcan
          rw [if_pos hcond]
          exact Set.mem_univ ω
      · intro hω
        rw [Set.mem_iUnion] at hω
        rcases hω with ⟨p, hpω⟩
        rw [Set.mem_inter_iff] at hpω
        rcases hpω with ⟨hfib, hif⟩
        rw [Set.mem_iInter] at hfib
        by_cases hcond : p ⟨t, Nat.lt_succ_self t⟩ ≠ none ∧
            canon (forgetTime (treeAt vbl (extendPattern p) t)) = σ
        · rw [if_pos hcond] at hif
          have hlogt : log vbl A pick hpick ω t = p ⟨t, Nat.lt_succ_self t⟩ := by
            simpa using hfib ⟨t, Nat.lt_succ_self t⟩
          have hne : log vbl A pick hpick ω t ≠ none := by
            rw [hlogt]
            exact hcond.1
          have hR : t < R vbl A pick hpick ω :=
            (log_ne_none_iff_lt_R (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω
              (t := t)).mp hne
          have hcongr : treeAt vbl (log vbl A pick hpick ω) t =
              treeAt vbl (extendPattern p) t := by
            apply treeAt_congr
            intro u hu
            have hu' : u < t + 1 := Nat.lt_succ_of_le hu
            rw [extendPattern_of_lt p hu']
            simpa using hfib ⟨u, hu'⟩
          refine ⟨hR, ?_⟩
          calc
            canon (T vbl A pick hpick ω t)
                = canon (forgetTime (treeAt vbl (log vbl A pick hpick ω) t)) := rfl
            _ = canon (forgetTime (treeAt vbl (extendPattern p) t)) := by
                exact congrArg canon (congrArg forgetTime hcongr)
            _ = σ := hcond.2
        · rw [if_neg hcond] at hif
          exact False.elim hif
    rw [hset]
    haveI : Finite (Fin (t + 1) → Option ι) := Finite.of_fintype (Fin (t + 1) → Option ι)
    haveI : Countable (Fin (t + 1) → Option ι) := Finite.to_countable
    refine MeasurableSet.iUnion (fun p : Fin (t + 1) → Option ι => ?_)
    refine MeasurableSet.inter ?_ ?_
    · haveI : Finite (Fin (t + 1)) := Finite.of_fintype (Fin (t + 1))
      haveI : Countable (Fin (t + 1)) := Finite.to_countable
      refine MeasurableSet.iInter (fun s : Fin (t + 1) => ?_)
      by_cases hs : p s = none
      · rw [hs]
        rw [show {ω : ΩN N Ω | log vbl A pick hpick ω s.1 = none} =
            ({ω : ΩN N Ω | s.1 < R vbl A pick hpick ω})ᶜ from by
          ext ω
          constructor
          · intro hlog
            rw [Set.mem_compl_iff]
            intro hmem
            change s.1 < R vbl A pick hpick ω at hmem
            exact ((log_ne_none_iff_lt_R (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω
              (t := s.1)).mpr hmem) hlog
          · intro hmem
            rw [Set.mem_compl_iff] at hmem
            change ¬ s.1 < R vbl A pick hpick ω at hmem
            exact log_eq_none_of_R_le (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω
              (Nat.le_of_not_gt hmem)]
        exact (measurableSet_lt_R (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) (hA := hA)
          (t := ⟨s.1, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ s.2) htN1⟩)).compl
      · rcases hps : p s with _ | i
        · exact False.elim (hs hps)
        · exact measurableSet_log_eq_some (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
            (hA := hA) (t := ⟨s.1, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ s.2) htN1⟩) (i := i)
    · by_cases hcond : p ⟨t, Nat.lt_succ_self t⟩ ≠ none ∧
          canon (forgetTime (treeAt vbl (extendPattern p) t)) = σ
      · rw [if_pos hcond]
        exact MeasurableSet.univ
      · rw [if_neg hcond]
        exact MeasurableSet.empty
  · have hset : {ω : ΩN N Ω |
        t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ} =
        (∅ : Set (ΩN N Ω)) := by
      ext ω
      change (t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ) ↔ False
      constructor
      · rintro ⟨hR, _⟩
        exact htN (le_trans (Nat.le_of_lt hR) (R_le vbl A pick hpick ω))
      · intro h
        exact h.elim
    rw [hset]
    exact MeasurableSet.empty

include hA in
/-- The 60.2 `E_σ`: the set of tables where `σ` occurs as the canonical occurring tree
before `R` is measurable (iUnion over `Fin N` of `measurableSet_occ_canon`, since
`t < R ≤ N`). -/
theorem measurableSet_occ (σ : WitnessTree ι) :
    MeasurableSet {ω : ΩN N Ω |
      ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ} := by
  classical
  have hset : {ω : ΩN N Ω |
      ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ} =
      ⋃ t : Fin N, {ω : ΩN N Ω |
        t.1 < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t.1) = σ} := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨t, htR, hcan⟩
      rw [Set.mem_iUnion]
      refine ⟨⟨t, Nat.lt_of_lt_of_le htR (R_le vbl A pick hpick ω)⟩, ?_⟩
      change t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ
      exact ⟨htR, hcan⟩
    · intro hω
      rw [Set.mem_iUnion] at hω
      rcases hω with ⟨t, ht⟩
      change t.1 < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t.1) = σ at ht
      exact ⟨t.1, ht.1, ht.2⟩
  rw [hset]
  haveI : Finite (Fin N) := Finite.of_fintype (Fin N)
  haveI : Countable (Fin N) := Finite.to_countable
  exact MeasurableSet.iUnion (fun t : Fin N =>
    measurableSet_occ_canon (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) (hA := hA)
      (t := t.1) σ)

include hA in
/-- The fiber size of `t ↦ canon (T ω t)` over `t < R` is a.e.-measurable in the table
(the ℕ-valued fiber count is measurable via the indicator-sum identity over `range N` +
`Measurable.indicator` + `Finset.measurable_sum`, and the cast into `ℝ≥0∞` is measurable
from the discrete measurable space on `ℕ`). -/
theorem aemeasurable_card_fiber (μ : Measure (ΩN N Ω)) (σ : WitnessTree ι) :
    AEMeasurable (fun ω =>
      (((Finset.range (R vbl A pick hpick ω)).filter
        (fun t => canon (T vbl A pick hpick ω t) = σ)).card : ℝ≥0∞)) μ := by
  classical
  let S (t : ℕ) : Set (ΩN N Ω) :=
    {ω | t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ}
  have hS (t : ℕ) : MeasurableSet (S t) :=
    measurableSet_occ_canon (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) (hA := hA)
      (t := t) σ
  have hcard : Measurable (fun ω : ΩN N Ω =>
      ((Finset.range (R vbl A pick hpick ω)).filter
        (fun t => canon (T vbl A pick hpick ω t) = σ)).card) := by
    have hfiber : Measurable (fun ω : ΩN N Ω =>
        ∑ t ∈ Finset.range N, (S t).indicator (fun _ => (1 : ℕ)) ω) := by
      refine Finset.measurable_sum (Finset.range N) ?_
      intro t ht
      exact Measurable.indicator measurable_const (hS t)
    have hcongr : (fun ω : ΩN N Ω =>
        ((Finset.range (R vbl A pick hpick ω)).filter
          (fun t => canon (T vbl A pick hpick ω t) = σ)).card) =
        (fun ω : ΩN N Ω => ∑ t ∈ Finset.range N,
          (S t).indicator (fun _ => (1 : ℕ)) ω) := by
      funext ω
      calc
        ((Finset.range (R vbl A pick hpick ω)).filter
            (fun t => canon (T vbl A pick hpick ω t) = σ)).card
            = ∑ t ∈ Finset.range (R vbl A pick hpick ω),
                (if canon (T vbl A pick hpick ω t) = σ then (1 : ℕ) else 0) := by
              rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = ∑ t ∈ Finset.range (R vbl A pick hpick ω),
                (if t < R vbl A pick hpick ω then
                  (if canon (T vbl A pick hpick ω t) = σ then (1 : ℕ) else 0) else 0) := by
              apply Finset.sum_congr rfl
              intro t ht
              rw [if_pos (Finset.mem_range.mp ht)]
        _ = ∑ t ∈ Finset.range N,
                (if t < R vbl A pick hpick ω then
                  (if canon (T vbl A pick hpick ω t) = σ then (1 : ℕ) else 0) else 0) := by
              rw [Finset.sum_subset
                (show Finset.range (R vbl A pick hpick ω) ⊆ Finset.range N from by
                intro t ht
                rw [Finset.mem_range] at ht ⊢
                exact Nat.lt_of_lt_of_le ht (R_le vbl A pick hpick ω))]
              intro t htN htR
              rw [if_neg (mt (Finset.mem_range.mpr) htR)]
        _ = ∑ t ∈ Finset.range N, (S t).indicator (fun _ => (1 : ℕ)) ω := by
              apply Finset.sum_congr rfl
              intro t ht
              unfold Set.indicator
              by_cases hR : t < R vbl A pick hpick ω
              · rw [if_pos hR]
                by_cases hcan : canon (T vbl A pick hpick ω t) = σ
                · rw [if_pos hcan, if_pos ?_]
                  change t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ
                  exact ⟨hR, hcan⟩
                · rw [if_neg hcan, if_neg ?_]
                  intro hmem
                  change t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ at hmem
                  exact hcan hmem.2
              · rw [if_neg hR, if_neg ?_]
                intro hmem
                change t < R vbl A pick hpick ω ∧ canon (T vbl A pick hpick ω t) = σ at hmem
                exact hR hmem.1
    rw [hcongr]
    exact hfiber
  have hcast : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := by
    intro s hs
    change True
    trivial
  exact (hcast.comp hcard).aemeasurable

end MeasurableOccurrence

/-! ## The main theorem: the Moser–Tardos bound (60.2)

Statement set per the 2026-08-17 Survey (blueprint 60.2 log row + prep), with the
three load-bearing corrections the Setup pinned:

(A) the 40.3-side re-shaping: `treeProfile_canon` / `check_canon` / `isGood_canon` /
`coupling_canon` / uniform wrapper `occurrence_canon_le_treeProd`;
(B) `canon_T_injective` (replaces the FALSE `T_size_eq`, correction (1)) + private
`fiber_card_le_one`;
(C) private ℝ/ENNReal bridges: `x'_nonneg` / `gwWeight_mul_x_eq` (correction (2)) /
`x'Prod_eq_div_mul_gwWeight` / `treeProd_le_ofReal_x'Prod`;
(D) measurability: imported (20.5 landed after the Survey ran) — no private slice;
(E) headline `moserTardos_bound` (exact pinned lintegral form; 60.3–60.5 consume it
unchanged).

The Survey corrections: (1) `T_size_eq` is FALSE (counterexample in the blueprint
prep — a table violating `b` at times 0,1 and `a` at time 2 gives `size (T ω 2) = 1`);
(2) 50.1's division-form `gwWeight_telescope` is unusable here (`hx₀` allows
`x j = 0`); (3) `coupling_canon`'s `hN` is not available for
`σ ∈ gwFinsetHeight vbl i (N-1)`, hence the uniform wrapper. Consequences: the
informal's `by_cases x i = 0` is subsumed by the uniform chain; `hLLL` enters only
via `treeProd_le_ofReal_x'Prod`'s per-node step (definitional after `unfold x'`,
via private `x'_nonneg`).

Transcription choices: the four private re-derivations of Basic.lean's own
file-scoped privates (`eq_of_labelOf_eq_of_nodup`, `canonChild_spec`,
`nodup_map_of_labelOf_inj`, `canonChildren_perm` — same statements) are dropped:
in-file privates are visible to later sections of the same file, so this section
uses the originals directly; `length_filter_range_lt` (private in WitnessTree.lean)
is re-derived here as a private; the check/isGood path-correspondence privates were
deliberately NOT stubbed — the Proof agent designed the lift machinery
(`canonLiftCert`, label- and length-preserving through the child permutation).

-/

section MainTheorem

variable {ι : Type u} [instDecidableEqι : DecidableEq ι] [instInhabitedι : Inhabited ι]
  [Fintype ι]
variable {κ : Type u} [DecidableEq κ] [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hA : ∀ i, MeasurableSet (A i))
variable (hdet : ∀ i, DeterminedBy (A i) (vbl i))
variable (x : ι → ℝ)
variable (hx₀ : ∀ i, 0 ≤ x i)
variable (hx₁ : ∀ i, x i < 1)
variable (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
  (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)
variable {N : ℕ}

/-! ## Path correspondence between `τ` and `canon τ` (40.3-side reshaping machinery) -/

/-- The label-sorted re-selection of the children — the order `canon` assembles its
children in. -/
private def canonChildrenList (cs : List (WitnessTree ι)) : List (WitnessTree ι) :=
  ((cs.map labelOf).toFinset).attach.toList.map
    (fun x => (cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 []))

omit [Inhabited ι] [Fintype ι] in
/-- The canonical children of a node are the `canon`-image of the re-selected children
(the one-map form `canon` uses vs the two-map shorthand). -/
private lemma canonChildren_eq_map_canon {cs : List (WitnessTree ι)} :
    (((cs.map labelOf).toFinset).attach.toList.map
      (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])))) =
    (canonChildrenList cs).map canon := by
  rw [canonChildrenList]
  rw [List.map_map]
  rfl

omit [Inhabited ι] [Fintype ι] in
/-- Decompose a canonical-child membership: from `c'` in the canonical children of `cs`,
the original child `c` selected for `c'`'s label satisfies `c ∈ cs` and `c' = canon c`. -/
private lemma canonChild_pack {cs : List (WitnessTree ι)} {c' : WitnessTree ι}
    (hc' : c' ∈ (canonChildrenList cs).map canon) :
    ∃ c : WitnessTree ι, c ∈ cs ∧ c' = canon c := by
  rw [← canonChildren_eq_map_canon] at hc'
  rw [List.mem_map] at hc'
  rcases hc' with ⟨x, hx, rfl⟩
  refine ⟨(cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 []),
    (canonChild_spec x.2).1, ?_⟩
  rfl

omit [Inhabited ι] [Fintype ι] in
/-- The canonical children of any node are label-Nodup, hence Nodup. -/
private lemma canonChildren_nodup {cs : List (WitnessTree ι)} :
    ((canonChildrenList cs).map canon).Nodup := by
  have hlabels : (((canonChildrenList cs).map canon).map labelOf).Nodup := by
    rw [List.map_map]
    have hcongr : (canonChildrenList cs).map (fun c => labelOf (canon c)) =
        (canonChildrenList cs).map (fun c => labelOf c) := by
      refine List.map_congr_left ?_
      intro c hc
      rw [labelOf_canon]
    change ((canonChildrenList cs).map (fun c => labelOf (canon c))).Nodup
    rw [hcongr]
    have hbase : (canonChildrenList cs).map labelOf =
        ((cs.map labelOf).toFinset).attach.toList.map (fun x => x.1) := by
      unfold canonChildrenList
      rw [List.map_map]
      refine List.map_congr_left ?_
      intro x hx
      exact (canonChild_spec x.2).2
    rw [hbase]
    exact List.Nodup.map Subtype.coe_injective
      (Finset.nodup_toList ((cs.map labelOf).toFinset).attach)
  exact List.Nodup.of_map labelOf hlabels

/-- The path-certificate lift: a valid path in `canon τ` lifts to a valid path in `τ` —
the reindexed preimage (each canonical child index is reindexed to the position of the
selected original child; the child's path is lifted recursively). Data-valued with the
certificate so the preservation lemmas unfold it (30.1/30.7's pattern: match the PATH
first; the child witness is `Classical.choose`, inlined — a wrapper breaks defeq at the
instances transparency; the recursive call receives the explicit `cast (congrArg …)`,
cf. `validPath_of_forgetTime`). -/
noncomputable def canonLiftCert {τ : WitnessTree ι} (hprop : Proper τ) {p : List ℕ}
    (hp : ValidPath (canon τ) p) : Σ q : List ℕ, ValidPath τ q :=
  match p with
  | [] => ⟨[], .root⟩
  | i' :: p' =>
      match hp with
      | .cons _ c' hc' hvp =>
          match τ with
          | mk a cs =>
              let hproper : ∀ c ∈ cs, Proper c := ((WitnessTree.proper_mk a cs).mp hprop).2
              let hmem : c' ∈ (canonChildrenList cs).map canon := by
                rw [← canonChildren_eq_map_canon]
                simpa only [canon.eq_1, WitnessTree.childrenOf_mk] using
                  (List.mem_of_getElem? hc')
              let c := Classical.choose (canonChild_pack hmem)
              let hspec := Classical.choose_spec (canonChild_pack hmem)
              let r := canonLiftCert (hproper c hspec.1)
                (cast (congrArg (fun x => ValidPath x p') hspec.2) hvp)
              ⟨List.idxOf c cs :: r.1, .cons (List.idxOf c cs) c
                (List.getElem?_idxOf hspec.1) r.2⟩

/-- The lifted path is valid in `τ`. -/
private def validPath_canonLift {τ : WitnessTree ι} (hprop : Proper τ) {p : List ℕ}
    (hp : ValidPath (canon τ) p) : ValidPath τ (canonLiftCert hprop hp).1 :=
  (canonLiftCert hprop hp).2

omit [Inhabited ι] [Fintype ι] in
/-- The lift preserves path length. -/
private lemma length_canonLift {τ : WitnessTree ι} (hprop : Proper τ) {p : List ℕ}
    (hp : ValidPath (canon τ) p) : (canonLiftCert hprop hp).1.length = p.length := by
  induction p generalizing τ with
  | nil => simp [canonLiftCert]
  | cons i' p' ih =>
      cases hp with
      | cons _ c' hc' hvp =>
          cases τ with
          | mk a cs =>
              let hproper : ∀ c ∈ cs, Proper c := ((WitnessTree.proper_mk a cs).mp hprop).2
              let hmem : c' ∈ (canonChildrenList cs).map canon := by
                rw [← canonChildren_eq_map_canon]
                simpa only [canon.eq_1, WitnessTree.childrenOf_mk] using
                  (List.mem_of_getElem? hc')
              let c := Classical.choose (canonChild_pack hmem)
              let hspec := Classical.choose_spec (canonChild_pack hmem)
              simp only [canonLiftCert]
              rw [List.length_cons, List.length_cons]
              exact congrArg (fun n : ℕ => n + 1) (ih (hproper c hspec.1)
                (cast (congrArg (fun x => ValidPath x p') hspec.2) hvp))

omit [Inhabited ι] [Fintype ι] in
/-- The lift preserves vertex labels. -/
private lemma labelAt_canonLift {τ : WitnessTree ι} (hprop : Proper τ) {p : List ℕ}
    (hp : ValidPath (canon τ) p) :
    labelAt (canonLiftCert hprop hp).2 = labelAt hp := by
  induction p generalizing τ with
  | nil =>
      cases hp with
      | root => simp [canonLiftCert, labelOf_canon]
  | cons i' p' ih =>
      cases hp with
      | cons _ c' hc' hvp =>
          cases τ with
          | mk a cs =>
              let hproper : ∀ c ∈ cs, Proper c := ((WitnessTree.proper_mk a cs).mp hprop).2
              let hmem : c' ∈ (canonChildrenList cs).map canon := by
                rw [← canonChildren_eq_map_canon]
                simpa only [canon.eq_1, WitnessTree.childrenOf_mk] using
                  (List.mem_of_getElem? hc')
              let c := Classical.choose (canonChild_pack hmem)
              let hspec := Classical.choose_spec (canonChild_pack hmem)
              simp only [canonLiftCert]
              change labelAt ((canonLiftCert (hproper c hspec.1)
                (cast (congrArg (fun x => ValidPath x p') hspec.2) hvp)).snd) = labelAt hvp
              rw [ih (hproper c hspec.1)
                (cast (congrArg (fun x => ValidPath x p') hspec.2) hvp)]
              exact labelAt_cast hspec.2 hvp

omit [Inhabited ι] [Fintype ι] in
/-- The lift commutes with casts along tree equalities (the glue for the injectivity
transport). -/
private lemma canonLift_cert_cast {τ τ' : WitnessTree ι} (h : τ = τ') (hprop : Proper τ)
    (hprop' : Proper τ') {p : List ℕ} (hp : ValidPath (canon τ) p) :
    (canonLiftCert hprop'
      (cast (congrArg (fun x => ValidPath x p) (congrArg canon h)) hp)).1 =
      (canonLiftCert hprop hp).1 := by
  subst h
  rfl

omit [Inhabited ι] [Fintype ι] in
/-- The lift is injective on paths: two canonical paths lifting to the same path agree
(the per-node reindex is injective by `idxOf_inj` — the canonical children are
label-Nodup — plus the recursive injectivity). -/
private lemma canonLift_injective {τ : WitnessTree ι} (hprop : Proper τ)
    {p q : List ℕ} (hp : ValidPath (canon τ) p) (hq : ValidPath (canon τ) q)
    (h : (canonLiftCert hprop hp).1 = (canonLiftCert hprop hq).1) : p = q := by
  induction p generalizing τ q with
  | nil =>
      cases q with
      | nil => rfl
      | cons j q' =>
          cases hq with
          | cons _ d' hd' hvq =>
              cases τ with
              | mk a cs =>
                  simp only [canonLiftCert] at h
                  cases h
  | cons i' p' ih =>
      cases q with
      | nil =>
          cases hp with
          | cons _ c' hc' hvp =>
              cases τ with
              | mk a cs =>
                  simp only [canonLiftCert] at h
                  cases h
      | cons j' q' =>
          cases hp with
          | cons _ c' hc' hvp =>
              cases hq with
              | cons _ d' hd' hvq =>
                  cases τ with
                  | mk a cs =>
                      let hproper : ∀ c ∈ cs, Proper c :=
                        ((WitnessTree.proper_mk a cs).mp hprop).2
                      let hmem₁ : c' ∈ (canonChildrenList cs).map canon := by
                        rw [← canonChildren_eq_map_canon]
                        simpa only [canon.eq_1, WitnessTree.childrenOf_mk] using
                          (List.mem_of_getElem? hc')
                      let hmem₂ : d' ∈ (canonChildrenList cs).map canon := by
                        rw [← canonChildren_eq_map_canon]
                        simpa only [canon.eq_1, WitnessTree.childrenOf_mk] using
                          (List.mem_of_getElem? hd')
                      let c₁ := Classical.choose (canonChild_pack hmem₁)
                      let c₂ := Classical.choose (canonChild_pack hmem₂)
                      let hspec₁ := Classical.choose_spec (canonChild_pack hmem₁)
                      let hspec₂ := Classical.choose_spec (canonChild_pack hmem₂)
                      simp only [canonLiftCert] at h
                      have hIdx : List.idxOf c₁ cs = List.idxOf c₂ cs := (List.cons.inj h).1
                      have hc12 : c₁ = c₂ := (List.idxOf_inj hspec₁.1).mp hIdx
                      have hcd : c' = d' :=
                        hspec₁.2.trans ((congrArg canon hc12).trans hspec₂.2.symm)
                      have hij' : i' = j' := by
                        have hnodup :
                            ((((cs.map labelOf).toFinset).attach.toList.map
                              (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                                (WitnessTree.mk x.1 []))))).Nodup := by
                          rw [canonChildren_eq_map_canon]
                          exact canonChildren_nodup (cs := cs)
                        have hget₁ := List.getElem?_eq_some_iff.mp hc'
                        have hget₂ := List.getElem?_eq_some_iff.mp hd'
                        have hb₁ : i' < (((cs.map labelOf).toFinset).attach.toList.map
                            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                              (WitnessTree.mk x.1 [])))).length := by
                          simpa only [canon.eq_1, WitnessTree.childrenOf_mk] using hget₁.1
                        have hb₂ : j' < (((cs.map labelOf).toFinset).attach.toList.map
                            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                              (WitnessTree.mk x.1 [])))).length := by
                          simpa only [canon.eq_1, WitnessTree.childrenOf_mk] using hget₂.1
                        have hg₁ : (((cs.map labelOf).toFinset).attach.toList.map
                            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                              (WitnessTree.mk x.1 []))))[i'] = c' := by
                          rw [canon.eq_1, WitnessTree.childrenOf_mk] at hget₁
                          exact hget₁.2
                        have hg₂ : (((cs.map labelOf).toFinset).attach.toList.map
                            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                              (WitnessTree.mk x.1 []))))[j'] = d' := by
                          rw [canon.eq_1, WitnessTree.childrenOf_mk] at hget₂
                          exact hget₂.2
                        have hccs : ((((cs.map labelOf).toFinset).attach.toList.map
                            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                              (WitnessTree.mk x.1 [])))))[i']'hb₁ =
                            ((((cs.map labelOf).toFinset).attach.toList.map
                            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                              (WitnessTree.mk x.1 [])))))[j']'hb₂ := by
                          simpa only [hg₁, hg₂] using hcd
                        exact (List.Nodup.getElem_inj_iff hnodup
                          (i := i') (hi := hb₁) (j := j') (hj := hb₂)).mp hccs
                      have hrec : (canonLiftCert (hproper c₁ hspec₁.1)
                          (cast (congrArg (fun x => ValidPath x p') hspec₁.2) hvp)).1 =
                          (canonLiftCert (hproper c₂ hspec₂.1)
                            (cast (congrArg (fun x => ValidPath x q') hspec₂.2) hvq)).1 :=
                        (List.cons.inj h).2
                      have hrec' : (canonLiftCert (hproper c₁ hspec₁.1)
                          (cast (congrArg (fun x => ValidPath x p') hspec₁.2) hvp)).1 =
                          (canonLiftCert (hproper c₁ hspec₁.1)
                            (cast (congrArg (fun x => ValidPath x q') (congrArg canon hc12.symm))
                              (cast (congrArg (fun x => ValidPath x q') hspec₂.2) hvq))).1 := by
                        have hc := canonLift_cert_cast hc12.symm (hproper c₂ hspec₂.1)
                          (hproper c₁ hspec₁.1)
                          (cast (congrArg (fun x => ValidPath x q') hspec₂.2) hvq)
                        calc
                          (canonLiftCert (hproper c₁ hspec₁.1)
                            (cast (congrArg (fun x => ValidPath x p') hspec₁.2) hvp)).1 =
                              (canonLiftCert (hproper c₂ hspec₂.1)
                                (cast (congrArg (fun x => ValidPath x q') hspec₂.2)
                                  hvq)).1 := hrec
                          _ = (canonLiftCert (hproper c₁ hspec₁.1)
                            (cast (congrArg (fun x => ValidPath x q') (congrArg canon hc12.symm))
                              (cast (congrArg (fun x => ValidPath x q') hspec₂.2)
                                hvq))).1 := hc.symm
                      have hpq' : p' = q' := ih (hproper c₁ hspec₁.1)
                        (cast (congrArg (fun x => ValidPath x p') hspec₁.2) hvp)
                        (cast (congrArg (fun x => ValidPath x q') (congrArg canon hc12.symm))
                          (cast (congrArg (fun x => ValidPath x q') hspec₂.2) hvq))
                        hrec'
                      rw [hij', hpq']

omit [Fintype κ] [Inhabited ι] [Fintype ι] in
/-- The tree profile is invariant under the canonical form on proper trees
(WitnessTree.rec + `canonChildren_perm` + `List.Perm.sum_eq`). -/
lemma treeProfile_canon {τ : WitnessTree ι} (hprop : Proper τ) (j : κ) (d : ℕ) :
    treeProfile vbl (canon τ) j d = treeProfile vbl τ j d := by
  refine WitnessTree.rec
      (motive_1 := fun τ => Proper τ → ∀ j d,
        treeProfile vbl (canon τ) j d = treeProfile vbl τ j d)
      (motive_2 := fun cs => ∀ c ∈ cs, Proper c → ∀ j d,
        treeProfile vbl (canon c) j d = treeProfile vbl c j d)
      ?_ ?_ ?_ τ hprop j d
  · intro a cs ih hprop j d
    have hnodup : (cs.map labelOf).Nodup := ((WitnessTree.proper_mk a cs).mp hprop).1
    have hproper : ∀ c ∈ cs, Proper c := ((WitnessTree.proper_mk a cs).mp hprop).2
    have hperm := canonChildren_perm hnodup
    cases d with
    | zero =>
        have hsum :
            ((((cs.map labelOf).toFinset).attach.toList.map
              (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                (WitnessTree.mk x.1 [])))).map (fun c => treeProfile vbl c j 0)).sum =
              (cs.map (fun c => treeProfile vbl c j 0)).sum := by
          have hmap :
              ((((cs.map labelOf).toFinset).attach.toList.map
                (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                  (WitnessTree.mk x.1 [])))).map (fun c => treeProfile vbl c j 0)) =
              ((((cs.map labelOf).toFinset).attach.toList.map
                (fun x => (cs.find? (fun c => labelOf c = x.1)).getD
                  (WitnessTree.mk x.1 []))).map (fun c => treeProfile vbl c j 0)) := by
            rw [List.map_map, List.map_map]
            refine List.map_congr_left ?_
            intro x hx
            have hs := canonChild_spec x.2
            exact ih ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1
              (hproper ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1)
              j 0
          rw [hmap]
          exact List.Perm.sum_eq (List.Perm.map (fun c => treeProfile vbl c j 0) hperm)
        rw [canon.eq_1]
        simp only [treeProfile]
        rw [hsum]
    | succ d =>
        have hsum :
            ((((cs.map labelOf).toFinset).attach.toList.map
              (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                (WitnessTree.mk x.1 [])))).map (fun c => treeProfile vbl c j d)).sum =
              (cs.map (fun c => treeProfile vbl c j d)).sum := by
          have hmap :
              ((((cs.map labelOf).toFinset).attach.toList.map
                (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
                  (WitnessTree.mk x.1 [])))).map (fun c => treeProfile vbl c j d)) =
              ((((cs.map labelOf).toFinset).attach.toList.map
                (fun x => (cs.find? (fun c => labelOf c = x.1)).getD
                  (WitnessTree.mk x.1 []))).map (fun c => treeProfile vbl c j d)) := by
            rw [List.map_map, List.map_map]
            refine List.map_congr_left ?_
            intro x hx
            have hs := canonChild_spec x.2
            exact ih ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1
              (hproper ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1)
              j d
          rw [hmap]
          exact List.Perm.sum_eq (List.Perm.map (fun c => treeProfile vbl c j d) hperm)
        rw [canon.eq_1]
        simp only [treeProfile]
        rw [hsum]
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

omit [Inhabited ι] [Fintype ι] in
/-- For a nodup-label child `c`, its canonical image is among the canonical children. -/
private lemma mem_ccs_of_mem {cs : List (WitnessTree ι)} (hnodup : (cs.map labelOf).Nodup)
    {c : WitnessTree ι} (hc : c ∈ cs) :
    canon c ∈ (canonChildrenList cs).map canon := by
  rw [List.mem_map]
  refine ⟨(cs.find? (fun c' => labelOf c' = labelOf c)).getD (WitnessTree.mk (labelOf c) []),
    ?_, ?_⟩
  · change (cs.find? (fun c' => labelOf c' = labelOf c)).getD
        (WitnessTree.mk (labelOf c) []) ∈
      ((cs.map labelOf).toFinset).attach.toList.map
        (fun x => (cs.find? (fun c' => labelOf c' = x.1)).getD (WitnessTree.mk x.1 []))
    rw [List.mem_map]
    refine ⟨(⟨labelOf c, (List.mem_toFinset.mpr (List.mem_map_of_mem hc) :
        labelOf c ∈ (cs.map labelOf).toFinset)⟩ :
        {y // y ∈ (cs.map labelOf).toFinset}), ?_, ?_⟩
    · exact Finset.mem_toList.mpr (Finset.mem_attach ((cs.map labelOf).toFinset)
        ⟨labelOf c, List.mem_toFinset.mpr (List.mem_map_of_mem hc)⟩)
    · rfl
  · have hsel : (cs.find? (fun c' => labelOf c' = labelOf c)).getD
      (WitnessTree.mk (labelOf c) []) = c := by
      have hs := canonChild_spec (B := labelOf c) (List.mem_toFinset.mpr (List.mem_map_of_mem hc))
      exact eq_of_labelOf_eq_of_nodup hnodup
        ((cs.find? (fun c' => labelOf c' = labelOf c)).getD
          (WitnessTree.mk (labelOf c) [])) hs.1
        c hc hs.2
    simp [hsel]

omit [∀ (j : κ), MeasurableSpace (Ω j)] [Fintype κ] [Inhabited ι] [Fintype ι] in
/-- The `checkAux` of the canonical form matches that of the original, node by node
(the whole-tree profile is invariant by `treeProfile_canon`; the child set is the
permutation correspondence). -/
private lemma checkAux_canon {τ : WitnessTree ι} (hprop : Proper τ) (hN : size τ ≤ N)
    (hNc : size (canon τ) ≤ N) (d : ℕ) (ω : ΩN N Ω) :
    checkAux vbl A hdet (canon τ) hNc (canon τ) d ω ↔ checkAux vbl A hdet τ hN τ d ω := by
  refine WitnessTree.rec
      (motive_1 := fun τ' => Proper τ' → ∀ d,
        checkAux vbl A hdet (canon τ) hNc (canon τ') d ω ↔
          checkAux vbl A hdet τ hN τ' d ω)
      (motive_2 := fun cs => ∀ c ∈ cs, Proper c → ∀ d,
        checkAux vbl A hdet (canon τ) hNc (canon c) d ω ↔
          checkAux vbl A hdet τ hN c d ω)
      ?_ ?_ ?_ τ hprop d
  · intro a cs ih hpropnode d
    have hnodup : (cs.map labelOf).Nodup := ((WitnessTree.proper_mk a cs).mp hpropnode).1
    have hproper : ∀ c ∈ cs, Proper c := ((WitnessTree.proper_mk a cs).mp hpropnode).2
    rw [canon.eq_1]
    simp only [checkAux]
    constructor
    · rintro ⟨hcond, hchildren⟩
      constructor
      · exact Eq.mp (congrArg (fun f => Classical.choose (hdet a) f) (by
          funext j
          congr 1
          apply Sigma.ext
          · rfl
          · exact heq_of_eq (Fin.ext (treeProfile_canon vbl hprop j (d + 1))))) hcond
      · intro c hc
        have hmem : canon c ∈ (canonChildrenList cs).map canon := mem_ccs_of_mem hnodup hc
        have hmem' : canon c ∈ (((cs.map labelOf).toFinset).attach.toList.map
            (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
              (WitnessTree.mk x.1 [])))) := by
          simpa [← canonChildren_eq_map_canon] using hmem
        have hcc := hchildren (canon c) hmem'
        exact (ih c hc (hproper c hc) (d + 1)).mp hcc
    · rintro ⟨hcond, hchildren⟩
      constructor
      · exact Eq.mpr (congrArg (fun f => Classical.choose (hdet a) f) (by
          funext j
          congr 1
          apply Sigma.ext
          · rfl
          · exact heq_of_eq (Fin.ext (treeProfile_canon vbl hprop j (d + 1))))) hcond
      · intro c' hc'
        have hc'' : c' ∈ (canonChildrenList cs).map canon := by
          simpa [canonChildren_eq_map_canon] using hc'
        rcases canonChild_pack hc'' with ⟨c, hc, hcc'⟩
        have hcch := hchildren c hc
        have hih := (ih c hc (hproper c hc) (d + 1)).mpr hcch
        simpa [hcc'] using hih
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

omit [(j : κ) → MeasurableSpace (Ω j)] [Fintype κ] [Inhabited ι] [Fintype ι] in
/-- The τ-check is invariant under the canonical form: `check` on `canon τ` (at the
canon size certificate) iff `check` on `τ` (at the original size certificate).
Proof shape: unfold both sides via `checkSet_eq_vertices`; private label- and
length-preserving path-correspondence lemmas between `ValidPath (canon τ)` and
`ValidPath τ` (through the child permutation — same-path validity is FALSE in
general) + `treeProfile_canon`. -/
lemma check_canon {τ : WitnessTree ι} (hprop : Proper τ) (hN : size τ ≤ N)
    (hNc : size (canon τ) ≤ N) (ω : ΩN N Ω) :
    check vbl A hdet hNc ω ↔ check vbl A hdet hN ω := by
  unfold check
  exact checkAux_canon vbl A hdet hprop hN hNc 0 ω

omit [Inhabited ι] [Fintype ι] in
/-- Canon preserves properness (`Proper` is the label-Nodup condition, and the
canonical children reorder — possibly dropping duplicate-label children — while
keeping the label-Nodup). -/
private lemma proper_canon {τ : WitnessTree ι} (hprop : Proper τ) : Proper (canon τ) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => Proper τ → Proper (canon τ))
      (motive_2 := fun cs => ∀ c ∈ cs, Proper c → Proper (canon c))
      ?_ ?_ ?_ τ hprop
  · intro a cs ih hprop
    rw [canon.eq_1]
    rw [WitnessTree.proper_mk]
    constructor
    · have hlabels :
        ((((cs.map labelOf).toFinset).attach.toList.map
          (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
            (WitnessTree.mk x.1 [])))).map labelOf).Nodup := by
        have hlabels' : (((canonChildrenList cs).map canon).map labelOf).Nodup := by
          rw [List.map_map]
          have hcongr : (canonChildrenList cs).map (fun c => labelOf (canon c)) =
              (canonChildrenList cs).map (fun c => labelOf c) := by
            refine List.map_congr_left ?_
            intro c hc
            rw [labelOf_canon]
          change ((canonChildrenList cs).map (fun c => labelOf (canon c))).Nodup
          rw [hcongr]
          have hbase : (canonChildrenList cs).map labelOf =
              ((cs.map labelOf).toFinset).attach.toList.map (fun x => x.1) := by
            rw [canonChildrenList]
            rw [List.map_map]
            refine List.map_congr_left ?_
            intro x hx
            exact (canonChild_spec x.2).2
          rw [hbase]
          exact List.Nodup.map Subtype.coe_injective
            (Finset.nodup_toList ((cs.map labelOf).toFinset).attach)
        simpa only [canonChildren_eq_map_canon] using hlabels'
      exact hlabels
    · intro c' hc'
      have hc'' : c' ∈ (canonChildrenList cs).map canon := by
        simpa [canonChildren_eq_map_canon] using hc'
      rcases canonChild_pack hc'' with ⟨c, hc, hcc'⟩
      have hpc : Proper c := ((WitnessTree.proper_mk a cs).mp hprop).2 c hc
      have hih := ih c hc hpc
      rwa [hcc']
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

omit [DecidableEq κ] [Fintype κ] [Inhabited ι] [Fintype ι] in
/-- `IsGood` is invariant under the canonical form (the HEAVY piece: private
`proper_canon` for the properness conjunct + the same path correspondence as
`check_canon` with injectivity for the `p ≠ q` transport — for two valid paths in
`canon τ`, lift them to distinct valid paths in `τ` with the same labels and depths,
and apply `IsGood vbl τ`). -/
lemma isGood_canon {τ : WitnessTree ι} (hgood : IsGood vbl τ) : IsGood vbl (canon τ) := by
  refine ⟨proper_canon hgood.1, ?_⟩
  intro p q hp hq hne hd
  have hdisj : Disjoint (vbl (labelAt (canonLiftCert hgood.1 hp).2))
      (vbl (labelAt (canonLiftCert hgood.1 hq).2)) := by
    refine hgood.2 (canonLiftCert hgood.1 hp).1 (canonLiftCert hgood.1 hq).1
      (canonLiftCert hgood.1 hp).2 (canonLiftCert hgood.1 hq).2 ?_ ?_
    · intro hpq
      have hpq' : p = q := canonLift_injective hgood.1 hp hq hpq
      exact hne hpq'
    · simpa [WitnessTree.depth, length_canonLift hgood.1 hp, length_canonLift hgood.1 hq] using hd
  rwa [← labelAt_canonLift hgood.1 hp, ← labelAt_canonLift hgood.1 hq]

omit [DecidableEq ι] [Inhabited ι] [Fintype ι] in
/-- The multiset of a `flatMap` of labels equals the sum of the per-child label
multisets. -/
private lemma coe_flatMap_labels {f : WitnessTree ι → List ι} {l : List (WitnessTree ι)} :
    (↑(l.flatMap f) : Multiset ι) = (l.map (fun c => (↑(f c) : Multiset ι))).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      unfold List.flatMap
      unfold List.flatMap at ih
      simp only [List.flatten_cons, List.map_cons, List.sum_cons]
      rw [← Multiset.coe_add, ih]

omit [Inhabited ι] [Fintype ι] in
/-- The label multiset of the canonical form equals that of the original on proper
trees (through `canonChildren_perm` — a Perm of the children preserves the
flatMap-labels multiset; `Proper` supplies the Nodup input). -/
private lemma labels_canon {τ : WitnessTree ι} (hprop : Proper τ) :
    (labels (canon τ) : Multiset ι) = labels τ := by
  refine WitnessTree.rec
      (motive_1 := fun τ => Proper τ → (labels (canon τ) : Multiset ι) = labels τ)
      (motive_2 := fun cs => ∀ c ∈ cs, Proper c → (labels (canon c) : Multiset ι) = labels c)
      ?_ ?_ ?_ τ hprop
  · intro a cs ih hprop
    have hnodup : (cs.map labelOf).Nodup := ((WitnessTree.proper_mk a cs).mp hprop).1
    have hproper : ∀ c ∈ cs, Proper c := ((WitnessTree.proper_mk a cs).mp hprop).2
    have hperm := canonChildren_perm hnodup
    rw [canon.eq_1]
    simp only [WitnessTree.labels]
    have hflat :
        ((↑((((cs.map labelOf).toFinset).attach.toList.map
          (fun x => canon ((cs.find? (fun c => labelOf c = x.1)).getD
            (WitnessTree.mk x.1 [])))).flatMap labels) : Multiset ι) =
          (↑(cs.flatMap labels) : Multiset ι)) := by
      rw [canonChildren_eq_map_canon]
      rw [List.flatMap_map]
      rw [coe_flatMap_labels (f := fun a => labels (canon a)),
        coe_flatMap_labels (f := labels)]
      have hcongr : (canonChildrenList cs).map (fun c => (↑(labels (canon c)) : Multiset ι)) =
          (canonChildrenList cs).map (fun c => (↑(labels c) : Multiset ι)) := by
        refine List.map_congr_left ?_
        intro c hc
        rw [canonChildrenList] at hc
        rw [List.mem_map] at hc
        rcases hc with ⟨x, hx, rfl⟩
        have hs := canonChild_spec x.2
        exact ih ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1
          (hproper ((cs.find? (fun c => labelOf c = x.1)).getD (WitnessTree.mk x.1 [])) hs.1)
      rw [hcongr]
      exact List.Perm.sum_eq (List.Perm.map (fun c => (↑(labels c) : Multiset ι)) hperm)
    simpa using congrArg (Multiset.cons a) hflat
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-! ## `canon_T_injective` (replaces the FALSE `T_size_eq`) -/

omit [Inhabited ι] [Fintype ι] in
/-- Re-derivation of WitnessTree.lean's private `length_filter_range_succ_lt` (30.6 glue,
file-scoped there). -/
private lemma length_filter_range_succ_lt {Λ : ℕ → Option ι} {s : ℕ}
    {a : ι} (hΛs : Λ s = some a) :
    ((List.range s).filter (fun u => Λ u = some a)).length <
      ((List.range (s + 1)).filter (fun u => Λ u = some a)).length := by
  rw [List.range_succ, List.filter_append, List.length_append]
  have hlen : (List.filter (fun u => Λ u = some a) [s]).length = 1 := by
    rw [List.filter_cons_of_pos]
    · simp
    · simpa using hΛs
  rw [hlen]
  omega

omit [Inhabited ι] [Fintype ι] in
/-- Re-derivation of WitnessTree.lean's private `length_filter_range_mono` (30.6 glue,
file-scoped there). -/
private lemma length_filter_range_mono {Λ : ℕ → Option ι} {n m : ℕ}
    {a : ι} (h : n ≤ m) :
    ((List.range n).filter (fun u => Λ u = some a)).length ≤
      ((List.range m).filter (fun u => Λ u = some a)).length := by
  induction h with
  | refl => rfl
  | step h ih =>
      exact le_trans ih (by
        rw [List.range_succ, List.filter_append, List.length_append]
        omega)

omit [Inhabited ι] [Fintype ι] in
/-- Re-derivation of WitnessTree.lean's private `length_filter_range_lt` (30.6 glue,
file-scoped there): an `a`-occurrence at time `s` strictly grows the filtered
prefix count between `s` and `t` for `s < t`. -/
private lemma length_filter_range_lt {Λ : ℕ → Option ι} {s t : ℕ}
    {a : ι} (hst : s < t) (hΛs : Λ s = some a) :
    ((List.range s).filter (fun u => Λ u = some a)).length <
      ((List.range t).filter (fun u => Λ u = some a)).length :=
  lt_of_lt_of_le (length_filter_range_succ_lt hΛs)
    (length_filter_range_mono (m := t) (Nat.succ_le_of_lt hst))

omit [Fintype κ] [∀ (j : κ), MeasurableSpace (Ω j)] [Fintype ι] in
/-- Canon-equality of two genuine occurring trees forces the times to be equal.
Proof shape (prep (1), NO size arguments): canon-equality + `labelOf_canon` give
`log t₁ = log t₂ = some a` (via `log_eq_some_iff_labelOf_T`); 30.6's
`treeAt_count_label` counts the `a`-occurrences in the label multiset — the
`a`-count of `T … t₂` strictly exceeds that of `T … t₁` (the occurrence at `t₁`,
`length_filter_range_lt`), contradicting the multiset equality from canon-equality
via `labels_canon` (properness from `(T_isGood …).1`). -/
lemma canon_T_injective {ω : ΩN N Ω} {t₁ t₂ : ℕ} (ht₁ : t₁ < R vbl A pick hpick ω)
    (ht₂ : t₂ < R vbl A pick hpick ω)
    (h : canon (T vbl A pick hpick ω t₁) = canon (T vbl A pick hpick ω t₂)) :
    t₁ = t₂ := by
  have key {s t : ℕ} (hst : s < t) (hs : s < R vbl A pick hpick ω)
      (ht : t < R vbl A pick hpick ω)
      (hc : canon (T vbl A pick hpick ω s) = canon (T vbl A pick hpick ω t)) : False := by
    have hnes : log vbl A pick hpick ω s ≠ none :=
      (log_ne_none_iff_lt_R vbl A pick hpick ω).mpr hs
    rcases Option.ne_none_iff_exists.mp hnes with ⟨a, hlogs⟩
    have hroot_s : labelOf (T vbl A pick hpick ω s) = a :=
      (log_eq_some_iff_labelOf_T vbl A pick hpick hs a).mp hlogs.symm
    have hroot_t : labelOf (T vbl A pick hpick ω t) = a := by
      calc
        labelOf (T vbl A pick hpick ω t) = labelOf (canon (T vbl A pick hpick ω t)) :=
            (labelOf_canon (T vbl A pick hpick ω t)).symm
        _ = labelOf (canon (T vbl A pick hpick ω s)) := congrArg labelOf hc.symm
        _ = labelOf (T vbl A pick hpick ω s) := labelOf_canon (T vbl A pick hpick ω s)
        _ = a := hroot_s
    have hlogt : log vbl A pick hpick ω t = some a :=
      (log_eq_some_iff_labelOf_T vbl A pick hpick ht a).mpr hroot_t
    have hprop_s : Proper (T vbl A pick hpick ω s) := (T_isGood vbl A pick hpick).1
    have hprop_t : Proper (T vbl A pick hpick ω t) := (T_isGood vbl A pick hpick).1
    have hle : (labels (T vbl A pick hpick ω s) : Multiset ι) =
        labels (T vbl A pick hpick ω t) := by
      calc
        (labels (T vbl A pick hpick ω s) : Multiset ι) =
            labels (canon (T vbl A pick hpick ω s)) := (labels_canon hprop_s).symm
        _ = labels (canon (T vbl A pick hpick ω t)) :=
            congrArg (fun τ : WitnessTree ι => (labels τ : Multiset ι)) hc
        _ = labels (T vbl A pick hpick ω t) := labels_canon hprop_t
    have hcs : (labels (T vbl A pick hpick ω s) : Multiset ι).count a =
        ((List.range s).filter (fun u => log vbl A pick hpick ω u = some a)).length + 1 := by
      simpa [T] using treeAt_count_label (vbl := vbl) hlogs.symm
    have hct : (labels (T vbl A pick hpick ω t) : Multiset ι).count a =
        ((List.range t).filter (fun u => log vbl A pick hpick ω u = some a)).length + 1 := by
      simpa [T] using treeAt_count_label (vbl := vbl) hlogt
    have hcount : ((List.range s).filter (fun u => log vbl A pick hpick ω u = some a)).length + 1 =
        ((List.range t).filter (fun u => log vbl A pick hpick ω u = some a)).length + 1 := by
      rw [← hcs, ← hct]
      exact congrArg (fun m : Multiset ι => m.count a) hle
    have hltlen := length_filter_range_lt hst hlogs.symm
    omega
  rcases Nat.lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · exact False.elim (key hlt ht₁ ht₂ h)
  · exact heq
  · exact False.elim (key hgt ht₂ ht₁ h.symm)

omit [Fintype κ] [(j : κ) → MeasurableSpace (Ω j)] [Fintype ι] in
/-- The fiber of `t ↦ canon (T ω t)` over a fixed `σ` has cardinal at most one
(`Finset.card_le_one.mpr` + `canon_T_injective`). Feeds the pointwise
`(card F_σ ω : ℝ≥0∞) ≤ E_σ.indicator 1 ω` step of the assembly chain. -/
private lemma fiber_card_le_one {ω : ΩN N Ω} (σ : WitnessTree ι) :
    ((Finset.range (R vbl A pick hpick ω)).filter
      (fun t => canon (T vbl A pick hpick ω t) = σ)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  exact canon_T_injective (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
    (Finset.mem_range.mp ha.1) (Finset.mem_range.mp hb.1) (ha.2.trans hb.2.symm)

/-! ## The canonical coupling and its uniform wrapper -/

include hA hdet in
omit [Fintype ι] in
/-- The canonical coupling (prep (3)): the measure of the canonical occurrence
`∃ t < R, canon (T ω t) = σ` is bounded by `treeProd A σ`, for `σ` fitting the
table. Proof shape: `by_cases IsGood vbl σ` — good: the occurrence ⊆ the
`check`-event of `σ` via `occurrence_implies_check` + `check_canon` +
`check_probability`; non-good: the event is empty via `T_isGood` + `isGood_canon`.
The `hN : size σ ≤ N` hypothesis is exactly what the assembly does NOT have for
`σ ∈ gwFinsetHeight vbl i (N - 1)` — the uniform wrapper `occurrence_canon_le_treeProd`
absorbs it by `by_cases size σ ≤ N`; use the wrapper there and this lemma where `hN` is
available. -/
lemma coupling_canon {σ : WitnessTree ι} (hN : size σ ≤ N) :
    μN N μ {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ} ≤
      treeProd (μ := μ) A σ := by
  by_cases hgood : IsGood vbl σ
  · have hsub : {ω : ΩN N Ω | ∃ t < R vbl A pick hpick ω,
        canon (T vbl A pick hpick ω t) = σ} ⊆
        {ω : ΩN N Ω | check vbl A hdet hN ω} := by
      intro ω hω
      rcases hω with ⟨t, ht, hT⟩
      have hNt : size (T vbl A pick hpick ω t) ≤ N :=
        T_size_le_N (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ht
      have hNc : size (canon (T vbl A pick hpick ω t)) ≤ N := by
        simpa [size_canon ((T_isGood (vbl := vbl) (A := A)
          (pick := pick) (hpick := hpick)).1)] using hNt
      have hck : check vbl A hdet hNc ω :=
        (check_canon (vbl := vbl) (A := A) (hdet := hdet)
          (hprop := (T_isGood (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)).1)
          (hN := hNt) (hNc := hNc) ω).mpr
          (occurrence_implies_check (vbl := vbl) (A := A) (hdet := hdet)
            (pick := pick) (hpick := hpick) ht rfl hNt)
      simpa [hT] using hck
    calc
      μN N μ {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ}
          ≤ μN N μ {ω | check vbl A hdet hN ω} := measure_mono hsub
      _ = treeProd (μ := μ) A σ := check_probability (vbl := vbl) (A := A) (hdet := hdet)
        hA hgood hN
  · have hempty : ({ω : ΩN N Ω | ∃ t < R vbl A pick hpick ω,
        canon (T vbl A pick hpick ω t) = σ}) = ∅ := by
      ext ω
      constructor
      · rintro ⟨t, ht, hT⟩
        have hgood' : IsGood vbl σ := by
          rw [← hT]
          exact isGood_canon (vbl := vbl) (T_isGood (vbl := vbl) (A := A)
            (pick := pick) (hpick := hpick))
        exact (hgood hgood').elim
      · intro h
        exact h.elim
    calc
      μN N μ {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ}
          = μN N μ (∅ : Set (ΩN N Ω)) := by rw [hempty]
      _ = 0 := measure_empty
      _ ≤ treeProd (μ := μ) A σ := by positivity

include hA hdet in
omit [Fintype ι] in
/-- The uniform wrapper (prep (3)): `by_cases size σ ≤ N` inside — `coupling_canon`,
or the empty event (`size σ = size (canon (T t)) = size (T t) ≤ N` via `T_size_le_N`
+ `size_canon` under `(T_isGood …).1`). This is the per-`σ` bound the assembly chain
consumes for `σ ∈ gwFinsetHeight vbl i (N-1)`, where `hN` is NOT available — the
`hN`-carrying twin is `coupling_canon`, used where the caller can produce the size
bound. -/
lemma occurrence_canon_le_treeProd (σ : WitnessTree ι) :
    μN N μ {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ} ≤
      treeProd (μ := μ) A σ := by
  by_cases hN : size σ ≤ N
  · exact coupling_canon (μ := μ) (vbl := vbl) (A := A) (hA := hA) (hdet := hdet)
      (pick := pick) (hpick := hpick) hN
  · have hempty : ({ω : ΩN N Ω | ∃ t < R vbl A pick hpick ω,
        canon (T vbl A pick hpick ω t) = σ}) = ∅ := by
      ext ω
      constructor
      · rintro ⟨t, ht, hT⟩
        have hsize : size (canon (T vbl A pick hpick ω t)) ≤ N := by
          calc
            size (canon (T vbl A pick hpick ω t))
                = size (T vbl A pick hpick ω t) :=
                  size_canon ((T_isGood (vbl := vbl) (A := A) (pick := pick)
                    (hpick := hpick)).1)
            _ ≤ N := T_size_le_N (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ht
        exact (hN (by simpa [hT] using hsize)).elim
      · intro h
        exact h.elim
    calc
      μN N μ {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ}
          = μN N μ (∅ : Set (ΩN N Ω)) := by rw [hempty]
      _ = 0 := measure_empty
      _ ≤ treeProd (μ := μ) A σ := by positivity

/-! ## Private ℝ/ENNReal bridges -/

omit [Inhabited ι] [Fintype κ] in
/-- Prep correction (2): the no-division replacement for 50.1's unusable
`gwWeight_telescope` (its `hx0 : ∀ j ∈ labels τ, j ≠ i → x j ≠ 0` is not derivable
from the pinned block — `hx₀` allows `x j = 0` for `j ≠ i`).
`x i * gwWeight vbl x τ = (1 - x i) * x'Prod vbl x τ` — WitnessTree.rec mirroring
50.1's Steps A–C with the `field_simp` steps replaced by `ring` (a strict
simplification); hypotheses hroot/hprop/hwit only. -/
private lemma gwWeight_mul_x_eq (i : ι) {τ : WitnessTree ι} (hroot : labelOf τ = i)
    (hprop : Proper τ) (hwit : IsWitnessTree vbl τ) :
    x i * gwWeight vbl x τ = (1 - x i) * x'Prod vbl x τ := by
  refine WitnessTree.rec
    (motive_1 := fun τ => ∀ ⦃i⦄, labelOf τ = i → Proper τ →
      IsWitnessTree vbl τ → x i * gwWeight vbl x τ = (1 - x i) * x'Prod vbl x τ)
    (motive_2 := fun cs => ∀ c ∈ cs, ∀ ⦃i⦄, labelOf c = i → Proper c →
      IsWitnessTree vbl c → x i * gwWeight vbl x c = (1 - x i) * x'Prod vbl x c)
    (fun a cs ih => ?mk) (by intro c hc; cases hc) (fun c cs ihc ihcs => ?cons) τ
    hroot hprop hwit
  · intro i hroot hprop hwit
    have hia : i = a := by simpa using hroot.symm
    subst hia
    rcases (proper_mk i cs).mp hprop with ⟨hcnodup, hcprop⟩
    rcases (show (∀ c ∈ cs, labelOf c ∈ gammaPlus vbl i) ∧
        ∀ c ∈ cs, IsWitnessTree vbl c by simpa [IsWitnessTree] using hwit) with
      ⟨hcwit, hcwit'⟩
    have ihc : ∀ c ∈ cs, x (labelOf c) * gwWeight vbl x c =
        (1 - x (labelOf c)) * x'Prod vbl x c :=
      fun c hc => ih c hc rfl (hcprop c hc) (hcwit' c hc)
    let rej : ℝ := ((gammaPlus vbl i).filter (fun j => j ∉ cs.map labelOf)).prod
      (fun j => 1 - x j)
    -- Step A: the child products cancel: `∏_c x[c'] · ∏_c gwWeight c =
    -- ∏_c (1 - x[c']) · ∏_c x'Prod c` (the telescope's hA, no division).
    have hA : (cs.map (fun c => x (labelOf c))).prod *
        (cs.map (gwWeight vbl x)).prod =
        (cs.map (fun c => 1 - x (labelOf c))).prod *
          (cs.map (x'Prod vbl x)).prod := by
      rw [← List.prod_map_mul, ← List.prod_map_mul]
      refine congrArg List.prod (List.map_congr_left ?_)
      intro c hc
      exact ihc c hc
    -- Step B: `∏_c (1 - x[c']) · rej = (1 - x i) · ∏_{j ∈ Γ(i)} (1 - x j)` (as in 50.1).
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
    calc
      x i * gwWeight vbl x (mk i cs)
          = x i * ((cs.map (fun c => x (labelOf c))).prod * rej *
              (cs.map (gwWeight vbl x)).prod) := by rw [gwWeight]
      _ = x i * ((cs.map (fun c => 1 - x (labelOf c))).prod * rej *
              (cs.map (x'Prod vbl x)).prod) := by
        rw [show (cs.map (fun c => x (labelOf c))).prod * rej *
            (cs.map (gwWeight vbl x)).prod =
            (cs.map (fun c => x (labelOf c))).prod *
              (cs.map (gwWeight vbl x)).prod * rej by ring]
        rw [hA]
        ring
      _ = x i * (((1 - x i) * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)) *
              (cs.map (x'Prod vbl x)).prod) := by
        rw [hB]
      _ = (1 - x i) * x'Prod vbl x (mk i cs) := by
        unfold x'Prod x'
        ring
  · intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

include hx₁ in
omit [Inhabited ι] [Fintype κ] in
/-- The divided form, dividing ONLY by `1 - x i ≠ 0` (from `hx₁`) — never by `x i`.
From `gwWeight_mul_x_eq` by `field_simp`/`nlinarith` on the ℝ side. -/
private lemma x'Prod_eq_div_mul_gwWeight (i : ι) {σ : WitnessTree ι} (hroot : labelOf σ = i)
    (hprop : Proper σ) (hwit : IsWitnessTree vbl σ) :
    x'Prod vbl x σ = (x i / (1 - x i)) * gwWeight vbl x σ := by
  have hneq : 1 - x i ≠ 0 := by nlinarith [hx₁ i]
  have h := gwWeight_mul_x_eq (vbl := vbl) (x := x) i hroot hprop hwit
  field_simp [hneq]
  simpa [mul_comm] using h.symm

include hx₀ hx₁ in
omit [Inhabited ι] [Fintype κ] in
/-- The LLL multiplier is nonnegative: `x i ≥ 0` (hx₀) times `∏ (1 - x j)` with
`1 - x j ≥ 0` from `x j ≤ 1` (hx₁). Needed for `ENNReal.ofReal_mul` in the chain. -/
private lemma x'_nonneg (i : ι) : 0 ≤ x' vbl x i := by
  unfold x'
  apply mul_nonneg (hx₀ i)
  refine Finset.prod_nonneg ?_
  intro j hj
  exact sub_nonneg.mpr (le_of_lt (hx₁ j))

omit [Inhabited ι] [Fintype κ] in
/-- The structural `x'`-fold is nonnegative pointwise (WitnessTree.rec + `mul_nonneg` +
`List.prod_nonneg`), given `x'` is nonnegative on every label. -/
private lemma x'Prod_nonneg (hx'0 : ∀ i, 0 ≤ x' vbl x i) (τ : WitnessTree ι) :
    0 ≤ x'Prod vbl x τ := by
  refine WitnessTree.rec (motive_1 := fun τ => 0 ≤ x'Prod vbl x τ)
    (motive_2 := fun cs => ∀ c ∈ cs, 0 ≤ x'Prod vbl x c)
    (fun a cs ih => ?_) (by intro c hc; cases hc) (fun c cs ihc ihcs c' hc' => ?_) τ
  · rw [x'Prod]
    exact mul_nonneg (hx'0 a) (List.prod_nonneg (by
      intro c hc
      rcases List.mem_map.mp hc with ⟨c', hc', rfl⟩
      exact ih c' hc'))
  · rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- `ENNReal.ofReal` commutes with a List product of nonnegative reals. -/
private lemma ofReal_list_prod_eq {α : Type*} (f : α → ℝ) {l : List α}
    (h : ∀ a ∈ l, 0 ≤ f a) :
    (l.map (ENNReal.ofReal ∘ f)).prod = ENNReal.ofReal ((l.map f).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply]
      rw [ENNReal.ofReal_mul (h a (by simp)), ih (fun b hb => h b (by simp [hb]))]

include hLLL in
omit [Inhabited ι] [∀ (j : κ), IsProbabilityMeasure (μ j)] in
/-- The per-`σ` bridge from the structural product to `ofReal (x'Prod σ)`: the
hLLL per-node step `μπ μ (A a) ≤ ENNReal.ofReal (x' vbl x a)` (definitional after
`unfold x'`) composed by `mul_le_mul'` + `ENNReal.ofReal_mul` (needs `x'_nonneg`)
down the tree (WitnessTree.rec + `List.prod_le_prod'`/`List.prod_map`). -/
private lemma treeProd_le_ofReal_x'Prod (hx'0 : ∀ i, 0 ≤ x' vbl x i) (σ : WitnessTree ι) :
    treeProd (μ := μ) A σ ≤ ENNReal.ofReal (x'Prod vbl x σ) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => treeProd (μ := μ) A τ ≤ ENNReal.ofReal (x'Prod vbl x τ))
      (motive_2 := fun cs => ∀ c ∈ cs,
        treeProd (μ := μ) A c ≤ ENNReal.ofReal (x'Prod vbl x c))
      (fun a cs ih => ?_) (by intro c hc; cases hc) (fun c cs ihc ihcs c' hc' => ?_) σ
  · have hroot : μπ μ (A a) ≤ ENNReal.ofReal (x' vbl x a) := by
      simpa [x'] using hLLL a
    have hchild : (cs.map (fun c => treeProd (μ := μ) A c)).prod ≤
        (cs.map (fun c => ENNReal.ofReal (x'Prod vbl x c))).prod := by
      induction cs with
      | nil => simp
      | cons c cs ihcs =>
          simp only [List.map_cons, List.prod_cons]
          exact mul_le_mul (ih c (by simp)) (ihcs (fun c' hc' => ih c' (by simp [hc'])))
            zero_le zero_le
    have hofReal : (cs.map (fun c => ENNReal.ofReal (x'Prod vbl x c))).prod =
        ENNReal.ofReal ((cs.map (x'Prod vbl x)).prod) := by
      refine ofReal_list_prod_eq (f := x'Prod vbl x) ?_
      intro c hc
      exact x'Prod_nonneg (vbl := vbl) (x := x) hx'0 c
    calc
      treeProd (μ := μ) A (mk a cs)
          = μπ μ (A a) * (cs.map (fun c => treeProd (μ := μ) A c)).prod := by rw [treeProd]
      _ ≤ ENNReal.ofReal (x' vbl x a) *
            (cs.map (fun c => ENNReal.ofReal (x'Prod vbl x c))).prod :=
          mul_le_mul hroot hchild zero_le zero_le
      _ = ENNReal.ofReal (x' vbl x a * (cs.map (x'Prod vbl x)).prod) := by
        rw [ENNReal.ofReal_mul (hx'0 a), hofReal]
      _ = ENNReal.ofReal (x'Prod vbl x (mk a cs)) := by rw [x'Prod]
  · rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-! ## The headline -/

/-- **THE MAIN THEOREM** (survey B F23, notes §15–18 Thm 5.1 = arXiv:0903.0544
Thm 1.2): the expected number of resamplings of event `i` in the first `N` steps of
the Moser–Tardos algorithm is at most `x i / (1 - x i)`, under the LLL condition
`μπ μ (A i) ≤ ofReal (x' vbl x i)`. The bound is uniform over the choice rule `pick`
(free by parametricity). All arithmetic on the right is ℝ inside `ENNReal.ofReal` —
no ENNReal division occurs anywhere.

Requires `[Inhabited ι]` (the paper's m ≥ 1 setting): the statement is indexed by an
explicit `i : ι` (uninstantiable at empty `ι`), and the proof route passes through the
witness-tree machinery (`treeAt`'s padded dummy root `WitnessTree.mk (t, default) []`),
which needs a default event label. -/
theorem moserTardos_bound {N : ℕ} (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
    (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1)
    (i : ι) :
    ∫⁻ ω : ΩN N Ω, (countLog (log vbl A pick hpick) ω i : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (x i / (1 - x i)) := by
  classical
  let s : Finset (WitnessTree ι) := gwFinsetHeight vbl i (N - 1)
  let F (σ : WitnessTree ι) (ω : ΩN N Ω) : ℝ≥0∞ :=
    (((Finset.range (R vbl A pick hpick ω)).filter
      (fun t => canon (T vbl A pick hpick ω t) = σ)).card : ℝ≥0∞)
  let E (σ : WitnessTree ι) : Set (ΩN N Ω) :=
    {ω | ∃ t < R vbl A pick hpick ω, canon (T vbl A pick hpick ω t) = σ}
  have hx'0 : ∀ j, 0 ≤ x' vbl x j :=
    x'_nonneg (vbl := vbl) (x := x) (hx₀ := hx₀) (hx₁ := hx₁)
  have hx1 : ∀ j, x j ≤ 1 := fun j => le_of_lt (hx₁ j)
  have hdiv_nonneg : 0 ≤ x i / (1 - x i) :=
    div_nonneg (hx₀ i) (sub_nonneg.mpr (le_of_lt (hx₁ i)))
  have hgw_nonneg (σ : WitnessTree ι) : 0 ≤ gwWeight vbl x σ :=
    gwWeight_nonneg vbl x hx₀ hx1 σ
  calc
    ∫⁻ ω : ΩN N Ω, (countLog (log vbl A pick hpick) ω i : ℝ≥0∞) ∂ μN N μ
        = ∫⁻ ω : ΩN N Ω, (∑ σ ∈ s, F σ ω) ∂ μN N μ := by
          apply lintegral_congr
          intro ω
          rw [countLog_eq_sum_card (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
            (N := N) (ω := ω) (i := i)]
          rw [Nat.cast_sum]
    _ = ∑ σ ∈ s, ∫⁻ ω : ΩN N Ω, F σ ω ∂ μN N μ := by
        rw [lintegral_finsetSum' s (f := F)]
        intro σ hσ
        simpa [F] using aemeasurable_card_fiber (vbl := vbl) (A := A) (hA := hA)
          (pick := pick) (hpick := hpick) (N := N) (μ := μN N μ) σ
    _ ≤ ∑ σ ∈ s, μN N μ (E σ) := by
        apply Finset.sum_le_sum
        intro σ hσ
        calc
          ∫⁻ ω : ΩN N Ω, F σ ω ∂ μN N μ
              ≤ ∫⁻ ω : ΩN N Ω, (E σ).indicator (fun _ => (1 : ℝ≥0∞)) ω
                  ∂ μN N μ := by
                apply lintegral_mono
                intro ω
                by_cases hω : ω ∈ E σ
                · rw [Set.indicator_of_mem hω]
                  change (((Finset.range (R vbl A pick hpick ω)).filter
                      (fun t => canon (T vbl A pick hpick ω t) = σ)).card : ℝ≥0∞) ≤
                    (1 : ℝ≥0∞)
                  have hcard : (((Finset.range (R vbl A pick hpick ω)).filter
                      (fun t => canon (T vbl A pick hpick ω t) = σ)).card : ℕ) ≤ 1 :=
                    fiber_card_le_one (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
                      (N := N) σ
                  exact_mod_cast hcard
                · rw [Set.indicator_of_notMem hω]
                  have hf : (Finset.range (R vbl A pick hpick ω)).filter
                      (fun t => canon (T vbl A pick hpick ω t) = σ) = ∅ := by
                    apply Finset.eq_empty_iff_forall_notMem.mpr
                    intro t ht
                    exact hω ⟨t, (Finset.mem_range.mp (Finset.mem_filter.mp ht).1),
                      (Finset.mem_filter.mp ht).2⟩
                  simp [F, hf]
          _ = (1 : ℝ≥0∞) * μN N μ (E σ) := by
              exact lintegral_indicator_const
                (measurableSet_occ (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
                  (hA := hA) (N := N) σ) (c := (1 : ℝ≥0∞))
          _ = μN N μ (E σ) := by simp
    _ ≤ ∑ σ ∈ s, treeProd (μ := μ) A σ := by
        apply Finset.sum_le_sum
        intro σ hσ
        simpa [E] using occurrence_canon_le_treeProd (μ := μ) (vbl := vbl) (A := A)
          (hA := hA) (hdet := hdet) (pick := pick) (hpick := hpick) (N := N) σ
    _ ≤ ∑ σ ∈ s, ENNReal.ofReal (x'Prod vbl x σ) := by
        apply Finset.sum_le_sum
        intro σ hσ
        exact treeProd_le_ofReal_x'Prod (μ := μ) (vbl := vbl) (A := A) (x := x)
          (hLLL := hLLL) (hx'0 := hx'0) σ
    _ = ∑ σ ∈ s, ENNReal.ofReal (x i / (1 - x i)) * ENNReal.ofReal (gwWeight vbl x σ) := by
        refine Finset.sum_congr rfl ?_
        intro σ hσ
        have hroot : labelOf σ = i := labelOf_mem_gwFinsetHeight vbl i (N - 1) hσ
        have hprop : Proper σ := proper_of_mem_gwFinsetHeight vbl i (N - 1) hσ
        have hwit : IsWitnessTree vbl σ := witness_of_mem_gwFinsetHeight vbl i (N - 1) hσ
        rw [x'Prod_eq_div_mul_gwWeight (vbl := vbl) (x := x) (hx₁ := hx₁) i hroot hprop hwit]
        rw [ENNReal.ofReal_mul hdiv_nonneg]
    _ = ENNReal.ofReal (x i / (1 - x i)) * ∑ σ ∈ s, ENNReal.ofReal (gwWeight vbl x σ) := by
        rw [← Finset.mul_sum]
    _ = ENNReal.ofReal (x i / (1 - x i)) * ENNReal.ofReal (∑ σ ∈ s, gwWeight vbl x σ) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro σ hσ
        exact hgw_nonneg σ
    _ ≤ ENNReal.ofReal (x i / (1 - x i)) * ENNReal.ofReal (1 : ℝ) := by
        exact mul_le_mul' le_rfl
          (ENNReal.ofReal_le_ofReal (gwWeight_sum_le_one vbl x hx₀ hx1 i (N - 1)))
    _ = ENNReal.ofReal (x i / (1 - x i)) := by
        rw [ENNReal.ofReal_one, mul_one]

include instInhabitedι in
omit [(j : κ) → MeasurableSpace (Ω j)] [DecidableEq κ] [Fintype κ] in
/-- The double-counting identity: the stopping time equals the sum of the per-variable
resample counts (each step resamples exactly one variable, counted by exactly one
`countLog`). `Finset.card_eq_sum_card_fiberwise` with `s = {t < N | log ω t ≠ none}`,
`t = univ`, `f t = (log ω t).getD default`; glue (a) `s = range (R ω)` via
`log_ne_none_iff_lt_R` + `R_le` + `Finset.card_range`, glue (b) per-`i` fiber equality
via `Option.some_ne_none` + `getD`/case-split simp. -/
private lemma R_eq_sum_countLog (ω : ΩN N Ω) :
    R vbl A pick hpick ω = ∑ i, countLog (log vbl A pick hpick) ω i := by
  let s : Finset ℕ := (Finset.range N).filter (fun t => log vbl A pick hpick ω t ≠ none)
  have hs : s = Finset.range (R vbl A pick hpick ω) := by
    apply Finset.ext; intro t
    simp only [s, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact (log_ne_none_iff_lt_R vbl A pick hpick ω).mp h.2
    · intro ht
      exact ⟨Nat.lt_of_lt_of_le ht (R_le vbl A pick hpick ω),
        (log_ne_none_iff_lt_R vbl A pick hpick ω).mpr ht⟩
  have hfiber : ∀ i, (s.filter (fun t => (log vbl A pick hpick ω t).getD default = i)) =
      (Finset.range N).filter (fun t => log vbl A pick hpick ω t = some i) := by
    intro i
    apply Finset.ext; intro t
    simp only [s, Finset.mem_filter]
    constructor
    · intro h
      rcases h with ⟨⟨htm, hne⟩, hi⟩
      refine ⟨htm, ?_⟩
      cases hx : log vbl A pick hpick ω t with
      | none => exact (hne hx).elim
      | some a =>
          rw [hx] at hi
          change a = i at hi
          rw [hi]
    · intro h
      rcases h with ⟨htm, heq⟩
      refine ⟨⟨htm, ?_⟩, ?_⟩
      · intro hnone
        rw [hnone] at heq
        cases heq
      · rw [heq]
        rfl
  calc
    R vbl A pick hpick ω
        = (Finset.range (R vbl A pick hpick ω)).card := (Finset.card_range _).symm
    _ = s.card := by rw [hs]
    _ = ∑ i, (s.filter (fun t => (log vbl A pick hpick ω t).getD default = i)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (s := s) (t := Finset.univ)
          (f := fun t => (log vbl A pick hpick ω t).getD default)]
        intro t ht
        exact Finset.mem_univ _
    _ = ∑ i, countLog (log vbl A pick hpick) ω i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hfiber i]
        rfl

include instInhabitedι instDecidableEqι in
/-- **The total expected number of resamplings** (survey B F24, blueprint 60.3): the
expectation of the stopping time is at most the LLL sum `∑ i, x i / (1 - x i)`. Four
calc steps: `lintegral_congr` + the double-counting identity `R_eq_sum_countLog` +
`Nat.cast_sum`; `lintegral_finsetSum' Finset.univ`; `Finset.sum_le_sum` + 60.2's
`moserTardos_bound`; `ENNReal.ofReal_sum_of_nonneg`. Same explicit-binder pattern as
`moserTardos_bound`.

Requires `[Inhabited ι]` (the paper's m ≥ 1 setting): the statement remains true at
empty `ι` — `R ω = 0` for every `ω` there (time 0 already has no violated event,
vacuously, so the stopping time is found, not the `N` fallback) — but the current proof
route cannot discharge it without an inhabitant (the per-`i` bound `moserTardos_bound`
plus `treeAt`'s dummy root `WitnessTree.mk (t, default) []`). -/
theorem moserTardos_total {N : ℕ} (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
    (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1) :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i)) := by
  calc
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
        = ∫⁻ ω : ΩN N Ω,
            (∑ i, (countLog (log vbl A pick hpick) ω i : ℝ≥0∞)) ∂ μN N μ := by
          apply lintegral_congr
          intro ω
          rw [R_eq_sum_countLog (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω]
          rw [Nat.cast_sum]
    _ = ∑ i, ∫⁻ ω : ΩN N Ω,
            (countLog (log vbl A pick hpick) ω i : ℝ≥0∞) ∂ μN N μ := by
          rw [lintegral_finsetSum' Finset.univ
            (f := fun i ω => (countLog (log vbl A pick hpick) ω i : ℝ≥0∞))]
          intro i hi
          have hcast : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := by
            intro s hs
            change True
            trivial
          exact (hcast.comp (measurable_countLog (vbl := vbl) (A := A) (hA := hA)
            (pick := pick) (hpick := hpick) (N := N) (i := i))).aemeasurable
    _ ≤ ∑ i, ENNReal.ofReal (x i / (1 - x i)) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact moserTardos_bound (N := N) (Ω := Ω) (μ := μ) (vbl := vbl) (A := A)
            (hA := hA) (hdet := hdet) (x := x) (hx₀ := hx₀) (hx₁ := hx₁)
            (hLLL := hLLL) (pick := pick) (hpick := hpick) (i := i)
    _ = ENNReal.ofReal (∑ i, x i / (1 - x i)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg]
          intro i hi
          exact div_nonneg (hx₀ i) (sub_nonneg.mpr (le_of_lt (hx₁ i)))

/-- The multiplicative Markov tail bound: the probability that the algorithm survives to
time `N` (i.e. `R = N`), weighted by `N`, is at most the LLL sum `∑ i, x i / (1 - x i)`.
True for all `N` (including `N = 0`, where the divided form is false).

Requires `[Inhabited ι]` (the paper's m ≥ 1 setting): the statement remains true at
empty `ι` — `R ω = 0` for every `ω` (time 0 already has no violated event, vacuously),
so `{ω | R ω = N}` is `∅` for `N > 0` and `Set.univ` for `N = 0`, giving LHS `0` in
both cases — but the current proof route cannot discharge it without an inhabitant
(via `moserTardos_total`, hence `treeAt`'s dummy root `WitnessTree.mk (t, default) []`). -/
theorem moserTardos_tail {N : ℕ} (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
    (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1) :
    (N : ℝ≥0∞) * μN N μ {ω : ΩN N Ω | R vbl A pick hpick ω = N}
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i)) := by
  classical
  let s : Set (ΩN N Ω) := {ω | R vbl A pick hpick ω = N}
  calc
    (N : ℝ≥0∞) * μN N μ s
        = ∫⁻ ω : ΩN N Ω, s.indicator (fun _ => (N : ℝ≥0∞)) ω ∂ μN N μ := by
          rw [lintegral_indicator_const
            (hs := show MeasurableSet s from measurableSet_R_eq (vbl := vbl) (A := A)
              (hA := hA) (pick := pick) (hpick := hpick) (N := N))
            (c := (N : ℝ≥0∞))]
    _ ≤ ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ := by
          apply lintegral_mono
          intro ω
          by_cases h : ω ∈ s
          · rw [Set.indicator_of_mem h]
            change (N : ℝ≥0∞) ≤ (R vbl A pick hpick ω : ℝ≥0∞)
            have hN : R vbl A pick hpick ω = N := h
            rw [hN]
          · rw [Set.indicator_of_notMem h]
            exact zero_le
    _ ≤ ENNReal.ofReal (∑ i, x i / (1 - x i)) := by
          exact moserTardos_total (N := N) (Ω := Ω) (μ := μ) (vbl := vbl) (A := A)
            (hA := hA) (hdet := hdet) (x := x) (hx₀ := hx₀) (hx₁ := hx₁)
            (hLLL := hLLL) (pick := pick) (hpick := hpick)

end MainTheorem

/-! ## Existence of an avoiding assignment (60.5) -/

section Exists

variable {ι : Type u} [instDecidableEqι : DecidableEq ι] [instInhabitedι : Inhabited ι]
  [Fintype ι]
variable {κ : Type u} [DecidableEq κ] [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hA : ∀ i, MeasurableSet (A i))
variable (hdet : ∀ i, DeterminedBy (A i) (vbl i))
variable (x : ι → ℝ)
variable (hx₀ : ∀ i, 0 ≤ x i)
variable (hx₁ : ∀ i, x i < 1)
variable (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
  (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-- The constructive Lovász Local Lemma (Moser–Tardos), pick-carrying variant: under
the variable-model hypotheses, some full assignment avoids every bad event. The `σ` is
exhibited by the algorithm's run at the stopping time: an execution of the resampling
algorithm up to `N` steps, for any `N` above the LLL sum `∑ i, x i / (1 - x i)`, must
stop strictly before `N` (the tail bound `moserTardos_tail` forces the stopping time
`R` to be below `N` on a set of positive measure), and the assignment at the stopping
time violates no bad event. This is the constructive companion of
`TCSLean.Lovasz.lovaszLocalLemma_exists`. -/
private lemma moserTardos_exists_pick (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j)))
    (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i := by
  classical
  let s := ∑ i, x i / (1 - x i)
  have hs₀ : 0 ≤ s :=
    Finset.sum_nonneg fun i _ => div_nonneg (hx₀ i) (sub_nonneg.mpr (le_of_lt (hx₁ i)))
  rcases exists_nat_gt s with ⟨N, hsN⟩
  have hNpos : 0 < N := by
    exact_mod_cast lt_of_le_of_lt hs₀ hsN
  have hNlt : ENNReal.ofReal s < (N : ℝ≥0∞) := by
    exact (ENNReal.ofReal_lt_natCast (n := N) (Nat.ne_of_gt hNpos)).2 hsN
  by_contra h
  push Not at h
  have hR : ∀ ω : ΩN N Ω, R vbl A pick hpick ω = N := by
    intro ω
    unfold R
    split_ifs with hf
    · exfalso
      rcases hf with ⟨t, ht⟩
      rcases ht with ⟨htlt, hnv⟩
      obtain ⟨i, hi⟩ := h (assign ω (count vbl A pick hpick ω ⟨t, htlt⟩))
      exact (hnv i) hi
    · rfl
  have htail := moserTardos_tail (N := N) (Ω := Ω) (μ := μ) (vbl := vbl) (A := A)
    (hA := hA) (hdet := hdet) (x := x) (hx₀ := hx₀) (hx₁ := hx₁) (hLLL := hLLL)
    (pick := pick) (hpick := hpick)
  have hset : {ω : ΩN N Ω | R vbl A pick hpick ω = N} = Set.univ := by
    ext ω
    simp [hR ω]
  rw [hset] at htail
  have hle : (N : ℝ≥0∞) ≤ ENNReal.ofReal s := by
    simpa [s] using htail
  exact (lt_irrefl (N : ℝ≥0∞)) (lt_of_le_of_lt hle hNlt)

/-- The constructive Lovász Local Lemma (Moser–Tardos), pick-free variant carrying the
section's `[Inhabited ι]` (the witness-tree route needs the inhabitant): the
tie-breaking-independent instantiation of `moserTardos_exists_pick` with
`Classical.choose`. The public `moserTardos_exists` below removes the inhabitant. -/
private lemma moserTardos_exists_inhabited (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j))) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i := by
  exact moserTardos_exists_pick Ω μ vbl A hA hdet x hx₀ hx₁ hLLL
    (fun S => Classical.choose S.2) (fun S => Classical.choose_spec S.2)

omit instInhabitedι in
/-- The constructive Lovász Local Lemma (Moser–Tardos): under the variable-model
hypotheses, some full assignment avoids every bad event. The conclusion is
tie-breaking-independent, so no `pick`/`hpick` choice function is required:
`moserTardos_exists_pick` is instantiated with `Classical.choose`. The `σ` is exhibited
by the algorithm's run at the stopping time: an execution of the resampling algorithm
up to `N` steps, for any `N` above the LLL sum `∑ i, x i / (1 - x i)`, must stop
strictly before `N` (the tail bound `moserTardos_tail` forces the stopping time `R` to
be below `N` on a set of positive measure), and the assignment at the stopping time
violates no bad event. This is the constructive companion of
`TCSLean.Lovasz.lovaszLocalLemma_exists`.

No `[Inhabited ι]` is required: the nonempty case calls the inhabitant-carrying
`moserTardos_exists_inhabited` after `Classical.inhabited_of_nonempty`, and at empty `ι`
the conclusion is vacuous (`∀ i, σ ∉ A i` holds for any `σ`), with `σ` built from the
nonemptiness of each `Ω j` (`μ j` is a probability measure, so `μ j Set.univ = 1 > 0`). -/
theorem moserTardos_exists (Ω : κ → Type v) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal
      (x i * ∏ j ∈ (overlapGraph vbl).neighborFinset i, (1 - x j))) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i := by
  classical
  by_cases hι : Nonempty ι
  · letI : Inhabited ι := Classical.inhabited_of_nonempty hι
    exact moserTardos_exists_inhabited Ω μ vbl A hA hdet x hx₀ hx₁ hLLL
  · have hΩ : ∀ j, Nonempty (Ω j) := by
      intro j
      have h1 : (μ j) Set.univ = 1 :=
        (show IsProbabilityMeasure (μ j) from inferInstance).measure_univ
      have huniv : (Set.univ : Set (Ω j)).Nonempty :=
        nonempty_of_measure_ne_zero (μ := μ j) (s := Set.univ) (by simp [h1])
      exact Nonempty.intro (Classical.choose huniv)
    refine ⟨fun j => Classical.choice (hΩ j), fun i => (hι ⟨i⟩).elim⟩

end Exists

end TCSLean.MoserTardos

end
