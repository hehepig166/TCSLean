/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
import TCSLean.MoserTardos.VariableModel
import TCSLean.MoserTardos.Algorithm

/-!
# Witness trees

This file defines the witness-tree type used by the Moser–Tardos witness-tree coupling:
a rooted tree whose vertices carry labels in `ι` and whose children form an ordered list.
Vertices are addressed by paths (lists of child indices); it also defines the structural
predicates `Proper` and `IsGood` (the hypothesis the coupling consumes) and a manually
written `DecidableEq` instance. It also constructs the witness tree of an execution log:
the reverse-scan construction `treeAt` (30.3), its time-stripping `forgetTime`, and the
occurring tree `T`.

## Main definitions

* `WitnessTree`: a rooted, ordered, labelled tree — constructor `mk`, accessors
  `labelOf`/`childrenOf`, and the structural measures `size`/`height`.
* `ValidPath`: a data-valued certificate that a list of child indices addresses a vertex.
* `treeAt`/`labelAt`: the subtree / label at a valid path.
* `depth`: the depth of the vertex at a path — the path length.
* `Proper`: the children of every vertex carry pairwise distinct labels.
* `IsGood`: `Proper` plus pairwise-disjoint variable sets for vertices at the same depth.
* `instDecidableEq`: decidable equality by mutual structural recursion
  (`eqDecTree`/`eqDecList`), computable and usable by `decide`.
* `deepestEligible`/`attachBelow`/`attachInFirst`: the reverse-scan insertion core
  (30.2) — the deepest eligible depth, and the attachment of a new leaf below a
  deepest eligible vertex (mutually recursive).
* `labels`: the labels of all vertices, in preorder.
* `validPath_append`: appends a child index to a valid path (data-valued, like
  `ValidPath` itself).
* `treeElig`: the time-labeled lift of Γ⁺-eligibility — same event, or overlapping
  variable sets (an `abbrev`, so the `Decidable` instance for `treeAt` synthesizes).
* `treeAt` (the construction fold, 30.3 — distinct from the path-API `treeAt` above):
  the reverse-scan `foldr` over `List.range t` building the witness tree of a log
  prefix, attaching each occurring entry below a deepest eligible vertex.
* `forgetTime`: drops the time component of the labels (shape-preserving).
* `T`: the occurring witness tree `T ω t` of the execution table at time `t`.

## Main results

* `treeAt_nil`/`treeAt_cons`, `labelAt_nil`/`labelAt_cons`: `rfl` round-trips of the
  path API.
* `depth_nil`/`depth_cons`: the depth unfolds as the path length.
* `labelOf_mk`/`childrenOf_mk`/`size_mk`: `simp` unfoldings of the structural API.
* `size_pos`: every tree has at least one vertex.
* `proper_mk`: the `simp` unfolding of `Proper` at the root.
* The attach spec family (the single invariant 30.4–30.6 consume):
  `deepestEligible_eq_none`/`deepestEligible_eq_some` (S1: the maximum eligible
  depth), `attachBelow_eq_self_of_deepestEligible_none` (S2a: no eligible vertex,
  tree unchanged), `attachBelow_spec`/`attachBelow_newVertex` (S2b: the new leaf
  `mk i []` is a child of a depth-`d` eligible vertex, at depth `d + 1` with label
  `i`), `labelAt_attachBelow` (old paths stay valid with unchanged labels),
  `size_attachBelow`/`labels_attachBelow` (the attachment is a single new leaf),
  `attachBelow_proper` (properness preserved).
* `treeAt_validPath_append`: the subtree at an appended path is the appended child.
* The construction root-label lemmas (30.6's injectivity inputs): `treeAt_root_label`
  (the root of the construction tree is the entry at time `t`) and `T_root_label` (the
  root of `T ω t` is the resampled event).
* The `forgetTime` transport API (30.7's inputs): `labelOf_forgetTime`/
  `childrenOf_forgetTime`/`size_forgetTime` (root label, children, and size project
  through the time-stripping), `forgetTime_getElem?`/`validPath_forgetTime`/
  `treeAt_forgetTime`/`labelAt_forgetTime` (child access, paths, subtrees, and labels
  transport).
* `treeAt_proper`/`treeAt_pair_proper` (30.4, Prop 10.1): the witness tree of a log
  prefix is proper — the abstract form `treeAt_proper` (for `forgetTime (treeAt vbl Λ t)`,
  the form `T` and 30.7 consume) and the pair-level bonus `treeAt_pair_proper` (for
  `treeAt vbl Λ t`), each via a one-insertion-step lemma plus a fold induction.
* `treeAt_count_label`/`treeAt_forgetTime_injective`/`treeAt_injective`/`T_injective`
  (30.6, Prop 12.1): the r-th occurrence A-count of `forgetTime (treeAt vbl Λ t)`, and
  the occurring-tree injectivity — distinct genuine times give distinct witness trees —
  via the fold invariant `foldr_count_label`, the occurrence comparison
  `length_filter_range_lt`, and the two-case argument on the time-labeled side.
* `depth_gt_of_earlier_overlap`/`treeAt_timeInject`/`vbl_disjoint_of_same_depth`
  (30.5, Lemma 11.1 / Cor 11.2): in the time-labeled constructed tree, an earlier entry
  sharing a variable with a later one is strictly deeper, distinct vertices have
  distinct times, and vertices at the same depth have disjoint variable sets — via the
  fold induction `foldr_depthStrict_timeInject` over `buildBelow`, the one-insertion
  steps `attachBelow_depthStrict_step`/`attachBelow_newVertex_unique`, and the
  old-or-new path glue `attachBelow_old_or_new`.
* `forgetTime_getElem?_of`/`validPath_of_forgetTime`/`labelAt_cast`/
  `labelAt_of_forgetTime` (30.7's inputs): the reverse transport — an abstract child of
  the `forgetTime` image lifts to a time-labeled child, a valid path in the image lifts
  to a valid path in the time-labeled tree (classical), and the lifted path carries the
  same label.
* `treeAt_isGood`/`T_isGood` (30.7, Prop 10.1 + Cor 11.2 transported): the witness tree
  of the log prefix is good — properness (30.4) plus same-depth disjointness (30.5)
  through the path lift. Unconditional: both ingredients hold for every `Λ`, so no
  `t < R` guard.
* `treeAt_size_le`/`T_size_le`/`T_size_le_N` (30.7): the occurring tree has at most
  `t + 1` vertices (each reverse-scan step adds at most one vertex, 30.2's
  `size_attachBelow`), hence at most `N` when `t < R` (20.3's `R_le`).

## References

The witness-tree type follows the Moser–Tardos notes, §8 ([moserTardos2010]).
-/

set_option autoImplicit false
set_option pp.unicode.fun true

namespace TCSLean.MoserTardos

universe u v

/-- A rooted tree whose vertices carry labels in `ι` and whose children form an ordered
list. Vertices are addressed by paths (lists of child indices); the root has label `label`
and children `children`. -/
inductive WitnessTree (ι : Type u) where
  | mk : (label : ι) → (children : List (WitnessTree ι)) → WitnessTree ι

namespace WitnessTree

variable {ι : Type u}
variable {κ : Type v}

/-- The label of the root. -/
def labelOf : WitnessTree ι → ι
  | mk a _ => a

/-- The children of the root, as a list. -/
def childrenOf : WitnessTree ι → List (WitnessTree ι)
  | mk _ cs => cs

/-- The number of vertices. -/
def size : WitnessTree ι → ℕ
  | mk _ cs => 1 + (cs.map size).sum

/-- The height: 0 for a leaf, 1 + the max height of the children otherwise. -/
def height : WitnessTree ι → ℕ
  | mk _ [] => 0
  | mk _ cs => (cs.map height).foldl max 0 + 1

/-! ## Path API -/

/-- A list of child indices addressing a vertex: `[]` is the root, `i :: p` is the vertex
reached from the `i`-th child by `p`. Data-valued so that `treeAt` can eliminate it
(a Prop `ValidPath` could not: eliminating a membership `Exists` into data needs choice). -/
inductive ValidPath : WitnessTree ι → List ℕ → Type u where
  | root {τ : WitnessTree ι} : ValidPath τ []
  | cons {τ : WitnessTree ι} {p : List ℕ} (i : ℕ) (c : WitnessTree ι)
      (hc : τ.childrenOf[i]? = some c) :
      ValidPath c p → ValidPath τ (i :: p)

/-- The subtree at path `p`, when `p` is a valid path. -/
def treeAt {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) : WitnessTree ι :=
  match p with
  | [] => τ
  | _i :: p' => by
      cases hp with
      | cons i c hc hvp => exact treeAt hvp

/-- The label of the vertex at path `p`, when `p` is a valid path. -/
def labelAt {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) : ι :=
  labelOf (treeAt hp)

/-- The depth of the vertex at path `p`: the path length (the tree argument is decorative,
kept for API uniformity). -/
def depth (_τ : WitnessTree ι) (p : List ℕ) : ℕ := p.length

/-- `Proper τ`: the children of every vertex carry pairwise distinct labels. -/
def Proper : WitnessTree ι → Prop
  | mk _ cs => (cs.map labelOf).Nodup ∧ ∀ c ∈ cs, Proper c

/-- `IsGood vbl τ`: `τ` is proper and vertices at the same depth have disjoint variable
sets (the hypothesis the coupling consumes; survey B §4.2-4.3). -/
def IsGood (vbl : ι → Finset κ) (τ : WitnessTree ι) : Prop :=
  Proper τ ∧
    ∀ p q (hp : ValidPath τ p) (hq : ValidPath τ q),
      p ≠ q → depth τ p = depth τ q →
        Disjoint (vbl (labelAt hp)) (vbl (labelAt hq))

/-! ## Round-trip lemmas -/

@[simp] theorem treeAt_nil (τ : WitnessTree ι) (hp : ValidPath τ []) :
    treeAt hp = τ := rfl

@[simp] theorem treeAt_cons (τ : WitnessTree ι) (i : ℕ) (p : List ℕ) (c : WitnessTree ι)
    (hc : τ.childrenOf[i]? = some c) (hvp : ValidPath c p) :
    treeAt (.cons i c hc hvp : ValidPath τ (i :: p)) = treeAt hvp := rfl

@[simp] theorem labelAt_nil (τ : WitnessTree ι) (hp : ValidPath τ []) :
    labelAt hp = labelOf τ := rfl

@[simp] theorem labelAt_cons (τ : WitnessTree ι) (i : ℕ) (p : List ℕ) (c : WitnessTree ι)
    (hc : τ.childrenOf[i]? = some c) (hvp : ValidPath c p) :
    labelAt (.cons i c hc hvp : ValidPath τ (i :: p)) = labelAt hvp := rfl

@[simp] theorem depth_nil (τ : WitnessTree ι) : depth τ [] = 0 := rfl

@[simp] theorem depth_cons (τ : WitnessTree ι) (i : ℕ) (p : List ℕ) :
    depth τ (i :: p) = depth τ p + 1 := by
  simp [depth]

@[simp] theorem labelOf_mk (l : ι) (cs : List (WitnessTree ι)) : labelOf (mk l cs) = l := rfl

@[simp] theorem childrenOf_mk (l : ι) (cs : List (WitnessTree ι)) :
    childrenOf (mk l cs) = cs := rfl

@[simp] theorem size_mk (l : ι) (cs : List (WitnessTree ι)) :
    size (mk l cs) = 1 + (cs.map size).sum := by
  simp [size]

theorem size_pos (τ : WitnessTree ι) : 0 < size τ := by
  cases τ with
  | mk l cs => simp

@[simp] theorem proper_mk (l : ι) (cs : List (WitnessTree ι)) :
    Proper (mk l cs) ↔ (cs.map labelOf).Nodup ∧ ∀ c ∈ cs, Proper c := by
  simp [Proper]

/-! ## Decidable equality (manual; `deriving DecidableEq` fails in v4.32.0) -/

mutual
  /-- Tree equality step of the manual `DecidableEq`: two trees are equal iff their labels
  and children are equal. -/
  def eqDecTree [DecidableEq ι] (a : WitnessTree ι) (b : WitnessTree ι) : Decidable (a = b) :=
    match a with
    | mk l₁ cs₁ =>
        match b with
        | mk l₂ cs₂ =>
            match decEq l₁ l₂ with
            | isTrue hl =>
                match eqDecList cs₁ cs₂ with
                | isTrue hcs => isTrue (by subst hl; subst hcs; rfl)
                | isFalse hcs => isFalse (by
                    intro h
                    exact hcs (congrArg childrenOf h))
            | isFalse hl => isFalse (by
                intro h
                exact hl (congrArg labelOf h))
  /-- List equality step of the manual `DecidableEq`, via `eqDecTree` on the heads. -/
  def eqDecList [DecidableEq ι] (l₁ : List (WitnessTree ι)) (l₂ : List (WitnessTree ι)) :
      Decidable (l₁ = l₂) :=
    match l₁ with
    | [] =>
        match l₂ with
        | [] => isTrue rfl
        | _ :: _ => isFalse (by intro h; cases h)
    | a :: as =>
        match l₂ with
        | [] => isFalse (by intro h; cases h)
        | b :: bs =>
            match eqDecTree a b with
            | isTrue hab =>
                match eqDecList as bs with
                | isTrue has => isTrue (by subst hab; subst has; rfl)
                | isFalse has => isFalse (by
                    intro h
                    exact has (List.cons.inj h).2)
            | isFalse hab => isFalse (by
                intro h
                exact hab (List.cons.inj h).1)
end

/-- Decidable equality for witness trees (manual: the `deriving` handler rejects this
inductive in v4.32.0, and the nested recursor `WitnessTree.rec` is not codegen-supported).
Mutual structural recursion with the list step, so it computes (usable by `decide`). -/
instance instDecidableEq [DecidableEq ι] : DecidableEq (WitnessTree ι) :=
  eqDecTree


/-! ## Reverse-scan insertion (30.2): deepestEligible / attachBelow / attachInFirst -/

/-- Combine two optional depths, taking the maximum. -/
private def maxOption (m o : Option ℕ) : Option ℕ :=
  match m, o with
  | none, o => o
  | m, none => m
  | some a, some b => some (max a b)

mutual
  /-- The maximum depth of a vertex of the tree whose label is eligible for `i`;
  `none` if no vertex is eligible. -/
  def deepestEligible (elig : ι → ι → Prop) [∀ a b, Decidable (elig a b)] (i : ι) :
      WitnessTree ι → Option ℕ
    | mk a cs =>
      let d := cs.foldl (fun m c => maxOption m ((deepestEligible elig i c).map (· + 1))) none
      if elig i a then some (d.getD 0) else d

  /-- Attach a new leaf labeled `i` below a deepest vertex whose label is eligible for `i`;
  if no vertex is eligible, the tree is unchanged. Children are appended (never prepended)
  so that existing paths remain valid (the notes allow any tie-break, notes §9 step 5). -/
  def attachBelow (elig : ι → ι → Prop) [∀ a b, Decidable (elig a b)] (i : ι) :
      WitnessTree ι → WitnessTree ι
    | mk a cs =>
      let d := cs.foldl (fun m c => maxOption m ((deepestEligible elig i c).map (· + 1))) none
      match d with
      | none => if elig i a then mk a (cs ++ [mk i []]) else mk a cs
      | some dd => mk a (attachInFirst elig i dd cs)

  /-- Replace the leftmost child whose subtree contains an eligible vertex at depth `dd - 1`
  by its `attachBelow`-image. -/
  def attachInFirst (elig : ι → ι → Prop) [∀ a b, Decidable (elig a b)] (i : ι)
      (dd : ℕ) :
      List (WitnessTree ι) → List (WitnessTree ι)
    | [] => []
    | c :: cs =>
      if deepestEligible elig i c = some (dd - 1) then
        attachBelow elig i c :: cs
      else c :: attachInFirst elig i dd cs
end

/-- The labels of all vertices, in preorder. -/
def labels : WitnessTree ι → List ι
  | mk a cs => a :: cs.flatMap labels

/-! ## Path extension (needed to name the newly attached vertex) -/

/-- Append a child index to a valid path. (Type-valued, like `ValidPath` itself:
the extension is a data certificate, not a proposition. Match on the path first —
recursing on `ValidPath` directly would use the codegen-unsupported indexed recursor,
cf. `treeAt` in 30.1.) -/
def validPath_append {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) {k : ℕ}
    {c : WitnessTree ι} (hk : (treeAt hp).childrenOf[k]? = some c) :
    ValidPath τ (p ++ [k]) :=
  match p with
  | [] => .cons k c hk .root
  | i :: p' => by
      match hp with
      | .cons j cj hcj hvp =>
          exact .cons j cj hcj (validPath_append hvp (by simpa [treeAt_cons] using hk))

/-- The subtree at an appended path is the appended child. -/
theorem treeAt_validPath_append {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) {k : ℕ}
    {c : WitnessTree ι} (hk : (treeAt hp).childrenOf[k]? = some c) :
    treeAt (validPath_append hp hk) = c :=
  match p with
  | [] => by
      simp [validPath_append, treeAt]
  | i :: p' => by
      cases hp with
      | cons j cj hcj hvp =>
          simp [validPath_append]
          exact treeAt_validPath_append hvp (by simpa [treeAt_cons] using hk)

/-! ## The attach spec (the single invariant consumed by 30.4–30.6) -/

section AttachSpec

variable {elig : ι → ι → Prop} [∀ a b, Decidable (elig a b)]
variable {i : ι}
variable {α : Type u}

/-! ## Private helpers for the spec proofs (S1, S2a, S2b) -/

private theorem maxOption_eq_none {m o : Option ℕ} :
    maxOption m o = none ↔ m = none ∧ o = none := by
  cases m <;> cases o <;> simp [maxOption]

private theorem maxOption_eq_some {m o : Option ℕ} {d : ℕ} :
    maxOption m o = some d ↔
      (m = some d ∨ o = some d) ∧ (∀ k, m = some k → k ≤ d) ∧
        (∀ k, o = some k → k ≤ d) := by
  cases m <;> cases o <;> simp [maxOption] <;> omega

private theorem maxOption_bound {m o : Option ℕ} {d : ℕ} :
    (∀ k, maxOption m o = some k → k ≤ d) ↔
      (∀ k, m = some k → k ≤ d) ∧ (∀ k, o = some k → k ≤ d) := by
  cases m <;> cases o <;> simp [maxOption]

private theorem exists_eq_or_imp_swap {p q : α → Prop} {a : α} :
    (∃ x, (x = a ∨ p x) ∧ q x) ↔ q a ∨ ∃ x, p x ∧ q x := by
  constructor
  · rintro ⟨x, hx | hx, hq⟩
    · exact Or.inl (hx ▸ hq)
    · exact Or.inr ⟨x, hx, hq⟩
  · rintro (ha | ⟨x, hp, hq⟩)
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨x, Or.inr hp, hq⟩

private theorem forall_eq_or_imp_swap {p q : α → Prop} {a : α} :
    (∀ x, (x = a ∨ p x) → q x) ↔ q a ∧ ∀ x, p x → q x := by
  constructor
  · intro h
    exact ⟨h a (Or.inl rfl), by intro x hp; exact h x (Or.inr hp)⟩
  · rintro ⟨ha, hp⟩ x (hx | hx)
    · simpa [hx] using ha
    · exact hp x hx

/-- The fold computes the maximum option: `none` iff all values are `none`. -/
private theorem foldl_maxOption_eq_none (g : α → Option ℕ) (cs : List α) :
    cs.foldl (fun m c => maxOption m (g c)) none = none ↔ ∀ c ∈ cs, g c = none := by
  have hgen : ∀ m : Option ℕ, cs.foldl (fun m c => maxOption m (g c)) m = none ↔
      m = none ∧ ∀ c ∈ cs, g c = none := by
    intro m
    induction cs generalizing m with
    | nil => simp
    | cons c cs ih =>
        simp only [List.foldl_cons, List.mem_cons]
        rw [ih (maxOption m (g c))]
        rw [maxOption_eq_none, forall_eq_or_imp_swap]
        tauto
  simpa using hgen none

/-- The fold computes the maximum option: `some d` iff `d` is attained and bounds all. -/
private theorem foldl_maxOption_eq_some (g : α → Option ℕ) (cs : List α) (d : ℕ) :
    cs.foldl (fun m c => maxOption m (g c)) none = some d ↔
      (∃ c ∈ cs, g c = some d) ∧ ∀ c ∈ cs, ∀ k, g c = some k → k ≤ d := by
  have hgen : ∀ m : Option ℕ, cs.foldl (fun m c => maxOption m (g c)) m = some d ↔
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
        rw [ih (maxOption m (g c))]
        rw [maxOption_eq_some, maxOption_bound, exists_eq_or_imp_swap, forall_eq_or_imp_swap]
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

/-- S1 for the children's fold: the fold is `none` iff no child has an eligible vertex. -/
private theorem deepestEligible_children_eq_none {cs : List (WitnessTree ι)}
    (hP : ∀ c ∈ cs, deepestEligible elig i c = none ↔
        ∀ p, ∀ hp : ValidPath c p, ¬ elig i (labelAt hp)) :
    cs.foldl (fun m c => maxOption m ((deepestEligible elig i c).map (· + 1))) none = none ↔
      ∀ c ∈ cs, ∀ p, ∀ hp : ValidPath c p, ¬ elig i (labelAt hp) := by
  rw [foldl_maxOption_eq_none]
  constructor
  · intro h c hc p hp
    have hc' := h c hc
    rw [Option.map_eq_none_iff] at hc'
    exact (hP c hc).mp hc' p hp
  · intro h c hc
    rw [Option.map_eq_none_iff]
    exact (hP c hc).mpr (h c hc)

/-- S1 for the children's fold: `some d` iff some child has an eligible vertex at depth
`d - 1` and no child has one deeper. -/
private theorem deepestEligible_children_eq_some {cs : List (WitnessTree ι)} (d : ℕ)
    (hP : ∀ c ∈ cs, (deepestEligible elig i c = none ↔
        ∀ p, ∀ hp : ValidPath c p, ¬ elig i (labelAt hp)) ∧
      ∀ m, (deepestEligible elig i c = some m ↔
        (∃ p, ∃ hp : ValidPath c p, depth c p = m ∧ elig i (labelAt hp)) ∧
        ∀ p, ∀ hp : ValidPath c p, elig i (labelAt hp) → depth c p ≤ m)) :
    cs.foldl (fun m c => maxOption m ((deepestEligible elig i c).map (· + 1))) none = some d ↔
      (∃ c ∈ cs, ∃ p, ∃ hp : ValidPath c p, depth c p + 1 = d ∧ elig i (labelAt hp)) ∧
      ∀ c ∈ cs, ∀ p, ∀ hp : ValidPath c p, elig i (labelAt hp) → depth c p + 1 ≤ d := by
  rw [foldl_maxOption_eq_some]
  constructor
  · rintro ⟨hatt, hbd⟩
    constructor
    · rcases hatt with ⟨c, hc, hc'⟩
      rw [Option_map_succ_eq_some] at hc'
      rcases hc' with ⟨hde, hpos⟩
      rcases ((hP c hc).2 (d - 1)).mp hde with ⟨hatt', _⟩
      rcases hatt' with ⟨p, hp, hdp, helig⟩
      refine ⟨c, hc, p, hp, ?_, helig⟩
      omega
    · intro c hc p hp helig
      have hne : deepestEligible elig i c ≠ none := by
        intro hc'
        exact (hP c hc).1.mp hc' p hp helig
      have hm : ∃ m, deepestEligible elig i c = some m := by
        cases hf : deepestEligible elig i c with
        | none => exact (hne hf).elim
        | some m => exact ⟨m, rfl⟩
      rcases hm with ⟨m, hm⟩
      have hbdm : m + 1 ≤ d := by
        have : (deepestEligible elig i c).map (· + 1) = some (m + 1) := by simp [hm]
        exact hbd c hc (m + 1) this
      have hdp_le : depth c p ≤ m := (((hP c hc).2 m).mp hm).2 p hp helig
      omega
  · rintro ⟨hatt, hbd⟩
    constructor
    · rcases hatt with ⟨c, hc, p, hp, hdp, helig⟩
      have hde : deepestEligible elig i c = some (depth c p) := by
        refine ((hP c hc).2 (depth c p)).mpr ⟨⟨p, hp, rfl, helig⟩, ?_⟩
        intro p' hp' helig'
        have hle : depth c p' + 1 ≤ d := hbd c hc p' hp' helig'
        omega
      refine ⟨c, hc, ?_⟩
      simp [hde, hdp]
    · intro c hc k hk
      rw [Option_map_succ_eq_some] at hk
      rcases hk with ⟨hke, _⟩
      rcases ((hP c hc).2 (k - 1)).mp hke with ⟨hatt', _⟩
      rcases hatt' with ⟨p, hp, hdp, helig⟩
      have hle : depth c p + 1 ≤ d := hbd c hc p hp helig
      omega

/-- S1 for `mk a cs` from the children's spec. -/
private theorem deepestEligible_spec_mk {a : ι} {cs : List (WitnessTree ι)}
    (hP : ∀ c ∈ cs, (deepestEligible elig i c = none ↔
        ∀ p, ∀ hp : ValidPath c p, ¬ elig i (labelAt hp)) ∧
      ∀ d, (deepestEligible elig i c = some d ↔
        (∃ p, ∃ hp : ValidPath c p, depth c p = d ∧ elig i (labelAt hp)) ∧
        ∀ p, ∀ hp : ValidPath c p, elig i (labelAt hp) → depth c p ≤ d)) :
    (deepestEligible elig i (mk a cs) = none ↔
      ∀ p, ∀ hp : ValidPath (mk a cs) p, ¬ elig i (labelAt hp)) ∧
    ∀ d, deepestEligible elig i (mk a cs) = some d ↔
      (∃ p, ∃ hp : ValidPath (mk a cs) p, depth (mk a cs) p = d ∧ elig i (labelAt hp)) ∧
      ∀ p, ∀ hp : ValidPath (mk a cs) p, elig i (labelAt hp) → depth (mk a cs) p ≤ d := by
  have hch_none := deepestEligible_children_eq_none (cs := cs) (fun c hc => (hP c hc).1)
  have hch_some := deepestEligible_children_eq_some (cs := cs) (hP := hP)
  constructor
  · by_cases ha : elig i a <;> simp only [deepestEligible, ha, if_true, if_false]
    · constructor
      · intro h
        cases h
      · intro h
        exact (h [] .root ha).elim
    · rw [hch_none]
      constructor
      · intro h p hp
        cases p with
        | nil =>
            cases hp
            exact ha
        | cons j p' =>
            cases hp with
            | cons j' c hc hvp =>
                have hc' : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                have h' : ¬ elig i (labelAt hvp) := h c hc' p' hvp
                simpa [labelAt_cons] using h'
      · intro h c hc p hp
        rcases (List.mem_iff_getElem?).mp hc with ⟨j, hj⟩
        have h' : ¬ elig i (labelAt (.cons j c (by simpa using hj) hp :
          ValidPath (mk a cs) (j :: p))) :=
          h (j :: p) (.cons j c (by simpa using hj) hp)
        simpa [labelAt_cons] using h'
  · intro d
    by_cases ha : elig i a <;> simp only [deepestEligible, ha, if_true, if_false]
    · by_cases hfold :
        cs.foldl (fun m c => maxOption m ((deepestEligible elig i c).map (· + 1))) none = none
      · simp only [hfold, Option.getD, Option.some.injEq]
        constructor
        · intro hd
          subst d
          constructor
          · refine ⟨[], .root, ?_, ?_⟩
            · rfl
            · exact ha
          · intro p hp helig
            cases p with
            | nil =>
                cases hp
                simp
            | cons j p' =>
                cases hp with
                | cons j' c hc hvp =>
                    exfalso
                    have hc' : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                    exact hch_none.mp hfold c hc' p' hvp helig
        · intro hRHS
          rcases hRHS.1 with ⟨p, hp, hdp, helig⟩
          cases p with
          | nil =>
              cases hp
              simp [depth] at hdp
              exact hdp
          | cons j p' =>
              cases hp with
              | cons j' c hc hvp =>
                  exfalso
                  have hc' : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                  exact hch_none.mp hfold c hc' p' hvp helig
      · have hm : ∃ m, cs.foldl (fun m c =>
          maxOption m ((deepestEligible elig i c).map (· + 1))) none = some m := by
          cases hf : cs.foldl (fun m c =>
              maxOption m ((deepestEligible elig i c).map (· + 1))) none with
          | none => exact (hfold hf).elim
          | some m => exact ⟨m, rfl⟩
        rcases hm with ⟨m, hfold⟩
        simp only [hfold, Option.getD, Option.some.injEq]
        constructor
        · intro hmd
          subst d
          constructor
          · rcases (hch_some m).mp hfold with ⟨hattM, hbdM⟩
            rcases hattM with ⟨c, hc, p, hp, hdp, helig⟩
            rcases (List.mem_iff_getElem?).mp hc with ⟨j, hj⟩
            refine ⟨j :: p, .cons j c (by simpa using hj) hp, ?_, ?_⟩
            · simpa [depth] using hdp
            · simpa [labelAt_cons] using helig
          · intro p hp helig
            cases p with
            | nil =>
                cases hp
                simp
            | cons j p' =>
                cases hp with
                | cons j' c hc hvp =>
                    have hc' : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                    have hle : depth c p' + 1 ≤ m := ((hch_some m).mp hfold).2 c hc' p' hvp helig
                    simpa [depth] using hle
        · intro hRHS
          rcases (hch_some m).mp hfold with ⟨hattM, hbdM⟩
          rcases hattM with ⟨cM, hcM, pM, hpM, hdpM, heligM⟩
          rcases (List.mem_iff_getElem?).mp hcM with ⟨jM, hjM⟩
          rcases hRHS.1 with ⟨p, hp, hdp, helig⟩
          have hmle : m ≤ d := by
            have hle := hRHS.2 (jM :: pM) (.cons jM cM (by simpa using hjM) hpM)
              (by simpa [labelAt_cons] using heligM)
            simpa [depth, ← hdpM] using hle
          cases p with
          | nil =>
              cases hp
              simp [depth] at hdp
              omega
          | cons j p' =>
              cases hp with
              | cons j' c hc hvp =>
                  have hc' : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                  have hle : d ≤ m := by
                    have hle' := hbdM c hc' p' hvp helig
                    simpa [depth, ← hdp] using hle'
                  omega
    · rw [hch_some d]
      constructor
      · rintro ⟨hatt, hbd⟩
        constructor
        · rcases hatt with ⟨c, hc, p, hp, hdp, helig⟩
          rcases (List.mem_iff_getElem?).mp hc with ⟨j, hj⟩
          refine ⟨j :: p, .cons j c (by simpa using hj) hp, ?_, ?_⟩
          · simpa [depth] using hdp
          · simpa [labelAt_cons] using helig
        · intro p hp helig
          cases p with
          | nil =>
              cases hp
              exact (ha helig).elim
          | cons j p' =>
              cases hp with
              | cons j' c hc hvp =>
                  have hc' : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                  have hle : depth c p' + 1 ≤ d := hbd c hc' p' hvp helig
                  simpa [depth] using hle
      · intro hRHS
        constructor
        · rcases hRHS.1 with ⟨p, hp, hdp, helig⟩
          cases p with
          | nil =>
              cases hp
              exact (ha helig).elim
          | cons j p' =>
              cases hp with
              | cons j' c hc hvp =>
                  have hc' : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                  refine ⟨c, hc', p', hvp, ?_, helig⟩
                  simpa [depth] using hdp
        · intro c hc p hp helig
          rcases (List.mem_iff_getElem?).mp hc with ⟨j, hj⟩
          have hle : depth (mk a cs) (j :: p) ≤ d :=
            hRHS.2 (j :: p) (.cons j c (by simpa using hj) hp) (by simpa [labelAt_cons] using helig)
          simpa [depth] using hle

/-- S1: `deepestEligible` computes the maximum eligible depth. -/
private theorem deepestEligible_spec (τ : WitnessTree ι) :
    (deepestEligible elig i τ = none ↔
      ∀ p, ∀ hp : ValidPath τ p, ¬ elig i (labelAt hp)) ∧
    ∀ d, deepestEligible elig i τ = some d ↔
      (∃ p, ∃ hp : ValidPath τ p, depth τ p = d ∧ elig i (labelAt hp)) ∧
      ∀ p, ∀ hp : ValidPath τ p, elig i (labelAt hp) → depth τ p ≤ d := by
  refine WitnessTree.rec
      (motive_1 := fun τ => (deepestEligible elig i τ = none ↔
        ∀ p, ∀ hp : ValidPath τ p, ¬ elig i (labelAt hp)) ∧
      ∀ d, deepestEligible elig i τ = some d ↔
        (∃ p, ∃ hp : ValidPath τ p, depth τ p = d ∧ elig i (labelAt hp)) ∧
        ∀ p, ∀ hp : ValidPath τ p, elig i (labelAt hp) → depth τ p ≤ d)
      (motive_2 := fun cs => ∀ c ∈ cs, (deepestEligible elig i c = none ↔
        ∀ p, ∀ hp : ValidPath c p, ¬ elig i (labelAt hp)) ∧
      ∀ d, deepestEligible elig i c = some d ↔
        (∃ p, ∃ hp : ValidPath c p, depth c p = d ∧ elig i (labelAt hp)) ∧
        ∀ p, ∀ hp : ValidPath c p, elig i (labelAt hp) → depth c p ≤ d) ?_ ?_ ?_ τ
  · intro a cs ih
    exact deepestEligible_spec_mk (a := a) (cs := cs) ih
  · intro c hc
    simp at hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- `attachInFirst` replaces the leftmost matching child (in place) or is the identity. -/
private theorem attachInFirst_spec (dd : ℕ) (cs : List (WitnessTree ι)) :
    (∃ cs₁ c cs₂, cs = cs₁ ++ c :: cs₂ ∧
        attachInFirst elig i dd cs = cs₁ ++ attachBelow elig i c :: cs₂ ∧
        deepestEligible elig i c = some (dd - 1) ∧
        ∀ c' ∈ cs₁, deepestEligible elig i c' ≠ some (dd - 1)) ∨
    (attachInFirst elig i dd cs = cs ∧
        ∀ c' ∈ cs, deepestEligible elig i c' ≠ some (dd - 1)) := by
  induction cs with
  | nil => right; simp [attachInFirst]
  | cons c cs ih =>
      by_cases hc : deepestEligible elig i c = some (dd - 1)
      · left
        refine ⟨[], c, cs, rfl, ?_, hc, ?_⟩
        · simp [attachInFirst, hc]
        · intro c' hc'
          simp at hc'
      · rcases ih with ⟨cs₁, c₂, cs₂, hcs, haif, hd, hne⟩ | ⟨haif, hne⟩
        · left
          refine ⟨c :: cs₁, c₂, cs₂, ?_, ?_, hd, ?_⟩
          · simp [hcs]
          · simp [attachInFirst, hc, haif]
          · intro c' hc'
            rw [List.mem_cons] at hc'
            rcases hc' with rfl | hc'
            · exact hc
            · exact hne c' hc'
        · right
          constructor
          · simp [attachInFirst, hc, haif]
          · intro c' hc'
            rw [List.mem_cons] at hc'
            rcases hc' with rfl | hc'
            · exact hc
            · exact hne c' hc'

/-- The root label is preserved. -/
private theorem labelOf_attachBelow (τ : WitnessTree ι) :
    labelOf (attachBelow elig i τ) = labelOf τ := by
  cases τ with
  | mk a cs =>
      simp [attachBelow]
      split
      · split <;> simp
      · simp

/-- Position preservation: the `k`-th child is kept or replaced by its `attachBelow`-image. -/
private theorem attachInFirst_childrenOf_eq {dd : ℕ} {cs : List (WitnessTree ι)} {k : ℕ}
    {c : WitnessTree ι} (h : cs[k]? = some c) :
    (attachInFirst elig i dd cs)[k]? = some c ∨
      (attachInFirst elig i dd cs)[k]? = some (attachBelow elig i c) := by
  induction cs generalizing k with
  | nil => simp at h
  | cons c' cs ih =>
      cases k with
      | zero =>
          have h' : c' = c := by simpa using h
          subst c
          by_cases hd : deepestEligible elig i c' = some (dd - 1)
          · right
            simp [attachInFirst, hd]
          · left
            simp [attachInFirst, hd]
      | succ k =>
          have hk : cs[k]? = some c := by simpa using h
          by_cases hd : deepestEligible elig i c' = some (dd - 1)
          · left
            simp [attachInFirst, hd, hk]
          · rcases ih hk with hk' | hk'
            · left
              simp [attachInFirst, hd, hk']
            · right
              simp [attachInFirst, hd, hk']

/-- The children's root labels are preserved. -/
private theorem attachInFirst_map_labelOf {dd : ℕ} (cs : List (WitnessTree ι)) :
    (attachInFirst elig i dd cs).map labelOf = cs.map labelOf := by
  induction cs with
  | nil => simp [attachInFirst]
  | cons c cs ih =>
      by_cases hd : deepestEligible elig i c = some (dd - 1)
      · simp [attachInFirst, hd, labelOf_attachBelow]
      · simp [attachInFirst, hd, ih]

/-- The `attachInFirst` branch of S2b: the new leaf sits below a depth-`d` eligible vertex. -/
private theorem attachBelow_spec_attachInFirst {a : ι} {cs : List (WitnessTree ι)} {dd d : ℕ}
    (hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none = some dd)
    (hdd : dd = d)
    (hih : ∀ c ∈ cs, ∀ d', deepestEligible elig i c = some d' →
      ∃ p, ∃ hp : ValidPath (attachBelow elig i c) p, ∃ k : ℕ,
        ∃ _ : (treeAt hp).childrenOf[k]? = some (mk i []),
          depth (attachBelow elig i c) p = d' ∧ elig i (labelAt hp)) :
    ∃ p, ∃ hp : ValidPath (mk a (attachInFirst elig i dd cs)) p, ∃ k : ℕ,
      ∃ _ : (treeAt hp).childrenOf[k]? = some (mk i []),
        depth (mk a (attachInFirst elig i dd cs)) p = d ∧ elig i (labelAt hp) := by
  have hatt := ((foldl_maxOption_eq_some
    (fun c => (deepestEligible elig i c).map (· + 1)) cs dd).mp hfold).1
  rcases hatt with ⟨c, hc, hc'⟩
  rw [Option_map_succ_eq_some] at hc'
  rcases hc' with ⟨hdc, hposdd⟩
  rcases attachInFirst_spec (elig := elig) (i := i) dd cs with
    ⟨cs₁, c', cs₂, hcs, haif, hd', hne⟩ | ⟨haif, hne⟩
  · have hc'm : c' ∈ cs := by simp [hcs, List.mem_append]
    have hpos : (mk a (attachInFirst elig i dd cs)).childrenOf[cs₁.length]? =
      some (attachBelow elig i c') := by
      simp [haif]
    rcases hih c' hc'm (dd - 1) hd' with ⟨p', hp', k', hk', hdp', helig'⟩
    refine ⟨cs₁.length :: p', .cons cs₁.length (attachBelow elig i c') hpos hp', k',
      ?_, ?_, ?_⟩
    · simpa [treeAt_cons] using hk'
    · have hdp : depth (mk a (attachInFirst elig i dd cs)) (cs₁.length :: p') = dd := by
        have hdp'nat : p'.length = dd - 1 := by simpa [depth] using hdp'
        simp [depth]
        omega
      simpa [hdd] using hdp
    · simpa [labelAt_cons] using helig'
  · exact False.elim (hne c hc hdc)

/-- The size grows by at most one through the `attachInFirst` branch. -/
private theorem size_attachInFirst {a : ι} {dd : ℕ} {cs : List (WitnessTree ι)}
    (hih : ∀ c ∈ cs, size (attachBelow elig i c) ≤ size c + 1) :
    size (mk a (attachInFirst elig i dd cs)) ≤ size (mk a cs) + 1 := by
  rcases attachInFirst_spec (elig := elig) (i := i) dd cs with
    ⟨cs₁, c, cs₂, hcs, haif, hd, hne⟩ | ⟨haif, hne⟩
  · have hc : c ∈ cs := by simp [hcs, List.mem_append]
    rw [haif, hcs]
    have hsize : size (attachBelow elig i c) ≤ size c + 1 := hih c hc
    simp [List.map_append, List.sum_append]
    omega
  · simp [haif]

/-- The label multiset gains exactly `i` through the `attachInFirst` branch. -/
private theorem labels_attachInFirst {a : ι} {dd : ℕ} {cs : List (WitnessTree ι)}
    (hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none = some dd)
    (hih : ∀ c ∈ cs, ∀ d', deepestEligible elig i c = some d' →
      (labels (attachBelow elig i c) : Multiset ι) = insert i (labels c : Multiset ι)) :
    (labels (mk a (attachInFirst elig i dd cs)) : Multiset ι) =
      insert i (labels (mk a cs) : Multiset ι) := by
  rcases attachInFirst_spec (elig := elig) (i := i) dd cs with
    ⟨cs₁, c, cs₂, hcs, haif, hd, hne⟩ | ⟨haif, hne⟩
  · have hc : c ∈ cs := by simp [hcs, List.mem_append]
    rw [haif, hcs]
    simp [labels, List.flatMap_append, List.flatMap_cons]
    have hperm : List.Perm (labels (attachBelow elig i c)) (i :: labels c) := by
      simpa [Multiset.insert_eq_cons] using (hih c hc (dd - 1) hd)
    refine List.Perm.trans ?_
      (List.perm_middle (a := i) (l₁ := a :: List.flatMap labels cs₁)
        (l₂ := labels c ++ List.flatMap labels cs₂))
    exact List.Perm.cons a
      (List.Perm.append_left (List.flatMap labels cs₁)
        (List.Perm.append_right (List.flatMap labels cs₂) hperm))
  · exfalso
    have hatt := ((foldl_maxOption_eq_some
      (fun c => (deepestEligible elig i c).map (· + 1)) cs dd).mp hfold).1
    rcases hatt with ⟨c', hc', hc''⟩
    rw [Option_map_succ_eq_some] at hc''
    exact hne c' hc' hc''.1

/-- `deepestEligible` returns `none` exactly when no vertex is eligible. -/
theorem deepestEligible_eq_none (τ : WitnessTree ι) :
    deepestEligible elig i τ = none ↔ ∀ p (hp : ValidPath τ p), ¬ elig i (labelAt hp) :=
  (deepestEligible_spec τ).1

/-- `deepestEligible` computes the maximum depth of an eligible vertex. -/
theorem deepestEligible_eq_some (τ : WitnessTree ι) (d : ℕ) :
    deepestEligible elig i τ = some d ↔
      (∃ p, ∃ hp : ValidPath τ p, depth τ p = d ∧ elig i (labelAt hp)) ∧
      ∀ p, ∀ hp : ValidPath τ p, elig i (labelAt hp) → depth τ p ≤ d :=
  (deepestEligible_spec τ).2 d

/-- No eligible vertex: the tree is unchanged. -/
theorem attachBelow_eq_self_of_deepestEligible_none {τ : WitnessTree ι}
    (h : deepestEligible elig i τ = none) : attachBelow elig i τ = τ := by
  cases τ with
  | mk a cs =>
      simp [deepestEligible] at h
      by_cases ha : elig i a
      · simp [ha] at h
      · simp [ha] at h
        simp [attachBelow, ha, h]

/-- The main spec (a): with a deepest eligible vertex at depth `d`, the new leaf `mk i []`
is attached as a child of a depth-`d` eligible vertex. -/
theorem attachBelow_spec {τ : WitnessTree ι} {d : ℕ} (h : deepestEligible elig i τ = some d) :
    ∃ p, ∃ hp : ValidPath (attachBelow elig i τ) p, ∃ k : ℕ,
      ∃ _ : (treeAt hp).childrenOf[k]? = some (mk i []),
        depth (attachBelow elig i τ) p = d ∧ elig i (labelAt hp) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => ∀ d, deepestEligible elig i τ = some d →
        ∃ p, ∃ hp : ValidPath (attachBelow elig i τ) p, ∃ k : ℕ,
          ∃ _ : (treeAt hp).childrenOf[k]? = some (mk i []),
            depth (attachBelow elig i τ) p = d ∧ elig i (labelAt hp))
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ d, deepestEligible elig i c = some d →
        ∃ p, ∃ hp : ValidPath (attachBelow elig i c) p, ∃ k : ℕ,
          ∃ _ : (treeAt hp).childrenOf[k]? = some (mk i []),
            depth (attachBelow elig i c) p = d ∧ elig i (labelAt hp)) ?_ ?_ ?_ τ d h
  · intro a cs ih d hd
    simp [deepestEligible] at hd
    by_cases ha : elig i a
    · cases hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none with
      | none =>
          have hd0 : 0 = d := by simpa [ha, hfold] using hd
          subst d
          refine ⟨[], .root, cs.length, ?_, ?_, ?_⟩
          · simp [attachBelow, hfold, ha, treeAt]
          · simp [depth]
          · simpa [labelAt_nil, labelOf_attachBelow] using ha
      | some dd =>
          have hdd : dd = d := by simpa [ha, hfold] using hd
          rw [show attachBelow elig i (mk a cs) = mk a (attachInFirst elig i dd cs) from by
            simp [attachBelow, hfold]]
          exact attachBelow_spec_attachInFirst (elig := elig) (i := i) (a := a) (cs := cs)
            hfold hdd ih
    · have hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none = some d := by
        simpa [ha] using hd
      rw [show attachBelow elig i (mk a cs) = mk a (attachInFirst elig i d cs) from by
        simp [attachBelow, hfold]]
      exact attachBelow_spec_attachInFirst (elig := elig) (i := i) (a := a) (cs := cs)
        (dd := d) hfold rfl ih
  · intro c hc
    simp at hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- The new vertex has depth `d + 1` and label `i` (c). -/
theorem attachBelow_newVertex {τ : WitnessTree ι} {d : ℕ}
    (h : deepestEligible elig i τ = some d) :
    ∃ p, ∃ hp : ValidPath (attachBelow elig i τ) p, ∃ k : ℕ,
      ∃ _ : (treeAt hp).childrenOf[k]? = some (mk i []),
        ∃ hpk : ValidPath (attachBelow elig i τ) (p ++ [k]),
          depth (attachBelow elig i τ) (p ++ [k]) = d + 1 ∧ labelAt hpk = i := by
  rcases attachBelow_spec (elig := elig) (i := i) (h := h) with ⟨p, hp, k, hk, hdp, helig⟩
  refine ⟨p, hp, k, hk, validPath_append hp hk, ?_, ?_⟩
  · have hplen : p.length = d := by simpa [depth] using hdp
    simp [depth, List.length_append, hplen]
  · simp [labelAt, treeAt_validPath_append hp hk, labelOf_mk]

/-- Old vertices keep their labels: every old path stays valid, addressing the same label.
Depths are definitionally the path length, hence automatically unchanged (b). -/
theorem labelAt_attachBelow {τ : WitnessTree ι} {p : List ℕ} (hp : ValidPath τ p) :
    ∃ hp' : ValidPath (attachBelow elig i τ) p, labelAt hp' = labelAt hp := by
  refine ValidPath.rec (motive := fun {τ : WitnessTree ι} {p : List ℕ} (_hp : ValidPath τ p) =>
      ∃ hp' : ValidPath (attachBelow elig i τ) p, labelAt hp' = labelAt _hp) ?_ ?_ hp
  · intro τ
    exact ⟨.root, by simp [labelAt_nil, labelOf_attachBelow]⟩
  · intro τ p j c hc hvp ih
    cases τ with
    | mk a cs =>
        cases hfold : cs.foldl (fun m c =>
            maxOption m ((deepestEligible elig i c).map (· + 1))) none with
        | none =>
            by_cases ha : elig i a
            · have hj : j < cs.length := by
                exact (List.getElem?_eq_some_iff.mp hc).1
              have hc' : (cs ++ [mk i []])[j]? = some c := by
                simpa using (List.getElem?_append_left (l₁ := cs) (l₂ := [mk i []])
                  (i := j) hj).trans hc
              refine ⟨.cons j c ?_ hvp, ?_⟩
              · simpa [attachBelow, hfold, ha] using hc'
              · simp [labelAt_cons]
            · refine ⟨.cons j c (by simpa [attachBelow, hfold, ha] using hc) hvp,
                by simp [labelAt_cons]⟩
        | some dd =>
            rcases attachInFirst_childrenOf_eq (elig := elig) (i := i) (h := hc) with hc' | hc'
            · refine ⟨.cons j c (by simpa [attachBelow, hfold] using hc') hvp,
                by simp [labelAt_cons]⟩
            · rcases ih with ⟨hvp', hl⟩
              refine ⟨.cons j (attachBelow elig i c)
                (by simpa [attachBelow, hfold] using hc') hvp',
                by simpa [labelAt_cons] using hl⟩

/-- The attachment is a single new leaf: the size grows by at most one. -/
theorem size_attachBelow (τ : WitnessTree ι) : size (attachBelow elig i τ) ≤ size τ + 1 := by
  refine WitnessTree.rec (motive_1 := fun τ => size (attachBelow elig i τ) ≤ size τ + 1)
      (motive_2 := fun cs => ∀ c ∈ cs, size (attachBelow elig i c) ≤ size c + 1) ?_ ?_ ?_ τ
  · intro a cs ih
    cases hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none with
    | none =>
        by_cases ha : elig i a
        · simp [attachBelow, hfold, ha, List.map_append, List.sum_append]
          omega
        · simp [attachBelow, hfold, ha]
    | some dd =>
        simpa [attachBelow, hfold] using size_attachInFirst (elig := elig) (i := i) (a := a) ih
  · intro c hc
    simp at hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- The attachment is a single new leaf: the label multiset gains exactly `i`. -/
theorem labels_attachBelow {τ : WitnessTree ι} {d : ℕ}
    (h : deepestEligible elig i τ = some d) :
    (labels (attachBelow elig i τ) : Multiset ι) = insert i (labels τ : Multiset ι) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => ∀ d, deepestEligible elig i τ = some d →
        (labels (attachBelow elig i τ) : Multiset ι) = insert i (labels τ : Multiset ι))
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ d, deepestEligible elig i c = some d →
        (labels (attachBelow elig i c) : Multiset ι) =
          insert i (labels c : Multiset ι)) ?_ ?_ ?_ τ d h
  · intro a cs ih d hd
    simp [deepestEligible] at hd
    by_cases ha : elig i a
    · cases hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none with
      | none =>
          simp [attachBelow, hfold, ha, labels, List.flatMap_append, List.flatMap_cons]
          refine List.Perm.trans
            (List.Perm.cons a (List.perm_append_singleton i (List.flatMap labels cs)))
            (List.Perm.swap i a (List.flatMap labels cs))
      | some dd =>
          rw [show attachBelow elig i (mk a cs) = mk a (attachInFirst elig i dd cs) from by
            simp [attachBelow, hfold]]
          exact labels_attachInFirst (elig := elig) (i := i) (a := a) (cs := cs) (dd := dd) hfold ih
    · have hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none = some d := by
        simpa [ha] using hd
      rw [show attachBelow elig i (mk a cs) = mk a (attachInFirst elig i d cs) from by
        simp [attachBelow, hfold]]
      exact labels_attachInFirst (elig := elig) (i := i) (a := a) (cs := cs) (dd := d) hfold ih
  · intro c hc
    simp at hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- Properness is preserved, provided `i` is eligible for itself (as in the fold's
eligibility relation) (d). -/
theorem attachBelow_proper {τ : WitnessTree ι} (hii : elig i i) (hτ : Proper τ) :
    Proper (attachBelow elig i τ) := by
  refine WitnessTree.rec (motive_1 := fun τ => Proper τ → Proper (attachBelow elig i τ))
      (motive_2 := fun cs => ∀ c ∈ cs, Proper c → Proper (attachBelow elig i c))
        ?_ ?_ ?_ τ hτ
  · intro a cs ih hτ
    cases hfold : cs.foldl (fun m c =>
        maxOption m ((deepestEligible elig i c).map (· + 1))) none with
    | none =>
        by_cases ha : elig i a
        · have hnodup : (cs.map labelOf).Nodup := ((proper_mk a cs).mp hτ).1
          have hproper : ∀ c ∈ cs, Proper c := ((proper_mk a cs).mp hτ).2
          have hdisj : List.Disjoint (cs.map labelOf) [i] := by
            rw [List.disjoint_left]
            intro x hx1
            rw [List.mem_map] at hx1
            rcases hx1 with ⟨c, hc, rfl⟩
            rw [List.mem_singleton]
            intro hci
            have hde : deepestEligible elig i c = none := by
              have hf := (foldl_maxOption_eq_none
                (fun c => (deepestEligible elig i c).map (· + 1)) cs).mp hfold
              exact Option.map_eq_none_iff.mp (hf c hc)
            exact (deepestEligible_eq_none (τ := c)).mp hde [] .root
              (by simpa [labelAt_nil, hci] using hii)
          have hnodup' : (cs.map labelOf ++ [i]).Nodup :=
            List.Nodup.append hnodup (by simp) hdisj
          have hproper' : ∀ c' ∈ cs ++ [mk i []], Proper c' := by
            intro c' hc'
            rw [List.mem_append] at hc'
            rcases hc' with hc' | hc'
            · exact hproper c' hc'
            · rw [List.mem_singleton] at hc'
              subst c'
              simp
          simpa [attachBelow, hfold, ha] using
            ((proper_mk a (cs ++ [mk i []])).mpr
              ⟨by simpa [List.map_append, labelOf_mk] using hnodup', hproper'⟩)
        · simpa [attachBelow, hfold, ha] using hτ
    | some dd =>
        have hmap : (attachInFirst elig i dd cs).map labelOf = cs.map labelOf :=
          attachInFirst_map_labelOf (elig := elig) (i := i) (dd := dd) cs
        have hnodup' : ((attachInFirst elig i dd cs).map labelOf).Nodup := by
          simpa [hmap] using ((proper_mk a cs).mp hτ).1
        have hproper' : ∀ c' ∈ attachInFirst elig i dd cs, Proper c' := by
          intro c' hc'
          rcases attachInFirst_spec (elig := elig) (i := i) dd cs with
            ⟨cs₁, c₂, cs₂, hcs, haif, hd, hne⟩ | ⟨haif, hne⟩
          · rw [haif, List.mem_append] at hc'
            rcases hc' with hc' | hc'
            · have hc'cs : c' ∈ cs := by simpa [hcs, List.mem_append] using Or.inl hc'
              exact ((proper_mk a cs).mp hτ).2 c' hc'cs
            · rw [List.mem_cons] at hc'
              rcases hc' with rfl | hc'
              · have hc₂cs : c₂ ∈ cs := by
                  simp [hcs, List.mem_append]
                exact ih c₂ hc₂cs (((proper_mk a cs).mp hτ).2 c₂ hc₂cs)
              · have hc'cs : c' ∈ cs := by
                  simpa [hcs, List.mem_append] using Or.inr (Or.inr hc')
                exact ((proper_mk a cs).mp hτ).2 c' hc'cs
          · rw [haif] at hc'
            exact ((proper_mk a cs).mp hτ).2 c' hc'
        simpa [attachBelow, hfold] using
          ((proper_mk a (attachInFirst elig i dd cs)).mpr ⟨hnodup', hproper'⟩)
  · intro c hc
    simp at hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

end AttachSpec

end WitnessTree

/-! ## The witness-tree construction (30.3): treeElig / treeAt / forgetTime / T -/

section TreeAt

variable {ι : Type u}
variable {κ : Type u} [DecidableEq κ]
variable {Ω : κ → Type v}
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-- Eligibility of a new time-labeled entry `p = (s, i)` for attachment below a vertex
labeled `q = (s', i')`: same event, or overlapping variable sets (the time-labeled lift of
Γ⁺-membership; the notes' §9 insertion rule). An `abbrev` so that typeclass synthesis can
unfold it to synthesize `Decidable (treeElig vbl a b)` from `[DecidableEq ι]`
(`instDecidableEq` on `p.2 = q.2`) and `[DecidableEq κ]` (the `∩`; `Finset.decidableNonempty`
is unconditional). -/
abbrev treeElig (vbl : ι → Finset κ) (p q : ℕ × ι) : Prop :=
  p.2 = q.2 ∨ (vbl p.2 ∩ vbl q.2).Nonempty

/-- The witness tree built from the log prefix `0..t`: the root is the entry at time `t`
(a dummy label when `Λ t = none` — the tree is only consumed at genuine times, 30.6/40.3
all carry `t < R`), and the earlier entries `t-1, …, 0` are scanned in reverse; `none`
entries create no vertex, each `some i` attaches a new leaf `(s, i)` below a deepest
eligible vertex (30.2's `attachBelow`). The reverse scan is a `foldr` over `List.range t`
(`range t = [0, …, t-1]`, so `foldr` processes `t-1` first — no explicit `.reverse`;
the prototype's `(range t).reverse.foldl` form is definitionally rewritten to exactly this
`foldr` by `simp` via `List.foldl_reverse`, so the fold lemmas are `foldr`-shaped anyway).
Computable: the dummy needs only the explicit `[Inhabited ι]`. -/
def treeAt [DecidableEq ι] [Inhabited ι] (vbl : ι → Finset κ) (Λ : ℕ → Option ι)
    (t : ℕ) : WitnessTree (ℕ × ι) :=
  (List.range t).foldr
    (fun s τ => match Λ s with
      | none => τ
      | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ)
    (match Λ t with
      | none => WitnessTree.mk (t, default) []
      | some i => WitnessTree.mk (t, i) [])

/-- Drop the time component of the labels (shape-preserving). -/
def forgetTime : WitnessTree (ℕ × ι) → WitnessTree ι
  | WitnessTree.mk p cs => WitnessTree.mk p.2 (cs.map forgetTime)

/-- The witness tree at time `t` of the execution table `ω`: the occurring tree of the
padded log. `noncomputable` because `log` is. -/
noncomputable def T [DecidableEq ι] [Inhabited ι] (ω : ΩN N Ω) (t : ℕ) : WitnessTree ι :=
  forgetTime (treeAt vbl (log vbl A pick hpick ω) t)

/-! ## forgetTime round-trips -/

/-- `forgetTime` projects the root label. -/
theorem labelOf_forgetTime (τ : WitnessTree (ℕ × ι)) :
    WitnessTree.labelOf (forgetTime τ) = (WitnessTree.labelOf τ).2 := by
  cases τ with
  | mk p cs => simp [forgetTime]

/-- `forgetTime` maps the children pointwise. -/
theorem childrenOf_forgetTime (τ : WitnessTree (ℕ × ι)) :
    WitnessTree.childrenOf (forgetTime τ) = (WitnessTree.childrenOf τ).map forgetTime := by
  cases τ with
  | mk p cs => simp [forgetTime]

/-- `forgetTime` preserves the size. (`induction` rejects the nested inductive, so the
proof goes through the generated recursor `WitnessTree.rec` with the list motive
`∀ c ∈ cs, …`; the pointwise step is `List.map_congr_left`.) -/
theorem size_forgetTime (τ : WitnessTree (ℕ × ι)) :
    WitnessTree.size (forgetTime τ) = WitnessTree.size τ := by
  refine WitnessTree.rec
    (motive_1 := fun τ => WitnessTree.size (forgetTime τ) = WitnessTree.size τ)
    (motive_2 := fun cs => ∀ c ∈ cs, WitnessTree.size (forgetTime c) = WitnessTree.size c)
    (fun p cs ih => ?_) (by intro c hc; cases hc) (fun c cs ihc ihcs => ?_) τ
  · simp [forgetTime]
    exact congrArg List.sum (List.map_congr_left (fun c hc => ih c hc))
  · intro c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with hEq | hIn
    · subst c'
      exact ihc
    · exact ihcs c' hIn

/-- The child-membership bridge through `forgetTime` (a theorem, not a `def`: it is a
proposition, and as a named declaration its application inside `validPath_forgetTime`
carries no embedded proof for the equation lemmas to rebuild). -/
theorem forgetTime_getElem? {τ : WitnessTree (ℕ × ι)} {i : ℕ} {c : WitnessTree (ℕ × ι)}
    (hc : τ.childrenOf[i]? = some c) : (forgetTime τ).childrenOf[i]? = some (forgetTime c) := by
  rw [childrenOf_forgetTime, List.getElem?_map, hc]
  rfl

/-- A valid path in the time-labeled tree stays valid in its `forgetTime` image (the
children list only gets mapped, so the same child indices address the corresponding
vertices). Data-valued, like `ValidPath`; match the PATH first, then the proof (30.1's
pattern) so the equation lemmas are clean. -/
def validPath_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
    (hp : WitnessTree.ValidPath τ p) :
    WitnessTree.ValidPath (forgetTime τ) p :=
  match p with
  | [] => .root
  | i :: _ =>
      match hp with
      | .cons i c hc hvp =>
          .cons i (forgetTime c) (forgetTime_getElem? hc) (validPath_forgetTime hvp)

/-- The subtree at a transported path is the transported subtree. -/
theorem treeAt_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
    (hp : WitnessTree.ValidPath τ p) :
    WitnessTree.treeAt (validPath_forgetTime hp) = forgetTime (WitnessTree.treeAt hp) := by
  induction p generalizing τ with
  | nil =>
      cases hp with
      | root => rfl
  | cons i p' ih =>
      cases hp with
      | cons i c hc hvp =>
          rw [validPath_forgetTime, WitnessTree.treeAt_cons, ih, WitnessTree.treeAt_cons]

/-- The label at a transported path is the projection of the original label. -/
theorem labelAt_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
    (hp : WitnessTree.ValidPath τ p) :
    WitnessTree.labelAt (validPath_forgetTime hp) = (WitnessTree.labelAt hp).2 := by
  unfold WitnessTree.labelAt
  rw [treeAt_forgetTime, labelOf_forgetTime]

/-! ## Root-label lemmas (30.6's injectivity inputs) -/

/-- `attachBelow` preserves the root label (private; derived from 30.2's integrated public
spec (b) `labelAt_attachBelow` at the root path — the scratch's self-contained `cases`
proof named 30.2's private `maxOption`, file-scoped and inaccessible from this block). -/
private theorem labelOf_attachBelow [DecidableEq ι] (p : ℕ × ι)
    (τ : WitnessTree (ℕ × ι)) :
    WitnessTree.labelOf (WitnessTree.attachBelow (treeElig vbl) p τ) =
      WitnessTree.labelOf τ := by
  rcases WitnessTree.labelAt_attachBelow (elig := treeElig vbl) (i := p) (τ := τ) (p := [])
    (hp := .root) with ⟨_hp', h⟩
  simpa using h

/-- The reverse-scan fold preserves the root label (the seed is generalized so the
induction hypothesis applies after one `foldr` step). -/
private theorem labelOf_foldr_treeAt [DecidableEq ι] (Λ : ℕ → Option ι) (l : List ℕ) :
    ∀ τ : WitnessTree (ℕ × ι),
      WitnessTree.labelOf (l.foldr (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) τ) =
          WitnessTree.labelOf τ := by
  induction l with
  | nil => intro τ; rfl
  | cons s l ih =>
      intro τ
      rw [List.foldr_cons]
      cases Λ s
      case none => simp [ih]
      case some i => simp [ih, labelOf_attachBelow vbl]

/-- The root of `treeAt` is the entry at time `t` (when genuine). -/
theorem treeAt_root_label [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ}
    {i : ι} (h : Λ t = some i) :
    WitnessTree.labelOf (treeAt vbl Λ t) = (t, i) := by
  simp [treeAt, h, labelOf_foldr_treeAt]

/-- The root label of the occurring tree `T ω t` is the event resampled at time `t`. -/
theorem T_root_label [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ} {i : ι}
    (h : log vbl A pick hpick ω t = some i) :
    WitnessTree.labelOf (T vbl A pick hpick ω t) = i := by
  unfold T
  rw [labelOf_forgetTime, treeAt_root_label vbl h]

/-! ## Properness of the construction (30.4): Prop 10.1 -/

/-- Definitional copy of 30.2's `maxOption` (namespace-private: invisible outside
`namespace WitnessTree` even in this file), so the fold terms inside the
`deepestEligible`/`attachBelow` equation lemmas are definitionally equal to the folds
built with this copy. -/
private def mtMaxOption (m o : Option ℕ) : Option ℕ :=
  match m, o with
  | none, o => o
  | m, none => m
  | some a, some b => some (max a b)

/-- The `attachBelow` equation, re-expressed with the local `mtMaxOption` (definitionally
equal to 30.2's private `maxOption`, so `rfl` closes it after the equation-lemma rewrite). -/
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

/-- Unpack `Proper (forgetTime (mk a cs))` into the child-label Nodup and the
per-child properness of the `forgetTime` images. -/
private lemma proper_mk_forgetTime_split {a : ℕ × ι} {cs : List (WitnessTree (ℕ × ι))}
    (hτ : WitnessTree.Proper (forgetTime (WitnessTree.mk a cs))) :
    ((cs.map forgetTime).map WitnessTree.labelOf).Nodup ∧
      (∀ d ∈ cs, WitnessTree.Proper (forgetTime d)) := by
  have h := (WitnessTree.proper_mk a.2 (cs.map forgetTime)).mp (by simpa [forgetTime] using hτ)
  exact ⟨h.1, fun d hd => h.2 (forgetTime d) (by rw [List.mem_map]; exact ⟨d, hd, rfl⟩)⟩

/-- The abstract child-label list is unchanged under the `attachInFirst` step. -/
private lemma forgetTime_attachInFirst_map_labelOf [DecidableEq ι] {s : ℕ} {i : ι}
    {dd : ℕ} (cs : List (WitnessTree (ℕ × ι))) :
    ((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime).map
        WitnessTree.labelOf = (cs.map forgetTime).map WitnessTree.labelOf := by
  induction cs with
  | nil => simp [WitnessTree.attachInFirst]
  | cons c cs ih =>
      by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s, i) c = some (dd - 1)
      · simp [WitnessTree.attachInFirst, hd, labelOf_forgetTime, labelOf_attachBelow]
      · simp [WitnessTree.attachInFirst, hd, ih, labelOf_forgetTime]

/-- Recursive properness of the `attachInFirst` step at the abstract level: the kept
children are proper by hypothesis, the replaced child by the induction hypothesis. -/
private lemma forgetTime_attachInFirst_proper [DecidableEq ι] {s : ℕ} {i : ι}
    {dd : ℕ} (cs : List (WitnessTree (ℕ × ι)))
    (hih : ∀ c ∈ cs, WitnessTree.Proper (forgetTime c) →
      WitnessTree.Proper (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c)))
    (hproper : ∀ c ∈ cs, WitnessTree.Proper (forgetTime c)) :
    ∀ c' ∈ (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime,
      WitnessTree.Proper c' := by
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
          exact hih c (by simp) (hproper c (by simp))
        · exact hproper d (by simp [hdmem])
      · simp only [WitnessTree.attachInFirst, hd, if_false]
        intro c' hc'
        rw [List.mem_map] at hc'; rcases hc' with ⟨d, hdmem, rfl⟩
        rw [List.mem_cons] at hdmem
        rcases hdmem with hEq | hdmem
        · subst d
          exact hproper c (by simp)
        · exact ih (fun c₀ hc₀ => hih c₀ (by simp [hc₀]))
            (fun c₀ hc₀ => hproper c₀ (by simp [hc₀])) (forgetTime d)
            (by rw [List.mem_map]; exact ⟨d, hdmem, rfl⟩)

/-- One insertion step preserves abstract properness: if the `forgetTime`-image of `τ`
is proper, so is that of `attachBelow (treeElig vbl) (s, i) τ`. This is where the notes'
self-loop argument (Prop 10.1) lives. -/
private theorem forgetTime_attachBelow_proper [DecidableEq ι] {s : ℕ} {i : ι}
    (τ : WitnessTree (ℕ × ι)) (hτ : WitnessTree.Proper (forgetTime τ)) :
    WitnessTree.Proper (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) τ)) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => WitnessTree.Proper (forgetTime τ) →
        WitnessTree.Proper (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) τ)))
      (motive_2 := fun cs => ∀ c ∈ cs, WitnessTree.Proper (forgetTime c) →
        WitnessTree.Proper (forgetTime (WitnessTree.attachBelow (treeElig vbl) (s, i) c)))
      ?_ ?_ ?_ τ hτ
  · intro a cs ih hτ
    cases hd : cs.foldl (fun m c => mtMaxOption m
        ((WitnessTree.deepestEligible (treeElig vbl) (s, i) c).map (· + 1))) none with
    | none =>
        by_cases ha : treeElig vbl (s, i) a
        · rcases proper_mk_forgetTime_split hτ with ⟨hnodup, hproper⟩
          have hdisj : List.Disjoint ((cs.map forgetTime).map WitnessTree.labelOf) [i] := by
            rw [List.disjoint_left]; intro x hx1 hx2
            rw [List.mem_singleton] at hx2; subst x
            rw [List.mem_map] at hx1; rcases hx1 with ⟨c, hc, hcl⟩
            rw [List.mem_map] at hc; rcases hc with ⟨c₀, hc₀, rfl⟩
            have hc₀i : (WitnessTree.labelOf c₀).2 = i := by
              simpa [labelOf_forgetTime] using hcl
            rcases (List.mem_iff_getElem?).mp hc₀ with ⟨j, hj⟩
            have helig : treeElig vbl (s, i) (WitnessTree.labelOf c₀) :=
              Or.inl (by simpa using hc₀i.symm)
            have hSome :
                WitnessTree.deepestEligible (treeElig vbl) (s, i)
                  (WitnessTree.mk a cs) = some 0 := by
              rw [deepestEligible_mk_treeElig vbl a cs]; simp [hd, ha]
            have hle : WitnessTree.depth (WitnessTree.mk a cs) [j] ≤ 0 :=
              ((WitnessTree.deepestEligible_eq_some (elig := treeElig vbl) (i := (s, i))
                (τ := WitnessTree.mk a cs) (d := 0)).mp hSome).2 [j]
                (.cons j c₀ (by simpa using hj) WitnessTree.ValidPath.root)
                (by simpa [WitnessTree.labelAt_cons] using helig)
            simp [WitnessTree.depth] at hle
          have hnodup' : (((cs ++ [WitnessTree.mk (s, i) []]).map forgetTime).map
              WitnessTree.labelOf).Nodup := by
            simpa [forgetTime] using (List.Nodup.append hnodup (List.nodup_singleton i) hdisj)
          have hproper' :
              ∀ c' ∈ (cs ++ [WitnessTree.mk (s, i) []]).map forgetTime,
                WitnessTree.Proper c' := by
            intro c' hc'
            rw [List.mem_map] at hc'; rcases hc' with ⟨d, hdmem, rfl⟩
            rw [List.mem_append] at hdmem; rcases hdmem with hdmem | hdmem
            · exact hproper d hdmem
            · rw [List.mem_singleton] at hdmem; subst d; simp [forgetTime]
          simpa [attachBelow_mk_treeElig vbl a cs, hd, ha, forgetTime] using
            (WitnessTree.proper_mk a.2
              ((cs ++ [WitnessTree.mk (s, i) []]).map forgetTime)).mpr ⟨hnodup', hproper'⟩
        · simpa [attachBelow_mk_treeElig vbl a cs, hd, ha] using hτ
    | some dd =>
        rcases proper_mk_forgetTime_split hτ with ⟨hnodup, hproper⟩
        have hmap : ((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime).map
            WitnessTree.labelOf = (cs.map forgetTime).map WitnessTree.labelOf :=
          forgetTime_attachInFirst_map_labelOf vbl cs
        have hnodup' : (((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime).map
            WitnessTree.labelOf).Nodup := by simpa [hmap] using hnodup
        have hproper' :
            ∀ c' ∈ (WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime,
              WitnessTree.Proper c' := forgetTime_attachInFirst_proper vbl cs ih hproper
        simpa [attachBelow_mk_treeElig vbl a cs, hd, forgetTime] using
          (WitnessTree.proper_mk a.2
            ((WitnessTree.attachInFirst (treeElig vbl) (s, i) dd cs).map forgetTime)).mpr
            ⟨hnodup', hproper'⟩
  · intro c hc; cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc' <;> [exact ihc; exact ihcs c' hc']

/-- The reverse-scan fold preserves abstract properness (list induction on the fold's
range list, with the accumulated tree generalized). -/
private theorem foldr_forgetTime_proper [DecidableEq ι] {Λ : ℕ → Option ι} :
    ∀ l : List ℕ, ∀ τ : WitnessTree (ℕ × ι), WitnessTree.Proper (forgetTime τ) →
      WitnessTree.Proper (forgetTime (l.foldr
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
      | some i => apply forgetTime_attachBelow_proper vbl; exact ih τ hτ

/-- Pair-level mirror of `foldr_forgetTime_proper` for the `treeAt_pair_proper` bonus
(the `some i` step is 30.2's `attachBelow_proper` with `hii := Or.inl rfl`). -/
private theorem foldr_pair_proper [DecidableEq ι] {Λ : ℕ → Option ι} :
    ∀ l : List ℕ, ∀ τ : WitnessTree (ℕ × ι), WitnessTree.Proper τ →
      WitnessTree.Proper (l.foldr
        (fun s τ => match Λ s with
          | none => τ
          | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) τ) := by
  intro l
  induction l with
  | nil => intro τ hτ; simpa using hτ
  | cons s l ih =>
      intro τ hτ
      rw [List.foldr_cons]
      cases h : Λ s with
      | none => simpa using ih τ hτ
      | some i =>
          exact WitnessTree.attachBelow_proper (elig := treeElig vbl) (i := (s, i))
            (hii := Or.inl rfl) (ih τ hτ)

/-- **Prop 10.1** (abstract tree): the witness tree built from the log prefix is
proper — for genuine `t` (where `Λ t = some _`) this is the occurring tree `T … ω t`,
the form 30.7/60.1 consume. -/
theorem treeAt_proper [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
    WitnessTree.Proper (forgetTime (treeAt vbl Λ t)) := by
  unfold treeAt
  apply foldr_forgetTime_proper
  cases h : Λ t <;> simp [forgetTime]

/-- Bonus (not consumed by 30.5/30.6): the time-labeled tree is proper. Trivial at the
pair level — each reverse-scan step creates at most one vertex with a fresh time, so
sibling pair-labels never repeat. -/
theorem treeAt_pair_proper [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
    WitnessTree.Proper (treeAt vbl Λ t) := by
  unfold treeAt
  apply foldr_pair_proper
  cases h : Λ t <;> simp

end TreeAt

/-! ## Prop 12.1: occurring-tree injectivity (30.6, A-count argument) -/

section TreeAtInjective

variable {ι : Type u}
variable {κ : Type u} [DecidableEq κ]
variable {Ω : κ → Type v}
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-! ### Private glue -/

/-- The reverse-scan fold of `treeAt` with the seed generalized (defeq to `treeAt`'s fold
term). -/
private def buildBelow [DecidableEq ι] (Λ : ℕ → Option ι) (l : List ℕ)
    (σ : WitnessTree (ℕ × ι)) : WitnessTree (ℕ × ι) :=
  l.foldr (fun s τ => match Λ s with
    | none => τ
    | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) σ

/- (The root-label glue reuses the TreeAt section's private `labelOf_attachBelow` and
`labelOf_foldr_treeAt` — same namespace, same statements; Lean rejects redeclaring a
private name in the same namespace.) -/

/-- The root label of `treeAt`, including the dummy case (the generalization of 30.3's
`treeAt_root_label` needed by the unconditional time-labeled injectivity). Note: the seed
`match` must be reduced by `change` first — `rw`/`simp` cannot match the fold lemma through
the unreduced seed match. -/
private theorem treeAt_root_label' [DecidableEq ι] [Inhabited ι] (Λ : ℕ → Option ι)
    (t : ℕ) :
    WitnessTree.labelOf (treeAt vbl Λ t) = (t, (Λ t).getD default) := by
  cases hΛt : Λ t with
  | none =>
      rw [treeAt, hΛt]
      change WitnessTree.labelOf ((List.range t).foldr
        (fun s τ => match Λ s with
          | none => τ
          | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ)
        (WitnessTree.mk (t, default) [])) = (t, default)
      rw [labelOf_foldr_treeAt vbl]
      rfl
  | some i =>
      rw [treeAt, hΛt]
      change WitnessTree.labelOf ((List.range t).foldr
        (fun s τ => match Λ s with
          | none => τ
          | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ)
        (WitnessTree.mk (t, i) [])) = (t, i)
      rw [labelOf_foldr_treeAt vbl]
      rfl

/-- The List→Multiset coercion commutes with `map` (no `Multiset.coe_map` in mathlib). -/
private theorem coe_map_multiset {α β : Type u} (f : α → β) (l : List α) :
    (l.map f : Multiset β) = (l : Multiset α).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

/-- `forgetTime` maps the preorder labels pointwise (projection of the label pairs). -/
private theorem labels_forgetTime (τ : WitnessTree (ℕ × ι)) :
    WitnessTree.labels (forgetTime τ) = (WitnessTree.labels τ).map (fun p => p.2) := by
  refine WitnessTree.rec
    (motive_1 := fun τ => WitnessTree.labels (forgetTime τ) =
      (WitnessTree.labels τ).map (fun p => p.2))
    (motive_2 := fun cs => ∀ c ∈ cs, WitnessTree.labels (forgetTime c) =
      (WitnessTree.labels c).map (fun p => p.2))
    (fun p cs ih => ?_) (by intro c hc; cases hc) (fun c cs ihc ihcs => ?_) τ
  · simp [forgetTime, WitnessTree.labels]
    rw [List.flatMap_map, List.map_flatMap]
    apply List.flatMap_congr
    intro c hc
    exact ih c hc
  · intro c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with hEq | hIn
    · subst c'
      exact ihc
    · exact ihcs c' hIn

/-- Multiset form of `labels_forgetTime` (the fold invariant uses the Multiset count). -/
private theorem labels_forgetTime_multiset (τ : WitnessTree (ℕ × ι)) :
    (WitnessTree.labels (forgetTime τ) : Multiset ι) =
      (WitnessTree.labels τ : Multiset (ℕ × ι)).map (fun p => p.2) := by
  rw [← coe_map_multiset (fun p : ℕ × ι => p.2) (WitnessTree.labels τ)]
  exact congrArg (fun l : List ι => (l : Multiset ι)) (labels_forgetTime τ)

/-- One insertion of an `a`-entry: attaches (the seed's `a`-vertex stays eligible via
`treeElig`'s equality disjunct), adds exactly one `a`-labeled vertex, keeps an `a`-vertex. -/
private theorem step_count_of_eq [DecidableEq ι] {a : ι} {u : ℕ}
    (τ : WitnessTree (ℕ × ι))
    (hA : ∃ p, ∃ hp : WitnessTree.ValidPath τ p, (WitnessTree.labelAt hp).2 = a) :
    (∃ p, ∃ hp : WitnessTree.ValidPath (WitnessTree.attachBelow (treeElig vbl) (u, a) τ) p,
      (WitnessTree.labelAt hp).2 = a) ∧
    (WitnessTree.labels (forgetTime (WitnessTree.attachBelow (treeElig vbl) (u, a) τ)) :
        Multiset ι).count a =
      (WitnessTree.labels (forgetTime τ) : Multiset ι).count a + 1 := by
  constructor
  · rcases hA with ⟨p, hp, hlab⟩
    rcases WitnessTree.labelAt_attachBelow (elig := treeElig vbl) (i := (u, a))
      (τ := τ) (p := p) hp with ⟨hp', hlab'⟩
    exact ⟨p, hp', by simpa [hlab'] using hlab⟩
  · rcases hA with ⟨p, hp, hlab⟩
    have hdne : WitnessTree.deepestEligible (treeElig vbl) (u, a) τ ≠ none := by
      intro hd
      rw [WitnessTree.deepestEligible_eq_none] at hd
      exact hd p hp (Or.inl (by simpa using hlab.symm))
    rcases Option.ne_none_iff_exists.mp hdne with ⟨d, hd⟩
    have hlab' : (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (u, a) τ) :
        Multiset (ℕ × ι)) = insert (u, a) (WitnessTree.labels τ : Multiset (ℕ × ι)) := by
      exact WitnessTree.labels_attachBelow (elig := treeElig vbl) (i := (u, a))
        (τ := τ) (d := d) hd.symm
    calc
      (WitnessTree.labels (forgetTime (WitnessTree.attachBelow (treeElig vbl) (u, a) τ)) :
          Multiset ι).count a =
          ((WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (u, a) τ) :
              Multiset (ℕ × ι)).map (fun p => p.2)).count a := by
            rw [labels_forgetTime_multiset]
      _ = ((insert (u, a) (WitnessTree.labels τ : Multiset (ℕ × ι))).map
          (fun p => p.2)).count a := by
            rw [hlab']
      _ = (Multiset.cons a ((WitnessTree.labels τ : Multiset (ℕ × ι)).map
          (fun p => p.2))).count a := by
            rw [Multiset.insert_eq_cons, Multiset.map_cons]
      _ = ((WitnessTree.labels τ : Multiset (ℕ × ι)).map (fun p => p.2)).count a + 1 := by
            rw [Multiset.count_cons_self]
      _ = (WitnessTree.labels (forgetTime τ) : Multiset ι).count a + 1 := by
            rw [← labels_forgetTime_multiset]

/-- One insertion of a non-`a` entry does not change the `a`-count (and keeps an
`a`-vertex), whether or not it attaches. -/
private theorem step_count_of_ne [DecidableEq ι] {a : ι} {u : ℕ} {i : ι}
    (hi : i ≠ a) (τ : WitnessTree (ℕ × ι))
    (hA : ∃ p, ∃ hp : WitnessTree.ValidPath τ p, (WitnessTree.labelAt hp).2 = a) :
    (∃ p, ∃ hp : WitnessTree.ValidPath (WitnessTree.attachBelow (treeElig vbl) (u, i) τ) p,
      (WitnessTree.labelAt hp).2 = a) ∧
    (WitnessTree.labels (forgetTime (WitnessTree.attachBelow (treeElig vbl) (u, i) τ)) :
        Multiset ι).count a =
      (WitnessTree.labels (forgetTime τ) : Multiset ι).count a := by
  constructor
  · rcases hA with ⟨p, hp, hlab⟩
    rcases WitnessTree.labelAt_attachBelow (elig := treeElig vbl) (i := (u, i))
      (τ := τ) (p := p) hp with ⟨hp', hlab'⟩
    exact ⟨p, hp', by simpa [hlab'] using hlab⟩
  · by_cases hdne : WitnessTree.deepestEligible (treeElig vbl) (u, i) τ = none
    · rw [WitnessTree.attachBelow_eq_self_of_deepestEligible_none
        (elig := treeElig vbl) (i := (u, i)) (τ := τ) hdne]
    · rcases Option.ne_none_iff_exists.mp hdne with ⟨d, hd⟩
      have hlab' : (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (u, i) τ) :
          Multiset (ℕ × ι)) = insert (u, i) (WitnessTree.labels τ : Multiset (ℕ × ι)) := by
        exact WitnessTree.labels_attachBelow (elig := treeElig vbl) (i := (u, i))
          (τ := τ) (d := d) hd.symm
      calc
        (WitnessTree.labels (forgetTime (WitnessTree.attachBelow (treeElig vbl) (u, i) τ)) :
            Multiset ι).count a =
            ((WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (u, i) τ) :
                Multiset (ℕ × ι)).map (fun p => p.2)).count a := by
              rw [labels_forgetTime_multiset]
        _ = ((insert (u, i) (WitnessTree.labels τ : Multiset (ℕ × ι))).map
            (fun p => p.2)).count a := by
              rw [hlab']
        _ = (Multiset.cons i ((WitnessTree.labels τ : Multiset (ℕ × ι)).map
            (fun p => p.2))).count a := by
              rw [Multiset.insert_eq_cons, Multiset.map_cons]
        _ = ((WitnessTree.labels τ : Multiset (ℕ × ι)).map (fun p => p.2)).count a := by
              rw [Multiset.count_cons_of_ne (Ne.symm hi)]
        _ = (WitnessTree.labels (forgetTime τ) : Multiset ι).count a := by
              rw [← labels_forgetTime_multiset]

/-- The fold invariant: each genuine `a`-entry processed adds exactly one `a`-labeled
vertex, so the final `a`-count is the seed count plus the number of `a`-entries in the
list; an `a`-vertex always exists once the seed has one. -/
private theorem foldr_count_label [DecidableEq ι] {Λ : ℕ → Option ι} {a : ι} (l : List ℕ)
    (σ : WitnessTree (ℕ × ι)) :
    (∃ p, ∃ hp : WitnessTree.ValidPath σ p, (WitnessTree.labelAt hp).2 = a) →
      (∃ p, ∃ hp : WitnessTree.ValidPath (buildBelow vbl Λ l σ) p,
        (WitnessTree.labelAt hp).2 = a) ∧
      (WitnessTree.labels (forgetTime (buildBelow vbl Λ l σ)) : Multiset ι).count a =
        (WitnessTree.labels (forgetTime σ) : Multiset ι).count a +
          (l.filter (fun u => Λ u = some a)).length := by
  intro hA
  induction l generalizing σ with
  | nil =>
      constructor
      · simpa [buildBelow] using hA
      · simp [buildBelow]
  | cons u l ih =>
      rw [buildBelow, List.foldr_cons]
      cases hΛu : Λ u with
      | none =>
          rw [List.filter_cons_of_neg (pa := by simp [hΛu])]
          change (∃ p, ∃ hp : WitnessTree.ValidPath (buildBelow vbl Λ l σ) p,
              (WitnessTree.labelAt hp).2 = a) ∧
            (WitnessTree.labels (forgetTime (buildBelow vbl Λ l σ)) : Multiset ι).count a =
              (WitnessTree.labels (forgetTime σ) : Multiset ι).count a +
                (l.filter (fun u => Λ u = some a)).length
          exact ih σ hA
      | some i =>
          by_cases hia : i = a
          · subst i
            have hih := ih σ hA
            have hs := step_count_of_eq vbl (a := a) (u := u)
              (τ := buildBelow vbl Λ l σ) (hA := hih.1)
            rw [buildBelow] at hih hs
            constructor
            · exact hs.1
            · rw [hs.2, hih.2]
              rw [List.filter_cons_of_pos (pa := by simp [hΛu])]
              simp
              omega
          · have hih := ih σ hA
            have hs := step_count_of_ne vbl (hi := hia) (a := a) (u := u) (i := i)
              (τ := buildBelow vbl Λ l σ) (hA := hih.1)
            rw [buildBelow] at hih hs
            constructor
            · exact hs.1
            · rw [hs.2, hih.2]
              rw [List.filter_cons_of_neg (pa := by simp [hΛu, hia])]

/-! ### Occurrence-count comparison (small list facts) -/

private theorem length_filter_range_succ_lt [DecidableEq ι] {Λ : ℕ → Option ι} {s : ℕ}
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

private theorem length_filter_range_mono [DecidableEq ι] {Λ : ℕ → Option ι} {n m : ℕ}
    {a : ι} (h : n ≤ m) :
    ((List.range n).filter (fun u => Λ u = some a)).length ≤
      ((List.range m).filter (fun u => Λ u = some a)).length := by
  induction h with
  | refl => rfl
  | step h ih =>
      exact le_trans ih (by
        rw [List.range_succ, List.filter_append, List.length_append]
        omega)

/-- The number of `a`-occurrences up to time `t` strictly exceeds that up to `s` when
`s < t` and `Λ s = some a` (the `r`-th vs `r'`-th occurrence comparison). -/
private theorem length_filter_range_lt [DecidableEq ι] {Λ : ℕ → Option ι} {s t : ℕ}
    {a : ι} (hst : s < t) (hΛs : Λ s = some a) :
    ((List.range s).filter (fun u => Λ u = some a)).length <
      ((List.range t).filter (fun u => Λ u = some a)).length :=
  lt_of_lt_of_le (length_filter_range_succ_lt hΛs)
    (length_filter_range_mono (m := t) (Nat.succ_le_of_lt hst))

/-! ### Public statements (Prop 12.1) -/

/-- **The r-th occurrence A-count**: when `Λ t = some a`, the occurring abstract tree
`forgetTime (treeAt vbl Λ t)` contains exactly one `a`-labeled vertex per `a`-occurrence
at or before `t`. -/
theorem treeAt_count_label [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ}
    {a : ι} (ht : Λ t = some a) :
    (WitnessTree.labels (forgetTime (treeAt vbl Λ t)) : Multiset ι).count a =
      ((List.range t).filter (fun u => Λ u = some a)).length + 1 := by
  unfold treeAt
  simp only [ht]
  change Multiset.count a
      ↑(forgetTime (buildBelow vbl Λ (List.range t) (WitnessTree.mk (t, a) []))).labels =
    (List.filter (fun u ↦ Λ u = some a) (List.range t)).length + 1
  rw [(foldr_count_label vbl (Λ := Λ) (a := a) (l := List.range t)
    (σ := WitnessTree.mk (t, a) []) ⟨[], .root, rfl⟩).2]
  simp [forgetTime, WitnessTree.labels]
  omega

/-! ### Prop 12.1, the two-case argument on the time-labeled side -/

/-- **Prop 12.1, the two-case argument on the time-labeled side** (symmetric lemma): different
root labels, or — for the same label `a` — different `a`-counts. -/
private theorem treeAt_forgetTime_injective_of_lt [DecidableEq ι] [Inhabited ι]
    {Λ : ℕ → Option ι} {s t : ℕ} (hst : s < t) (hs : Λ s ≠ none) (ht : Λ t ≠ none) :
    forgetTime (treeAt vbl Λ s) ≠ forgetTime (treeAt vbl Λ t) := by
  rcases Option.ne_none_iff_exists.mp hs with ⟨i, hsi⟩
  rcases Option.ne_none_iff_exists.mp ht with ⟨j, htj⟩
  by_cases hij : i = j
  · subst j
    intro heq
    have hs' := treeAt_count_label vbl (t := s) (a := i) (ht := hsi.symm)
    have ht' := treeAt_count_label vbl (t := t) (a := i) (ht := htj.symm)
    have hc : ((List.range s).filter (fun u => Λ u = some i)).length + 1 =
        ((List.range t).filter (fun u => Λ u = some i)).length + 1 := by
      rw [← hs', ← ht']
      exact congrArg (fun τ => (WitnessTree.labels τ : Multiset ι).count i) heq
    have hlt : ((List.range s).filter (fun u => Λ u = some i)).length <
        ((List.range t).filter (fun u => Λ u = some i)).length :=
      length_filter_range_lt hst hsi.symm
    omega
  · intro heq
    have hi' : WitnessTree.labelOf (forgetTime (treeAt vbl Λ s)) = i := by
      rw [labelOf_forgetTime, treeAt_root_label vbl hsi.symm]
    have hj' : WitnessTree.labelOf (forgetTime (treeAt vbl Λ t)) = j := by
      rw [labelOf_forgetTime, treeAt_root_label vbl htj.symm]
    exact hij (by rw [← hi', ← hj', heq])

/-- **Prop 12.1**: distinct genuine times give distinct occurring trees after forgetting
the time (60.1's injectivity input, at the abstract-tree level). -/
theorem treeAt_forgetTime_injective [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι}
    {s t : ℕ} (hne : s ≠ t) (hs : Λ s ≠ none) (ht : Λ t ≠ none) :
    forgetTime (treeAt vbl Λ s) ≠ forgetTime (treeAt vbl Λ t) := by
  rcases Nat.lt_or_gt_of_ne hne with hst | hts
  · exact treeAt_forgetTime_injective_of_lt vbl hst hs ht
  · exact (treeAt_forgetTime_injective_of_lt vbl hts ht hs).symm

/-- Bonus (trivial): the time-labeled `treeAt` itself is injective — the roots carry the
times (`treeAt_root_label'`). -/
theorem treeAt_injective [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {s t : ℕ}
    (hne : s ≠ t) :
    treeAt vbl Λ s ≠ treeAt vbl Λ t := by
  intro h
  have hl := congrArg (fun τ : WitnessTree (ℕ × ι) => WitnessTree.labelOf τ) h
  rw [treeAt_root_label' vbl Λ s, treeAt_root_label' vbl Λ t] at hl
  exact hne (Prod.ext_iff.mp hl).1

/-- **Prop 12.1 (60.1's form)**: distinct stopping-time predecessors give distinct
occurring (abstract) trees. `log_ne_none_iff_lt_R` lifts the `t < R` guards. -/
theorem T_injective [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {s t : ℕ} (hne : s ≠ t)
    (hs : s < R vbl A pick hpick ω) (ht : t < R vbl A pick hpick ω) :
    T vbl A pick hpick ω s ≠ T vbl A pick hpick ω t := by
  unfold T
  exact treeAt_forgetTime_injective vbl hne
    ((log_ne_none_iff_lt_R vbl A pick hpick ω).2 hs)
    ((log_ne_none_iff_lt_R vbl A pick hpick ω).2 ht)

end TreeAtInjective

/-! ## Abstract-level attach glue (namespace WitnessTree; consumed by 30.5) -/

namespace WitnessTree

variable {ι : Type u}
variable {elig : ι → ι → Prop} [∀ a b, Decidable (elig a b)]
variable {i : ι}

/-- Definitional copy of the file-private `maxOption`, so the folds inside the
`deepestEligible`/`attachBelow` equation lemmas can be re-expressed. -/
private def mtMaxOption' (m o : Option ℕ) : Option ℕ :=
  match m, o with
  | none, o => o
  | m, none => m
  | some a, some b => some (max a b)

private lemma deepestEligible_mk (a : ι) (cs : List (WitnessTree ι)) :
    deepestEligible elig i (mk a cs) =
      (let d := cs.foldl (fun m c => mtMaxOption' m ((deepestEligible elig i c).map (· + 1))) none
      if elig i a then some (d.getD 0) else d) := by
  rw [deepestEligible.eq_1]
  rfl

private lemma attachBelow_mk (a : ι) (cs : List (WitnessTree ι)) :
    attachBelow elig i (mk a cs) =
      (let d := cs.foldl (fun m c => mtMaxOption' m ((deepestEligible elig i c).map (· + 1))) none
      match d with
      | none => if elig i a then mk a (cs ++ [mk i []]) else mk a cs
      | some dd => mk a (attachInFirst elig i dd cs)) := by
  rw [attachBelow.eq_1]
  rfl

/-- A `some dd` value of the children's max-fold is at least `1` (each entry is a
`(· + 1)`-shifted depth). -/
private lemma foldl_mtMaxOption_ge_one'' {dd : ℕ} :
    ∀ (cs : List (WitnessTree ι)) (m : Option ℕ), (∀ k, m = some k → 1 ≤ k) →
      cs.foldl (fun m c => mtMaxOption' m ((deepestEligible elig i c).map (· + 1))) m = some dd →
      1 ≤ dd := by
  intro cs
  induction cs with
  | nil => intro m hm h; rw [List.foldl_nil] at h; exact hm dd h
  | cons c cs ih =>
      intro m hm h
      rw [List.foldl_cons] at h
      have hm' : ∀ k, mtMaxOption' m ((deepestEligible elig i c).map (· + 1)) = some k → 1 ≤ k := by
        intro k hk
        cases m with
        | none =>
            cases hk' : deepestEligible elig i c with
            | none => simp [mtMaxOption', hk'] at hk
            | some n =>
                have hsn : n + 1 = k := by simpa [mtMaxOption', hk'] using hk
                omega
        | some n =>
            cases hk' : deepestEligible elig i c with
            | none =>
                have hn1 : 1 ≤ n := hm n rfl
                have hsn : n = k := by simpa [mtMaxOption', hk'] using hk
                omega
            | some m' =>
                have hmx : max n (m' + 1) = k := by simpa [mtMaxOption', hk'] using hk
                omega
      exact ih (mtMaxOption' m ((deepestEligible elig i c).map (· + 1))) hm' h

private lemma foldl_mtMaxOption_ge_one {cs : List (WitnessTree ι)} {dd : ℕ}
    (hfold : cs.foldl (fun m c => mtMaxOption' m ((deepestEligible elig i c).map (· + 1))) none
      = some dd) : 1 ≤ dd :=
  foldl_mtMaxOption_ge_one'' cs none (by intro k hk; cases hk) hfold

/-- The `j`-th child of `attachInFirst` is kept or replaced by its `attachBelow`-image. -/
private theorem attachInFirst_childrenOf {dd : ℕ} {cs : List (WitnessTree ι)} {j : ℕ}
    {c' : WitnessTree ι} (h : (attachInFirst elig i dd cs)[j]? = some c') :
    (∃ c, cs[j]? = some c ∧ c' = c) ∨
      (∃ c, cs[j]? = some c ∧ c' = attachBelow elig i c) := by
  induction cs generalizing j with
  | nil => simp [attachInFirst] at h
  | cons c cs ih =>
      cases j with
      | zero =>
          by_cases hd : deepestEligible elig i c = some (dd - 1)
          · right
            refine ⟨c, by simp, ?_⟩
            simpa [attachInFirst, hd] using h.symm
          · left
            refine ⟨c, by simp, ?_⟩
            simpa [attachInFirst, hd] using h.symm
      | succ j =>
          by_cases hd : deepestEligible elig i c = some (dd - 1)
          · have hc : cs[j]? = some c' := by simpa [attachInFirst, hd] using h
            left
            refine ⟨c', ?_, rfl⟩
            simpa using hc
          · have hc : (attachInFirst elig i dd cs)[j]? = some c' := by simpa [attachInFirst,
            hd] using h
            rcases ih hc with hkept | hrepl
            · rcases hkept with ⟨c₀, hc₀, hcc⟩
              left
              refine ⟨c₀, ?_, hcc⟩
              simpa using hc₀
            · rcases hrepl with ⟨c₀, hc₀, hcc⟩
              right
              refine ⟨c₀, ?_, hcc⟩
              simpa using hc₀

/-- A replaced child is a `some (dd - 1)`-match, unless the attachment was a no-op
(in which case the child is unchanged and the kept case above applies). Note the extra
`hc : cs[j]? = some c` (the child's position) — without it the statement is false: a kept
child equal to `c`'s no-op image satisfies the hypothesis but neither disjunct. -/
private theorem attachInFirst_replaced {dd : ℕ} {cs : List (WitnessTree ι)} {j : ℕ}
    {c : WitnessTree ι} (h : (attachInFirst elig i dd cs)[j]? = some (attachBelow elig i c))
    (hc : cs[j]? = some c) :
    deepestEligible elig i c = some (dd - 1) ∨ attachBelow elig i c = c := by
  induction cs generalizing j with
  | nil => simp at hc
  | cons c' cs ih =>
      cases j with
      | zero =>
          have hcc' : c' = c := by simpa using hc
          subst c
          by_cases hd : deepestEligible elig i c' = some (dd - 1)
          · left
            simp [hd]
          · right
            simpa [attachInFirst, hd] using h.symm
      | succ j =>
          have hcs : cs[j]? = some c := by simpa using hc
          by_cases hd : deepestEligible elig i c' = some (dd - 1)
          · have h' : cs[j]? = some (attachBelow elig i c) := by simpa [attachInFirst, hd] using h
            right
            have heq : c = attachBelow elig i c := by
              have : some c = some (attachBelow elig i c) := by simpa [hcs] using h'
              simpa using this
            exact heq.symm
          · have h' : (attachInFirst elig i dd cs)[j]? = some (attachBelow elig i c) := by
              simpa [attachInFirst, hd] using h
            exact ih h' hcs

/-- A path in `attachBelow`'s output addresses either an old vertex (valid in the input,
same label) or the new leaf (label `i`, depth `d + 1`). The disjunction is not exclusive:
an old vertex labeled `i` satisfies both. (Public by necessity: private names do not
resolve across the `TCSLean.MoserTardos` / `TCSLean.MoserTardos.WitnessTree` namespace boundary, so it
must stay public for the `TreeAtDepth` section to use it.) -/
theorem attachBelow_old_or_new {τ : WitnessTree ι} {d : ℕ}
    (h : deepestEligible elig i τ = some d) {q : List ℕ}
    (hq : ValidPath (attachBelow elig i τ) q) :
    (∃ hq' : ValidPath τ q, labelAt hq' = labelAt hq) ∨
      (labelAt hq = i ∧ depth (attachBelow elig i τ) q = d + 1) := by
  refine WitnessTree.rec
      (motive_1 := fun τ => ∀ d, deepestEligible elig i τ = some d → ∀ q,
        (hq : ValidPath (attachBelow elig i τ) q) →
          (∃ hq' : ValidPath τ q, labelAt hq' = labelAt hq) ∨
            (labelAt hq = i ∧ depth (attachBelow elig i τ) q = d + 1))
      (motive_2 := fun cs => ∀ c ∈ cs, ∀ d, deepestEligible elig i c = some d → ∀ q,
        (hq : ValidPath (attachBelow elig i c) q) →
          (∃ hq' : ValidPath c q, labelAt hq' = labelAt hq) ∨
            (labelAt hq = i ∧ depth (attachBelow elig i c) q = d + 1)) ?_ ?_ ?_ τ d h q hq
  · intro a cs ih d hd q hq
    cases hfold : cs.foldl (fun m c => mtMaxOption' m ((deepestEligible elig i c).map (· + 1)))
      none with
    | none =>
        rw [deepestEligible_mk] at hd
        simp [hfold, Option.getD] at hd
        have ha : elig i a := hd.1
        have hd0 : d = 0 := hd.2.symm
        have hab : attachBelow elig i (mk a cs) = mk a (cs ++ [mk i []]) := by
          rw [attachBelow_mk]
          simp [hfold, ha]
        cases q with
        | nil =>
            left
            exact ⟨.root, by simp [labelAt_nil, labelOf_mk, hab]⟩
        | cons j q' =>
            cases hq with
            | cons j' c hc hvp =>
                rw [hab] at hc
                by_cases hj : j < cs.length
                · left
                  have hca : (cs ++ [mk i []])[j]? = some c := by simpa using hc
                  have hc' : cs[j]? = some c := by
                    rwa [List.getElem?_append_left (l₁ := cs) (l₂ := [mk i []]) (i := j) hj] at hca
                  refine ⟨.cons j c hc' hvp, ?_⟩
                  simp [labelAt_cons]
                · right
                  have hjlt : j < cs.length + 1 := by
                    have hca : (cs ++ [mk i []])[j]? = some c := by simpa using hc
                    simpa [List.length_append] using (List.getElem?_eq_some_iff.mp hca).1
                  have hj' : j = cs.length := by omega
                  subst j
                  have hcl : c = mk i [] := by simpa using hc.symm
                  subst c
                  have hq' : q' = [] := by
                    cases hvp with
                    | root => rfl
                    | cons _ _ hc'' _ =>
                        rw [childrenOf_mk] at hc''
                        simp at hc''
                  subst q'
                  constructor
                  · simp [labelAt_nil, labelOf_mk]
                  · rw [hab]
                    simp [depth, hd0]
    | some dd =>
        rw [deepestEligible_mk] at hd
        have hdd : dd = d := by
          by_cases ha : elig i a <;> simp [ha, hfold, Option.getD] at hd <;> simpa using hd
        have hab : attachBelow elig i (mk a cs) = mk a (attachInFirst elig i dd cs) := by
          rw [attachBelow_mk]
          simp [hfold]
        cases q with
        | nil =>
            left
            exact ⟨.root, by simp [labelAt_nil, labelOf_mk, hab]⟩
        | cons j q' =>
            cases hq with
            | cons j' c' hc' hvp =>
                rw [hab] at hc'
                rcases attachInFirst_childrenOf (by simpa using hc') with hkept | hrepl
                · rcases hkept with ⟨c, hc, hcc⟩
                  subst c'
                  left
                  refine ⟨.cons j c hc hvp, ?_⟩
                  simp [labelAt_cons]
                · rcases hrepl with ⟨c, hc, hcc⟩
                  rcases attachInFirst_replaced (by simpa [hcc] using hc') hc with hde | hself
                  · subst c'
                    rcases ih c (List.mem_of_getElem? (by simpa using hc)) (dd - 1) hde q' hvp with
                      hcold | hcnew
                    · rcases hcold with ⟨hvp', hl⟩
                      left
                      refine ⟨.cons j c hc hvp', ?_⟩
                      simpa [labelAt_cons] using hl
                    · rcases hcnew with ⟨hl, hd'⟩
                      right
                      constructor
                      · simpa [labelAt_cons] using hl
                      · rw [hab]
                        have hpos : 1 ≤ dd := foldl_mtMaxOption_ge_one hfold
                        have hdd' : (dd - 1) + 1 = dd := Nat.succ_pred_eq_of_pos hpos
                        have hlen : q'.length = dd := by simpa [depth, hdd'] using hd'
                        have hdepth : depth (mk a (attachInFirst elig i dd cs)) (j :: q') = dd
                          + 1 := by
                          simp [depth, hlen]
                        rw [hdepth, hdd]
                  · have hcc' : c' = c := hcc.trans hself
                    clear hcc
                    subst c'
                    left
                    refine ⟨.cons j c hc hvp, ?_⟩
                    simp [labelAt_cons]
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

end WitnessTree

/-! ## The time-labeled depth structure (30.5): Lemma 11.1 / Cor 11.2 -/

section TreeAtDepth

variable {ι : Type u}
variable {κ : Type u} [DecidableEq κ]
variable {Ω : κ → Type v}
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-! ## Private machinery: predicates -/

/-- Lemma 11.1's invariant on an arbitrary time-labeled tree: earlier time + overlap
implies strictly deeper. -/
private def depthStrict (vbl : ι → Finset κ) (τ : WitnessTree (ℕ × ι)) : Prop :=
  ∀ p q (hp : WitnessTree.ValidPath τ p) (hq : WitnessTree.ValidPath τ q),
    (WitnessTree.labelAt hp).1 < (WitnessTree.labelAt hq).1 →
      (vbl (WitnessTree.labelAt hp).2 ∩ vbl (WitnessTree.labelAt hq).2).Nonempty →
        WitnessTree.depth τ p > WitnessTree.depth τ q

/-- Distinct vertices have distinct times. -/
private def timeInject (τ : WitnessTree (ℕ × ι)) : Prop :=
  ∀ p q (hp : WitnessTree.ValidPath τ p) (hq : WitnessTree.ValidPath τ q),
    p ≠ q → (WitnessTree.labelAt hp).1 ≠ (WitnessTree.labelAt hq).1

/-! ## Private machinery: the attach glue (needs only 30.2's public API) -/

private theorem attachBelow_depthStrict_step [DecidableEq ι] {s : ℕ} {i : ι}
    (σ : WitnessTree (ℕ × ι))
    (hσ : depthStrict vbl σ)
    (ht : ∀ p (hp : WitnessTree.ValidPath σ p), s < (WitnessTree.labelAt hp).1) :
    depthStrict vbl (WitnessTree.attachBelow (treeElig vbl) (s, i) σ) := by
  intro p q hp hq hlt hov
  by_cases hd' : WitnessTree.deepestEligible (treeElig vbl) (s, i) σ = none
  · have hself : WitnessTree.attachBelow (treeElig vbl) (s, i) σ = σ :=
      WitnessTree.attachBelow_eq_self_of_deepestEligible_none (elig := treeElig vbl)
        (i := (s, i)) (τ := σ) hd'
    exact (hself ▸ hσ) p q hp hq hlt hov
  · have hm : ∃ d, WitnessTree.deepestEligible (treeElig vbl) (s, i) σ = some d := by
      cases hf : WitnessTree.deepestEligible (treeElig vbl) (s, i) σ with
      | none => exact (hd' hf).elim
      | some d => exact ⟨d, rfl⟩
    rcases hm with ⟨d, hd⟩
    -- the new vertex: time s
    by_cases hsu : (WitnessTree.labelAt hp).1 = s
    · rcases _root_.TCSLean.MoserTardos.WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i
      := (s, i))
        (τ := σ) hd hp with hpold | hpnew
      · rcases hpold with ⟨hp', hl⟩
        have hgt : s < (WitnessTree.labelAt hp).1 := by simpa [hl] using ht p hp'
        omega
      · rcases hpnew with ⟨hlp, hdp⟩
        have hst : s < (WitnessTree.labelAt hq).1 := by simpa [hlp] using hlt
        rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s, i))
          (τ := σ) hd hq with hqold | hqnew
        · rcases hqold with ⟨hq', hlq⟩
          have helig : treeElig vbl (s, i) (WitnessTree.labelAt hq') := by
            right
            simpa [hlp, hlq] using hov
          have hle : WitnessTree.depth σ q ≤ d :=
            ((WitnessTree.deepestEligible_eq_some (elig := treeElig vbl) (i := (s, i))
              (τ := σ) (d := d)).mp hd).2 q hq' helig
          have hle' : WitnessTree.depth (WitnessTree.attachBelow (treeElig vbl) (s, i) σ) q
            ≤ d := by
            simpa [WitnessTree.depth] using hle
          rw [hdp]
          omega
        · rcases hqnew with ⟨hlq, _⟩
          have : (WitnessTree.labelAt hq).1 = s := by simp [hlq]
          omega
    · rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s, i))
        (τ := σ) hd hp with hpold | hpnew
      · rcases hpold with ⟨hp', hlp⟩
        rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s, i))
          (τ := σ) hd hq with hqold | hqnew
        · rcases hqold with ⟨hq', hlq⟩
          have hlt' : (WitnessTree.labelAt hp').1 < (WitnessTree.labelAt hq').1 := by
            simpa [hlp, hlq] using hlt
          have hov' : (vbl (WitnessTree.labelAt hp').2 ∩ vbl (WitnessTree.labelAt
            hq').2).Nonempty := by
            simpa [hlp, hlq] using hov
          exact hσ p q hp' hq' hlt' hov'
        · rcases hqnew with ⟨hlq, _⟩
          have hgt : s < (WitnessTree.labelAt hp).1 := by simpa [hlp] using ht p hp'
          have hsq : (WitnessTree.labelAt hq).1 = s := by simp [hlq]
          omega
      · rcases hpnew with ⟨hlp, _⟩
        have hsp : (WitnessTree.labelAt hp).1 = s := by simp [hlp]
        exact (hsu hsp).elim

/-! ## Private machinery: the labels-multiset bridge (uniqueness of the new vertex) -/

private theorem mem_labels_of_labelAt {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
    (hp : WitnessTree.ValidPath τ p) : WitnessTree.labelAt hp ∈ WitnessTree.labels τ := by
  refine WitnessTree.ValidPath.rec (motive := fun {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
      (_hp : WitnessTree.ValidPath τ p) => WitnessTree.labelAt _hp ∈ WitnessTree.labels τ) ?_ ?_ hp
  · intro τ
    cases τ with
    | mk a cs => simp [WitnessTree.labelAt, WitnessTree.labels]
  · intro τ p j c hc hvp ih
    cases τ with
    | mk a cs =>
        simp only [WitnessTree.labelAt, WitnessTree.labels]
        right
        exact List.mem_flatMap.mpr ⟨c, List.mem_of_getElem? (by simpa using hc), by simpa
          [WitnessTree.labelAt] using ih⟩

private theorem time_gt_of_mem_labels {s : ℕ} {τ : WitnessTree (ℕ × ι)}
    (ht : ∀ p (hp : WitnessTree.ValidPath τ p), s < (WitnessTree.labelAt hp).1) {a : ℕ × ι}
    (ha : a ∈ WitnessTree.labels τ) : s < a.1 := by
  refine WitnessTree.rec
    (motive_1 := fun τ => (∀ p (hp : WitnessTree.ValidPath τ p), s < (WitnessTree.labelAt hp).1) →
      ∀ a, a ∈ WitnessTree.labels τ → s < a.1)
    (motive_2 := fun cs => ∀ c ∈ cs, (∀ p (hp : WitnessTree.ValidPath c p),
      s < (WitnessTree.labelAt hp).1) → ∀ a, a ∈ WitnessTree.labels c → s < a.1) ?_ ?_ ?_ τ ht a ha
  · intro b cs ih ht a ha
    simp [WitnessTree.labels] at ha
    rcases ha with ha₁ | hIn
    · subst a
      simpa [WitnessTree.labelAt, WitnessTree.treeAt] using ht [] .root
    · rcases hIn with ⟨c, hc, ha'⟩
      rcases (List.mem_iff_getElem?).mp hc with ⟨j, hj⟩
      exact ih c hc (fun p hp => by
        let hlift : WitnessTree.ValidPath (WitnessTree.mk b cs) (j :: p) :=
          .cons j c (by simpa using hj) hp
        simpa [WitnessTree.labelAt, hlift] using ht (j :: p) hlift) a ha'
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

private theorem count_le_count_flatMap [DecidableEq ι] {cs : List (WitnessTree (ℕ × ι))}
    {c : WitnessTree (ℕ × ι)} {a : ℕ × ι} (hc : c ∈ cs) :
    (WitnessTree.labels c).count a ≤ (cs.flatMap WitnessTree.labels).count a := by
  induction cs with
  | nil => simp at hc
  | cons c' cs ih =>
      rw [List.flatMap_cons, List.count_append]
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · omega
      · exact Nat.le_trans (ih hc)
          (Nat.le_add_left ((cs.flatMap WitnessTree.labels).count a) ((WitnessTree.labels
            c').count a))

private theorem count_add_count_le_count_flatMap [DecidableEq ι] {cs : List (WitnessTree (ℕ × ι))}
    {c c' : WitnessTree (ℕ × ι)} {a : ℕ × ι} {j k : ℕ}
    (hc : cs[j]? = some c) (hc' : cs[k]? = some c') (hjk : j ≠ k) :
    (WitnessTree.labels c).count a + (WitnessTree.labels c').count a ≤
      (cs.flatMap WitnessTree.labels).count a := by
  induction cs generalizing j k with
  | nil => simp at hc
  | cons d ds ih =>
      rw [List.flatMap_cons, List.count_append]
      cases j with
      | zero =>
          have hcd : c = d := by simpa using hc.symm
          subst c
          cases k with
          | zero => exact (hjk rfl).elim
          | succ k' =>
              have hck : ds[k']? = some c' := by simpa using hc'
              have hle := count_le_count_flatMap (a := a)
                (List.mem_of_getElem? (by simpa using hck))
              omega
      | succ j' =>
          have hcj : ds[j']? = some c := by simpa using hc
          cases k with
          | zero =>
              have hcd : c' = d := by simpa using hc'.symm
              subst c'
              have hle := count_le_count_flatMap (a := a)
                (List.mem_of_getElem? (by simpa using hcj))
              omega
          | succ k' =>
              have hck : ds[k']? = some c' := by simpa using hc'
              have hjk' : j' ≠ k' := by intro h; exact hjk (by simp [h])
              exact Nat.le_trans (ih hcj hck hjk')
                (Nat.le_add_left ((ds.flatMap WitnessTree.labels).count a) ((WitnessTree.labels
                  d).count a))

private theorem two_le_count_labels_of_two_paths [DecidableEq ι] {τ : WitnessTree (ℕ × ι)}
    {p q : List ℕ} (hp : WitnessTree.ValidPath τ p) (hq : WitnessTree.ValidPath τ q)
    (hne : p ≠ q) (hl : WitnessTree.labelAt hp = WitnessTree.labelAt hq) :
    2 ≤ (WitnessTree.labels τ).count (WitnessTree.labelAt hp) := by
  refine WitnessTree.rec
    (motive_1 := fun τ => ∀ p q (hp : WitnessTree.ValidPath τ p) (hq : WitnessTree.ValidPath τ q),
      p ≠ q → WitnessTree.labelAt hp = WitnessTree.labelAt hq →
        2 ≤ (WitnessTree.labels τ).count (WitnessTree.labelAt hp))
    (motive_2 := fun cs => ∀ c ∈ cs, ∀ p q (hp : WitnessTree.ValidPath c p)
      (hq : WitnessTree.ValidPath c q), p ≠ q →
        WitnessTree.labelAt hp = WitnessTree.labelAt hq →
          2 ≤ (WitnessTree.labels c).count (WitnessTree.labelAt hp)) ?_ ?_ ?_ τ p q hp hq hne hl
  · intro a cs ih p q hp hq hne hl
    cases p with
    | nil =>
        cases q with
        | nil => exact (hne rfl).elim
        | cons k q' =>
            cases hq with
            | cons k' c hc hvp =>
                have hcm : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
                have hla : WitnessTree.labelAt hvp = a := by
                  simpa using hl.symm
                have hcnt : 1 ≤ (WitnessTree.labels c).count a := by
                  rw [← hla]
                  have : 0 < (WitnessTree.labels c).count (WitnessTree.labelAt hvp) :=
                    List.count_pos_iff.mpr (mem_labels_of_labelAt hvp)
                  omega
                have hle := count_le_count_flatMap (a := a) hcm
                have htwo : 2 ≤ (cs.flatMap WitnessTree.labels).count a + 1 := by omega
                simp only [WitnessTree.labelAt_nil, WitnessTree.labelOf_mk, WitnessTree.labels]
                simpa using htwo
    | cons j p' =>
        cases hp with
        | cons j' c hc hvp =>
            have hcm : c ∈ cs := List.mem_of_getElem? (by simpa using hc)
            cases q with
            | nil =>
                cases hq with
                | root =>
                    have hla : WitnessTree.labelAt hvp = a := by
                      simpa using hl
                    have hcnt : 1 ≤ (WitnessTree.labels c).count (WitnessTree.labelAt hvp) := by
                      have : 0 < (WitnessTree.labels c).count (WitnessTree.labelAt hvp) :=
                        List.count_pos_iff.mpr (mem_labels_of_labelAt hvp)
                      omega
                    have hle := count_le_count_flatMap (a := WitnessTree.labelAt hvp) hcm
                    have htwo : 2 ≤ (cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt hvp)
                      + 1 := by
                      omega
                    simp only [WitnessTree.labelAt_cons, WitnessTree.labels]
                    simpa [hla] using htwo
            | cons k q'' =>
                cases hq with
                | cons k' c' hc' hvq =>
                    by_cases hjk : j = k
                    · subst k
                      have hcc : c = c' := by
                        have : some c = some c' := hc.symm.trans hc'
                        simpa using this
                      subst c'
                      have hne' : p' ≠ q'' := by intro h; exact hne (by simp [h])
                      have hl' : WitnessTree.labelAt hvp = WitnessTree.labelAt hvq := by
                        simpa only [WitnessTree.labelAt_cons] using hl
                      have htwo' : 2 ≤ (WitnessTree.labels c).count (WitnessTree.labelAt hvp) :=
                        ih c hcm p' q'' hvp hvq hne' hl'
                      have hle := count_le_count_flatMap (a := WitnessTree.labelAt hvp) hcm
                      have hle' : (cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt hvp) ≤
                          (a :: cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt hvp) := by
                        rw [List.count_cons]
                        exact Nat.le_add_right
                          ((cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt hvp)) _
                      have hres : 2 ≤ (a :: cs.flatMap WitnessTree.labels).count
                        (WitnessTree.labelAt hvp) := by
                        omega
                      simpa only [WitnessTree.labelAt_cons, WitnessTree.labels] using hres
                    · have hcnt₁ : 1 ≤ (WitnessTree.labels c).count (WitnessTree.labelAt hvp) := by
                        have : 0 < (WitnessTree.labels c).count (WitnessTree.labelAt hvp) :=
                          List.count_pos_iff.mpr (mem_labels_of_labelAt hvp)
                        omega
                      have hcnt₂ : 1 ≤ (WitnessTree.labels c').count (WitnessTree.labelAt hvp) := by
                        have hl' : WitnessTree.labelAt hvp = WitnessTree.labelAt hvq := by
                          simpa only [WitnessTree.labelAt_cons] using hl
                        rw [hl']
                        have : 0 < (WitnessTree.labels c').count (WitnessTree.labelAt hvq) :=
                          List.count_pos_iff.mpr (mem_labels_of_labelAt hvq)
                        omega
                      have hsum := count_add_count_le_count_flatMap (a := WitnessTree.labelAt hvp)
                        (by simpa using hc) (by simpa using hc') hjk
                      have htwo : 2 ≤ (cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt
                        hvp) := by
                        omega
                      have hle' : (cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt hvp) ≤
                          (a :: cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt hvp) := by
                        rw [List.count_cons]
                        exact Nat.le_add_right
                          ((cs.flatMap WitnessTree.labels).count (WitnessTree.labelAt hvp)) _
                      have hres : 2 ≤ (a :: cs.flatMap WitnessTree.labels).count
                        (WitnessTree.labelAt hvp) := by
                        omega
                      simpa only [WitnessTree.labelAt_cons, WitnessTree.labels] using hres
  · intro c hc
    cases hc
  · intro c cs ihc ihcs c' hc'
    rw [List.mem_cons] at hc'
    rcases hc' with rfl | hc'
    · exact ihc
    · exact ihcs c' hc'

/-- The `List.count` of the default product `BEq` agrees with the decidable one (both are
lawful over `[DecidableEq ι]`), bridging the instance mismatch between `two_le_…`'s
count and `Multiset.coe_count`'s. -/
private theorem list_count_beqProd_eq [DecidableEq ι] {a : ℕ × ι} {l : List (ℕ × ι)} :
    @List.count (ℕ × ι) instBEqProd a l = @List.count (ℕ × ι) instBEqOfDecidableEq a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [List.count_cons, ih]
      simp [beq_iff_eq]

private theorem attachBelow_newVertex_unique [DecidableEq ι] {s : ℕ} {i : ι}
    {σ : WitnessTree (ℕ × ι)} {d : ℕ}
    (h : WitnessTree.deepestEligible (treeElig vbl) (s, i) σ = some d)
    (ht : ∀ p (hp : WitnessTree.ValidPath σ p), s < (WitnessTree.labelAt hp).1)
    {q₁ q₂ : List ℕ}
    (h₁ : WitnessTree.ValidPath (WitnessTree.attachBelow (treeElig vbl) (s, i) σ) q₁)
    (h₂ : WitnessTree.ValidPath (WitnessTree.attachBelow (treeElig vbl) (s, i) σ) q₂)
    (ht₁ : (WitnessTree.labelAt h₁).1 = s) (ht₂ : (WitnessTree.labelAt h₂).1 = s) :
    q₁ = q₂ := by
  by_contra hne
  have hlabels : (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (s, i) σ) : Multiset
    (ℕ × ι)) =
      insert (s, i) (WitnessTree.labels σ : Multiset (ℕ × ι)) :=
    WitnessTree.labels_attachBelow (elig := treeElig vbl) (i := (s, i)) (τ := σ) h
  have hf₁ : WitnessTree.labelAt h₁ ∉ (WitnessTree.labels σ : Multiset (ℕ × ι)) := by
    intro hmem
    rw [Multiset.mem_coe] at hmem
    have hgt : s < (WitnessTree.labelAt h₁).1 := time_gt_of_mem_labels (τ := σ) ht hmem
    omega
  have hm₁ : WitnessTree.labelAt h₁ ∈ (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl)
    (s, i) σ) : Multiset (ℕ × ι)) := by
    rw [Multiset.mem_coe]
    exact mem_labels_of_labelAt h₁
  have hl₁ : WitnessTree.labelAt h₁ = (s, i) := by
    rw [hlabels] at hm₁
    rw [Multiset.insert_eq_cons, Multiset.mem_cons] at hm₁
    rcases hm₁ with hEq | hMem
    · exact hEq
    · exact (hf₁ hMem).elim
  have hf₂ : WitnessTree.labelAt h₂ ∉ (WitnessTree.labels σ : Multiset (ℕ × ι)) := by
    intro hmem
    rw [Multiset.mem_coe] at hmem
    have hgt : s < (WitnessTree.labelAt h₂).1 := time_gt_of_mem_labels (τ := σ) ht hmem
    omega
  have hl₂ : WitnessTree.labelAt h₂ = (s, i) := by
    have hm₂ : WitnessTree.labelAt h₂ ∈ (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl)
      (s, i) σ) : Multiset (ℕ × ι)) := by
      rw [Multiset.mem_coe]
      exact mem_labels_of_labelAt h₂
    rw [hlabels] at hm₂
    rw [Multiset.insert_eq_cons, Multiset.mem_cons] at hm₂
    rcases hm₂ with hEq | hMem
    · exact hEq
    · exact (hf₂ hMem).elim
  have htwo : 2 ≤ (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (s, i) σ)).count
      (WitnessTree.labelAt h₁) :=
    two_le_count_labels_of_two_paths (τ := WitnessTree.attachBelow (treeElig vbl) (s, i) σ)
      h₁ h₂ hne (hl₁.trans hl₂.symm)
  rw [hl₁] at hf₁
  have hcount : (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (s, i) σ) : Multiset (ℕ
    × ι)).count
      (s, i) = 1 := by
    rw [hlabels, Multiset.insert_eq_cons, Multiset.count_cons_self]
    have hz := Multiset.count_eq_zero_of_notMem hf₁
    omega
  have htwo' : 2 ≤ (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (s, i) σ) : Multiset
    (ℕ × ι)).count
      (s, i) := by
    rw [Multiset.coe_count]
    rw [show @List.count (ℕ × ι) instBEqOfDecidableEq (s, i)
        (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (s, i) σ)) =
        @List.count (ℕ × ι) instBEqProd (s, i)
        (WitnessTree.labels (WitnessTree.attachBelow (treeElig vbl) (s, i) σ)) from
      (list_count_beqProd_eq).symm]
    simpa [hl₁] using htwo
  omega

/-! ## Private machinery: the fold induction -/

/-- Transporting a valid path along a tree equality preserves its label. -/
private theorem labelAt_cast_tree {τ₁ τ₂ : WitnessTree (ℕ × ι)} (h : τ₁ = τ₂) {p : List ℕ}
    (hp : WitnessTree.ValidPath τ₁ p) :
    WitnessTree.labelAt (h ▸ hp) = WitnessTree.labelAt hp := by
  subst τ₂
  rfl

private theorem foldr_time_gt [DecidableEq ι] (Λ : ℕ → Option ι) (l : List ℕ) :
    ∀ (s : ℕ) (σ : WitnessTree (ℕ × ι)),
      (∀ s' ∈ l, s < s') →
      (∀ p (hp : WitnessTree.ValidPath σ p), s < (WitnessTree.labelAt hp).1) →
      ∀ p (hp : WitnessTree.ValidPath (buildBelow vbl Λ l σ) p), s < (WitnessTree.labelAt
        hp).1 := by
  induction l with
  | nil =>
      intro s σ hmem ht p hp
      simpa [buildBelow] using ht p hp
  | cons s₁ l ih =>
      intro s σ hmem ht p hp
      simp only [List.mem_cons] at hmem
      have hss₁ : s < s₁ := hmem s₁ (Or.inl rfl)
      have hmem' : ∀ s' ∈ l, s < s' := fun s' hs' => hmem s' (Or.inr hs')
      simp only [buildBelow, List.foldr_cons] at hp ⊢
      revert hp
      cases hΛ : Λ s₁ with
      | none =>
          intro hp
          exact ih s σ hmem' ht p hp
      | some i =>
          intro hp
          by_cases hd : WitnessTree.deepestEligible (treeElig vbl) (s₁, i) (buildBelow vbl Λ l
            σ) = none
          · have hself : WitnessTree.attachBelow (treeElig vbl) (s₁, i) (buildBelow vbl Λ l σ) =
              buildBelow vbl Λ l σ :=
              WitnessTree.attachBelow_eq_self_of_deepestEligible_none (elig := treeElig vbl)
                (i := (s₁, i)) (τ := buildBelow vbl Λ l σ) hd
            exact labelAt_cast_tree hself hp ▸ ih s σ hmem' ht p (hself ▸ hp)
          · have hm : ∃ d, WitnessTree.deepestEligible (treeElig vbl) (s₁, i) (buildBelow vbl Λ l σ)
            = some d := by
              cases hf : WitnessTree.deepestEligible (treeElig vbl) (s₁, i) (buildBelow vbl Λ
                l σ) with
              | none => exact (hd hf).elim
              | some d => exact ⟨d, rfl⟩
            rcases hm with ⟨d, hd⟩
            rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s₁, i))
              (τ := buildBelow vbl Λ l σ) hd hp with hpold | hpnew
            · rcases hpold with ⟨hp'', hl⟩
              have hgt : s < (WitnessTree.labelAt hp'').1 := ih s σ hmem' ht p hp''
              exact hl ▸ hgt
            · rcases hpnew with ⟨hl, _⟩
              have : (WitnessTree.labelAt hp).1 = s₁ := congrArg (fun x : ℕ × ι => x.1) hl
              omega

private theorem foldr_depthStrict_timeInject [DecidableEq ι] (Λ : ℕ → Option ι) (l : List ℕ) :
    ∀ (σ : WitnessTree (ℕ × ι)),
      depthStrict vbl σ → timeInject σ →
      (∀ s ∈ l, ∀ p (hp : WitnessTree.ValidPath σ p), s < (WitnessTree.labelAt hp).1) →
      l.Pairwise (· < ·) →
      depthStrict vbl (buildBelow vbl Λ l σ) ∧ timeInject (buildBelow vbl Λ l σ) := by
  induction l with
  | nil =>
      intro σ hσ htσ htimes hpair
      simpa [buildBelow] using ⟨hσ, htσ⟩
  | cons s₁ l ih =>
      intro σ hσ htσ htimes hpair
      have hss : ∀ b ∈ l, s₁ < b := (List.pairwise_cons.mp hpair).1
      have hpair' : l.Pairwise (· < ·) := (List.pairwise_cons.mp hpair).2
      have htimes' : ∀ s ∈ l, ∀ p (hp : WitnessTree.ValidPath σ p), s < (WitnessTree.labelAt
        hp).1 := by
        intro s hs
        exact htimes s (by simp [hs])
      have hs₁σ : ∀ p (hp : WitnessTree.ValidPath σ p), s₁ < (WitnessTree.labelAt hp).1 :=
        htimes s₁ (by simp)
      simp only [buildBelow, List.foldr_cons]
      cases hΛ : Λ s₁ with
      | none =>
          simpa [buildBelow, hΛ] using ih σ hσ htσ htimes' hpair'
      | some i =>
          let τ' := WitnessTree.attachBelow (treeElig vbl) (s₁, i) (buildBelow vbl Λ l σ)
          have hres := ih σ hσ htσ htimes' hpair'
          have hs₁ : ∀ p (hp : WitnessTree.ValidPath (buildBelow vbl Λ l σ) p), s₁ <
            (WitnessTree.labelAt hp).1 :=
            foldr_time_gt vbl Λ l s₁ σ hss hs₁σ
          have hdS' : depthStrict vbl τ' :=
            attachBelow_depthStrict_step vbl (buildBelow vbl Λ l σ) hres.1 hs₁
          have hti' : timeInject τ' := by
            intro p q hp hq hne
            by_cases hd' : WitnessTree.deepestEligible (treeElig vbl) (s₁, i) (buildBelow vbl Λ l
              σ) = none
            · have hself : τ' = buildBelow vbl Λ l σ := by
                simpa [τ'] using (WitnessTree.attachBelow_eq_self_of_deepestEligible_none
                  (elig := treeElig vbl) (i := (s₁, i)) (τ := buildBelow vbl Λ l σ) hd')
              exact labelAt_cast_tree hself hp ▸ labelAt_cast_tree hself hq ▸
                hres.2 p q (hself ▸ hp) (hself ▸ hq) hne
            · have hm : ∃ d, WitnessTree.deepestEligible (treeElig vbl) (s₁, i) (buildBelow vbl Λ l
              σ) = some d := by
                cases hf : WitnessTree.deepestEligible (treeElig vbl) (s₁, i) (buildBelow vbl Λ
                  l σ) with
                | none => exact (hd' hf).elim
                | some d => exact ⟨d, rfl⟩
              rcases hm with ⟨d, hd⟩
              rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s₁, i))
                (τ := buildBelow vbl Λ l σ) hd hp with hpo | hpn
              · rcases hpo with ⟨hp', hlp⟩
                rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s₁, i))
                  (τ := buildBelow vbl Λ l σ) hd hq with hqo | hqn
                · rcases hqo with ⟨hq', hlq⟩
                  exact hlp ▸ (hlq ▸ hres.2 p q hp' hq' hne)
                · rcases hqn with ⟨hlq, _⟩
                  have hps : s₁ < (WitnessTree.labelAt hp).1 := hlp ▸ hs₁ p hp'
                  have hqs : (WitnessTree.labelAt hq).1 = s₁ := congrArg (fun x : ℕ × ι => x.1) hlq
                  omega
              · rcases hpn with ⟨hlp, _⟩
                rcases WitnessTree.attachBelow_old_or_new (elig := treeElig vbl) (i := (s₁, i))
                  (τ := buildBelow vbl Λ l σ) hd hq with hqo | hqn
                · rcases hqo with ⟨hq', hlq⟩
                  have hps : (WitnessTree.labelAt hp).1 = s₁ := congrArg (fun x : ℕ × ι => x.1) hlp
                  have hqs : s₁ < (WitnessTree.labelAt hq).1 := hlq ▸ hs₁ q hq'
                  omega
                · rcases hqn with ⟨hlq, _⟩
                  have heq : p = q := by
                    exact attachBelow_newVertex_unique vbl (σ := buildBelow vbl Λ l σ) hd hs₁
                      hp hq (congrArg (fun x : ℕ × ι => x.1) hlp) (congrArg (fun x : ℕ × ι =>
                        x.1) hlq)
                  exact (hne heq).elim
          constructor
          · exact hdS'
          · exact hti'

/-- The leaf seed satisfies the invariants vacuously (the only path is the root). -/
private theorem leaf_depthStrict [DecidableEq ι] {t : ℕ} (x : ι) :
    depthStrict vbl (WitnessTree.mk (t, x) []) := by
  intro p q hp hq hlt hov
  cases p with
  | nil =>
      cases q with
      | nil =>
          have : t < t := by
            simp [WitnessTree.labelAt, WitnessTree.treeAt] at hlt
          omega
      | cons _ _ =>
          cases hq with
          | cons _ _ hc _ => rw [WitnessTree.childrenOf_mk] at hc; simp at hc
  | cons _ _ => cases hp with | cons _ _ hc _ => rw [WitnessTree.childrenOf_mk] at hc; simp at hc

private theorem leaf_timeInject [DecidableEq ι] {t : ℕ} (x : ι) :
    timeInject (WitnessTree.mk (t, x) []) := by
  intro p q hp hq hne
  cases p with
  | nil =>
      cases q with
      | nil => exact (hne rfl).elim
      | cons _ _ =>
          cases hq with
          | cons _ _ hc _ => rw [WitnessTree.childrenOf_mk] at hc; simp at hc
  | cons _ _ => cases hp with | cons _ _ hc _ => rw [WitnessTree.childrenOf_mk] at hc; simp at hc

private theorem leaf_time_gt [DecidableEq ι] {t : ℕ} (x : ι) {s : ℕ} (hs : s < t) :
    ∀ p (hp : WitnessTree.ValidPath (WitnessTree.mk (t, x) []) p), s < (WitnessTree.labelAt
      hp).1 := by
  intro p hp
  cases p with
  | nil => simpa [WitnessTree.labelAt, WitnessTree.treeAt] using hs
  | cons _ _ => cases hp with | cons _ _ hc _ => rw [WitnessTree.childrenOf_mk] at hc; simp at hc

private theorem treeAt_depthStrict [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
    depthStrict vbl (treeAt vbl Λ t) := by
  unfold treeAt
  cases h : Λ t with
  | none =>
      refine (foldr_depthStrict_timeInject vbl Λ (List.range t) (WitnessTree.mk (t, default) [])
        ?_ ?_ ?_ ?_).1
      · exact leaf_depthStrict (vbl := vbl) (t := t) default
      · exact leaf_timeInject (t := t) default
      · intro s hs
        exact leaf_time_gt (t := t) default (List.mem_range.mp hs)
      · exact List.pairwise_lt_range
  | some i =>
      refine (foldr_depthStrict_timeInject vbl Λ (List.range t) (WitnessTree.mk (t, i) [])
        ?_ ?_ ?_ ?_).1
      · exact leaf_depthStrict (vbl := vbl) (t := t) i
      · exact leaf_timeInject (t := t) i
      · intro s hs
        exact leaf_time_gt (t := t) i (List.mem_range.mp hs)
      · exact List.pairwise_lt_range

private theorem treeAt_timeInject' [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
    timeInject (treeAt vbl Λ t) := by
  unfold treeAt
  cases h : Λ t with
  | none =>
      refine (foldr_depthStrict_timeInject vbl Λ (List.range t) (WitnessTree.mk (t, default) [])
        ?_ ?_ ?_ ?_).2
      · exact leaf_depthStrict (vbl := vbl) (t := t) default
      · exact leaf_timeInject (t := t) default
      · intro s hs
        exact leaf_time_gt (t := t) default (List.mem_range.mp hs)
      · exact List.pairwise_lt_range
  | some i =>
      refine (foldr_depthStrict_timeInject vbl Λ (List.range t) (WitnessTree.mk (t, i) [])
        ?_ ?_ ?_ ?_).2
      · exact leaf_depthStrict (vbl := vbl) (t := t) i
      · exact leaf_timeInject (t := t) i
      · intro s hs
        exact leaf_time_gt (t := t) i (List.mem_range.mp hs)
      · exact List.pairwise_lt_range

/-- **Lemma 11.1**: in the witness tree built from the log prefix, an earlier entry
sharing a variable with a later one is strictly deeper. -/
theorem depth_gt_of_earlier_overlap [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ}
    {p q : List ℕ} (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p)
    (hq : WitnessTree.ValidPath (treeAt vbl Λ t) q)
    (ht : (WitnessTree.labelAt hp).1 < (WitnessTree.labelAt hq).1)
    (hov : (vbl (WitnessTree.labelAt hp).2 ∩ vbl (WitnessTree.labelAt hq).2).Nonempty) :
    WitnessTree.depth (treeAt vbl Λ t) p > WitnessTree.depth (treeAt vbl Λ t) q := by
  exact treeAt_depthStrict vbl p q hp hq ht hov

/-- Distinct vertices of a constructed tree have distinct times (each reverse-scan step
creates at most one vertex). The input of Cor 11.2's comparability step (and of 40.2's
backward direction). -/
theorem treeAt_timeInject [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ}
    {p q : List ℕ} (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p)
    (hq : WitnessTree.ValidPath (treeAt vbl Λ t) q) (hne : p ≠ q) :
    (WitnessTree.labelAt hp).1 ≠ (WitnessTree.labelAt hq).1 := by
  exact treeAt_timeInject' vbl p q hp hq hne

/-- **Cor 11.2**: vertices at the same depth have disjoint variable sets (distinct
vertices have distinct times, so Lemma 11.1 applies symmetrically). -/
theorem vbl_disjoint_of_same_depth [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ}
    {p q : List ℕ} (hp : WitnessTree.ValidPath (treeAt vbl Λ t) p)
    (hq : WitnessTree.ValidPath (treeAt vbl Λ t) q)
    (hne : p ≠ q)
    (hdepth : WitnessTree.depth (treeAt vbl Λ t) p = WitnessTree.depth (treeAt vbl Λ t) q) :
    Disjoint (vbl (WitnessTree.labelAt hp).2) (vbl (WitnessTree.labelAt hq).2) := by
  by_contra hdisj
  rcases Finset.not_disjoint_iff.mp hdisj with ⟨x, hx₁, hx₂⟩
  have hov : (vbl (WitnessTree.labelAt hp).2 ∩ vbl (WitnessTree.labelAt hq).2).Nonempty := by
    exact ⟨x, Finset.mem_inter.mpr ⟨hx₁, hx₂⟩⟩
  have hov' : (vbl (WitnessTree.labelAt hq).2 ∩ vbl (WitnessTree.labelAt hp).2).Nonempty := by
    exact ⟨x, Finset.mem_inter.mpr ⟨hx₂, hx₁⟩⟩
  have htneq : (WitnessTree.labelAt hp).1 ≠ (WitnessTree.labelAt hq).1 :=
    treeAt_timeInject vbl hp hq hne
  rcases Nat.lt_or_gt_of_ne htneq with hlt | hgt
  · have hdgt : WitnessTree.depth (treeAt vbl Λ t) p > WitnessTree.depth (treeAt vbl Λ t) q :=
      depth_gt_of_earlier_overlap vbl hp hq hlt hov
    omega
  · have hdgt : WitnessTree.depth (treeAt vbl Λ t) q > WitnessTree.depth (treeAt vbl Λ t) p :=
      depth_gt_of_earlier_overlap vbl hq hp hgt hov'
    omega

end TreeAtDepth

/-! ## Occurring trees are good and small (30.7): the IsGood transport + size bounds -/

section TreeAtGood

variable {ι : Type u}
variable {κ : Type u} [DecidableEq κ]
variable {Ω : κ → Type v}
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-! ## forgetTime path transport, reverse direction (30.7) -/

/-- The reverse of 30.3's `forgetTime_getElem?`: an abstract child of the `forgetTime`
image comes from a time-labeled child. -/
theorem forgetTime_getElem?_of {τ : WitnessTree (ℕ × ι)} {i : ℕ} {c' : WitnessTree ι}
    (hc' : (forgetTime τ).childrenOf[i]? = some c') :
    ∃ c : WitnessTree (ℕ × ι), τ.childrenOf[i]? = some c ∧ forgetTime c = c' := by
  rw [childrenOf_forgetTime, List.getElem?_map, Option.map_eq_some_iff] at hc'
  exact hc'

/-- A valid path in the `forgetTime` image lifts to a valid path in the time-labeled tree
(the same child-index list; the lifted path visits the preimage vertices). Data-valued like
`ValidPath`; match the PATH first (30.1's pattern). The child witness is
`Classical.choose` (the `Exists` cannot be cased into the Type-valued `ValidPath` — cf.
the 30.3 Survey's flag; note the choose is INLINED here, not wrapped in a def — a wrapper
breaks defeq at the instances transparency, compile-verified). The recursive call receives
the cast of `hvp` along `forgetTime c = c'` (explicit `cast (congrArg …)` — the `▸`
notation fails to compute the motive here, compile-verified). -/
noncomputable def validPath_of_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
    (hp : WitnessTree.ValidPath (forgetTime τ) p) : WitnessTree.ValidPath τ p :=
  match p with
  | [] => .root
  | i :: p' =>
      match hp with
      | .cons i _ hc' hvp =>
          .cons i (Classical.choose (forgetTime_getElem?_of hc'))
            (Classical.choose_spec (forgetTime_getElem?_of hc')).1
            (validPath_of_forgetTime
              (cast (congrArg (fun x => WitnessTree.ValidPath x p')
                (Classical.choose_spec (forgetTime_getElem?_of hc')).2.symm) hvp))

/-- Labels survive casts of the tree along an equality (the glue for transporting labels
through the lift's preimage cast). Stated in the `cast (congrArg …)` form to match the
lift's inner cast exactly (the `▸` form is not defeq — different motives). -/
theorem labelAt_cast {τ τ' : WitnessTree ι} (h : τ = τ') {p : List ℕ}
    (hp : WitnessTree.ValidPath τ p) :
    WitnessTree.labelAt
        (cast (congrArg (fun x => WitnessTree.ValidPath x p) h) hp) =
      WitnessTree.labelAt hp := by
  subst h
  rfl

/-- The lifted path carries the same label: the abstract label at `hp` is the event
component of the time-labeled label at the lift. The single transport lemma 30.7's
`IsGood` proof consumes. -/
theorem labelAt_of_forgetTime {τ : WitnessTree (ℕ × ι)} {p : List ℕ}
    (hp : WitnessTree.ValidPath (forgetTime τ) p) :
    (WitnessTree.labelAt (validPath_of_forgetTime hp)).2 = WitnessTree.labelAt hp := by
  induction p generalizing τ with
  | nil =>
      cases hp with
      | root => simp [validPath_of_forgetTime, labelOf_forgetTime]
  | cons i p' ih =>
      cases hp with
      | cons i _ hc' hvp =>
          rw [validPath_of_forgetTime, WitnessTree.labelAt_cons, WitnessTree.labelAt_cons]
          have hih := ih (τ := Classical.choose (forgetTime_getElem?_of hc'))
            (cast (congrArg (fun x => WitnessTree.ValidPath x p')
              (Classical.choose_spec (forgetTime_getElem?_of hc')).2.symm) hvp)
          have hl := labelAt_cast (Classical.choose_spec (forgetTime_getElem?_of hc')).2.symm
            hvp
          simpa [← hl] using hih

/-! ## Occurring trees are good (30.7): Prop 10.1 + Cor 11.2 transported -/

/-- **30.7 headline** (abstract, unconditional): the witness tree built from the log
prefix is good — properness by Prop 10.1 (30.4), same-depth disjointness by Cor 11.2
(30.5, the integrated `vbl_disjoint_of_same_depth`) transported through the path lift.
No `t < R` needed: both ingredients hold for every `Λ` (the dummy root breaks neither). -/
theorem treeAt_isGood [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
    WitnessTree.IsGood vbl (forgetTime (treeAt vbl Λ t)) := by
  refine ⟨treeAt_proper vbl, ?_⟩
  intro p q hp hq hne hd
  have hdisj : Disjoint (vbl (WitnessTree.labelAt (validPath_of_forgetTime hp)).2)
      (vbl (WitnessTree.labelAt (validPath_of_forgetTime hq)).2) :=
    vbl_disjoint_of_same_depth vbl (validPath_of_forgetTime hp)
      (validPath_of_forgetTime hq) hne hd
  rw [← labelAt_of_forgetTime hp, ← labelAt_of_forgetTime hq]
  exact hdisj

/-- **The 40.3 form**: the occurring tree `T … ω t` is good. Unconditional (the coupling's
`t < R` guard serves other purposes — log genuineness — not goodness). -/
theorem T_isGood [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ} :
    WitnessTree.IsGood vbl (T vbl A pick hpick ω t) := by
  unfold T
  exact treeAt_isGood vbl

/-! ## Occurring trees are small (30.7): size ≤ t + 1 -/

/-- The reverse-scan fold grows the size by at most the length of the scanned list. -/
private theorem foldr_size_le [DecidableEq ι] {Λ : ℕ → Option ι} :
    ∀ l : List ℕ, ∀ τ : WitnessTree (ℕ × ι),
      WitnessTree.size (l.foldr (fun s τ => match Λ s with
        | none => τ
        | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) τ) ≤
        WitnessTree.size τ + l.length := by
  intro l
  induction l with
  | nil => intro τ; simp
  | cons s l ih =>
      intro τ
      rw [List.foldr_cons]
      cases h : Λ s with
      | none =>
          simp only [List.length_cons]
          have hi := ih τ
          omega
      | some i =>
          simp only [List.length_cons]
          have hs := WitnessTree.size_attachBelow (elig := treeElig vbl) (i := (s, i))
            (τ := l.foldr (fun s τ => match Λ s with
              | none => τ
              | some i => WitnessTree.attachBelow (treeElig vbl) (s, i) τ) τ)
          have hi := ih τ
          omega

/-- **30.7 headline** (size): each reverse-scan step adds at most one vertex (30.2's
`size_attachBelow`), the seed is a single root — so `size (treeAt vbl Λ t) ≤ t + 1`. -/
theorem treeAt_size_le [DecidableEq ι] [Inhabited ι] {Λ : ℕ → Option ι} {t : ℕ} :
    WitnessTree.size (treeAt vbl Λ t) ≤ t + 1 := by
  unfold treeAt
  refine Nat.le_trans (foldr_size_le vbl (List.range t)
    (match Λ t with
      | none => WitnessTree.mk (t, default) []
      | some i => WitnessTree.mk (t, i) [])) ?_
  cases h : Λ t <;> simp [WitnessTree.size_mk, List.length_range] <;> omega

/-- The occurring tree `T … ω t` has at most `t + 1` vertices. -/
theorem T_size_le [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ} :
    WitnessTree.size (T vbl A pick hpick ω t) ≤ t + 1 := by
  unfold T
  simpa [size_forgetTime] using treeAt_size_le vbl

/-- 40.3's `size τ ≤ N` input: for `t < R ω` the occurring tree fits the table
(`t < R ≤ N` via 20.3's `R_le`). -/
theorem T_size_le_N [DecidableEq ι] [Inhabited ι] {ω : ΩN N Ω} {t : ℕ}
    (ht : t < R vbl A pick hpick ω) :
    WitnessTree.size (T vbl A pick hpick ω t) ≤ N := by
  refine Nat.le_trans (T_size_le vbl A pick hpick) ?_
  exact Nat.le_trans (Nat.succ_le_of_lt ht) (R_le vbl A pick hpick ω)

end TreeAtGood

end TCSLean.MoserTardos
