/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Variable model for the Moser–Tardos algorithm

This file sets up the random variables of the Moser–Tardos resampling algorithm: for each
variable `j : κ` there is a value space `Ω j` with probability law `μ j`, and the algorithm
runs against a **truncated resampling table** `ΩN N Ω` with `N + 1` rows per variable (the
cumulative-row convention of the notes §7: a variable resampled `s` times holds the value of
row `s`, so an execution of up to `N` steps can reach row `N`).

Truncation design: every result downstream is stated per truncation level `N` (the finite
table, no infinite product). The per-`N` bound for all `N`, the per-`N` tail
(`moserTardos_tail`, 60.4), and existence (60.5) are captured, but there is deliberately
no `lim_N μN{R = N} = 0` / `E[R_∞] ≤ C` "terminates a.s." analogue — the paper's
infinite-run statements are out of scope for this library.

## Main definitions

* `ΩN N Ω`: the truncated resampling table — for every pair `(j, r)` of a variable `j : κ` and
  a row `r : Fin (N + 1)`, one value in `Ω j`. The table is indexed by the sigma type
  `Σ _ : κ, Fin (N + 1)` so that its law is literally `Measure.pi` (survey A §5.5).
* `ΩN.instMeasurableSpace`: the product measurable space on the table (needed because typeclass
  search does not unfold the semireducible `def ΩN` when elaborating `Measure (ΩN N Ω)`).
* `μN N μ`: the law of the table — the product measure over the pairs `(j, r)`, where the
  coordinate `(j, r)` has law `μ j`.
* `μπ μ`: the joint law on `Π j, Ω j` — the product measure over the variables.
* `DeterminedBy A S`: event `A` is determined by the variables in the finset `S` —
  membership depends only on the restriction `fun j => σ j` to `S`, through a predicate `f`
  on `Π j : S, Ω j`.
* `overlapGraph vbl`: the variable-overlap dependency graph on the variables `ι` — two
  variables are adjacent when they are distinct and their variable sets overlap
  (`Adj i j := i ≠ j ∧ (vbl i ∩ vbl j).Nonempty`), loopless by the `i ≠ j` guard.
* `gammaPlus vbl i`: the inclusive neighborhood Γ⁺ i of `i` in the overlap graph —
  `insert i ((overlapGraph vbl).neighborFinset i)`.

## Main results

* `μN.instIsProbabilityMeasure`: if every `μ j` is a probability measure, so is `μN N μ`.
* `μπ.instIsProbabilityMeasure`: if every `μ j` is a probability measure, so is `μπ μ`.
* `mem_gammaPlus`: the membership iff for Γ⁺ —
  `j ∈ gammaPlus vbl i ↔ j = i ∨ (overlapGraph vbl).Adj i j`.
* `mem_gammaPlus_of_overlap`: if `i = j ∨ (vbl i ∩ vbl j).Nonempty` then
  `j ∈ gammaPlus vbl i` — the two-case lemma that fixes the notes' Lemma 11.1 sentence.

## References

The resampling-table model follows the Moser–Tardos notes, §7 ([moserTardos2010]).
-/

set_option autoImplicit false
set_option pp.unicode.fun true

open MeasureTheory

universe u v

namespace TCSLean.MoserTardos

variable {κ : Type u} [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable {μ : ∀ j, Measure (Ω j)} [∀ j, IsProbabilityMeasure (μ j)]

/-- The truncated resampling table for `N` steps: one value in `Ω j` for every pair `(j, r)`
of a variable `j : κ` and a row `r : Fin (N + 1)`. The extra row (`N + 1` instead of `N`)
is the cumulative-row convention: a variable resampled `s` times holds the value of row `s`,
and an execution of up to `N` steps can resample one variable `N` times, reaching row `N`.

The table is indexed by the sigma type `Σ _ : κ, Fin (N + 1)` (not the curried
`Π j : κ, Fin (N + 1) → Ω j`) so that its law `μN` is literally `Measure.pi` over the pairs —
the curried form would need a pushforward equivalence for the measure (survey A §5.5). -/
def ΩN (N : ℕ) (Ω : κ → Type v) : Type (max u v) :=
  Π p : Σ _ : κ, Fin (N + 1), Ω p.1

/-- The product measurable space on the truncated resampling table. Needed because typeclass
search does not unfold the (semireducible) `def ΩN` when synthesizing the instance argument of
`Measure (ΩN N Ω)`. -/
instance ΩN.instMeasurableSpace (N : ℕ) : MeasurableSpace (ΩN N Ω) := by
  dsimp [ΩN]
  infer_instance

/-- The law of the truncated resampling table: the product measure over the pairs `(j, r)`,
with each pair having law `μ j`. -/
noncomputable def μN (N : ℕ) (μ : ∀ j, Measure (Ω j)) : Measure (ΩN N Ω) :=
  Measure.pi (fun p : Σ _ : κ, Fin (N + 1) => μ p.1)

instance μN.instIsProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (μN N μ) := by
  -- `change` is needed: after unfolding `μN`, the goal's *class* argument is still the
  -- constant `ΩN N Ω`, which typeclass search does not reduce, so it misses the instance
  -- `Measure.pi.instIsProbabilityMeasure` (whose class argument is a literal Pi type).
  change IsProbabilityMeasure (Measure.pi (fun p : Σ _ : κ, Fin (N + 1) => μ p.1))
  infer_instance

/-- The joint law on `Π j, Ω j`: the product measure over the variables. -/
noncomputable def μπ (μ : ∀ j, Measure (Ω j)) : Measure (Π j, Ω j) := Measure.pi μ

instance μπ.instIsProbabilityMeasure : IsProbabilityMeasure (μπ μ) := by
  dsimp [μπ]
  infer_instance

/-- `A` is determined by the variables in `S`: membership depends only on the coordinates
in `S`. -/
def DeterminedBy (A : Set (Π j, Ω j)) (S : Finset κ) : Prop :=
  ∃ f : (Π j : S, Ω j) → Prop, ∀ σ, σ ∈ A ↔ f fun j => σ j

section OverlapGraph

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable [DecidableEq κ]

-- No declaration in this section needs `[Fintype κ]` (the `neighborFinset` finiteness
-- chain uses only `[Fintype ι]`, `[DecidableEq ι]`, `[DecidableEq κ]`), but Lean's
-- theorem auto-include would still add the instance binder to every theorem whose header
-- mentions `κ`; `omit` keeps the section's theorems clean.
omit [Fintype κ]

/-- The variable-overlap dependency graph: `i` and `j` are adjacent when they are distinct
and their variable sets overlap (`(vbl i ∩ vbl j).Nonempty`). Loopless by the `i ≠ j`
guard. Built with the `SimpleGraph` structure constructor (NOT `SimpleGraph.fromRel`,
which symmetrizes with `∨` and would break the definitional `Adj`). -/
def overlapGraph (vbl : ι → Finset κ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (vbl i ∩ vbl j).Nonempty
  symm := by
    constructor
    intro i j h
    exact ⟨h.1.symm, by
      rw [Finset.inter_comm]
      exact h.2⟩
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

/-- Decidability of adjacency of the overlap graph: from `[DecidableEq ι]` alone (the
`Nonempty` check on the finite intersection is decidable unconditionally via
`Finset.decidableNonempty`, and `≠` via `instDecidableNe`). Needed for the local
finiteness `Fintype ((overlapGraph vbl).neighborSet i)` of `neighborFinset`. -/
instance overlapGraph.instDecidableRelAdj (vbl : ι → Finset κ) :
    DecidableRel (overlapGraph vbl).Adj :=
  fun i j => by
    change Decidable (i ≠ j ∧ (vbl i ∩ vbl j).Nonempty)
    infer_instance

/-- The inclusive neighborhood Γ⁺ i of `i` in the overlap graph: `i` itself together with
its neighbors. -/
def gammaPlus (vbl : ι → Finset κ) (i : ι) : Finset ι :=
  insert i ((overlapGraph vbl).neighborFinset i)

/-- The `neighborFinset` membership bridge for the overlap graph (unfolds `overlapGraph`
under `mem_neighborFinset`). -/
theorem mem_overlap_neighborFinset (vbl : ι → Finset κ) {i j : ι} :
    j ∈ (overlapGraph vbl).neighborFinset i ↔ i ≠ j ∧ (vbl i ∩ vbl j).Nonempty := by
  rw [SimpleGraph.mem_neighborFinset]
  rfl

/-- The inclusive self-membership of Γ⁺. -/
@[simp]
theorem mem_gammaPlus_self (vbl : ι → Finset κ) (i : ι) : i ∈ gammaPlus vbl i := by
  unfold gammaPlus
  exact Finset.mem_insert_self i ((overlapGraph vbl).neighborFinset i)

/-- The membership iff for Γ⁺. -/
theorem mem_gammaPlus (vbl : ι → Finset κ) {i j : ι} :
    j ∈ gammaPlus vbl i ↔ j = i ∨ (overlapGraph vbl).Adj i j := by
  unfold gammaPlus
  rw [Finset.mem_insert, SimpleGraph.mem_neighborFinset]

/-- Two-case membership in Γ⁺: if `i = j` the inclusive self-loop `i ∈ insert i …` applies,
and if `i ≠ j` the overlap gives adjacency (neighbor membership). Both cases land in
`gammaPlus vbl i`. -/
theorem mem_gammaPlus_of_overlap (vbl : ι → Finset κ) {i j : ι}
    (h : i = j ∨ (vbl i ∩ vbl j).Nonempty) :
    j ∈ gammaPlus vbl i := by
  rcases h with rfl | h
  · exact mem_gammaPlus_self vbl i
  · by_cases hij : i = j
    · subst hij
      exact mem_gammaPlus_self vbl i
    · exact (mem_gammaPlus vbl).mpr (Or.inr ⟨hij, h⟩)

end OverlapGraph

end TCSLean.MoserTardos
