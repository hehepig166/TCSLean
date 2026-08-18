/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
import TCSLean.MoserTardos.VariableModel

/-!
# Resampling step of the Moser–Tardos algorithm

This file defines the one-step transition of the truncated Moser–Tardos resampling
algorithm: the state counts how many rows each variable has consumed, `assign` reads the
table at the current rows, and `step` resamples one violated event whose variable rows are
all still available, carrying the picked event as a certificate. It also defines the
truncated run (`run`/`count`) and the stopping time `R` at which the run first has no
violated event, together with the padded execution log (`log`/`countLog`): the event
resampled at each integer time before `R`, and `none` at and after `R`.

## Main definitions

* `State N`: the state of the truncated run — for each variable `j : κ` the number of rows
  it has consumed, as a row index `Fin (N + 1)`.
* `assign`: the assignment determined by a state `c` on a table `ω` — variable `j` holds
  the value in row `c j` of the table (`ω ⟨j, c j⟩`, total by `c j : Fin (N + 1)`).
* `Avail`: the events that are currently violated and whose variable rows are all still
  available (`(c j : ℕ) < N`).
* `Payload`: the certificate carried by a step that resamples event `e` — `e` is violated
  under the current assignment and all its variable rows are still available.
* `step`: one step of the resampling algorithm — if some event is available, pick one via
  `pick`/`hpick`, advance the row counts of exactly its variables by one (the certificate
  supplies the `Fin` bound), and return the new state with the picked event; otherwise
  freeze.
* `run`: the truncated run of the resampling algorithm — entry `t : Fin (N + 1)` is the
  pair (counts *before* step `t`, event of step `t` as the certificate-carrying `Option`),
  built by `Fin.induction`; once the option is `none` the recursion freezes.
* `count`: the row counts before step `t` — the state component of `run ω t`.
* `Violated`: some event is violated at state `c` — the compressed concept behind the
  per-event predicate `assign ω c ∈ A i`.
* `NoViolation`: at (integer) time `t`, no event is violated by the assignment of the run's
  state before step `t` — the ℕ-typed ∃-`ht` predicate `R`'s `Nat.find` searches over.
* `R`: the stopping time — the least `t ≤ N` with no violated event, or `N` if the run
  stays violated through step `N`.
* `log`: the padded execution log — the event resampled at (integer) time `t`, or `none`
  once the run has reached the stopping time (the pinned `if t < R` form; see the
  declaration docstring).
* `countLog`: the number of times a log resampled event `i` — `#{t < N : Λ ω t = some i}`.

## Main results

* `step_fst_val_eq_of_mem`: when the step resampled event `e`, the row count of each
  variable of `e` advanced by exactly one.
* `step_fst_eq_of_not_mem`: variables outside `vbl e` keep their row counts.
* `step_fst_eq_of_none`: when no event is available the state freezes.
* `run_count_le`: the rows-never-run-out invariant — after `t` steps each variable has
  consumed at most `t` rows, so the availability guard never bites before `N` steps.
* `R_le`: the stopping time never exceeds `N`.
* `NoViolation_fin_iff`: the `Fin`-indexed form of `NoViolation` is definitionally the
  finite boolean combination `∀ i, assign ω (count ω t) ∉ A i`.
* `R_lt_N_iff`: `R < N` holds exactly when some proper time `t : Fin N` already has no
  violated event.
* `run_snd_eq_step`: the run's option at `t` is the step at the run's state before `t`.
* `run_snd_eq_some_of_Avail_ne`: an available event makes the run's option `some`.
* `run_step_of_lt_R`: before the stopping time the run takes a genuine step.
* `log_eq_none_of_R_le`: the log is `none` at and after the stopping time.
* `log_ne_none_iff_lt_R`: `log ω t ≠ none` exactly before the stopping time.

## Measurability

The `section Measurability` (second half of the file) carries the measurable-slice
library the counting identity and the main theorem consume — 18 public statements:

* `State.instMeasurableSpace`: the product measurable space on the state type.
* `measurable_assign`: the assignment `ω ↦ assign ω c` is measurable (per-coordinate
  `measurable_pi_lambda`/`measurable_pi_apply`).
* `measurableSet_assign_mem`: `{ω | assign ω c ∈ A i}` is measurable (preimage under
  `measurable_assign` + `hA`).
* `measurableSet_Avail_eq`: `{ω | Avail vbl A ω c = S}` is measurable (biInter over `i`
  + `by_cases i ∈ S` and the ω-free availability guard).
* `measurableSet_Avail_nonempty`: `{ω | (Avail vbl A ω c).Nonempty}` is measurable
  (biUnion over `i`).
* `measurableSet_step_fst_eq`: `{ω | (step vbl A pick hpick ω c).1 = c'}` is
  measurable (finite union over availability fibers `S`; the ω-free next-state
  predicate is the supporting `advance`).
* `count_succ_eq_step_fst`: the count at `t.succ` is the first component of the step at
  the count at `t` (Fin.induction unfold + `run_snd_eq_step`).
* `measurableSet_count_eq`: the count fibers `{ω | count vbl A pick hpick ω t = c}` are
  measurable (Fin.induction: constant base, step = finite union of fibers).
* `measurable_count`: the count at time `t` is measurable in the table.
* `NoViolation_mono`/`lt_R_iff`: the freeze monotonicity of `NoViolation` in
  `t ≤ s ≤ N`, and the `Fin`-time characterization `t.val < R ↔ t.val < N ∧ ∃ i,
  assign ω (count ω t) ∈ A i` (the `t.val < N` conjunct handles the `t = N = R`
  fallback corner).
* `measurableSet_NoViolation`/`measurableSet_lt_R`/`measurableSet_R_lt_N`/
  `measurableSet_R_eq`: the measurable stopping-time slices — no violation at `t`,
  `t < R`, `R < N`, and `{R = N} = {R < N}ᶜ` via `R_le`.
* `measurableSet_log_eq_some`: `{ω | log vbl A pick hpick ω t = some i}` is measurable —
  the hard core (finite union over count fibers `c` and availability fibers `S` of
  `{count ω t = c} ∩ {Avail ω c = ↑S} ∩ {t < R}` intersected with the ω-free
  pick-condition `pick ⟨↑S, hS⟩ = i`).
* `measurable_countLog`/`measurableSet_countLog_eq`: the padded-log count of event `i`
  is measurable in the table, and its level sets `{ω | countLog … ω i = k}` are
  measurable (preimage of the singleton `{k}`).

## References

The one-step transition follows the Moser–Tardos notes, §4 ([moserTardos2010]).
-/

set_option autoImplicit false
set_option pp.unicode.fun true

open MeasureTheory
open scoped BigOperators

universe u v

namespace TCSLean.MoserTardos

section Step

variable {ι : Type u}
variable {κ : Type u} [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

-- No declaration in this section needs `[Fintype κ]` or `[∀ j, MeasurableSpace (Ω j)]`
-- (none of the defs below uses them, and Lean's theorem auto-include would still add the
-- instance binders to every theorem whose header mentions `κ`/`Ω` — cf. the
-- `section OverlapGraph` omit in `VariableModel`), so omit them for clean signatures.
omit [Fintype κ]
omit [∀ j, MeasurableSpace (Ω j)]

/-- The state of the truncated run: for each variable `j`, the number of rows it has
consumed, i.e. how many times it has been resampled so far, as a row index `Fin (N + 1)`.
The `N + 1` rows match the table `ΩN N Ω`: a variable resampled at every one of `N` steps
reaches row `N` and must not overflow. -/
def State (N : ℕ) := κ → Fin (N + 1)

/-- The assignment determined by a state `c` on a table `ω`: variable `j` holds the value in
row `c j` of the table. The table is Sigma-indexed (`ΩN`), so the row is read as
`ω ⟨j, c j⟩` — total because `c j : Fin (N + 1)`, and `⟨j, c j⟩.1 = j` definitionally. -/
def assign (ω : ΩN N Ω) (c : State (κ := κ) N) : Π j, Ω j := fun j => ω ⟨j, c j⟩

/-- The events that are currently violated (`assign ω c ∈ A i`) and whose variable rows are
all still available (`(c j : ℕ) < N`). The availability guard exists only to keep `step`
total; by `run_count_le` (20.2) it never bites before `N` steps. The explicit `ℕ` coercion
is mandatory: mathlib v4.32.0 has no heterogeneous `LT (Fin n) ℕ` instance. -/
def Avail (ω : ΩN N Ω) (c : State (κ := κ) N) : Set ι :=
  {i | assign ω c ∈ A i ∧ ∀ j ∈ vbl i, (c j : ℕ) < N}

/-- The certificate carried by a step that resamples event `e`: `e` is violated under the
current assignment and all its variable rows are still available. Defeq to
`{e : ι // e ∈ Avail vbl A ω c}` (the `Avail` membership predicate is exactly this
predicate). -/
def Payload (ω : ΩN N Ω) (c : State N) :=
  {e : ι // assign ω c ∈ A e ∧ ∀ j ∈ vbl e, (c j : ℕ) < N}

/-- One step of the resampling algorithm: if some event is available (`Avail` nonempty),
pick one via `pick`/`hpick`, advance the row counts of exactly its variables by one (the
availability certificate supplies the `Fin` bound `Nat.succ_lt_succ (e.2.2 j hj)`), and
return the new state together with the picked event; otherwise freeze (`(c, none)`).
`classical` supplies the dite decidability, so no `[DecidableEq ι]`/`[DecidableEq κ]`
hypotheses are required. -/
noncomputable def step (ω : ΩN N Ω) (c : State (κ := κ) N) :
    State (κ := κ) N × Option (Payload vbl A ω c) := by
  classical
  exact
    if h : (Avail vbl A ω c).Nonempty then
      let e : Payload vbl A ω c :=
        ⟨pick ⟨Avail vbl A ω c, h⟩, hpick ⟨Avail vbl A ω c, h⟩⟩
      (fun j => if hj : j ∈ vbl e.1 then
          ⟨(c j : ℕ) + 1, Nat.succ_lt_succ (e.2.2 j hj)⟩
        else c j, some e)
    else (c, none)

/-- Step spec: when the step resampled event `e`, the row count of each variable of `e`
advanced by exactly one. (`if`-free conclusion, so no `Decidable` hypotheses.) -/
theorem step_fst_val_eq_of_mem {ω : ΩN N Ω} {c : State N} {e : Payload vbl A ω c} {j : κ}
    (h : (step vbl A pick hpick ω c).2 = some e) (hj : j ∈ vbl e.1) :
    (((step vbl A pick hpick ω c).1 j : Fin (N + 1)) : ℕ) = (c j : ℕ) + 1 := by
  unfold step at h ⊢
  split_ifs at h ⊢ with hAv
  · simp at h
    subst e
    simp [hj]

/-- Step spec: variables outside `vbl e` keep their row counts. -/
theorem step_fst_eq_of_not_mem {ω : ΩN N Ω} {c : State N} {e : Payload vbl A ω c} {j : κ}
    (h : (step vbl A pick hpick ω c).2 = some e) (hj : j ∉ vbl e.1) :
    (step vbl A pick hpick ω c).1 j = c j := by
  unfold step at h ⊢
  split_ifs at h ⊢ with hAv
  · simp at h
    subst e
    simp [hj]

/-- Step spec: when no event is available the state freezes. -/
theorem step_fst_eq_of_none {ω : ΩN N Ω} {c : State N}
    (h : (step vbl A pick hpick ω c).2 = none) :
    (step vbl A pick hpick ω c).1 = c := by
  unfold step at h ⊢
  split_ifs at h ⊢ with hAv
  · rfl

end Step

section Run

variable {ι : Type u}
variable {κ : Type u} [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

-- No declaration in this section needs `[Fintype κ]` or `[∀ j, MeasurableSpace (Ω j)]`,
-- so omit them for clean signatures (matching `section Step`).
omit [Fintype κ]
omit [∀ j, MeasurableSpace (Ω j)]

/-- The truncated run: entry `t` is the pair (counts *before* step `t`, event of step `t`),
carried as the dependent Sigma `Σ c, Option (Payload vbl A ω c)` because `Payload` is
indexed by the state `c`. Once the option is `none` the recursion freezes (the `match`
keeps the same `c`) — exactly "the algorithm stops". `Fin.induction` over `Fin (N + 1)`;
`classical` supplies the dite decidability (the section carries no `[DecidableEq κ]`). -/
noncomputable def run (ω : ΩN N Ω) :
    Fin (N + 1) → Σ c : State (κ := κ) N, Option (Payload vbl A ω c) := by
  classical
  exact Fin.induction
    (⟨fun _ => 0, (step vbl A pick hpick ω (fun _ => 0)).2⟩)
    (fun _ (rec : Σ c : State (κ := κ) N, Option (Payload vbl A ω c)) =>
      let c := rec.1
      let c' := match rec.2 with
        | none => c
        | some e => fun j => if hj : j ∈ vbl e.1 then
            ⟨(c j : ℕ) + 1, Nat.succ_lt_succ (e.2.2 j hj)⟩
          else c j
      ⟨c', (step vbl A pick hpick ω c').2⟩)

/-- The row counts before step `t`: the state component of `run ω t`. -/
noncomputable def count (ω : ΩN N Ω) (t : Fin (N + 1)) : State (κ := κ) N :=
  (run vbl A pick hpick ω t).1

/-- The rows-never-run-out invariant: after `t` steps each variable has consumed at most
`t` rows, so at any time `t < N` every violated event is available and the availability
guard of `step` never bites before `N` steps. -/
theorem run_count_le (ω : ΩN N Ω) (t : Fin (N + 1)) (j : κ) :
    ((count vbl A pick hpick ω t) j : ℕ) ≤ t.val := by
  classical
  induction t using Fin.induction with
  | zero => simp [count, run]
  | succ i ih =>
      rcases h : (run vbl A pick hpick ω i.castSucc).2 with _ | ⟨e, he⟩
      · simp [count, run] at h ⊢
        rw [h]
        simp
        simp [count] at ih
        exact Nat.le_trans ih (by simp)
      · simp [count, run] at h ⊢
        rw [h]
        by_cases hj : j ∈ vbl e
        · simp [hj]
          simp [count] at ih
          exact ih
        · simp [hj]
          simp [count] at ih
          exact Nat.le_trans ih (by simp)

end Run

section Stopping

variable {ι : Type u}
variable {κ : Type u} [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

-- No declaration in this section needs `[Fintype κ]` or `[∀ j, MeasurableSpace (Ω j)]`,
-- so omit them for clean signatures (matching `section Run`).
omit [Fintype κ]
omit [∀ j, MeasurableSpace (Ω j)]

/-- Some event is violated at state `c`: the compressed concept behind the per-event
predicate `assign ω c ∈ A i` (which stays the workhorse everywhere); consumed by 20.5's
prose and by `¬ Violated … ↔ ∀ i, …`. -/
def Violated (ω : ΩN N Ω) (c : State (κ := κ) N) : Prop := ∃ i, assign ω c ∈ A i

/-- At (integer) time `t`, no event is violated by the assignment of the run's state
before step `t`: the ℕ-typed ∃-`ht` predicate that `R`'s `Nat.find` searches over — the
`ht` witness carries `t ≤ N`, so `∃ t, NoViolation ω t` is exactly "some `t ≤ N` has no
violated event". -/
def NoViolation (ω : ΩN N Ω) (t : ℕ) : Prop :=
  ∃ ht : t < N + 1, ∀ i, assign ω (count vbl A pick hpick ω ⟨t, ht⟩) ∉ A i

/-- The stopping time: the least `t ≤ N` with no violated event, or `N` if the run stays
violated through step `N` (the fallback covers both "still violated at N" and the
row-exhausted-at-N state). `classical` supplies the dite decidability. -/
noncomputable def R (ω : ΩN N Ω) : ℕ := by
  classical
  exact if h : ∃ t : ℕ, NoViolation vbl A pick hpick ω t then Nat.find h else N

/-- The stopping time never exceeds `N`. -/
theorem R_le (ω : ΩN N Ω) : R vbl A pick hpick ω ≤ N := by
  classical
  by_cases h : ∃ t : ℕ, NoViolation vbl A pick hpick ω t
  · simp [R, h]
    rcases Nat.find_spec h with ⟨hlt, hv⟩
    exact ⟨Nat.find h, Nat.le_of_lt_succ hlt, ⟨hlt, hv⟩⟩
  · simp [R, h]

/-- Glue for 20.5: the Fin-indexed form of `NoViolation` is definitionally the finite
boolean combination `∀ i, assign ω (count ω t) ∉ A i` (`count ω ⟨t.val, ht⟩` and
`count ω t` are defeq — the `Fin.isLt` proofs are proof-irrelevant). -/
theorem NoViolation_fin_iff (ω : ΩN N Ω) {t : Fin (N + 1)} :
    NoViolation vbl A pick hpick ω t.val ↔
      ∀ i, assign ω (count vbl A pick hpick ω t) ∉ A i := by
  constructor
  · rintro ⟨ht, hnv⟩
    simpa using hnv
  · intro hnv
    exact ⟨t.isLt, by simpa using hnv⟩

/-- Glue for 20.5: `R < N` holds exactly when some proper time `t : Fin N` already has no
violated event (finite boolean combination free of `Nat.find`/classical). -/
theorem R_lt_N_iff (ω : ΩN N Ω) :
    R vbl A pick hpick ω < N ↔ ∃ t : Fin N, NoViolation vbl A pick hpick ω t.val := by
  classical
  constructor
  · intro hR
    unfold R at hR
    split_ifs at hR with h
    · exact ⟨⟨Nat.find h, hR⟩, Nat.find_spec h⟩
    · simp at hR
  · intro hnv
    rcases hnv with ⟨t, hnv⟩
    unfold R
    split_ifs with h
    · exact Nat.lt_of_le_of_lt (Nat.find_min' h hnv) t.isLt
    · exfalso
      exact h ⟨t.val, hnv⟩

end Stopping

section Log

variable {ι : Type u}
variable {κ : Type u} [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

-- No declaration in this section needs `[Fintype κ]` or `[∀ j, MeasurableSpace (Ω j)]`,
-- so omit them for clean signatures (matching `section Stopping`).
omit [Fintype κ]
omit [∀ j, MeasurableSpace (Ω j)]

/-- The defeq glue: the run's option at `t` is the step at the run's state before `t`.
Not `rfl` for a variable `t` (the `Fin.induction` match is stuck), but each case is `rfl`
after unfolding: `induction t using Fin.induction` + `simp [count, run]`. NOT `@[simp]`
(do not unfold `run`/`step` in the default simplifier). -/
theorem run_snd_eq_step (ω : ΩN N Ω) (t : Fin (N + 1)) :
    (run vbl A pick hpick ω t).2 =
      (step vbl A pick hpick ω (count vbl A pick hpick ω t)).2 := by
  induction t using Fin.induction <;> simp [count, run]

/-- An available event makes the run's option `some`. -/
theorem run_snd_eq_some_of_Avail_ne (ω : ΩN N Ω) {t : Fin (N + 1)} {i : ι}
    (hi : i ∈ Avail vbl A ω (count vbl A pick hpick ω t)) :
    ∃ e, (run vbl A pick hpick ω t).2 = some e := by
  let hne : (Avail vbl A ω (count vbl A pick hpick ω t)).Nonempty := ⟨i, hi⟩
  refine ⟨⟨pick ⟨Avail vbl A ω (count vbl A pick hpick ω t), hne⟩,
      hpick ⟨Avail vbl A ω (count vbl A pick hpick ω t), hne⟩⟩, ?_⟩
  rw [run_snd_eq_step vbl A pick hpick]
  unfold step
  rw [dif_pos hne]
  rfl

/-- The genuine-step lemma: before the stopping time, the run's option is `some`
(the inline `Fin` proof term is the derived `t < N + 1`). -/
theorem run_step_of_lt_R (ω : ΩN N Ω) {t : ℕ} (ht : t < R vbl A pick hpick ω) :
    ∃ e, (run vbl A pick hpick ω ⟨t, Nat.lt_of_lt_of_le ht
      (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))⟩).2 = some e := by
  classical
  have ht' : t < N + 1 := Nat.lt_of_lt_of_le ht
    (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))
  have hnv' : ¬ NoViolation vbl A pick hpick ω t := by
    unfold R at ht
    split_ifs at ht with h
    · exact Nat.find_min h ht
    · intro hn
      exact h ⟨t, hn⟩
  have hi' : ∃ i, assign ω (count vbl A pick hpick ω ⟨t, ht'⟩) ∈ A i := by
    unfold NoViolation at hnv'
    push Not at hnv'
    exact hnv' ht'
  have htN : t < N := Nat.lt_of_lt_of_le ht (R_le vbl A pick hpick ω)
  rcases hi' with ⟨i, hi⟩
  have hAvail : ∀ j ∈ vbl i, ((count vbl A pick hpick ω ⟨t, ht'⟩) j : ℕ) < N := by
    intro j hj
    exact Nat.lt_of_le_of_lt (run_count_le vbl A pick hpick ω ⟨t, ht'⟩ j) htN
  exact run_snd_eq_some_of_Avail_ne vbl A pick hpick ω ⟨hi, hAvail⟩

/-- The padded execution log: the event resampled at (integer) time `t`, or `none` once
the run has reached the stopping time. The `if t < R` form is load-bearing (NOT the
"read the run's option" form): at `t = R = N` in the fallback branch the run's option
can still be `some`, so the option-reading log would break `log_eq_none_of_R_le`. The
`Classical.choose` makes the `t < R` branch syntactically `some _`, so the pad lemmas
are one `rw` each. -/
noncomputable def log (ω : ΩN N Ω) (t : ℕ) : Option ι := by
  classical
  exact
    if h : t < R vbl A pick hpick ω then
      some ((Classical.choose (run_step_of_lt_R vbl A pick hpick ω h)).1)
    else none

/-- The log is `none` at and after the stopping time: `unfold log;
rw [dif_neg (Nat.not_lt_of_le ht)]`. -/
theorem log_eq_none_of_R_le (ω : ΩN N Ω) {t : ℕ} (ht : R vbl A pick hpick ω ≤ t) :
    log vbl A pick hpick ω t = none := by
  unfold log
  rw [dif_neg (Nat.not_lt_of_le ht)]

/-- The counting glue for 60.1/60.3: `log ω t ≠ none` exactly before the stopping time.
NOT `@[simp]` (deliberate — 60.1 rewrites explicitly). -/
theorem log_ne_none_iff_lt_R (ω : ΩN N Ω) {t : ℕ} :
    log vbl A pick hpick ω t ≠ none ↔ t < R vbl A pick hpick ω := by
  constructor
  · intro hne
    by_contra hlt
    exact hne (log_eq_none_of_R_le vbl A pick hpick ω (Nat.le_of_not_gt hlt))
  · intro ht
    unfold log
    rw [dif_pos ht]
    exact Option.some_ne_none _

/-- The number of times event `i` was resampled by the log `Λ`: survey B §1.1-exact.
The `[DecidableEq ι]` is an explicit binder (the sections carry none). -/
def countLog [DecidableEq ι] (Λ : ΩN N Ω → ℕ → Option ι) (ω : ΩN N Ω) (i : ι) : ℕ :=
  ((Finset.range N).filter fun t => Λ ω t = some i).card

end Log

section Measurability

variable {ι : Type u} [Fintype ι]
variable {κ : Type u} [Fintype κ]
variable {Ω : κ → Type v} [∀ j, MeasurableSpace (Ω j)]
variable {N : ℕ}
variable (vbl : ι → Finset κ)
variable (A : ι → Set (Π j, Ω j))
variable (hA : ∀ i, MeasurableSet (A i))
variable (pick : {S : Set ι // S.Nonempty} → ι)
variable (hpick : ∀ S, pick S ∈ S.1)

/-- The product measurable space on the state type. Needed because typeclass search does
not unfold the (semireducible) `def State` when synthesizing the instance argument of
`Measurable (fun ω => count … ω t)` (the `ΩN.instMeasurableSpace` precedent). -/
instance State.instMeasurableSpace (N : ℕ) : MeasurableSpace (State (κ := κ) N) := by
  dsimp [State]
  infer_instance

omit [Fintype κ] in
/-- The assignment at a fixed state `c` is measurable in the table `ω` (componentwise
measurability via `measurable_pi_lambda`/`measurable_pi_apply`). -/
theorem measurable_assign (c : State (κ := κ) N) :
    Measurable (fun ω : ΩN N Ω => assign ω c) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  exact measurable_pi_apply (⟨j, c j⟩ : Σ _ : κ, Fin (N + 1))

include hA in
omit [Fintype ι] [Fintype κ] in
/-- Membership of `assign ω c` in the measurable event `A i` is a measurable condition on
`ω` (preimage of `A i` under the measurable `assign`, using `hA`). -/
theorem measurableSet_assign_mem {i : ι} {c : State (κ := κ) N} :
    MeasurableSet {ω | assign ω c ∈ A i} := by
  exact (measurable_assign c) (hA i)

include hA in
omit [Fintype ι] in
/-- Per-event availability `i ∈ Avail vbl A ω c` is measurable in `ω`: under the ω-free
guard `∀ j ∈ vbl i, (c j : ℕ) < N` the set equals `{ω | assign ω c ∈ A i}`, otherwise it
is empty. -/
private lemma measurableSet_Avail_mem {c : State (κ := κ) N} (i : ι) :
    MeasurableSet {ω | i ∈ Avail vbl A ω c} := by
  classical
  by_cases hguard : ∀ j ∈ vbl i, (c j : ℕ) < N
  · rw [show {ω : ΩN N Ω | i ∈ Avail vbl A ω c} = {ω | assign ω c ∈ A i} from by
      ext ω
      change (assign ω c ∈ A i ∧ ∀ j ∈ vbl i, (c j : ℕ) < N) ↔ assign ω c ∈ A i
      exact ⟨fun h => h.1, fun h => ⟨h, hguard⟩⟩]
    exact measurableSet_assign_mem (A := A) (hA := hA)
  · rw [show {ω : ΩN N Ω | i ∈ Avail vbl A ω c} = (∅ : Set (ΩN N Ω)) from by
      ext ω
      change (assign ω c ∈ A i ∧ ∀ j ∈ vbl i, (c j : ℕ) < N) ↔ False
      exact ⟨fun h => hguard h.2, fun h => h.elim⟩]
    exact MeasurableSet.empty

include hA in
/-- The set of tables where the available-event set equals `S` is measurable: a biInter
over `i` with `by_cases` on `i ∈ S`, combined with the ω-free availability guard
`∀ j ∈ vbl i, (c j : ℕ) < N`. -/
theorem measurableSet_Avail_eq {c : State (κ := κ) N} (S : Finset ι) :
    MeasurableSet {ω | Avail vbl A ω c = S} := by
  classical
  have hset : {ω : ΩN N Ω | Avail vbl A ω c = S} =
      (⋂ i : {i // i ∈ S}, {ω : ΩN N Ω | i.1 ∈ Avail vbl A ω c}) ∩
        (⋂ i : {i // i ∉ S}, {ω : ΩN N Ω | i.1 ∉ Avail vbl A ω c}) := by
    ext ω
    constructor
    · intro h
      constructor
      · rw [Set.mem_iInter]
        intro i
        change ↑i ∈ Avail vbl A ω c
        rw [h]
        simp
      · rw [Set.mem_iInter]
        intro i hiAv
        rw [h] at hiAv
        exact i.2 (by simpa using hiAv)
    · intro h
      have h1 : ω ∈ ⋂ i : {i // i ∈ S}, {ω : ΩN N Ω | i.1 ∈ Avail vbl A ω c} := h.1
      have h2 : ω ∈ ⋂ i : {i // i ∉ S}, {ω : ΩN N Ω | i.1 ∉ Avail vbl A ω c} := h.2
      rw [Set.mem_iInter] at h1 h2
      ext i
      by_cases hi : i ∈ S
      · exact ⟨fun _ => hi, fun _ => by
          change (⟨i, hi⟩ : {i // i ∈ S}).1 ∈ Avail vbl A ω c
          simpa using h1 ⟨i, hi⟩⟩
      · refine ⟨fun hiAv => False.elim ((h2 ⟨i, hi⟩) hiAv), fun hiS => False.elim (hi hiS)⟩
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · exact MeasurableSet.iInter (fun i : {i // i ∈ S} =>
      measurableSet_Avail_mem (vbl := vbl) (A := A) (hA := hA) (c := c) i.1)
  · exact MeasurableSet.iInter (fun i : {i // i ∉ S} =>
      (measurableSet_Avail_mem (vbl := vbl) (A := A) (hA := hA) (c := c) i.1).compl)

include hA in
/-- The set of tables where some event is available is measurable: a biUnion over `i` of
the per-event availability conditions. -/
theorem measurableSet_Avail_nonempty {c : State (κ := κ) N} :
    MeasurableSet {ω | (Avail vbl A ω c).Nonempty} := by
  classical
  have hset : {ω : ΩN N Ω | (Avail vbl A ω c).Nonempty} =
      ⋃ i ∈ (Finset.univ : Finset ι), {ω : ΩN N Ω | i ∈ Avail vbl A ω c} := by
    ext ω
    constructor
    · intro h
      rcases h with ⟨i, hi⟩
      rw [Set.mem_iUnion]
      exact ⟨i, by rw [Set.mem_iUnion]; exact ⟨Finset.mem_univ i, hi⟩⟩
    · intro h
      rw [Set.mem_iUnion] at h
      rcases h with ⟨i, hi⟩
      rw [Set.mem_iUnion] at hi
      rcases hi with ⟨_, hiAv⟩
      exact ⟨i, hiAv⟩
  rw [hset]
  exact Finset.measurableSet_biUnion (s := Finset.univ)
    (fun i _ => measurableSet_Avail_mem (vbl := vbl) (A := A) (hA := hA) i)

/-- ω-free advance condition: the state `c'` is `c` advanced by event `i` (every variable
of `i` advanced by one row, all others unchanged), compared at the level of row indices so
that no availability certificate is needed. -/
noncomputable def advance (c c' : State (κ := κ) N) (i : ι) : Prop := by
  classical
  exact ∀ j, if hj : j ∈ vbl i then (c j : ℕ) + 1 = (c' j : ℕ) else c j = c' j

include hA in
/-- The set of tables where the step's next state is `c'` is measurable: a finite union
over availability fibers `S` with the ω-free advance-if definition of the next state. -/
theorem measurableSet_step_fst_eq {c c' : State (κ := κ) N} :
    MeasurableSet {ω | (step vbl A pick hpick ω c).1 = c'} := by
  classical
  have hset : {ω : ΩN N Ω | (step vbl A pick hpick ω c).1 = c'} =
      ({ω : ΩN N Ω | ¬ (Avail vbl A ω c).Nonempty} ∩ {ω : ΩN N Ω | c = c'}) ∪
        (⋃ S : Finset ι,
          ({ω : ΩN N Ω | Avail vbl A ω c = S} ∩
            (if hS : (↑S : Set ι).Nonempty then
              (if advance vbl c c' (pick ⟨↑S, hS⟩) then (Set.univ : Set (ΩN N Ω)) else ∅)
            else ∅))) := by
    ext ω
    constructor
    · intro h
      by_cases havail : (Avail vbl A ω c).Nonempty
      · right
        rw [Set.mem_iUnion]
        let S₀ : Finset ι := Finset.univ.filter (fun i => i ∈ Avail vbl A ω c)
        refine ⟨S₀, ?_⟩
        constructor
        · change Avail vbl A ω c = ↑S₀
          ext i
          simp [S₀]
        · have hS : (↑S₀ : Set ι).Nonempty := by
            rwa [show ↑S₀ = Avail vbl A ω c from by ext i; simp [S₀]]
          rw [dif_pos hS]
          by_cases hadv : advance vbl c c' (pick ⟨↑S₀, hS⟩)
          · rw [if_pos hadv]
            exact Set.mem_univ ω
          · exfalso
            apply hadv
            intro j
            by_cases hj : j ∈ vbl (pick ⟨↑S₀, hS⟩)
            · rw [dif_pos hj]
              let e : Payload vbl A ω c :=
                ⟨pick ⟨Avail vbl A ω c, havail⟩, hpick ⟨Avail vbl A ω c, havail⟩⟩
              have hsome : (step vbl A pick hpick ω c).2 = some e := by
                unfold step
                rw [dif_pos havail]
              have hsub : (⟨Avail vbl A ω c, havail⟩ : {S : Set ι // S.Nonempty}) =
          ⟨↑S₀, hS⟩ :=
                Subtype.ext (show Avail vbl A ω c = ↑S₀ from by ext i; simp [S₀])
              have hi₀ : pick ⟨Avail vbl A ω c, havail⟩ = pick ⟨↑S₀, hS⟩ :=
        congrArg pick hsub
              have hj' : j ∈ vbl e.1 := by simpa [e, hi₀] using hj
              calc
                (c j : ℕ) + 1 = (((step vbl A pick hpick ω c).1 j : Fin (N + 1)) : ℕ) :=
                  (step_fst_val_eq_of_mem (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
                    hsome hj').symm
                _ = (c' j : ℕ) := congrArg (fun x : Fin (N + 1) => (x : ℕ)) (congrFun h j)
            · rw [dif_neg hj]
              let e : Payload vbl A ω c :=
                ⟨pick ⟨Avail vbl A ω c, havail⟩, hpick ⟨Avail vbl A ω c, havail⟩⟩
              have hsome : (step vbl A pick hpick ω c).2 = some e := by
                unfold step
                rw [dif_pos havail]
              have hsub : (⟨Avail vbl A ω c, havail⟩ : {S : Set ι // S.Nonempty}) =
          ⟨↑S₀, hS⟩ :=
                Subtype.ext (show Avail vbl A ω c = ↑S₀ from by ext i; simp [S₀])
              have hi₀ : pick ⟨Avail vbl A ω c, havail⟩ = pick ⟨↑S₀, hS⟩ :=
        congrArg pick hsub
              have hj' : j ∉ vbl e.1 := by simpa [e, hi₀] using hj
              calc
                c j = (step vbl A pick hpick ω c).1 j :=
                  (step_fst_eq_of_not_mem (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
                    hsome hj').symm
                _ = c' j := congrFun h j
      · left
        constructor
        · simpa using havail
        · change c = c'
          have hnone : (step vbl A pick hpick ω c).2 = none := by
            unfold step
            rw [dif_neg havail]
          exact (step_fst_eq_of_none (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
            hnone).symm.trans h
    · intro hω
      rw [Set.mem_union] at hω
      rcases hω with hω | hω
      · rcases hω with ⟨hnotAv, hcc'⟩
        change ¬ (Avail vbl A ω c).Nonempty at hnotAv
        change c = c' at hcc'
        have hnone : (step vbl A pick hpick ω c).2 = none := by
          unfold step
          rw [dif_neg hnotAv]
        exact (step_fst_eq_of_none (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
          hnone).trans hcc'
      · rw [Set.mem_iUnion] at hω
        rcases hω with ⟨S, hSfib, hSif⟩
        change Avail vbl A ω c = ↑S at hSfib
        by_cases hS : (↑S : Set ι).Nonempty
        · rw [dif_pos hS] at hSif
          by_cases hadv : advance vbl c c' (pick ⟨↑S, hS⟩)
          · have havail : (Avail vbl A ω c).Nonempty := by
              rcases hS with ⟨i, hi⟩
              exact ⟨i, by simpa [← hSfib] using hi⟩
            have hsome : (step vbl A pick hpick ω c).2 = some
                (⟨pick ⟨Avail vbl A ω c, havail⟩, hpick ⟨Avail vbl A ω c, havail⟩⟩ :
                  Payload vbl A ω c) := by
              unfold step
              rw [dif_pos havail]
              rfl
            have hsub : (⟨Avail vbl A ω c, havail⟩ : {S : Set ι // S.Nonempty}) =
          ⟨↑S, hS⟩ :=
              Subtype.ext hSfib
            have hi₀ : pick ⟨Avail vbl A ω c, havail⟩ = pick ⟨↑S, hS⟩ :=
        congrArg pick hsub
            funext j
            by_cases hj : j ∈ vbl (pick ⟨↑S, hS⟩)
            · apply Fin.ext
              have hj' : j ∈ vbl (pick ⟨Avail vbl A ω c, havail⟩) := by
                simpa [hi₀] using hj
              have hval := step_fst_val_eq_of_mem (vbl := vbl) (A := A) (pick := pick)
                (hpick := hpick) hsome hj'
              have hadvj : (c j : ℕ) + 1 = (c' j : ℕ) := by
                have hadvj' := hadv j
                rw [dif_pos hj] at hadvj'
                exact hadvj'
              calc
                (((step vbl A pick hpick ω c).1 j : Fin (N + 1)) : ℕ) = (c j : ℕ) + 1 := hval
                _ = (c' j : ℕ) := hadvj
            · have hj' : j ∉ vbl (pick ⟨Avail vbl A ω c, havail⟩) := by
                simpa [hi₀] using hj
              have hnm := step_fst_eq_of_not_mem (vbl := vbl) (A := A) (pick := pick)
                (hpick := hpick) hsome hj'
              have hadvj : c j = c' j := by
                have hadvj' := hadv j
                rw [dif_neg hj] at hadvj'
                exact hadvj'
              exact hnm.trans hadvj
          · exfalso
            rw [if_neg hadv] at hSif
            exact hSif
        · exfalso
          rw [dif_neg hS] at hSif
          exact hSif
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · refine ((measurableSet_Avail_nonempty (vbl := vbl) (A := A) (hA := hA)
      (c := c)).compl).inter ?_
    by_cases hcc' : c = c'
    · have hset' : {ω : ΩN N Ω | c = c'} = (Set.univ : Set (ΩN N Ω)) := by
        ext ω
        simp [hcc']
      rw [hset']
      exact MeasurableSet.univ
    · have hset' : {ω : ΩN N Ω | c = c'} = (∅ : Set (ΩN N Ω)) := by
        ext ω
        simp [hcc']
      rw [hset']
      exact MeasurableSet.empty
  · refine MeasurableSet.iUnion (fun S => ?_)
    refine (measurableSet_Avail_eq (vbl := vbl) (A := A) (hA := hA) (c := c) S).inter ?_
    by_cases hS : (↑S : Set ι).Nonempty
    · by_cases hadv : advance vbl c c' (pick ⟨↑S, hS⟩)
      · rw [dif_pos hS, if_pos hadv]
        exact MeasurableSet.univ
      · rw [dif_pos hS, if_neg hadv]
        exact MeasurableSet.empty
    · rw [dif_neg hS]
      exact MeasurableSet.empty

omit [Fintype ι] [Fintype κ] [∀ j, MeasurableSpace (Ω j)] in
/-- The count at `t.succ` is the first component of the step at the count at `t`
(Fin.induction unfold + `run_snd_eq_step`). -/
theorem count_succ_eq_step_fst (ω : ΩN N Ω) {t : Fin N} :
    count vbl A pick hpick ω t.succ =
      (step vbl A pick hpick ω (count vbl A pick hpick ω t.castSucc)).1 := by
  classical
  have hmatch :
      (step vbl A pick hpick ω (count vbl A pick hpick ω t.castSucc)).1 =
        match (step vbl A pick hpick ω
          (count vbl A pick hpick ω t.castSucc)).2 with
        | none => count vbl A pick hpick ω t.castSucc
        | some e => fun j => if hj : j ∈ vbl e.1 then
            ⟨((count vbl A pick hpick ω t.castSucc) j : ℕ) + 1, Nat.succ_lt_succ (e.2.2 j hj)⟩
          else count vbl A pick hpick ω t.castSucc j := by
    unfold step
    split_ifs with h
    · simp
    · simp
  rw [hmatch]
  rcases hopt : (run vbl A pick hpick ω t.castSucc).2 with _ | e
  · have hstep : (step vbl A pick hpick ω (count vbl A pick hpick ω t.castSucc)).2 = none := by
      rw [← run_snd_eq_step vbl A pick hpick ω t.castSucc]
      exact hopt
    rw [hstep]
    simp only [count, run]
    rw [Fin.induction_succ]
    erw [hopt]
  · have hstep : (step vbl A pick hpick ω (count vbl A pick hpick ω t.castSucc)).2 = some e := by
      rw [← run_snd_eq_step vbl A pick hpick ω t.castSucc]
      exact hopt
    rw [hstep]
    simp only [count, run]
    rw [Fin.induction_succ]
    erw [hopt]

include hA in
/-- The set of tables where the count at `t` is `c` is measurable (Fin.induction: base
constant; step = finite union over `c`-fibers and availability fibers). -/
theorem measurableSet_count_eq {t : Fin (N + 1)} {c : State (κ := κ) N} :
    MeasurableSet {ω | count vbl A pick hpick ω t = c} := by
  classical
  revert c
  induction t using Fin.induction with
  | zero =>
      intro c
      have hset : {ω : ΩN N Ω | count vbl A pick hpick ω 0 = c} =
          (if (fun _ : κ => (0 : Fin (N + 1))) = c then (Set.univ : Set (ΩN N Ω)) else ∅) := by
        ext ω
        by_cases hc : (fun _ : κ => (0 : Fin (N + 1))) = c
        · simp [hc, count, run]
        · simp [hc, count, run]
          exact hc
      rw [hset]
      by_cases hc : (fun _ : κ => (0 : Fin (N + 1))) = c
      · rw [if_pos hc]
        exact MeasurableSet.univ
      · rw [if_neg hc]
        exact MeasurableSet.empty
  | succ i ih =>
      intro c
      have hset : {ω : ΩN N Ω | count vbl A pick hpick ω i.succ = c} =
          ⋃ c₀ : State (κ := κ) N,
            ({ω : ΩN N Ω | count vbl A pick hpick ω i.castSucc = c₀} ∩
              {ω : ΩN N Ω | (step vbl A pick hpick ω c₀).1 = c}) := by
        ext ω
        constructor
        · intro h
          change count vbl A pick hpick ω i.succ = c at h
          rw [Set.mem_iUnion]
          refine ⟨count vbl A pick hpick ω i.castSucc, ?_⟩
          constructor
          · rfl
          · change (step vbl A pick hpick ω (count vbl A pick hpick ω i.castSucc)).1 = c
            exact (count_succ_eq_step_fst (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
              ω).symm.trans h
        · intro h
          rw [Set.mem_iUnion] at h
          rcases h with ⟨c₀, hc₀, hstep⟩
          change count vbl A pick hpick ω i.castSucc = c₀ at hc₀
          change (step vbl A pick hpick ω c₀).1 = c at hstep
          change count vbl A pick hpick ω i.succ = c
          rw [count_succ_eq_step_fst (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω]
          rw [hc₀, hstep]
      rw [hset]
      haveI : Fintype (State (κ := κ) N) := by
        dsimp [State]
        infer_instance
      haveI : Finite (State (κ := κ) N) := Finite.of_fintype (State (κ := κ) N)
      haveI : Countable (State (κ := κ) N) := Finite.to_countable
      refine MeasurableSet.iUnion (fun c₀ => ?_)
      exact (ih (c := c₀)).inter (measurableSet_step_fst_eq (vbl := vbl) (A := A)
        (pick := pick) (hpick := hpick) (hA := hA) (c := c₀) (c' := c))

include hA in
/-- The count at time `t` is measurable in the table (`measurable_pi_iff` + finite unions
of the fibers). -/
theorem measurable_count {t : Fin (N + 1)} :
    Measurable (fun ω => count vbl A pick hpick ω t) := by
  classical
  refine measurable_pi_lambda _ (fun j => ?_)
  haveI : Finite (Fin (N + 1)) := Finite.of_fintype (Fin (N + 1))
  haveI : Countable (Fin (N + 1)) := Finite.to_countable
  refine measurable_to_countable' (fun k => ?_)
  have hfiber : MeasurableSet {ω : ΩN N Ω | (count vbl A pick hpick ω t) j = k} := by
    have hset : {ω : ΩN N Ω | (count vbl A pick hpick ω t) j = k} =
        ⋃ c : State (κ := κ) N,
          ({ω : ΩN N Ω | count vbl A pick hpick ω t = c} ∩
            (if c j = k then (Set.univ : Set (ΩN N Ω)) else ∅)) := by
      ext ω
      constructor
      · intro h
        change (count vbl A pick hpick ω t) j = k at h
        rw [Set.mem_iUnion]
        refine ⟨count vbl A pick hpick ω t, ?_⟩
        constructor
        · rfl
        · by_cases hjk : (count vbl A pick hpick ω t) j = k
          · rw [if_pos hjk]
            exact Set.mem_univ ω
          · exfalso
            exact hjk h
      · intro h
        rw [Set.mem_iUnion] at h
        rcases h with ⟨c₀, hc₀, hif⟩
        change count vbl A pick hpick ω t = c₀ at hc₀
        change (count vbl A pick hpick ω t) j = k
        by_cases hjk : c₀ j = k
        · simp [hc₀, hjk]
        · exfalso
          rw [if_neg hjk] at hif
          exact hif
    rw [hset]
    haveI : Fintype (State (κ := κ) N) := by
      dsimp [State]
      infer_instance
    haveI : Finite (State (κ := κ) N) := Finite.of_fintype (State (κ := κ) N)
    haveI : Countable (State (κ := κ) N) := Finite.to_countable
    refine MeasurableSet.iUnion (fun c₀ => ?_)
    refine (measurableSet_count_eq (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
      (hA := hA) (t := t) (c := c₀)).inter ?_
    by_cases hjk : c₀ j = k
    · rw [if_pos hjk]
      exact MeasurableSet.univ
    · rw [if_neg hjk]
      exact MeasurableSet.empty
  change MeasurableSet {c : ΩN N Ω |
    (count vbl A pick hpick c t) j ∈ ({k} : Set (Fin (N + 1)))}
  simpa only [Set.mem_singleton_iff] using hfiber

omit [Fintype ι] [Fintype κ] [∀ j, MeasurableSpace (Ω j)] in
/-- The freeze lemma: once no event is violated at time `t`, the run stays there (the
run's option `none` freezes the state), so `NoViolation` is monotone in `t ≤ s ≤ N`.
Load-bearing for `lt_R_iff`'s backward direction. -/
theorem NoViolation_mono {ω : ΩN N Ω} {t s : ℕ} (ht : NoViolation vbl A pick hpick ω t)
    (hts : t ≤ s) (hs : s ≤ N) : NoViolation vbl A pick hpick ω s := by
  classical
  have hfreeze_step {u : ℕ} (hu : u < N) :
      NoViolation vbl A pick hpick ω u →
        NoViolation vbl A pick hpick ω (u + 1) := by
    intro hnvu
    rcases hnvu with ⟨hu1, hnv⟩
    let c : State (κ := κ) N := count vbl A pick hpick ω ⟨u, hu1⟩
    have hnv' : ∀ i, assign ω c ∉ A i := by
      intro i
      change assign ω (count vbl A pick hpick ω ⟨u, hu1⟩) ∉ A i
      exact hnv i
    have havail : ¬ (Avail vbl A ω c).Nonempty := by
      intro h
      rcases h with ⟨i, hi⟩
      exact hnv' i hi.1
    have hnone : (step vbl A pick hpick ω c).2 = none := by
      unfold step
      rw [dif_neg havail]
    have hfst : (step vbl A pick hpick ω c).1 = c :=
      step_fst_eq_of_none (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) hnone
    refine ⟨Nat.succ_lt_succ hu, ?_⟩
    intro i
    have hcount : count vbl A pick hpick ω ⟨u + 1, Nat.succ_lt_succ hu⟩ = c := by
      dsimp [c]
      erw [count_succ_eq_step_fst (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
        ω (t := ⟨u, hu⟩)]
      exact hfst
    rw [hcount]
    exact hnv' i
  have hiter : ∀ k : ℕ, t + k ≤ N → NoViolation vbl A pick hpick ω (t + k) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using ht
    | succ k ih =>
        intro hN
        have hlt : t + k < N := by omega
        exact hfreeze_step hlt (ih (Nat.le_of_lt hlt))
  rcases Nat.exists_eq_add_of_le hts with ⟨k, rfl⟩
  exact hiter k hs

omit [Fintype ι] [Fintype κ] [∀ j, MeasurableSpace (Ω j)] in
/-- Before the stopping time, some event is violated at the current count; conversely a
violated event before `N` forces `R` past `t` (forward: `run_step_of_lt_R`'s violation
witness; backward: `NoViolation_mono` + `R`/`Nat.find_min`). The `t.val < N` conjunct
handles the `t = N = R` fallback corner where the equivalence fails. -/
theorem lt_R_iff {ω : ΩN N Ω} {t : Fin (N + 1)} :
    t.val < R vbl A pick hpick ω ↔
      t.val < N ∧ ∃ i, assign ω (count vbl A pick hpick ω t) ∈ A i := by
  classical
  constructor
  · intro htR
    constructor
    · exact Nat.lt_of_lt_of_le htR (R_le vbl A pick hpick ω)
    · rcases run_step_of_lt_R (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω htR
        with ⟨e, _⟩
      exact ⟨e.1, e.2.1⟩
  · rintro ⟨htN, i, hi⟩
    by_cases hfind : ∃ t : ℕ, NoViolation vbl A pick hpick ω t
    · simp [R, hfind]
      intro m hm hnov
      have hnov' : NoViolation vbl A pick hpick ω t.val :=
        NoViolation_mono (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
          hnov hm (Nat.le_of_lt htN)
      rcases hnov' with ⟨_, hnov'⟩
      exact hnov' i hi
    · simp [R, hfind]
      exact htN

include hA in
/-- The set of tables with no violation at time `t` is measurable (`NoViolation_fin_iff` +
union over states `c` ∩ intersection over `i` of complements of the membership sets). -/
theorem measurableSet_NoViolation {t : Fin (N + 1)} :
    MeasurableSet {ω : ΩN N Ω | NoViolation vbl A pick hpick ω t.val} := by
  classical
  have hset : {ω : ΩN N Ω | NoViolation vbl A pick hpick ω t.val} =
      ⋂ i : ι, (⋃ c : State (κ := κ) N,
        ({ω : ΩN N Ω | count vbl A pick hpick ω t = c} ∩
          {ω : ΩN N Ω | assign ω c ∈ A i}))ᶜ := by
    ext ω
    constructor
    · intro h
      rw [Set.mem_iInter]
      intro i
      have hiff := (NoViolation_fin_iff (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
        ω (t := t)).mp h
      rw [Set.mem_compl_iff]
      intro hU
      rw [Set.mem_iUnion] at hU
      rcases hU with ⟨c, hci⟩
      change count vbl A pick hpick ω t = c ∧ assign ω c ∈ A i at hci
      rcases hci with ⟨hcount, hi⟩
      exact hiff i (by rw [hcount]; exact hi)
    · intro h
      rw [Set.mem_iInter] at h
      refine (NoViolation_fin_iff (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
        ω (t := t)).mpr ?_
      intro i
      have hi : ω ∈ (⋃ c : State (κ := κ) N,
          {ω : ΩN N Ω | count vbl A pick hpick ω t = c} ∩
            {ω : ΩN N Ω | assign ω c ∈ A i})ᶜ := h i
      rw [Set.mem_compl_iff] at hi
      intro hmem
      exact hi (by
        rw [Set.mem_iUnion]
        refine ⟨count vbl A pick hpick ω t, ?_⟩
        constructor
        · rfl
        · exact hmem)
  rw [hset]
  haveI : Finite ι := Finite.of_fintype ι
  haveI : Countable ι := Finite.to_countable
  refine MeasurableSet.iInter (fun i => ?_)
  haveI : Fintype (State (κ := κ) N) := by
    dsimp [State]
    infer_instance
  haveI : Finite (State (κ := κ) N) := Finite.of_fintype (State (κ := κ) N)
  haveI : Countable (State (κ := κ) N) := Finite.to_countable
  exact (MeasurableSet.iUnion (fun c =>
    (measurableSet_count_eq (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) (hA := hA)
      (t := t) (c := c)).inter
      (measurableSet_assign_mem (A := A) (hA := hA) (i := i) (c := c)))).compl

include hA in
/-- The set of tables with `t < R` is measurable (via `lt_R_iff` + decomposition over
states `c`). -/
theorem measurableSet_lt_R {t : Fin (N + 1)} :
    MeasurableSet {ω : ΩN N Ω | t.val < R vbl A pick hpick ω} := by
  classical
  have hset : {ω : ΩN N Ω | t.val < R vbl A pick hpick ω} =
      {ω : ΩN N Ω | t.val < N} ∩
        (⋃ c : State (κ := κ) N, ⋃ i : ι,
          {ω : ΩN N Ω | count vbl A pick hpick ω t = c} ∩
            {ω : ΩN N Ω | assign ω c ∈ A i}) := by
    ext ω
    constructor
    · intro h
      have hiff := (lt_R_iff (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
        (ω := ω) (t := t)).mp h
      rcases hiff with ⟨htN, i, hi⟩
      rw [Set.mem_inter_iff]
      constructor
      · exact htN
      · rw [Set.mem_iUnion]
        refine ⟨count vbl A pick hpick ω t, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨i, ?_⟩
        constructor
        · rfl
        · exact hi
    · intro h
      rw [Set.mem_inter_iff] at h
      rw [Set.mem_iUnion] at h
      rcases h with ⟨htN, hU⟩
      rcases hU with ⟨c, hc⟩
      rw [Set.mem_iUnion] at hc
      rcases hc with ⟨i, hci⟩
      change count vbl A pick hpick ω t = c ∧ assign ω c ∈ A i at hci
      rcases hci with ⟨hcount, hi⟩
      exact (lt_R_iff (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
        (ω := ω) (t := t)).mpr ⟨htN, i, by rw [hcount]; exact hi⟩
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · have hsetN : {ω : ΩN N Ω | t.val < N} =
        (if t.val < N then (Set.univ : Set (ΩN N Ω)) else ∅) := by
      ext ω
      by_cases htN : t.val < N <;> simp [htN]
    rw [hsetN]
    by_cases htN : t.val < N
    · rw [if_pos htN]
      exact MeasurableSet.univ
    · rw [if_neg htN]
      exact MeasurableSet.empty
  · haveI : Fintype (State (κ := κ) N) := by
      dsimp [State]
      infer_instance
    haveI : Finite (State (κ := κ) N) := Finite.of_fintype (State (κ := κ) N)
    haveI : Countable (State (κ := κ) N) := Finite.to_countable
    refine MeasurableSet.iUnion (fun c => ?_)
    haveI : Finite ι := Finite.of_fintype ι
    haveI : Countable ι := Finite.to_countable
    refine MeasurableSet.iUnion (fun i => ?_)
    exact (measurableSet_count_eq (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
      (hA := hA) (t := t) (c := c)).inter
      (measurableSet_assign_mem (A := A) (hA := hA) (i := i) (c := c))

include hA in
/-- The set of tables where `R < N` is measurable (`R_lt_N_iff` + biUnion over `Fin N` of
the NoViolation sets). -/
theorem measurableSet_R_lt_N :
    MeasurableSet {ω : ΩN N Ω | R vbl A pick hpick ω < N} := by
  classical
  have hset : {ω : ΩN N Ω | R vbl A pick hpick ω < N} =
      ⋃ t : Fin (N + 1), ({ω : ΩN N Ω | t.val < N} ∩
        {ω : ΩN N Ω | NoViolation vbl A pick hpick ω t.val}) := by
    ext ω
    constructor
    · intro h
      rcases (R_lt_N_iff (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω).mp h
        with ⟨t, hnv⟩
      rw [Set.mem_iUnion]
      refine ⟨t.castSucc, ?_⟩
      rw [Set.mem_inter_iff]
      constructor
      · exact t.isLt
      · exact hnv
    · intro h
      rw [Set.mem_iUnion] at h
      rcases h with ⟨t, ht⟩
      rw [Set.mem_inter_iff] at ht
      rcases ht with ⟨htN, hnv⟩
      exact (R_lt_N_iff (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω).mpr
        ⟨⟨t.val, htN⟩, by simpa using hnv⟩
  rw [hset]
  haveI : Finite (Fin (N + 1)) := Finite.of_fintype (Fin (N + 1))
  haveI : Countable (Fin (N + 1)) := Finite.to_countable
  refine MeasurableSet.iUnion (fun t : Fin (N + 1) => ?_)
  refine MeasurableSet.inter ?_ ?_
  · have hsetN : {ω : ΩN N Ω | t.val < N} =
        (if t.val < N then (Set.univ : Set (ΩN N Ω)) else ∅) := by
      ext ω
      by_cases htN : t.val < N <;> simp [htN]
    rw [hsetN]
    by_cases htN : t.val < N
    · rw [if_pos htN]
      exact MeasurableSet.univ
    · rw [if_neg htN]
      exact MeasurableSet.empty
  · exact measurableSet_NoViolation (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
      (hA := hA) (t := t)

include hA in
/-- The set of tables where `R = N` is measurable: `{R = N} = {R < N}ᶜ` via `R_le`. -/
theorem measurableSet_R_eq : MeasurableSet {ω : ΩN N Ω | R vbl A pick hpick ω = N} := by
  classical
  have hset : {ω : ΩN N Ω | R vbl A pick hpick ω = N} =
      ({ω : ΩN N Ω | R vbl A pick hpick ω < N})ᶜ := by
    ext ω
    constructor
    · intro h
      rw [Set.mem_compl_iff]
      intro hlt
      change R vbl A pick hpick ω < N at hlt
      rw [h] at hlt
      exact (Nat.lt_irrefl N hlt).elim
    · intro h
      rw [Set.mem_compl_iff] at h
      change ¬ R vbl A pick hpick ω < N at h
      exact Nat.le_antisymm (R_le vbl A pick hpick ω) (Nat.le_of_not_gt h)
  rw [hset]
  exact (measurableSet_R_lt_N (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
    (hA := hA)).compl

include hA in
/-- The set of tables where the log resampled `i` at time `t` is measurable: unfold
`log`'s `dif` to `{ω | t < R ω ∧ (Classical.choose (run_step_of_lt_R … h)).1 = i}`, then a
finite union over states `c` and availability finsets `S` of
`{count ω t = c} ∩ {Avail ω c = ↑S} ∩ {t < R ω}` intersected with the ω-free pick
condition `pick ⟨↑S, hS⟩ = i` (option-singleton + subtype ext for the choose equality). -/
theorem measurableSet_log_eq_some {t : Fin (N + 1)} {i : ι} :
    MeasurableSet {ω : ΩN N Ω | log vbl A pick hpick ω t.val = some i} := by
  classical
  have hset : {ω : ΩN N Ω | log vbl A pick hpick ω t.val = some i} =
      ({ω : ΩN N Ω | t.val < R vbl A pick hpick ω} ∩
        ⋃ c : State (κ := κ) N, ⋃ S : Finset ι,
          ({ω : ΩN N Ω | count vbl A pick hpick ω t = c} ∩
            {ω : ΩN N Ω | Avail vbl A ω c = S} ∩
            (if hS : (↑S : Set ι).Nonempty then
              (if pick ⟨↑S, hS⟩ = i then (Set.univ : Set (ΩN N Ω)) else ∅)
            else ∅))) := by
    ext ω
    constructor
    · intro hlog
      have hne : log vbl A pick hpick ω t.val ≠ none := by
        rw [hlog]
        exact Option.some_ne_none i
      have hR : t.val < R vbl A pick hpick ω :=
        (log_ne_none_iff_lt_R (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) ω
          (t := t.val)).mp hne
      have ht' : t.val < N + 1 := Nat.lt_of_lt_of_le hR
        (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))
      let u : Fin (N + 1) := ⟨t.val, ht'⟩
      have hu : u = t := Fin.ext rfl
      let c₀ : State (κ := κ) N := count vbl A pick hpick ω u
      let e : Payload vbl A ω c₀ :=
        Classical.choose (run_step_of_lt_R vbl A pick hpick ω hR)
      have he_spec : (run vbl A pick hpick ω u).2 = some e := by
        dsimp [e]
        exact Classical.choose_spec (run_step_of_lt_R vbl A pick hpick ω hR)
      have he₁ : e.1 = i := by
        change log vbl A pick hpick ω t.val = some i at hlog
        unfold log at hlog
        rw [dif_pos hR] at hlog
        exact Option.some.inj hlog
      have hstep : (step vbl A pick hpick ω c₀).2 = some e := by
        dsimp [c₀]
        exact (run_snd_eq_step (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
          ω u).symm.trans he_spec
      have hstep' : ∃ hAv : (Avail vbl A ω c₀).Nonempty,
          pick ⟨Avail vbl A ω c₀, hAv⟩ = e.1 := by
        unfold step at hstep
        split_ifs at hstep with hAv
        refine ⟨hAv, ?_⟩
        simp at hstep
        exact congrArg Subtype.val hstep
      rcases hstep' with ⟨hAv, hpickAv⟩
      let S : Finset ι := Finset.univ.filter (fun i => i ∈ Avail vbl A ω c₀)
      have hS : (↑S : Set ι).Nonempty := by
        refine ⟨e.1, ?_⟩
        rw [show (↑S : Set ι) = Avail vbl A ω c₀ from by
          ext i
          simp [S]]
        exact ⟨e.2.1, e.2.2⟩
      have hsub : (⟨↑S, hS⟩ : {S : Set ι // S.Nonempty}) =
          ⟨Avail vbl A ω c₀, hAv⟩ := by
        apply Subtype.ext
        ext i
        simp [S]
      have hpS : pick ⟨↑S, hS⟩ = e.1 := (congrArg pick hsub).trans hpickAv
      have hAvfiber : Avail vbl A ω (count vbl A pick hpick ω t) = (↑S : Set ι) := by
        have hc : count vbl A pick hpick ω u = count vbl A pick hpick ω t :=
          congrArg (count vbl A pick hpick ω) hu
        calc
          Avail vbl A ω (count vbl A pick hpick ω t) =
              Avail vbl A ω (count vbl A pick hpick ω u) := congrArg (Avail vbl A ω) hc.symm
          _ = (↑S : Set ι) := by
            ext i
            simp [S, c₀]
      rw [Set.mem_inter_iff]
      constructor
      · exact hR
      · rw [Set.mem_iUnion]
        refine ⟨count vbl A pick hpick ω t, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨S, ?_⟩
        rw [Set.mem_inter_iff]
        constructor
        · rw [Set.mem_inter_iff]
          constructor
          · rfl
          · exact hAvfiber
        · rw [dif_pos hS, if_pos (hpS.trans he₁)]
          exact Set.mem_univ ω
    · intro hω
      rw [Set.mem_inter_iff] at hω
      rcases hω with ⟨hR, hU⟩
      change t.val < R vbl A pick hpick ω at hR
      rw [Set.mem_iUnion] at hU
      rcases hU with ⟨c, hc⟩
      rw [Set.mem_iUnion] at hc
      rcases hc with ⟨S, hSω⟩
      rw [Set.mem_inter_iff] at hSω
      rcases hSω with ⟨hfib, hif⟩
      rw [Set.mem_inter_iff] at hfib
      rcases hfib with ⟨hcount, hAv⟩
      change count vbl A pick hpick ω t = c at hcount
      change Avail vbl A ω c = (↑S : Set ι) at hAv
      by_cases hS : (↑S : Set ι).Nonempty
      · rw [dif_pos hS] at hif
        by_cases hpi : pick ⟨↑S, hS⟩ = i
        · rw [if_pos hpi] at hif
          have ht' : t.val < N + 1 := Nat.lt_of_lt_of_le hR
            (Nat.le_trans (R_le vbl A pick hpick ω) (Nat.le_succ N))
          let u : Fin (N + 1) := ⟨t.val, ht'⟩
          have hu : u = t := Fin.ext rfl
          let c₀ : State (κ := κ) N := count vbl A pick hpick ω u
          let e : Payload vbl A ω c₀ :=
            Classical.choose (run_step_of_lt_R vbl A pick hpick ω hR)
          have he_spec : (run vbl A pick hpick ω u).2 = some e := by
            dsimp [e]
            exact Classical.choose_spec (run_step_of_lt_R vbl A pick hpick ω hR)
          have hstep : (step vbl A pick hpick ω c₀).2 = some e := by
            dsimp [c₀]
            exact (run_snd_eq_step (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
              ω u).symm.trans he_spec
          have hstep' : ∃ hAv : (Avail vbl A ω c₀).Nonempty,
              pick ⟨Avail vbl A ω c₀, hAv⟩ = e.1 := by
            unfold step at hstep
            split_ifs at hstep with hAvc
            refine ⟨hAvc, ?_⟩
            simp at hstep
            exact congrArg Subtype.val hstep
          rcases hstep' with ⟨hAvc, hpickAv⟩
          have hc₀ : count vbl A pick hpick ω u = count vbl A pick hpick ω t :=
            congrArg (count vbl A pick hpick ω) hu
          have hAvu : Avail vbl A ω (count vbl A pick hpick ω u) = (↑S : Set ι) := by
            calc
              Avail vbl A ω (count vbl A pick hpick ω u) =
                  Avail vbl A ω (count vbl A pick hpick ω t) := congrArg (Avail vbl A ω) hc₀
              _ = Avail vbl A ω c := congrArg (Avail vbl A ω) hcount
              _ = (↑S : Set ι) := hAv
          have hsub : (⟨Avail vbl A ω c₀, hAvc⟩ : {S : Set ι // S.Nonempty}) =
              ⟨↑S, hS⟩ := by
            apply Subtype.ext
            dsimp [c₀]
            exact hAvu
          have he₁ : e.1 = i := by
            calc
              e.1 = pick ⟨Avail vbl A ω c₀, hAvc⟩ := hpickAv.symm
              _ = pick ⟨↑S, hS⟩ := congrArg pick hsub
              _ = i := hpi
          change log vbl A pick hpick ω t.val = some i
          unfold log
          rw [dif_pos hR]
          exact Option.some_inj.mpr he₁
        · rw [if_neg hpi] at hif
          simp at hif
      · rw [dif_neg hS] at hif
        simp at hif
  rw [hset]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_lt_R (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
      (hA := hA) (t := t)
  · haveI : Fintype (State (κ := κ) N) := by
      dsimp [State]
      infer_instance
    haveI : Finite (State (κ := κ) N) := Finite.of_fintype (State (κ := κ) N)
    haveI : Countable (State (κ := κ) N) := Finite.to_countable
    refine MeasurableSet.iUnion (fun c : State (κ := κ) N => ?_)
    refine MeasurableSet.iUnion (fun S : Finset ι => ?_)
    refine MeasurableSet.inter ?_ ?_
    · exact (measurableSet_count_eq (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
        (hA := hA) (t := t) (c := c)).inter
        (measurableSet_Avail_eq (vbl := vbl) (A := A) (hA := hA) (c := c) S)
    · by_cases hS : (↑S : Set ι).Nonempty
      · by_cases hpi : pick ⟨↑S, hS⟩ = i
        · rw [dif_pos hS, if_pos hpi]
          exact MeasurableSet.univ
        · rw [dif_pos hS, if_neg hpi]
          exact MeasurableSet.empty
      · rw [dif_neg hS]
        exact MeasurableSet.empty

include hA in
/-- The padded-log count of event `i` is measurable in the table (`Finset.card_filter` +
`Measurable.ite` + `Finset.measurable_sum`). The `[DecidableEq ι]` is an explicit binder
(matching `countLog`). -/
theorem measurable_countLog [DecidableEq ι] {i : ι} :
    Measurable (fun ω : ΩN N Ω => countLog (log vbl A pick hpick) ω i) := by
  classical
  have hfiber : Measurable (fun ω : ΩN N Ω =>
      ∑ t ∈ Finset.range N, (if log vbl A pick hpick ω t = some i then (1 : ℕ) else 0)) := by
    refine Finset.measurable_sum (Finset.range N) ?_
    intro t ht
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_log_eq_some (vbl := vbl) (A := A) (pick := pick) (hpick := hpick)
      (hA := hA) (t := ⟨t, Nat.lt_of_lt_of_le (Finset.mem_range.mp ht) (Nat.le_succ N)⟩)
      (i := i)
  have hcongr : (fun ω : ΩN N Ω => countLog (log vbl A pick hpick) ω i) =
      (fun ω : ΩN N Ω =>
        ∑ t ∈ Finset.range N,
          (if log vbl A pick hpick ω t = some i then (1 : ℕ) else 0)) := by
    funext ω
    change ((Finset.range N).filter (fun t => log vbl A pick hpick ω t = some i)).card =
      ∑ t ∈ Finset.range N, (if log vbl A pick hpick ω t = some i then (1 : ℕ) else 0)
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcongr]
  exact hfiber

include hA in
/-- The set of tables where the padded-log count of `i` is `k` is measurable (preimage of
the singleton `{k}`, `MeasurableSingletonClass.measurableSet_singleton`). -/
theorem measurableSet_countLog_eq [DecidableEq ι] {i : ι} {k : ℕ} :
    MeasurableSet {ω : ΩN N Ω | countLog (log vbl A pick hpick) ω i = k} := by
  rw [show {ω : ΩN N Ω | countLog (log vbl A pick hpick) ω i = k} =
      (fun ω : ΩN N Ω => countLog (log vbl A pick hpick) ω i) ⁻¹' ({k} : Set ℕ) from by
    ext ω
    simp]
  exact (measurable_countLog (vbl := vbl) (A := A) (pick := pick) (hpick := hpick) (hA := hA)
    (i := i)) (measurableSet_singleton k)

end Measurability

end TCSLean.MoserTardos
