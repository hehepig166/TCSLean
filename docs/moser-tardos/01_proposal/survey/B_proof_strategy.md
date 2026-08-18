# B. Proof Strategy & Formalization Plan (Moser–Tardos Algorithmic LLL, Asymmetric, Variable Framework)

**Scope note.** This survey assumes mathlib `v4.32.0` (pinned by `StatsMLlib/lakefile.lean`), the
variable-framework Moser–Tardos theorem (notes `ref/moser_tardos_algorithmic_lll_notes.md`
Theorem 5.1 = arXiv:0903.0544 Theorem 1.2, sequential form), and the finite-truncation
architecture of PLAN §3. All Lean names cited were checked by grepping
`StatsMLlib/.lake/packages/mathlib/Mathlib` or by compile tests in `/tmp` (scratch prototypes
`/tmp/mt_proto_trees.lean`, `/tmp/mt_proto_run.lean`, `/tmp/mt_smoke.lean` — see §3.0). Names
marked **TBC** or **NEW** are to be created or confirmed by agent A.

**Headline findings (amendments to PLAN §3):**

1. **The truncated table must have `N+1` rows per variable, not `N`** (`Ω_N := Π j, Fin (N+1) → Ω j`).
   The notes' resampling-table convention (§7) is cumulative: "if X_j has already been resampled
   s times, its current value is X_j^{(s)}". An execution of up to `N` steps can resample one
   variable `N` times, reaching row `N`. With `Fin N` rows, a variable resampled at every step
   would overflow at the last step, and the coupling (notes (14.5)) is provably incompatible with
   any "step t uses row t" convention. Fin (N+1) rows fix this with zero other changes.
2. **The padded log should be `Option`-valued**: `Λ : Ω_N → ℕ → Option ι` with `Λ t = some e` for
   genuine steps `t < R`, `none` otherwise. Then the plan's count `#{t < N : Λ t = i}` survives
   verbatim as `#{t < N : Λ t = some i}`, no `[Nonempty ι]` is needed for a padding dummy, and
   padded entries are structurally excluded from witness-tree construction (mission 1b(iii): pad
   never creates trees, Prop 12.1 is stated for `t < R` only — confirmed in §3.2).
3. **No infinite product measure / Kolmogorov is needed.** Everything is stated and proved on
   `Ω_N` with `Measure.pi` (finite index type `Σ j, Fin (N+1)`), `lintegral`-based expectations;
   the honest corollaries (total bound, multiplicative Markov tail, constructive existence,
   a.s.-style termination-in-ε–N form) all live on `Ω_N`. This validates the finite-truncation
   architecture; see §2.
4. The whole proof chain of the notes (§6–§20) is mathematically sound for the truncation,
   including the two spots the mission flagged (padded-log injectivity; the `x i = 0` case).
   One formulation gap in the notes was found and filled (§3.5, the `N = 0` tail bound), and
   one sloppy step in the notes' Lemma 11.1 proof is harmless (§3.2).

---

## 1. Pinned theorem statement

### 1.0 The variable framework (informal)

Finite event index `ι` and variable index `κ` (both `Fintype`); variable `j` takes values in a
measurable space `Ω j` with probability measure `μ j`; the joint law on `Π j, Ω j` is
`Measure.pi μ` (denoted `μπ` below). Each bad event `A i ⊆ Π j, Ω j` is **determined by**
`vbl i ⊆ κ` (finitely many variables). The dependency structure is the **variable-overlap
graph**: `i` and `j` are adjacent iff `i ≠ j` and `vbl i ∩ vbl j ≠ ∅`; `Γ(i)` = open overlap
neighborhood, `Γ⁺(i) = Γ(i) ∪ {i}`. The LLL condition: for weights `x : ι → ℝ`,
`0 ≤ x i`, `x i < 1`:

```
μπ (A i) ≤ x i · ∏_{j ∈ Γ(i)} (1 - x j)          for all i          (LLL)
```

### 1.1 Main theorem (Lean-level; the plan's pinned shape, amended per findings 1–2)

```lean
namespace MoserTardos

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

-- truncated table: N+1 rows per variable (finding 1)
def ΩN (N : ℕ) (Ω : κ → Type*) : Type* := Π j : κ, Fin (N + 1) → Ω j
-- measure on the table
def μN (N : ℕ) (μ : ∀ j, Measure (Ω j)) : Measure (ΩN N Ω) :=
  Measure.pi (fun p : Σ j : κ, Fin (N + 1) => μ p.1)          -- [IsProbabilityMeasure] inferable

def countLog {N} (Λ : ΩN N Ω → ℕ → Option ι) (ω) (i : ι) : ℕ :=
  ((Finset.range N).filter fun t => Λ ω t = some i).card

/-- Moser–Tardos: expected number of resamplings of event i is ≤ x i / (1 - x i). -/
theorem moserTardos_bound {N : ℕ} (Ω : κ → Type*) [∀ j, MeasurableSpace (Ω j)]
    (μ : ∀ j, Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (vbl : ι → Finset κ) (A : ι → Set (Π j, Ω j)) (hA : ∀ i, MeasurableSet (A i))
    (hdet : ∀ i, DeterminedBy (A i) (vbl i))            -- §4.4
    (x : ι → ℝ) (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μπ μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ Γ vbl i, (1 - x j)))
    (pick : {S : Set ι // S.Nonempty} → ι) (hpick : ∀ S, pick S ∈ S.1)
    (i : ι) :
    ∫⁻ ω : ΩN N Ω, (countLog (log vbl A pick hpick) ω i : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (x i / (1 - x i))
```

where `Γ vbl i := (overlapGraph vbl).neighborFinset i`, `μπ μ := Measure.pi μ`, and
`log vbl A pick hpick : ΩN N Ω → ℕ → Option ι` is the deterministic resampling log (§3.1).
The theorem holds for **every** pick — uniformity over the choice rule is free by
parametricity (notes §4 "Fix any rule"; §4.1). The `x i = 0` case needs no division: it is
absorbed inside the proof via `by_cases` (§3.4). All arithmetic on the right is ℝ inside
`ENNReal.ofReal`; **no ENNReal division occurs anywhere**.

Cross-check against the notes §5.1 and arXiv:0903.0544 Thm 1.2: both state
`E[N_i] ≤ x(A_i)/(1 - x(A_i))`; our `countLog` is exactly `N_i^{(N)}` (occurrences of `i`
in the log prefix of length `N`), and the truncation only restricts the log to `N` steps —
no other change.

### 1.2 Corollaries (initial scope = all of these)

```lean
/-- Total expected resamplings. -/
theorem moserTardos_total (…same hypotheses…) :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))

/-- Markov tail bound, multiplicative form (division-free; the honest statement — see §3.5). -/
theorem moserTardos_tail (…same hypotheses…) :
    (N : ℝ≥0∞) * μN N μ {ω | R vbl A pick hpick ω = N}
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))

/-- Constructive LLL: the algorithm's output at time R < N avoids every bad event. -/
theorem moserTardos_exists (…same hypotheses…) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i

/-- Symmetric form (follow-up PR, §5/§6): e·p·(d+1) ≤ 1 ⟹ E[R] ≤ m/d. -/
theorem moserTardos_symmetric (…framework…)
    {p : ℝ} {d : ℕ} (hp : ∀ i, μπ μ (A i) ≤ p)
    (hd : ∀ i, (overlapGraph vbl).degree i ≤ d) (hd1 : 1 ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1) (…pick…) :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / d)
```

All four were audited against the notes (§19, §20) — see §3.5.

---

## 2. Architecture verdict: finite truncation validated (with the two amendments)

**Verdict: validate.** The witness-tree + coupling + Galton–Watson chain transfers to the
truncated table verbatim, *provided* the two amendments of the headline findings are adopted.
Detailed audit in §3; the design points the PLAN left open are settled in §4.

- **Rows:** `Fin (N+1)` per variable; steps indexed `t < N`; `R ≤ N` always.
- **Log:** `Option ι`-valued; witness trees are only ever built at genuine times `t < R`.
- **No infinite products anywhere**; termination is expressed through `μN (R = N)` (tail bound)
  and the constructive existence corollary — this is honest, since mathlib v4.32.0 has **no
  Kolmogorov/countable-product measure** to state a.s. termination of the infinite algorithm
  directly (agent A confirms; even if it existed, the truncated statement is strictly simpler
  and implies the useful forms).
- The PLAN's decomposition (witness trees → coupling → GW → main bound) is exactly the
  right skeleton; §5 refines it into 27 declaration items with the fold-invariant lemma (C10)
  as the single hardest point.

---

## 3. Detailed proof audit

**3.0 Prototypes compiled (all under `/tmp`, nothing in the repo touched).**

- `/tmp/mt_proto_trees.lean`: `WitnessTree ι` inductive (List children), `deepestEligible`
  (Option ℕ depths), `attachBelow` + `attachInFirst` (mutual recursion, **accepted with plain
  structural termination**), the reverse-scan fold `treeAt`, all compiling.
- `/tmp/mt_smoke.lean`: evaluated the construction on the slides' example log
  `D, C, E, D` (overlap graph A~{B,E}, B~{A,C}, C~{B,D}, D~{C,E}, E~{A,D}), getting
  `mk (3,D) [mk (1,C) [mk (0,D) []], mk (2,E) []]` — root D(3); C(1) and E(2) children of the
  root (both overlap D); D(0) attached below C(1) (deepest eligible; C, E tied at depth 1, the
  leftmost tie-break picks C — the notes allow *any* tie-break, §9 step 5). Depth-lemma sanity:
  q(D₀)=0 < q(E₂)=2, overlap ⟹ depth 2 > 1 ✓.
- `/tmp/mt_proto_run.lean`: the truncated-table algorithm — `Table κ N Ω := Π j, Fin (N+1) → Ω j`,
  `State κ N := κ → Fin (N+1)`, `assign`, `Avail` (violated + rows remaining), **availability-
  carrying `step`** returning `Option {e : ι // occurs ∧ ∀ j ∈ vbl e, c j < N}`, the
  `Fin.induction`-based `run`, `count`, the invariant `run_count_le : (count … t) j ≤ t.val`
  (statement elaborated; proof steps left as prototype `sorry`s — standard `Fin.induction`),
  `Violated`, `NoViolation`, `R` (via `Nat.find`, classical), `R_le`, `log`. All typecheck.

**3.1 Algorithm on the truncated table (mission 1a).**

- **State:** `c : κ → Fin (N+1)` (rows consumed per variable). **Current assignment:**
  `assign ω c : Π j, Ω j` with `(assign ω c) j = ω j (c j)` — total because `c j : Fin (N+1)`.
  **Violated set:** `{i | assign ω c ∈ A i}`.
- **Deterministic pick:** `pick : {S : Set ι // S.Nonempty} → ι` with `hpick : pick S ∈ S.1`,
  applied to the *available* violated set `Avail ω c := {i | assign ω c ∈ A i ∧ ∀ j ∈ vbl i, (c j) < N}`
  (the `< N` guard is the availability certificate — it exists only to make `step` total;
  see the next bullet).
- **One step:** advance `c j ↦ c j + 1` for `j ∈ vbl (picked event)`, using the certificate in
  the `Fin` proof term (`Nat.succ_lt_succ (cert j hj)`).
- **`run`:** `Fin.induction` over `Fin (N+1)`: entry `t` = (counts *before* step `t`, event of
  step `t` as `Option` with the certificate). Once the option is `none` the recursion freezes
  (the match keeps the same `c`), which is exactly "the algorithm stops".
- **Rows never run out (verified).** For `t < N`: `(count ω t) j ≤ t < N` (invariant
  `run_count_le`, proved by `Fin.induction`; the only place the inductive step needs care is
  unfolding `run`'s `Fin.induction` term — routine). Hence at any time `t < N` *every* violated
  event is available (its variables have `c j ≤ t < N`), so **the availability guard never
  bites before `N` steps**, and the guarded `step` is definitionally the honest algorithm on
  the relevant prefix. The log is therefore well-defined for all `t < R` (since `t < R ≤ N`
  gives `t < N`).
- **Stopping time:** `NoViolation ω t := ∃ ht : t < N+1, ∀ i, assign ω (count ω ⟨t, ht⟩) ∉ A i`;
  `R ω := Nat.find` of the first `t ≤ N` with no violated event, else `N` (classical; the
  fallback covers both "still violated at N" and the possible row-exhausted-at-N state, e.g. an
  always-violated single-variable event exhausts its rows exactly at time N).
  `R_le : R ω ≤ N` (compiled in the prototype).
- **Padded log:** `log ω t := if t < R ω then (the event of step t — obtained via the lemma
  `run_step_of_lt_R : t < R ω → ∃ e, (run ω t).2 = some e`) else none`. Equivalently, since the
  run's option is itself `none` exactly at/after the first violated-free time, one can define
  `log` directly from the run's option and prove `log ω t = none` for `t ≥ R`. The count in the
  main theorem, `#{t < N : Λ t = some i}`, then automatically equals `#{t < R ω : Λ t = some i}`.

**3.2 Witness-tree construction, Prop 10.1, Lemma 11.1/Cor 11.2, Prop 12.1 (mission 1b).**

- **Construction.** `treeAt Λ t : WitnessTree (ℕ × ι)` — the fold over the reversed prefix
  `s = t-1 … 0`: skip `none` entries; for `some i`, `attachBelow` a new leaf `(s, i)` below the
  deepest vertex whose label is eligible, where eligibility of `(s,i)` below `(s',i')` is
  `i = i' ∨ (vbl i ∩ vbl i').Nonempty` (i.e. `i ∈ Γ⁺(i')` — the prototype's
  `fun p q => p.2 = q.2 ∨ elig p.2 q.2`). Time-labeled trees carry `q(u)` as part of the label;
  `T(ω,t) := forgetTime (treeAt (log ω) t) : WitnessTree ι`.
- **(i) Prop 10.1 (occurring trees proper).** Verified. The argument: children of a parent are
  inserted in reverse-scan order; if a later insertion `w` created a second child with label `A`
  under `u`, the earlier sibling `v` (label `A`) was already present, is eligible (`A ∈ Γ⁺(A)`),
  and lies one level deeper than `u` — so `u` was not a deepest eligible vertex. Lean form: a
  consequence of the spec lemma C10 (below), proved once by induction over the fold; no new
  circularity. (Sanity: the prototype's tree for the slides' example is proper ✓.)
- **(ii) Lemma 11.1 / Cor 11.2.** Verified, and the notes' proof is *clean* precisely because
  the dependency graph is **defined as** the variable-overlap graph: sharing a variable gives
  `[u] ∈ Γ⁺([v])` unconditionally — if `[u] ≠ [v]` it is adjacency, and if `[u] = [v]` the
  inclusive self-loop `A ∈ Γ⁺(A)` applies. (The notes' sentence "Hence [u] ∈ Γ([v]) ⊆ Γ⁺([v])"
  is technically wrong in the equal-label case, but the needed conclusion `[u] ∈ Γ⁺([v])` holds
  in both cases; no fix needed beyond stating the two-case lemma
  `mem_gammaPlus_of_overlap : i = j ∨ (vbl i ∩ vbl j).Nonempty → i ∈ Γ⁺ vbl j`.) The depth
  conclusion `d(u) ≥ d(v) + 1` comes from the deepest-eligible insertion rule: the new vertex is
  a child of a max-depth eligible vertex, hence deeper than *every* eligible vertex. Lean form:
  another consequence of C10. Cor 11.2 (same depth ⟹ disjoint `vbl`) is immediate by symmetry of
  q-values (distinct vertices have distinct times — each reverse-scan step creates at most one
  vertex, and the root's time `t` is fresh).
- **(iii) Prop 12.1 (injectivity) under the padded log. Confirmed: the pad does not break it.**
  `T(ω,t)` is only *used* at genuine times `t < R(ω)` (the counting identity of §3.4 quantifies
  `t < R`); for `t < R` the scan covers `s < t < R`, i.e. **only genuine entries**, so padded
  `none` entries never enter any `T(ω,t)` used in the proof. The two-case proof of the notes
  survives verbatim: (a) different root labels → different trees; (b) same label `A`: `T(Λ,t_r)`
  contains exactly `r` vertices labeled `A` — every earlier `A`-occurrence is inserted (the root
  labeled `A` is always an eligible attachment point via `A ∈ Γ⁺(A)`), each insertion creates a
  fresh vertex, and all `A`-labeled vertices come from entries — so the `r`-th and `r'`-th
  occurrences (`r ≠ r'`) yield trees with different `A`-counts. Stated for `s ≠ t`, `s, t < R`.

**3.3 Coupling lemma 14.1 (mission 1c) — audited; the recommended formal split.**

The notes' coupling applies Cor 11.2 to the *fixed* tree `τ` only under the assumption
`T(Λ,t) = τ`; the clean formal structure separates three ingredients, exactly as the mission
suggests:

- **Abstract τ-check with genuinely fresh samples.** For a fixed witness tree `τ` (an abstract
  `WitnessTree ι`), define the check *structurally*, with no sequential process and no vertex
  index type needed:
  `treeProfile τ j d := #{vertices v of τ : depth v ≥ d, j ∈ vbl (label v)}` (recursive;
  compiled pattern in the prototype family). Vertex `v` at depth `d` is checked on the table
  entries `(j, treeProfile τ j (d+1))` for `j ∈ vbl (label v)` — this is exactly the notes'
  `(X, |S_X(u)|)` (14.4), since `S_X(u) = {v : depth v > depth u, X ∈ vbl[v]}`. The check
  succeeds at `v` iff `f_{label v}` holds of those entries, where `f_i` is the `DeterminedBy`
  witness (`A i ↔ f_i` on the `vbl i` restriction) — no completion of coordinates outside
  `vbl i` is ever needed, and no `Nonempty (Ω j)` hypothesis.
  `check τ ω := ∀ v, f_v (fun j => ω j ⟨profile j (d(v)+1), h⟩)` (recursive definition with a
  depth parameter; the profile of the whole tree is threaded down unchanged).
- **(a) Entry injectivity for occurring trees — verified, via two cases.** The read coordinate
  `(v, j) ↦ (j, profile j (d(v)+1))` is injective on `{j ∈ vbl (label v)}`: same vertex trivial;
  distinct vertices at the same depth have disjoint `vbl` (Cor 11.2 for occurring trees / the
  `IsGood` hypothesis for abstract trees); distinct depths with shared `j`: if
  `d(v') > d(v)` then `v'` itself contributes to the count at depth `d(v)+1` but not to
  `d(v')+1`, giving the **strict** inequality
  `profile j (d(v)+1) ≥ profile j (d(v')) + 1 > profile j (d(v')+1)` — this is precisely the
  mission's "deeper vertex lies in the shallower's S_X but not its own" argument, confirmed
  sound (the shallow vertex's index counts all of `{depth > d(v)}`, which contains
  `{depth ≥ d(v')} ∋ v'`).
- **(b) `{∃t < R, T(Λ,t) = τ} ⊆ {check passes}` — audited, both directions of the bijection
  hold.** For the occurring tree (worked on its time-labeled version `τ̃ = treeAt (log ω) t`,
  whose shape matches `τ` via `forgetTime`), for each vertex `u` and each `X ∈ vbl[u]`:
  *Forward:* `s < q(u)` with `X ∈ vbl[Λ s]` ⟹ the entry at `s` is inserted (its label overlaps
  `[u]` through `X`, so `u`, already present since `q(u) > s`, is eligible) and by Lemma 11.1
  (applied to the inserted vertex and `u`) the new vertex has depth `> d(u)` — hence it is
  counted in `S_X(u)`.
  *Backward:* `v ∈ S_X(u)` (so `d(v) > d(u)`, `X ∈ vbl[v]`): if `q(u) < q(v)`, Lemma 11.1 gives
  `d(u) > d(v)`, contradiction; `q(u) ≠ q(v)` (distinct vertices, distinct times), hence
  `q(v) < q(u)` — so `v` represents a resampling of `X` before time `q(u)`.
  Distinct times ↔ distinct vertices makes this a bijection, so
  `#{X-resamplings before q(u)} = |S_X(u)| = profile τ X (d(u)+1)`. Therefore MT's value of `X`
  immediately before resampling `u` is `ω X ⟨|S_X(u)|⟩` — the very entry the check reads — and
  since the algorithm only resamples occurring events, `A[u]` occurs under those values; by
  `DeterminedBy`, `f_u` holds of them. So `check τ ω` holds. (The mission's `q(v) < q(u)`
  argument is confirmed as the backward direction.)
- **(c) Measure preservation — no coupling map φ is needed as a separate construction.** Because
  the check reads *injective* coordinates, `μN {ω | check τ ω} = treeProd τ` where
  `treeProd τ := μπ (A (root)) * ∏_{c ∈ children} treeProd c` is provable by tree induction:
  the root's coordinate family `{(j, profile j 1)}` is disjoint from the forest's families
  (same strict-profile inequality), children's families are pairwise disjoint (same argument),
  so the event factors as a product of independent cylinder events, each with law `μπ (A[v])`
  (marginal of a product measure under a coordinate-reading map). Ingredients (all present in
  mathlib v4.32.0, agent A to pin exact names): `Measure.pi_pi_finset`
  (`MeasureTheory/Constructions/Pi.lean:315`), the coordinatewise-map lemma
  `(Measure.pi μ).map (fun x i => f i (x i)) = Measure.pi (fun i => (μ i).map (f i))`
  (`Pi.lean:390`), `iIndepFun`/`IndepFun` (`Probability/Independence/Basic.lean:136,144`) and
  `indepFun_iff_measure_inter_preimage_eq_mul` (`:644`), `lintegral_indicator`
  (`MeasureTheory/Integral/Lebesgue/Basic.lean`).
  Then `μN {∃t < R, T(Λ,t) = τ} ≤ μN {check τ} = treeProd τ` — the **coupling lemma**. Formal
  split recommendation: `IsGood τ := Proper τ ∧ SameDepthDisjointVbl τ` (both path-based on the
  abstract tree); (1) occurring trees are good (Prop 10.1 + Cor 11.2 transported through
  `forgetTime`); (2) the profile inequality (the deeper-vertex strictness) for good trees;
  (3) `check_probability : IsGood τ → |V τ| ≤ N → μN {check τ} = treeProd τ` (the `|V τ| ≤ N`
  bound makes every `profile j (d+1) ≤ N-1 < N+1`, so the check reads valid rows);
  (4) `occurrence_implies_check : T ω t = τ → check τ ω`; (5) assembly.

**3.4 Galton–Watson block and the final chain (mission 1d).**

- **Weight formula.** Define `gwWeight τ` by the *genuine branching probability* (17.3) as a
  structural fold — accepted-child products `∏_{B ∈ C_τ(u)} x B` times rejected
  `∏_{B ∈ Γ⁺([u]) \ C_τ(u)} (1 - x B)` — with `C_τ(u)` the Finset of child labels (well-defined
  because `τ` is proper). **No division here.** The telescoping to (17.2) is then a lemma with
  the division hypothesis:
  `gwWeight_telescope (hxi : x i ≠ 0) : gwWeight τ = ((1 - x i) / x i) * ∏_{u ∈ V τ} x' ([u])`
  where `x' i := x i * ∏_{B ∈ Γ(i)} (1 - x B)` — proven by tree induction using (a) the
  child-to-nonroot reindexing `∏_u ∏_{B ∈ C_τ(u)} x B = ∏_{v ≠ root} x ([v])` (each non-root is
  the child of exactly one parent) and (b) the rejection-product cancellation
  `∏_u ∏_{B ∈ W_u} (1 - x B) = (1 - x i) * ∏_u ∏_{B ∈ Γ([u])} (1 - x B)` via
  `Γ⁺([u]) = C_τ(u) ⊔ W_u` (uses child labels ⊆ Γ⁺(parent) — the witness-tree condition). Pure
  ℝ/Finset algebra; both identities audited against notes (17.4)–(17.2) ✓.
- **Sum bound.** `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ 1` where `𝒯_i(N)` = proper witness trees rooted
  at `i` with `≤ N` vertices (a Fintype — item E20). Proof by the height-`h` induction:
  `S_h(i) := ∑_{τ rooted at i, height τ ≤ h} gwWeight τ`; the recurrence
  `S_{h+1}(i) = ∏_{B ∈ Γ⁺(i)} [(1 - x B) + x B · S_h(B)]` comes from the multinomial
  factorization over child-label sets `C ⊆ Γ⁺(i)`
  (`∏_B (a_B + b_B) = ∑_{C ⊆ S} ∏_{B∈C} b_B · ∏_{B∉C} a_B`; mathlib `prod_sum`,
  `Algebra/BigOperators/Fin.lean` — exact application TBC) — audited: subtree heights line up
  (`height ≤ h` in child coordinates ⟺ `height ≤ h+1` globally), and the sum ranges over proper
  trees automatically since `C` is a *set*. Then `0 ≤ x B ≤ 1` and `S_h(B) ≤ 1` give
  `(1 - x B) + x B · S_h(B) ≤ 1`, base `S_0(i) = ∏_{B ∈ Γ⁺(i)} (1 - x B) ≤ 1`. Since
  `height τ ≤ size τ - 1 ≤ N - 1`, `∑_{τ ∈ 𝒯_i(N)} gwWeight τ ≤ S_N(i) ≤ 1` ✓.
- **Final chain.** `E[N_i^{(N)}] = Σ_{τ ∈ 𝒯_i(N)} μN{∃t < R, T = τ}` (counting identity via
  Prop 12.1: the injective map `t ↦ T(ω,t)` from `{t < N : Λ t = some i}` into `𝒯_i(N)` turns
  the count into a sum of indicators) `≤ Σ_τ treeProd τ` (coupling) `≤ Σ_τ ofReal (∏_u x'([u]))`
  (hLLL per node + product monotonicity; needs `0 ≤ x' i` — from `hx₀` and `1 - x B ≥ 0` via
  `hx₁`) — then:
  - **`x i = 0` case — confirmed, no division, closes via the root factor.** `hLLL` gives
    `μπ (A i) ≤ ofReal 0 = 0`, and since every `τ ∈ 𝒯_i(N)` has root label `i`,
    `treeProd τ ≤ μπ (A i) = 0`, so the chain stops at `0 ≤ ofReal (x i/(1-x i)) = ofReal 0`.
    The GW block is never entered. **`by_cases h : x i = 0` enters exactly once, at the top of
    the main assembly (item F23).** (This also matches the mission's observation that
    `x'([r]) = 0` kills `∏_u x'([u])` — either reading works; the root-factor-via-coupling one
    needs no GW at all.)
  - **`x i > 0`:** `ofReal (∏_u x'([u])) = ofReal (x i/(1-x i)) * ofReal (gwWeight τ)` via the
    telescope + `ENNReal.ofReal_mul`/`ofReal_div` glue (`ofReal_div_of_pos`/
    `ofReal_div_le`, `Data/ENNReal/Inv.lean:946,952`; `ofReal_mul` in `Data/ENNReal/Real.lean`)
    → `Σ_τ … ≤ ofReal (x i/(1-x i)) · 1` by the sum bound.

**3.5 Corollaries (mission 1e).**

- **Total bound:** `R = Σ_i N_i^{(N)}` pointwise (each `t < R` has `Λ t = some e` for exactly one
  `e`), so `∫⁻ R = Σ_i ∫⁻ countLog` via `lintegral_finset_sum` (name TBC — the finite-sum
  version of `lintegral_sum`, `Lebesgue/Basic.lean`) — no additional content.
- **Tail bound — inequality direction checked, and `N = 0` DOES need a case.** Pointwise
  `N · 𝟙[R = N] ≤ R`: if `R = N`, `N ≤ R = N`; if `R ≠ N`, `0 ≤ R` (using `R ≤ N`) — direction
  correct. However the *divided* form `μN(R = N) ≤ (Σ x i/(1-x i))/N` is **false for `N = 0`**
  (then `R = 0` a.s. and the RHS is `x/0 = 0` in Lean's ℝ). Hence the honest statement is the
  **multiplicative** one in §1.2 (true for all `N`); the ε–N divided form
  (`μN(R = N) ≤ ε` for `N ≥ (Σ x i/(1-x i))/ε`, `ε > 0`) is a follow-up with `N ≠ 0`. Measurability
  of `{R = N}`: `R < N ⟺ ∃ t : Fin (N+1), ∀ i, ¬ Violated …` — a finite boolean combination of
  `assign … ∈ A i` tests, measurable from `hA` (item B8).
- **Constructive existence:** choose `N` with `Σ x i/(1-x i) < N` (e.g. `Nat.ceil … + 1`; the sum
  is finite because `ι` is `Fintype`); the tail bound gives `μN (R = N) < 1`, so
  `μN {R < N} > 0`, hence (by `exists_mem_of_measure_ne_zero_of_ae`,
  `MeasureTheory/Measure/Restrict.lean:414`, or `nonempty_of_measure_ne_zero`-style glue — exact
  name TBC) some `ω` has `R ω < N`; then `assign ω (count ω ⟨R ω, …⟩) ∈ ⋂ i, (A i)ᶜ` by the
  definition of `R` — **no `Nonempty (Π j, Ω j)` hypothesis needed** (σ is exhibited from ω).
  This is the new constructive LLL in the variable model.
- **Symmetric form:** `x ≡ 1/(d+1)` with `hd1 : 1 ≤ d` (the notes' Corollary 20.1 assumes
  `d ≥ 1` — **the `d = 0` pitfall is excluded by hypothesis**, unlike the classical-LPP
  symmetric form which needed a separate `d = 0` branch: here `d = 0` would force `x = 1`,
  violating `hx₁`). Chain for `hLLL`: `p ≤ 1/(e(d+1))` (from `hcond` by `field_simp`,
  `0 < Real.exp 1`, `0 < d+1`) `≤ (1/(d+1)) · (d/(d+1))^d` (from
  `(1+1/d)^d ≤ e` via `Real.add_one_le_exp` — verified present,
  `Analysis/SpecialFunctions/Exp.lean:211` — and `d/(d+1) = 1/(1+1/d)`, `d ≠ 0` from `hd1`)
  `≤ x · ∏_{j ∈ Γ(i)} (1 - x)` (via `|Γ(i)| ≤ d` = `hd` on `(overlapGraph vbl).degree i`, and
  `pow_le_pow_of_le_one` with `0 ≤ d/(d+1) ≤ 1`; `∏ = (d/(d+1))^{|Γ(i)|}` by `Finset.prod_const`).
  Conclusion `E[R] ≤ m/d`: `Σ_i ofReal(x/(1-x)) = ofReal(m · x/(1-x)) = ofReal(m/d)` via
  `ofReal_sum`/`ofReal_natCast` (Real.lean:311) + `field_simp (d+1 ≠ 0)`.

---

## 4. Design decisions (one recommendation each)

1. **Pick rule: parameterized `pick : {S : Set ι // S.Nonempty} → ι` with `hpick : pick S ∈ S.1`
   — recommended** over least-index-under-`LinearOrder ι`. Rationale: (a) the notes' "the
   analysis does not depend on the rule" becomes the theorem itself — the main theorem holds for
   *every* `pick`, uniformly, by parametricity (no separate uniformity theorem needed; the
   least-index instantiation, if wanted, is a one-line corollary using `Finset.min'`); (b) no
   `[LinearOrder ι]` (or `Nonempty ι`) anywhere in the core; (c) the pick is applied to the
   *available* violated set (the `Avail` predicate), which is exactly the guarded set the
   totality of `step` needs.
2. **Witness tree: custom inductive `WitnessTree ι | mk (label : ι) (children : List (WitnessTree ι))`
   — recommended** (prototype-compiled). Rationale: mathlib's only tree (`Data/Tree.lean`) is a
   *binary* storage tree with a nil node and no rooted-forest API — useless here. List-children
   make the reverse-scan construction, the structural folds (`treeProd`, `gwWeight`, `check`,
   `treeProfile`) and the size/height functions natural. Vertices are addressed as *paths*
   (`List ℕ`, `ValidPath`/`treeAt`/`labelAt`/`depth`) only where needed (`IsGood`,
   Cor 11.2, Prop 12.1's counting); the coupling and GW blocks avoid path-indexed products by
   working with structural folds. `deriving DecidableEq` currently *fails* for this inductive in
   v4.32.0 (verified — the deriving handler rejects it); a manual `instDecidableEq` (~10 lines)
   or avoidance of tree-Finset equality is needed (see Risks).
3. **Where `IsGood` lives:** on the abstract `WitnessTree ι`, path-based:
   `IsGood τ := Proper τ ∧ ∀ p q, p ≠ q → depth p = depth q → Disjoint (vbl (labelAt p)) (vbl (labelAt q))`.
   Occurring trees are good (Prop 10.1 + Cor 11.2 through `forgetTime`); the coupling is stated
   for good trees; the GW block needs only `Proper`.
4. **`Ω_N` statement shape:** `ΩN N Ω := Π j : κ, Fin (N+1) → Ω j` (amended), `μN` = `Measure.pi`
   over `Σ j, Fin (N+1)` — a probability measure automatically from `[∀ j, IsProbabilityMeasure (μ j)]`.
   Steps `t < N`; `R ≤ N`; log `Ω_N → ℕ → Option ι`.
5. **Expectations via `lintegral` — recommended** over `Measure.real`. The entire proof is
   ENNReal monotone arithmetic (indicators, `lintegral_finset_sum`, `lintegral_indicator`), the
   counts are ℕ-valued, and the LLL house style (existing `LovaszLocal.lean`) is ENNReal-first
   with ℝ only inside `ofReal`. `Measure.real` would drag integrability proofs for zero benefit.
6. **Determinism formulation:** `DeterminedBy (A i) (vbl i) := ∃ f : (Π j : vbl i, Ω j) → Prop, ∀ σ, σ ∈ A i ↔ f (fun j => σ j)` — an ∃-hypothesis; the coupling section picks witnesses once via
   `Classical.choose` (`noncomputable`). Rationale: it is exactly what the τ-check consumes (no
   coordinate completion, no `Nonempty (Ω j)`), and the alternative data-carrying interface
   (`eval : ∀ i, (Π j : vbl i, Ω j) → Prop` + `hEval`) is a mechanical variant users can
   instantiate (Open questions).
7. **Time-labeled construction trees** `WitnessTree (ℕ × ι)`: the structural lemmas (10.1, 11.1,
   11.2, 12.1) are stated and proved on the time-labeled `treeAt` (where `q(u)` is a label
   component); the coupling transports them to abstract trees via `forgetTime` (shape- and
   label-preserving). This keeps the abstract type clean for the GW algebra.

---

## 5. Declaration-level decomposition (27 items; LLL-proposal style)

Critical path (★) = A3 → B4 → B5 → B7 → C9 → C10 → C11 → C12 → C13 → C14 → D17 → D18 → E19 →
E20 → E21 → F22 → F23 → F24 → F25 → F26. Off-path but needed: A1, A2, B6, B8, C15, D16, F27.

| # | Item (notes anchor) | Lean declaration (suggested) | Informal statement (Lean-level) | Diff. | Est. lines | Deps |
|---|---|---|---|---|---|---|
| A1 | §2 overlap graph | `overlapGraph (vbl) : SimpleGraph ι` + `mem_overlap_neighborFinset` | `Adj i j ↔ i ≠ j ∧ (vbl i ∩ vbl j).Nonempty`; `Γ⁺ i := insert i (overlapGraph vbl).neighborFinset i`; `mem_gammaPlus_of_overlap` | Easy | 40 | — |
| A2 | §1 determinism | `DeterminedBy` (def) | `∃ f : (Π j : S, Ω j) → Prop, ∀ σ, σ ∈ A ↔ f (σ ∘ Subtype.val)` | Easy | 15 | — |
| A3 | §7 table | `ΩN`, `μN` + probability instance | `Measure.pi` over `Σ j, Fin (N+1)`; `[IsProbabilityMeasure (μN N μ)]` | Easy | 30 | — |
| B4 | §4 algorithm step | `State`, `assign`, `Avail`, `Payload`, `step` | availability-carrying one step; `step ω c = (c', some e)` iff `Avail` nonempty | Easy–Med | 90 | A1–A3 |
| B5 | §4 run | `run`, `count`, `run_count_le` ★ | `Fin.induction` run; invariant `(count ω t) j ≤ t.val` | Medium | 80 | B4 |
| B6 | §4 stopping | `Violated`, `NoViolation`, `R`, `R_le` | `R =` first `t ≤ N` with no violated event else `N`; `R ≤ N` | Easy–Med | 60 | B5 |
| B7 | §6 log | `log` (Option-valued) + `run_step_of_lt_R` + `log_eq_none_of_R_le` ★ | `t < R ⟹ ∃ e, (run ω t).2 = some e`; pad = `none` | Medium | 60 | B5, B6 |
| B8 | measurability | `measurable_run`/`measurable_count`/`measurableSet_R_eq` | all algorithm functions are measurable (from `hA`) | Medium | 100 | B4–B7 |
| C9 | §8 tree type | `WitnessTree`, `label/children/size/height`, path API (`ValidPath`, `treeAt`, `labelAt`, `depth`), `Proper`, `IsGood`, `instDecidableEq` | inductive + path API; proper = distinct child labels; good = proper + same-depth disjoint `vbl` | Medium | 200 | — |
| C10 | §9 construction core | `deepestEligible`, `attachBelow`, `attachInFirst` + **spec lemma** ★ | mutual recursion (prototype-compiled); spec: new leaf below a max-depth eligible vertex; old vertices and depths unchanged; properness preserved | **Hard** | 200 | C9 |
| C11 | §9 construction | `treeAt`, `forgetTime`, `T` ★ | reverse-scan fold (time-labeled); `T ω t := forgetTime (treeAt (log ω) t)` | Easy | 50 | C10, B7 |
| C12 | §10 Prop 10.1 | `treeAt_proper` ★ | `Proper (treeAt Λ t)` | Medium | 80 | C10, C11 |
| C13 | §11 Lemma 11.1/Cor 11.2 | `depth_gt_of_earlier_overlap`, `vbl_disjoint_of_same_depth` ★ | `q(u) < q(v) ∧ overlap ⟹ depth u > depth v`; same depth ⟹ disjoint `vbl` | Med–Hard | 150 | C10, C11 |
| C14 | §12 Prop 12.1 | `treeAt_injective` ★ | `s ≠ t → s < R ω → t < R ω → T ω s ≠ T ω t` (A-count argument) | Medium | 100 | C11–C13 |
| C15 | occurring trees good | `treeAt_isGood`, `treeAt_size_le` | occurring trees are good; `size (T ω t) ≤ t + 1 ≤ N` | Easy–Med | 60 | C12–C14 |
| D16 | §14 check | `treeProfile`, `check` + profile inequality | structural τ-check reading rows `profile j (d+1)`; deeper-vertex strict inequality | Medium | 120 | C9 |
| D17 | §14 (14.2)+(c) | `check_probability` ★ | `IsGood τ → size τ ≤ N → μN {check τ} = treeProd τ` (disjoint-coordinate independence + marginals) | **Hard** | 200 | D16, A3 |
| D18 | §14 Lemma 14.1 | `occurrence_implies_check`, `coupling` ★ | `T ω t = τ ⟹ check τ ω`; `μN {∃ t < R, T = τ} ≤ treeProd τ` | **Hard** | 250 | C13–C15, D17 |
| E19 | §17 Lemma 17.1 | `x'`, `gwWeight`, `gwWeight_telescope` ★ | (17.3)-fold; `x i ≠ 0 → gwWeight τ = ((1-x i)/x i) * ∏_u x'([u])` | Medium | 150 | C9 |
| E20 | finiteness | `treesFinset` / Fintype `𝒯_i(N)` | Fintype of proper trees rooted at `i` with `≤ N` vertices | Medium | 120 | C9 |
| E21 | §16–18 sum bound | `gwWeight_sum_le_one` ★ | `∑_{τ ∈ 𝒯_i(N)} ofReal (gwWeight τ) ≤ 1` (height-h induction + multinomial factorization) | Med–Hard | 150 | E19, E20 |
| F22 | §13 counting | `countLog_eq_sum_tree_indicators` ★ | `countLog ω i = ∑_{τ ∈ 𝒯_i(N)} [∃ t < R ω, T ω t = τ]` | Medium | 80 | C14, C15, E20 |
| F23 | §15–18 main | **`moserTardos_bound`** ★ | §1.1; `by_cases x i = 0` (coupling+root factor) vs `> 0` (GW chain) | **Hard** | 200 | F22, D18, E21 |
| F24 | §18 (5.2) | `moserTardos_total` ★ | `∫⁻ R ≤ ofReal (∑ i, x i/(1-x i))` | Easy | 40 | F23 |
| F25 | §19 tail | `moserTardos_tail` ★ | multiplicative Markov: `(N : ℝ≥0∞) * μN {R = N} ≤ ofReal (∑ i, x i/(1-x i))` | Easy–Med | 60 | F24, B8 |
| F26 | §19 constructive | `moserTardos_exists` ★ | `∃ σ : Π j, Ω j, ∀ i, σ ∉ A i` | Medium | 80 | F25 |
| F27 | §20 symmetric | `moserTardos_symmetric` (follow-up) | `ep(d+1) ≤ 1 ⟹ ∫⁻ R ≤ ofReal (m/d)` | Medium | 150 | F24, A1 |

**Critical path (20 items, ≈ 2370 lines):** A3 → B4 → B5 → B7 → C9 → C10 → C11 → C12 → C13 →
C14 → D17 → D18 → E19 → E20 → E21 → F22 → F23 → F24 → F25 → F26. The three **Hard** items are
C10 (fold invariant), D17 (check probability), D18 (coupling), F23 (assembly).

---

## 6. Total line estimate and PR split

- **Core (A1–F26): ≈ 2400–2900 lines** (sum of the table ≈ 2700; the three Hard items carry
  the variance). Plus **symmetric form (F27): ≈ 150 lines**; plus the ε–N divided tail form and
  pick-instantiation niceties ≈ 80.
- **PR split recommendation:**
  - **PR 1 — core:** everything A1–F26 in a *folder*
    `StatsMLlib/Probability/MoserTardos/` (suggested files: `VariableModel.lean` (A1–A3),
    `Algorithm.lean` (B4–B8), `WitnessTree.lean` (C9–C15), `Coupling.lean` (D16–D18),
    `GaltonWatson.lean` (E19–E21), `Basic.lean` (F22–F26 + main docstring)). At ≈ 2700 lines a
    single flat file would blow past the ~1500-line promotion trigger used for
    `LovaszLocal.lean`; agent D should confirm the folder layout against ARCHITECTURE.md. If a
    single PR is judged too large, split into PR 1a (framework + algorithm + witness trees,
    A–C, ≈ 1400 lines, culminating in Prop 12.1) and PR 1b (coupling + GW + main theorem +
    corollaries, D–F, ≈ 1300 lines) — but PR 1a then lands no named theorem, which is weaker
    for review; single-PR is preferred if maintainers accept the size.
  - **PR 2 — symmetric form** (F27) + ε–N tail refinement.
  - **PR 3+ — applications** (k-SAT, hypergraph coloring) — after the variable model, reusing
    the LLL proposal's application strategy (`Measure.pi_pi`, uniform measures).
- **Placement signal for agent D:** folder-split recommended (core ≈ 2700 lines ≫ the 1500-line
  flat-file trigger); git choreography unchanged from the LLL pattern.

---

## Risks

| # | Risk | Severity | Mitigation |
|---|---|---|---|
| 1 | **The fold-invariant spec lemma (C10)** — the deepest-eligible insertion property that Prop 10.1, Lemma 11.1 and Prop 12.1 all consume. The `Option ℕ` depth bookkeeping (root-eligible vs none) and the leftmost-child recursion are subtle; the prototype found one real bug (a `0`-ambiguity that broke parent→child depth transfer) before the `Option` fix. | **High** | Prototype already compiles the mutual recursion and the invariant's *statement* is pinned. Prove the spec by tree induction once, test against computed examples (`/tmp/mt_smoke.lean` pattern, `rfl`/`decide` on small logs); every later structural lemma only cites the spec. |
| 2 | **Coupling index bookkeeping (D16–D18)** — the `profile`/`|S_X(u)|` counts, the strict inequality `profile j (d(v)+1) > profile j (d(v')+1)` for `d(v) < d(v')`, and the resampling↔`S_X(u)` bijection with the `q(v) < q(u)` contradiction step. | **High** | The structural (profile-based) check formulation removes the sequential process and the vertex-index-type entirely; the bijection is proven once on time-labeled trees using C10's corollaries (Lemma 11.1) and transported by `forgetTime`. State the profile inequality as a standalone lemma with an explicit `Nat` proof (`omega`). |
| 3 | **Check-probability computation (D17)** — "the measure of a conjunction of cylinder tests over injectively-indexed fresh coordinates factors as a product" for `Measure.pi`. The needed ingredients exist (`Measure.pi_pi_finset`, `Pi.lean:390` coordinatewise-map, `iIndepFun`), but assembling the marginal-of-restriction lemma for the `vbl`-subtype index is new glue. | Medium–High | Agent A compiles this first (checklist A: disjoint-coordinate independence). Fallback: Finset-induction over vertices using `Measure.pi_pi_finset` directly, avoiding `iIndepFun`-level generality. |
| 4 | **Fintype `𝒯_i(N)` (E20)** — the finite set of proper witness trees with ≤ N vertices over Fintype `ι`; `deriving DecidableEq` fails for the List-children inductive (verified), so both the Fintype and the tree-Finset equality need a hand-written encoding. | Medium | Encode a tree with ≤ N vertices as `(Fin N → Fin N)`-parent-pointers × `(Fin N → ι)` with well-formedness predicates (`Fintype.ofInjective`, ~120 lines); manual `instDecidableEq` (~10 lines) for `WitnessTree`. Agent A compile-tests the finiteness. |
| 5 | **ENNReal/ℝ glue and edge cases** — `ofReal_div`/`ofReal_mul`/`ofReal_prod_of_nonneg` threading; the `by_cases x i = 0` split; `N = 0` in the tail bound (the divided form is *false* for `N = 0`). | Medium | GW algebra entirely in ℝ (division only inside `ofReal`); `ofReal_div_of_pos`/`ofReal_div_le` (Inv.lean:946,952) verified; tail bound stated multiplicatively (§1.2); `ofReal_one_sub` already exists in `LovaszLocal.lean` for the symmetric form. |
| 6 | **`Option ι`-valued log and the `pick` availability guard** — totality of `step` forces the `Avail` guard; proving the guard is vacuous for `t < R` (via `run_count_le`) is on the critical path of B7; forgetting the certificate when threading `run` would silently weaken `log`. | Medium | The prototype's `Payload` (certificate-carrying `Option {e // occurs ∧ rows available}`) typechecks end-to-end; keep the certificate in the `run` state (never project it away before B7). |

## Open questions

1. **File layout:** folder `Probability/MoserTardos/{VariableModel,Algorithm,WitnessTree,Coupling,GaltonWatson,Basic}.lean` (recommended, given ≈ 2700 core lines) vs a single flat `MoserTardos.lean` — agent D to rule on ARCHITECTURE.md compliance; the survey B estimate strongly favors the folder.
2. **`DeterminedBy` ∃-hypothesis vs data interface** (`eval : ∀ i, (Π j : vbl i, Ω j) → Prop` bundled with `hEval`): recommend the ∃-form (§4.6) + `Classical.choose`; the data form is a trivial wrapper for applications that already have `eval` in hand — include both?
3. **Log interface:** `Ω_N → ℕ → Option ι` (recommended) vs `Ω_N → ℕ → ι` with `[Nonempty ι]` + a dummy — the latter keeps the plan's `Λ t = i` shape literally but adds the Nonempty hypothesis and a junk-event in every tree lemma statement; the former needs one `simp` to unfold `some`.
4. **`hLLL` shape:** bundled `μπ (A i) ≤ ofReal (x i * ∏ j ∈ Γ vbl i, (1 - x j))` (recommended, matches `LovaszLocal.lean`) vs split `ofReal (x i) * ofReal (∏ …)`.
5. **Tie-break documentation:** the construction's deterministic tie-break (leftmost = most-recently-inserted in the prototype) is arbitrary per the notes; should the file *state* a theorem that all structural lemmas hold for any tie-break, or just fix one (recommended: fix one, note the arbitrariness in a docstring — a tie-break-parametric refactor is not worth the abstraction cost)?
6. **`μN {R = N}` vs `μN {log ω N = none}`** as the "did not finish" event: equivalent given B7, but which is the public tail-bound statement? (Recommend `R = N`, matching the notes.)
7. **Where do `countLog`'s `lintegral` measurability obligations surface:** if B8's `measurable_run` proves awkward, an alternative is to never take `lintegral` of run-dependent functions and instead bound `∫⁻ N_i` by `Σ_τ μN{…}` through *set* monotonicity (`lintegral` of a finite sum of indicators needs only measurability of the sets `{∃t < R, T = τ}`, which follows from the same B8 ingredients). Keep B8 scoped to exactly what F22–F25 consume.
8. **Scope check for agent C:** does `EdouardBonnet/moser-tardos` (active, sorry-free) already contain a sequential truncated-table MT bound we would be duplicating? Its modeling choices (if any) should be compared against §3–§4 before the blueprint is written.
