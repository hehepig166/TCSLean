# Survey A — Mathlib API Inventory & Gap Check for the Lovász Local Lemma

Survey agent A report. All paths relative to `StatsMLlib/.lake/packages/mathlib/` (mathlib v4.32.0)
or to `StatsMLlib/` (the library root). Every lemma name below was verified by reading the mathlib
sources on disk (grep + Read) or via leansearch; nothing is from memory. Unverified items are marked
TBC.

Reference for the proof being inventoried: `doc/lovasz/01_proposal/ref/gpt-notes.md`, §4–5
(asymmetric LLL via the key conditional-probability lemma 4.2; symmetric forms `ep(d+1) ≤ 1`
and `4pd ≤ 1`).

---

## 1. LLL presence check — verdict: ABSENT from mathlib v4.32.0

- `grep -rin "lovasz|lovász" Mathlib/` over the whole mathlib tree returns exactly **3 hits**, all in
  `Mathlib/Combinatorics/SetFamily/KruskalKatona.lean`:
  - line 295: doc comment "The **Lovasz formulation of the Kruskal-Katona theorem**"
  - line 301: `theorem kruskal_katona_lovasz_form` (the Lovász formulation of Kruskal–Katona,
    a completely different theorem)
  - lines 372–373: proof comments referencing that form.
- `grep -rln "LocalLemma\|Local Lemma\|dependency graph\|DependencyGraph" Mathlib/` returns
  **nothing**.
- leansearch query "Lovasz local lemma probability dependency graph": top hits are irrelevant
  (`SimpleGraph.LocallyFinite`, the `⟂ᵢ` notation declarations, `SimpleGraph.indepNum`).
- loogle cannot parse free-text queries (type patterns only); the source grep is authoritative.

**Verdict: the Lovász Local Lemma — asymmetric, symmetric, or any other variant — does not exist in
mathlib v4.32.0. No local lemma, no dependency-graph API. Everything is ours to build.**

---

## 2. Probability / independence API

### 2.1 Core predicates — `Mathlib/Probability/Independence/Basic.lean`

All declarations live in `namespace ProbabilityTheory` (opened at line 86). File imports
(`public import`): `Mathlib.Probability.Independence.Kernel.IndepFun`,
`Mathlib.MeasureTheory.Constructions.Pi`, `Mathlib.MeasureTheory.Group.Convolution`.

Definitions (exact lines):

| Name | Line | Signature (abbreviated) |
|---|---|---|
| `iIndepSets` | 96 | `(π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) : Prop` — family of π-systems independent: for all finite `s`, `f i ∈ π i`, `μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i)` |
| `IndepSets` | 102 | `(s1 s2 : Set (Set Ω)) (μ) : Prop` — two π-systems independent |
| `iIndep` | 111 | `(m : ι → MeasurableSpace Ω) (μ) : Prop` — family of σ-algebras independent |
| `Indep` | 118 | `(m₁ m₂ : MeasurableSpace Ω) (μ) : Prop` — two σ-algebras independent |
| `iIndepSet` | 124 | `(s : ι → Set Ω) (μ) : Prop` — family of *events* independent |
| `IndepSet` | 129 | `(s t : Set Ω) (μ) : Prop` — two events independent |
| `iIndepFun` | 136 | `{β : ι → Type*} [∀ x, MeasurableSpace (β x)] (f : ∀ x, Ω → β x) (μ) : Prop` |
| `IndepFun` | 144 | `[MeasurableSpace β] [MeasurableSpace γ] (f : Ω → β) (g : Ω → γ) (μ) : Prop`; notation `f ⟂ᵢ[μ] g` |

Key lemmas turning independence into probability products (all verified):

- `iIndepSets_iff` :160 — unfolds the definition as an explicit finite-product property.
- `iIndepSets.meas_biInter` :165 —
  `(h : iIndepSets π μ) (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i, i ∈ s → f i ∈ π i) :
  μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i)`.
- `iIndepSets.meas_iInter` :172 — `[Fintype ι]` version over the full index type.
- `IndepSets_iff` :175 — `IndepSets s1 s2 μ ↔ ∀ t1 t2, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2`.
- `iIndep_iff` :190 — `iIndep m μ ↔ ∀ (s : Finset ι) {f}, (∀ i ∈ s, MeasurableSet[m i] (f i)) → μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i)`.
- `iIndep.meas_biInter` :195 —
  `(hμ : iIndep m μ) (hs : ∀ i, i ∈ S → MeasurableSet[m i] (s i)) : μ (⋂ i ∈ S, s i) = ∏ i ∈ S, μ (s i)`.
- `iIndep.meas_iInter` :198 — `[Fintype ι]` version.
- `Indep_iff` :205 — two-σ-algebra product characterization.
- `IndepFun_iff` :274 and `IndepFun.meas_inter` :280 —
  `(hfg : f ⟂ᵢ[μ] g) {s t} (hs : MeasurableSet[mβ.comap f] s) (ht : MeasurableSet[mγ.comap g] t) :
  μ (s ∩ t) = μ s * μ t`.
- `iIndepFun.meas_biInter` :261 — same for families of functions.
- `iIndepSet_iff_meas_biInter` :623 —
  `(hf : ∀ i, MeasurableSet (f i)) : iIndepSet f μ ↔ ∀ s, μ (⋂ i ∈ s, f i) = ∏ i ∈ s, μ (f i)`.
- `iIndepSet.meas_biInter` :615 — forward direction of the above.
- `iIndepSets_singleton_iff` :610 —
  `iIndepSets (fun i ↦ {s i}) μ ↔ ∀ t, μ (⋂ i ∈ t, s i) = ∏ i ∈ t, μ (s i)`.
- `indepSet_iff_measure_inter_eq_mul` :579 —
  `(hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t) [IsZeroOrProbabilityMeasure μ] :
  IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t`.
- `IndepSet.measure_inter_eq_mul` :584 — `(h : IndepSet s t μ) : μ (s ∩ t) = μ s * μ t`
  (no measurability/finiteness hypothesis — the kernel-level lemma).
- `indepSet_iff_indepSets_singleton` :574 — `IndepSet s t μ ↔ IndepSets {s} {t} μ`.
- `IndepSets.indepSet_of_mem` :588 — membership in independent π-systems gives `IndepSet`.
- `Indep.indepSet_of_measurableSet` :595 — `Indep m₁ m₂ μ → MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ`.
- `indep_iff_forall_indepSet` :600 — `Indep m₁ m₂ μ ↔ ∀ s t, MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ`.

### 2.2 "A i is independent of the family {A j : j ∈ S}" — closest existing predicates

This is Definition 1.1 of the gpt-notes. The cleanest available statement is at the σ-algebra
level:

```
Indep (generateFrom {A i}) (generateFrom {t | ∃ j ∈ S, A j = t}) μ
```

Everything needed to work with this form EXISTS:

- `IndepSet_iff_Indep` :223 — `IndepSet s t μ ↔ Indep (generateFrom {s}) (generateFrom {t}) μ`
  (confirms `IndepSet` means independence of the generated σ-algebras).
- `indep_of_indep_of_le_left` :371 / `indep_of_indep_of_le_right` :375 / `indep_of_indep_of_le` :379 —
  restricting independence to coarser σ-algebras; this is how one derives the hypothesis for an
  arbitrary finite `S ⊆ ι \ (Γ i ∪ {i})` from a single per-`i` hypothesis on the whole
  non-neighbor family.
- `iIndepSet.indep_generateFrom_of_disjoint` :506 —
  `(hsm : ∀ n, MeasurableSet (s n)) (hs : iIndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
  Indep (generateFrom {t | ∃ n ∈ S, s n = t}) (generateFrom {t | ∃ k ∈ T, s k = t}) μ`
  — the exact idiom, but it requires *global* independence `iIndepSet s μ`, which the LLL does
  NOT assume (only non-neighbor independence). Useful for the variable-model application
  (Proposition 3.2), not for the LLL hypothesis itself.
- `iIndepSets.piiUnionInter_of_notMem` :548 —
  `(hp_ind : iIndepSets π μ) (haS : a ∉ S) : IndepSets (piiUnionInter π S) (π a) μ` — π-system
  version (again from global independence).
- `generateFrom_piiUnionInter_singleton_left` — `Mathlib/MeasureTheory/PiSystem.lean:399` —
  `generateFrom (piiUnionInter (fun k => {s k}) S) = generateFrom {t | ∃ k ∈ S, s k = t}`;
  identifies "σ-algebra generated by finite intersections of the A j, j ∈ S" (exactly the
  Definition 1.1 family) with the σ-algebra generated by the family `{A j : j ∈ S}`.
- `piiUnionInter` — `Mathlib/MeasureTheory/PiSystem.lean:357` —
  `(π : ι → Set (Set α)) (S : Set ι) : Set (Set α)` := finite intersections `⋂ x ∈ t, f x`,
  `t ⊆ S`, `f x ∈ π x`; a π-system if each `π x` is (`isPiSystem_piiUnionInter`, :413).
- `IndepSets.indep'` :495 / `IndepSets.indep` :488 — lift π-system independence to σ-algebra
  independence (needs `[IsZeroOrProbabilityMeasure μ]`, `IsPiSystem`, measurability).
- `indep_iSup_of_disjoint` :511 —
  `(h_le : ∀ i, m i ≤ _mΩ) (h_indep : iIndep m μ) {S T : Set ι} (hST : Disjoint S T) :
  Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ` — the workhorse for Proposition 3.2
  (events determined by disjoint variable sets, given `iIndepFun` of the variables).

**Recommended formal statement of the LLL hypothesis** (no new definition needed):

```
∀ i, Indep (generateFrom {A i}) (generateFrom {t | ∃ j, j ≠ i ∧ j ∉ Γ i ∧ A j = t}) μ
```

with `Γ i = G.neighborSet i` for a `SimpleGraph` on the index type. Finite subsets `S` are then
handled by `indep_of_indep_of_le_right` plus `generateFrom_mono`.

### 2.3 Conditional probability — `Mathlib/Probability/ConditionalProbability.lean`

`namespace ProbabilityTheory`; imports `Mathlib.MeasureTheory.Measure.Typeclasses.Probability` and
`Mathlib.Tactic.CrossRefAttribute`.

- `cond` :76 — `ProbabilityTheory.cond μ s : Measure Ω := (μ s)⁻¹ • μ.restrict s`
  (μ is an explicit argument). Notations (all scoped `ProbabilityTheory`):
  `μ[|s]` (:80), `μ[t | s]` (:83) = `cond μ s t`, `μ[|X in s]` (:130), `μ[s | X in t]` (:136),
  `μ[|X ← x]` (:143).

Lemmas relevant to the proof:

- `cond_isProbabilityMeasure_of_finite` :154 — `(hcs : μ s ≠ 0) (hs : μ s ≠ ∞) : IsProbabilityMeasure μ[|s]`;
  `cond_isProbabilityMeasure` :164 — `[IsFiniteMeasure μ] (hcs : μ s ≠ 0) : IsProbabilityMeasure μ[|s]`.
- instance `IsZeroOrProbabilityMeasure μ[|s]` :167 — **unconditional**: `μ[|s]` is zero or a
  probability measure; so conditioning on a null/∞-measure set yields the zero measure.
- `cond_eq_zero` :211 — `μ[|s] = 0 ↔ μ s = ∞ ∨ μ s = 0`; `cond_eq_zero_of_meas_eq_zero` :213;
  `cond_empty` :205 (simp); `cond_univ` :208 (simp, `[IsProbabilityMeasure μ] : μ[|univ] = μ`).
- `cond_apply` :216 — the axiomatic form:
  `(hms : MeasurableSet s) : μ[t | s] = (μ s)⁻¹ * μ (s ∩ t)`; `cond_apply'` :220 — variant
  assuming `MeasurableSet t` instead.
- `cond_apply_self` :223 — `(hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : μ[s | s] = 1` (simp).
- `cond_inter_self` :226 — `(hms : MeasurableSet s) : μ[s ∩ t | s] = μ[t | s]`.
- `inter_pos_of_cond_ne_zero` :230 — `(hms) (hcst : μ[t | s] ≠ 0) : 0 < μ (s ∩ t)`;
  `cond_pos_of_inter_ne_zero` :236 — `[IsFiniteMeasure μ] (hms) (hci : μ (s ∩ t) ≠ 0) : 0 < μ[t | s]`.
- **Multiplication rule**: `cond_mul_eq_inter'` :258 —
  `(hms : MeasurableSet s) (hcs' : μ s ≠ ∞) : μ[t | s] * μ s = μ (s ∩ t)`;
  `cond_mul_eq_inter` :264 — `[IsFiniteMeasure μ]` variant. (This is the workhorse for
  `μ(B_S) = μ(B_{S\{r}}) · μ[(A_r)ᶜ | B_{S\{r}}]`.)
- **Total probability / peeling**: `cond_add_cond_compl_eq` :268 —
  `(hms) [IsFiniteMeasure μ] : μ[t | s] * μ s + μ[t | sᶜ] * μ sᶜ = μ t`.
- `cond_cond_eq_cond_inter'` :242 / `cond_cond_eq_cond_inter` :254 — conditioning twice = conditioning on the intersection.
- Bayes: `cond_eq_inv_mul_cond_mul` :275.

For the peeling step in gpt-notes §4.1 the needed identity is
`μ (s ∩ tᶜ) = μ s · (1 - μ[t | s])` for `0 < μ s < ∞`:

```
calc
  μ (s ∩ tᶜ) = μ s - μ (s ∩ t)          -- measure_inter_add_sdiff (see below), μ s < ∞
  _          = μ s - μ[t | s] * μ s     -- cond_mul_eq_inter'
  _          = μ s * (1 - μ[t | s])     -- ENNReal: μ[t|s] ≤ 1, μ s ≠ ∞, mul_sub/eq_sub_of_add_eq
```

All ingredients EXIST; a convenience lemma can be created (`cond_inter_compl_mul_eq` or similar).

**ABSENT** (must create, small):
1. `μ[t | s] = μ t` under `IndepSet t s μ` (with `0 < μ s`, `μ s < ∞`, measurability) — the
   "independence ⇒ conditioning does nothing" lemma; direct proof:
   `cond_apply` + `IndepSet.measure_inter_eq_mul` + `ENNReal.mul_inv_cancel` (via
   `mul_eq_mul_right_iff`-style reasoning; the cancellation is `ENNReal.mul_right_inj`-adjacent —
   TBC, exact name to pick at use site, e.g. `eq_of_mul_eq_mul_right` guarded by `≠ 0` / `≠ ∞`).
2. `μ[t | sᶜ] = 1 - μ[t | s]` for probability μ, `0 < μ s`, `μ s < 1` — NOT present as such
   (only the total-probability form :268); derivable but a dedicated lemma
   (`cond_compl_eq_one_sub`) will pay for itself.
3. `μ[t | s] ≤ 1` for probability μ, `μ s ≠ 0` — trivial from `cond_apply` +
   `measure_mono`; likely to be needed repeatedly.

### 2.4 Conditional independence — `Mathlib/Probability/Independence/Conditional.lean`

- `CondIndepSet` :136 — `(s t : Set Ω) (μ) [IsFiniteMeasure μ] : Prop`
  (in a section with `variable (m' : MeasurableSpace Ω) {mΩ} [StandardBorelSpace Ω] (hm' : m' ≤ mΩ)`).
- `CondIndepSets` :94, `iCondIndepSet` :129, `CondIndep` :115, `iCondIndep` :105,
  `CondIndepFun` :155, `iCondIndepFun` :145.
- `condIndepSet_iff` :330 —
  `CondIndepSet m' hm' s t μ ↔ (μ⟦s ∩ t | m'⟧) =ᵐ[μ] (μ⟦s | m'⟧) * (μ⟦t | m'⟧)`.
- Equivalences/structural lemmas at :178–:419, `CondIndep.symm` :442, disjointness lemmas
  `iCondIndepSet.condIndep_generateFrom_of_disjoint` :560, etc.

**Verdict: NOT needed for the asymmetric LLL.** This API conditions on a σ-algebra via
conditional-expectation kernels (`condExpKernel`), requires `[StandardBorelSpace Ω]` and
`hm' : m' ≤ mΩ`, and its statements are `=ᵐ[μ]` (a.e.) equalities — far heavier than the
event-level conditioning the gpt-notes proof uses. We should NOT import this file for the core
proof. (It could matter for a future "lopsided"/σ-algebra version; note only.)

### 2.5 Misc measure facts used by the proof

- `measure_inter_add_sdiff` — `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:118` —
  `(s : Set α) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s` (the add-complement split).
- `Finset.measurableSet_biInter` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:149` —
  `(s : Finset β) (h : ∀ i ∈ s, MeasurableSet (f i)) : MeasurableSet (⋂ i ∈ s, f i)` — needed to
  apply `cond_apply`/`cond_mul_eq_inter'` to `B_S = ⋂ j ∈ S, (A j)ᶜ` and for the σ-algebra
  membership arguments in the independence step.
- Membership of finset biIntersections: `Set.mem_iInter₂` (`Mathlib/Data/Set/Lattice.lean:61`),
  `mem_iInter_of_mem` (:71), `mem_iInter₂_of_mem` (:74), `Set.mem_biInter` (:656) — `simp` handles
  `x ∈ ⋂ i ∈ s, f i` through these (there is no dedicated `Finset.mem_biInter` lemma; the finset
  version is the Set notation applied to the coercion).
- `indep_bot_right` :350 / `indep_bot_left` :353, `indepSet_empty_right` :355 /
  `indepSet_empty_left` :358 — for the empty-family corner cases (`[IsZeroOrProbabilityMeasure μ]`).

---

## 3. SimpleGraph API — `Mathlib/Combinatorics/SimpleGraph/`

- `neighborSet` — `Basic.lean:444` — `def neighborSet (v : V) : Set V := {w | G.Adj v w}`.
- `neighborFinset` — `Finite.lean:166` —
  `variable (v) [Fintype (G.neighborSet v)]` / `def neighborFinset : Finset V := (G.neighborSet v).toFinset`.
  **The required typeclass is `[Fintype (G.neighborSet v)]`, NOT `[Fintype V]`.** With a global
  `[Fintype V]`, the instance `[Fintype (G.neighborSet v)]` is synthesized automatically (a Set
  subtype of a Fintype is a Fintype), so in practice `[Fintype V]` suffices.
- `neighborFinset_def` :169 (rfl), `coe_neighborFinset` :173 (simp, norm_cast),
  `mem_neighborFinset` :177 — `w ∈ G.neighborFinset v ↔ G.Adj v w` (simp),
  `notMem_neighborFinset_self` :180, `neighborFinset_eq_empty` :188 (simp),
  `neighborFinset_nonempty` :191 (simp), `neighborFinset_eq_filter` :350
  (`[DecidableRel G.Adj]`), `neighborFinset_compl` :353 (`[DecidableEq V] [DecidableRel G.Adj]`).
- `degree` — `Finite.lean:200` — `def degree : ℕ := #(G.neighborFinset v)` (same
  `[Fintype (G.neighborSet v)]` context);
  `card_neighborFinset_eq_degree` :203 (simp), `degree_eq_zero` :208, `degree_pos` :209.
- `maxDegree` — `Finite.lean:427` — `def maxDegree [DecidableRel G.Adj] : ℕ :=
  WithBot.unbotD 0 (univ.image fun v => G.degree v).max` (needs `[Fintype V]` in scope for `univ`);
  `exists_maximal_degree_vertex` :433, `degree_le_maxDegree` / `maxDegree_le_of_forall_degree_le`
  (referenced in doc at :425–426).

**Dependency-graph style API: ABSENT.** No `DependencyGraph`, no local-lemma infrastructure. The
LLL statement will use a bare `SimpleGraph ι` (self-loops disallowed by definition — good, since a
dependency graph has no loops) and `G.neighborSet i` / `G.degree i` / `G.maxDegree`.

---

## 4. Finset / big operators

### Strong induction

- `Finset.strongInduction` — `Mathlib/Data/Finset/Card.lean:838` —
  `def strongInduction {p : Finset α → Sort*} (H : ∀ s, (∀ t ⊂ s, p t) → p s) : ∀ s, p s`.
- `Finset.strongInductionOn` — `Card.lean:852` — argument-swapped version, `(s : Finset α)` first.
  `strongInductionOn_eq` :855 is the equation lemma (unfold/fixpoint).
- `Finset.case_strong_induction_on` — `Card.lean:862` — `[DecidableEq α] {p : Finset α → Prop}
  (s : Finset α) (h₀ : p ∅) ...` — case-analysis form.
- Note: these induct on `⊂` (strict subset), which for finsets is equivalent to `#t < #s`
  (`Finset.ssubset_iff_card_lt`-style reasoning; `card_erase_lt_of_mem` below supplies the
  descent step). Inducting on `⊂` directly matches the gpt-notes induction on `|S|` without
  re-indexing.

### Product lemmas

- `Finset.prod_le_prod'` — `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:109` —
  `[MulLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` (gcongr).
- `Finset.prod_le_prod` — `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:38` —
  `[CommMonoidWithZero R] [Preorder R] [ZeroLEOneClass R] [PosMulMono R]
  (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i` — the ℝ /
  ℝ≥0 / ENNReal-friendly variant.
- **`Finset.prod_le_prod_of_subset_of_le_one'`** — `Group/Finset.lean:141` —
  `[CommMonoid N] [Preorder N] [MulLeftMono N] (h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
  ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i` — **exactly** step (6) of the gpt-notes proof
  (`∏_{j ∈ Γ(i)} (1-α_j) ≤ ∏_{j ∈ N} (1-α_j)` for `N ⊆ Γ(i)`, factors `≤ 1`).
- `Finset.prod_le_prod_of_subset_of_one_le'` :132 — the `1 ≤`-factor dual.
- `Finset.prod_le_one'` — `Group/Finset.lean:128` — `[MulLeftMono N] (h : ∀ i ∈ s, f i ≤ 1) :
  ∏ i ∈ s, f i ≤ 1` — for the base case `∏_{j ∈ Γ(i)} (1-α_j) ≤ 1`.
- `Finset.prod_le_one` — `GroupWithZero/Finset.lean:50` — `(h0 : ∀ i ∈ s, 0 ≤ f i)
  (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1`.
- `Finset.one_le_prod` :55 (GroupWithZero) / `one_le_prod'` :120 (Group) — factors `≥ 1`.
- `Finset.prod_pos` — `GroupWithZero/Finset.lean:107` —
  `(h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i` — for `∏_{i} (1 - x i) > 0` from `x i < 1`.
- `Finset.prod_nonneg` — `GroupWithZero/Finset.lean:31` — `(h0 : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i`.
- `Finset.prod_insert` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:49` —
  `[DecidableEq ι] : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x` (peeling a singleton).
- `Finset.prod_eq_mul_prod_diff_singleton` — alias at
  `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:202` (of
  `prod_eq_mul_prod_sdiff_singleton`; the `_of_mem` variant at :210) — for splitting a product
  at a chosen element `a ∈ s`.
- `Finset.prod_filter_mul_prod_filter_not` — `Group/Finset/Basic.lean:144` — partition into
  `N` and `M = S \ N` in the induction step.

### Erase / card / membership

- `Finset.mem_erase` — `Mathlib/Data/Finset/Erase.lean:57` — `a ∈ erase s b ↔ a ≠ b ∧ a ∈ s`.
- `Finset.erase_eq_of_notMem` — `Erase.lean:75` — `(h : a ∉ s) : erase s a = s`.
- `Finset.erase_insert` — `Mathlib/Data/Finset/Basic.lean:134` — `(h : a ∉ s) : (insert a s).erase a = s`;
  `erase_insert_of_ne` :136; `erase_eq` :204 — `s.erase a = s \ {a}`.
- `Finset.card_erase_of_mem` — `Mathlib/Data/Finset/Card.lean:152` — `a ∈ s → #(s.erase a) = #s - 1`.
- `Finset.card_erase_lt_of_mem` — `Card.lean:159` — `a ∈ s → #(s.erase a) < #s` — the descent step
  of the strong induction.

---

## 5. ENNReal vs ℝ

### ENNReal.ofReal algebra — `Mathlib/Data/ENNReal/Real.lean` (and Basic/Operations/BigOperators)

- `ENNReal.ofReal_mul` — `Real.lean:297` — `(hp : 0 ≤ p) : ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q`;
  `ofReal_mul'` :301 — variant assuming `0 ≤ q`.
- `ENNReal.ofReal_le_ofReal` — `Real.lean:137` — `(h : p ≤ q) : ofReal p ≤ ofReal q`;
  `ofReal_le_ofReal_iff` :147 — `(h : 0 ≤ q) : ofReal p ≤ ofReal q ↔ p ≤ q`;
  `ofReal_lt_ofReal_iff` :167 — `(h : 0 < q)`; `ofReal_lt_ofReal_iff_of_nonneg` :171.
- `ENNReal.ofReal_one` — `Basic.lean:297` (simp) — `ofReal 1 = 1`.
- `ENNReal.ofReal_ne_top` — `Basic.lean:344`; `ENNReal.ofReal_lt_top` :346 (simp) — `ofReal x < ∞`
  always; this is what makes `sub`/`mul_inv_cancel` applicable to `ofReal`-values.
- `ENNReal.ofReal_pow` — `Real.lean:306` — `(hp : 0 ≤ p) (n : ℕ) : ofReal (p ^ n) = ofReal p ^ n`.
- `ENNReal.ofReal_add` — `Real.lean:52` — `(hp : 0 ≤ p) (hq : 0 ≤ q) : ofReal (p + q) = ofReal p + ofReal q`;
  `ofReal_add_le` :57.
- **`ENNReal.ofReal_sub`** — `Operations.lean:435` —
  `(p : ℝ) {q : ℝ} (hq : 0 ≤ q) : ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q`.
  With `p = 1` and `ofReal_one` this is the one-sub-ofReal fact:
  `ENNReal.ofReal (1 - x) = 1 - ENNReal.ofReal x` for `x ≥ 0` (when `1 - x < 0` both sides are 0 —
  truncated subtraction — so the identity is unconditional, and it is an exact (non-truncating)
  equality on the `[0,1]` range used in the LLL).
- `ENNReal.ofReal_prod_of_nonneg` — `BigOperators.lean:64` —
  `(hf : ∀ i, i ∈ s → 0 ≤ f i) : ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i)` —
  the bridge for the final conclusion `∏ (1 - x_i) ≤ μ (⋂ (A i)ᶜ)`.
- `ENNReal.toReal_prod` — `BigOperators.lean:60`; `ENNReal.prod_ne_top` :90; `prod_lt_top` :93 —
  products of finite factors stay finite.

### ENNReal subtraction — `Mathlib/Data/ENNReal/Operations.lean` (with `OrderedSub` instance at `Basic.lean:168`)

- `ENNReal.sub_eq_of_eq_add` — :306 — `(hb : b ≠ ∞) : a = c + b → a - b = c`
  (and `sub_eq_of_eq_add'` :311 with `ha : a ≠ ∞`; `sub_eq_of_eq_add_rev` :326).
- `ENNReal.eq_sub_of_add_eq` — :316 — `(hc : c ≠ ∞) : a + c = b → a = b - c`.
- `ENNReal.add_sub_cancel_left` :334 / `add_sub_cancel_right` :337 — `(ha/hb : _ ≠ ∞)`.
- `ENNReal.sub_le_sub_iff_left` :417 — `(h : c ≤ a) (h' : a ≠ ∞) : a - c ≤ b - c ↔ a ≤ b`.
- `ENNReal.sub_sub_cancel` :400 — `(h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b`.
- `ENNReal.sub_mul` :408 / `mul_sub` :413 — distributing multiplication over truncated
  subtraction under finiteness guards — used in `μ s * (1 - μ[t|s])` rewrites.
- Generic `tsub_le_tsub_left` / `tsub_le_tsub_right` — `Mathlib/Algebra/Order/Sub/Defs.lean:115`/`:102` —
  `(h : a ≤ b) (c) : c - b ≤ c - a` / `(h : a ≤ b) (c) : a - c ≤ b - c` — instantiate to ENNReal
  via the `OrderedSub` instance; `tsub_le_tsub_left` with `c = 1` is the monotonicity of
  `1 - ·` used in the peeling step.
- `ENNReal.toReal_sub_of_le` — `Operations.lean:432` — `(hba : b ≤ a) (ha : a ≠ ∞) :
  (a - b).toReal = a.toReal - b.toReal` (simp) — for the ℝ corollary.

### ENNReal multiplication / division / inversion

- `mul_le_mul'` — `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:209` —
  `[MulLeftMono α] [MulRightMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d` (gcongr);
  `mul_le_mul_left` :81 / `mul_le_mul_right` :70 — one-sided versions. ENNReal has the required
  instances; `gcongr`/`positivity` will do most of the bookkeeping.
- `ENNReal.inv_le_inv` — `Mathlib/Data/ENNReal/Inv.lean:297` — `a⁻¹ ≤ b⁻¹ ↔ b ≤ a`;
  `inv_le_inv'` :306 (gcongr, forward version); `one_le_inv` :314 — `1 ≤ a⁻¹ ↔ a ≤ 1`;
  `mul_inv_le_one` :398 — `a * a⁻¹ ≤ 1`.
- `ENNReal.div_le_div_right` — `Inv.lean:468` — `(h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c`.
- `ENNReal.le_div_iff_mul_le` — `Inv.lean:363` —
  `(h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : a ≤ c / b ↔ a * b ≤ c` — multiply-up form for
  the division step (3) of the gpt-notes.

### The ℝ-valued probability API (`probReal`) — has been renamed to `Measure.real`

Important API change in mathlib v4.32.0 (post-dates many references): the old
`ProbabilityTheory.probReal` **function no longer exists**. The current API is:

- `Measure.real` — `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:101` —
  `protected def Measure.real (μ : Measure α) (s : Set α) : ℝ := (μ s).toReal`; used as `μ.real s`.
- Lemma API in `Mathlib/MeasureTheory/Measure/Real.lean` (namespace `MeasureTheory`):
  `measureReal_eq_zero_iff` :40, `measureReal_nonneg` :53 (simp), `measureReal_empty` :55 (simp),
  `probReal_univ` : (also in `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:118`) —
  `@[simp] lemma probReal_univ : μ.real univ = 1`,
  `probReal_compl_eq_one_sub` : Real.lean:485 — `(hs : MeasurableSet s) : μ.real sᶜ = 1 - μ.real s`
  (₀-variant :482), `probReal_add_probReal_compl` : Typeclasses/Probability.lean:95,
  `ofReal_measureReal` : Real.lean:67 — `(h : μ s ≠ ∞) : ENNReal.ofReal (μ.real s) = μ s`,
  `measureReal_mono` :90, `measureReal_inter_add_sdiff` :239,
  `measureReal_add_measureReal_compl` :225.
  (Some lemma names still begin with `probReal`; `measureReal_univ_eq_one` is a
  *deprecated* alias of `probReal_univ`, Real.lean:57.)
- Bridge to ENNReal: `ENNReal.toReal_le_toReal` — `Real.lean:61` —
  `(ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal ≤ b.toReal ↔ a ≤ b` — turns the ENNReal LLL statement
  into the ℝ corollary.

### Awkward points of the ENNReal route (from gpt-notes §4.1)

- Step (2), numerator monotonicity `μ(A_i ∩ B_N | B_M) ≤ μ(A_i | B_M)`: fine — `cond_apply` +
  `measure_mono` + `mul_le_mul'`.
- Step (3), the division `μ[A_i | B_S] ≤ μ(A_i) / μ(B_N | B_M)`: **recommend the multiplied-up
  form** `μ[A_i | B_S] * μ(B_N | B_M) ≤ μ(A_i)` (via `ENNReal.le_div_iff_mul_le`), and at the end
  divide by the same positive finite factor `μ(B_N | B_M)` using `ENNReal.div_le_div_right` —
  avoiding `a / b ≤ c` shapes and their `∞`/`0` case splits.
- The cancellation `(α_i * D) / D = α_i` needs `D ≠ 0` and `D ≠ ∞`; `D = μ(B_N | B_M)` satisfies
  `0 < D` (from `∏ (1-α_j) ≤ D` and positivity of the product) and `D ≤ 1 < ∞` (from the
  `μ[t|s] ≤ 1` glue lemma in §2.3).
- `1 - μ[A_r | B]` is exact (no truncation) precisely because `μ[A_r | B] ≤ 1` — another reason to
  prove that glue lemma early.
- Nothing in the proof requires `ENNReal` subtraction of two *arbitrary* quantities; all
  subtractions are `1 - something ≤ 1` or `μ s - μ (s ∩ t)` with `μ s < ∞` (probability measure).

---

## 6. Real inequalities for the symmetric versions

- **Bernoulli** `(1 - x)^d ≥ 1 - d·x` for `x ∈ [0,1]`:
  `one_add_mul_le_pow` — `Mathlib/Algebra/Order/Ring/Pow.lean:100` —
  `[Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : ℕ} (H : -2 ≤ a) :
  1 + n * a ≤ (1 + a) ^ n`.
  Instantiate `R = ℝ`, `a = -x`: needs `-2 ≤ -x` ⇔ `x ≤ 2` ✓ for `x ∈ [0,1]`; then
  `ring_nf`/`simp [sub_eq_add_neg]` converts `1 + n * (-x) ≤ (1 + (-x)) ^ n` to
  `1 - n * x ≤ (1 - x) ^ n`. (Used with `x = 1/(2d)` for the `4pd ≤ 1` criterion.)
  Also available: `one_add_le_pow_of_two_add_nonneg` (same file, :92) for linear ordered
  semirings.
- **`(1 + 1/d)^d ≤ e`**: `Real.one_add_inv_pow_le_exp` — `Mathlib/Analysis/Complex/Exponential.lean:653` —
  `lemma one_add_inv_pow_le_exp {n : ℕ} : (1 + (n : ℝ)⁻¹) ^ n ≤ exp 1`
  (in `namespace Real`; the file despite its name hosts the ℝ exp API in `namespace Real`,
  opened at line 200). Caution: for `n = 0` the LHS is `1^0 = 1 ≤ e` ✓, so no `d ≥ 1` caveat
  needed here.
- **`(d/(d+1))^d ≥ e⁻¹`**: NOT a named lemma; one-line glue:
  `d/(d+1) = (1 + 1/d)⁻¹` (`field_simp`, `d ≠ 0`), so
  `(d/(d+1))^d = ((1 + 1/d)^d)⁻¹ ≥ e⁻¹` via `Real.one_add_inv_pow_le_exp` (n := d) +
  `inv_le_inv₀` — `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1218` —
  `(ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a` (positivity of `(1+1/d)^d` and `e` by
  `Real.exp_pos` — `Exponential.lean:282` — `theorem exp_pos (x : ℝ) : 0 < exp x`, in `namespace Real`).
- **`1 - x ≤ e^{-x}` / `1 - x < e^{-x}` (x ≠ 0)**: `Real.one_sub_le_exp_neg` / `Real.one_sub_lt_exp_neg` —
  `Exponential.lean:638` / `:635`. Related: `Real.add_one_le_exp` :631 — `(x : ℝ) : x + 1 ≤ exp x`,
  `Real.add_one_lt_exp` :622 — `(hx : x ≠ 0) : x + 1 < exp x`,
  `Real.one_sub_div_pow_le_exp_neg` :642 — `{n : ℕ} {t : ℝ} (ht' : t ≤ n) :
  (1 - t / n) ^ n ≤ exp (-t)` (the lemma `one_add_inv_pow_le_exp` is built from).
- `Real.exp_ne_zero` — `Exponential.lean:235` (`nonrec theorem exp_ne_zero`) — for division by `e`.
- ABSENT (but not needed): a named `(1 - 1/n)^n ≥ 1/e`-style lemma; the two-step glue above
  suffices, and `(1+1/d)^d ≤ e` is already exactly the gpt-notes' "standard inequality".

---

## 7. StatsMLlib local infrastructure

### `StatsMLlib/Probability/Independence/FinsetPi.lean` (103 lines)

Imports (all clean, all in mathlib v4.32.0):
- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`
- `Mathlib.Probability.Independence.Basic`
- `Mathlib.MeasureTheory.Constructions.Pi`

API (namespace-free, top-level; opens `MeasureTheory ProbabilityTheory`):

- `pi_map_eval` :28 —
  `{ι : Type*} {Ω : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, MeasurableSpace (Ω i)]
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] (k : ι) :
  (Measure.pi μ).map (Function.eval k) = μ k` — coordinate marginal of a finite product measure.
- `pi_eval_iIndepFun` :48 —
  `[MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] :
  iIndepFun Function.eval (Measure.pi fun _ ↦ μ : Measure (ι → Ω))` — coordinate projections of
  iid copies are independent.
- `pi_comp_eval_iIndepFun` :101 —
  `[MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]
  {𝓧 : Type*} [MeasurableSpace 𝓧] {X : Ω → 𝓧} (hX : Measurable X) :
  iIndepFun (fun i ↦ X ∘ Function.eval i) (Measure.pi fun _ ↦ μ)` — independence after applying a
  measurable map coordinatewise (via `iIndepFun.comp`).

This is exactly the variable-model infrastructure for gpt-notes §3.1/Proposition 3.2
(events determined by disjoint variable sets): from `pi_eval_iIndepFun` +
`iIndepFun_iff_iIndep` + `indep_iSup_of_disjoint` + `indep_of_indep_of_le` one gets
`Indep (generateFrom {A i}) (generateFrom {A j | j ∈ S})` whenever the variable sets are
disjoint. The glue for this (comparing `generateFrom {A i}` with the ⨆ of comaps of the
relevant coordinates) is **not yet in StatsMLlib** and must be created for the applications
section (not needed for the core LLL statement, whose hypothesis can be stated directly).

### Other local facts

- `grep -rn "Lovasz|Lovász" StatsMLlib/` — **no hits**; nothing LLL-related exists locally.
- `grep -rn "ProbabilityTheory.cond" StatsMLlib/` — **no hits**; StatsMLlib does not yet use
  `ProbabilityTheory.cond` anywhere (only unrelated `[|`-looking absolute-value bars in comments).
- StatsMLlib layout: `StatsMLlib/Probability/{Concentration,Entropy,Gaussian,Independence,Moments,
  Process,RandomMatrix,SmallBall}`. A natural home for the LLL:
  `StatsMLlib/Probability/LocalLemma.lean` (or a `Probability/LocalLemma/` folder mirroring
  mathlib style).
- Conventions to respect (lakefile.lean): `autoImplicit` is OFF; weak linters active include
  `longLine`, `style.lambdaSyntax`, `oldObtain`, `refine`, `dollarSyntax` — new code must avoid
  `refine`/`obtain`-style pitfalls. Fine-grained mathlib imports (no `import Mathlib`).
- `FinsetPi.lean` is currently the **only** file in `StatsMLlib/Probability/Independence/`; adding
  `StatsMLlib/Probability/Independence/IndepEvents.lean` (or similar) for the LLL glue lemmas
  (cond-under-independence, dependency-graph-from-disjoint-variables) fits the existing structure.

---

## 8. Gap summary

Legend: ✅ = exists (name verified), 🟡 = exists but needs a thin glue lemma, ❌ = must create.

| Needed ingredient | Status | Exact name (mathlib, path relative to `.lake/packages/mathlib/`) or proposed name |
|---|---|---|
| LLL itself (any variant) | ❌ | ABSENT — proposed `ProbabilityTheory.LovaszLocalLemma` / `lovasz_local_lemma_asymmetric` in StatsMLlib |
| Two events independent | ✅ | `ProbabilityTheory.IndepSet` — `Mathlib/Probability/Independence/Basic.lean:129` |
| Family of events independent | ✅ | `ProbabilityTheory.iIndepSet` — `Basic.lean:124` |
| Two σ-algebras independent | ✅ | `ProbabilityTheory.Indep` — `Basic.lean:118` |
| Independence → product `μ (s ∩ t) = μ s * μ t` | ✅ | `IndepSet.measure_inter_eq_mul` :584; `indepSet_iff_measure_inter_eq_mul` :579 |
| Family independence → biInter product | ✅ | `iIndep.meas_biInter` :195; `iIndepSet.meas_biInter` :615 |
| "A i ⟂ family {A j : j ∈ S}" as a statement | ✅ | `Indep (generateFrom {A i}) (generateFrom {t | ∃ j ∈ S, A j = t}) μ`; supported by `generateFrom_piiUnionInter_singleton_left` (`Mathlib/MeasureTheory/PiSystem.lean:399`), `indep_of_indep_of_le_left/right` :371/:375 |
| Independence from disjoint index sets (global indep) | ✅ | `iIndepSet.indep_generateFrom_of_disjoint` :506; `indep_iSup_of_disjoint` :511; `iIndepSets.piiUnionInter_of_notMem` :548 |
| Conditional probability measure | ✅ | `ProbabilityTheory.cond` — `Mathlib/Probability/ConditionalProbability.lean:76` (notation `μ[t | s]`) |
| Multiplication rule | ✅ | `cond_mul_eq_inter'` :258 / `cond_mul_eq_inter` :264 |
| Total probability (complement) | ✅ | `cond_add_cond_compl_eq` :268 |
| Add-complement measure split | ✅ | `measure_inter_add_sdiff` — `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:118` |
| Cond of complement = 1 − cond | 🟡 | derive from :268 + `sub_eq_of_eq_add`; propose `cond_compl_eq_one_sub` |
| Cond under independence (`μ[t|s] = μ t`) | 🟡 | propose `cond_eq_of_indepSet` (from `cond_apply` + `IndepSet.measure_inter_eq_mul`) |
| `μ[t|s] ≤ 1` for probability μ | 🟡 | propose `cond_le_one` (from `cond_apply` + `measure_mono` + `mul_inv_cancel`) |
| Cond behavior at μ s = 0 or ∞ | ✅ | `cond_eq_zero` :211; instance `IsZeroOrProbabilityMeasure μ[|s]` :167 |
| Conditional independence | ✅ (not needed) | `CondIndepSet` etc. — `Mathlib/Probability/Independence/Conditional.lean:136`; skip for core proof |
| Dependency graph data | ✅ | `SimpleGraph`; `neighborSet` `Basic.lean:444`; `neighborFinset` `Finite.lean:166` (needs `[Fintype (G.neighborSet v)]`, auto from `[Fintype V]`); `degree` `Finite.lean:200`; `maxDegree` `Finite.lean:427` (`[DecidableRel G.Adj]`) |
| "Dependency graph" API | ❌ | ABSENT — our own `IsDependencyGraph` definition |
| Strong induction on Finsets | ✅ | `Finset.strongInductionOn` — `Mathlib/Data/Finset/Card.lean:852`; `case_strong_induction_on` :862 |
| Descent `#(s.erase a) < #s` | ✅ | `Finset.card_erase_lt_of_mem` — `Card.lean:159`; `card_erase_of_mem` :152 |
| `∏_{t} f ≤ ∏_{s} f` for `s ⊆ t`, factors ≤ 1 | ✅ | `Finset.prod_le_prod_of_subset_of_le_one'` — `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:141` |
| Product ≤ 1 for factors ∈ [0,1] | ✅ | `Finset.prod_le_one` — `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:50` |
| Strict positivity of product | ✅ | `Finset.prod_pos` — `GroupWithZero/Finset.lean:107` |
| Peeling a product at a member | ✅ | `Finset.prod_insert` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:49`; `prod_eq_mul_prod_diff_singleton` — `Piecewise.lean:202` |
| Measurability of `⋂ j ∈ S, (A j)ᶜ` | ✅ | `Finset.measurableSet_biInter` — `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:149` |
| ofReal mul / prod / sub / one / le | ✅ | `ENNReal.ofReal_mul` `Real.lean:297`; `ofReal_prod_of_nonneg` `BigOperators.lean:64`; `ofReal_sub` `Operations.lean:435`; `ofReal_one` `Basic.lean:297`; `ofReal_le_ofReal` `Real.lean:137` |
| ENNReal truncated subtraction under finiteness | ✅ | `ENNReal.sub_eq_of_eq_add` `Operations.lean:306`; `add_sub_cancel_left/right` :325/:330; `sub_mul` :408 / `mul_sub` :413; `tsub_le_tsub_left` `Mathlib/Algebra/Order/Sub/Defs.lean:115` (via `OrderedSub` instance `Basic.lean:168`) |
| ENNReal division / multiply-up | ✅ | `ENNReal.div_le_div_right` `Inv.lean:468`; `ENNReal.le_div_iff_mul_le` `Inv.lean:363` |
| ℝ probability API | ✅ | `Measure.real` — `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:101`; `probReal_compl_eq_one_sub` `Real.lean:485`; `ofReal_measureReal` `Real.lean:67`; `ENNReal.toReal_le_toReal` `Real.lean:61` (old `probReal` function is gone) |
| Bernoulli `(1-x)^d ≥ 1-dx` | ✅ | `one_add_mul_le_pow` — `Mathlib/Algebra/Order/Ring/Pow.lean:100` |
| `(1+1/d)^d ≤ e` | ✅ | `Real.one_add_inv_pow_le_exp` — `Mathlib/Analysis/Complex/Exponential.lean:653` |
| `(d/(d+1))^d ≥ e⁻¹` | 🟡 | glue from `Real.one_add_inv_pow_le_exp` + `inv_le_inv₀` (`Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1218`) + `Real.exp_pos` (`Exponential.lean:282`); propose `one_add_inv_pow_inv_le_inv_exp` or inline |
| Variable-model independence (iid coordinates) | ✅ | StatsMLlib `pi_eval_iIndepFun`, `pi_comp_eval_iIndepFun`, `pi_map_eval` — `StatsMLlib/Probability/Independence/FinsetPi.lean:48/:101/:28` |
| Events-from-disjoint-variables ⇒ dependency graph | 🟡 | glue: `iIndepFun_iff_iIndep` + `indep_iSup_of_disjoint` + `indep_of_indep_of_le`; propose `StatsMLlib/Probability/Independence/IndepEvents.lean` |

**Top three must-create items** (small, standalone, all in one new StatsMLlib file):
1. `cond_le_one`, `cond_compl_eq_one_sub`, `cond_eq_of_indepSet` — the cond glue package.
2. `IsDependencyGraph` definition + the LLL hypothesis statement.
3. Variable-model glue (`iIndepFun` of coordinates ⇒ the `Indep (generateFrom {A i}) (generateFrom {A j | j ∈ S})` hypothesis) for the applications.
