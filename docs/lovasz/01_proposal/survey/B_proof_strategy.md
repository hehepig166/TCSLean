# B. Proof Strategy & Formalization Plan (Asymmetric LLL)

**Scope note.** This survey assumes mathlib `v4.32.0` (pinned by `StatsMLlib/lakefile.lean`; `lake-manifest.json` rev `81a5d257c8e410db227a6665ed08f64fea08e997`) and targets the **asymmetric Lovász Local Lemma** (gpt-notes Theorem 4.1) with the weak dependency-graph hypothesis. All lemma names cited below were verified by grepping `StatsMLlib/.lake/packages/mathlib/Mathlib/` unless marked **TBC**. Names marked **NEW** must be created.

**Key finding:** the gpt-notes proof can be fully reorganized as a *peeling* strong induction over arbitrary finite subsets `S ⊆ ι` (Section 1.1 below). This removes the enumeration-based chain rule used in the final assembly of gpt-notes §4.2 — consequently **no linear order on the index type is needed** and the theorem can be stated over an arbitrary `[Fintype ι] [DecidableEq ι]`. The induction simultaneously proves two order-free inequalities (P1)/(P2) (Section 1.3), and the final product bound falls out of (P1) at `S = univ`; the gpt-notes chain-rule step (4) inside Lemma 4.2 is replaced by a nested `Finset.induction` over `N` (Section 2, step 8).

---

## 1. Pinned theorem statement

### 1.0 Precise math statement (target)

Let `μ` be a probability measure on a measurable space `Ω` and let `A i ⊆ Ω` be a measurable "bad event" for each `i ∈ ι`, `ι` finite. Let `G` be a finite simple undirected graph on `ι` such that **for every `i` and every `S ⊆ ι` with `i ∉ S` and every `j ∈ S` a non-neighbor of `i`, the event `A i` is independent of `B_S := ⋂_{j∈S} (A j)ᶜ`** (this is exactly the fragment of gpt-notes Definition 3.1/1.1 that the proof consumes — see §1.2). If there exist reals `x_i ∈ [0,1)` with

```
μ (A i) ≤ x_i · ∏_{j ∈ Γ(i)} (1 - x_j)      for all i          (LLL)
```

where `Γ(i) := {j : G.Adj i j}` is the open neighborhood of `i`, then

```
∏_{i ∈ ι} (1 - x_i) ≤ μ (⋂_{i ∈ ι} (A i)ᶜ)      and in particular 0 < μ (⋂_{i ∈ ι} (A i)ᶜ).
```

### 1.1 Index type: `{ι : Type*} [Fintype ι] [DecidableEq ι]` — decided, no total order needed

**Decision: arbitrary finite type, not `Fin n`.** Justification and sanity check against the proof:

- *Lemma 4.2 induction step* (gpt-notes): picks `r ∈ S`, partitions `S` into `N := S ∩ Γ(i)` and `M := S \ N`. No order is used — only the chain rule (4), which enumerates `N = {j_1,…,j_ℓ}`. This is the **only** order dependence in the whole gpt-notes proof.
- *Theorem 4.1 assembly* (gpt-notes §4.2): applies the chain rule over an enumeration of `[m]`. Again the only order use.
- **Replacement (order-free):** the final assembly is replaced by (P1) at `S = univ` (see §1.3), and the chain rule (4) is replaced by the following peeling identities over `Finset`s, valid for any `ι` with `DecidableEq`:

  ```
  (i)   bset A (insert r T) = (A r)ᶜ ∩ bset A T              (r ∉ T)
  (ii)  μ (bset A (insert r T)) + μ (A r ∩ bset A T) = μ (bset A T)   -- disjoint union
  (iii) bset A (N ∪ M) = bset A N ∩ bset A M                 (Disjoint N M)
  (iv)  M ⊆ S  ⟹  bset A S ⊆ bset A M
  ```

  (ii) is the peeling identity that replaces both chain-rule uses; iterating it over `N` by nested `Finset.induction` reproduces (5) of gpt-notes without any enumeration. **The claim "no total order on ι is needed" is verified** — the proof only ever needs `Finset.erase`, `Finset.filter`, `Finset.union`, and `Finset.strongInductionOn` (well-founded on `Finset.card`; exists at `Mathlib/Data/Finset/Card.lean:852`), none of which require an order on `ι`.
- Benefit: applications (k-SAT clauses, hypergraph edges) get their natural index types; no `Fin n` transport glue (unlike the Talagrand survey, which needed `measure_pi_snoc`).

### 1.2 Dependency structure: `SimpleGraph ι` — decided

**Decision: `SimpleGraph ι`** (mathlib `Combinatorics.SimpleGraph`), not a raw relation. Justification:

- `Γ(i)` products become `∏ j ∈ G.neighborFinset i, (1 - x j)`: `SimpleGraph.neighborFinset` (Finite.lean:166) needs only `[Fintype (G.neighborSet v)]`, and that instance is automatic under `[Fintype ι] [DecidableRel G.Adj]` (the old `neighborSetFintype` abbrev is `@[deprecated inferInstance]` since 2026-04-29). `@[simp] mem_neighborFinset : w ∈ G.neighborFinset v ↔ G.Adj v w`, and `notMem_neighborFinset_self` gives loop-freeness for free, which is what makes Definition 3.1's `Γ(i) ∪ {i}` collapse to `Γ(i)`.
- The symmetric corollaries read well: `G.degree i` (`(G.neighborFinset i).card`, rfl) for `|Γ(i)|`, hypothesis `∀ i, G.degree i ≤ d` — no `max` over `univ` needed.
- A raw relation would force us to bundle symmetry and irreflexivity as hypotheses everywhere. With `SimpleGraph` the user must supply these proofs once at construction (k-SAT: `Adj i j := i ≠ j ∧ (vbl i ∩ vbl j).Nonempty` — the `i ≠ j` guard is the only extra bookkeeping).

**Independence hypothesis — weak form, recommended for the first version:**

```
def bset (A : ι → Set Ω) (S : Finset ι) : Set Ω := ⋂ j ∈ S, (A j)ᶜ     -- = Finset.inf, see §1.4

def IsDependencyGraph (G : SimpleGraph ι) (A : ι → Set Ω) : Prop :=
  ∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) → IndepSet (A i) (bset A S)
```

Tracing the gpt-notes proof: the **only** independence facts used are
- `P(A i | B_M) = P(A i)` for the non-neighbor part `M` of `S` (gpt-notes Lemma 4.2, `N ≠ ∅` case), and
- `P(A i | B_S) = P(A i)` when `S` is all non-neighbors (the `N = ∅` case).

Both are exactly `IndepSet (A i) (bset A S)` instances, i.e. `μ (A i ∩ bset A S) = μ (A i) · μ (bset A S)` via `indepSet_iff_measure_inter_eq_mul` (Basic.lean:579, needs measurability of both sets and `[IsZeroOrProbabilityMeasure μ]`). The strong classical hypothesis (gpt-notes Def 1.1, independence from every Boolean combination) is **never needed**. Notes:

- **(a) Strong form (classical):** in mathlib terms this is `iIndepSet` / `IndepSets` applied to the atoms of the generated σ-algebra, e.g. `Indep (generateFrom {s | s = A i ∨ s = (A i)ᶜ}) (generateFrom {s | ∃ j ∈ S, s = A j ∨ s = (A j)ᶜ}) μ`, or `iIndepSet` on a two-element family. The equivalence with the weak form is classical (the π-system `{bset A T | T ⊆ S}` generates the same algebra as `{A j, (A j)ᶜ | j ∈ S}`) and provable via `indepSets_singleton_iff` / `iIndepSets.iIndep` (Basic.lean:34,574,619) plus an atoms lemma — but it is nontrivial (~100–150 lines). **Defer.**
- **(b) Weak form (recommended):** exactly the two bullet facts above. It is the honest minimal input, is stated in two lines, and matches the variable model (gpt-notes Prop 3.2) directly: `A i` determined by `vbl i`, `bset A S` determined by `⋃_{j∈S} vbl j`, disjoint index sets + `iIndepFun` ⟹ `IndepSet` (via `iIndepFun.measure_inter_preimage_eq_mul`, Basic.lean:654, plus a new glue lemma — see §4.2).
- The guard `i ∉ S` is **required for satisfiability**: without it, `S = {i}` would demand `IndepSet (A i) ((A i)ᶜ)`, which forces `μ (A i) ∈ {0,1}`. Since `G` is loopless, `i ∉ S → (∀ j ∈ S, ¬ G.Adj i j)` is exactly `S ⊆ ι \ (Γ(i) ∪ {i})` of Definition 3.1.

### 1.3 ENNReal vs ℝ, and the (P1)/(P2) induction

**Decision: internal induction in `ℝ≥0∞` (ENNReal), as proposed; ℝ (`μ.real`) kept as a documented fallback.** The route is coherent; verification of the induction step:

Induction proposition (`Finset.strongInductionOn` on `S`):

```
(P1)  ENNReal.ofReal (∏ j ∈ S, (1 - x j)) ≤ μ (bset A S)
(P2)  ∀ i, i ∉ S → μ (A i ∩ bset A S) ≤ ENNReal.ofReal (x i) * μ (bset A S)
```

- **Base `S = ∅`.** `bset A ∅ = Set.univ`; (P1) is `ofReal 1 = 1 ≤ μ univ = 1`. (P2): `μ (A i ∩ univ) = μ (A i) ≤ ofReal (x i · ∏_{Γ(i)} (1 - x j)) = ofReal (x i) · ofReal (∏_{Γ(i)} (1 - x j)) ≤ ofReal (x i) · 1 = ofReal (x i) · μ (bset A ∅)`, using `∏_{Γ(i)} (1 - x_j) ≤ 1` (pointwise `1 - x j ≤ 1` from `0 ≤ x j`, via `Finset.prod_le_one'` — verified, `Algebra/Order/BigOperators/Group/Finset.lean:128`) and `ofReal_prod_of_nonneg` (BigOperators.lean:64). No IH needed.
- **P1 step** (`S` nonempty, pick `r ∈ S`): `∏_{j∈S} (1-x_j) = (1-x_r)·∏_{j∈S.erase r} (1-x_j)`; by IH(P1) at `S.erase r` and P2-IH at `(r, S.erase r)` (available since `r ∉ S.erase r`):

  ```
  μ (bset A S) = μ (bset A (insert r (S.erase r)))                       -- S = insert r (S.erase r)
               = μ (bset A (S.erase r)) - μ (A r ∩ bset A (S.erase r))   -- peeling identity (ii)
               ≥ μ (bset A (S.erase r)) - ofReal (x r) · μ (bset A (S.erase r))   -- P2-IH + tsub_le_tsub_left
               = (1 - ofReal (x r)) · μ (bset A (S.erase r))              -- ENNReal.sub_mul
               = ofReal (1 - x r) · μ (bset A (S.erase r))                -- NEW ofReal_one_sub glue
               ≥ ofReal (1 - x r) · ofReal (∏_{S.erase r} (1 - x_j))      -- P1-IH + mul_le_mul_left'
               = ofReal (∏_{j∈S} (1 - x_j))                                -- ofReal_mul + prod_erase_mul
  ```

  All finiteness conditions are met because `μ` is a probability measure: `μ s ≤ μ univ = 1 < ⊤` (`measure_mono (Set.subset_univ _)` + `measure_univ`), so `μ s ≠ ⊤` (needed by `ENNReal.sub_mul`'s hypothesis `0 < b → b < a → c ≠ ∞` and by the `tsub` cancellation family `tsub_eq_of_eq_add`/`eq_tsub_of_add_eq`, Operations.lean:307–332).
- **P2 step** (`i ∉ S`). Split `N := S.filter (fun j => G.Adj i j)`, `M := S.filter (fun j => ¬ G.Adj i j)`. If `N = ∅`: `hdg` at `(i, S)` gives `IndepSet (A i) (bset A S)`, so `μ (A i ∩ bset A S) = μ (A i) · μ (bset A S) ≤ ofReal (x i) · 1 · μ (bset A S)` as in the base case. If `N ≠ ∅`:

  ```
  μ (A i ∩ bset A S) ≤ μ (A i ∩ bset A M)                              -- (iv), measure_mono
                     = μ (A i) · μ (bset A M)                          -- hdg at (i, M) + indepSet_iff_measure_inter_eq_mul
                     ≤ ofReal (x i) · ofReal (∏_{Γ(i)} (1-x_j)) · μ (bset A M)   -- (LLL) + mul_le_mul_right'
                     ≤ ofReal (x i) · ofReal (∏_{N} (1-x_j)) · μ (bset A M)      -- N ⊆ Γ(i): prod_le_prod_of_subset_of_le_one'
                     ≤ ofReal (x i) · μ (bset A (N ∪ M))               -- NEW product-chain bound (§2 step 8)
                     = ofReal (x i) · μ (bset A S)                      -- S = N ∪ M
  ```

  The **product-chain bound** `ofReal (∏_{j∈N} (1-x_j)) · μ (bset A M) ≤ μ (bset A (N ∪ M))` is proved by nested `Finset.induction` on `N`, peeling one `r ∈ N` at a time with the same one-step peeling as in the P1 step; each peel applies P2-IH at the set `M ∪ (N.erase r)` of size `|S| - 1 < |S|` (this replaces the gpt-notes chain rule (4), whose conditioning set excludes exactly `|M| + ℓ - r < k` events). Base `N = ∅`: `ofReal 1 · μ (bset A M) = μ (bset A M)`.
- **Final assembly (no chain rule, no order):** (P1) at `S = univ` gives `ofReal (∏ i, 1 - x i) ≤ μ (bset A univ)`, and `bset A univ = ⋂ i, (A i)ᶜ`. Positivity: each `1 - x i > 0` (`x i < 1`), so `∏ i (1 - x i) > 0` (`Finset.prod_pos`), hence `0 < ofReal (∏ i, 1 - x i)` (`ofReal_pos`), hence `0 < μ (⋂ i, (A i)ᶜ)`. **This is the whole replacement for gpt-notes §4.2.** Coherent. ✔

**Exact glue-lemma inventory consumed by the ENNReal route** (verified names; ✓ = exists in mathlib v4.32.0, NEW = to create):

| Lemma | Status | Notes |
|---|---|---|
| `Finset.strongInductionOn` | ✓ | `Data/Finset/Card.lean:852`, IH over `t ⊂ s` |
| `Finset.inf_set_eq_iInter`, `Finset.inf_eq_iInf`, `inf_insert` | ✓ | `Data/Finset/Lattice/Fold.lean:308-309`, `Lattice/Pi.lean:34` usage — `⋂ j ∈ S, (A j)ᶜ` over a `Finset` is `S.inf` |
| `Finset.measurableSet_biInter` | ✓ | `MeasureTheory/MeasurableSpace/Defs.lean:149` (shape TBC — may be over `(s : Set β)`; trivial adaptor otherwise) |
| `measure_union` (`Disjoint` + measurability) | ✓ | `MeasureSpace.lean:112` |
| `measure_mono`, `measure_univ` (`IsProbabilityMeasure`), `measure_ne_top` (`IsFiniteMeasure`) | ✓ | `Typeclasses/Probability.lean`, `MeasureSpace.lean` (used at `ConditionalProbability.lean:254`) |
| `indepSet_iff_measure_inter_eq_mul` | ✓ | `Probability/Independence/Basic.lean:579`, `[IsZeroOrProbabilityMeasure μ]` + both sets measurable |
| `ENNReal.ofReal_mul` (`0 ≤ p`), `ofReal_add`, `ofReal_le_ofReal`, `ofReal_mono`, `ofReal_pos`, `ofReal_le_one`, `ofReal_lt_one`, `ofReal_eq_one` | ✓ | `Data/ENNReal/Real.lean` |
| `ENNReal.ofReal_prod_of_nonneg` | ✓ | `Data/ENNReal/BigOperators.lean:64` |
| `ENNReal.sub_mul` | ✓ | `Operations.lean:408`, hypothesis `0 < b → b < a → c ≠ ∞` — discharge with `measure_ne_top` |
| `ENNReal.tsub_le_iff_right`, `tsub_le_tsub_left`, `le_sub_iff_add_le_right` (`c ≠ ∞`, `c ≤ b`), `tsub_eq_of_eq_add` / `eq_tsub_of_add_eq` family (`cancel_of_ne`) | ✓ | `Operations.lean:280,386–389,307–332,695` |
| `ENNReal.toReal_mul`, `toReal_ofReal`, `ofReal_toReal`, `ofReal_le_iff_le_toReal`, `toReal_sub_of_le` | ✓ | `Real.lean:339`, `Basic.lean:246/250`, `Real.lean:262`, `Operations.lean:433` — the ℝ fallback route (§5, risk 1) |
| `mul_le_mul_left'` / `mul_le_mul_right'` | ✓ | generic; ENNReal is `MulPosMono`/`PosMulMono` |
| `Finset.prod_le_prod_of_subset_of_le_one'` | ✓ | `Algebra/Order/BigOperators/Group/Finset.lean:141` — `s ⊆ t`, off-set factors ≤ 1 ⟹ `∏ t ≤ ∏ s`: exactly the `N ⊆ Γ(i)` step |
| `Finset.prod_erase_mul`, `Finset.prod_const`, `Finset.prod_pos` | ✓ | standard BigOperators (names TBC-trivial) |
| `ENNReal.ofReal_one_sub` (`0 ≤ x`, `x ≤ 1` ⟹ `ofReal (1 - x) = 1 - ofReal x`) | **NEW** | ~4 lines: `ofReal_add` + `tsub_eq_of_eq_add`; **absent** from mathlib (grep of `ofReal_sub`/`ofReal_one_sub`/`ofReal_tsub` found none) |

**ℝ fallback (documented, not planned):** run the same induction on `μ.real` (`= (μ s).toReal`, exists: `Typeclasses/Probability.lean`; simp lemmas `probReal_univ`, `probReal_add_probReal_compl`) — all subtraction/distributivity is plain field algebra (`linarith`, `ring_nf`), converted to the ENNReal statement at the end via `ofReal_le_iff_le_toReal` + `toReal_mul` + `toReal_ofReal`. Only if ENNReal tsub glue proves painful.

### 1.4 Lean statement skeleton

```lean
import Mathlib.Probability.Independence.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype ι] [DecidableEq ι]

/-- `bset A S`: none of the bad events indexed by `S` occurs. (Finset-inf form: `⋂ j ∈ S, (A j)ᶜ`.) -/
def bset (A : ι → Set Ω) (S : Finset ι) : Set Ω := ⋂ j ∈ S, (A j)ᶜ

/-- `G` is a dependency graph for the family of bad events `A`: each `A i` is independent of
"none of `A j` occurs" for every index set `S` of non-neighbors of `i` (not containing `i`).
This is the (weak) fragment of the classical Definition 3.1 that the proof actually uses. -/
def IsDependencyGraph (G : SimpleGraph ι) (A : ι → Set Ω) : Prop :=
  ∀ i (S : Finset ι), i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) → IndepSet (A i) (bset A S)

theorem lovaszLocalLemma {G : SimpleGraph ι} [DecidableRel G.Adj] {A : ι → Set Ω} (x : ι → ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hdg : IsDependencyGraph G A)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))) :
    ENNReal.ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ) := by
  -- (P1) at S = univ + bset_univ_eq_iInter

theorem lovaszLocalLemma_pos {G : SimpleGraph ι} [DecidableRel G.Adj] {A : ι → Set Ω} (x : ι → ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hdg : IsDependencyGraph G A)
    (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))) :
    0 < μ (⋂ i, (A i)ᶜ) := by
  exact lt_of_lt_of_le (by positivity) (lovaszLocalLemma ...)

/-- ℝ-valued corollary via `μ.real`. -/
theorem lovaszLocalLemma_probReal ... (same hypotheses) :
    ∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)
```

**Decisions baked into the skeleton (with rationale):**
- `x : ι → ℝ` with `hx₀ : 0 ≤ x i`, `hx₁ : x i < 1` — mirrors gpt-notes `α_i ∈ [0,1)`; keeps `linarith`/`field_simp` usable. (`ℝ≥0` would need `tsub` casts for `1 - x i`; `Ioo 0 1` erases the endpoints, which the proofs use explicitly.)
- `hLLL` bundles the product inside one `ofReal`: `ofReal (x i * ∏ …)`. Users can rewrite with `ofReal_mul` (`0 ≤ x i`) and `ofReal_prod_of_nonneg` when needed; the symmetric corollaries plug in without touching `ofReal` at all.
- `[DecidableRel G.Adj]` is a theorem hypothesis (needed for `neighborFinset`); applications must supply it (usually `Classical.decRel _`).
- Final public theorem: the **ENNReal form** above, plus `lovaszLocalLemma_pos` as the headline "existence" statement and the one-line `lovaszLocalLemma_probReal` ℝ corollary (`μ.real` is mathlib's probability-realization of `probReal`; `probReal_univ` etc. exist).

---

## 2. Proof decomposition

Notation: `B S := bset A S`; `Γ(i) := G.neighborFinset i`; `P1 S` / `P2 i S` as in §1.3.

| # | Step (gpt-notes anchor) | Lean declaration | Difficulty | Consumes (inventory) | Est. lines |
|---|---|---|---|---|---|
| 1 | §3 setup: `B_S` | `bset` (def) + `bset_empty`, `bset_insert`, `bset_subset_bset_of_subset`, `bset_union`, `bset_univ_eq_iInter` (NEW) | Easy | `Finset.inf_set_eq_iInter`, `inf_insert`, `Set.iInter` simp | 60 |
| 2 | measurability of `B_S` | `measurableSet_bset (hA : ∀ i, MeasurableSet (A i))` (NEW) | Easy | `Finset.measurableSet_biInter` or plain `Finset.induction` + `MeasurableSet.inter` | 15 |
| 3 | Def 3.1 (weak) | `IsDependencyGraph` (def, NEW) | Easy | `IndepSet` | 10 |
| 4 | `1 - ofReal x` glue | `ofReal_one_sub` (NEW) | Easy | `ofReal_add`, `ofReal_le_ofReal`, `tsub_eq_of_eq_add` (`cancel_of_ne`) | 8 |
| 5 | product monotonicity `N ⊆ Γ(i)` | (use `Finset.prod_le_prod_of_subset_of_le_one'` directly; optional NEW wrapper `prod_le_prod_of_subset_of_nonneg_le_one`) | Easy | `prod_le_prod_of_subset_of_le_one'` | 5–15 |
| 6 | peeling identity (ii): `μ (B (insert r T)) = μ (B T) - μ (A r ∩ B T)` | `measure_bset_insert` (NEW) | Easy–Medium | `measure_union`, `Disjoint`, `eq_tsub_of_add_eq`/`tsub_eq_of_eq_add`, `measure_mono`, `measure_ne_top` | 40 |
| 7 | one-step peeling bound: `ofReal (1 - x r) · μ (B T) ≤ μ (B (insert r T))` given P2 at `(r, T)` | `measure_bset_insert_le` (NEW) | **Medium** | step 6, `ofReal_one_sub`, `ENNReal.sub_mul`, `tsub_le_tsub_left`, `mul_le_mul_left'` | 50 |
| 8 | product-chain bound (replaces chain rule (4)): `ofReal (∏_{j∈N} (1-x_j)) · μ (B M) ≤ μ (B (N ∪ M))`, nested `Finset.induction` on `N` | `prob_bset_inter_prod` (NEW) | Medium | step 7 (per peel), P2-IH at `M ∪ N.erase r`, `ofReal_mul`, `prod_insert` | 70 |
| 9 | base cases `|S| = 0` (Lemma 4.2 base) | inline in step 10 | Easy | `bset_empty`, `ofReal_eq_one`, `ofReal_prod_of_nonneg`, `∏ (1-x) ≤ 1` | 30 |
| 10 | **simultaneous induction** `C S := P1 S ∧ ∀ i ∉ S, P2 i S` (Lemma 4.2) | `lll_prob_bset` (NEW) | **Hard** | `Finset.strongInductionOn`; P1 step: steps 7 + IH; P2 step: `hdg`, `indepSet_iff_measure_inter_eq_mul`, `hLLL`, `ofReal_mul`, steps 5, 8, `mul_le_mul_right'`, `measure_mono` + step 1(iv) | 250–350 |
| 11 | final product bound (Theorem 4.1, chain-rule-free) | `lovaszLocalLemma` (NEW) | Easy | step 10 (P1 at `univ`), `bset_univ_eq_iInter`, `Finset.inf_set_eq_iInter` | 25 |
| 12 | positivity `0 < μ (⋂ i, (A i)ᶜ)` | `lovaszLocalLemma_pos` (NEW) | Easy | `Finset.prod_pos`, `sub_pos` (`hx₁`), `ofReal_pos` | 10 |
| 13 | ℝ corollary | `lovaszLocalLemma_probReal` (NEW) | Easy | `toReal_mul`? — actually only `ofReal_le_iff_le_toReal` + `measure_ne_top` + `toReal_ofReal` | 15 |
| 14 | conditional form `μ[A i ‖ B S] ≤ ofReal (x i)` (Lemma 4.2 verbatim; optional) | `lovaszLocalLemma_cond` (NEW, optional) | Easy | `cond_mul_eq_inter` (`[IsFiniteMeasure μ]`), P2 + positivity of `μ (B S)` | 20 |

**Total estimate: ~600–750 lines** for the asymmetric LLL core (steps 1–13).

Step 10 internal structure (the only hard part): `by_cases` on `S = ∅`; P1: `rcases S.eq_empty_or_nonempty`, pick `r := S.max' …` or `Classical.choose S.nonempty`; P2: `by_cases` on `N = ∅` (`hdg` direct) vs `N ≠ ∅` (5-inequality chain of §1.3, ending with step 8 at `(N, M)` where `S = N ∪ M` follows from the `filter` partition `Finset.filter_union_filter_neg_eq` — TBC exact name, trivial).

---

## 3. New declarations list

1. `bset` (definition) — **Easy**
2. `bset_empty`, `bset_insert`, `bset_erase` — **Easy**
3. `bset_subset_bset_of_subset` (antitone) — **Easy**
4. `bset_union` (`Disjoint N M → bset A (N ∪ M) = bset A N ∩ bset A M`) — **Easy**
5. `bset_univ_eq_iInter` — **Easy**
6. `measurableSet_bset` — **Easy**
7. `IsDependencyGraph` (definition) — **Easy**
8. `ofReal_one_sub` — **Easy**
9. `measure_bset_insert` (peeling identity (ii)) — **Easy–Medium**
10. **`measure_bset_insert_le`** (one-step peeling bound) — **Medium**
11. **`prob_bset_inter_prod`** (chain-rule-free product lower bound) — **Medium**
12. **`lll_prob_bset`** (the (P1)+(P2) strong induction) — **Hard**
13. `lovaszLocalLemma` — **Easy** (assembly only)
14. `lovaszLocalLemma_pos` — **Easy**
15. `lovaszLocalLemma_probReal` — **Easy**
16. `lovaszLocalLemma_cond` (optional, conditional form) — **Easy**
17. `IsDependencyGraph_of_strong` / strong-vs-weak equivalence (deferred) — **Medium**

---

## 4. Symmetric LLL and beyond

### 4.1 Symmetric form (`ep(d+1) ≤ 1`) — follow-up PR, +200–300 lines

```
theorem lovaszLocalLemma_symmetric {G : SimpleGraph ι} [DecidableRel G.Adj] {A : ι → Set Ω}
    {p : ℝ} {d : ℕ} (hp : ∀ i, μ (A i) ≤ p) (hd : ∀ i, G.degree i ≤ d)
    (hcond : Real.exp 1 * p * (d + 1) ≤ 1) : 0 < μ (⋂ i, (A i)ᶜ)
```

Incremental needs on top of the asymmetric theorem:
- `d ≥ 1` case: apply `lovaszLocalLemma_pos` with `x i := 1 / (d + 1)`. Required chain for `hLLL`:
  `p ≤ 1 / (Real.exp 1 * (d+1))` (from `hcond` by `field_simp`, positivity `0 < d + 1`, `0 < Real.exp 1` — `Real.exp_pos`);
  `1 / (Real.exp 1 * (d+1)) ≤ 1/(d+1) · (d/(d+1))^d` ⟸ `1/e ≤ (d/(d+1))^d` ⟸ `(1 + 1/d)^d ≤ Real.exp 1`, via
  `Real.add_one_le_exp` (verified: `Analysis/SpecialFunctions/Exp.lean`, used at line 211), `pow_le_pow_left₀` (verified: `Algebra/Order/GroupWithZero/Basic.lean:470`) and `Real.exp_nat_mul` (`(Real.exp x)^n = Real.exp (n·x)`, verified usage Exp.lean:256), plus `d/(d+1) = 1/(1+1/d)` algebra (`field_simp`, `d ≠ 0`);
  `(d/(d+1))^{|Γ(i)|} ≥ (d/(d+1))^d` from `|Γ(i)| ≤ d` (`hd i`; `G.degree i = (G.neighborFinset i).card` is rfl) and `pow_le_pow_of_le_one` (verified: `Algebra/Order/GroupWithZero/Basic.lean:393`, needs `0 ≤ d/(d+1) ≤ 1`);
  `∏_{j∈Γ(i)} (1 - x j) = (d/(d+1))^{|Γ(i)|}` via `Finset.prod_const`.
- `d = 0` case: `hd` forces every `G.degree i = 0`, so `neighborFinset i = ∅` (`degree_eq_zero` + `neighborFinset_eq_empty` — verified, Finite.lean); apply the asymmetric LLL with `x i := p`, where `p < 1` follows from `Real.exp 1 * p * 1 ≤ 1` and `1 < Real.exp 1` (e.g. via `Real.exp_one_gt`-style lemma, TBC exact name; or `add_one_le_exp 0`). No separate mutual-independence argument is needed (the gpt-notes d=0 shortcut is absorbed by the asymmetric theorem).
- Difficulty: **Medium** (real-field algebra + exp lemma plumbing; no new induction).

Alternative sharper form `p ≤ d^d / (d+1)^(d+1)` (gpt-notes §5.1): drops the `e` step entirely; `p < 1` and the `hLLL` chain are direct. Easy–Medium. Worth including as the internal lemma; derive the `ep(d+1)` statement from it.

### 4.2 `4pd` criterion (gpt-notes Corollary 5.2) — follow-up, +100–150 lines

`x i := 1 / (2d)`, `d ≥ 1`. Needs only Bernoulli `one_add_mul_le_pow` (verified: `Algebra/Order/Ring/Pow.lean:100`, instantiate `a = -1/(2d)`, hypothesis `-2 ≤ -1/(2d)` — fine for `d ≥ 1`) to get `(1 - 1/(2d))^d ≥ 1/2`, then `1/(2d) · (1/2) = 1/(4d)`, and `hcond : 4 * p * d ≤ 1` ⟹ `p ≤ 1/(4d)` by `field_simp`. Difficulty: **Easy–Medium** (ring arithmetic; no exp).

### 4.3 Variable model (gpt-notes §3.1, Prop 3.2) — follow-up, +200–300 lines

The missing bridge is:

```
theorem isDependencyGraph_variableModel {𝓧 : Type*} [MeasurableSpace 𝓧] [Fintype n-as-ι']
    {X : ι → Ω → 𝓧} (hX : iIndepFun X μ) {vbl : ι → Finset ι'} ... :
    (∀ i j, i ≠ j → Disjoint (vbl i) (vbl j)) → IsDependencyGraph (overlapGraph vbl) A
```

- Infrastructure available: `iIndepFun`, `iIndepFun.comp`, `iIndepFun.measure_inter_preimage_eq_mul`, `indepFun_iff_indepSet_preimage` (Basic.lean:449,654,670,681) and StatsMLlib's `pi_eval_iIndepFun` / `pi_comp_eval_iIndepFun` (`StatsMLlib/Probability/Independence/FinsetPi.lean`, verified) for the `Measure.pi` case.
- The genuinely new glue is the **restriction lemma**: for finite disjoint `J, K ⊆ ι'`, the tuple maps `evalJ : Ω → (J → 𝓧)` and `evalK : Ω → (K → 𝓧)` are `IndepFun` for `Measure.pi μs`, i.e. a "disjoint index sets ⟹ independent projections" lemma. Not found in mathlib (TBC; `iIndepFun.indepFun` exists only for two distinct indices). Needs a small measure argument (`Measure.pi` over subtypes, cylinder sets) — **Medium**, ~80–120 lines.
- Then `IsDependencyGraph` follows by `IndepSet (A i) (bset A S)`: `A i = f i ⁻¹' …` measurable, `bset A S` measurable (step 2), `indepFun_iff_indepSet_preimage`-style transport. Easy once the restriction lemma exists.
- Scope: worth its own file `VariableModel.lean`; it is what makes k-SAT/hypergraph applications *instance-free*.

### 4.4 Applications — follow-up PRs (each after 4.3 or hand-rolled graphs)

- **k-SAT (gpt-notes Thm 6.1):** `Ω := Fin n → Bool`, product of uniform Bool measures (`Measure.pi (fun _ => uniformOfFintype?)` — TBC; or `Measure.count` normalized). Bad event `A C = {assignment | clause C violated}`, `μ (A C) = 2^(-k)` via the `Measure.pi` product formula (`Measure.pi_pi`, exists). Dependency graph = clause-variable overlap via 4.3. Conclude `Set.Nonempty (⋂ …)` from `0 < μ` (lemma: `0 < μ s → s.Nonempty` — e.g. `measure_pos_iff`-adjacent, TBC exact name; trivial glue). Cost ~300–400 lines beyond 4.3; difficulty **Medium** (mostly finite-type bookkeeping and `2^k` arithmetic).
- **Hypergraph coloring (gpt-notes Thm 7.1):** `Ω := V → Fin q`, uniform product; bad event `A e = {e monochromatic}`, `μ (A e) = q·q^{-k} = q^{1-k}`; dependency degree `d ≤ k(Δ-1)` counted via `Finset.filter`/`card` lemmas; needs `e·p·(d+1) ≤ 1` arithmetic with rationals. Cost ~400–500 lines beyond 4.3; difficulty **Medium** (uniform-measure probability of cylinders + degree counting). Recommend a first application only after the symmetric form + variable model land.

**PR split recommendation:** PR 1 = asymmetric LLL only (this survey, §1–3, ~600–750 lines). PR 2 = symmetric form + sharp variant + `4pd` (§4.1–4.2, +300–450). PR 3 = variable model (§4.3). PR 4+ = k-SAT, hypergraph coloring.

---

## 5. Risks & open questions

| # | Risk | Severity | Mitigation |
|---|---|---|---|
| 1 | **ENNReal tsub/distributivity ergonomics.** `ENNReal.sub_mul` has the awkward hypothesis `0 < b → b < a → c ≠ ∞`; the `tsub_eq_of_eq_add` family needs `cancel_of_ne`; each peeling step must thread finiteness proofs. | Medium–High | All finiteness is automatic: probability measure ⟹ `μ s ≤ μ univ = 1 < ⊤` via `measure_mono` + `measure_univ`, so `measure_ne_top` applies everywhere. Wrap once in a private lemma (`measure_bset_insert_le`) so the main induction sees clean statements. **Verified fallback:** rerun the whole induction on `μ.real` (ℝ) — `toReal_mul` (`@[simp]`), `toReal_ofReal`, `ofReal_le_iff_le_toReal`, `toReal_sub_of_le` all exist — and convert once at the end. |
| 2 | **`⋂ j ∈ S, f j` notation over `Finset`.** Elaborates to `Finset.inf` (needs the `Lattice` import); interplay with `Set.iInter` in `iIndepSet_iff_meas_biInter` and the final `⋂ i, (A i)ᶜ` can cause goal-shape mismatches. | Medium | Verified `Finset.inf_set_eq_iInter` bridges `S.inf f = ⋂ x ∈ S, f x`. Define `bset` with the Finset binder; add `bset_univ_eq_iInter` as a `@[simp]`-adjacent lemma; keep `Set.iInter` only in the final theorem statement. |
| 3 | **`neighborFinset` instances.** `G.neighborFinset i` needs `Fintype (G.neighborSet i)`; the automatic instance requires `[Fintype ι] [DecidableRel G.Adj]`, and `SimpleGraph` has no global `DecidableRel`. | Low–Medium | Put `[DecidableRel G.Adj]` among the theorem variables; applications instantiate with `Classical.decRel` or build a graph whose `Adj` is decidable by construction. Verified: instance is `inferInstance` (the old `neighborSetFintype` abbrev is deprecated since 2026-04-29). |
| 4 | **IndepSet vs iIndepSet / strong-form equivalence.** `indepSet_iff_measure_inter_eq_mul` needs both sets measurable + `[IsZeroOrProbabilityMeasure μ]`; the classical Definition 3.1 (independence from every Boolean combination) is not a one-liner from the weak form, and stating the theorem with the strong form would drag π-system/atoms lemmas (`IndepSets`, `iIndepSets.iIndep`) into the critical path. | Medium | State the theorem with the weak `IsDependencyGraph` (exactly what the proof consumes). Provide `IsDependencyGraph` ⟺ strong-form equivalence (deferred, ~100–150 lines) for users who want the classical definition. Applications (variable model) prove the weak form directly, which is what their proofs naturally yield. |
| 5 | **The combined induction `C S := P1 S ∧ ∀ i ∉ S, P2 i S`.** The P2 sub-proof consumes IH at two different smaller sets (`M` and `M ∪ N.erase r`) plus its own just-proved P1; Lean cannot do mutual recursion over `strongInductionOn` cleanly, so this must be one `And`. | Medium–High | Extract the two reusable ingredients as standalone lemmas parameterized by explicit P2-like hypotheses (`measure_bset_insert_le`, `prob_bset_inter_prod`); the induction body then only assembles them. The IH access pattern is uniform: `(ih (S.erase r) (erase_ssubset hr))` and `(ih (M ∪ N.erase r) …)` with `card` decreasing by exactly 1. |
| 6 | **`x i < 1` vs `x i ≤ 1` bookkeeping.** Product monotonicity and `ofReal_one_sub` need `x i ≤ 1` and `0 ≤ x i`; positivity needs `x i < 1`. | Low | Keep both hypotheses; derive `x i ≤ 1` with `le_of_lt` once in a `have` block. `1 - x j > 0` via `sub_pos.mpr (hx₁ j)`. |
| 7 | **Symmetric-form arithmetic.** `field_simp` on `p ≤ 1/(e(d+1))`, `1/(1+1/d)` rewrites, and the `d = 0` case split are fiddly; `Real.exp_one_gt`-style positivity lemmas need name-checking. | Medium | Multiply up rather than divide (`e·p·(d+1) ≤ 1` is already in multiplicative form); use the sharp `p ≤ d^d/(d+1)^(d+1)` internal lemma to bypass `e`; TBC-name the exp lemma before starting (§4.1). |
| 8 | **Variable-model restriction lemma.** "iIndepFun ⟹ independence of projections onto disjoint finite index sets" is not directly in mathlib (TBC) and needs `Measure.pi` subtype/cylinder reasoning. | Medium (application-layer) | Defer to PR 3; if painful, hand-roll the dependency graph per application (k-SAT: clauses share a variable ⟹ non-sharing clauses' bad events are independent — provable per application with `pi_comp_eval_iIndepFun` + Finset induction, at ~+100 lines per application). |

**Open questions for the proposal's "API questions" section:**
1. File layout: new folder `StatsMLlib/Probability/LocalLemma/` with `Basic.lean` (asymmetric), `Symmetric.lean`, `VariableModel.lean`, `Applications/KSAT.lean`, `Applications/Hypergraph.lean` — or flatten into `Probability/LovaszLocalLemma.lean`? (Repo convention seems thematic folders.)
2. `x : ι → ℝ` with `hx₀`/`hx₁` (recommended) vs `x : ι → Ioo (0 : ℝ) 1` vs `x : ι → ℝ≥0` with `< 1`.
3. Should `hLLL` take the bundled form `μ (A i) ≤ ofReal (x i * ∏ …)` (recommended) or the split form `μ (A i) ≤ ofReal (x i) * ofReal (∏ …)`? (They differ by one `ofReal_mul` application.)
4. Should `lovaszLocalLemma_pos` (existence form) be the primary public theorem, with the product bound as a secondary `le` statement? (Recommended: both, as above.)
5. Should the conditional-probability form of Lemma 4.2 (`μ[A i ‖ bset A S] ≤ ofReal (x i)`) be included for math-text fidelity? (Cheap — step 14 — but adds `[IsFiniteMeasure μ]` noise.)
6. Is the weak `IsDependencyGraph` acceptable as the *public* dependency-graph definition, or must the strong form be the definition with the weak form as a derived lemma? (Recommend weak-first; strong equivalence as follow-up.)
