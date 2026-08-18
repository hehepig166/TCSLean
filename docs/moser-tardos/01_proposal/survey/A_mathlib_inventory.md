# Survey A — Mathlib API Inventory & Gap Check for the Moser–Tardos Algorithmic LLL

Survey agent A report. All mathlib paths are relative to `StatsMLlib/.lake/packages/mathlib/`
(mathlib v4.32.0) or to `StatsMLlib/` (the library root). Every lemma name below was verified
against the mathlib sources on disk (grep + Read) **or by an actual `lake env lean` compile test**;
nothing is from memory. The two riskiest claims — (i) independence of functions of disjoint
coordinate sets under a product measure, (ii) finiteness of bounded-size witness trees — were
compile-tested in scratch files under `/tmp` (full transcripts in §3). Repo code was not modified.

Reference for the proof being inventoried: `doc/moser-tardos/01_proposal/ref/moser_tardos_algorithmic_lll_notes.md`
(§1 variable framework, §7 resampling table, §8–§12 witness trees, §14 coupling, §16–§17
Galton–Watson) and the orchestrator's architecture seed in `survey/PLAN.md` §3 (finite-truncation
formulation: table `Ω_N := Π (j : κ), Fin N → Ω j`, measure
`Measure.pi (fun p : (j : κ) × Fin N => μ p.1)`, expectations via `lintegral`).

---

## 1. Scope & method

Scope: verify every Lean dependency the PLAN §3 architecture names, answer the four design
questions (countable products, "determined by `vbl`", tree representation, disjoint-coordinate
independence), and flag every missing lemma with a Lean-level statement. Method:

1. **Source greps** over `StatsMLlib/.lake/packages/mathlib/Mathlib/` for names + `file:line`.
2. **Compile tests** via
   `cd /Users/zhuzekai/workspace/StatsLean/StatsMLlib && lake env lean /tmp/mt_*.lean`
   (two files: `mt_indep_test.lean`, 106 lines; `mt_tree_test.lean`, 135 lines — both compile
   with **0 errors**).
3. **Absence checks** by grep over the whole mathlib tree.

Notation below: ✅ exists (verified), 🟡 exists but needs a thin glue lemma, ❌ must create.

---

## 2. Verified existing infrastructure

### 2.1 Product measures — finite, countable, and arbitrary-index

#### 2.1.1 `Measure.pi` (finite index type) — ✅

`Mathlib/MeasureTheory/Constructions/Pi.lean`:

| Name | Line | Content |
|---|---|---|
| `Measure.pi` | :210 | `protected irreducible_def pi : Measure (∀ i, α i)` — in a section with `variable [Fintype ι]`, `[∀ i, MeasurableSpace (α i)]`, `(μ : ∀ i, Measure (α i))`. **No `DecidableEq ι`, no `SigmaFinite` needed for the definition itself.** |
| `pi_pi` | :290 | `[∀ i, SigmaFinite (μ i)] (s : (i : ι) → Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)` |
| `pi_univ` | :295 | `[∀ i, SigmaFinite (μ i)] : Measure.pi μ univ = ∏ i, μ i univ` |
| `pi.instIsFiniteMeasure` | :302 | `[∀ i, IsFiniteMeasure (μ i)] : IsFiniteMeasure (Measure.pi μ)` |
| `pi.instIsProbabilityMeasure` | :312 | `[∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (Measure.pi μ)` |
| `pi_pi_finset` | :315 | `[∀ i, IsProbabilityMeasure (μ i)] (f : (i : ι) → Set (α i)) (s : Finset ι) : Measure.pi μ ((s : Set ι).pi f) = ∏ i ∈ s, μ i (f i)` |
| `pi_map_eval` | :376 | `[DecidableEq ι] (i : ι) : (Measure.pi μ).map (Function.eval i) = μ i` (mathlib's own coordinate-marginal; StatsMLlib re-derives it at `FinsetPi.lean:28`) |
| `Measure.tprod` | :~133 | product measure over a `List δ` of indices (`tprod_cons` :146) |
| `Measure.pi'` | :177 | `[Encodable ι] : Measure (∀ i, α i)` — **countable** product via `tprod` over `sortedUniv ι`; docstring says to prefer `Measure.pi` |

The PLAN's table syntax compiles exactly as written: `(j : κ) × Fin N` is a Sigma type
(`Σ j : κ, Fin N`), which is automatically `Fintype` when `κ` is, and
`Measure.pi (fun p : (_ : κ) × Fin N => μv p.1)` elaborates and gets the probability instance —
compile-tested, test (5) in §3.1. (Cosmetic note: the binder `j` in `(j : κ) × Fin N` triggers an
unused-variable warning; write `(_ : κ) × Fin N`.)

#### 2.1.2 Infinite / countable / arbitrary-index product measures — ✅ **THIS IS THE DECISIVE ANSWER**

**mathlib v4.32.0 DOES contain infinite product measures**, and they do **not** require Polish or
standard-Borel hypotheses. The main API is `Mathlib/Probability/ProductMeasure.lean` (added by
Etienne Marion, 2025):

| Name | Line | Content |
|---|---|---|
| `Measure.infinitePi` | :356 | `(μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] : Measure (Π i, X i)` — **for an arbitrary index type `ι`** (not just countable!), the unique probability measure with `ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)` for all finsets `s` and measurable `t`. Defined via an `if` on the probability hypothesis so it is usable without the proof. |
| `eq_infinitePi` | :386 | uniqueness: any measure agreeing with products of measurable boxes is `infinitePi μ` |
| `infinitePi_pi` | :403 | `infinitePi μ (Set.pi s t) = ∏ i ∈ s, μ i (t i)` |
| `infinitePi_pi_of_countable` | :423 | same for a countable index set `s : Set ι` |
| `infinitePi_pi_univ` | :450 | `[Countable ι] : infinitePi μ (Set.pi univ t) = ∏ i, μ i (t i)` |
| `isProjectiveLimit_infinitePi` | :364 | `infinitePi` is the projective limit of the partial products `Measure.pi (fun i : I ↦ μ i)` |
| `infinitePi_map_restrict` | :375 | `(infinitePi μ).map I.restrict = Measure.pi (fun i : I ↦ μ i)` — **this is the identity that evaluates cylinders** |
| `infinitePi_map_restrict'` | :414 | Set-indexed variant |
| `infinitePi_map_eval` | :479 | coordinate marginal |
| `measurePreserving_eval_infinitePi` | :468 | coordinate projection is measure-preserving |
| `infinitePi_map_pi` | :483 | pushforward by coordinatewise maps |
| `infinitePi_eq_pi` | :510 | `[Fintype ι] : infinitePi μ = Measure.pi μ` — **the finite and infinite theories agree** |
| `piContent` | :77 | the cylinder content (`AddContent`); `piContent_cylinder` :80, `piContent_eq_measure_pi [Fintype ι]` :84 |
| `piContent_tendsto_zero` | :265 | the key σ-additivity lemma (decreasing cylinders with empty intersection have content → 0) — the Kolmogorov-extension substitute |

Implementation: Ionescu–Tulcea for the `ℕ`-indexed case
(`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` — `traj` :518, `traj_eq_prod` :583,
`trajMeasure` :762), then Carathéodory extension of `piContent` to arbitrary index types.

**Assessment for the proposal.** An infinite-table a.s. formulation
(`Measure.infinitePi (fun p : (_ : κ) × ℕ => μ p.1)` on `Π (j : κ), ℕ → Ω j`) is *feasible* in
mathlib v4.32.0, with no extra hypotheses. However (see §5.1) the finite-truncation formulation
remains the recommendation; the infinite API still earns its keep inside the finite proof: the
identity `(Measure.pi μ) (cylinder I S) = Measure.pi (fun a : I ↦ μ a) S` — needed to turn the
τ-check probability into `∏ Pr(A[u])` — is proved in 3 lines via `infinitePi_eq_pi` +
`infinitePi_map_restrict` (compile test (4)); I found no direct finite-`Measure.pi` lemma for it.

### 2.2 Independence API — `Mathlib/Probability/Independence/Basic.lean` — ✅

Core predicates (all verified at these lines): `iIndepSets` :96, `IndepSets` :102, `iIndep` :111,
`Indep` :118, `iIndepSet` :124, `IndepSet` :129, `iIndepFun` :136, `IndepFun` :144
(notation `f ⟂ᵢ[μ] g`).

The lemmas that form the **disjoint-coordinate independence engine** (all compile-tested, §3.1):

| Name | Line | Content |
|---|---|---|
| `iIndepFun_pi` | :893 | `{μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)] {X : (i : ι) → Ω i → 𝓧 i} (mX : ∀ i, AEMeasurable (X i) (μ i)) : iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)` — **general (non-iid) coordinate independence**; with `X = id` this is `iIndepFun (fun a ω => ω a) (Measure.pi μ)`. (StatsMLlib's `pi_eval_iIndepFun`, `FinsetPi.lean:48`, only covers the iid case `fun _ ↦ μ`.) |
| `iIndepFun.indepFun_finset₀` | :803 | `(S T : Finset ι) (hST : Disjoint S T) (hf : iIndepFun f μ) (hf_meas : ∀ i, AEMeasurable (f i) μ) : IndepFun (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) μ` — disjoint index sets ⇒ the two tuples are independent |
| `iIndepFun.comp` | :670 | push independence through measurable maps (coordinatewise) |
| `IndepFun.comp` | :756 | `(hfg : IndepFun f g μ) (hf' : Measurable f') (hg' : Measurable g') : IndepFun (f' ∘ f) (g' ∘ g) μ` |
| `IndepFun_iff_Indep` | :269 | `IndepFun f g μ ↔ Indep (mβ.comap f) (mγ.comap g) μ` |
| `Indep.indepSet_of_measurableSet` | :595 | `Indep m₁ m₂ μ → MeasurableSet[m₁] s → MeasurableSet[m₂] t → IndepSet s t μ` |
| `IndepSet.measure_inter_eq_mul` | :584 | `(h : IndepSet s t μ) : μ (s ∩ t) = μ s * μ t` (no measurability hypothesis) |
| `indep_iSup_of_disjoint` | :511 | σ-algebra level: `iIndep m μ → (∀ i, m i ≤ mΩ) → Disjoint S T → Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ` (for the overlap-graph-is-a-dependency-graph proof) |
| `iIndepFun_iff_map_fun_eq_pi_map` | :864 | characterization of `iIndepFun` by pushforward = `Measure.pi` |
| `iIndepFun_iff_finset` / `iIndepFun.restrict` | :837 | restricting a family to a finset preserves independence |

**Verdict for the τ-check:** everything needed is present and compile-tested; the glue is ~8
lines per claim (see §3.1, tests (2)–(3)). No new mathlib content is required.

### 2.3 Expectation infrastructure (`lintegral`) — ✅

`Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean` (and `Add.lean`):

| Name | Line | Content |
|---|---|---|
| `lintegral_const` | Basic.lean:110 | `(c : ℝ≥0∞) : ∫⁻ _, c ∂μ = c * μ univ` |
| `lintegral_indicator` | Basic.lean:496 | `(hs : MeasurableSet s) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ` |
| `lintegral_indicator₀` | Basic.lean:508 | null-measurable variant |
| `lintegral_indicator_const` | Basic.lean:527 | `(hs : MeasurableSet s) (c : ℝ≥0∞) : ∫⁻ a, s.indicator (fun _ ↦ c) a ∂μ = c * μ s` — the counting-function workhorse |
| `lintegral_indicator_one` | Basic.lean:558 | `(hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s` (₀-variant :553) |
| `lintegral_iUnion` | Basic.lean:583 | `[Countable β] (hm : ∀ i, MeasurableSet (s i)) : ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ` |
| `lintegral_add_right'` | Add.lean:329 | `(hg : AEMeasurable g μ) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ` |
| **`lintegral_finsetSum'`** | Add.lean:341 | `(s : Finset β) (hf : ∀ b ∈ s, AEMeasurable (f b) μ) : ∫⁻ a, ∑ b ∈ s, f b a ∂μ = ∑ b ∈ s, ∫⁻ a, f b a ∂μ` — **renamed** (2026-04-08); the old names `lintegral_finset_sum'` :352, `lintegral_finsetSum` :354, `lintegral_finset_sum` :358 exist only as `@[deprecated]` aliases. **Do not use `lintegral_finset_sum` in new code.** |
| `lintegral_tsum` | Add.lean:360 | `[Countable β] (hf : ∀ i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ` |

**ℝ-valued probability:** `Measure.real` — `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:101`
— `protected def Measure.real (μ : Measure α) (s : Set α) : ℝ := (μ s).toReal`; the old
`ProbabilityTheory.probReal` function **does not exist** in v4.32.0 (confirmed again; same finding
as the LLL survey).

**Measurability of ι-valued counting functions** (`Λ t : Ω_N → ι`): mathlib's
`measurable_of_countable` / `measurable_of_finite`
(`Mathlib/MeasureTheory/MeasurableSpace/Basic.lean:287/:291`) cover the *domain*-countable
direction (any function **from** a finite/countable space with singleton-measurable class is
measurable), **not** the codomain-countable direction we need. No "fiber" characterization
(`Measurable f ↔ ∀ i, MeasurableSet (f ⁻¹' {i})` for countable codomain) was found. Practical
route (recommended): put the discrete `MeasurableSpace` on `ι` and prove measurability of `Λ t`
structurally by induction over the algorithm definition (each step is an `if` over a measurable
condition composed with measurable maps), or state the needed facts directly about the sets
`{ω | Λ t ω = i}`. Either way this is routine; flag it as a small gap item (§4.3).

### 2.4 Cylinders and the `comap` formulation — ✅

`Mathlib/MeasureTheory/Constructions/Cylinders.lean`:

| Name | Line | Content |
|---|---|---|
| `cylinder` | :159 | `def cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) : Set (∀ i, α i) := s.restrict ⁻¹' S` — **the cylinder is literally the preimage of the restriction map**, so the comap formulation (a) and the cylinder-predicate formulation (b) of "determined by `vbl`" are the same object. |
| `mem_cylinder` | :163 | `f ∈ cylinder s S ↔ s.restrict f ∈ S` |
| `MeasurableSet.cylinder` | :253 | `(s : Finset ι) (hS : MeasurableSet S) : MeasurableSet (cylinder s S)` |
| `inter_cylinder` | :192 | `cylinder s₁ S₁ ∩ cylinder s₂ S₂ = cylinder (s₁ ∪ s₂) (restrict₂ S₁ ∩ restrict₂ S₂)` (needs `s₁ ⊆ s₁∪s₂` etc.; for disjoint finsets this is the τ-check intersection identity) |
| `union_cylinder` :202, `compl_cylinder` :212, `eq_of_cylinder_eq_of_subset` :222 | | cylinder algebra |

Supporting maps/lemmas: `Finset.restrict (s : Finset ι) (f : (i : ι) → π i) : (i : s) → π i`
(`Mathlib/Data/Finset/Pi.lean:161`, used as `s.restrict f`); `Finset.measurable_restrict (s) :
Measurable (s.restrict (π := X))` (`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:657`);
`MeasurableSpace.measurableSet_comap {m} {f} : MeasurableSet[m.comap f] s ↔ ∃ t, MeasurableSet[m] t ∧ f ⁻¹' t = s`
(`MeasurableSpace/Basic.lean:90`); `comap_iSup` :134, `comap_generateFrom` :168,
`measurable_iff_comap_le` :187; `MeasurableSpace.pi = ⨆ a, (m a).comap (fun b => b a)`
(`MeasurableSpace/Constructions.lean:566–567`).

### 2.5 Tree data structures — 🟡 (nothing off-the-shelf; custom type recommended)

- `Mathlib/Data/Tree/Basic.lean` contains only **`BinaryTree`** (:33; `numNodes` :110,
  `height` :130, `numLeaves` :120) — binary, unlabeled-at-the-structure-level, no List children.
  Not suitable for witness trees.
- `SimpleGraph.IsTree` (`Mathlib/Combinatorics/SimpleGraph/Acyclic.lean:60`, `IsAcyclic` :56) is a
  **Prop** over a given graph with walks — no data, no root/labels built in. Using it would mean
  maintaining a vertex set, an ordering, and the adjacency separately — far more friction than the
  proof needs.
- No `Fintype (List α)` and **no `Fintype (Multiset α)`** instance exists anywhere in mathlib
  (verified by grep); only `fintypeNodupList : Fintype {l : List α // l.Nodup}`
  (`Mathlib/Data/Fintype/List.lean:58`). This constrains the finiteness proof (§2.6).

**Recommendation: custom inductive** — compile-tested in §3.2:

```lean
inductive WT (ι : Type*) where
  | node (label : ι) (children : List (WT ι))
```

with accessors `labelOf`/`childrenOf`, `size`/`height` by well-founded recursion, and
`IsProper (t) := (t.childrenOf.map labelOf).Nodup`. Rationale in §5.3. Two Lean-specific
gotchas discovered during testing (both in §3.2): (i) `node` is a Lean parser keyword — pattern
matching on it only resolves **inside a namespace**; (ii) inductive constructors do **not**
generate field projections (`c.label` is invalid) — accessor defs are required.

### 2.6 Finiteness of bounded trees — ✅ (mechanism compile-tested)

The Fintype ingredients (all with exact lines):

| Name | Location | Content |
|---|---|---|
| `Fintype.ofInjective` | `Mathlib/Data/Fintype/OfMap.lean:67` | `noncomputable def ofInjective [Fintype β] (f : α → β) (H : Function.Injective f) : Fintype α` — the cleanest way to get Fintype for a bounded-tree subtype |
| `Fintype.subtype` | `Mathlib/Data/Fintype/Basic.lean` | `[Fintype α] [DecidablePred p] : Fintype {a // p a}` (needs `classical`) |
| `Option.fintype` | `Mathlib/Data/Fintype/Option.lean:29` | `[Fintype α] : Fintype (Option α)` |
| `Pi.instFintype` | `Mathlib/Data/Fintype/Pi.lean:134` | `[DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] : Fintype (∀ a, β a)` |
| `Prod.fintype` | `Mathlib/Data/Fintype/Prod.lean` | product of fintypes |
| `List.sizeOf_lt_of_mem` | Lean core `Init/Data/List/BasicAux.lean:295` | `(h : a ∈ as) : sizeOf a < sizeOf as` — needed for termination of `size`/`height` |
| `List.ext_getElem?'` | `Mathlib/Data/List/Basic.lean:623` | `(∀ n < max l₁.length l₂.length, l₁[n]? = l₂[n]?) → l₁ = l₂` |
| `List.getElem?_eq_getElem` | List API (used at Basic.lean:654; core) | `(h : i < l.length) : l[i]? = some (l[i]'h)` |
| `List.attach_map_subtype_val` | core `Init/Data/List/Attach.lean` | `l.attach.map Subtype.val = l` |
| `List.length_le_sum_of_one_le` | `Mathlib/Algebra/BigOperators/Group/List/Basic.lean:518` | `(L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum` |

**Compile-tested result** (transcript §3.2): for `WT ι` with List children,
`noncomputable def fintypeSizeLE : ∀ N : ℕ, Fintype {t : WT ι // t.size ≤ N}` is provable by
induction on `N` via `Fintype.ofInjective` into `ι × (Fin n → Option T)` (children padded with
`none`; `T = {t // t.size ≤ n}`). ~65 lines including the support lemmas
(`size_le_sum_of_mem`, `length_le_sizeSum`, the padded-list injectivity argument). The
height-bounded variant `Fintype {t // t.height ≤ h}` uses the same mechanism (children of height
≤ h have height ≤ h−1) and was not separately tested.

⚠️ **Import-granularity trap discovered during testing:** `Fintype` instances for
`Option`/function types/`Prod` live in `Mathlib.Data.Fintype.{Option,Pi,Prod}.lean` and are NOT
imported by `Mathlib.Data.Fintype.Basic`. With missing imports, `Fintype (ι × (Fin n → Option T))`
fails to synthesize with a misleading message. The compile tests import all five files explicitly.

### 2.7 Real / ENNReal toolbox — ✅ (with one correction to the LLL survey)

| Name | Location | Content |
|---|---|---|
| `Real.one_add_inv_pow_le_exp` | `Mathlib/Analysis/Complex/Exponential.lean:653` | `{n : ℕ} : (1 + (n : ℝ)⁻¹) ^ n ≤ exp 1` — exactly the symmetric-form inequality `(1+1/d)^d ≤ e` |
| `one_add_mul_le_pow` | `Mathlib/Algebra/Order/Ring/Pow.lean:100` | `(H : -2 ≤ a) (n) : 1 + n * a ≤ (1 + a) ^ n` — Bernoulli |
| `Finset.prod_le_prod_of_subset_of_le_one'` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:141` | `(h : s ⊆ t) (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i` |
| `ENNReal.ofReal_mul` | `Mathlib/Data/ENNReal/Real.lean:297` | `(hp : 0 ≤ p) : ofReal (p * q) = ofReal p * ofReal q` (`ofReal_mul'` :301) |
| `ENNReal.ofReal_sub` | `Mathlib/Data/ENNReal/Operations.lean:436` | `(hq : 0 ≤ q) : ofReal (p - q) = ofReal p - ofReal q` |
| `ENNReal.ofReal_div_of_pos` | `Mathlib/Data/ENNReal/Inv.lean:952` | `{x y : ℝ} (hy : 0 < y) : ofReal (x / y) = ofReal x / ofReal y` — **the** lemma for `ofReal (x i / (1 - x i))` (with `x i < 1` we have `0 < 1 - x i`) |
| `ENNReal.ofReal_div_le` | `Inv.lean:946` | `(hy : 0 ≤ y) : ofReal (x / y) ≤ ofReal x / ofReal y` — inequality variant |
| `ENNReal.ofReal_inv_le` / `ofReal_inv_of_pos` | `Inv.lean:940/:~944` | inversion variants |
| `ENNReal.ofReal_prod_of_nonneg` | `Mathlib/Data/ENNReal/BigOperators.lean:64` | `(hf : ∀ i ∈ s, 0 ≤ f i) : ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ofReal (f i)` |
| `ENNReal.div_le_div_right` | `Inv.lean:468` | `(h : a ≤ b) (c) : a / c ≤ b / c` |
| `ENNReal.le_div_iff_mul_le` | `Inv.lean:363` | `(h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : a ≤ c / b ↔ a * b ≤ c` |

**Correction to the LLL survey's guess:** there is **no** unconditional `ENNReal.ofReal_div`. The
equality needs `0 < y` (`ofReal_div_of_pos`) and the general case is only `≤` (`ofReal_div_le`).
For the MT bound `x i / (1 - x i)` with `x i ∈ [0,1)` this is harmless (the denominator is
strictly positive), but the `x i = 0` trivial case must be split off anyway (PLAN §3 already does).

### 2.8 Deterministic pick rule — ✅

`Finset.min' (s : Finset α) (H : s.Nonempty) : α` — `Mathlib/Data/Finset/Max.lean:180`
(requires `[LinearOrder α]`); `min'_mem` :191, `min'_le` :194, `le_min'_iff` :204,
`min'_eq_min` etc. The least-violated-event pick rule
`(Finset.univ.filter (fun i => σ ∈ A i)).min' h` compiles (test (6) in §3.1) with
`classical` supplying `DecidablePred` for membership. No dedicated "least element of a Set under a
linear order" API is needed — the Finset filter + `min'` idiom suffices.

### 2.9 StatsMLlib local infrastructure

- `StatsMLlib/Probability/Independence/FinsetPi.lean` (103 lines) — current content re-read:
  `pi_map_eval` :28 (coordinate marginal), `pi_eval_iIndepFun` :48 (**iid case only**:
  `iIndepFun Function.eval (Measure.pi fun _ ↦ μ)`), `pi_comp_eval_iIndepFun` :101. The general
  non-iid version now lives in mathlib as `iIndepFun_pi` (Independence/Basic.lean:893), which is
  what the MT proof should use; `FinsetPi.lean` needs no changes for MT.
- `grep -rin "MoserTardos\|moser_tardos\|moser-tardos" StatsMLlib/` — no hits; nothing MT-related
  exists locally. `Probability/LovaszLocal.lean` is the classical LLL (its API inventory is agent
  D's job; per the LLL survey it has no dependency-graph abstraction reusable for MT).

### 2.10 Absence check: Moser–Tardos / LLL in mathlib v4.32.0 — ✅ (absent)

- `grep -rin "mosertardos\|moser-tardos\|moser_tardos" Mathlib/` — **0 hits**.
- `grep -rin "lovasz\|lovász" Mathlib/` — 3 hits, all in
  `Mathlib/Combinatorics/SetFamily/KruskalKatona.lean` (the unrelated "Lovász formulation of
  Kruskal–Katona"). No `LocalLemma`, no dependency-graph API.
- In-flight mathlib PRs: a Dec-2023 Zulip thread discussed contributing an LLL formalization to
  mathlib4 (never merged); no Moser–Tardos PR is visible.
  (Source: leanprover Zulip archive topic "Lovasz Local Lemma - mathlib4 Contribution",
  https://leanprover-community.github.io/archive/stream/113488-general/topic/Lovasz.20Local.20Lemma.20-.20mathlib4.20Contribution.html)

**Verdict: nothing MT/LLL exists in mathlib; everything is ours to build.**

---

## 3. Compile tests (the two riskiest claims)

Both files were run with
`cd /Users/zhuzekai/workspace/StatsLean/StatsMLlib && lake env lean <file>` — final state:
**0 errors** in both. (No repo files touched; scratch only in `/tmp`.)

### 3.1 Test 1 — disjoint-coordinate independence (`/tmp/mt_indep_test.lean`, 106 lines)

Imports: `Mathlib.Probability.Independence.Basic`, `Mathlib.MeasureTheory.Constructions.Pi`,
`Mathlib.MeasureTheory.Constructions.Cylinders`, `Mathlib.Probability.ProductMeasure`.
Context: `{α} [Fintype α] {Ω : α → Type*} [∀ a, MeasurableSpace (Ω a)]`
`(μ : (a : α) → Measure (Ω a)) [∀ a, IsProbabilityMeasure (μ a)]`.

**(1) Coordinates of a general product measure are independent** (4 lines):

```lean
example : iIndepFun (fun a (ω : Π a, Ω a) => ω a) (Measure.pi μ) := by
  exact iIndepFun_pi (μ := μ) (X := fun a => (id : Ω a → Ω a))
    (mX := fun a => aemeasurable_id)
```

**(2) Functions of disjoint coordinate sets are independent** (10 lines): for `S T : Finset α`,
`hST : Disjoint S T`, measurable `f : (Π a : S, Ω a) → β`, `g : (Π a : T, Ω a) → γ`:

```lean
example : IndepFun (f ∘ S.restrict) (g ∘ T.restrict) (Measure.pi μ) := by
  have hcoord : iIndepFun (fun a (ω : Π a, Ω a) => ω a) (Measure.pi μ) :=
    iIndepFun_pi (μ := μ) (X := fun a => (id : Ω a → Ω a)) (mX := fun a => aemeasurable_id)
  have htuples : IndepFun (S.restrict : (Π a, Ω a) → Π a : S, Ω a)
      (T.restrict : (Π a, Ω a) → Π a : T, Ω a) (Measure.pi μ) :=
    hcoord.indepFun_finset₀ S T hST (fun a => (measurable_pi_apply a).aemeasurable)
  exact htuples.comp hf hg
```

**(3) Cylinder events over disjoint coordinate sets are independent, with the measure-product
identity** (18 lines): `IndepSet (cylinder S C) (cylinder T D) (Measure.pi μ)` via
`IndepFun_iff_Indep` + `MeasurableSpace.measurableSet_comap` + `Indep.indepSet_of_measurableSet`,
and then `(Measure.pi μ) (cylinder S C ∩ cylinder T D) = (Measure.pi μ) (cylinder S C) *
(Measure.pi μ) (cylinder T D)` via `IndepSet.measure_inter_eq_mul`.

**(4) The τ-check cylinder identity** (8 lines) — this is what turns
`Pr[τ-check passes]` into `∏ Pr(A[u])` in the coupling lemma:

```lean
example {I : Finset α} {S : Set (Π a : I, Ω a)} (hS : MeasurableSet S) :
    (Measure.pi μ) (cylinder I S) = Measure.pi (fun a : I ↦ μ a) S := by
  calc
    (Measure.pi μ) (cylinder I S) = (Measure.infinitePi μ) (cylinder I S) := by
      rw [Measure.infinitePi_eq_pi]
    _ = (Measure.pi (fun a : I ↦ μ a)) S := by
      rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict I) hS,
        Measure.infinitePi_map_restrict]
```

(Note the amusing route: the *infinite* product API proves the finite cylinder identity, because
`Measure.pi` lacks a direct `map_restrict` lemma.)

**(5) The truncated resampling table is a probability measure** (2 lines) — the PLAN's exact
syntax:

```lean
variable {κ : Type*} [Fintype κ] {Ωv : κ → Type*} [∀ j, MeasurableSpace (Ωv j)]
variable (μv : (j : κ) → Measure (Ωv j)) [∀ j, IsProbabilityMeasure (μv j)]
variable (N : ℕ)

example : IsProbabilityMeasure (Measure.pi (fun p : (_ : κ) × Fin N => μv p.1)) := by
  infer_instance
```

**(6) Deterministic pick rule** (9 lines): least violated event under `[LinearOrder ι]`:

```lean
noncomputable example {ι : Type*} [Fintype ι] [LinearOrder ι] {A : ι → Set (Π j : κ, Ωv j)}
    {σ : Π j : κ, Ωv j} (h : ∃ i, σ ∈ A i) : ι := by
  classical
  exact (Finset.univ.filter (fun i => σ ∈ A i)).min' (by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rcases h with ⟨i, hi⟩
    have : i ∈ Finset.univ.filter (fun j => σ ∈ A j) := by simp [hi]
    exact Finset.ne_empty_of_mem this he)
```

**Conclusion: the independence engine of the τ-check is fully present in mathlib v4.32.0 and
packages into ~10-line lemmas.** No missing mathlib content on the critical path.

### 3.2 Test 2 — witness trees + finiteness (`/tmp/mt_tree_test.lean`, 135 lines)

Imports: `Mathlib.Data.Fintype.{Basic,List,Pi,Option,Prod}`, `Mathlib.Data.Finset.Max`,
`Mathlib.Algebra.BigOperators.Group.List.Basic`.

**Data structure and recursion** (verified patterns):

```lean
inductive WT (ι : Type*) where
  | node (label : ι) (children : List (WT ι))

namespace WT   -- NOTE: patterns `| node …` only resolve inside the namespace

def labelOf : WT ι → ι | node l _ => l
def childrenOf : WT ι → List (WT ι) | node _ cs => cs

def size : WT ι → ℕ
  | node _ cs => 1 + (cs.map size).sum
termination_by t => t
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega)

def height : WT ι → ℕ
  | node _ cs => 1 + (cs.map height).foldr max 0
termination_by t => t
decreasing_by
  simp_wf
  exact Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption)) (by omega)

def IsProper (t : WT ι) : Prop :=
  match t with
  | node _ cs => (cs.map labelOf).Nodup
```

Termination finding: `decreasing_by simp_wf` alone does **not** close the `sizeOf` goals for
recursion through `List.map`; the explicit `List.sizeOf_lt_of_mem` line is required (Lean core
`Init/Data/List/BasicAux.lean:295`).

**Support lemmas** (verified): `size_pos`, `size_le_sum_of_mem` (by `induction cs generalizing c`
— plain `induction cs` fails with a dependent-elimination error on the membership hypothesis),
`length_le_sizeSum` (via `List.length_le_sum_of_one_le`, `Algebra/BigOperators/Group/List/Basic.lean:518`).

**The finiteness theorem** (the risky part — 65 lines total):

```lean
noncomputable def fintypeSizeLE [Fintype ι] [DecidableEq ι] :
    ∀ N : ℕ, Fintype {t : WT ι // t.size ≤ N} := by
  intro N
  induction N with
  | zero =>
    exact ⟨∅, by
      rintro ⟨t, ht⟩
      cases t with
      | node _ cs =>
        have : 1 + (cs.map size).sum ≤ 0 := by simpa [size] using ht
        omega⟩
  | succ n ih =>
    classical
    letI := ih
    let T := {t : WT ι // t.size ≤ n}
    let f : {t : WT ι // t.size ≤ n + 1} → ι × (Fin n → Option T) := fun t => by
      cases t with
      | mk tval ht =>
        cases tval with
        | node l cs =>
          let childrenT : List T := cs.attach.map (fun c => (⟨c.1, by
            have hle : (node l cs).size ≤ n + 1 := ht
            simp [size] at hle
            exact Nat.le_trans (size_le_sum_of_mem c.2) (by omega)⟩ : T))
          exact (l, fun k =>
            if hk : k.1 < childrenT.length then some (childrenT.get ⟨k.1, hk⟩) else none)
    have hf_injective : Function.Injective f := by
      rintro ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ h
      cases t₁ with
      | node l₁ cs₁ =>
        cases t₂ with
        | node l₂ cs₂ =>
          simp [f] at h
          rcases h with ⟨rfl, hpad⟩
          have hlen₁ : cs₁.length ≤ n := by …      -- via length_le_sizeSum + omega
          have hlen₂ : cs₂.length ≤ n := by …
          have hcs : cs₁ = cs₂ := by                -- List.ext_getElem?' + Option.some.inj
            apply List.ext_getElem?'
            intro i hi
            have hi' : i < n := lt_of_lt_of_le hi (max_le hlen₁ hlen₂)
            have e := congrFun hpad ⟨i, hi'⟩
            by_cases hi₁ : i < cs₁.length
            · have hi₂ : i < cs₂.length := by
                by_contra hni
                have : ¬ i < cs₂.length := hni
                simp [hi₁, this] at e
              rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]
              exact congrArg Option.some (congrArg (fun t : T => t.1) (Option.some.inj (by
                simpa [hi₁, hi₂] using e)))
            · have hi₂ : ¬ i < cs₂.length := by
                by_contra hi₂'
                simp [hi₁, hi₂'] at e
              simp [hi₁, hi₂]
          apply Subtype.ext
          exact congrArg (node l₁) hcs
    exact Fintype.ofInjective f hf_injective
```

**Conclusion: the finiteness mechanism works.** {proper witness trees over finite `ι` with
size ≤ N} is a Fintype: take the subtype `{t : WT ι // IsProper t ∧ t.size ≤ N}` of
`fintypeSizeLE` (`Fintype.subtype` + `classical`). The same argument gives the height-bounded
variant needed for the Galton–Watson induction. Iteration notes worth recording for the blueprint
(all resolved): (i) `node` is a parser keyword → keep patterns inside a namespace; (ii) inductive
fields give no projections → define `labelOf`/`childrenOf`; (iii) `rw` on subtype-equalities fails
with motive errors → close with `Subtype.ext` + `congrArg (node l₁)`; (iv) `Fintype` instances for
`Option`/functions/`Prod` need their own imports (see the trap in §2.6).

---

## 4. Missing infrastructure (everything to create)

Each item with a Lean-level statement. All are MT-specific; none requires new mathlib content.

1. **Variable model** (new, ~30 lines):
   ```lean
   structure VariableModel (ι κ : Type*) [Fintype ι] [Fintype κ] where
     Ω : κ → Type*
     [mΩ : ∀ j, MeasurableSpace (Ω j)]
     μ : (j : κ) → Measure (Ω j)
     [hμ : ∀ j, IsProbabilityMeasure (μ j)]
     A : ι → Set (Π j, Ω j)
     [hA : ∀ i, MeasurableSet (A i)]
     vbl : ι → Finset κ
     determines : ∀ i, ∃ C : Set (Π j : vbl i, Ω j), MeasurableSet C ∧ A i = cylinder (vbl i) C
   ```
   (cylinder form — §5.4). The overlap graph is a bare function `Adj i j := (vbl i ∩ vbl j).Nonempty`;
   no `SimpleGraph` needed (a `SimpleGraph` would add `DecidableRel`/`neighborSet` ceremony for no
   gain — the LLL file's experience; agent D can confirm).

2. **Overlap graph is a dependency graph** (🟡 glue, ~20 lines) — from `iIndepFun_pi` +
   `iIndepFun_iff_iIndep` + `indep_iSup_of_disjoint` + `indep_of_indep_of_le_left/right`
   (`Independence/Basic.lean:371/:375`) + `MeasurableSpace.pi`'s iSup form, prove:
   ```lean
   theorem indep_generateFrom_of_disjoint_vbl (S T : Finset ι) (hST : Disjoint S T) :
     Indep (generateFrom {t | ∃ i ∈ S, A i = t}) (generateFrom {t | ∃ j ∈ T, A j = t})
       (Measure.pi μ)
   ```
   (Not compile-tested as a package; each ingredient is verified, cf. the LLL survey §2.2 which
   tested the identical idiom.)

3. **Counting-function measurability** (🟡 small): either a lemma
   `measurable_iff_fiber` for countable codomains (not found in mathlib) or structural proofs
   for each `Λ t`; recommend the latter.

4. **Truncated table + algorithm** (new, ~120 lines): `Ω_N`, initial assignment, resampling
   step, padded log `Λ : Π p, Ω p.1 → ℕ → ι`, stopping time `R`, count
   `N_i^{(N)} ω = #{t < N | Λ t ω = i}` via `Finset.card (Finset.filter … (Finset.range N))`.

5. **Witness trees** (new, ~100 lines): `WT ι` (as compile-tested), `T (Λ) (t)` by reverse-chronological
   insertion with the deepest-eligible + least-index tie-break, `IsProper`, depth/size lemmas,
   Prop 10.1, Lemma 11.1, Cor 11.2, Prop 12.1 (injectivity via A-label counts).

6. **τ-check + coupling lemma** (new, ~150 lines): the τ-check event as a finite intersection of
   cylinders over pairwise-disjoint table-coordinate finsets; the product-of-measures identity via
   test (3) generalized from 2 to n vertices (induction — untested but mechanical); the coupling
   map `Ω_N → Ω_check` built from the tree structure (the hard part is not measure theory but the
   bookkeeping of row indices `σ_j(u)`, notes §14).

7. **Galton–Watson weight formula** (new, ~80 lines): products over `childrenOf` labels with
   `Finset.prod`-lemmas; the telescoping uses `Finset.prod_eq_mul_prod_diff_singleton`
   (`Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:202`, from the LLL survey).

8. **Main theorem + corollaries** (new, ~100 lines):
   ```lean
   theorem moserTardos_bound (hLLL : ∀ i, μN (A i preimage…) ≤ ENNReal.ofReal (x i * ∏ j ∈ Γ i, (1 - x j))) :
     ∫⁻ ω, (N_i^{(N)} ω : ℝ≥0∞) ∂(Measure.pi (fun p : (_ : κ) × Fin N => μ p.1))
       ≤ ENNReal.ofReal (x i / (1 - x i))
   ```
   with `x i ∈ [0,1)`, plus total-resamples, Markov tail `μ_N (R = N) ≤ (∑ᵢ x i/(1−x i))/N`,
   constructive LLL `∃ σ, ∀ i, σ ∉ A i`, and (follow-up) the symmetric form.

9. **ENNReal glue specific to MT** (🟡): none missing in principle — `ofReal_div_of_pos`
   covers `x i / (1 - x i)` (with the `x i = 0` split first); the division-free product form
   `ENNReal.ofReal (x i * ∏ …) ≤ μ(A i)` is preferred as the hypothesis shape to avoid division
   altogether in the core proof.

---

## 5. Decisions recommended (with rationale)

**5.1 Countable product measures — keep the finite-truncation formulation.** mathlib v4.32.0
*does* have `Measure.infinitePi` (arbitrary index type, probability measures only, no Polish
assumptions), so an infinite-table a.s. statement is feasible — but the finite-truncation
architecture remains the right choice: (i) the algorithm, the log `Λ`, `R`, and every count are
finite objects; (ii) the main theorem is a uniform-in-`N` bound, which the a.s. formulation would
need anyway via limits; (iii) the constructive-LLL corollary needs a single `N` with `R < N`.
The infinite API is still used inside the finite proof (the cylinder identity, test (4)), and a
later upgrade to `μ(R = ∞) = 0` on `infinitePi` via `infinitePi_eq_pi` + monotone limits is a
clean follow-up PR.

**5.2 Determinism formulation — least-index pick rule.** Use
`(Finset.univ.filter (fun i => σ ∈ A i)).min' h` under `[LinearOrder ι]` (compile-tested). This
is simpler than a parameterized `pick : {S : Set ι // S.Nonempty} → ι` and suffices: the proof
only needs *some* deterministic rule. (If agent B wants the parameterized version for generality,
it costs one extra hypothesis and changes nothing downstream.)

**5.3 Tree representation — custom inductive with `List` children.** Recommended:
`WT ι := node (label : ι) (children : List (WT ι))`. Rationale: (i) `T(Λ,t)` is built by
reverse-chronological insertion — the child order is exactly the insertion order, which makes the
construction a plain function; (ii) properness is `(childrenOf.map labelOf).Nodup`, the exact
statement of Prop 10.1's definition; (iii) `size`/`height`/`childrenOf` recurse cleanly
(compile-tested). Alternatives considered and rejected: mathlib `BinaryTree` (binary only);
`SimpleGraph.IsTree` (a Prop over graphs — no data, no vertex addressing, heavy);
`Multiset` children (would make the Fintype nearly trivial — but there is **no**
`Fintype (Multiset α)` instance in mathlib either, and losing the child order breaks the
deterministic definition of `T(Λ,t)`); a parent-map representation `List (ι × Option (Fin k))`
(attractive for the incremental construction, but complicates size/depth/coupling recursion —
leave as a possible internal representation for agent B to weigh).

**5.4 "`A i` determined by `vbl i`" — the explicit cylinder predicate.** Recommended form:
`∃ C : Set (Π j : vbl i, Ω j), MeasurableSet C ∧ A i = cylinder (vbl i) C`.
Rationale: `cylinder` is defined (`Cylinders.lean:159`) as `(vbl i).restrict ⁻¹' C`, so this form
is *equivalent to* the comap-measurability form (via `MeasurableSpace.measurableSet_comap`,
`MeasurableSpace/Basic.lean:90`) but strictly more usable: the algorithm must **evaluate** `A i`
on the restricted assignment (`σ ∈ A i ↔ (vbl i).restrict σ ∈ C`), and the τ-check events are
literally cylinders over table-coordinate finsets, so the measure computations of §3.1 (3)–(4)
apply directly. The σ-algebra form remains the right statement for the dependency-graph proof
(§4.2), derived from the cylinder form.

**5.5 Table type — Sigma-indexed.** Use `Ω_N := Π p : (_ : κ) × Fin N, Ω p.1` with
`Measure.pi (fun p => μ p.1)` (compile-tested, PLAN syntax). The curried
`Π j : κ, Fin N → Ω j` would need a pushforward equivalence for the measure; the Sigma form is
literally `Measure.pi` and costs nothing. (Note: `Finset.restrict` is the table-side restriction
used by `cylinder`; `(vbl i)`-indexed products in the event type use the same map.)

**5.6 Expectations — ENNReal `lintegral` (per PLAN).** All lemmas verified (§2.3); the only
naming trap is `lintegral_finsetSum'` (do not use the deprecated `lintegral_finset_sum`).

---

## 6. Risks

1. **Import granularity for Fintype instances.** `Fintype.{Option,Pi,Prod,List}` are separate
   importable files; missing one makes `Fintype (ι × (Fin n → Option T))` fail to synthesize with
   a misleading error (witnessed repeatedly during test 2). Mitigation: the blueprint should list
   these imports explicitly; add `Mathlib.Data.Fintype.{Option,Pi,Prod}` alongside the usual
   `Mathlib.Data.Fintype.Basic`.
2. **No `Fintype (List α)` / `Fintype (Multiset α)` in mathlib.** The bounded-tree Fintype must go
   through the padded-function encoding (`Fin n → Option T`) or an equivalent; this is compile-tested
   but adds ~65 lines of finiteness glue. The height-bounded variant (for the GW induction) uses
   the same mechanism and is untested — low risk, but budget for it.
3. **Lean specifics around the tree type.** `node` is a parser keyword (patterns must live inside a
   namespace); inductive fields do not generate projections (`c.label` invalid — use accessor
   defs); `rw` on subtype-equalities hits motive errors (close with `Subtype.ext` +
   `congrArg (node l)`). All resolved in the compile test; they will resurface if the type is
   redesigned.
4. **`lintegral_finset_sum` is deprecated.** Using the old name is easy (it still exists as an
   alias) and will trip linters/style review; use `lintegral_finsetSum'` (Add.lean:341).
5. **No unconditional `ENNReal.ofReal_div`.** The equality form `ofReal_div_of_pos` requires
   `0 < 1 - x i`, forcing the `x i = 0` case split early (PLAN §3 already plans this); forgetting
   the split leaves a stuck positivity goal, not a wrong statement.
6. **τ-check for n > 2 vertices.** Tests (3)–(4) verify the pairwise case; the n-fold
   intersection-product needs a 2-to-n induction (mechanical, untested). If it fights back, the
   fallback is `iIndepFun`-indexed-by-vertices with `iIndepFun.precomp` (`Basic.lean:324`).
7. **`infinitePi`-dependent lemma is the cylinder bridge.** The identity in test (4) currently
   routes through `Measure.infinitePi_eq_pi` + `infinitePi_map_restrict`; if the blueprint prefers
   to avoid importing `Probability.ProductMeasure`, the 3-line proof can be replaced by a direct
   `Measure.pi` argument (`pi_eq` on boxes, `Constructions/Pi.lean:275`) — small either way.
8. **Counting-function measurability.** No codomain-countable "fiber" lemma was found in mathlib;
   if agent B's proof needs `Measurable (Λ t)` as a function (rather than per-fiber measurable
   sets), budget ~30 extra lines of structural proofs or a one-off `measurable_of_countable_range`-style
   lemma.

---

## 7. Open questions

1. **Curried vs Sigma table** — I recommend the Sigma form `Π p : (_ : κ) × Fin N, Ω p.1`
   (compile-tested); confirm with agent B that no part of the proof wants the curried
   `Π j, Fin N → Ω j` (e.g. for readability of the resampling map).
2. **Tree children order** — List children recommended (§5.3). Does agent B's construction of
   `T(Λ,t)` need anything beyond reverse-chronological insertion order (e.g. sibling order in the
   τ-check product)? If not, List is final.
3. **Which finiteness is used where** — the coupling sum needs
   `Fintype {τ : WT ι // IsProper τ ∧ τ.size ≤ N}` (subtype of the tested `fintypeSizeLE`), while
   the GW induction sums over height ≤ h. Should the GW sum be phrased over the Finset of
   bounded-height trees (needs the untested height variant) or avoided by the telescoping
   induction in notes §17–18 (agent B's call)?
4. **Hypothesis shape of the LLL condition** — ENNReal product form
   `μ(A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ Γ i, (1 - x j))` (division-free) vs the divided form; the
   division-free form keeps `ofReal_div_of_pos` out of the core and only enters in the final
   rewrite. Recommend the former.
5. **Statement flavor of the main theorem** — ENNReal `lintegral` bound (as in PLAN §3) with an
   ℝ-valued `Measure.real` corollary, mirroring the LLL file's two-layer style; confirm with
   agent D that this matches `LovaszLocal.lean` conventions.
6. **Do we import `Mathlib.Probability.ProductMeasure` at all** — only for the cylinder identity
   (risk 7). Decide whether the import (and its Ionescu–Tulcea dependency chain) is acceptable for
   a 3-line convenience, or whether to prove the identity directly with `Measure.pi_eq`.
7. **`iIndepFun_pi` vs StatsMLlib `FinsetPi`** — the general lemma now exists in mathlib; should
   StatsMLlib's `pi_eval_iIndepFun`/`pi_comp_eval_iIndepFun` be generalized/deprecated in a
   follow-up (agent D's domain), or does MT just use mathlib's directly?
