# E. Scope & File Planning

## 1. File Location Decision

**Recommendation: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`** (module `StatsMLlib.Probability.Concentration.ConvexDistance`).

### Why the Probability layer

Per `/Users/zhuzekai/workspace/StatsLean/StatsMLlib/ARCHITECTURE.md`, the layer table assigns to `Probability`: "Random variables and processes, **moments, concentration**, entropy methods, Gaussian analysis, and random matrices." Talagrand's convex-distance inequality is unambiguously a concentration result for product measures, so `Probability` is the owning layer. The three competing layers fail the ownership test:

- **`MeasureTheory`** owns "reusable measure, integral, and convergence results that **do not require probabilistic structure**." Talagrand's theorem is the opposite — it is a probabilistic concentration statement; only its ingredients (Measure.pi, Fubini, infDist) live in MeasureTheory.
- **`Analysis`** owns deterministic analytic constructions. The convex-hull geometry is deterministic, but the theorem's subject is probabilistic. The repo precedent `Probability/RandomMatrix` vs `LinearAlgebra/Matrix` (deterministic matrix spectral theory in LinearAlgebra, random-matrix theorems in Probability) shows the theorem's subject, not its technique, decides the layer.
- **`LearningTheory` / `Statistics`** are downstream tiers; the inequality itself has no learning-theoretic structure. The empirical-process form (Bousquet-Talagrand) belongs there later, and would import from Probability — a legal downward edge.

### Why `Concentration/` (not a new sibling)

`Probability/Concentration/` is the established home for named inequalities: `Chernoff`, `Hoeffding`, `McDiarmid`, `EfronStein`, `HansonWright`, `Maximal`, plus the `LogSobolev/` family. The proposal's placement matches the naming rule "Prefer full subject names in paths" — `ConvexDistance` is a precise subject name, exactly like `RandomMatrix`, `LogSobolev`, `EckartYoungMirsky`.

### Directory alternative `ConvexDistance/`

Allowed by the rules: `ARCHITECTURE.md` permits `Defs.lean` "only when their directory gives a precise subject," and `ConvexDistance/Defs.lean` does. But it is not the right *initial* shape — see Section 2.

### Import-flow check (preview)

All imports needed (Section 4) are Mathlib, plus at most same-layer StatsMLlib modules. Everything flows downward; no cycle is possible because no existing module imports ConvexDistance. Full tier-compliance check in Section 4.

## 2. Single vs Multi-File Recommendation

**Recommendation: ONE file `ConvexDistance.lean` for the initial contribution**, organized with clear `/-! ## ... -/` section headers, with a documented promotion path to a directory.

### Evidence from repo convention

| File | Size | Nature |
| --- | ---: | --- |
| `Probability/Concentration/HansonWright.lean` | 207 KB | one inequality, one file |
| `Probability/Concentration/EfronStein.lean` | 125 KB | one inequality + machinery, one file |
| `Probability/Concentration/McDiarmid.lean` | 48 KB | one inequality (pos/neg/tails), one file |
| `Probability/Concentration/Maximal.lean` | 34 KB | one inequality family, one file |
| `Probability/Concentration/LogSobolev/` | 5 files | a *family* of related inequalities sharing infrastructure |
| `LearningTheory/Rademacher/` | 6 files | multi-theorem area with a real definition layer (Signs, empiricalRademacherComplexity, rademacherComplexity) |
| `Probability/Gaussian/Sobolev/` | 5 files | large machinery (mollifiers, density theorems) split off from defs |

The repo's rule is: **a single theorem → a single file, even at 200 KB**; directories appear only for *families* with substantial independently-useful definitions.

### Why the criteria favor one file

1. **Expected size.** The proof is the standard coordinate induction (10 steps: defs, properties, base cases, `Fin (n+1) ≃ Fin n ⊕ PUnit` identification, projection/section decomposition, geometric recursion, exponentiation + Holder, Fubini, scalar optimization, Markov tail). McDiarmid's martingale argument is 48 KB; EfronStein's induction is 125 KB. A fair estimate is **60–120 KB** — comfortably within the single-file convention (under the 207 KB precedent).
2. **The definition layer is tiny.** `mismatchVector`, `convexMismatchSet`, `convexDistance` are 2–6 lines each. Compare `Rademacher/Defs.lean` (Signs + two complexity definitions + a dozen lemmas) or `Gaussian/Sobolev/Defs.lean` (GaussianSobolevNorm, MemW12Gaussian, smoothCutoff, smoothCutoffR, stdMollifier, mollify). A `ConvexDistance/Defs.lean` would be the smallest Defs file in the repo by an order of magnitude, with zero external consumers.
3. **Strictly linear dependency chain.** Defs → basic properties → sections/projection lemmas → geometric recursion → main theorem → tails. Every later declaration needs the earlier ones *within the same PR*; splitting creates an artificial boundary with churn when a proof step needs a lemma from the other file (e.g., the recursion needs the `≤ sqrt n` bound from the properties section).
4. **Definitions are reusable, but file-level imports make that moot.** Consumers import whole files (e.g., `UniformDeviation/Bounds.lean` imports all of McDiarmid). There is no partial-import benefit until the file is large.
5. **Future extension paths are additive.** Weighted-Hamming dual, convex-Lipschitz, and certificate applications are new *statements* using the public API of the first three definitions — they can land as new sections in the same file, and the moment they arrive is exactly the moment to promote (see below). The promotion is lossless and precedented.

### Promotion trigger (documented in the file header or proposal)

Promote `ConvexDistance.lean` → `ConvexDistance/` when **either**:
- the file exceeds ~150 KB, or
- the first application-family PR lands (convex-Lipschitz, weighted-Hamming dual, certificates, or a `Fin n` → `Fintype ι` generalization).

Split mapping:

```
ConvexDistance/Defs.lean          ← defs + basic properties + measurability notes
ConvexDistance/Inequality.lean    ← sections/recursion + main theorem + tails
ConvexDistance/Applications.lean  ← convex-Lipschitz, weighted-Hamming dual, certificates (new content)
```

If maintainers prefer the directory from day one, use **`Defs.lean` + `Inequality.lean` only** — do not create an empty `Applications.lean` (no placeholder files exist in the repo). This document plans the single-file structure; Section 3 gives the per-section mapping so the split is mechanical.

## 3. Module Content Plan

### File: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`

Header: `Copyright (c) 2026`, `Authors:` (per `CONTRIBUTING.md`), module docstring `# Talagrand's Convex-Distance Inequality` with `## Main definitions`, `## Main results`, `## References` (Talagrand 1995, Ledoux "Four Talagrand Inequalities", BLM). `open MeasureTheory ProbabilityTheory Real`, `open scoped ENNReal`.

### Section A. Definitions

```lean
/-- Coordinatewise disagreement indicator: (mismatchVector x y) i = 1 iff x i ≠ y i. -/
def mismatchVector {n : ℕ} {Ω : Type*} [DecidableEq Ω] (x y : Fin n → Ω) :
    EuclideanSpace ℝ (Fin n)

/-- Convex hull of disagreement vectors between x and points of A. -/
def convexMismatchSet {n : ℕ} {Ω : Type*} (A : Set (Fin n → Ω)) (x : Fin n → Ω) :
    Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (mismatchVector x '' A)

/-- Talagrand's convex distance from x to A. -/
def convexDistance {n : ℕ} {Ω : Type*} (A : Set (Fin n → Ω)) (x : Fin n → Ω) : ℝ :=
  Metric.infDist 0 (convexMismatchSet A x)
```

These match the proposal and repo camelCase-definition style (`uniformDeviation`, `empiricalRademacherComplexity`, `flipCoord`). `[DecidableEq Ω]` is required by the `if x i = y i then 0 else 1` body. Keep `convexDistance`'s range ℝ (not NNReal) so the squared/tail statements stay simple.

### Section B. Basic properties

- `mismatchVector_self : mismatchVector x x = 0`
- `mismatchVector_apply (i) : (mismatchVector x y) i = if x i = y i then 0 else 1` (reduction lemma for the recursion)
- `mismatchVector_norm_le : ‖mismatchVector x y‖ ≤ Real.sqrt n` (Euclidean norm; entries in `{0,1}`)
- `convexDistance_nonneg : 0 ≤ convexDistance A x` (from `Metric.infDist_nonneg`)
- `convexDistance_mem : x ∈ A → convexDistance A x = 0`
- `convexDistance_mono : A ⊆ B → convexDistance B x ≤ convexDistance A x`
- `convexDistance_le_sqrt : A.Nonempty → convexDistance A x ≤ Real.sqrt n` (inf over nonempty set ≤ distance to any witness `y ∈ A`)
- `convexDistance_eq_zero_iff : convexDistance A x = 0 ↔ 0 ∈ convexMismatchSet A x` (only if the induction needs it; note this is *not* `x ∈ A` in general)

### Section C. Sections and projections (`Fin (n+1) → Ω ≃ (Fin n → Ω) × Ω`)

- Identification: `Equiv.sumArrowEquivProdArrow` with `finSumFinEquiv` / `Fin.succFunEquiv`; measure compatibility of `Measure.pi` under the equiv (`Measure.pi_update`, `pi_pi`).
- `projection` `B := {x | ∃ ω, (x, ω) ∈ A}` and `section A ω := {x | (x, ω) ∈ A}`.
- `measure_section_integral` (Fubini): `probReal (Measure.pi μs) A = ∫ ω, probReal (Measure.pi (μs ∘ Fin.castSucc)) (section A ω) ∂ (μs (Fin.last n))`.
- Finite-discrete measurability: with `[Fintype Ω] [MeasurableSingletonClass Ω]` every set in `Fin n → Ω` is measurable (instance-based; `MeasurableSingletonClass.pi`), so all sets/functions below are measurable and `Real.exp (convexDistance A x ^ 2 / 4)` is integrable automatically. Only a handful of `measurability`-trigger lemmas should be needed.

### Section D. Key geometric recursion

- `convexDistance_recursion` — the heart of the proof: for `0 ≤ λ`, `λ ≤ 1`, nonempty `A`, and `B`, `Aω` as above,

  ```
  convexDistance A (x, ω) ^ 2
    ≤ (1 - λ) * convexDistance B x ^ 2 + λ * convexDistance (Aω) x ^ 2 + (1 - λ) ^ 2
  ```

  with a companion lemma handling empty sections `Aω = ∅` (replaced by the `≤ sqrt n` bound or a trivial factor, since `μ {ω} = 0` sections carry no mass).
- Supporting scalar lemma for the `λ`-optimization (the constant `4` in the exponent emerges here): a weighted-AM-GM / one-variable calculus inequality, provable via `Mathlib.Analysis.MeanInequalities` or `nlinarith`.

### Section E. Main theorem (exponential-integrability form)

```lean
theorem talagrand_convexDistance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω]
    [MeasurableSingletonClass Ω] {μs : Fin n → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {A : Set (Fin n → Ω)} (hA : A.Nonempty) :
    probReal (Measure.pi μs) A *
      ∫ x, Real.exp (convexDistance A x ^ 2 / 4) ∂(Measure.pi μs) ≤ 1
```

The ℝ/`probReal` form matches McDiarmid's `(μ s).toReal` style and the `MeasureTheory.probReal` API already used in the repo (e.g., `Probability/Gaussian/Lipschitz.lean:115`). The variable block `{μs : Fin n → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]` is exactly the pattern already used in `EfronStein.lean` (line 13) — a strong precedent. Proof steps: base cases `n = 0, 1` → identify `Fin (n+1)` → apply the recursion inside `exp` → Holder/interpolation on the product measure → invoke induction hypotheses for `B` and the nonempty sections → Fubini to recover `probReal μ A` → scalar optimization. (Helper: `exp_recursion_bound`, an exp-monotonicity lemma; the Holder step needs an `(∫ f)^(1-λ) (∫ g)^λ`-type interpolation lemma — flagged as a gap to pin down in survey B.)

### Section F. Tail corollaries

- `talagrand_convexDistance_tail_pos` — upper tail (Markov on `exp (d^2/4)`): for `0 ≤ t`,

  ```
  probReal μ A * probReal μ {x | t ≤ convexDistance A x} ≤ Real.exp (-(t ^ 2) / 4)
  ```

- `talagrand_convexDistance_tail_half` — the `1/2`-measure version:

  ```
  1 / 2 ≤ probReal μ A → probReal μ {x | t ≤ convexDistance A x} ≤ 2 * Real.exp (-(t ^ 2) / 4)
  ```

- `talagrand_convexDistance_tail_neg` — complement/lower-tail version (mirrors `mcdiarmid_inequality_neg`): the same statement with `Aᶜ`:

  ```
  probReal μ Aᶜ * probReal μ {x | t ≤ convexDistance Aᶜ x} ≤ Real.exp (-(t ^ 2) / 4)
  ```

- `talagrand_convexDistance_two_sided` — conjunction of the pos and neg half-measure versions:

  ```
  1 / 2 ≤ probReal μ A → 1 / 2 ≤ probReal μ Aᶜ →
    (probReal μ {x | t ≤ convexDistance A x} ≤ 2 * Real.exp (-(t ^ 2) / 4)
      ∧ probReal μ {x | t ≤ convexDistance Aᶜ x} ≤ 2 * Real.exp (-(t ^ 2) / 4))
  ```

### Future promotion mapping (if split later)

| Single-file section | Future file |
| --- | --- |
| A + B (+ measurability notes) | `ConvexDistance/Defs.lean` |
| C + D + E + F | `ConvexDistance/Inequality.lean` |
| (new) weighted-Hamming dual, convex-Lipschitz, certificates | `ConvexDistance/Applications.lean` |

## 4. Import Dependency Analysis

### Mathlib imports (all standard, mathlib v4.32.0)

| Import | Purpose | Verified in package |
| --- | --- | --- |
| `Mathlib.MeasureTheory.Constructions.Pi` | `Measure.pi`, `pi_pi`, `Measure.pi_update` | used by `EfronStein`, `FinsetPi` |
| `Mathlib.MeasureTheory.Integral.Pi` | Fubini/integral for product measures | used by `EfronStein` |
| `Mathlib.MeasureTheory.Integral.Prod` | `integral_prod` (×-identification route) | used by `EfronStein`, `Moments/Expectation` |
| `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` | `IsProbabilityMeasure` | used repo-wide |
| `Mathlib.MeasureTheory.Measure.Typeclasses.Finite` | finite-measure classes | used by `Moments/Expectation` |
| `Mathlib.Probability.Notation` | `μ[f]` expectation notation | used repo-wide |
| `Mathlib.Probability.Moments.Basic` | `ProbabilityTheory.measure_ge_le_exp_mul_mgf` (Markov/mgf tail, line 429) | used by `McDiarmid` |
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `EuclideanSpace`, `EuclideanSpace.finAddEquivProd` (line 380), norm API | `finAddEquivProd` verified |
| `Mathlib.Analysis.Convex.Hull` | `convexHull` (line 46) | verified |
| `Mathlib.Analysis.Convex.Combination` | `Finset.centerMass_mem_convexHull` (finite hull elements) | verified |
| `Mathlib.Topology.MetricSpace.HausdorffDistance` | `Metric.infDist` (line 573), `infDist_nonneg`, `isGLB_infDist` | verified |
| `Mathlib.Logic.Equiv.Fin.Basic` | `Fin.succFunEquiv`, `Fin.castSucc`, `Fin.succAbove` | verified |
| `Mathlib.Analysis.MeanInequalities` | weighted AM-GM / interpolation for the `λ`-optimization and Holder step | standard |
| `Mathlib.Data.Set.Finite` (+ `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`) | finite-set measurability under `MeasurableSingletonClass` | standard |

### StatsMLlib imports

- **Required: none.** The proof is self-contained in Mathlib.
- **Optional:** `StatsMLlib.Probability.Independence.FinsetPi` (`pi_map_eval`) if marginal-extraction helpers prove convenient — same layer, allowed.
- **Tier check:** Probability layer may import within its own layer and from `{MeasureTheory, Topology, LinearAlgebra, Analysis}`. Every StatsMLlib candidate is in `Probability` itself. **No later-tier import, no cycle**: `ConvexDistance` is a leaf module — no existing StatsMLlib file imports it (verified by grep: zero references to `talagrand`/`convexDistance` in `StatsMLlib/`), and none of its imports reach toward it.
- Weight note: `PiL2` is already imported by the Statistics least-squares linear chain, and `Integral.Pi`/`Prod` by EfronStein, so no new heavy dependency enters the build graph.

### Bookkeeping

Adding the file changes the module count (89 → 90) in `FILE_TREE.md`; per `CONTRIBUTING.md`, run `LEAN_NUM_THREADS=$(nproc) lake build` and keep the file free of warnings, `sorry`, `axiom`, and unused parameters.

## 5. Future Extension Path

| Extension | Where it lands | Supported by the initial structure? |
| --- | --- | --- |
| `Fin n` → arbitrary `Fintype ι` | new section in the same file (or `Inequality.lean` after promotion) | **Yes.** Transport exactly as `mcdiarmid_inequality_pos` does (line ~968: `let ιm : ι ≃ Fin m := Fintype.equivFinOfCardEq rfl`), reindexing `mismatchVector` under the equiv. The `Fin n` development must stay self-contained so the corollary is a thin wrapper. |
| Finite discrete `Ω` → countable/Polish | new file `ConvexDistance/Polish.lean` (or section) | **Yes, structurally.** Requires new machinery (projection measurability, `infDist` attainment, section measurability) — a separate PR. Public statement shapes (`convexDistance`, the recursion) do not change. |
| Weighted-Hamming dual formulation | new section (Applications) | **Yes.** Reuses only `mismatchVector` + `convexMismatchSet`; the defs are top-level public API. |
| Convex-Lipschitz concentration | `ConvexDistance/Applications.lean` (or `Probability/Concentration/ConvexLipschitz.lean`) | **Yes.** Corollary using `talagrand_convexDistance` + convexity of `{f ≤ med}`. This is the discrete-product counterpart of the existing `Probability/Gaussian/LipschitzConcentration.lean`. |
| Talagrand's T₂ transport inequality | new module (e.g., `Probability/Entropy/` or a Transport area) | **Yes, independent.** Different technique (couplings); may cite the main theorem later. |
| Bousquet-Talagrand empirical-process inequality | `LearningTheory/EmpiricalProcess/Talagrand.lean` | **Yes, layer-compliant.** LearningTheory may import Probability (downward edge); the main theorem's importable API is exactly what such a file needs. |

One design note for this support: state the main theorem in terms of `convexDistance` (as planned) rather than in terms of tubular neighborhoods or certificates, so all future consumers have a stable API.

## 6. Downstream Consumer Analysis

Existing modules that import the concentration inequalities Talagrand sits alongside:

- `LearningTheory/UniformDeviation/Bounds.lean` — the only file importing `Probability.Concentration.McDiarmid` (line 8). Its uniform-deviation tail bounds are the natural place a future `talagrand`-based one-sided deviation bound for finite classes would be added (the functional `x ↦ sup_f (P_n f - P f)` is convex in the sample even when the class is not convex, so Talagrand gives Gaussian-type one-sided tails). Additive theorem, no refactor.
- `LearningTheory/Rademacher/Massart.lean` — imports `Probability.Concentration.Maximal` (line 7). The Rademacher sum `sup_f (1/n) Σ ε_i f(x_i)` is convex in the signs `ε`, so Talagrand's inequality yields concentration of Rademacher processes — a future `Rademacher/Talagrand.lean` or an addition to `Complexity.lean`.
- `Probability/Concentration/Maximal.lean` (imports Hoeffding) and `McDiarmid.lean` (imports Hoeffding) — thematic neighbors; no changes.

Potential beneficiaries with no current concentration import:

- `Probability/Gaussian/LipschitzConcentration.lean` — the Gaussian (LSI-route) analog; a unified "convex-Lipschitz on product spaces" corollary is a future cross-cutting result.
- `Statistics/Regression/LeastSquares/*` — the Linear pipeline is Gaussian-complexity driven (`LocalGaussianComplexity`, `SubGaussianity` import `Probability.Gaussian.*`), the L1 pipeline is covering-number driven; no immediate benefit, possible long-term use in localization arguments.
- `Probability/Process/FiniteMaximum.lean`, `Probability/SmallBall.lean` — no direct use.

**Bottom line:** no existing file needs modification for the initial PR; the concrete future consumers are `UniformDeviation/Bounds` and the Rademacher family, both importing from a later tier (allowed downward).

## 7. Proposed Names

**Module**: `StatsMLlib.Probability.Concentration.ConvexDistance` (file `StatsMLlib/Probability/Concentration/ConvexDistance.lean`).

**Namespace**: no new namespace for the main theorems — top-level with a `talagrand_` prefix, exactly matching the `mcdiarmid_*` precedent (McDiarmid.lean is namespace-free; Hoeffding/Maximal use `ProbabilityTheory`; HansonWright uses a subject namespace). Rationale: `mcdiarmid_inequality_*` is the closest sibling and sets the pattern for named concentration inequalities.

**Definitions** (endorse the proposal's names; repo-consistent camelCase):

- `mismatchVector` — disagreement vector `(if x i = y i then 0 else 1)` in `EuclideanSpace ℝ (Fin n)`
- `convexMismatchSet` — `convexHull ℝ (mismatchVector x '' A)`
- `convexDistance` — `Metric.infDist 0 (convexMismatchSet A x)`

**Theorems**:

- `talagrand_convexDistance` — main exponential-integrability form (Section 3.E)
- `talagrand_convexDistance_tail_pos` — upper tail with the `1 / probReal μ A` factor
- `talagrand_convexDistance_tail_half` — the `probReal μ A ≥ 1 / 2` corollary (`≤ 2 * exp (-(t^2) / 4)`)
- `talagrand_convexDistance_tail_neg` — complement (lower-tail) variant, mirroring `mcdiarmid_inequality_neg`
- `talagrand_convexDistance_two_sided` — conjunction of pos/neg half-measure versions

**Internal helpers** (no public API): `mismatchVector_self`, `mismatchVector_apply`, `mismatchVector_norm_le`, `convexDistance_nonneg`, `convexDistance_mem`, `convexDistance_mono`, `convexDistance_le_sqrt`, `measure_section_integral`, `convexDistance_recursion`, and the scalar `λ`-optimization lemma (names ending in `_recursion` / `_optimization` to keep them clearly internal).

## Summary: Proposed File Structure

```text
StatsMLlib/
└── Probability/
    └── Concentration/
        ├── Chernoff.lean
        ├── EfronStein.lean
        ├── HansonWright.lean
        ├── Hoeffding.lean
        ├── LogSobolev/            (existing family)
        ├── Maximal.lean
        ├── McDiarmid.lean
        └── ConvexDistance.lean    ← NEW (initial PR)
            ├── Section A: Definitions (mismatchVector, convexMismatchSet, convexDistance)
            ├── Section B: Basic properties (nonneg, mono, sqrt-n bound)
            ├── Section C: Sections/projections for Fin (n+1) ≃ (Fin n) × Ω
            ├── Section D: Geometric recursion (convexDistance_recursion)
            ├── Section E: talagrand_convexDistance (exponential-integrability form)
            └── Section F: Tail corollaries (pos, half, neg, two-sided)
```

Future promotion (trigger: >~150 KB or first applications PR):

```text
Probability/Concentration/ConvexDistance/
├── Defs.lean          ← Sections A + B
├── Inequality.lean    ← Sections C + D + E + F
└── Applications.lean  ← convex-Lipschitz, weighted-Hamming dual, certificates (added when written)
```

The single-file choice is consistent with every precedent in the repo (HansonWright at 207 KB stayed one file), avoids premature module boundaries on a strictly linear proof chain, keeps the tiny definition layer exactly where its consumers are, and makes all six future extension paths additive rather than structural.
