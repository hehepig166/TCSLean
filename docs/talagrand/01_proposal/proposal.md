# Proposal: Talagrand's Convex-Distance Inequality on Finite Discrete Product Spaces

## Motivation

StatsMLlib currently has Hoeffding, McDiarmid (bounded differences), Efron–Stein, and Gaussian
Lipschitz concentration — but no convexity-aware concentration result. Talagrand's convex-distance
inequality fills this gap: it provides Gaussian-type `exp(−t²/4)` tails for *any* set `A` in a
product space, not just those expressible via bounded-difference functions. The inequality is a
cornerstone of modern concentration theory with downstream applications to:

- Convex-Lipschitz function concentration
- Rademacher process tail bounds (the empirical-process sup is convex in the signs)
- One-sided uniform deviation bounds for finite classes
- Weighted-certificate and influence-function arguments

This proposal formalizes the simplest version — finite discrete coordinate spaces — using the
standard coordinate-induction proof. A key finding from the survey is that the 0/1-mismatch
convention (as opposed to the ±1 formulation) eliminates the calculus-heavy scalar optimization
for two-valued coordinates, making the first contribution tractable.

## Proposed Theorem (Simplest Version)

### Definitions

Let `Ω` be a finite discrete measurable space. For `x, y : Fin n → Ω`:

```lean
def mismatchVector {n : ℕ} {Ω : Type*} [DecidableEq Ω] (x y : Fin n → Ω) :
    EuclideanSpace ℝ (Fin n) :=
  fun i => if x i = y i then (0 : ℝ) else 1
```

For `A : Set (Fin n → Ω)` and `x : Fin n → Ω`:

```lean
def convexMismatchSet {n : ℕ} {Ω : Type*} (A : Set (Fin n → Ω)) (x : Fin n → Ω) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  convexHull ℝ (mismatchVector x '' A)

def convexDistance {n : ℕ} {Ω : Type*} (A : Set (Fin n → Ω)) (x : Fin n → Ω) : ℝ :=
  Metric.infDist 0 (convexMismatchSet A x)
```

### Main Theorem (Exponential-Integrability Form)

For `μs : Fin n → Measure Ω` all probability measures, `μ := Measure.pi μs`, and nonempty `A`:

```lean
theorem talagrand_convexDistance {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω]
    [MeasurableSingletonClass Ω] {μs : Fin n → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {A : Set (Fin n → Ω)} (hA : A.Nonempty) :
    probReal (Measure.pi μs) A *
      ∫ x, Real.exp (convexDistance A x ^ 2 / 4) ∂(Measure.pi μs) ≤ 1
```

The multiplication form avoids division by `probReal μ A` (total for `μ(A) = 0`).

### Tail Corollary

For `t ≥ 0`:

```lean
theorem talagrand_convexDistance_tail (ht : 0 ≤ t) :
    probReal μ A * probReal μ {x | t ≤ convexDistance A x} ≤ Real.exp (-(t ^ 2) / 4)
```

When `probReal μ A ≥ 1/2`:

```lean
theorem talagrand_convexDistance_tail_half (h : 1/2 ≤ probReal μ A) (ht : 0 ≤ t) :
    probReal μ {x | t ≤ convexDistance A x} ≤ 2 * Real.exp (-(t ^ 2) / 4)
```

Plus `_neg` (complement) and `_two_sided` variants mirroring McDiarmid's pattern.

### Initial Scope

- Index type: `Fin n` (induction-friendly; generalization to `Fintype ι` via `Fintype.equivFinOfCardEq` is a thin post-hoc wrapper, exactly as in McDiarmid)
- Coordinate space: `Ω` finite discrete with `[Fintype Ω] [MeasurableSingletonClass Ω]` (all sets/functions automatically measurable)
- **Coordinate values: two-valued (uniform Bernoulli or biased coin).** The survey [C_proof_strategy](survey/C_proof_strategy.md) found that for two-valued coordinates the scalar optimization step admits a purely arithmetic `λ ∈ {0,1}` case-split proof with no calculus — the 0/1-mismatch convention makes the recursion constant `(1−λ)²` and allows per-branch `λ` choices. General finite `Ω` requires a non-trivial scalar inequality deferred to a follow-up PR.
- Coordinate measures: heterogeneous (allowed to differ per coordinate, matching `EfronStein`'s `μs : Fin n → Measure Ω` pattern)

## Proposed Location

**Single file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`**
(Module: `StatsMLlib.Probability.Concentration.ConvexDistance`)

The survey [E_scope_and_files](survey/E_scope_and_files.md) recommends one file for the initial
contribution, consistent with every named inequality in the repo (HansonWright at 207 KB stayed
one file). Promotion trigger to `ConvexDistance/Defs.lean` + `ConvexDistance/Inequality.lean` +
`ConvexDistance/Applications.lean` when either >~150 KB or the first applications PR lands.

The file is organized in 6 sections with `/-! ## ... -/` headers:

| Section | Contents | Difficulty |
|---------|----------|------------|
| A. Definitions | `mismatchVector`, `convexMismatchSet`, `convexDistance` | Easy |
| B. Basic Properties | Nonnegativity, monotonicity, `≤ sqrt n`, Lipschitz, ε-approximations | Easy–Medium |
| C. Sections & Projections | `Fin (n+1) ≃ (Fin n) × Ω` transport, `B` and `A_ω` definitions, Fubini | Medium–Hard |
| D. Geometric Recursion | `convexDistance_recursion` — the key lemma (total, handles empty sections) | Hard |
| E. Main Theorem | Coordinate induction, Hölder, scalar optimization, assembly | Hard |
| F. Tail Corollaries | Markov step, half-measure, neg, two-sided variants | Easy |

## Proof Approach

The proof follows the standard coordinate induction on `n` (base `n = 0`; step via
`Fin.snocEquiv : Ω × (Fin n → Ω) ≃ (Fin (n+1) → Ω)`). The survey [C_proof_strategy](survey/C_proof_strategy.md)
identifies 24 new lemmas in a 10-step decomposition, with 3 Hard points:

### 1. The Geometric Recursion (Step 4 — Hard)

The heart of the proof: for `A ⊆ Fin (n+1) → Ω`, projection `B := {y | ∃ ω', Fin.snoc y ω' ∈ A}`,
section `A_ω := {y | Fin.snoc y ω ∈ A}`, and `λ ∈ [0,1]`:

```
convexDistance A (Fin.snoc x ω)² ≤ (1−λ)·convexDistance B x² + λ·convexDistance A_ω x² + (1−λ)²
```

Proved by taking ε-approximate minimizers `y₁ ∈ A_{ω'}` and `y₂ ∈ A_ω`, forming the convex
combination `(1−λ)·v₁ + λ·v₂` in `convexMismatchSet A (x,ω)`, using convexity of `‖·‖²` and
the 0/1 structure of mismatch vectors. Empty sections handled by `infDist_empty = 0`.

Prerequisite lemma (must be created — not in mathlib): **`convexOn_norm_sq`** — proved from the
parallelogram law: `‖(1−λ)a + λb‖² = (1−λ)‖a‖² + λ‖b‖² − λ(1−λ)‖a−b‖² ≤ (1−λ)‖a‖² + λ‖b‖²`.

### 2. The Scalar Optimization (Step 7 — Easy for two-valued Ω)

With per-branch `λ_ω ∈ {0,1}` choices, the two-factor inequality becomes:

```
(θ·u₀ + (1−θ)·u₁) · (θ·e^{c}·u₀^{−1} + (1−θ)·e^{c·(1−λ)²}·u₁^{−λ}·r^{λ}) ≤ 1
```

For two-valued coordinates, `λ₀, λ₁ ∈ {0,1}` gives a purely arithmetic proof with `c ≤ log 2` ≈ 0.693,
so `c = 1/4` has large slack. **No Taylor expansions, no derivatives required.** This is a new
observation relative to the ±1-cube formulation (which forces `λ₀ = λ₁` and needs calculus).

### 3. Induction Assembly (Step 8 — Hard)

The measure transport under `Fin.snocEquiv` requires a new lemma **`measure_pi_snoc`** — the
`Measure.pi` sum-type decomposition `Measure.pi (Sum.elim ν η) = ν.prod η` is not in mathlib v4.32.0,
but can be proved via `Measure.pi_eq` or `pi_pi`, following the pattern of StatsMLlib's
`pi_map_eval` in `Probability/Independence/FinsetPi.lean`.

### Full Dependency Graph

See [C_proof_strategy §5](survey/C_proof_strategy.md) for the complete 23-node dependency graph.

## Relevant Existing Modules

### Mathlib (all present in v4.32.0)

| Module | Provides |
|--------|----------|
| `Analysis.InnerProductSpace.PiL2` | `EuclideanSpace`, `finAddEquivProd`, `dist_sq_eq_of_L2` |
| `Analysis.Convex.Hull` | `convexHull`, `convex_convexHull`, `subset_convexHull` |
| `Analysis.Convex.Combination` | `Finset.mem_convexHull'` (finite-set weight characterization) |
| `Analysis.Convex.Topology` | `Set.Finite.isCompact_convexHull`, `isClosed_convexHull` |
| `Analysis.Convex.Integral` | Jensen: `ConvexOn.map_integral_le` |
| `Topology.MetricSpace.HausdorffDistance` | `Metric.infDist`, `infDist_nonneg`, `infDist_le_dist_of_mem`, `IsCompact.exists_infDist_eq_dist` |
| `MeasureTheory.Constructions.Pi` | `Measure.pi`, `pi.instIsProbabilityMeasure`, `pi_pi` |
| `MeasureTheory.Integral.Prod` | `integral_prod` (Fubini) |
| `MeasureTheory.Integral.Pi` | `integral_fintype_prod_eq_prod` |
| `MeasureTheory.Integral.MeanInequalities` | Hölder: `integral_mul_le_Lp_mul_Lq` |
| `MeasureTheory.Integral.Lebesgue.Markov` | `mul_meas_ge_le_lintegral₀` (Markov) |
| `Probability.Independence.Basic` | `iIndepFun`, `iIndepFun_pi` |
| `Probability.Independence.Integration` | `iIndepFun.integral_prod_eq_prod_integral` |
| `Logic.Equiv.Fin.Basic` | `Fin.snocEquiv`, `Fin.castSucc`, `Fin.last` |

A detailed audit of all 8 API areas (EuclideanSpace, convexHull, infDist, Measure.pi, iIndepFun,
Fin, key inequalities, discrete measurable spaces) with exact theorem names and line numbers is in
[B_mathlib_api](survey/B_mathlib_api.md).

### StatsMLlib (optional — none strictly required)

| Module | Potential Use |
|--------|---------------|
| `Probability.Independence.FinsetPi` | `pi_map_eval`, `pi_eval_iIndepFun` — proof patterns for the `measure_pi_snoc` lemma |
| `Probability.Concentration.Chernoff` | Pattern reference for exponential-moment → tail via Markov |

The survey [A_existing_infrastructure](survey/A_existing_infrastructure.md) confirmed: `convexHull`
and `Metric.infDist` appear **zero times** in the entire StatsMLlib source tree — all geometry here
is new to the library. The LSI machinery, cgf→tail pipeline, product-measure independence, and
covering numbers infrastructure are all production-quality and available, but none are needed
for the coordinate-induction proof.

## Missing Infrastructure (Must Be Created)

All 24 new declarations live in the proposed file. The critical new pieces:

1. **`convexOn_norm_sq`** — squared Euclidean norm is convex (parallelogram law proof). Not in mathlib v4.32.0.
2. **`convexDistance_recursion`** — the key geometric lemma (Hard, ~150–300 lines). The single most important declaration.
3. **`measure_pi_snoc`** — `Measure.pi` decomposition under `Fin.snocEquiv`. Not in mathlib v4.32.0 (~50–100 lines).
4. **`exp_holder`** — Hölder wrapper for exponentials with `Real.rpow` exponents (~30–50 lines).
5. **`talagrand_convexDistance`** — the main theorem (Hard, ~200–400 lines of induction assembly).

See [C_proof_strategy §Summary](survey/C_proof_strategy.md) for the numbered list with difficulty ratings.

## Code Conventions

The survey [D_code_patterns](survey/D_code_patterns.md) provides a complete template. Key conventions:

- **Header:** `Copyright (c) 2026 Yuanhe Zhang` / `Authors: Yuanhe Zhang, ...` with module docstring
  `# Talagrand's Convex-Distance Inequality` including `## Main definitions`, `## Main results`,
  `## References` (Talagrand 1995, Ledoux "Four Talagrand Inequalities", BLM)
- **Namespace:** Top-level (namespace-free), matching McDiarmid's pattern — theorems named
  `talagrand_convexDistance`, `talagrand_convexDistance_tail`, etc.
- **Tail probability idiom:** `(μ {ω | ... ≥ ε}).toReal ≤ exp(-2*ε²*t)` — ENNReal coerced to ℝ
- **Product measure notation:** `μs : Fin n → Measure Ω` with `Measure.pi μs` (EfronStein pattern)
- **Hypothesis naming:** `hA` (nonempty), `hμ` (probability), `hX` (measurability), `hε` (tail ≥ 0)
- **Strict linters:** No `#`-commands, no `λ` (use `fun`), no `$`, bullets must be `·`, lines ≤ 100,
  `autoImplicit := false`, `pp.unicode.fun := true` (arrow notation)

## API Questions for Maintainers

1. **Two-valued coordinates only for the first contribution — acceptable?** The scalar step for
   general finite `Ω` requires a non-trivial analytic lemma (`(E U)(E U⁻¹·Φ(U)) ≤ 1`) or a
   splitting/atomization reduction; both are ~2+ weeks of research-level work. Two-valued
   coordinates (uniform Bernoulli or biased coin) cover the classical applications and make the
   scalar step a purely arithmetic case-split.

2. **`Fin n` vs `Fintype ι` as the primary index type?** The induction proof works on `Fin n`;
   `Fintype ι` can be added as a thin post-hoc wrapper (exactly as `mcdiarmid_inequality_pos`
   wraps `mcdiarmid_inequality_aux` via `Fintype.equivFinOfCardEq`). Recommend `Fin n` first.

3. **Single `ConvexDistance.lean` file vs `ConvexDistance/Defs.lean` + `Inequality.lean`?**
   Recommend one file initially (consistent with HansonWright at 207 KB staying one file).
   Promotion trigger: >~150 KB or first applications PR.

4. **Should `convexDistance` range in ℝ or ℝ≥0?** Recommend ℝ for simplicity of squared/tail
   statements; nonnegativity is a lemma (`convexDistance_nonneg`).

5. **Should the primary theorem be the exponential-integrability form, the tail form, or both?**
   The exponential-integrability form is the mathematical heart and the cleanest statement.
   Include 5 tail corollaries (`_pos`, `_half`, `_neg`, `_two_sided`) as in McDiarmid.

## Future Extensions (Out of Scope for Initial PR)

| Extension | Difficulty | Notes |
|-----------|------------|-------|
| `Fin n` → `Fintype ι` wrapper | Easy | Thin transport via `Fintype.equivFinOfCardEq` (McDiarmid pattern) |
| Two-valued → biased two-valued | Medium | One-variable calculus for `Φ(u)` |
| Two-valued → general finite `Ω` | Hard | Splitting reduction or new two-factor analytic lemma |
| Finite discrete → Polish `Ω` | Hard | Projection measurability, infDist attainment in general spaces |
| Weighted-Hamming dual formulation | Medium | New corollary using `convexDistance` API |
| Convex-Lipschitz concentration | Medium | Corollary: `P(|f(X) − M f| ≥ t) ≤ 2 exp(−t²/4L²)` for convex L-Lipschitz `f` |
| Talagrand's T₂ transport inequality | Hard | Different technique (couplings); independent module |
| Bousquet-Talagrand empirical-process inequality | Hard | New `LearningTheory/EmpiricalProcess/Talagrand.lean` importing from Probability |

All future extensions are additive and none require refactoring the initial file. The architectural
survey [E_scope_and_files §5](survey/E_scope_and_files.md) details each path.

## References

- Michel Talagrand, *Concentration of Measure and Isoperimetric Inequalities in Product Spaces*,
  Publications Mathématiques de l'IHÉS, 1995.
- Michel Ledoux, *Four Talagrand Inequalities under the Same Umbrella*, 2015.
- Michel Ledoux, *The Concentration of Measure Phenomenon*, AMS, 2001.
- Stéphane Boucheron, Gábor Lugosi, and Pascal Massart, *Concentration Inequalities: A
  Nonasymptotic Theory of Independence*, Oxford, 2013.
- Terry Tao, *Talagrand's concentration inequality*, blog post, 2009.
  https://terrytao.wordpress.com/2009/06/09/talagrands-concentration-inequality/

---

## Survey Reports

Detailed research reports supporting this proposal are in the `survey/` directory:

| File | Content |
|------|---------|
| [PLAN.md](survey/PLAN.md) | Survey plan and checklist |
| [A_existing_infrastructure.md](survey/A_existing_infrastructure.md) | Audit of all 89 StatsMLlib modules: what's available, what's missing |
| [B_mathlib_api.md](survey/B_mathlib_api.md) | Deep dive into 8 mathlib API areas with exact theorem names and locations |
| [C_proof_strategy.md](survey/C_proof_strategy.md) | 10-step proof decomposition, 24-lemma dependency graph, risk assessment |
| [D_code_patterns.md](survey/D_code_patterns.md) | File header format, naming conventions, proof patterns, linter constraints |
| [E_scope_and_files.md](survey/E_scope_and_files.md) | File location, import analysis, downstream consumers, future extensions |
