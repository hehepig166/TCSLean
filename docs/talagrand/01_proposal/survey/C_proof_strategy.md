# C. Proof Strategy & Gap Analysis

**Scope note.** This survey assumes mathlib `v4.32.0` (pinned by `StatsMLlib/lakefile.lean`) and the finite-discrete scope: coordinates `Fin n`, values in a finite `Ω`, coordinate measures `μs : Fin n → Measure Ω`, product measure `μ = Measure.pi μs`, target constant `c = 1/4` (exponent `d²/4`).

**Key finding:** In the 0/1-mismatch formulation, the parameter optimization step is much easier than in Tao's blog writeup. Tao's calculus-heavy optimization is an artifact of (a) the ±1 cube convention (last-coordinate constant `4λ²` instead of `(1−λ)²`) and (b) his forcing a single `λ` for both coordinate branches by symmetry. In the 0/1 version, `λ` may be chosen *independently per value of the last coordinate*, and the two-point scalar step reduces to a case split with `λ ∈ {0, 1}` and no calculus at all. The genuinely hard scalar problem only appears when `Ω` has more than two atoms.

---

## 1. Proof Step Decomposition

Notation: `mismatchVector x y : EuclideanSpace ℝ (Fin n)` with `(mismatchVector x y) i = if x i = y i then 0 else 1`; `convexMismatchSet A x := convexHull ℝ (mismatchVector x '' A)`; `convexDistance A x := Metric.infDist 0 (convexMismatchSet A x)`.

### Step 1 — Definitions and elementary API for `mismatchVector`
- **Statement.** `mismatchVector x x = 0`; `mismatchVector x y = 0 ↔ x = y`; `‖mismatchVector x y‖² ≤ Fintype.card ι`; pointwise `0/1` bounds; snoc decomposition `mismatchVector (Fin.snoc x ω) (Fin.snoc y ω') = (mismatchVector x y, if ω = ω' then 0 else 1)` in `EuclideanSpace ℝ (Fin (n+1)) ≃L EuclideanSpace ℝ (Fin n) × ℝ`.
- **New.** All declarations; none is hard.
- **Difficulty: Easy** (~100 lines).

### Step 2 — Basic properties of `convexDistance`
- **Statement.** `0 ≤ convexDistance A x`; `x ∈ A → convexDistance A x = 0`; `A ⊆ B → convexDistance B x ≤ convexDistance A x` (anti-monotone); `convexDistance A x ≤ sqrt n`; `convexDistance A (x,ω) ≤ convexDistance A_ω x` (trivial section bound); 1-Lipschitzness.
- **New.** `convexMismatchSet`, `convexDistance`, plus ~10 property lemmas.
- **Reuse.** `Metric.infDist` API, `convexHull` API.
- **Difficulty: Easy–Medium** (~200 lines).

### Step 3 — Minimizer / ε-approximation infrastructure
- **Statement.** For nonempty `A_ω`, `B` (finite sets): `∃ y ∈ A_ω, ‖mismatchVector x y‖² ≤ convexDistance A_ω x² + ε`.
- **New.** `exists_mismatch_approx_of_nonempty`.
- **Reuse.** `Set.Finite.isCompact_convexHull`, `infDist_lt_iff`.
- **Difficulty: Easy–Medium.** Recommend the ε-route (no `ProperSpace`/minimizer machinery needed).

### Step 4 — The key geometric recursion (the heart)
- **Statement.** For `A : Set (Fin (n+1) → Ω)`, `x : Fin n → Ω`, `ω : Ω`, projection `B := {y | ∃ ω', Fin.snoc y ω' ∈ A}`, section `Aω := {y | Fin.snoc y ω ∈ A}`:
  `convexDistance A (Fin.snoc x ω)² ≤ (1−λ)·convexDistance B x² + λ·convexDistance Aω x² + (1−λ)²` for all `λ ∈ [0,1]`.
- **New.** `convexDistance_recursion` — the single most important lemma (~150–300 lines).
- **Prerequisite.** `convexOn_norm_sq` (parallelogram law proof: `‖(1−λ)a + λb‖² = (1−λ)‖a‖² + λ‖b‖² − λ(1−λ)‖a−b‖² ≤ (1−λ)‖a‖² + λ‖b‖²`).
- **Difficulty: Hard.** Self-contained but requires careful case analysis on empty vs nonempty sections.

### Step 5 — Product decomposition and transport for `Fin (n+1)`
- **Statement.** `(Fin (n+1) → Ω) ≃ Ω × (Fin n → Ω)` via `Fin.snocEquiv`; measure identity + norm identity under `finAddEquivProd`.
- **New.** `measure_pi_snoc` (Medium — `Measure.pi` sum-split lemma not in mathlib v4.32), `convexDistance_congr_snocEquiv` (Easy).
- **Reuse.** `Fin.snocEquiv`, `EuclideanSpace.finAddEquivProd`, `measurePreserving_piCongrLeft`, `integral_prod`.
- **Difficulty: Medium–Hard** (index bookkeeping; `Measure.pi` sum-type decomposition must be proved).

### Step 6 — Exponentiation and Hölder
- **Statement.** `∫ x, exp (a·f x + b·g x) ∂ν ≤ (∫ x, exp (f x) ∂ν)^a · (∫ x, exp (g x) ∂ν)^b` for `a+b=1`.
- **New.** `exp_holder` wrapper.
- **Reuse.** Hölder for integrals (`integral_mul_le_Lp_mul_Lq`), `Real.rpow` API.
- **Difficulty: Medium.** `rpow` of possibly-zero integrals needs care.

### Step 7 — The scalar optimization lemma
- **Statement.** For two-valued `Ω` with weights `(θ, 1−θ)`: `(∑_ω p_ω u_ω)·(∑_ω p_ω e^{c(1−λ_ω)²} u_ω^{−λ_ω}) ≤ 1` via `λ_ω ∈ {0,1}` choice.
- **Key finding:** For uniform two-point coordinates, `λ ∈ {0,1}` per branch gives a **purely arithmetic** proof (`c ≤ log 2`, large slack for `c=1/4`). No Taylor expansions, no derivatives needed. Biased two-point requires one-variable calculus (Medium). General finite `Ω` with ≥3 atoms is the genuinely hard case (requires splitting reduction or new analytic lemma).
- **Difficulty: Easy (uniform) / Medium (biased) / Hard (general Ω).**
- **Recommendation:** Scope first contribution to two-valued coordinates.

### Step 8 — Induction assembly
- **Statement.** `probReal μ A · ∫ x, exp (convexDistance A x² / 4) ∂μ ≤ 1`.
- **Structure.** Induction on `n`; base `n=0` trivial; step uses Steps 5–7.
- **New.** `talagrand_convexDistance_exponential` (Hard — long, bookkeeping-heavy).
- **Difficulty: Hard.** Not conceptually new after Steps 4–7, but Long.

### Step 9 — Tail via Markov
- **Statement.** `probReal μ A · probReal μ {x | t ≤ convexDistance A x} ≤ exp (−t²/4)`.
- **New.** `talagrand_convexDistance_tail`.
- **Difficulty: Easy.**

### Step 10 — Corollaries
- **Statement.** `probReal μ A ≥ 1/2` ⟹ `probReal μ {x | t ≤ d_A(x)} ≤ 2·exp(−t²/4)`.
- **New.** `talagrand_convexDistance_tail_half`.
- **Difficulty: Easy.**

---

## 2. Key Geometric Lemma Deep Dive

The recursion (Step 4) is the heart. The standard derivation adapted to 0/1 mismatch:

**Case 1 (`∃ z ∈ A, z.2 ≠ ω`):** Pick `y₁ ∈ A_{ω'}`, `y₂ ∈ A_ω` via Step 3 ε-approximation. Both `v₁ := mismatchVector (x,ω) (y₁,ω')` and `v₂ := mismatchVector (x,ω) (y₂,ω)` are in `mismatchVector (x,ω) '' A`. Since `convexHull` is convex, `w := (1−λ)·v₁ + λ·v₂ ∈ convexMismatchSet A (x,ω)`. Then:
- `d_A(x,ω) ≤ ‖w‖` by `infDist_le_dist_of_mem`;
- `‖w‖² = ‖(1−λ)·v₁[:n] + λ·v₂[:n]‖² + (1−λ)²` (last coordinate: `v₁` has 1, `v₂` has 0);
- convexity of `‖·‖²` → `≤ (1−λ)‖v₁[:n]‖² + λ‖v₂[:n]‖² + (1−λ)²`;
- `d_{A_{ω'}}(x) ≤ d_B(x)` (since `A_{ω'} ⊆ B`);
- ε → 0 via `le_of_forall_pos_le_add`.

**Case 2 (`∀ z ∈ A, z.2 = ω`):** Then `B = A_ω` and `d_A(x,ω) = d_{A_ω}(x)`. RHS = `(1−λ)d_{A_ω}² + λd_{A_ω}² + (1−λ)² ≥ d_{A_ω}² =` LHS.

**What the lemma needs:** (1) `convexOn_norm_sq` (must create; use parallelogram law), (2) `mismatchVector_snoc` decomposition lemma, (3) `infDist` anti-monotonicity, (4) case analysis on sections. Self-contained but delicate. Difficulty: Hard.

## 3. Induction Structure

- **Base case `n = 0`:** `Fin 0 → Ω` is a singleton, `convexDistance A x = 0`, trivial.
- **Inductive step:** `Fin (n+1) → Ω` decomposes via `Fin.snocEquiv` (append at end, consistent with `finAddEquivProd`).
- **Measure transport:** `Measure.map (Fin.snocEquiv ...).symm (Measure.pi μs) = (μs (Fin.last n)).prod (Measure.pi (μs ∘ Fin.castSucc))`. Needs new `Measure.pi` sum-type split lemma (not in mathlib v4.32).
- **IH application:** Twice per `ω` — for `B` (projection) and `A_ω` (section), both with `μs ∘ Fin.castSucc`.
- **Statement hygiene:** Multiplication form `probReal μ A * ∫ ... ≤ 1` avoids division by zero.

Difficulty: Hard (assembly), decomposed into: base Easy, transport Medium, IH plumbing Easy, summation Medium.

## 4. Parameter Optimization

**For uniform two-point coordinates:** `λ ∈ {0,1}` per branch gives a purely arithmetic proof with `c ≤ log 2` ≈ 0.693, so `c = 1/4` has large slack. No calculus needed. Easy.

**For biased two-point:** One-variable calculus (`HasDerivAt`, `ConvexOn`). Medium.

**For general finite Ω:** Requires either a splitting/atomization reduction or a new two-factor analytic inequality `(E U)(E U^{−1}·Φ(U)) ≤ 1`. Hard / research-level. **Defer to follow-up PR.**

## 5. Dependency Graph

```
L1 mismatchVector (NEW, E)
├─ L2 mismatchVector_snoc (NEW, E)
├─ L3 norm_sq_mismatchVector_le (NEW, E)
└─ L4 mismatchVector_eq_zero_iff (NEW, E)

L5 convexMismatchSet (NEW, E)
└─ L6 convexDistance (NEW, E)
    ├─ L7-13: basic properties (NEW, E–M)
    └─ L14 exists_mismatch_approx (NEW, M)

L15 convexOn_norm_sq (NEW, M)
L16 convexDistance_recursion (NEW, HARD) ← L2, L11, L12, L14, L15
L17 product_transport (NEW, M–H) ← Fin.snocEquiv, finAddEquivProd, Measure.pi
L18 exp_holder (NEW, M)
L19 convexDistance_exp_section (NEW, M) ← L16, L18
L20 scalar_two_point (NEW, E–M)
L21 talagrand_convexDistance_exponential (NEW, HARD) ← L17, L19, L20
L22 talagrand_convexDistance_tail (NEW, E) ← L21
L23 corollaries (NEW, E) ← L22
```

## 6. Critical Path & Risk Assessment

| Risk | Difficulty | Mitigation |
|------|-----------|------------|
| General-Ω scalar lemma | Hard / research | Cut to two-valued coordinates only |
| Geometric recursion (Step 4) | Hard | Self-contained; ~3–5 days |
| Induction assembly (Step 8) | Hard | Bookkeeping-heavy; ~1 week; prove `L17a` early |
| Hölder wrapper (Step 6) | Medium | Work in `ℝ≥0∞` if `rpow` gets painful |
| `Measure.pi` sum-split (L17a) | Medium | Prove early as standalone lemma |
| Everything else (Steps 1–3, 5, 9–10) | Easy–Medium | Routine |

**Effort estimate:**
- Two-valued coordinates (uniform): ~1500–2500 lines, 2–3 weeks
- Two-valued coordinates (biased): +200–400 lines, +1 week
- General finite Ω (splitting route): +500–1000 lines, +2+ weeks, real research risk

---

## Summary: New Lemmas Required

1. `mismatchVector` + `mismatchVector_apply` — **Easy**
2. `mismatchVector_self`, `mismatchVector_eq_zero_iff` — **Easy**
3. `norm_sq_mismatchVector_le` — **Easy**
4. `mismatchVector_snoc` — **Easy**
5. `convexMismatchSet` (definition) — **Easy**
6. `convexDistance` + `_nonneg`/`_zero_of_mem` — **Easy**
7. `convexDistance_le_of_subset` — **Easy**
8. `convexDistance_le_sqrt_card` — **Easy**
9. `convexDistance_le_trivial_section` — **Easy**
10. `convexDistance_eq_section` — **Medium**
11. `convexDistance_lipschitz` — **Easy**
12. `exists_mismatch_approx` — **Medium**
13. `convexOn_norm_sq` — **Medium**
14. **`convexDistance_recursion`** — **Hard**
15. `measure_pi_snoc` — **Medium**
16. `convexDistance_congr_snoc` + `norm_sq_prod_finAdd` — **Easy**
17. `exp_holder` — **Medium**
18. `convexDistance_exp_section` — **Medium**
19. `talagrand_scalar_two_point_uniform` — **Easy**
20. `talagrand_scalar_two_point_biased` — **Medium** (if biased in scope)
21. `talagrand_scalar_finite` — **Hard / research-level** (defer)
22. **`talagrand_convexDistance_exponential`** — **Hard**
23. `talagrand_convexDistance_tail` — **Easy**
24. `talagrand_convexDistance_tail_half` — **Easy**
