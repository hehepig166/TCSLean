# TCSLean

Formalizations of theoretical computer science results in [Lean 4](https://lean-lang.org/),
built on [mathlib](https://github.com/leanprover-community/mathlib4) (pinned to v4.32.0).

## Formalized content

| # | Formalization | Modules | References | Status |
|---|---|---|---|---|
| 1 | Talagrand's convex-distance concentration inequality | [`TCSLean.Talagrand`](TCSLean/Talagrand) | [Wikipedia](https://en.wikipedia.org/wiki/Talagrand%27s_concentration_inequality) · Talagrand 1995 (IHÉS) · [Pollard, arXiv:math/0611770](https://arxiv.org/abs/math/0611770) · [Tao's notes](https://terrytao.wordpress.com/2009/06/09/talagrands-concentration-inequality/) | ✅ complete (2026-08-14) |
| 2 | Lovász local lemma | [`TCSLean.LovaszLocal`](TCSLean/LovaszLocal) | [Wikipedia](https://en.wikipedia.org/wiki/Lov%C3%A1sz_local_lemma) · Erdős–Lovász 1975 · Alon–Spencer ch. 5 | ✅ complete (2026-08-16) |
| 3 | Moser–Tardos algorithmic Lovász local lemma | [`TCSLean.MoserTardos`](TCSLean/MoserTardos) | [Wikipedia](https://en.wikipedia.org/wiki/Algorithmic_Lov%C3%A1sz_local_lemma) · [Moser & Tardos, arXiv:0903.0544](https://arxiv.org/abs/0903.0544) | ✅ complete (2026-08-18) |

Each section below follows a fixed template — **Modules / Main theorems / Development
record** — so new formalizations can be appended in the same shape.

---

## 1. Talagrand's convex-distance concentration inequality

**Modules:** `TCSLean.Talagrand.TalagrandInequality` (~2,540 lines, namespace
`TCSLean.Talagrand`)

Convex-distance concentration on finite discrete product probability spaces (Talagrand's
original theorem; Pollard 2006 presentation). Hypotheses elided below — the full statements
live in the module docstring.

```lean
-- the main exponential-moment inequality: μ(A) · ∫ exp(d_A(x)² / 4) ≤ 1
theorem talagrand_convexDistance {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, Fintype (Ω i)] … (A : Set ((i : Fin n) → Ω i))
    (hA : A.Nonempty) :
    (Measure.pi μ A).toReal * (∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ)) ≤ 1

-- tail bounds
theorem talagrand_convexDistance_tail … (ht : 0 ≤ t) :
    (Measure.pi μ A).toReal * (Measure.pi μ {x | t ≤ convexDistance x A}).toReal ≤ Real.exp (-(t ^ 2) / 4)

theorem talagrand_convexDistance_tail_half … (h_half : 1 / 2 ≤ (Measure.pi μ A).toReal)
    (ht : 0 ≤ t) : (Measure.pi μ {x | t ≤ convexDistance x A}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4)

theorem talagrand_convexDistance_integral_le_one_div … (hμ : 0 < (Measure.pi μ A).toReal) :
    ∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ) ≤ 1 / (Measure.pi μ A).toReal

theorem talagrand_convexDistance_two_sided …  -- set-level two-sided interface

-- the classical dual form (bridge theorem): D(x, A) = sup_{w ≥ 0, ‖w‖ ≤ 1} inf_{y ∈ A} Σᵢ wᵢ·1[xᵢ ≠ yᵢ]
theorem convexDistance_eq_dual {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    [∀ i, Fintype (Ω i)] (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i))
    (hA : A.Nonempty) :
    convexDistance x A = sSup {r | ∃ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧ r = ⨅ y : A, w ⬝ᵥ mismatchVector x y}
```

**Development record:** [`docs/talagrand/`](docs/talagrand) — proposal, surveys, blueprint
(15 items, all done), GPT review, PR description.

---

## 2. Lovász local lemma

**Modules:** `TCSLean.LovaszLocal.LovaszLocal` (786 lines, namespace `TCSLean.LovaszLocal`)

The Lovász local lemma (Alon–Spencer ch. 5): asymmetric and symmetric forms, the
existence witness, and the conditional-probability form, over an arbitrary
`[Fintype ι] [DecidableEq ι]` dependency-graph setting.

```lean
-- the asymmetric LLL
theorem lovaszLocalLemma (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {G : SimpleGraph ι} [DecidableRel G.Adj] (hdg : IsDependencyGraph (μ := μ) G A)
    {x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∀ i, x i < 1)
    (hLLL : ∀ i, μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))) :
    ENNReal.ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)

-- the existence form: some point avoids every bad event
theorem lovaszLocalLemma_exists … (hLLL : ∀ i, …) : ∃ ω, ∀ i, ω ∉ A i

-- symmetric forms
theorem lovaszLocalLemma_symmetric_optimalWeight …   -- (d + 1)^(d + 1) · p ≤ d^d
theorem lovaszLocalLemma_symmetric … (hcond : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
    0 < μ (⋂ i, (A i)ᶜ)                              -- e · p · (d + 1) ≤ 1
theorem lovaszLocalLemma_4pd … (hcond : 4 * p * (d : ℝ) ≤ 1) :
    0 < μ (⋂ i, (A i)ᶜ)                              -- 4 · p · d ≤ 1

-- the conditional-probability form of the key lemma
theorem lovaszLocalLemma_cond … : μ[(A i) | bset A S] ≤ ENNReal.ofReal (x i)

-- dependency-graph bridge: avoidance-event formulation ⇔ generated-σ-algebra formulation
theorem isDependencyGraph_iff_strong {G : SimpleGraph ι} {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) : IsDependencyGraph (μ := μ) G A ↔ IsDependencyGraphStrong (μ := μ) G A
```

**Development record:** [`docs/lovasz/`](docs/lovasz) — proposal, surveys, blueprint
(21 items, all done), GPT reviews, PR description.

---

## 3. Moser–Tardos algorithmic Lovász local lemma

**Modules:** `TCSLean.MoserTardos` — 7 modules, ~10,200 lines: `VariableModel`
(overlap graph, truncated resampling table), `Algorithm` (resampling run, stopping
time, measurability), `WitnessTree`, `Coupling`, `GaltonWatson` (weight algebra),
`Basic` (canonical form, counting identity, main bound), `Symmetric`.

The algorithmic LLL (Moser & Tardos, arXiv:0903.0544, Thm 1.2): expected resampling
bounds and the constructive existence form, uniformly in the truncation `N`.

```lean
-- the main bound: E[# resamplings of i] ≤ x i / (1 - x i)
theorem moserTardos_bound {N : ℕ} … (i : ι) :
    ∫⁻ ω : ΩN N Ω, (countLog (log vbl A pick hpick) ω i : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (x i / (1 - x i))

-- total and tail
theorem moserTardos_total {N : ℕ} … :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))

theorem moserTardos_tail {N : ℕ} … :
    (N : ℝ≥0∞) * μN N μ {ω : ΩN N Ω | R vbl A pick hpick ω = N}
      ≤ ENNReal.ofReal (∑ i, x i / (1 - x i))

-- the constructive LLL (pick-free): some full assignment avoids every bad event
theorem moserTardos_exists … : ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i

-- symmetric form (e · p · (d + 1) ≤ 1)
theorem moserTardos_symmetric … (hcond : Real.exp 1 * p * (d + 1) ≤ 1) :
    ∃ σ : Π j, Ω j, ∀ i, σ ∉ A i

theorem moserTardos_symmetric_total {N : ℕ} … :
    ∫⁻ ω : ΩN N Ω, (R vbl A pick hpick ω : ℝ≥0∞) ∂ μN N μ
      ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / d)
```

**Development record:** [`docs/moser-tardos/`](docs/moser-tardos) — proposal, surveys,
blueprint (27 items, all done), full statement review with fixes, PR description.

---

## Repository layout

```
TCSLean/           Lean sources, one folder per formalization
docs/              development records: proposal → survey → blueprint → review → PR
lakefile.toml      mathlib v4.32.0; linter set aligned with the development configuration
TCSLean.lean       root module aggregating the imports
```

## Conventions for adding a new formalization

1. **Modules:** `TCSLean/<Topic>/` folder with declarations in `namespace TCSLean.<Topic>`
   (a dedicated module per layer, e.g. defs / algorithm / main theorems).
2. **Development record:** `docs/<topic>/` with `01_proposal/`, `02_blueprint/`,
   `03_gpt_review/`, `04_pr/` — the harness-driven proposal → survey → blueprint → proof
   → review loop.
3. **Catalogue:** append a numbered section to the table above following the fixed
   template (Modules / Main theorems / Development record), and update this
   conventions list if the process changes.
4. **Quality bar:** no `sorry`/`admit`/custom `axiom`; 0 warnings under the lakefile
   linters; main theorems stated with full hypotheses in their module docstrings.
