# Proposal: Talagrand's Convex-Distance Inequality

## Motivation

StatsMLlib has Hoeffding, McDiarmid, Efron–Stein, and Gaussian Lipschitz concentration — but no
convexity-aware concentration. Talagrand's inequality gives Gaussian-type $\exp(-t^2/4)$ tails for
*any* set $A$ in a product space. McDiarmid (bounded differences) only gives $\exp(-t^2/n)$ for
generic sets — Talagrand recovers the dimension-free rate. Downstream applications include
convex-Lipschitz functions, Rademacher processes, and uniform deviation bounds.

## The Theorem

**Setup.** Let $(\Omega_i, \mu_i)_{i=1}^n$ be finite probability spaces (coordinates may differ).
Take $\Omega = \prod_{i=1}^n \Omega_i$ with product measure $\mu = \bigotimes_i \mu_i$.

**Convex distance.** Identify each point with its disagreement pattern. For $x, y \in \Omega$,
the *mismatch vector* $v(x,y) \in \mathbb{R}^n$ is

$$v(x,y)_i = \begin{cases} 0 & x_i = y_i \\ 1 & x_i \neq y_i \end{cases}$$

For $A \subseteq \Omega$, $x \in \Omega$, define

$$d_A(x) = \mathrm{dist}\!\big(0,\; \mathrm{conv}\{v(x,y) : y \in A\}\big)$$

the Euclidean distance from the origin to the convex hull of mismatch vectors from $x$ to $A$.

**Main inequality.**

$$\mu(A) \cdot \int_\Omega \exp\!\left(\frac{d_A(x)^2}{4}\right) d\mu(x) \;\leq\; 1$$

**Tail bound** (via Markov). For $t \geq 0$,

$$\mu(A) \cdot \mu(\{x : d_A(x) \geq t\}) \;\leq\; \exp\!\left(-\frac{t^2}{4}\right)$$

When $\mu(A) \geq 1/2$, this simplifies to $\mu(\{x : d_A(x) \geq t\}) \leq 2\exp(-t^2/4)$.

## Scope

| Choice | Rationale |
|--------|-----------|
| Two-valued $\Omega_i$ (initial) | Scalar optimization becomes a 10-line case split ($\lambda \in \{0,1\}$, $nlinarith$). General finite $\Omega$ deferred. |
| $\mathrm{Fin}\;n$ as index | Induction-friendly. $[\mathrm{Fintype}\;\iota]$ wrapper deferred (same pattern as McDiarmid). |
| Heterogeneous marginals | Allowed (matching EfronStein's `μs : Fin n → Measure Ω` pattern). |

## Proof Strategy

Induction on $n$. Base $n = 0$: trivial.

**Inductive step.** Decompose $\prod_{i=1}^{n+1} \Omega_i \simeq \bigl(\prod_{i=1}^n \Omega_i\bigr) \times \Omega_{n+1}$.
For $A \subseteq \prod_{i=1}^{n+1} \Omega_i$, define projection $B = \{x : \exists\omega,\;(x,\omega) \in A\}$
and sections $A_\omega = \{x : (x,\omega) \in A\}$.

**Key geometric lemma** (the heart):

$$d_A(x,\omega)^2 \;\leq\; (1-\lambda)\,d_B(x)^2 \;+\; \lambda\,d_{A_\omega}(x)^2 \;+\; (1-\lambda)^2 \qquad (\lambda \in [0,1])$$

This uses convexity of $\|\cdot\|^2$ (via `parallelogram_law_with_norm`), the 0/1 structure of
mismatch vectors, and the convex hull of the section images. Empty sections handled separately.

**Analytic assembly:** Exponentiate, apply Hölder to separate the $d_B^2$ and $d_{A_\omega}^2$ terms,
invoke the induction hypothesis for $B$ and each $A_\omega$, integrate over $\omega$ via Fubini,
and optimize $\lambda$. For two-valued coordinates, $\lambda_\omega \in \{0,1\}$ works directly
($e^{1/4} \leq 2$, i.e. $1/4 \leq \log 2 \approx 0.693$, so the constant $1/4$ has large slack).

## What Exists vs. What's New

### Already in mathlib v4.32.0 (adequate)

- `EuclideanSpace ℝ (Fin n)` + `dist_sq_eq_of_L2`, `finAddEquivProd`
- `convexHull ℝ`, `convex_convexHull`, `Set.Finite.isCompact_convexHull`
- `Metric.infDist`, `infDist_nonneg`, `infDist_le_dist_of_mem`
- `Measure.pi`, `pi.instIsProbabilityMeasure`
- `iIndepFun`, `iIndepFun_pi` (unused for the induction proof but available)
- `parallelogram_law_with_norm` — gives convexity of $\|\cdot\|^2$ in 3 lines
- `finSuccEquivLast : Fin (n+1) ≃ Option (Fin n)` — for the measure decomposition
- `pi_map_piOptionEquivProd` — decomposes `Measure.pi` over `Option` into a binary product
- `measurePreserving_piCongrLeft` — reindexes product measures under any equiv
- Hölder (`integral_mul_le_Lp_mul_Lq`), Fubini (`integral_prod`), Markov
- `Real.exp`, `Real.rpow`, `nlinarith`

**Note.** `convexHull` and `Metric.infDist` appear zero times in the current 89-module StatsMLlib
source — all geometry here is net-new, but the mathlib APIs are adequate.

### Must be created

| Item | Kind | Effort |
|------|------|--------|
| `mismatchVector`, `convexMismatchSet`, `convexDistance` | `def` ×3 | Trivial |
| Basic properties (~10 lemmas: nonneg, zero-of-mem, monotone, $\leq\sqrt{n}$, Lipschitz, snoc decomposition, …) | `lemma` | Easy (1–5 lines each) |
| **`convexDistance_recursion`** — key geometric lemma | `lemma` | **Hard** (~100–200 lines) |
| Scalar optimization (two-valued case, case split + `nlinarith`) | `lemma` | Easy |
| **`talagrand_convexDistance`** — main theorem, induction assembly | `theorem` | **Hard** (~100–200 lines) |
| `_tail`, `_tail_half`, `_tail_neg`, `_two_sided` | `theorem` ×4 | Trivial (3–5 lines each) |

Total estimate: ~800–1200 lines of Lean, with the two Hard lemmas accounting for ~60% of the work.

### Things previously thought missing but actually present

- **`convexOn_norm_sq`.** Not needed as a separate lemma. The specific bound
  $\|(1-\lambda)a + \lambda b\|^2 \le (1-\lambda)\|a\|^2 + \lambda\|b\|^2$ follows in 3 lines
  from `parallelogram_law_with_norm` (`Analysis/InnerProductSpace/Basic.lean:493`).
- **`measure_pi_snoc`.** The building blocks (`finSuccEquivLast`, `measurePreserving_piCongrLeft`,
  `pi_map_piOptionEquivProd`, `integral_prod`) all exist. Assembling them for the `Fin` case is
  a routine 10–15 line proof, not a missing lemma.
- **`exp_holder`.** Direct 3-line application of `integral_mul_le_Lp_mul_Lq` with conjugate
  exponents $1/a$ and $1/b$. Not a gap.

## Proposed File

`StatsMLlib/Probability/Concentration/ConvexDistance.lean` — single file, consistent with every
named inequality in the repo (HansonWright is 207 KB in one file).

## Questions for Maintainers

1. Two-valued coordinates only as initial scope — acceptable?
2. `Fin n` as primary index type (with `Fintype ι` wrapper deferred)?
3. Single file OK?

## References

- M. Talagrand, *Concentration of Measure and Isoperimetric Inequalities in Product Spaces*, IHÉS, 1995.
- M. Ledoux, *Four Talagrand Inequalities under the Same Umbrella*, 2015.
- S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*, Oxford, 2013.
- T. Tao, *Talagrand's concentration inequality*, blog post, 2009.
