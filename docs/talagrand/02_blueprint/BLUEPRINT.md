# Blueprint: Talagrand's Convex-Distance Concentration Inequality

## Format

Each item has this structure. See the end of this section for the log column spec.

- **meta**
    - kind: <def|lemma|theorem>
    - priority: <1|2|3>          (1 = nice-to-have, 2 = important, 3 = critical path)
    - status: <pending|working|done>
    - attempts: <current> / <bucket>    (bucket default = 15)
    - file: `<Path/To/File.lean>`
- **informal**
    - statement: |
        <LaTeX or plain-English statement. For defs, describe what it defines.>
    - proof: |
        <Proof sketch. Bullet points or paragraph. Empty for defs.>
- **prep**
    - `<Lean.Declaration.Name>` — <brief description>
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|

Log columns:
- `Date`, `Att`, `Status`(initial=`working`), `Goal`, `Tmp` — written by Survey at attempt start.
- `Proof Feedback` — filled by Review from Proof subagent's report.
- `Review Feedback` — filled by Review (verification, integration decision, next-attempt guidance).
- `Status`(final) — updated by Review: `done` | `pending` | `stuck`.
- **Newest entries first.**

### Numbering

Hierarchical: `## 10. Group`, `### 10.1. item`, `#### 10.1.1. sub-item`. Gaps allowed for insertion.

Group ranges: `10`--`19` Definitions, `20`--`39` Basic properties, `40`--`59` Core lemmas,
`60`--`79` Main theorem, `80`--`99` Corollaries.

### Status Lifecycle

```
pending ---> working ---> done
  ^           |
  +-----------+  (retry)
```

`attempts = bucket / bucket` with status != `done` --> **blocked**, needs human intervention.

## Overview

Formalize Talagrand's convex-distance concentration inequality on finite discrete product
probability spaces. The theorem bounds the moment generating function of the convex distance
$d_A(x)$ from a point $x$ to a measurable set $A$ in a product space, yielding subgaussian
concentration.

**Setup:** Let $(\Omega_i, \mu_i)$ for $i=1,\dots,n$ be finite probability spaces, with each
$\Omega_i$ finite and discrete. Form the product $\Omega = \prod_{i=1}^n \Omega_i$ with product
measure $\mu = \bigotimes_{i=1}^n \mu_i$. The index set is $\mathrm{Fin}\;n$.

**Mismatch vector:** For $x,y \in \Omega$, define $v(x,y) \in \mathbb{R}^n$ (as
`EuclideanSpace \mathbb{R} (\mathrm{Fin}\;n)`) by
$$v(x,y)_i = \begin{cases} 0 & \text{if } x_i = y_i \\ 1 & \text{if } x_i \neq y_i \end{cases}$$

**Convex distance:** For $A \subseteq \Omega$, the convex distance from $x$ to $A$ is
$$d_A(x) = \inf\{\|z\| : z \in \mathrm{conv}\{v(x,y) : y \in A\}\}$$
where $\mathrm{conv}$ denotes the convex hull in $\mathbb{R}^n$ and $\|\cdot\|$ is the Euclidean norm.

**Main theorem:** $\mu(A) \cdot \int_\Omega \exp(d_A(x)^2 / 4) \, d\mu(x) \leq 1$.

**Tail bound:** $\mu(A) \cdot \mu(\{x : d_A(x) \geq t\}) \leq \exp(-t^2/4)$. When $\mu(A) \geq 1/2$,
$\mu(\{x : d_A(x) \geq t\}) \leq 2\exp(-t^2/4)$.

**Proof strategy:** Induction on the number of coordinates $n$, using coordinate-by-coordinate
decomposition via `Fin.snoc`. Base case $n=0$ is trivial. The inductive step decomposes
$\Omega \simeq \Omega^{(n)} \times \Omega_{n+1}$ and applies a key geometric recursion for
$d_A(x,\omega)^2$ in terms of projections and sections, followed by analytic assembly using
Holder's inequality, the induction hypothesis, and Fubini's theorem.

## Items

---
## 10. Definitions

### 10.1. mismatchVector

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For $x, y : \Omega = \prod_{i:\mathrm{Fin}\;n} \Omega_i$, define the mismatch vector
        $v(x,y) \in \mathrm{EuclideanSpace}\;\mathbb{R}\;(\mathrm{Fin}\;n)$ by:
        $$v(x,y)_i = \mathbb{1}[x_i \neq y_i]$$
        where the $i$-th coordinate is $0$ if $x_i = y_i$ and $1$ otherwise. This is a
        `EuclideanSpace ℝ (Fin n)`-valued function.
    - proof: |
        Definition, no proof.
- **prep**
    - `EuclideanSpace ℝ (Fin n)` — `PiLp 2 (fun _ : Fin n => ℝ)`, with coordinate access via `x i`. Defined in `Mathlib.Analysis.InnerProductSpace.PiL2`.
    - `WithLp.toLp 2` — constructor for `EuclideanSpace ℝ (Fin n)` from a `Fin n → ℝ` function. `toLp_apply` gives `toLp 2 f i = f i`.
    - `EuclideanSpace.single i a` — basis vector with `a` at coordinate `i`, `0` elsewhere (not needed for this def, but useful for downstream lemmas).
    - `PiLp.ext` — extensionality for `EuclideanSpace` values (via `@[ext]`).
    - `[∀ i, DecidableEq (Ω i)]` — needed for the `if x i = y i then ... else ...` in the definition.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Write the `def mismatchVector` with its type signature and make it compile | Definition written and compiles. Uses `WithLp.toLp 2` to lift `Fin n → ℝ` into `EuclideanSpace`. Requires `[∀ i, DecidableEq (Ω i)]` for coordinate comparison. | Verified. Integrated into `ConvexDistance.lean` with import `Mathlib.Analysis.InnerProductSpace.PiL2`. Tmp file deleted. | `tmp_mismatch_vector.lean` |

### 10.5. convexMismatchSet

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For $x : \Omega$ and $A : \mathrm{Set}\;\Omega$, define the convex mismatch set:
        $$C_A(x) = \mathrm{convexHull}\;\mathbb{R}\;\{v(x,y) : y \in A\}$$
        This is the convex hull (in $\mathbb{R}^n$) of all mismatch vectors from $x$ to points in $A$.
        For $A = \emptyset$, the set is empty and the convex hull is $\emptyset$.
    - proof: |
        Definition, no proof.
- **prep**
    - `convexHull ℝ` — convex hull operator over ℝ. From `Mathlib.Analysis.Convex.Hull`. Type: `convexHull 𝕜 : ClosureOperator (Set E)`, applied as `convexHull 𝕜 s : Set E`. Requires `[AddCommMonoid E] [Module ℝ E]`, satisfied by `EuclideanSpace ℝ (Fin n)`.
    - `mismatchVector` (item 10.1) — the mismatch vector `(x y : Π i, Ω i) → EuclideanSpace ℝ (Fin n)`. Already defined in `ConvexDistance.lean`.
    - `Set.image` — `mismatchVector x '' A` yields `{v(x,y) | y ∈ A}` as a `Set (EuclideanSpace ℝ (Fin n))`.
    - Key API for downstream proofs: `convexHull_empty`, `subset_convexHull`, `convex_convexHull`, `convexHull_mono`, `convexHull_singleton`, `mem_convexHull_iff` (all in `Mathlib.Analysis.Convex.Hull`).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Write the `def convexMismatchSet` with its type signature and make it compile | Definition written and compiles. Uses `convexHull ℝ (mismatchVector x '' A)`. Requires `Mathlib.Analysis.Convex.Hull` for `convexHull`. | Verified. Integrated into `ConvexDistance.lean` with import `Mathlib.Analysis.Convex.Hull`. Tmp file deleted. | `tmp_convex_mismatch_set.lean` |

### 10.10. convexDistance

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For $x : \Omega$ and $A : \mathrm{Set}\;\Omega$, define the convex distance:
        $$d_A(x) = \mathrm{Metric.infDist}\;0\;(\mathrm{convexMismatchSet}\;x\;A)$$
        Equivalently, $d_A(x) = \inf\{\|z\| : z \in \mathrm{conv}\{v(x,y) : y \in A\}\}$.
        When $A = \emptyset$, the convex hull of $\emptyset$ is $\emptyset$, and
        $\mathrm{infDist}\;0\;\emptyset = \infty$ (by convention we take $+\infty$,
        but in practice $A$ is nonempty in all applications).
    - proof: |
        Definition, no proof. Note: `Metric.infDist` is defined for any set, returning $0$ for
        the empty set only if we adopt the convention that $\inf\emptyset = 0$, which is the
        mathlib convention for `infDist`. We prove separately that $d_\emptyset(x) = 0$ follows
        from this convention, or we handle the empty-set case specially in lemmas that need it.
- **prep**
    - `Metric.infDist` — infimum distance from a point to a set. From `Mathlib.Topology.MetricSpace.HausdorffDistance`. Type: `Metric.infDist x s : ℝ` where `x : α`, `s : Set α`, requires `[PseudoMetricSpace α]`. Satisfied by `EuclideanSpace ℝ (Fin n)` via its inner product structure.
    - `Metric.infDist_nonneg` — `0 ≤ Metric.infDist x s`. Nonnegativity (used in item 20.15).
    - `Metric.infDist_empty` — `Metric.infDist x ∅ = 0`. Mathlib convention: infimum over empty set is 0 (used in item 20.30).
    - `Metric.infDist_singleton` — `Metric.infDist x {y} = dist x y` (used in item 20.35).
    - `Metric.infDist_zero_of_mem` — `x ∈ s → Metric.infDist x s = 0` (used in item 20.20).
    - `convexMismatchSet` (item 10.5) — the `Set (EuclideanSpace ℝ (Fin n))` whose distance we measure.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Write the `def convexDistance` with its type signature and make it compile | Definition written and compiles. Uses `Metric.infDist 0` on `convexMismatchSet x A` to compute the convex distance. Type: `convexDistance x A : ℝ` with `[∀ i, DecidableEq (Ω i)]`. Requires `Mathlib.Topology.MetricSpace.HausdorffDistance` for `Metric.infDist`. | Verified. Integrated into `ConvexDistance.lean` with import `Mathlib.Topology.MetricSpace.HausdorffDistance`. Tmp file deleted. | `tmp_convex_distance.lean` |

---
## 20. Basic Properties

### 20.1. mismatchVector_self

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For all $x : \Omega$, $v(x,x) = 0$ (the zero vector in `EuclideanSpace ℝ (Fin n)`).
    - proof: |
        By definition, each coordinate is $\mathbb{1}[x_i \neq x_i] = 0$. Use `funext` and
        the coordinate-wise definition of `EuclideanSpace`.
- **prep**
    - `mismatchVector` (item 10.1) — the mismatch vector definition
    - `PiLp.ext` — extensionality for `EuclideanSpace` (used automatically by the `ext` tactic)
    - `PiLp.toLp_apply` — coordinate access lemma: `toLp p x i = x i` (used via `simp [mismatchVector]`)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `mismatchVector x x = 0` using `ext i; simp [mismatchVector]` | One-liner: `ext i; simp [mismatchVector]`. Uses `PiLp.ext` for extensionality and `simp` expands the definition to `0 = 0`. Clean, no `sorry`, no `axiom`. | Verified compilation (no errors). Proof correct. Integrated into `ConvexDistance.lean` as `@[simp]` lemma after `mismatchVector` definition. Tmp file deleted. | `tmp_mismatch_vector_self.lean` |

### 20.5. mismatchVector_coord

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For all $x, y : \Omega$ and $i : \mathrm{Fin}\;n$,
        $(v(x,y)\;i) \in \{0, 1\}$. The coordinate is $0$ iff $x_i = y_i$, and $1$ iff $x_i \neq y_i$.
        Also $\|v(x,y)\|^2 = \sum_i \mathbb{1}[x_i \neq y_i]$.
    - proof: |
        The first part follows directly from the definition. For the norm-squared identity,
        use `EuclideanSpace.dist_sq_eq` or `PiLp.norm_sq_eq_of_L2`, noting that each coordinate
        is either 0 or 1, so $\|v(x,y)\|^2 = \sum_i \mathbb{1}[x_i \neq y_i]^2 = \sum_i \mathbb{1}[x_i \neq y_i]$.
- **prep**
    - `mismatchVector` (item 10.1) — the mismatch vector definition
    - `PiLp.toLp_apply` — `toLp p x i = x i`, coordinate extraction from `EuclideanSpace` (used in `mismatchVector_apply` proof)
    - `EuclideanSpace.real_norm_sq_eq` — `‖x‖² = Σ i, (x i)²` for `x : EuclideanSpace ℝ n` (ℝ-specific simplification, used in `norm_sq_mismatchVector` proof)
    - `PiLp.norm_sq_eq_of_L2` — `‖x‖² = Σ ‖x i‖²` for `x : PiLp 2 β` (general version, underlying `EuclideanSpace.real_norm_sq_eq`)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `mismatchVector_apply` and `norm_sq_mismatchVector` — coordinate extraction and norm-squared identity | Two lemmas proved. `mismatchVector_apply` (with `@[simp]`): coordinate access via `PiLp.toLp_apply` — one-line `simp`. `norm_sq_mismatchVector`: squared Euclidean norm equals sum of mismatch indicators — one-line `simp` using `EuclideanSpace.real_norm_sq_eq`. Both clean, no `sorry`, no `axiom`. | Verified compilation (no errors). Proofs correct — `mismatchVector_apply` uses `PiLp.toLp_apply` for coordinate extraction; `norm_sq_mismatchVector` uses `EuclideanSpace.real_norm_sq_eq` and each `0²=0`, `1²=1` simplifies via `simp`. No new imports needed — `PiL2` already imported. Both lemmas integrated into `ConvexDistance.lean` after `mismatchVector_self`. Tmp file deleted. | `tmp_mismatch_vector_coord.lean` |

### 20.10. mismatchVector_snoc

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        Under the identification $\Omega^{(n+1)} \simeq \Omega^{(n)} \times \Omega_{n+1}$ via
        `Fin.snoc`, the mismatch vector decomposes as:
        $$v((x,\omega), (y,\omega')) = (v(x,y),\; \mathbb{1}[\omega \neq \omega'])$$
        where the last coordinate is $0$ if $\omega = \omega'$ and $1$ otherwise, and
        $v(x,y)$ is the mismatch vector on the first $n$ coordinates.
    - proof: |
        Use `Fin.snoc` to decompose a function `Fin (n+1) -> Omega` into `x : Fin n -> Omega` and
        `omega : Omega_{last}`. For each coordinate $i$, case-split on whether $i$ is the last
        coordinate (`Fin.last n`) or not. For non-last coordinates, the mismatch is $v(x,y)_i$.
        For the last coordinate, $\mathbb{1}[\omega \neq \omega']$.
        Using `EuclideanSpace.finAddEquivProd` to map to the product representation.
- **prep**
    - `mismatchVector` (item 10.1) — mismatch vector definition, in `ConvexDistance.lean`
    - `mismatchVector_apply` (item 20.5) — `@[simp]` coordinate access: `mismatchVector x y i = ...`
    - `Fin.snoc` — `(p : (i : Fin n) → α i.castSucc) → α (Fin.last n) → (i : Fin (n+1)) → α i`. From `Mathlib.Data.Fin.Tuple.Basic`.
    - `Fin.last n` — last element of `Fin (n+1)`. Core.
    - `Fin.castSucc` — embed `Fin n` into `Fin (n+1)`. Core.
    - `Fin.lastCases` — case analysis on `Fin (n+1)`: `last` vs `castSucc i`. Core.
    - `Fin.snoc_castSucc` — `Fin.snoc p x i.castSucc = p i`. From `Mathlib.Data.Fin.Tuple.Basic`.
    - `Fin.snoc_last` — `Fin.snoc p x (Fin.last n) = x`. From `Mathlib.Data.Fin.Tuple.Basic`.
    - `EuclideanSpace.finAddEquivProd` — `EuclideanSpace ℝ (Fin (n+m)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)`. From `Mathlib.Analysis.InnerProductSpace.PiL2`.
    - `EuclideanSpace.equiv` — `EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜`. From `Mathlib.Analysis.InnerProductSpace.PiL2`. Maps to underlying function type.
    - `PiLp.ext` — `@[ext]` extensionality for `EuclideanSpace`. Automatic.
    - `Prod.ext` — `@[ext]` extensionality for `Prod`. Used if proving via `finAddEquivProd`.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `mismatchVector_snoc` decomposing mismatch vector under `Fin.snoc` — two coordinate-wise `@[simp]` lemmas plus combined lemma using `EuclideanSpace.equiv` + `Fin.snoc` | Three lemmas proved: `mismatchVector_snoc_castSucc` (`@[simp]`), `mismatchVector_snoc_last` (`@[simp]`), and `mismatchVector_snoc`. All use `simp [mismatchVector]` — trivial from definition. The combined lemma uses `ext i; induction i using Fin.lastCases` to case-split on last vs non-last coordinate. | Verified compilation (0 errors, 0 warnings). No `sorry`, no `axiom`. Added `Mathlib.Data.Fin.Tuple.Basic` import to main file. Integrated 3 lemmas into `ConvexDistance.lean` after `norm_sq_mismatchVector`. Tmp file deleted. | `tmp_mismatch_vector_snoc.lean` |

### 20.15. convexDistance_nonneg

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For all $x : \Omega$ and $A \subseteq \Omega$, $d_A(x) \geq 0$.
    - proof: |
        Direct application of `Metric.infDist_nonneg`.
- **prep**
    - `Metric.infDist_nonneg` — infDist is always nonnegative
    - `convexDistance` (item 10.10)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `convexDistance_nonneg` using `Metric.infDist_nonneg` — trivial 1-line proof via `simp` or direct application | Trivial 1-liner: `Metric.infDist_nonneg`. No `sorry`, no `axiom`. `@[simp]` not applied (nonnegativity lemmas are not typical simp targets). | Verified compilation (0 errors). Proof correct — `convexDistance` unfolds to `Metric.infDist 0 (convexMismatchSet x A)`, so `Metric.infDist_nonneg` applies directly. Integrated into `ConvexDistance.lean` after `convexDistance` definition. Tmp file deleted. | `tmp_convex_distance_nonneg.lean` |

### 20.20. convexDistance_zero_of_mem

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        If $x \in A$, then $d_A(x) = 0$.
    - proof: |
        If $x \in A$, then $v(x,x) = 0$ (by `mismatchVector_self`) is in the mismatch set for $A$,
        hence $0$ is in the convex hull of the mismatch set. Therefore `Metric.infDist 0 S = 0`
        for any set $S$ containing $0$. Use `Metric.infDist_zero_of_mem` or a direct argument
        with `Metric.mem_iff_infDist_eq_zero`.
- **prep**
    - `mismatchVector_self` (item 20.1) — `mismatchVector x x = 0`
    - `subset_convexHull` — `s ⊆ convexHull R s` (from `Mathlib.Analysis.Convex.Hull`)
    - `Metric.infDist_zero_of_mem` — `x ∈ s → Metric.infDist x s = 0` (from `Mathlib.Topology.MetricSpace.HausdorffDistance`)
    - `convexDistance` (item 10.10)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `convexDistance_zero_of_mem` using `Metric.infDist_zero_of_mem` and `subset_convexHull` | 5-line proof: `rw [convexDistance]`, `apply Metric.infDist_zero_of_mem`, `apply subset_convexHull ℝ`, `exact ⟨x, h, mismatchVector_self x⟩`. Clean, no `sorry`, no `axiom`. Uses `mismatchVector_self` to show `0` is in the image, then `subset_convexHull` to get `0 ∈ convexMismatchSet`. | Verified compilation (0 errors, 0 warnings). Proof correct — chain: `x ∈ A` → `mismatchVector x x = 0 ∈ mismatchVector x '' A` → `0 ∈ convexMismatchSet x A` → `Metric.infDist 0 (convexMismatchSet x A) = 0`. Integrated into `ConvexDistance.lean` after `convexDistance_nonneg`. Tmp file deleted. | `tmp_convex_distance_zero_of_mem.lean` |

### 20.25. convexDistance_mono

- **meta**
    - kind: lemma
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        If $A \subseteq B \subseteq \Omega$ and $A$ is nonempty, then $d_B(x) \leq d_A(x)$ for all $x$.
        The `A.Nonempty` hypothesis is required because `Metric.infDist_le_infDist_of_subset`
        requires the smaller set to be nonempty.
    - proof: |
        `A ⊆ B` implies `mismatchVector x '' A ⊆ mismatchVector x '' B` (by `Set.image_mono`),
        so `convexHull` is monotone via `convexHull_mono`.
        Then `Metric.infDist_le_infDist_of_subset` gives the inequality (requires the smaller set
        is nonempty, which follows from `hA : A.Nonempty`).
    - **prep**
        - `convexDistance` (item 10.10)
        - `convexHull_mono` — monotonicity of convex hull: `s ⊆ t → convexHull 𝕜 s ⊆ convexHull 𝕜 t`
        - `Metric.infDist_le_infDist_of_subset` — `s ⊆ t → s.Nonempty → Metric.infDist x t ≤ Metric.infDist x s`
        - `Set.image_mono` — `s ⊆ t → f '' s ⊆ f '' t`
        - `subset_convexHull` — `s ⊆ convexHull 𝕜 s`
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `convexDistance_mono` using `Metric.infDist_le_infDist_of_subset` and `convexHull_mono`. Requires `A.Nonempty` hypothesis. | 7-line proof: unwraps `convexDistance`, applies `Metric.infDist_le_infDist_of_subset` with `convexHull_mono` for subset and `subset_convexHull` to show nonempty. Clean, no `sorry`, no `axiom`. | Verified compilation (0 errors, 0 warnings). Proof correct — uses `Set.image_mono` for image inclusion, `convexHull_mono` for convex-hull inclusion, and `hA : A.Nonempty` to produce a witness for `Metric.infDist_le_infDist_of_subset`. Integrated into `ConvexDistance.lean` after `convexDistance_zero_of_mem`. Tmp file deleted. | `tmp_convex_distance_mono.lean` |

### 20.30. convexDistance_empty

- **meta**
    - kind: lemma
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For all $x : \Omega$, $d_\emptyset(x) = 0$ (by the mathlib convention that
        $\inf\emptyset = 0$ for `infDist`).
    - proof: |
        `Metric.infDist` on the empty set is defined to be $0$ in mathlib
        (`Metric.infDist_empty`). So this follows directly.
- **prep**
    - `Metric.infDist_empty` — infDist to empty set is 0
    - `convexDistance` (item 10.10)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `convexDistance_empty` using `simp [convexDistance, convexMismatchSet, Metric.infDist_empty]` | 1-line proof: `simp [convexDistance, convexMismatchSet, Metric.infDist_empty]`. Clean, no `sorry`, no `axiom`. `@[simp]` added. | Verified compilation (0 errors, 0 warnings). Trivial proof — `Metric.infDist_empty` handles the empty-set convention for `infDist`. Integrated into `ConvexDistance.lean` after `convexDistance_mono`. Tmp file at `StatsMLlib/Probability/Concentration/tmp_convex_distance_empty.lean`. | `tmp_convex_distance_empty.lean` |

### 20.35. convexDistance_singleton

- **meta**
    - kind: lemma
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For a singleton set $A = \{y\}$, $d_{\{y\}}(x) = \|v(x,y)\| = \sqrt{\sum_i \mathbb{1}[x_i \neq y_i]}$.
        This is the Hamming distance between $x$ and $y$.
    - proof: |
        The mismatch set for $\{y\}$ is $\{v(x,y)\}$, a singleton. Its convex hull is the same
        singleton. So $d_{\{y\}}(x) = \mathrm{infDist}\;0\;\{v(x,y)\} = \|v(x,y)\|$ by
        `Metric.infDist_singleton`. Then use `mismatchVector_coord` (item 20.5) for the norm formula.
- **prep**
    - `Metric.infDist_singleton` — distance to a singleton
    - `mismatchVector_coord` (item 20.5) — norm formula
    - `convexDistance` (item 10.10)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 | done | convexDistance x {y} = \|mismatchVector x y\| | Proved in one `simp`: `convexDistance_singleton` via `Set.image_singleton`, `convexHull_singleton`, `Metric.infDist_singleton`, `dist_zero_left`. Integrated directly into ConvexDistance.lean (line ~136) with `@[simp]`. | Verified (commit feat(20.35)). Bookkeeping catch-up: meta status was left `working` because the Survey integrated directly without a Review pass; corrected to `done` on 2026-08-12. | `tmp_convex_distance_singleton.lean` |

### 20.40. prod_section_projection

- **meta**
    - kind: def
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For $A \subseteq \Omega^{(n+1)} = (\prod_{i:\mathrm{Fin}\;n} \Omega_i) \times \Omega_{n+1}$, define:
        - The **projection** $B = \pi(A) = \{x \in \prod_{i:\mathrm{Fin}\;n} \Omega_i : \exists \omega \in \Omega_{n+1},\; (x,\omega) \in A\}$.
        - For each $\omega \in \Omega_{n+1}$, the **section** $A_\omega = \{x \in \prod_{i:\mathrm{Fin}\;n} \Omega_i : (x,\omega) \in A\}$.
        These are used in the inductive step of the main proof.
    - proof: |
        Definition, no proof.
- **prep**
    - `Fin.snoc` for appending last coordinate
    - `Set.mem_setOf_eq` for set comprehension reduction
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Define `sectionSet` and `projectionSet` using `Fin.snoc` set comprehensions. Type pattern follows existing `mismatchVector_snoc` convention: `Ω : Fin (n+1) → Type*`. | Two defs, no proofs needed. Uses `Fin.snoc`, `Fin.last`, `Fin.castSucc` from `Mathlib.Data.Fin.Tuple.Basic` (already imported). Both are simple `Set` comprehensions — `sectionSet` picks `x` with fixed `ω`, `projectionSet` exists over `ω`. | Verified compilation (0 errors, 0 warnings). Integrated into `ConvexDistance.lean` after `convexDistance_singleton`. Tmp file deleted. | `tmp_prod_section_projection.lean` |

---
## 40. Core Lemmas

### 40.5. convexDistance_recursion

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 4 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
    - note: |
        RESTRUCTURED (attempt 4): the theorem now carries the hypothesis
        `(h_sec : (sectionSet A ω).Nonempty)`. The empty-section branch was FALSE
        for t ∈ (0,1] (counterexample: Ω={0,1}, A={(1,1)}, x=0, ω=0, t=1 gives
        LHS=2 > RHS=0) and has been removed together with its sorry. The empty
        case is covered exactly by item 40.7 (`convexDistance_snoc_empty_section_eq`).
        The nonempty-section proof (t=0, t=1, and general t) uses h_sec directly.
- **informal**
    - statement: |
        **The key geometric recursion.** Let $\Omega^{(n+1)} = \Omega^{(n)} \times \Omega_{n+1}$,
        $A \subseteq \Omega^{(n+1)}$, and define $B = \pi(A)$ (projection) and $A_\omega$ (sections)
        as in item 20.40. Then for any $x \in \Omega^{(n)}$, $\omega \in \Omega_{n+1}$, and
        $\lambda \in [0,1]$:
        $$d_A(x,\omega)^2 \leq (1-\lambda)\, d_B(x)^2 + \lambda\, d_{A_\omega}(x)^2 + (1-\lambda)^2.$$
    - proof: |
        This is the heart of the entire proof. The argument uses convexity of $\|\cdot\|^2$ and
        a case analysis on whether $A_\omega$ is empty or nonempty.

        **Step 1: Represent mismatch vectors.** Using `mismatchVector_snoc` (item 20.10),
        for any $(y, \omega') \in A$, the mismatch vector from $(x,\omega)$ to $(y,\omega')$ is
        $v((x,\omega), (y,\omega')) = (v(x,y), \mathbb{1}[\omega \neq \omega'])$.

        **Step 2: Two key cases.**

        *Case A: $A_\omega$ is nonempty.* Pick $y \in A_\omega$, so $(y, \omega) \in A$.
        Then $v((x,\omega), (y,\omega)) = (v(x,y), 0)$. Since $v(x,y)$ is in the mismatch set
        for $A_\omega$, its convex hull gives elements $(z, 0)$ where $z$ is in
        $\mathrm{conv}\{v(x,y') : y' \in A_\omega\}$. Setting $\lambda = 1$ gives:
        $d_A(x,\omega)^2 \leq d_{A_\omega}(x)^2 = (1-1)d_B^2 + 1\cdot d_{A_\omega}^2 + 0$.

        *Case B: $A_\omega$ is empty but $B$ is nonempty.* Pick $y \in B$ and some $\omega'$
        with $(y, \omega') \in A$. Since $A_\omega$ is empty, $\omega' \neq \omega$, so
        $v((x,\omega), (y,\omega')) = (v(x,y), 1)$. Then
        $\|(v(x,y), 1)\|^2 = \|v(x,y)\|^2 + 1$. Setting $\lambda = 0$ gives:
        $d_A(x,\omega)^2 \leq d_B(x)^2 + 1 = d_B^2 + 0 + 1^2$.

        **Step 3: Interpolation via convexity.** For general $\lambda \in [0,1]$, use convexity
        of $\|\cdot\|^2$ (`convexOn_normSq`, item 40.1). Take a convex combination of the two
        bounding vectors from cases A and B: if we have $(z_A, 0) \in \mathrm{conv}(A_\omega\text{-mismatch})$
        and $(z_B, 1)$ from the B case, then for any $\lambda$,
        $$\|(1-\lambda)(z_B,1) + \lambda(z_A,0)\|^2 = \|((1-\lambda)z_B + \lambda z_A,\; 1-\lambda)\|^2$$
        $$= \|(1-\lambda)z_B + \lambda z_A\|^2 + (1-\lambda)^2 \leq (1-\lambda)\|z_B\|^2 + \lambda\|z_A\|^2 + (1-\lambda)^2.$$
        Taking infimum over $z_A, z_B$ in the respective convex hulls yields the result.

        **Step 4: Edge cases.** If both $A_\omega$ and $B$ are empty, then $A$ is empty and
        $d_A = 0$, so the inequality holds trivially ($0 \leq (1-\lambda)^2$).

        The formal proof in Lean will involve: (i) using the explicit representation of convex
        hull elements as convex combinations; (ii) manipulating `Metric.infDist` over convex hulls;
        (iii) careful handling of the empty-set cases; (iv) algebraic manipulation with norms
        using `nlinarith`. Expected length: 100-200 lines.

        **Status: t=0 and t=1 cases integrated into main file. General t case deferred (not needed for two-valued induction).**
    - prep
        - `mismatchVector_snoc` (20.10) — decomposition of mismatch vector under `Fin.snoc`. In `ConvexDistance.lean`.
        - `sectionSet`, `projectionSet` (20.40) — section and projection definitions. In `ConvexDistance.lean`.
        - `convexDistance` (10.10) — definition of convex distance. In `ConvexDistance.lean`.
        - `convexDistance_mono` (20.25) — monotonicity: A ⊆ B ∧ A.Nonempty → d_B ≤ d_A. In `ConvexDistance.lean`.
        - `convexDistance_empty` (20.30) — convex distance to empty set is 0. In `ConvexDistance.lean`.
        - `convexDistance_nonneg` (20.15) — 0 ≤ convexDistance. In `ConvexDistance.lean`.
        - `parallelogram_law_with_norm` — `‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)`. From `Mathlib.Analysis.InnerProductSpace.Basic`. Used to prove convexity of ‖·‖².
        - `Metric.infDist_nonneg` — `0 ≤ Metric.infDist x s`. Already imported.
        - `Metric.isGLB_infDist` — `s.Nonempty → IsGLB (dist x '' s) (infDist x s)`. From `Mathlib.Topology.MetricSpace.HausdorffDistance`. For infimum properties.
        - `IsCompact.exists_infDist_eq_dist` — compact nonempty set attains infDist. From `Mathlib.Topology.MetricSpace.HausdorffDistance`. Alternative to ε-approach.
        - `Set.Finite.isCompact_convexHull` — convex hull of finite set is compact. From `Mathlib.Analysis.Convex.Topology`.
        - `mem_convexHull_iff` — universal property: x ∈ convexHull s ↔ ∀ t, s ⊆ t → Convex t → x ∈ t. From `Mathlib.Analysis.Convex.Hull`.
        - `convexHull_vadd` — `convexHull (v + s) = v + convexHull s`. From `Mathlib.Analysis.Convex.Hull`.
        - `LinearMap.image_convexHull` — `f '' (convexHull R s) = convexHull R (f '' s)`. From `Mathlib.Analysis.Convex.Hull`. Used for both t=0 (projectLastLM) and t=1 (embedWithZeroLM) cases.
        - `convexHull_pair` — `convexHull 𝕜 {x, y} = segment 𝕜 x y`. From `Mathlib.Analysis.Convex.Hull`. For last-coordinate bound: convexHull {0,1} = segment ℝ 0 1.
        - `segment_eq_Icc` — `segment 𝕜 x y = Set.Icc x y` when x ≤ y. From `Mathlib.Analysis.Convex.Segment`. For last-coordinate bound: segment ℝ 0 1 = Icc 0 1.
        - `Metric.infDist_lt_iff` — `s.Nonempty → (infDist x s < r ↔ ∃ y ∈ s, dist x y < r)`. From `Mathlib.Topology.MetricSpace.HausdorffDistance`. For ε-approximate minimizers from the T-side.
        - `Metric.infDist_le_dist_of_mem` — `y ∈ s → infDist x s ≤ dist x y`. From `Mathlib.Topology.MetricSpace.HausdorffDistance`. For bounding convexDistance by a specific convex hull element.
        - `EuclideanSpace.equiv` — `EuclideanSpace 𝕜 ι ≃L[𝕜] (ι → 𝕜)`. From `Mathlib.Analysis.InnerProductSpace.PiL2`.
        - `EuclideanSpace.finAddEquivProd` — `EuclideanSpace 𝕜 (Fin (n+m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)`. From `Mathlib.Analysis.InnerProductSpace.PiL2`.
        - `EuclideanSpace.norm_sq_eq` — `‖x‖² = Σ i, ‖x.ofLp i‖²`. From `Mathlib.Analysis.InnerProductSpace.PiL2`.
        - `Fin.sum_univ_succ`, `Fin.sum_univ_castSucc` — sum decomposition over `Fin (n+1)`. From `Mathlib.Algebra.BigOperators.Fin`.
        - `nlinarith` — tactic for algebraic simplification.
        **Proved in tmp (t=0 and t=1 infrastructure, all compile with 0 errors):**
        - `norm_sq_snoc` (tmp L69) — `‖Fin.snoc z a‖² = ‖z‖² + a²`. Norm decomposition for Fin.snoc vectors.
        - `convexity_norm_sq` (tmp L78) — `‖(1-t)·a + t·b‖² ≤ (1-t)‖a‖² + t‖b‖²` for t ∈ [0,1]. Via parallelogram law.
        - `le_of_le_add_epsilon` (tmp L117) — ε-principle: a ≤ b + ε ∀ε>0 → a ≤ b.
        - `le_of_lt_add_sq_epsilon` (tmp L323) — a < (b+ε)² + 1 ∀ε>0 ∧ b ≥ 0 → a ≤ b² + 1. For the t=0 case.
        - `embedWithZeroLM` / `embedWithZero` (tmp L139-198) — linear isometric embedding appending 0 as last coordinate. `embedWithZero_norm_sq`, `embedWithZero_norm_eq`, `embedWithZero_isometry`, `embedWithZero_mismatchVector` all proved. For t=1 case.
        - `projectLastLM` / `projectLast` (tmp L244-271) — linear projection dropping last coordinate. `projectLast_mismatchVector` relates projection of mismatch vectors.
        - `norm_sq_projectLast_add_last_sq` (tmp L272) — `‖z‖² = ‖projectLastLM z‖² + lastCoord(z)²`. Norm decomposition for the general case.
        - `lastCoordLM` (tmp L278) — linear map extracting last coordinate.
        - `last_coord_sq_le_one` (tmp L286) — for z ∈ convexMismatchSet, `(lastCoordLM z)² ≤ 1`. Via convexHull of {0,1} ⊆ [0,1].
        - `convexDistance_snoc_section_nonempty_le` (tmp L199) — **t=1 case proved**: d_A² ≤ d_sec² when section nonempty. Uses embedWithZero isometry + LinearMap.image_convexHull.
        - `convexDistance_snoc_le_projection_add_one` (tmp L358) — **t=0 case proved**: d_A² ≤ d_proj² + 1. Uses ε-approximation via Metric.infDist_lt_iff, surjectivity π(C_A) = C_proj, norm decomposition, and last_coord_sq_le_one.
        **Potential new lemmas for general t ∈ (0,1) approach (ATTEMPT 3):**
        - `exists_min_last_coord_lift` — For z ∈ C_proj, ∃ w ∈ C_A s.t. π(w) = z and lastCoordLM(w) ≤ lastCoordLM(w') for all w' ∈ C_A with π(w') = z. This minimal α = α_min(z) would help control the slack term (1-t)·α². The fiber π⁻¹{z} ∩ C_A is convex (intersection of convex sets), and lastCoordLM restricted to this fiber is a linear function attaining its min/max at extreme points. Since C_A is the convex hull of a finite set in finite dimensions, the fiber is a convex polytope; its minimal last-coordinate point should be attainable.
        - `last_coord_zero_for_section` — If w ∈ C_A comes from section-only generators (i.e., only mismatch vectors with last coord 0), then lastCoordLM(w) = 0. Used to show embedWithZero lifts have α = 0.
        - `Metric.infDist_lt_iff` (confirmed available) — `s.Nonempty → (infDist x s < r ↔ ∃ y ∈ s, dist x y < r)`. Already used for ε-approximation in both t=0 and t=1 proofs. Will be reused for general t.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 4 / 15 | done | Restructure: add `(h_sec : (sectionSet A ω).Nonempty)` hypothesis to `convexDistance_recursion`, delete the false empty-section branch (t ∈ (0,1]) together with its sorry, and use h_sec directly in the nonempty branch. | The empty-section branch was mathematically FALSE for t ∈ (0,1] (counterexample: Ω={0,1}, A={(1,1)}, x=0, ω=0, t=1 gives 2 ≤ 0) — removed. Nonempty-section proof keeps t=0, t=1, general-t subcases, all proved; A nonemptiness in the general-t branch is now derived from h_sec (`rcases h_sec with ⟨y, hy⟩; exact ⟨Fin.snoc y ω, hy⟩`). Empty case is covered exactly by item 40.7. | Verified compilation of `ConvexDistance.lean` (0 errors, 0 warnings, 0 sorries). Docstring updated to state the nonempty-section hypothesis and the 40.7 fallback. No other module uses this theorem, so no downstream breakage. | `tmp_convex_distance_recursion.lean` |
    | 2026-08-12 | 3 / 15 | done | Prove `convexDistance_recursion` for general t ∈ (0,1) with nonempty section. ε-approximate minimizer approach: pick δ-approximate z_proj ∈ C_proj and z_sec ∈ C_sec, lift z_proj to w_proj ∈ C_A via surjectivity of projectLastLM, embed z_sec as w_sec ∈ C_A with last coord 0, form convex combination w = (1-t)·w_proj + t·w_sec ∈ C_A. Norm decomposition: ‖w‖² = ‖(1-t)z_proj + t·z_sec‖² + ((1-t)·lastCoord(w_proj))². Convexity of ‖·‖² bounds the first term, last_coord_sq_le_one bounds the last-coord term by (1-t)². δ → 0 via le_of_le_add_epsilon. | **General t with nonempty section PROVED** (~200 lines, ε-approximation + convexity + surjectivity). Empty-section case for t ∈ (0,1] has 1 deferred sorry (not needed for two-valued induction Item 40.10). Theorem integrated into `ConvexDistance.lean`. Tmp file kept as documentation. | | `tmp_convex_distance_recursion.lean` |
    | 2026-08-12 | 2 / 15 | pending | Prove `convexDistance_snoc_le_projection_add_one` (t=0 case): d_A² ≤ d_B² + 1 using ε-approximation from T-side with surjectivity lift, norm decomposition, and last-coordinate-bound lemma. Also fix `norm_sq_projectLast_add_last_sq` (already compiles, remove unused `Pi.add_apply`). | **t=0 case proved:** `convexDistance_snoc_le_projection_add_one` (d_A² ≤ d_B² + 1) via ε-approximation from projection side with surjectivity lift, norm decomposition, and last-coordinate-bound lemma. **t=1 case proved** (previous attempt): `convexDistance_snoc_section_nonempty_le` (d_A² ≤ d_{A_ω}²). **Helper lemmas proved:** `lastCoordLM`, `last_coord_sq_le_one`, `le_of_lt_add_sq_epsilon`. **Remaining sorries:** `convexDistance_recursion` general t ∈ (0,1) case -- deferred, not needed for two-valued induction (item 40.10). | Verified compilation (0 errors, 0 warnings). All no-sorry lemmas integrated into `ConvexDistance.lean`: `norm_sq_snoc`, `convexity_norm_sq`, `le_of_le_add_epsilon`, `le_of_lt_add_sq_epsilon`, `embedWithZero*` helpers, `convexDistance_snoc_section_nonempty_le` (t=1), `projectLast*` helpers, `lastCoordLM`, `last_coord_sq_le_one`, `convexDistance_snoc_le_projection_add_one` (t=0). Tmp file kept -- `convexDistance_recursion` with general t sorries stays there. t=0 and t=1 cases unblock item 40.10. Next attempt: prove general t case (optional) or proceed to 40.10. | `tmp_convex_distance_recursion.lean` |
    | 2026-08-12 | 1 / 15 | pending | Write statement of `convexDistance_recursion` with general λ ∈ [0,1]. Set up proof skeleton with 3 helper lemmas: `norm_sq_snoc`, `convexity_norm_sq`, `le_of_le_add_epsilon`. Prove λ=0 and λ=1 special cases. | **What was proved (compiles, no sorries):** (1) `norm_sq_snoc` — ‖Fin.snoc x r‖² = ‖x‖² + r²; (2) `convexity_norm_sq` — ‖(1-t)a + t·b‖² ≤ (1-t)‖a‖² + t‖b‖² via parallelogram law expansion; (3) `le_of_le_add_epsilon` — epsilon principle; (4) `embedWithZero` linear isometric embedding + supporting lemmas (`embedWithZero_norm_sq`, `embedWithZero_norm_eq`, `embedWithZero_isometry`); (5) `embedWithZero_mismatchVector` — key relationship with mismatch vectors; (6) **`convexDistance_snoc_section_nonempty_le`** — **t=1 case proved**: d_A(snoc x ω)² ≤ d_{A_ω}(x)² when A_ω nonempty, using embedWithZero isometry, convexHull image commuting with linear maps, and convexDistance_mono. **What remains (sorries):** (a) `norm_sq_projectLast_add_last_sq` — norm decomposition for projection (line ~272); (b) `convexDistance_snoc_le_projection_add_one` — t=0 case, d_A² ≤ d_B² + 1 (line ~276); (c) `convexDistance_recursion` — general t statement (line ~338). **Approaches that worked:** linear isometric embedding (`embedWithZero`) cleanly handles t=1 case; `convexity_norm_sq` uses inner product algebra (no heavy topology needed); `embedWithZeroLM.image_convexHull` uses mathlib's `LinearMap.image_convexHull`. | Partial — t=1 case and linear algebra infrastructure done. Tmp file kept for next attempt. Focus next attempt on: (1) finishing `convexDistance_snoc_le_projection_add_one` (t=0 case) via projection linear map; (2) assembling the general t bound using t=0 and t=1 cases. | `tmp_convex_distance_recursion.lean` |

### 40.7. convexDistance_snoc_empty_section_eq

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
    - note: |
        The theorem carries the hypothesis `(h_nonempty : A.Nonempty)`: if `A = ∅` the
        identity reads `0 = 1`, so nonemptiness of A is required. When the ω-section is
        empty but A is not, the identity holds for every x and ω.
- **informal**
    - statement: |
        When the ω-section of A is empty (and A is nonempty), the convex distance has the exact form:
        $$d_A(\mathrm{snoc}\;x\;\omega)^2 = d_B(x)^2 + 1$$
        where B = projectionSet A.
        All mismatch vectors from (x,ω) to points of A have last coordinate 1, so the convex
        hull lies in the hyperplane {last = 1}, and the squared distance decomposes exactly.
    - proof: |
        Every z ∈ A has z_last ≠ ω (since A_ω = ∅). Every mismatch vector has last coordinate 1.
        C_A = convex hull of {(v, 1) : v ∈ conv(v(x, B))} = conv(v(x, B)) × {1}.
        So d_A² = inf{‖v‖² + 1 : v ∈ conv(v(x, B))} = d_B² + 1.
        Formal proof: isometry between C_A and C_B (projectLastLM restricted is an isometry
        onto), or directly via the norm decomposition `norm_sq_projectLast_add_last_sq`
        + `last_coord_sq_le_one` sharpened to equality on this hyperplane.
    - **prep**
        - `norm_sq_projectLast_add_last_sq` — norm decomposition
        - `projectLastLM` — projection map
        - `convexDistance_snoc_le_projection_add_one` (t=0 case) — for the ≤ direction
        - `projectLast_mismatchVector` — projection of mismatch vectors
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `convexDistance_snoc_empty_section_eq : d_A(snoc x ω)² = d_proj(x)² + 1` when `sectionSet A ω = ∅` and `A.Nonempty`. ≤ direction from `convexDistance_snoc_le_projection_add_one` (t=0 case). ≥ direction: every mismatch vector from (x,ω) to A has last coordinate exactly 1 (`mismatchVector_last_eq_one_of_empty_section`), so the whole convex mismatch set lies in the hyperplane {last = 1} (`lastCoord_eq_one_of_empty_section` via `convexHull_min`), hence ‖w‖² = ‖π w‖² + 1 for all w ∈ C_A; ε-approximate minimizer via `Metric.infDist_lt_iff` + `le_of_lt_add_sq_eps` closes the gap. | Verified compilation (0 errors, 0 warnings). Theorem `convexDistance_snoc_empty_section_eq` plus helpers `le_of_lt_add_sq_eps`, `mismatchVector_last_eq_one_of_empty_section`, `lastCoord_eq_one_of_empty_section` integrated into `ConvexDistance.lean` after `convexDistance_snoc_le_projection_add_one`. Note: statement requires `A.Nonempty` — if A = ∅ the identity reads 0 = 1. Tmp file deleted. | `tmp_empty_section_eq.lean` |

### 40.10. scalar_optimization_two_valued

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        When each $\Omega_i$ has only two values (so the last coordinate $\omega$ takes values in
        a two-element set), the bound from the geometric recursion can be simplified:
        for $\lambda \in \{0, 1\}$ chosen appropriately based on whether $A_\omega$ is empty,
        $$d_A(x,\omega)^2 \leq \begin{cases} d_B(x)^2 & \text{if } A_\omega = \emptyset,\\ d_{A_\omega}(x)^2 + 1 & \text{if } A_\omega \neq \emptyset. \end{cases}$$
        Consequently, $\exp(d_A(x,\omega)^2/4) \leq \exp(d_B(x)^2/4) \cdot \exp(1/4)$
        when $A_\omega$ is nonempty, and $\exp(d_A(x,\omega)^2/4) \leq \exp(d_B(x)^2/4)$
        when $A_\omega$ is empty (using the $\lambda=1$ and $\lambda=0$ cases of the recursion).
    - proof: |
        Apply `convexDistance_recursion` (item 40.5) with $\lambda = 0$ when $A_\omega = \emptyset$
        and $\lambda = 1$ when $A_\omega \neq \emptyset$. In the nonempty case,
        $(1-\lambda)^2 = 0$; in the empty case, $(1-\lambda)^2 = 1$, but the $\lambda d_{A_\omega}^2$
        term drops since $\lambda = 0$. For two-valued $\Omega_{n+1}$, the optimization is: pick
        best of $\lambda=0$ and $\lambda=1$. The exponentiated form follows by monotonicity of
        $\exp$. The slack factor $e^{1/4} \leq 2$ is used later.
    - prep
        - `convexDistance_recursion` (item 40.5) — the key recursion
        - `Real.exp` — exponential function
        - `Real.exp_add` — exp(a+b) = exp(a)*exp(b) (for the exponentiated form)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Combine t=0 (`convexDistance_snoc_le_projection_add_one`) and t=1 (`convexDistance_snoc_section_nonempty_le`) with `Real.exp` monotonicity. Returns And of universal bound (exp(d_A²/4) ≤ exp(1/4)·exp(d_proj²/4)) and conditional bound (if section nonempty: exp(d_A²/4) ≤ exp(d_sec²/4)). ~50 lines, clean proof. | 2-part lemma: universal bound from t=0 lemma via `Real.exp_le_exp.mpr` + `Real.exp_add`; conditional bound from t=1 lemma. Uses `convexDistance_nonneg` in the first part to guarantee nonnegativity for `nlinarith`. No new imports needed — `Real` available via existing imports. | Verified compilation (0 errors, 0 warnings). No `sorry`, no `axiom`. Integrated into `ConvexDistance.lean` after `convexDistance_snoc_le_projection_add_one`. Tmp file deleted. | tmp_scalar_optimization.lean |

---
## 60. Main Theorem

### 60.1. measure_pi_snoc_decomposition

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For a product measure $\mu = \bigotimes_{i=0}^n \mu_i$ on $\prod_{i=0}^n \Omega_i$,
        under the identification $\prod_{i=0}^n \Omega_i \simeq (\prod_{i=0}^{n-1} \Omega_i) \times \Omega_n$
        (via `Fin.snoc`), the measure decomposes as the product of the first $n$ marginals and
        the last marginal. That is, the natural map is measure-preserving, and Fubini's theorem
        applies:
        $$\int_{\Omega^{(n+1)}} f \, d\mu = \int_{\Omega_{n+1}} \int_{\Omega^{(n)}} f(x, \omega) \, d\mu^{(n)}(x) \, d\mu_{n+1}(\omega).$$
    - proof: |
        Compose the chain of measure-preserving transformations:
        `finSuccEquivLast` maps `Fin (n+1)` to `Option (Fin n)`, then
        `pi_map_piOptionEquivProd` relates `Measure.pi` over `Option (Fin n)` to the product
        of `Measure.pi` over `Fin n` with the last marginal, together with
        `measurePreserving_piCongrLeft` for the reindexing. The integral identity follows from
        `MeasureTheory.integral_prod` (Fubini) after applying these measure-preserving maps.
        This is a routine 10-15 line proof combining existing mathlib lemmas.
    - prep
        - `finSuccEquivLast` — `Fin (n+1) ≃ Option (Fin n)`
        - `MeasureTheory.Measure.pi_map_piOptionEquivProd` — pi over Option decomposes as product
        - `MeasureTheory.measurePreserving_piCongrLeft` — reindexing preserves measure
        - `MeasureTheory.integral_prod` — Fubini's theorem
        - `MeasureTheory.Measure.pi` — product measure
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove measure_pi_snoc_decomposition using snocME MeasurableEquiv + Measure.pi_eq + integral_map_equiv + integral_prod | Uses custom `snocME` MeasurableEquiv for Fin.snoc decomposition. Proof via measure-preserving map and Fubini: `Measure.pi_eq` for measure equality, `integral_map_equiv` for change-of-variables, `integral_prod` for Fubini. 0 errors, 0 warnings. | Verified compilation (0 errors, 0 warnings). No `sorry`, no `axiom`. Integrated into `ConvexDistance.lean` with imports `Mathlib.MeasureTheory.Constructions.Pi` and `Mathlib.MeasureTheory.Integral.Prod`. Added `open MeasureTheory`. Helper `snocME` also integrated. Tmp file deleted. | `tmp_measure_pi_snoc.lean` |

### 60.5. exp_holder

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For nonnegative measurable functions $f, g$ and $\lambda \in [0,1]$,
        $$\int f^{1-\lambda} \, g^{\lambda} \, d\mu \leq \left(\int f \, d\mu\right)^{1-\lambda} \left(\int g \, d\mu\right)^{\lambda}.$$
        This is Holder's inequality with exponents $p = 1/(1-\lambda)$ and $q = 1/\lambda$,
        which are Holder conjugates.
    - proof: |
        Direct application of Holder's inequality (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`)
        with $p = 1/(1-\lambda)$ and $q = 1/\lambda$. Set $F = f^{1-\lambda}$ and $G = g^{\lambda}$.
        This is a 3-line proof: verify the Holder conjugate condition, apply the lemma, and
        simplify using `integral_rpow` or similar.
    - prep
        - `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` — Holder's inequality for nonnegative functions
        - `Real.rpow` — real exponentiation
        - `Real.HolderConjugate` — definition of Holder conjugate exponents
        - `Real.rpow_mul` — `(x^y)^z = x^(y*z)` for `x ≥ 0`
        - `ENNReal.ofReal_inv_of_pos` — `ENNReal.ofReal (x⁻¹) = (ENNReal.ofReal x)⁻¹` for `x > 0`
        - `memLp_norm_rpow_iff` — relates `MemLp (|f|^a) (p/q)` to `MemLp f p`
        - `memLp_one_iff_integrable` — `MemLp f 1` iff `Integrable f`
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Apply Hölder via integral_mul_le_Lp_mul_Lq_of_nonneg; handle t=0,1 edge cases; prove MemLp conditions via memLp_norm_rpow_iff | Theorem proved via `integral_mul_le_Lp_mul_Lq_of_nonneg`. t=0 and t=1 edge cases handled by `simp`. Interior case (0 < t < 1) uses `Real.HolderConjugate.one_sub_inv_inv` for conjugate exponents and `memLp_norm_rpow_iff` for MemLp derivations. ~85 lines, no `sorry`, no `axiom`. | Verified compilation (0 errors, 0 warnings). No `sorry`, no `axiom`. Added imports `Mathlib.Data.Real.ConjExponents`, `Mathlib.Data.ENNReal.Inv`, `Mathlib.MeasureTheory.Function.LpSpace.Basic`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`. Added `open ENNReal`. Integrated into `ConvexDistance.lean` after `measure_pi_snoc_decomposition`. Tmp file deleted. | `tmp_exp_holder.lean` |

### 60.7. talagrand_real_variable_lemma

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For $0 < r \le 1$ there exists $\lambda \in [0,1]$ (explicitly $\lambda = \max(0, 1 + 2\log r)$)
        such that
        $$e^{(1-\lambda)^2/4} \cdot r^{-\lambda} \le 2 - r .$$
        This is the classical "real-variable lemma" of the induction step in Talagrand's
        convex distance inequality (Cook's notes on Talagrand's isoperimetric inequality, Lemma 4;
        MIT OCW 18.465 Lecture 26, Lemma 26.1; Steele, *Probability Theory and Combinatorial
        Optimization*, Ch. 6).
    - proof: |
        Take $\lambda := \max(0, 1 + 2\log r)$. Then $0 \le \lambda \le 1$ since $\log r \le 0$.
        Case split at $r = e^{-1/2}$.
        - If $r \le e^{-1/2}$, then $\lambda = 0$ (via `Real.log_le_iff_le_exp`) and it suffices to
          show $e^{1/4} \le 2 - r$. Since $r \le e^{-1/2}$, $2 - r \ge 2 - e^{-1/2}$, and
          $e^{1/4} < 4/3$ (via `Real.exp_bound_div_one_sub_of_interval'` at $x = 1/4$),
          $e^{-1/2} \le 2/3$ (via `Real.add_one_le_exp`: $3/2 \le e^{1/2}$, inverted),
          so $e^{1/4} < 4/3 = 2 - 2/3 \le 2 - e^{-1/2} \le 2 - r$.
        - If $r \ge e^{-1/2}$, then $\lambda = 1 + 2\log r$ and, using `Real.rpow_def_of_pos`,
          `Real.rpow_add` and `Real.exp_log`,
          $$e^{(1-\lambda)^2/4} r^{-\lambda} = e^{(\log r)^2} \cdot r^{-1} \cdot r^{-2\log r}
            = e^{-(\log r)^2} / r .$$
          Writing $L := -\log r \in [0, 1/2]$ (so $r = e^{-L}$), the claim is equivalent to
          $h(L) := e^{L-L^2} + e^{-L} \le 2$. Prove $h$ is antitone on $[0,1/2]$ via
          `antitoneOn_of_deriv_nonpos`: $h'(L) = (1-2L)e^{L-L^2} - e^{-L} \le 0$, shown by
          $\log(1-2L) \le -2L \le L^2 - 2L$ (first inequality via `Real.log_le_sub_one_of_pos`,
          second since $L^2 \ge 0$) and monotonicity of `Real.exp`. Since $h(0) = 2$, done.
          (Alternative without derivatives: Taylor bounds
          $e^{-L} \le 1 - L + L^2/2$ and $e^{L-L^2} \le 1 + (L-L^2) + (L-L^2)^2/2 + (L-L^2)^3/(6(1-(L-L^2)/4))$,
          reducing to a polynomial inequality in $L \in [0,1/2]$ solvable by `nlinarith`.)
    - prep
        - `Real.rpow_def_of_pos` — `0 < x → x ^ y = exp (log x * y)`
        - `Real.rpow_add` — `0 < x → x ^ (y+z) = x^y * x^z`
        - `Real.rpow_zero` — `x ^ (0 : ℝ) = 1`
        - `Real.exp_log` — `0 < x → exp (log x) = x`; `Real.log_exp` — `log (exp x) = x`
        - `Real.log_le_log` / `Real.log_lt_log` — log monotonicity
        - `Real.log_le_sub_one_of_pos` — `0 < x → log x ≤ x - 1` (gives `log(1-2L) ≤ -2L`)
        - `Real.log_le_iff_le_exp` — `0 < x → (log x ≤ y ↔ x ≤ exp y)` (case split at `e^(-1/2)`)
        - `Real.add_one_le_exp` — `x + 1 ≤ exp x` (gives `e^(-1/2) ≤ 2/3`)
        - `Real.exp_bound_div_one_sub_of_interval'` — `0 < x < 1 → exp x < 1/(1-x)` (gives `e^(1/4) < 4/3`)
        - `Real.exp_le_exp` / `Real.exp_lt_exp` — exp monotonicity
        - `Real.exp_add` / `Real.exp_neg` / `Real.exp_pos` — exp arithmetic and positivity
        - `antitoneOn_of_deriv_nonpos` — `Convex D → ContinuousOn f D → DifferentiableOn f (interior D) → (∀ x ∈ interior D, deriv f x ≤ 0) → AntitoneOn f D`
        - `interior_Icc` — `interior (Icc a b) = Ioo a b`
        - `max_le_iff`, `le_max_iff` — max algebra
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `∃ t ∈ [0,1], exp((1-t)²/4)·r^(-t) ≤ 2-r` for `0 < r ≤ 1` with `t = max 0 (1+2·log r)`; case 2 via `h(L) = e^(L-L²)+e^(-L) ≤ 2` antitone on [0,1/2] | Proved via case split at `r = e^(-1/2)`. Case 1 (`r ≤ e^(-1/2)`, `t = 0`): `e^(1/4) < 4/3` via `Real.exp_bound_div_one_sub_of_interval'`, `e^(-1/2) ≤ 2/3` via `Real.add_one_le_exp`. Case 2: `t = 1+2·log r`, `u = -log r ∈ [0,1/2]`; auxiliary `talagrand_real_variable_case2` proved `talagrandCase2Fun` antitone on [0,1/2] via `antitoneOn_of_deriv_nonpos` with `h'(u) = (1-2u)e^(u-u²) - e^(-u) ≤ 0` from `log(1-2u) ≤ -2u ≤ u²-2u`. ~150 lines, no `sorry`, no `axiom`. | Verified compilation (0 errors, 0 warnings). No `sorry`, no `axiom`. Only 3 of the 5 suggested imports needed: `Mathlib.Analysis.SpecialFunctions.ExpDeriv`, `Mathlib.Analysis.Calculus.Deriv.MeanValue`, `Mathlib.Analysis.Calculus.Deriv.Pow` (`FDeriv.Pow` and `Tactic.Ring.RingNF` not needed). Integrated `talagrand_real_variable_lemma`, `talagrand_real_variable_case2`, `talagrandCase2Fun` into `ConvexDistance.lean` before item 60.12. Full `lake build` passes. Tmp file deleted. | `tmp_real_variable_lemma.lean` |

### 60.8. talagrand_algebraic_assembly

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        Generic algebraic assembly for the induction step; works for any finite $\Omega_{n+1}$
        (no empty-section case analysis, no two-valued restriction). Given:
        - $q_\omega \ge 0$ with $\sum_\omega q_\omega = 1$,
        - $0 \le x_\omega \le Y$, and $S = \sum_\omega q_\omega x_\omega$,
        - per-$\omega$ bounds: (interpolation) if $x_\omega > 0$, then for every $\lambda \in [0,1]$,
          $I_\omega \le \exp((1-\lambda)^2/4) \cdot Y^{\lambda-1} \cdot x_\omega^{-\lambda}$;
          (null section) if $x_\omega = 0$, then $I_\omega \le \exp(1/4) / Y$.

        Then $S \cdot \sum_\omega q_\omega I_\omega \le 1$.

        NOTE (corrected 2026-08-12): the previous informal statement — using only the two bounds
        (nonempty: $I \le J$, $x J \le 1$; universal: $I \le e^{1/4} J_B$, $Y J_B \le 1$) — is FALSE.
        Counterexample: $q_0 = q_1 = 1/2$, $x_0 = 0.78Y$, $x_1 = Y$,
        $I_0 = \min(e^{1/4}/Y,\, 1/x_0)$, $I_1 = 1/Y$ satisfy both bounds but give
        $S(q_0 I_0 + q_1 I_1) \approx 1.0155 > 1$. The $\lambda$-interpolation bounds are strictly
        stronger and are required.
    - proof: |
        For each $\omega$ with $x_\omega > 0$, apply `talagrand_real_variable_lemma` (item 60.7)
        with $r = x_\omega / Y$ (valid since $0 < x_\omega \le Y$) to obtain $\lambda \in [0,1]$,
        and combine with the interpolation hypothesis:
        $I_\omega \le (2 - x_\omega/Y)/Y$.
        For $x_\omega = 0$, use $\exp(1/4) \le 2$ (e.g. `Real.exp_bound_div_one_sub_of_interval'`
        gives $e^{1/4} < 4/3 < 2$) to get $I_\omega \le 2/Y = (2 - 0/Y)/Y$.
        Sum over $\omega$ (via `Finset.sum_le_sum`, using $q_\omega \ge 0$):
        $$\sum_\omega q_\omega I_\omega \le \frac{1}{Y} \sum_\omega q_\omega (2 - x_\omega/Y)
          = \frac{2 - S/Y}{Y}.$$
        Then $S \cdot \sum q_\omega I_\omega \le (S/Y)(2 - S/Y) \le 1$: from $0 \le S \le Y$
        we get $0 \le S/Y \le 1$, and $(S/Y)(2 - S/Y) = 1 - (S/Y - 1)^2$ (`sq_nonneg` + `nlinarith`).

        NOTE: choosing $t = x_\omega/Y$ in the recursion does NOT work: the resulting inequality
        $(\sum q_\omega u_\omega)(\sum q_\omega e^{(1-u_\omega)^2/4} u_\omega^{-u_\omega}) \le 1$
        is FALSE (counterexample $q_0 = 0.93$, $u_0 = 1$, $q_1 = 0.07$, $u_1 \approx 0.704$ gives
        $\approx 1.00044 > 1$). The optimal $t$ is $\max(0,\, 1 + 2\log(x_\omega/Y))$, which yields
        exactly the $2 - r$ bound of item 60.7. The `one_empty_section_quadratic_bound` approach is
        subsumed by this and is no longer needed.
    - prep
        - `talagrand_real_variable_lemma` (item 60.7) — $e^{(1-\lambda)^2/4} r^{-\lambda} \le 2-r$ for $0 < r \le 1$
        - `hq_sum` — $\sum q_\omega = 1$ (hypothesis)
        - `hx_sec_le_Y` — $x_\omega \le Y$ (hypothesis)
        - `Real.exp_bound_div_one_sub_of_interval'` — for $\exp(1/4) < 4/3 < 2$ (null-section case)
        - `Finset.sum_le_sum` — termwise sum inequality (needs $q_\omega \ge 0$)
        - `Finset.sum_mul`, `Finset.mul_sum` — distributivity of sums
        - `sq_nonneg` — $(S/Y - 1)^2 \ge 0$ closes the proof
        - `div_le_div_iff_of_pos_right` — division bookkeeping with $Y > 0$
        - `Real.rpow_zero` — $x^0 = 1$ (null-section case: $(2 - 0/Y)/Y = 2/Y$)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `talagrand_real_variable_lemma` (new item 60.7: λ = max(0, 1+2·log r), case split at r = e^(-1/2), case 2 via h(L) = e^(L-L²)+e^(-L) ≤ 2 antitone on [0,1/2]); then state + prove `talagrand_algebraic_assembly` in generic Fintype form: per-ω interpolation bounds → I_ω ≤ (2 - x_ω/Y)/Y → sum → (S/Y)(2 - S/Y) ≤ 1 | Proved `talagrand_algebraic_assembly` in generic `Fintype ι` form. Per-ω bound `I ω ≤ (2 - x ω / Y) / Y`: null-section case (`x ω = 0`) via `e^(1/4) < 4/3 < 2` from `Real.exp_bound_div_one_sub_of_interval'`; positive case applies `talagrand_real_variable_lemma` (60.7) with `r = x ω / Y` (valid since `0 < x ω ≤ Y` via `div_pos`/`div_le_one`), rewrites `Y^(t-1)·(x ω)^(-t) = Y^(-1)·r^(-t)` via `Real.mul_rpow` + `Real.rpow_add`. Sum over ω via `Finset.sum_le_sum` with `q ω ≥ 0` and `Finset.sum_div`/`mul_div_assoc` bookkeeping. Closes via `field_simp`+`ring`: `1 - S·(2-S/Y)/Y = (1-S/Y)²`, `sq_nonneg`. ~110 lines, no `sorry`, no `axiom`. | Verified compilation (0 errors) after integration. No `sorry`, no `axiom`. No new imports needed: `Real.exp_bound_div_one_sub_of_interval'` (ExpDeriv), `Real.mul_rpow`/`Real.rpow_add`/`Real.rpow_neg_one`/`Real.rpow_nonneg` (Pow.Real) already imported in `ConvexDistance.lean`. Integrated after item 60.7, before item 60.12. Tmp file deleted. NOTE: user's `tmp_mannual.lean` also declares `talagrand_algebraic_assembly` and now fails to build (duplicate name) — left untouched per instructions. | `tmp_algebraic_assembly.lean` |

### 60.12. measure_decomposition_S

- **meta**
    - kind: lemma
    - priority: 3
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        Under `Fin.snoc` decomposition, $\mu(A) = \sum_\omega \mu_{n+1}(\{\omega\}) \cdot \mu^{(n)}(A_\omega)$.
        In real probabilities: $S = \sum_\omega q_\omega \cdot x_\omega$ where
        $S = \mu(A).{\rm toReal}$, $q_\omega = \mu_{n+1}(\{\omega\}).{\rm toReal}$, $x_\omega = \mu^{(n)}(A_\omega).{\rm toReal}$.
    - proof: |
        Apply `measure_pi_snoc_decomposition` (item 60.1) to the indicator function of $A$.
        The LHS gives $\mu(A)$, the RHS decomposes as iterated integral = $\sum_\omega \mu_{n+1}(\{\omega\}) \cdot \mu^{(n)}(A_\omega)$.
        Convert ENNReal to Real via `ENNReal.toReal`.
        
        Detailed proof chain (5 steps):
        1. Set `f := A.indicator (fun _ => (1 : ℝ))`. Prove `Integrable f (Measure.pi μ)` via `Integrable.of_finite` 
           (available since `[Fintype (Ω i)]` → product is Finite, `[MeasurableSingletonClass (Ω i)]` → 
           `Pi.instMeasurableSingletonClass` on product, `[IsProbabilityMeasure (μ i)]` → `IsFiniteMeasure`).
        2. Apply `measure_pi_snoc_decomposition μ f hf_int` to get
           `∫ f = ∫_ω ∫_x f(Fin.snoc x ω) dP dμ_last`.
        3. LHS: `∫ x, A.indicator 1 x d(Measure.pi μ) = (Measure.pi μ A).toReal = S` via `integral_indicator_one`
           (requires `MeasurableSet A` → via `DiscreteMeasurableSpace.forall_measurableSet`).
        4. Inner: `f(Fin.snoc x ω) = (sectionSet A ω).indicator 1 x` (lemma `indicator_snoc`, 1-line `simp`).
           Then `∫ x, (sectionSet A ω).indicator 1 x dP = (P (sectionSet A ω)).toReal = x_sec ω` via `integral_indicator_one`.
        5. Outer: `∫_ω x_sec ω dμ_last = ∑_ω (μ_last {ω}).toReal * x_sec ω = ∑_ω q ω * x_sec ω` via `integral_fintype`.
    - **prep**
        - `measure_pi_snoc_decomposition` (item 60.1) — Fubini under Fin.snoc. Signature: `Integrable f (Measure.pi μ) → ∫ f = ∫_ω ∫_x f(snoc x ω) dP dμ_last`.
        - `Integrable.of_finite` — `[Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ] → Integrable f μ`. Simplest integrability for indicator. In `Mathlib/MeasureTheory/Function/L1Space/Integrable`.
        - `Integrable.indicator` (alternative): `Integrable f μ → MeasurableSet s → Integrable (s.indicator f) μ`. In `Mathlib/MeasureTheory/Integral/IntegrableOn`.
        - `integral_indicator_one` — `∫ x, s.indicator 1 x ∂μ = μ.real s` (requires `MeasurableSet s`). `@[simp]`. In `Mathlib/MeasureTheory/Integral/Bochner/Set`.
        - `integral_fintype` — `Integrable f μ → ∫ f = ∑ x, μ.real {x} • f x`. In `Mathlib/MeasureTheory/Integral/Bochner/SumMeasure`.
        - `DiscreteMeasurableSpace.forall_measurableSet` — `MeasurableSet s` for any `s`. Instance chain: `Fintype` → `Countable` → `MeasurableSingletonClass.toDiscreteMeasurableSpace`. Product has `MeasurableSingletonClass` via `Pi.instMeasurableSingletonClass` (requires countable index set, satisfied by `Fin n`).
        - `indicator_snoc` (new lemma, ~2 lines): `A.indicator 1 (Fin.snoc x ω) = (sectionSet A ω).indicator 1 x`. Proved by `simp [sectionSet, Set.indicator]`.
        - `sectionSet` (item 20.40) — section set definition
        - `MeasureTheory.measureReal_def` — `μ.real s = (μ s).toReal`
        - `integral_const` — `∫ x, c ∂μ = c * (μ univ).toReal` (used implicitly)
    - **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-12 | 1 / 15 | done | Prove `hS_eq_sum : S = Σ_ω q ω * x_sec ω` via measure_pi_snoc_decomposition applied to `A.indicator 1`. Chain: Integrable.of_finite → measure_pi_snoc_decomposition → integral_indicator_one (LHS + inner) → integral_fintype (outer sum). ~40 lines clean proof. | Proved via 5-step chain: (1) `Integrable.of_finite` for indicator integrability, (2) `measure_pi_snoc_decomposition` for Fubini, (3) `integral_indicator_one` for LHS → S, (4) `indicator_snoc` + `integral_indicator_one` for inner → x_sec ω, (5) `integral_fintype` for outer → sum q ω * x_sec ω. Uses `MeasurableSet.of_discrete` for measurability in finite discrete setting. Helper lemma `indicator_snoc` (1-line `simp`) integrated nearby. | Verified compilation (0 errors, 1 pre-existing warning). No `sorry`, no `axiom`. Integrated `indicator_snoc` after `projectionSet` and `measure_decomposition_S` after `exp_holder` in `ConvexDistance.lean`. Tmp file deleted. | `tmp_measure_decomposition_S.lean` |

### 60.10. talagrand_convexDistance

- **meta**
    - kind: theorem
    - priority: 3
    - status: done
    - attempts: 5 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        **Talagrand's convex-distance concentration inequality (main theorem).**
        Let $(\Omega_i, \mu_i)_{i=1}^n$ be finite discrete probability spaces, each with two values.
        Let $\Omega = \prod_{i=1}^n \Omega_i$ with product measure $\mu = \bigotimes \mu_i$.
        For any measurable set $A \subseteq \Omega$ with $\mu(A) > 0$:
        $$\mu(A) \cdot \int_\Omega \exp(d_A(x)^2 / 4) \, d\mu(x) \leq 1.$$
        Equivalently, $\int_\Omega \exp(d_A(x)^2 / 4) \, d\mu(x) \leq 1 / \mu(A)$.
    - proof: |
        **Induction on $n$** (the number of coordinates, indexed by `Fin n`).

        **Base case $n = 0$:** $\Omega$ is a singleton, $\mu(\Omega) = 1$, $d_A(x) = 0$ for any $x$
        (since $v(x,x) = 0$ is in the mismatch set). Then $\exp(0) = 1$, so the integral is $1$.
        The inequality $\mu(A) \cdot 1 \leq 1$ holds since $\mu(A) \leq 1$.

        **Inductive step $n \to n+1$:** Identify $\Omega^{(n+1)} \simeq \Omega^{(n)} \times \Omega_{n+1}$
        via `Fin.snoc`. Let $\mu = \mu^{(n)} \otimes \mu_{n+1}$. For $A \subseteq \Omega^{(n+1)}$,
        define projection $B = \pi(A)$ and sections $A_\omega$ as in item 20.40.

        **Step 1: Apply geometric recursion.** Using `scalar_optimization_two_valued` (item 40.10),
        for each $\omega \in \Omega_{n+1}$ there exists $\lambda_\omega \in \{0,1\}$ such that:
        $$\exp(d_A(x,\omega)^2/4) \leq \exp(d_B(x)^2/4)^{1-\lambda_\omega} \cdot \exp(d_{A_\omega}(x)^2/4)^{\lambda_\omega} \cdot \exp((1-\lambda_\omega)^2/4).$$

        The factor $\exp((1-\lambda_\omega)^2/4)$ equals $1$ if $\lambda_\omega = 1$ (nonempty section)
        and $\exp(1/4) \leq 2$ if $\lambda_\omega = 0$ (empty section).

        **Step 2: Integrate over $x$ for fixed $\omega$.** By Holder's inequality (`exp_holder`, item 60.5):
        $$\int_{\Omega^{(n)}} \exp(d_B^2/4)^{1-\lambda} \cdot \exp(d_{A_\omega}^2/4)^{\lambda} \, d\mu^{(n)}
        \leq \left(\int \exp(d_B^2/4)\right)^{1-\lambda} \left(\int \exp(d_{A_\omega}^2/4)\right)^{\lambda}.$$

        **Step 3: Apply induction hypothesis.**
        $$\int_{\Omega^{(n)}} \exp(d_B(x)^2/4) \, d\mu^{(n)}(x) \leq 1/\mu^{(n)}(B),$$
        $$\int_{\Omega^{(n)}} \exp(d_{A_\omega}(x)^2/4) \, d\mu^{(n)}(x) \leq 1/\mu^{(n)}(A_\omega).$$

        So the inner integral is bounded by $\mu^{(n)}(B)^{-(1-\lambda_\omega)} \cdot \mu^{(n)}(A_\omega)^{-\lambda_\omega}$.

        **Step 4: Integrate over $\omega$ (Fubini).** Using `measure_pi_snoc_decomposition` (item 60.1):
        $$\int_{\Omega^{(n+1)}} \exp(d_A^2/4) \, d\mu \leq \sum_{\omega \in \Omega_{n+1}} \mu_{n+1}(\{\omega\}) \cdot e^{(1-\lambda_\omega)^2/4} \cdot \mu^{(n)}(B)^{-(1-\lambda_\omega)} \cdot \mu^{(n)}(A_\omega)^{-\lambda_\omega}.$$

        **Step 5: Optimize over $\lambda_\omega$.** For the two-valued case, we can explicitly sum
        over $\Omega_{n+1} = \{0,1\}$ and bound:
        - For $\omega$ where $A_\omega \neq \emptyset$ ($\lambda = 1$): contribution = $\mu_{n+1}(\omega) \cdot 1 \cdot 1 \cdot \mu^{(n)}(A_\omega)^{-1}$.
        - For $\omega$ where $A_\omega = \emptyset$ ($\lambda = 0$): contribution = $\mu_{n+1}(\omega) \cdot e^{1/4} \cdot \mu^{(n)}(B)^{-1} \cdot 1$.
        The sum telescopes to $\leq 1/\mu(A)$, using:
        $\mu(A) = \sum_\omega \mu_{n+1}(\{\omega\}) \cdot \mu^{(n)}(A_\omega)$ and
        $\mu^{(n)}(A_\omega) \leq \mu^{(n)}(B)$ (since $A_\omega \subseteq B$).

        This completes the induction. The formal proof is 100-200 lines due to the need for
        careful measure-theoretic bookkeeping, Fubini, and the finite-sum expansion for
        discrete $\Omega_{n+1}$.
    - prep
        **Definitions** (all in `ConvexDistance.lean`, all verified compiling with 0 errors):
        - `convexDistance` (10.10) — definition of d_A, line 95
        - `mismatchVector` (10.1) — mismatch vector, line 34
        - `convexMismatchSet` (10.5) — convex hull of mismatch set, line 86
        - `sectionSet` / `projectionSet` (20.40) — sections and projection, lines 145/155
        **Geometric recursion lemmas** (all in `ConvexDistance.lean`, no sorries):
        - `scalar_optimization_two_valued` (40.10) — combined t=0/t=1 exponential bounds, line 568
          Returns `∧` of: (1) universal bound `exp(d_A²/4) ≤ exp(1/4)·exp(d_proj²/4)`;
          (2) if section nonempty then `exp(d_A²/4) ≤ exp(d_sec²/4)`.
        - `convexDistance_snoc_section_nonempty_le` — t=1 case: `d_A² ≤ d_{sec}²`, line 283
        - `convexDistance_snoc_le_projection_add_one` — t=0 case: `d_A² ≤ d_{proj}² + 1`, line 445
        - `convexDistance_nonneg` (20.15) — `0 ≤ d_A`, line 100
        - `convexDistance_zero_of_mem` (20.20) — `x∈A → d_A(x)=0`, line 105
        - `convexDistance_mono` (20.25) — monotonicity, line 115
        - `convexDistance_empty` (20.30) — `d_∅(x)=0`, line 128
        - `convexDistance_singleton` (20.35) — `d_{y}(x)=‖v(x,y)‖`, line 136
        **Coordinate decomposition** (all in `ConvexDistance.lean`):
        - `mismatchVector_snoc` (20.10) — combined decomposition, line 78
        - `mismatchVector_snoc_castSucc` / `mismatchVector_snoc_last` — `@[simp]` coordinate access, lines 59/68
        - `Fin_snoc_eta` — `y = Fin.snoc (y∘castSucc) (y last)`, line 343
        - `norm_sq_snoc` — `‖Fin.snoc z a‖² = ‖z‖² + a²`, line 166
        - `projectLast_mismatchVector` — projection of mismatch vector, line 348
        **Integration tools**:
        - `exp_holder` (60.5) — Holder inequality `∫ f^{1-t}g^t ≤ (∫f)^{1-t}(∫g)^t`, line 685
          Requires `hf_nonneg`, `hg_nonneg`, `hf_int`, `hg_int`, `t∈[0,1]`.
        - `measure_pi_snoc_decomposition` (60.1) — Fubini under Fin.snoc, line 633
          Requires `Integrable f (Measure.pi μ)` and `[SigmaFinite (μ i)]`.
          Uses custom `snocME` MeasurableEquiv (line 610).
        - `MeasureTheory.integral_prod` — Fubini theorem (imported via `Mathlib.MeasureTheory.Integral.Prod`)
        - `measure_decomposition_S` (60.12) — $S = \sum q_\omega x_\omega$, measure decomposition of $A$
        - `talagrand_real_variable_lemma` (60.7) — $e^{(1-\lambda)^2/4} r^{-\lambda} \le 2-r$ for $0 < r \le 1$ (optimal $\lambda = \max(0, 1+2\log r)$); turns the per-$\omega$ interpolation bound into $I_\omega \le (2 - x_\omega/Y)/Y$
        - `talagrand_algebraic_assembly` (60.8) — the algebraic telescoping lemma
        - `sum_pointMasses_eq_one` — $\sum_\omega (\mu\{\omega\}).{\rm toReal} = 1$, proved inline
        - `MeasureTheory.integral_map_equiv` — change of variables (used in measure_pi_snoc_decomposition)
        **Real analysis**:
        - `Real.exp` / `Real.exp_add` / `Real.exp_le_exp.mpr` — exponential and monotonicity
        - `Real.rpow` / `Real.rpow_mul` — real exponentiation (used in exp_holder)
        - `Real.HolderConjugate.one_sub_inv_inv` — Holder conjugates for `t∈(0,1)` (used in exp_holder)
        **Measure theory typeclasses** (required in theorem statement):
        - `[∀ i, MeasurableSpace (Ω i)]` — for `Measure.pi`
        - `[∀ i, SigmaFinite (μ i)]` — for Fubini; follows from `IsProbabilityMeasure`
        - `[∀ i, IsProbabilityMeasure (μ i)]` — each μ_i is a probability measure (total mass 1)
        - `[∀ i, Fintype (Ω i)]` — each Ω_i finite (discrete probability)
        **Supporting lemmas for measure/section relationship** (to be proved in tmp file if needed):
        - `sectionSet_subset_projectionSet` — `sectionSet A ω ⊆ projectionSet A` (trivial from defs)
        - `measure_pi_section_eq` — `μ(A) = ∫_ω μ^{(n)}(A_ω) dμ_{n+1}(ω)` (via Fubini with indicator)
        **Tactics**: `nlinarith`, `ring`, `field_simp`, `positivity`, `calc`
    - log
        | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
        |------|-----|--------|------|----------------|-----------------|-----|
        | 2026-08-12 | 1 / 15 | pending | Prove the main theorem `talagrand_convexDistance` by induction on n. Base n=0: trivial (0-dim Euclidean space, unique point in product). Inductive n→n+1: decompose via Fin.snoc, apply `scalar_optimization_two_valued` per ω for the exponential bound, assemble via `exp_holder` on the inner integral, apply induction hypothesis for B (projection) and A_ω (sections), use `measure_pi_snoc_decomposition` for Fubini, sum over Fintype Ω_{n+1} (2-valued), and telescope the bound to 1 using μ(A) = Σ_ω μ_{n+1}({ω})·μ^{(n)}(A_ω) and A_ω ⊆ B. | Base case done (n=0: subsingleton + measure_univ=1 + probA≤1). Inductive step structured: Fubini decomposition, projection B=projectionSet A, hB_nonempty proved, IH applied. Strategy laid out in comments: pointwise bound from scalar_optimization_two_valued → exp_holder → IH → algebraic assembly. 1 sorry remains (line 174) for the telescoping-sum final bound. | Keep tmp. Verified compiles with 1 sorry (0 errors). Focus attempt 2 on: (1) completing the telescoping sum for the two-valued case using Fintype.instOfFinite to sum over Ω_{n+1}; (2) the measure decomposition μ(A) = Σ_ω μ_{n+1}({ω})·μ^{(n)}(A_ω) via `measure_pi_snoc_decomposition` with indicator. Core infrastructure ready. | `tmp_talagrand_convex_distance.lean` |
    | 2026-08-13 | 5 / 15 | done | Prove the main theorem `talagrand_convexDistance` by induction on n (same plan as attempt 1, with the telescoping step delegated to `talagrand_algebraic_assembly` 60.8). | **MAIN THEOREM PROVED.** Full induction completed, no sorry: base n=0 (subsingleton, integral=1, μ(A)≤1); inductive step n→n+1 via Fubini (`measure_pi_snoc_decomposition` 60.1), projection `B = projectionSet A`, IH applied to B and to each section `A_ω`; per-ω interpolation bound (recursion `convexDistance_recursion` 40.5 + `exp_holder` 60.5 + rpow arithmetic via new helper `Real.exp_rpow`); empty-section bound via `scalar_optimization_two_valued`; measure decomposition `S = Σ q ω·x_sec ω` (`measure_decomposition_S` 60.12) and `S ≤ Y`; final telescoping via `talagrand_algebraic_assembly` (60.8). | Verified 0 errors, 0 warnings (`lake build` + diagnostics clean). `#print axioms` gives only propext, Classical.choice, Quot.sound for the theorem and both helpers. Integrated `talagrand_convexDistance` plus helpers `Real.exp_rpow`, `sum_pointMasses_eq_one` at the end of `ConvexDistance.lean` (helpers were absent from the main file; no new imports needed). Thorough docstring documenting the proof structure. Tmp file deleted. | `tmp_talagrand_main.lean` |

---
## 80. Corollaries

### 80.1. talagrand_convexDistance_tail

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        **Tail bound.** Under the same hypotheses as the main theorem, for any $t \geq 0$:
        $$\mu(A) \cdot \mu(\{x \in \Omega : d_A(x) \geq t\}) \leq \exp(-t^2/4).$$
    - proof: |
        Apply Markov's inequality / exponential Chebyshev to the main theorem.
        Specifically, since $\exp(d_A(x)^2/4) \geq \exp(t^2/4)$ on the set $\{x : d_A(x) \geq t\}$,
        $$\mu(\{d_A \geq t\}) \cdot \exp(t^2/4) \leq \int \exp(d_A^2/4) \, d\mu \leq 1/\mu(A).$$
        Rearranging gives the result. Use `ProbabilityTheory.measure_ge_le_exp_mul_mgf` or a direct
        application of `MeasureTheory.meas_ge_le_lintegral_div`.
        This is a 5-line proof.
    - prep
        - `talagrand_convexDistance` (item 60.10) — main theorem
        - `MeasureTheory.meas_ge_le_lintegral_div` — Markov inequality (or `measure_ge_le_exp_mul_mgf`)
        - `Real.exp_monotone` or `Real.exp_le_exp` — monotonicity of exp
        - `Real.exp` — exponential
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-13 | 1 / 15 | done | Prove `talagrand_convexDistance_tail`: μ(A)·μ({d_A ≥ t}) ≤ exp(-t²/4) for t ≥ 0, via Markov/exponential Chebyshev applied to the main theorem (60.10). | **PROVED.** Direct Markov argument: pointwise bound `exp(t²/4) ≤ exp(d_A(x)²/4)` on `B = {x | t ≤ d_A(x)}` (via `Real.exp_le_exp`, `sq_le_sq`, `convexDistance_nonneg`); integrated with indicator over finite set B (`integral_indicator_const`, `integral_mono`, `Integrable.of_finite`); combined with `talagrand_convexDistance` and divided by `exp(t²/4) > 0` (`le_div_iff₀`); final rewrite `1/exp(c) = exp(-c)` via `neg_div`, `Real.exp_neg`. | Verified 0 errors, 0 warnings in tmp; `#print axioms` gives only propext, Classical.choice, Quot.sound. All four tail corollaries (80.1, 80.5, 80.10, 80.15) proved in one tmp file and integrated at end of `ConvexDistance.lean` after the main theorem. Tmp deleted. | `tmp_tail_bounds.lean` |

### 80.5. talagrand_convexDistance_tail_half

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        When $\mu(A) \geq 1/2$, the tail bound simplifies to:
        $$\mu(\{x \in \Omega : d_A(x) \geq t\}) \leq 2\exp(-t^2/4).$$
    - proof: |
        From `talagrand_convexDistance_tail` (item 80.1): $\mu(\{d_A \geq t\}) \leq \exp(-t^2/4) / \mu(A)$.
        Since $\mu(A) \geq 1/2$, we have $1/\mu(A) \leq 2$. Hence the result.
    - prep
        - `talagrand_convexDistance_tail` (item 80.1) — tail bound with mu(A) factor
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-13 | 1 / 15 | done | Prove `talagrand_convexDistance_tail_half`: μ({d_A ≥ t}) ≤ 2 exp(-t²/4) when μ(A) ≥ 1/2. | **PROVED.** Let pA = μ(A).toReal, pB = μ({d_A ≥ t}).toReal. From 80.1: pA·pB ≤ exp(-t²/4). Since pA ≥ 1/2, nlinarith gives `1 ≤ 2·pA`; multiply by pB ≥ 0 (`mul_le_mul_of_nonneg_left`, `ENNReal.toReal_nonneg`) to get pB ≤ pB·(2·pA) = 2·(pA·pB) ≤ 2·exp(-t²/4). | 0 errors, 0 warnings; axioms: propext, Classical.choice, Quot.sound only. Integrated into `ConvexDistance.lean`. | `tmp_tail_bounds.lean` |

### 80.10. talagrand_convexDistance_tail_neg

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        Complement form of the tail bound. Apply `talagrand_convexDistance_tail` (item 80.1)
        to the complement set $A^c$:
        $$\mu(A^c) \cdot \mu(\{x : d_{A^c}(x) \geq t\}) \leq \exp(-t^2/4).$$
        When $\mu(A^c) \geq 1/2$, this gives $\mu(\{x : d_{A^c}(x) \geq t\}) \leq 2\exp(-t^2/4)$.
        This mirrors McDiarmid's `mcdiarmid_inequality_neg` pattern: apply the upper-tail result
        to the complement.
    - proof: |
        Apply `talagrand_convexDistance_tail` (item 80.1) with $A$ replaced by $A^c$.
        The hypothesis $\mu(A^c) \geq 1/2$ gives the simplified form via the same argument
        as `talagrand_convexDistance_tail_half` (item 80.5). This is a 2-line proof.
    - prep
        - `talagrand_convexDistance_tail` (item 80.1)
        - `talagrand_convexDistance_tail_half` (item 80.5) — for the μ(Aᶜ) ≥ 1/2 case
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-13 | 1 / 15 | done | Prove `talagrand_convexDistance_tail_neg`: μ({d_{Aᶜ} ≥ t}) ≤ 2 exp(-t²/4) when μ(Aᶜ) ≥ 1/2. | **PROVED (2 lines).** Direct instantiation: `exact talagrand_convexDistance_tail_half (μ := μ) Aᶜ hAc h_half ht` — item 80.5 applied to the complement set Aᶜ with hypotheses `Aᶜ.Nonempty` and `1/2 ≤ μ(Aᶜ).toReal`. Mirrors the McDiarmid neg pattern. | 0 errors, 0 warnings; axioms: propext, Classical.choice, Quot.sound only. Integrated into `ConvexDistance.lean`. | `tmp_tail_bounds.lean` |

### 80.15. talagrand_convexDistance_two_sided

- **meta**
    - kind: theorem
    - priority: 1
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
    - note: |
        RESTRUCTURED by item 80.16 (GPT review, doc/talagram/03_gpt_review/2026_08_14.md,
        point 3): requiring both $\mu(A) \ge 1/2$ and $\mu(A^c) \ge 1/2$ forces
        $\mu(A) = \mu(A^c) = 1/2$ exactly, so this statement is too special to be
        called "two-sided". The restructured version (80.16) makes each bound a
        separate implication. The genuine median-based two-sided concentration
        $P(|f - \mathrm{med}\, f| \ge t) \le 4e^{-t^2/4}$ (via the two DIFFERENT sets
        $A_- = \{f \le m\}$, $A_+ = \{f \ge m\}$) is reserved as future work.
- **informal**
    - statement: |
        Two-sided tail bound. When both $\mu(A) \geq 1/2$ AND $\mu(A^c) \geq 1/2$:
        $$\mu(\{x : d_A(x) \geq t\}) \leq 2\exp(-t^2/4) \quad\text{AND}\quad \mu(\{x : d_{A^c}(x) \geq t\}) \leq 2\exp(-t^2/4).$$
        This is simply the conjunction of the half-measure tail bound (item 80.5) applied to
        $A$ and to $A^c$, following the pattern of McDiarmid's pos/neg pair.
    - proof: |
        Apply `talagrand_convexDistance_tail_half` (item 80.5) to $A$, and
        `talagrand_convexDistance_tail_neg` (item 80.10) to $A^c$.
        Conjoin the results. This is a 2-line proof.
    - prep
        - `talagrand_convexDistance_tail_half` (item 80.5)
        - `talagrand_convexDistance_tail_neg` (item 80.10)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-13 | 1 / 15 | done | Prove `talagrand_convexDistance_two_sided`: conjunction of the two one-sided tail bounds on A and Aᶜ when both μ(A) ≥ 1/2 and μ(Aᶜ) ≥ 1/2. | **PROVED (2 lines).** `exact ⟨talagrand_convexDistance_tail_half (μ := μ) A hA h_halfA ht, talagrand_convexDistance_tail_neg (μ := μ) A hAc h_halfAc ht⟩` — pure conjunction of 80.5 on A and 80.10 on Aᶜ. | 0 errors, 0 warnings; axioms: propext, Classical.choice, Quot.sound only. Integrated into `ConvexDistance.lean`. **TALAGRAND INEQUALITY BLUEPRINT COMPLETE.** | `tmp_tail_bounds.lean` |

### 80.16. talagrand_convexDistance_two_sided (restructure)

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
    - note: |
        GPT-review follow-up (doc/talagram/03_gpt_review/2026_08_14.md, point 3).
        Restructures the 80.15 statement; the declaration name `two_sided` stays
        for this set-level interface. The future median-based theorem gets its own
        name (e.g. `two_sided_concentration`), NOT this one.
- **informal**
    - statement: |
        Set-level two-sided tail interface. For ANY $A$ (with $A$ and $A^c$ nonempty),
        each side is an independent implication:
        $$\mu(A) \ge \tfrac12 \;\Longrightarrow\; \mu\{x : d_A(x) \ge t\} \le 2e^{-t^2/4},$$
        $$\mu(A^c) \ge \tfrac12 \;\Longrightarrow\; \mu\{x : d_{A^c}(x) \ge t\} \le 2e^{-t^2/4}.$$
        Lean statement (replaces the current one near the end of the file):
        ```lean
        (A : Set ((i : Fin n) → Ω i)) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
          {t : ℝ} (ht : 0 ≤ t) :
          (1 / 2 ≤ (Measure.pi μ A).toReal →
            (Measure.pi μ {x | t ≤ convexDistance x A}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4))
          ∧
          (1 / 2 ≤ (Measure.pi μ Aᶜ).toReal →
            (Measure.pi μ {x | t ≤ convexDistance x Aᶜ}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4))
        ```
        Docstring must state: the two antecedents together force μ(A) = μ(Aᶜ) = 1/2
        (balanced set); the genuine median-based two-sided concentration
        P(|f − med f| ≥ t) ≤ 4e^(−t²/4) (via A₋ = {f ≤ m}, A₊ = {f ≥ m}) is reserved
        as future work. Also update the file-summary comment (~line 1936) that
        references item 80.15.
    - proof: |
        Move the half-measure hypotheses inside the implications:
        `⟨fun hh ↦ talagrand_convexDistance_tail_half (μ := μ) A hA hh ht,
          fun hh ↦ talagrand_convexDistance_tail_neg (μ := μ) A hAc hh ht⟩`.
        2-line proof; no new imports.
- **prep**
    - `talagrand_convexDistance_tail_half` (item 80.5) — in `ConvexDistance.lean`
    - `talagrand_convexDistance_tail_neg` (item 80.10) — in `ConvexDistance.lean`
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-14 | 1 / 15 | done | Restructure `talagrand_convexDistance_two_sided` into the conjunction of two implications — move `h_halfA` / `h_halfAc` inside the implications exactly per informal.statement (2-line proof, no new imports); update the theorem docstring with the balanced-set caveat (antecedents force μ(A) = μ(Aᶜ) = 1/2) and "median version is future work"; update the file-summary comment (lines 1920–1938, incl. section header) that references item 80.15. | **PROVED (1-line proof).** `exact ⟨fun hh => talagrand_convexDistance_tail_half (μ := μ) A hA hh ht, fun hh => talagrand_convexDistance_tail_neg (μ := μ) A hAc hh ht⟩` — each side is an independent implication (80.5 on `A`, 80.10 on `Aᶜ`) with the half-measure hypothesis moved inside. | 0 errors, 0 warnings on tmp and main file; no sorry/admit/axiom (proof uses only `tail_half`/`tail_neg`, whose axioms are propext, Classical.choice, Quot.sound). Integrated: old docstring + declaration (lines 2052–2070) replaced by restructured `talagrand_convexDistance_two_sided` (now line 2093) with the item-80.16 docstring (independent implications, balanced-set μ(A) = μ(Aᶜ) = 1/2, median-based P(|f − med f| ≥ t) ≤ 4e^(−t²/4) via A₋ = {f ≤ m}, A₊ = {f ≥ m} reserved as future work); file-summary header (line 1921) and bullet (lines 1936–1940) updated to reference item 80.16. `tmp_two_sided.lean` deleted. | `tmp_two_sided.lean` |

### 80.20. talagrand_convexDistance_integral_le_one_div

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
    - note: |
        GPT-review follow-up (point 2): the main-theorem docstring claims
        "Equivalently, ∫ exp(d_A²/4) dμ ≤ 1 / μ(A)" unconditionally, which is FALSE
        when μ(A) = 0 (Lean reals: 1/0 = 0, so it would claim I ≤ 0). This item
        formalizes the correct conditional form and fixes that comment (~line 1558).
- **informal**
    - statement: |
        When $0 < \mu(A)$:
        $$\int_\Omega \exp(d_A(x)^2/4)\,d\mu(x) \le 1/\mu(A).$$
        Lean:
        ```lean
        (A : Set ((i : Fin n) → Ω i)) (hA : A.Nonempty)
          (hμ : 0 < (Measure.pi μ A).toReal) :
          ∫ x, Real.exp ((convexDistance x A) ^ 2 / 4) ∂(Measure.pi μ) ≤
            1 / (Measure.pi μ A).toReal
        ```
        Also fix the main theorem docstring (~line 1558): replace "Equivalently,
        `∫ ≤ 1 / μ(A)`" with "Equivalently, when `0 < μ(A)`, `∫ ≤ 1 / μ(A)`
        (see item 80.20)".
    - proof: |
        From `talagrand_convexDistance` (60.10): `pA * I ≤ 1` where
        `pA = (Measure.pi μ A).toReal`. With `0 < pA`, `(le_div_iff₀ hμ).2`
        after `simpa [mul_comm]` gives `I ≤ 1 / pA`. ~5 lines, no new imports.
- **prep**
    - `talagrand_convexDistance` (item 60.10) — main theorem, in `ConvexDistance.lean`
    - `le_div_iff₀` — exact mathlib statement: `(hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b`
      (in `Mathlib.Algebra.Order.GroupWithZero.Basic`, transitively imported).
      Instantiate `a := I`, `b := 1`, `c := pA`, then `simpa [mul_comm]`.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-14 | 1 / 15 | done | Prove `talagrand_convexDistance_integral_le_one_div` with `(hμ : 0 < (Measure.pi μ A).toReal)`: from `talagrand_convexDistance` get `pA * I ≤ 1`, apply `(le_div_iff₀ hμ).2` after `simpa [mul_comm]`; fix the main-theorem docstring "Equivalently, ∫ ≤ 1 / μ(A)" (~line 1558) to the conditional form "when `0 < μ(A)` (see item 80.20)". | **PROVED (1-line proof).** `exact (le_div_iff₀ hμ).2 (by simpa [mul_comm] using talagrand_convexDistance (μ := μ) A hA)` — divides `μ(A) · ∫ exp(d_A²/4) dμ ≤ 1` by `μ(A) > 0`. | 0 errors, 0 warnings on tmp and main file; no sorry/admit/axiom (proof uses only `talagrand_convexDistance` and `le_div_iff₀`, whose axioms are propext, Classical.choice, Quot.sound). Integrated: theorem inserted at line 2070 (right after `talagrand_convexDistance_tail_neg`, before two_sided) with docstring noting it is the correct conditional form of the "1/μ(A)" equivalence (GPT-review point 2); main-theorem docstring (~line 1558) fixed to the conditional form; file-summary bullet added. `tmp_integral_le_one_div.lean` deleted. | `tmp_integral_le_one_div.lean` |

---
## 90. Classical Equivalence

Formalize the equivalence between our `convexDistance` (infimum over the convex hull)
and the classical dual/supremum form (Pollard 2006):
$$D(x,A) = \sup_{\substack{w \ge 0,\ \|w\| \le 1}} \inf_{y \in A} \sum_i w_i\, 1_{x_i \ne y_i}.$$
This closes the interface loop recommended by the GPT review
(doc/talagram/03_gpt_review/2026_08_14.md, final remark).

### 90.1. iInf_inner_convexHull

- **meta**
    - kind: lemma
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For any `w : EuclideanSpace ℝ (Fin n)` and any set `M` in `EuclideanSpace ℝ (Fin n)`
        (in applications: `M = mismatchVector x '' A`), taking the convex hull does not
        change the infimum of the linear functional `w ⬝ᵥ ·`:
        $$\inf_{z \in \mathrm{conv}(M)} w \cdot z = \inf_{v \in M} w \cdot v.$$
        Pure convex algebra — no topological assumptions needed.
        Lean (recommended): `(⨅ z ∈ convexHull ℝ M, w ⬝ᵥ z) = ⨅ v ∈ M, w ⬝ᵥ v`.
        No `M.Nonempty` hypothesis: for `M = ∅` both sides are `⊤` (`convexHull_empty`),
        so the empty case is free.
    - proof: |
        (≤): `M ⊆ convexHull ℝ M` (`subset_convexHull`), and iInf is antitone in the set
        — `biInf_mono` (VERIFIED; `iInf_le_iInf` / `Set.iInf_mono` do NOT exist).
        (≥): for `z ∈ convexHull ℝ M`, write z as a finite convex combination
        `z = Σ λᵢ • vᵢ`, `vᵢ ∈ M`, `λᵢ ≥ 0`, `Σ λᵢ = 1` via
        `mem_convexHull_iff_exists_fintype` (VERIFIED, `Mathlib.Analysis.Convex.Combination`).
        Then `w ⬝ᵥ z = Σ λᵢ (w ⬝ᵥ vᵢ) ≥ Σ λᵢ · (⨅ v ∈ M, w ⬝ᵥ v) = ⨅ v ∈ M, w ⬝ᵥ v`
        (bilinearity via `inner_sum` + `inner_smul_right`; termwise via `iInf₂_le`,
        `smul_le_smul_of_nonneg_left`, `Finset.sum_le_sum`; the trailing equality via
        `Finset.sum_mul`). Close with `le_iInf₂_iff`.
- **prep**
    - `mem_convexHull_iff_exists_fintype` (`Mathlib.Analysis.Convex.Combination`) — `x ∈ convexHull R s ↔ ∃ ι [Fintype ι] w z, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ (∀ i, z i ∈ s) ∧ ∑ i, w i • z i = x`
    - `mem_convexHull_of_exists_fintype` — reverse direction, explicit (universe-polymorphic version)
    - `convexHull_eq` (`Mathlib.Analysis.Convex.Combination`) — alternative `Finset.centerMass` characterization
    - `Set.Finite.convexHull_eq_image` (`Mathlib.Analysis.Convex.StdSimplex`, NOT Combination) — finite `s`: hull = linear image of `stdSimplex R s`; not needed here (used by 90.2)
    - `subset_convexHull` (`Mathlib.Analysis.Convex.Hull`) — `s ⊆ convexHull 𝕜 s`
    - `convexHull_empty` — `convexHull 𝕜 ∅ = ∅` (empty case automatic)
    - `biInf_mono` (`Mathlib.Order.CompleteLattice.Basic`) — `(∀ i, p i → q i) → (⨅ i, ⨅ _ : q i, f i) ≤ (⨅ i, ⨅ _ : p i, f i)`; gives (≤)
    - `le_iInf₂_iff` — `a ≤ (⨅ i, ⨅ j, f i j) ↔ ∀ i j, a ≤ f i j`; final step of (≥)
    - `iInf₂_le` — `(⨅ i, ⨅ j, f i j) ≤ f i j`; termwise bound from `vᵢ ∈ M`
    - `iInf_image` (`Mathlib.Order.CompleteLattice.Basic`, to_dual of `iSup_image`) — `(⨅ c ∈ f '' t, g c) = ⨅ b ∈ t, g (f b)` (needed in 90.3)
    - `inner_sum` (`Mathlib.Analysis.InnerProductSpace.Basic`) — `⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫`
    - `inner_smul_right` — `⟪x, r • y⟫ = r * ⟪x, y⟫`
    - `smul_le_smul_of_nonneg_left` (`Mathlib.Algebra.Order.Module.Defs`, @[gcongr]) — `b₁ ≤ b₂ → 0 ≤ a → a • b₁ ≤ a • b₂`
    - `Finset.sum_le_sum` — termwise sum inequality
    - `Finset.sum_mul` / `Finset.mul_sum` (`Mathlib.Algebra.BigOperators.Ring.Finset`) — `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`, for the `(∑ λᵢ) • b = b` step
    - NOT in mathlib (removed): `mem_convexHull_iff_exists_finset`, `exists_convex_convexHull_mem`, `iInf_le_iInf`, `Set.iInf_mono`, `inner_comm` (real version is `real_inner_comm`; not needed here)
    - KEY INSIGHT (affects 90.3): on ℝ, `⨅ v ∈ M, f v` is the CONDITIONAL `sInf`
      (`Real.sInf_empty : sInf (∅ : Set ℝ) = 0`), NOT `⊤`. The generic
      complete-lattice argument fails; the proof needs a `BddBelow` case split on
      `Set.range (fun v => ⨅ _ : v ∈ M, f v)` — the unbounded branch gives both
      sides equal 0 via `csInf_of_not_bddBelow`. For `M = ∅` both sides are 0
      (each pointwise iInf over an empty Prop is 0, so each range is `{0}`),
      handled by the bounded branch, not by a `⊤` argument. Also: `ciInf_le hB (z' i)`
      needs the `BddBelow` hypothesis on ℝ — hence the split.
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-14 | 1 / 15 | done | Prove `iInf_inner_convexHull` in `tmp_bridge.lean`: `(⨅ z ∈ convexHull ℝ M, w ⬝ᵥ z) = ⨅ v ∈ M, w ⬝ᵥ v` for `w : EuclideanSpace ℝ (Fin n)`, `M : Set (EuclideanSpace ℝ (Fin n))` — no `M.Nonempty` (empty case free via `convexHull_empty`); (≤) by `biInf_mono` + `subset_convexHull`, (≥) by `mem_convexHull_iff_exists_fintype` + `inner_sum` + `inner_smul_right` + `smul_le_smul_of_nonneg_left` + `sum_le_sum` + `le_iInf₂_iff` | **PROVED.** Naive calc fails because on ℝ `⨅ v ∈ M, f v` is the CONDITIONAL sInf (`sInf ∅ = 0`, not ⊤), so the proof is a `BddBelow` case split on `Set.range (fun v => ⨅ _ : v ∈ M, w ⬝ᵥ v)`. (i) Bounded branch: `hsubset` (M-range ⊆ hull-range, cases on membership with 0 as fallback witness); for `z ∈ convexHull ℝ M` via `mem_convexHull_iff_exists_fintype` (`z = ∑ a i • z' i`, `a i ≥ 0`, `∑ a = 1`), termwise `ciInf_le hB (z' i)`, then `sum_le_sum` + `mul_le_mul_of_nonneg_left`; bilinearity via helpers `dot_eq_inner` (`w ⬝ᵥ x = ⟪x, w⟫_ℝ` via `EuclideanSpace.inner_eq_star_dotProduct`) and `inner_sum_smul`; directions closed by `csInf_le_csInf` (with `hc_le_zero`: 0 is always in the M-range) and `le_ciInf`. (ii) Unbounded branch: both sInfs are 0 via `csInf_of_not_bddBelow` (hull-range ⊇ M-range so also unbounded via `BddBelow.mono`). Extra helpers: `iInf_prop_const_of_mem`/`_of_not` (pointwise iInf over inhabited/empty Prop = a / 0); local notation `⟪x, y⟫_ℝ` for `inner ℝ x y`. | Verified independently. tmp compiled 0 errors 0 warnings; no sorry/admit/axiom; `#print axioms iInf_inner_convexHull` = [propext, Classical.choice, Quot.sound] only. BddBelow split read and confirmed correct (no hidden assumptions: `hsubset` proved before the split; unbounded branch is a valid `BddBelow.mono` contradiction; empty-M case handled by the bounded branch since both ranges are `{0}`). Integrated into `ConvexDistance.lean`: added import `Mathlib.Analysis.Convex.Combination` (needed for `mem_convexHull_iff_exists_fintype`); new section `/-! # Classical Dual Form (Blueprint Items 90.1-90.3) -/` appended at end of file (theorem at lines ~2152-2240); helpers kept `private`, local notation kept but scoped inside `section ClassicalDualForm`. `tmp_bridge.lean` deleted. Main file re-checked: 0 errors 0 warnings; full `lake build` clean. | `tmp_bridge.lean` |

### 90.2. convexMismatchSet_nearest_point

- **meta**
    - kind: lemma
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For `K = convexMismatchSet x A` with `A.Nonempty`, the nearest-point machinery:
        (a) `IsCompact K` (hence `IsClosed K`) — needs `[∀ i, Fintype (Ω i)]`;
        (b) `∃ z ∈ K, ‖z‖ = Metric.infDist 0 K`;
        (c) for that z, `∀ u ∈ K, z ⬝ᵥ (u − z) ≥ 0` (variational inequality);
        (d) `∀ i, 0 ≤ z i` (K lies in the nonneg orthant).
        May be split into several named lemmas; the package is the item.
        IMPORTANT: `EuclideanSpace ℝ (Fin n)` (= `PiLp 2 _`) has NO order (LE) instance,
        so the orthant is `{v | ∀ i, 0 ≤ v i}` — coordinatewise, never `0 ≤ v`.
    - proof: |
        (a) `mismatchVector x '' A` is finite (via `[∀ i, Fintype (Ω i)]`:
        `Set.finite_univ` + `Set.Finite.subset` + `Set.Finite.image`); convex hull of a
        FINITE set is compact: `Set.Finite.isCompact_convexHull`
        (`Mathlib.Analysis.Convex.Topology` — VERIFIED; `IsCompact.convexHull` does NOT
        exist, no `Mathlib.Analysis.Convex.Compact` module). Closedness via
        `IsCompact.isClosed` (T2).
        (b) nearest point: `IsCompact.exists_infDist_eq_dist` (VERIFIED,
        HausdorffDistance) gives `∃ z ∈ K, infDist 0 K = dist 0 z`; `dist_zero_left`
        (to_additive of `dist_one_left`) converts to `‖z‖ = infDist 0 K`. No need for
        `exists_isMinOn` + `infDist_eq_iInf` juggling.
        (c) For `ε ∈ [0,1]`, `z + ε • (u − z) ∈ K` via `Convex.add_smul_sub_mem` (exact
        fit); `‖z‖² ≤ ‖z + ε•(u−z)‖² = ‖z‖² + 2ε ⟪z,u−z⟫_ℝ + ε² ‖u−z‖²`
        (`norm_add_sq_real` + `real_inner_smul_right` + `norm_smul_of_nonneg`).
        Divide by `ε > 0`; pass to the limit with the SEQUENCE `ε_k = 1/(k+1)`
        (`tendsto_one_div_add_atTop_nhds_zero_nat` + `ge_of_tendsto`).
        (Derivative route NOT recommended: `hasDerivAt_norm_sq` does NOT exist; would
        need hand-built HasFDerivAt + `IsLocalMinOn.hasFDerivWithinAt_nonneg` + tangent
        cone glue.)
        (d) every mismatch vector is {0,1}-valued (`mismatchVector_apply`, main file
        line 50 — the blueprint name `mismatchVector_coord` is wrong), so
        `mismatchVector x '' A ⊆ {v | ∀ i, 0 ≤ v i}`; the orthant is convex
        (`convex_pi` + `convex_Ici` on the pi type, pulled back through the linear
        equivalence `EuclideanSpace.equiv (Fin n) ℝ` via `Convex.linear_preimage` —
        the pullback is DEFINITIONALLY the orthant since `⇑(PiLp.continuousLinearEquiv) =
        ofLp` is rfl); then `convexHull_min`.
- **prep**
    - `Set.Finite.isCompact_convexHull` (`Mathlib.Analysis.Convex.Topology` — NEW IMPORT) — `{s : Set E} (hs : s.Finite) : IsCompact (convexHull 𝕜 s)`; needs `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜] [ContinuousAdd 𝕜]` + `[IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]` — all available for 𝕜 = ℝ (`IsOrderedRing.toIsStrictOrderedRing`, `ConditionallyCompleteLinearOrder.toCompactIccSpace`) and `E = EuclideanSpace ℝ (Fin n)`. NOTE: `IsCompact.convexHull` does NOT exist; module `Mathlib.Analysis.Convex.Compact` does not exist.
    - `Set.Finite.isClosed_convexHull` (same module, extra `[T2Space E]`) — closedness of finite-set hull directly (alternative to compact→closed)
    - `Set.finite_univ` (`Mathlib.Data.Set.Finite.Basic`, instance) — `(univ : Set α).Finite` given `[Finite α]`
    - `Set.Finite.subset` — `(hs : s.Finite) → t ⊆ s → t.Finite`
    - `Set.Finite.image` — `(f : α → β) → s.Finite → (f '' s).Finite`
    - `Set.Nonempty.image` (`Mathlib.Data.Set.Image`) — `s.Nonempty → (f '' s).Nonempty`
    - `Set.Nonempty.mono` — `(ht : s ⊆ t) → s.Nonempty → t.Nonempty` (note arg order)
    - `IsCompact.isClosed` (`Mathlib.Topology.Separation.Hausdorff`) — `[T2Space X] → IsCompact s → IsClosed s`
    - `IsCompact.exists_infDist_eq_dist` (`Mathlib.Topology.MetricSpace.HausdorffDistance`, imported) — `(h : IsCompact s) → (hne : s.Nonempty) → (x : α) → ∃ y ∈ s, infDist x s = dist x y` — PRIMARY route for (b)
    - `Metric.infDist_eq_iInf` (same module) — VERIFIED: `infDist x s = ⨅ y : s, dist x y` (only needed for 90.3, not for (b) itself)
    - `Metric.infDist_le_dist_of_mem` (same module) — `(h : y ∈ s) → infDist x s ≤ dist x y` (90.3's prep previously wrote `infDist_le_dist` — WRONG name)
    - `dist_zero_left` (`Mathlib.Analysis.Normed.Group.Basic`, to_additive of `dist_one_left`) — `dist 0 a = ‖a‖`; `dist_zero_right` is the `[simp]`-tagged variant
    - `IsCompact.exists_isMinOn` (`Mathlib.Topology.Order.Compact`) — `[ClosedIicTopology α] → IsCompact s → s.Nonempty → ContinuousOn f s → ∃ x ∈ s, IsMinOn f s x` — ALTERNATIVE route for (b), not needed
    - `convex_convexHull` (`Mathlib.Analysis.Convex.Hull`, imported) — `Convex 𝕜 (convexHull 𝕜 s)`
    - `Convex.add_smul_sub_mem` (`Mathlib.Analysis.Convex.Basic`, imported via Combination) — `(h : Convex 𝕜 s) → x ∈ s → y ∈ s → {t : 𝕜} → t ∈ Icc (0 : 𝕜) 1 → x + t • (y - x) ∈ s` — EXACT fit for (c)
    - `norm_add_sq_real` (`Mathlib.Analysis.InnerProductSpace.Basic`) — `‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2`
    - `real_inner_smul_right` (same module) — `⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ`
    - `norm_smul_of_nonneg` (`Mathlib.Analysis.Normed.Module.RCLike.Real`) — `0 ≤ t → ‖t • x‖ = t * ‖x‖`
    - `real_inner_self_eq_norm_sq` (`Mathlib.Analysis.InnerProductSpace.Basic`) — `⟪x, x⟫_ℝ = ‖x‖ ^ 2` (used in 90.3, not strictly needed for (c))
    - `ge_of_tendsto` (`Mathlib.Topology.Order.OrderClosed`, to_dual of `le_of_tendsto`) — `[NeBot x] → Tendsto f x (𝓝 a) → (∀ᶠ c in x, b ≤ f c) → b ≤ a` — ε → 0 limit step
    - `tendsto_one_div_add_atTop_nhds_zero_nat` (`Mathlib.Analysis.SpecificLimits.Basic` — NEW IMPORT) — `Tendsto (fun n : ℕ ↦ 1 / ((n : 𝕜) + 1)) atTop (𝓝 0)`
    - `Filter.Tendsto.add` / `.mul_const` / `tendsto_const_nhds` (`Mathlib.Topology.Algebra.Order.Limits`-ish, standard) — assembling the limit
    - `nonneg_of_mul_nonneg_right` — `0 ≤ a * b → 0 < b → 0 ≤ a` (dividing by 2 at the end)
    - `mismatchVector_apply` (main file, line 50) — `mismatchVector x y i = if x i = y i then (0 : ℝ) else (1 : ℝ)` (VERIFIED name; blueprint previously said `mismatchVector_coord` — WRONG)
    - `convex_pi` (`Mathlib.Analysis.Convex.Basic`) — `Convex 𝕜 (s.pi t)` from coordinatewise convexity
    - `convex_Ici` (same module) — `Convex 𝕜 (Ici r)` for `[AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]`
    - `Convex.linear_preimage` (same module) — `Convex 𝕜 s → (f : E →ₗ[𝕜] F) → Convex 𝕜 (f ⁻¹' s)`; apply with `(EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.toLinearMap` — pullback is definitionally the orthant (`coe_continuousLinearEquiv : ⇑(PiLp.continuousLinearEquiv p 𝕜 β) = ofLp` is rfl)
    - `convexHull_min` (`Mathlib.Analysis.Convex.Hull`) — `s ⊆ t → Convex 𝕜 t → convexHull 𝕜 s ⊆ t`
    - `PiLp.smul_apply` / `PiLp.add_apply` (`Mathlib.Analysis.Normed.Lp.PiLp`, `[simp]`, rfl) — `(c • x) i = c • x i`, `(x + y) i = x i + y i` (needed by 90.3 for `0 ≤ (‖z‖⁻¹ • z) i`)
    - NOT in mathlib (removed from prep): `IsCompact.convexHull`, `Metric.infDist_eq_sInf`, `hasDerivAt_norm_sq`, `hasFDerivAt_norm_sq`, `mismatchVector_coord`, `Set.Finite.isCompact` (unneeded — `isCompact_convexHull` subsumes it), `Metric.infDist_le_dist` (real name: `infDist_le_dist_of_mem`)
    - MATHLIB v4.32 DIVERGENCES (from attempt 1): (i) `sq_le_sq` does NOT exist → use
      `sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)`; (ii) `eventually_of_forall` does NOT
      exist → use `Filter.mem_of_superset Filter.univ_mem`; (iii) the
      `Convex.linear_preimage` pullback route for the orthant was SKIPPED:
      `PiLp`/`WithLp` is a type synonym so `Set.pi univ …` is not defeq the orthant —
      used a direct 5-line convexity check instead; (iv)
      `EuclideanSpace.inner_eq_star_dotProduct` has swapped argument order → apply
      `real_inner_comm` first.
    - KEY INSIGHT 1 (affects 90.3): no `LE` instance on `PiLp`/`EuclideanSpace` — every "`w ≥ 0`" statement must be coordinatewise `∀ i, 0 ≤ w i`; the package lemma returns `∀ i, 0 ≤ z i`.
    - KEY INSIGHT 2 (affects 90.3): compactness of `convexMismatchSet x A` requires `[∀ i, Fintype (Ω i)]` (the hull of a finite set in `EuclideanSpace ℝ (Fin n)` is compact). 90.3's statement must carry this hypothesis (or `A.Finite`).
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-14 | 1 / 15 | done | Prove the 90.2 nearest-point package in `tmp_bridge.lean` (section `ClassicalDualForm` of `ConvexDistance.lean`): (a) `convexMismatchSet_isCompact` / `convexMismatchSet_isClosed` via `Set.Finite.isCompact_convexHull` (+ `Set.finite_univ`/`Finite.subset`/`Finite.image`); (b) generic `exists_norm_eq_infDist_zero {E} [NormedAddCommGroup E] (K) (hK : IsCompact K) (hne : K.Nonempty) : ∃ z ∈ K, ‖z‖ = Metric.infDist (0 : E) K` via `IsCompact.exists_infDist_eq_dist` + `dist_zero_left`; (c) generic `variational_inequality_nearest_point {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K) (hKconv : Convex ℝ K) (z) (hz : z ∈ K) (hzmin : ∀ u ∈ K, ‖z‖ ≤ ‖u‖) : ∀ u ∈ K, 0 ≤ ⟪z, u - z⟫_ℝ` via `Convex.add_smul_sub_mem` + `norm_add_sq_real` + `real_inner_smul_right` + `norm_smul_of_nonneg`, ε_k = 1/(k+1) limit via `tendsto_one_div_add_atTop_nhds_zero_nat` + `ge_of_tendsto`; (d) `convexMismatchSet_subset_nonneg : convexMismatchSet x A ⊆ {v | ∀ i, 0 ≤ v i}` via `convexHull_min` + `convex_pi`/`convex_Ici`/`Convex.linear_preimage` + `mismatchVector_apply`; assemble `convexMismatchSet_nearest_point` package (∃ z ∈ K, ‖z‖ = infDist 0 K ∧ ∀ u ∈ K, 0 ≤ z ⬝ᵥ (u − z) ∧ ∀ i, 0 ≤ z i). New imports: `Mathlib.Analysis.Convex.Topology`, `Mathlib.Analysis.SpecificLimits.Basic`. | **PROVED.** All six declarations. (a) `convexMismatchSet_isCompact`/`isClosed` via `Set.Finite.isCompact_convexHull` (image of `Set.Finite.subset Set.finite_univ`). (b) generic `exists_norm_eq_infDist_zero` via `IsCompact.exists_infDist_eq_dist` + `dist_zero_left`. (c) `variational_inequality_nearest_point`: for t ∈ (0,1], `z + t•(u−z) ∈ K` via `Convex.add_smul_sub_mem`; expand `‖z‖² ≤ ‖z + t•(u−z)‖²` (`norm_add_sq_real` + `real_inner_smul_right` + `norm_smul_of_nonneg`), divide by t > 0 (`nonneg_of_mul_nonneg_right`) → `0 ≤ 2⟪z,u−z⟫ + t‖u−z‖²`; limit t_k = 1/(k+1) → 0 via `tendsto_one_div_add_atTop_nhds_zero_nat` + `ge_of_tendsto` (membership t_k ∈ [0,1]: `div_le_one` with k ≥ 0); finish with `nonneg_of_mul_nonneg_right` (divide by 2). (d) `convexMismatchSet_subset_nonneg` via `convexHull_min`: generators {0,1}-valued (`mismatchVector_apply` case split); orthant convexity by direct 5-line check (nlinarith + mul_nonneg) — planned `Convex.linear_preimage` pullback SKIPPED (PiLp/WithLp type synonym: `Set.pi univ` not defeq the orthant). Assembly: K compact + nonempty (from `hA` via `subset_convexHull`) + convex (`convex_convexHull`); nearest z from (b); hzmin via `Metric.infDist_le_dist_of_mem` + hznorm; inner→dot conversion via `real_inner_comm` then `EuclideanSpace.inner_eq_star_dotProduct` (v4.32 swapped arg order) — conclusion is the dotProduct form `0 ≤ z ⬝ᵥ (u − z)`; coordinatewise nonneg from (d). Mathlib v4.32 divergences recorded in prep. | Verified independently. tmp compiled 0 errors 0 warnings (132 lines); no sorry/admit/axiom/native_decide; `#print axioms` on all six declarations = [propext, Classical.choice, Quot.sound] only. Proof read and confirmed correct: t_k = 1/(k+1) ∈ [0,1] for all k (positivity + `div_le_one`), division by positive t_k, `ge_of_tendsto` applied to the atTop-eventually-everywhere inequality (`Filter.mem_of_superset Filter.univ_mem` since `eventually_of_forall` does not exist in v4.32); `sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)` in place of nonexistent `sq_le_sq`; orthant convexity is a genuine direct Convex check (a,b ≥ 0, a+b = 1, coordinatewise nlinarith with mul_nonneg) and `convexHull_min` is applied correctly; final conclusion is the dotProduct `0 ≤ z ⬝ᵥ (u − z)` as stated. Integrated into `ConvexDistance.lean`: added imports `Mathlib.Analysis.Convex.Topology` + `Mathlib.Analysis.SpecificLimits.Basic` (lines 16-17); six declarations inserted at end of existing `section ClassicalDualForm` (lines 2246-2358, before its `end` at 2359); notation not re-declared, `Filter.`-qualified names kept. Main file: 0 errors, 0 warnings, 0 sorries; full `lake build` passes. `tmp_bridge.lean` deleted. | `tmp_bridge.lean` |

### 90.3. convexDistance_eq_dual

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
- **informal**
    - statement: |
        For `A.Nonempty`:
        $$d_A(x) = \sup\bigl\{ r \,\big|\, \exists w : \mathrm{EuclideanSpace}\;\mathbb{R}\;(\mathrm{Fin}\;n),\ \|w\| \le 1,\ 0 \le w,\ r = \inf_{y \in A} w \cdot v(x,y) \bigr\}.$$
        Lean (CORRECTED by 90.3 survey — see correction (iii)):
        ```lean
        convexDistance x A = sSup {r | ∃ w : EuclideanSpace ℝ (Fin n),
          ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧ r = ⨅ y : A, w ⬝ᵥ mismatchVector x y}
        ```
        This is the classical dual form of Talagrand's convex distance (Pollard 2006).
        CORRECTIONS (from 90.2 survey): (i) `0 ≤ w` must be coordinatewise
        `∀ i, 0 ≤ w i` — `EuclideanSpace ℝ (Fin n)` has NO order instance;
        (ii) the theorem needs `[∀ i, Fintype (Ω i)]` (compactness of
        `convexMismatchSet x A`, needed for the (≥) direction via 90.2);
        (iii) (from 90.3 survey) the iInf MUST be the subtype form `⨅ y : A, …`,
        NOT `⨅ y ∈ A, …`. On ℝ the set-membership form elaborates to
        `⨅ y, ⨅ _ : y ∈ A, …` and for `y ∉ A` the inner iInf is `sInf ∅ = 0`
        (`Real.sInf_empty`; cf. `iInf_prop_const_of_not` in the 90.1 proof), so with
        `w ⬝ᵥ v(x,y) ≥ 0` the whole expression collapses to `0` for any proper
        nonempty `A` (counterexample: `n = 1`, `A = {0} ⊊ Ω`, `x ≠ 0` gives
        `convexDistance = 1` but RHS = `sSup {0} = 0`). The subtype iInf
        `⨅ y : A, …` is the true inf over `A` and matches `Metric.infDist_eq_iInf`'s
        subtype form directly. Same degeneracy means the integrated 90.1 theorem
        (both sides `⨅ v ∈ M`) has degenerate content for nonneg functionals —
        the (≤) direction must REPLICATE 90.1's bounded-branch argument
        (`mem_convexHull_iff_exists_fintype` convex combination) as a tmp helper
        with a subtype-iInf LHS instead of applying 90.1 directly.
    - proof: |
        Let `d := convexDistance x A`, `K := convexMismatchSet x A` (so `d = infDist 0 K` by rfl),
        `S := {r | ∃ w, ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧ r = ⨅ y : A, w ⬝ᵥ mismatchVector x y}`.
        (≤): for admissible w and every `z ∈ K`:
        (i) `r := ⨅ y : A, w ⬝ᵥ mismatchVector x y ≤ w ⬝ᵥ z` via the 90.1 bounded-branch
        argument replicated for the subtype iInf (tmp helper
        `iInf_subtype_dot_le_of_mem_convexHull`, hypotheses: M nonempty, M ⊆ nonneg orthant,
        w coordinatewise nonneg, `BddBelow` of the range by 0);
        (ii) `w ⬝ᵥ z ≤ ⟪z, w⟫_ℝ ≤ ‖z‖ * ‖w‖ ≤ ‖z‖` (`real_inner_le_norm` — DIRECT
        Cauchy–Schwarz for ℝ, no abs dance needed; `mul_le_mul_of_nonneg_right` with `‖w‖ ≤ 1`,
        `norm_nonneg`);
        (iii) `r ≤ ⨅ z : K, ‖z‖` via `le_ciInf` (needs only `[Nonempty K]`, from `hA` —
        NO BddBelow needed);
        (iv) `⨅ z : K, ‖z‖ = ⨅ z : K, dist 0 ↑z = infDist 0 K = d` (`dist_zero_left`,
        `Metric.infDist_eq_iInf` — the subtype form matches directly; `convexDistance` defn).
        So `∀ r ∈ S, r ≤ d`; then `BddAbove S = ⟨d, …⟩`, `S.Nonempty` (w = 0 candidate:
        `zero_dotProduct` + `ciInf_const` with `[Nonempty A]`), and `sSup S ≤ d` via
        `csSup_le` (`sSup_le_iff` is CompleteLattice-only — NOT on ℝ).
        (≥): package 90.2 gives `z ∈ K`, `‖z‖ = infDist 0 K = d`, `∀ u ∈ K, 0 ≤ z ⬝ᵥ (u − z)`,
        `∀ i, 0 ≤ z i`.
        If `z = 0`: `d = 0`, candidate `w = 0` gives `r = 0 = d`.
        If `z ≠ 0`: `w = ‖z‖⁻¹ • z`; `‖w‖ = 1` (`norm_smul` + `Real.norm_of_nonneg
        (inv_nonneg_of_nonneg (norm_nonneg z))` + `inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)`);
        `∀ i, 0 ≤ w i` via `PiLp.smul_apply` + `mul_nonneg`. For `y : A`, `u := mismatchVector
        x y ∈ K` (`subset_convexHull`): `0 ≤ z ⬝ᵥ (u − z)` → (`dotProduct_sub`) `‖z‖² ≤
        z ⬝ᵥ u` (via `z ⬝ᵥ z = ⟪z, z⟫_ℝ = ‖z‖²`: dot→inner conversion as in 90.1/90.2 plus
        `real_inner_self_eq_norm_sq`; NO `dotProduct_self` in mathlib) → (`smul_dotProduct`,
        `mul_le_mul_of_nonneg_left` with `inv_nonneg (norm_nonneg z)`) `‖z‖⁻¹ • ‖z‖² ≤
        w ⬝ᵥ u` → (`sq`, `inv_mul_cancel₀`, `norm_pos_iff.mpr hz`) `d = ‖z‖ ≤ w ⬝ᵥ u`.
        Hence `d ≤ ⨅ y : A, w ⬝ᵥ mismatchVector x y` via `le_ciInf`; combined with (≤):
        `r = d`, so `d ∈ S`, and `d ≤ sSup S` via `le_csSup` (BddAbove S, d ∈ S —
        note arg order: BddAbove FIRST). Close with `le_antisymm`.
- **prep**
    - `iInf_inner_convexHull` (90.1, integrated main file) — statement is degenerate on ℝ for nonneg functionals (see correction (iii)); its bounded-branch PROOF PATTERN gets replicated in the tmp helper `iInf_subtype_dot_le_of_mem_convexHull` with a subtype-iInf LHS. NOT applied directly.
    - `convexMismatchSet_nearest_point` package (90.2, integrated main file) — `∃ z ∈ K, ‖z‖ = Metric.infDist 0 K ∧ (∀ u ∈ K, 0 ≤ z ⬝ᵥ (u − z)) ∧ ∀ i, 0 ≤ z i`; needs `[∀ i, DecidableEq (Ω i)] [∀ i, Fintype (Ω i)]` and `hA : A.Nonempty`
    - PRIVATE main-file helpers (90.1 section, must be COPIED into tmp): `dot_eq_inner` (`w ⬝ᵥ x = ⟪x, w⟫_ℝ` via `EuclideanSpace.inner_eq_star_dotProduct`), `inner_sum_smul` (`⟪∑ a i • z i, w⟫_ℝ = ∑ a i * ⟪z i, w⟫_ℝ` via `sum_inner` + `inner_smul_left`), `iInf_prop_const_of_mem`/`_of_not`
    - Cauchy–Schwarz: `real_inner_le_norm` (`Mathlib.Analysis.InnerProductSpace.Basic`) — VERIFIED: `inner ℝ x y ≤ ‖x‖ * ‖y‖` (DIRECT, no abs dance; `norm_inner_le_norm` = `‖inner 𝕜 x y‖ ≤ ‖x‖ * ‖y‖` is the RCLike fallback). Bridge via `real_inner_comm` (`inner ℝ y x = inner ℝ x y`) + `EuclideanSpace.inner_eq_star_dotProduct` (v4.32: swapped args + star).
    - sSup (all VERIFIED via `#check`): `csSup_le : s.Nonempty → (∀ b ∈ s, b ≤ a) → sSup s ≤ a`; `le_csSup : BddAbove s → a ∈ s → a ≤ sSup s` (NOTE arg order: BddAbove FIRST); `csSup_le_iff : BddAbove s → s.Nonempty → (sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a)`; `csSup_of_not_bddAbove : ¬BddAbove s → sSup s = sSup ∅` + `Real.sSup_empty : sSup ∅ = 0`. NOT on ℝ (CompleteLattice-only, REMOVED from prep): `sSup_le_iff`, `le_sSup`, `le_sSup_iff`.
    - iInf (all VERIFIED via `#check`): `le_ciInf : [Nonempty ι] (∀ x, c ≤ f x) → c ≤ iInf f` (NO BddBelow needed — key for both directions); `ciInf_le : BddBelow (range f) → iInf f ≤ f c` (helper's termwise step); `ciInf_const : [Nonempty ι] ⨅ x, a = a` (w = 0 candidate, task 7 — hA.Nonempty is exactly the needed Nonempty); `ciInf_mono : BddBelow (range f) → (∀ x, f x ≤ g x) → iInf f ≤ iInf g` (task 3 fallback); `le_csInf : s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s`; `csInf_le : BddBelow s → a ∈ s → sInf s ≤ a`; `le_csInf_iff`. NOT on ℝ (CompleteLattice-only, REMOVED from prep): `iInf_image`, `iInf_subtype`, `biInf_mono`, `iInf₂_mono`, `iInf₂_le`, `le_iInf₂_iff`, `iInf_le` — on ℝ use the conditional lemmas above; `Metric.infDist_eq_iInf`'s subtype form makes image bridging unnecessary.
    - `Metric.infDist_eq_iInf` — VERIFIED: `infDist x s = ⨅ y : s, dist x ↑y` (subtype iInf — matches the corrected statement directly)
    - `Metric.infDist_le_dist_of_mem` — `(h : y ∈ s) → infDist x s ≤ dist x y`
    - `dist_zero_left` — `dist 0 a = ‖a‖` (`SeminormedAddGroup`); `dist_zero_right` `[simp]` variant
    - dot algebra (root namespace `Mathlib.Data.Matrix.Mul`, VERIFIED — NOT under `Matrix.`): `dotProduct_sub : u ⬝ᵥ (v − w) = u ⬝ᵥ v − u ⬝ᵥ w`; `sub_dotProduct`; `smul_dotProduct : x • v ⬝ᵥ w = x • (v ⬝ᵥ w)` (for `w ⬝ᵥ u = ‖z‖⁻¹ * (z ⬝ᵥ u)`); `dotProduct_smul`; `zero_dotProduct : 0 ⬝ᵥ v = 0`; `dotProduct_zero`. NO `dotProduct_self` in mathlib — `z ⬝ᵥ z = ‖z‖²` goes through inner: `z ⬝ᵥ z = ⟪z, z⟫_ℝ = ‖z‖²` (`dot_eq_inner` copy + `real_inner_self_eq_norm_sq : inner ℝ x x = ‖x‖ ^ 2`).
    - scaling algebra: `norm_smul : ‖r • x‖ = ‖r‖ * ‖x‖`; `norm_smul_of_nonneg : 0 ≤ t → ‖t • x‖ = t * ‖x‖`; `norm_ne_zero_iff : ‖a‖ ≠ 0 ↔ a ≠ 0`; `norm_pos_iff : 0 < ‖a‖ ↔ a ≠ 0`; `real_inner_self_eq_norm_sq` (above); `Real.norm_eq_abs` / `Real.norm_of_nonneg`; `inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a` / `inv_nonneg_of_nonneg`; `inv_mul_cancel₀ : a ≠ 0 → a⁻¹ * a = 1`; `sq : a ^ 2 = a * a`; `PiLp.smul_apply : (c • x).ofLp i = c • x.ofLp i` (`[simp]`, for `0 ≤ (‖z‖⁻¹ • z) i`); `mul_le_mul_of_nonneg_right`/`_left`; `Finset.sum_nonneg`
    - hull: `mem_convexHull_iff_exists_fintype` (90.1-verified), `subset_convexHull` (90.1-verified), `csInf_le_csInf` (90.1-verified), `csInf_of_not_bddBelow` + `Real.sInf_empty` (90.1-verified)
    - `mismatchVector` (10.1), `convexDistance` (10.10, def = `Metric.infDist 0 (convexMismatchSet x A)`), `convexMismatchSet` (10.5), `convexMismatchSet_subset_nonneg` (90.2(d), for the orthant in the tmp helper's BddBelow)
    - RECOMMENDED tmp helper (prove first): `iInf_subtype_dot_le_of_mem_convexHull {n} (w : EuclideanSpace ℝ (Fin n)) (M : Set (EuclideanSpace ℝ (Fin n))) (hM : M.Nonempty) (hMnn : M ⊆ {v | ∀ i, 0 ≤ v i}) (hw : ∀ i, 0 ≤ w i) {z} (hz : z ∈ convexHull ℝ M) : (⨅ v : M, w ⬝ᵥ v.1) ≤ w ⬝ᵥ z` — mirror of 90.1's bounded branch: `mem_convexHull_iff_exists_fintype`, termwise `ciInf_le` (BddBelow by 0 from hw + hMnn via `Finset.sum_nonneg` + `mul_nonneg`), `Finset.sum_le_sum` + `mul_le_mul_of_nonneg_left`, bilinearity via `inner_sum_smul` copy; close `(∑ a) * inf = inf` via `Finset.sum_mul` + `one_mul`. INTEGRATED NOTES: (a) the `hM : M.Nonempty` binder was DROPPED as mathematically unnecessary (linter-unused — the BddBelow-by-0 argument holds without it); (b) new helper `dot_nonneg` was ADDED (`0 ≤ w ⬝ᵥ v` for coordinatewise nonneg `w`, `v` via `Finset.sum_nonneg` + `mul_nonneg`), supplying the BddBelow-by-0 arguments in both directions
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-14 | 1 / 15 | done | Prove `convexDistance_eq_dual` in `tmp_bridge.lean` with the CORRECTED statement (subtype iInf): `convexDistance x A = sSup {r \| ∃ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ 1 ∧ (∀ i, 0 ≤ w i) ∧ r = ⨅ y : A, w ⬝ᵥ mismatchVector x y}` for `{n} {Ω} [∀ i, DecidableEq (Ω i)] [∀ i, Fintype (Ω i)] (x) (A) (hA : A.Nonempty)`. Start by proving the tmp helper `iInf_subtype_dot_le_of_mem_convexHull` (mirror of 90.1's bounded branch with subtype-iInf LHS; `mem_convexHull_iff_exists_fintype` + `ciInf_le` with BddBelow-by-0 + copied private `dot_eq_inner`/`inner_sum_smul` helpers). (≤): helper + `real_inner_le_norm` (CS) + `mul_le_mul_of_nonneg_right` (‖w‖ ≤ 1) → `r ≤ ⨅ z : K, ‖z‖` via `le_ciInf` → `= infDist 0 K = d` via `dist_zero_left` + `Metric.infDist_eq_iInf` + `convexDistance` rfl; close `sSup S ≤ d` with `csSup_le` (S.Nonempty from w = 0 candidate: `zero_dotProduct` + `ciInf_const`). (≥): 90.2 package z; case z = 0 (w = 0, r = 0 = d) and z ≠ 0 (w = ‖z‖⁻¹ • z; `norm_smul` + `Real.norm_of_nonneg` + `inv_mul_cancel₀`; `∀ i, 0 ≤ w i` via `PiLp.smul_apply`; per-y: `dotProduct_sub` + `z ⬝ᵥ z = ‖z‖²` via inner + `real_inner_self_eq_norm_sq` + `smul_dotProduct` + `inv_mul_cancel₀` → `d ≤ w ⬝ᵥ u`); `d ≤ ⨅ y : A, …` via `le_ciInf`; antisymm → r = d ∈ S; `le_csSup` (BddAbove first); `le_antisymm`. | PROVED. Added `dot_nonneg` (0 ≤ w·v for coordinatewise nonneg w, v via `Finset.sum_nonneg` + `mul_nonneg` — supplies the BddBelow-by-0 arguments) and the helper `iInf_subtype_dot_le_of_mem_convexHull` (mirror of 90.1's bounded branch, subtype-iInf LHS: `mem_convexHull_iff_exists_fintype`, BddBelow-by-0 via `dot_nonneg` + hMnn, termwise `ciInf_le`, `Finset.sum_le_sum` + `mul_le_mul_of_nonneg_left`, bilinearity via the copied private `dot_eq_inner`/`inner_sum_smul`); the blueprint's `hM : M.Nonempty` binder DROPPED as mathematically unnecessary (linter-unused). (≤): for admissible w and z ∈ K: reindex iInf over A ≤ iInf over the image `mismatchVector x '' A` via `le_ciInf` with a per-image-point preimage witness y (`rcases` the image membership, `ciInf_le` with BddBelow-by-0 from `dot_nonneg` + `mismatchVector_apply` — ONE direction only, no surjection lemma); then helper + Cauchy–Schwarz `real_inner_le_norm` + `mul_le_mul_of_nonneg_left` (‖w‖ ≤ 1, `norm_nonneg`) give r ≤ ‖z‖; `le_ciInf` over z ∈ K + `dist_zero_left` + `Metric.infDist_eq_iInf` + `convexDistance` rfl → r ≤ d; `BddAbove S` from this, `S.Nonempty` via the w = 0 candidate (`zero_dotProduct` + `ciInf_const` with `[Nonempty A]`), `csSup_le` closes sSup S ≤ d. (≥): 90.2 package gives nearest z with ‖z‖ = d, variational inequality, z ≥ 0 coordinatewise; z = 0 branch: d = 0, w = 0 candidate, `le_csSup`; z ≠ 0: w = ‖z‖⁻¹•z with ‖w‖ = 1 (`norm_smul` + `Real.norm_of_nonneg` + `inv_mul_cancel₀` of `norm_ne_zero_iff.mpr hz0`) and coordinatewise w ≥ 0 (`PiLp.smul_apply`); per y : A, u = v(x,y) ∈ K: `dotProduct_sub` + z·z = ‖z‖² via inner (`real_inner_self_eq_norm_sq`) → nlinarith gives ‖z‖² ≤ z·u → ‖z‖ = ‖z‖⁻¹·‖z‖² ≤ ‖z‖⁻¹·(z·u) = w·u via `smul_dotProduct`; `le_ciInf` gives d ≤ r, r ∈ S (witness w), `le_csSup` (BddAbove FIRST) closes d ≤ sSup S; `le_antisymm`. | Verified independently. tmp 213 lines (< 500), 0 errors / 0 warnings; no sorry/admit/axiom; `#print axioms` on both `convexDistance_eq_dual` and `iInf_subtype_dot_le_of_mem_convexHull` = [propext, Classical.choice, Quot.sound] only. Proof read line-by-line: the reindexing is a sound one-directional argument (the image family's values sit inside the A-family's values, per-point witness via the image-membership proof); BddBelow-by-0 correct (`dot_nonneg` needs w ≥ 0 and mismatch vectors ≥ 0 coordinatewise, the latter via `mismatchVector_apply`); z ≠ 0 branch sound (`‖z‖⁻¹ * ‖z‖² = ‖z‖` via `sq` + `inv_mul_cancel₀`); `csSup_le`/`le_csSup` hypotheses (S.Nonempty, BddAbove, membership) all discharged; `le_antisymm` correct. Integrated into `ConvexDistance.lean` section `ClassicalDualForm` (after `convexMismatchSet_nearest_point`, before its `end`): only the NEW declarations `dot_nonneg` (private), `iInf_subtype_dot_le_of_mem_convexHull`, `convexDistance_eq_dual` (full docstring: classical dual form per Pollard 2006, corrected subtype-iInf statement, correction (iii) narrative); the tmp's verbatim copies of `dot_eq_inner`/`inner_sum_smul` were NOT duplicated — references reuse the existing private helpers. No new imports. Main file re-checked: 0 errors / 0 new warnings. Full `lake build` passed (exit 0). `tmp_bridge.lean` deleted. | `tmp_bridge.lean` |

### 80.25. talagrand_convexDistance_two_sided (interface polish, GPT v2)

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
    - note: |
        GPT v2 review follow-up (doc/talagram/03_gpt_review/2026_08_14_v2.md, points 1, 2, 4).
        (1) Drop the explicit `(hA : A.Nonempty) (hAc : Aᶜ.Nonempty)` hypotheses: each
        antecedent `1/2 ≤ μ(·).toReal` already implies nonemptiness (an empty set has
        measure 0). (2) Remove the "GPT-review point 2" provenance from
        `talagrand_convexDistance_integral_le_one_div`'s docstring (line ~2068) — keep
        only the mathematical explanation. (4) Fix the mathematically FALSE claim in the
        two_sided docstring: the median-based bound is NOT obtained from the two set
        implications alone — it needs a separation hypothesis.
- **informal**
    - statement: |
        Same implication pair as 80.16 but WITHOUT `hA`/`hAc`:
        `(A : Set ((i : Fin n) → Ω i)) {t : ℝ} (ht : 0 ≤ t) :
        (1/2 ≤ μ(A).toReal → μ{d_A ≥ t}.toReal ≤ 2·exp(-t²/4)) ∧
        (1/2 ≤ μ(Aᶜ).toReal → μ{d_{Aᶜ} ≥ t}.toReal ≤ 2·exp(-t²/4))`.
        Docstring fixes:
        - median claim: a genuine median-based two-sided concentration theorem
          `P(|f − med f| ≥ s) ≤ 4e^(−s²/(4L²))` additionally requires a hypothesis
          relating deviations of `f` from its median to the convex distance from the
          lower/upper median sets (e.g. `f(x) ≥ m + s ⟹ d_{A₋}(x) ≥ s/L` with
          `A₋ = {f ≤ m}`, and analogously for `A₊ = {f ≥ m}`); it does NOT follow from
          the two set implications alone. Only for `L = 1` does this give `4e^(−s²/4)`.
        - `talagrand_convexDistance_integral_le_one_div` docstring: replace the
          "(GPT-review point 2)" wording with the plain mathematical reason
          (`1/0 = 0` in Lean reals makes the unconditional form false).
    - proof: |
        In each implication, derive nonemptiness from the antecedent by contradiction:
        `A = ∅` forces `(Measure.pi μ A).toReal = 0` (simp with the empty-set equality),
        contradicting `1/2 ≤ …` (nlinarith). Then apply
        `talagrand_convexDistance_tail_half` / `_tail_neg` exactly as in 80.16.
- **prep**
    - `talagrand_convexDistance_tail_half` (80.5), `talagrand_convexDistance_tail_neg` (80.10)
    - `Set.not_nonempty_iff_eq_empty` — `¬s.Nonempty ↔ s = ∅` (by-contradiction step, verified)
    - measure of the empty set: `measure_empty` (simp-normal; verified: `simp` closes
      `Measure.pi μ ∅ = 0`, no `Measure.pi_empty` lemma needed)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-14 | 1 / 15 | done | Restructure `talagrand_convexDistance_two_sided` to drop `hA`/`hAc` (derive nonempty from the half-measure antecedents by contradiction); fix the median docstring (separation hypothesis, L-scaled bound); remove the "GPT-review point 2" provenance from the integral_le_one_div docstring. | **PROVED.** `exact ⟨fun hh => let hA' : A.Nonempty := by by_contra hne; ...; nlinarith; talagrand_convexDistance_tail_half (μ := μ) A hA' hh ht, fun hh => let hAc' : Aᶜ.Nonempty := ...; talagrand_convexDistance_tail_neg (μ := μ) A hAc' hh ht⟩` — each implication arm derives nonemptiness by contradiction from its own antecedent (`A = ∅` via `Set.not_nonempty_iff_eq_empty.mp` forces `(Measure.pi μ A).toReal = 0` by simp, contradicting `1/2 ≤ …` by nlinarith; same for `Aᶜ`), then applies the 80.5/80.10 corollaries exactly as before. No new imports. | Verified independently. tmp 34 lines (< 500), 0 errors / 0 warnings; no sorry/admit/axiom; axiom check on the restructured theorem = [propext, Classical.choice, Quot.sound] only. Proof read line-by-line: both by-contradiction nonemptiness derivations correct (`not_nonempty_iff_eq_empty` + simp for measure-∅ + nlinarith against `1/2 ≤ 0`). Integrated into `ConvexDistance.lean` replacing the 80.16 block (docstring ~2082, theorem ~2096, now binders `(A) {t : ℝ} (ht : 0 ≤ t)`, no hA/hAc); new docstring states (a) each side is an independent implication, (b) both antecedents force μ(A) = μ(Aᶜ) = 1/2, (c) the genuine median bound `P(\|f − med f\| ≥ s) ≤ 4e^(−s²/(4L²))` additionally requires a deviation-to-convex-distance hypothesis (e.g. `f(x) ≥ m + s ⟹ d_{A₋}(x) ≥ s/L`, `A₋ = {f ≤ m}`, analogously `A₊ = {f ≥ m}`), does NOT follow from the two set implications alone, L = 1 gives `4e^(−s²/4)`, marked future work. Removed "(GPT-review point 2)" from `talagrand_convexDistance_integral_le_one_div`'s docstring (math explanation kept). File-summary section header + bullet updated to Item 80.25. Main file re-checked: 0 errors / 0 warnings / 0 sorries; full `lake build` passed (exit 0). `tmp_two_sided.lean` deleted. | `tmp_two_sided.lean` |

### 90.5. iInf_inner_convexHull (subtype refactor, GPT v2)

- **meta**
    - kind: theorem
    - priority: 2
    - status: done
    - attempts: 1 / 15
    - file: `StatsMLlib/Probability/Concentration/ConvexDistance.lean`
    - note: |
        GPT v2 review follow-up (point 5). The current set-membership form
        `(⨅ z ∈ convexHull ℝ M, …) = ⨅ v ∈ M, …` is degenerate on ℝ: the
        prop-indexed iInf has the `sInf ∅ = 0` fallback, so for `w ≥ 0` and
        `M ⊆` nonneg orthant (the Talagrand case) both sides collapse to
        `min(inf, 0)` and the theorem only asserts trivial content when the hull is
        proper. Nothing uses the theorem (grep-verified); refactor to the subtype form
        and delete the obsolete machinery. Survey (2026-08-15) pinned the
        SPECIALIZED subtype form with `hMnn`/`hw`/`hM` (see informal.statement).
- **informal**
    - statement: |
        **SURVEY-PINNED (2026-08-15): specialized subtype form.** Exact Lean statement:

        ```
        theorem iInf_inner_convexHull {n : ℕ} (w : EuclideanSpace ℝ (Fin n))
            (M : Set (EuclideanSpace ℝ (Fin n)))
            (hMnn : M ⊆ {v | ∀ i, 0 ≤ v i}) (hw : ∀ i, 0 ≤ w i) (hM : M.Nonempty) :
            (⨅ z : convexHull ℝ M, w ⬝ᵥ z.1) = (⨅ v : M, w ⬝ᵥ v.1)
        ```

        Rationale — general vs specialized (THE design decision):
        (i) GENERAL `hM` + `hB : BddBelow (range (fun v : M => w ⬝ᵥ v.1))` is the
        mathematically clean statement but (a) cannot reuse the 90.3 helper — it
        duplicates the convex-combination argument a second time with `ciInf_le hB`;
        (b) `hB` is an awkward hypothesis for any future consumer (in the Talagrand
        case it is exactly the free BddBelow-by-0); (c) the BddBelow-free variants
        do NOT exist on ℝ (verified): `ciInf_le'` needs
        `[ConditionallyCompleteLinearOrderBot α]` (no instance for ℝ, no bot) and
        `iInf_le_iInf_of_subset` needs `[CompleteLattice α]` (and is prop-indexed).
        (ii) SPECIALIZED (CHOSEN): matches the Talagrand setting exactly
        (`M = mismatchVector x '' A` lies in the orthant by 90.2(d); admissible
        `w ≥ 0`); consistent with the 90.3 helper
        `iInf_subtype_dot_le_of_mem_convexHull` (same `hMnn`/`hw` hypotheses);
        drops ALL `BddBelow` hypotheses (M-side free by 0 inside the helper;
        hull-side derived from the pointwise (≥) bound with bound = the M-iInf
        itself).
        `hM` IS required: `le_ciInf` needs `[Nonempty ι]` on BOTH index types
        (verified v4.32 shape); hull nonemptiness follows from `hM` via
        `subset_convexHull`. The `hM`-free alternative (by_cases on emptiness) is
        provable — verified `(⨅ v : (∅ : Set E), w ⬝ᵥ v.1) = 0` and
        `(⨅ z : convexHull ℝ (∅ : Set E), w ⬝ᵥ z.1) = 0` via `iInf_of_isEmpty` +
        `Real.sInf_empty` + manual `IsEmpty` instance `⟨fun v => v.2⟩` (no automatic
        instance for empty subtypes in v4.32) + `convexHull_empty` — but adds ~8
        lines of machinery for a degenerate case nobody consumes. Chosen: `hM`.
        Integration (Review): delete the old 90.1 theorem (main file ~2177-2263) and
        the two prop-const helpers (~2142-2149); KEEP `dot_eq_inner` (~2136) and
        `inner_sum_smul` (~2152, used by the 90.3 helper); place the new theorem
        AFTER `iInf_subtype_dot_le_of_mem_convexHull` (~2399, it uses it) and BEFORE
        `convexDistance_eq_dual` (~2460); reword the section header (~2129
        "Items 90.1-90.3" → "Items 90.2, 90.3, 90.5"), the 90.3-helper docstring
        (~2390 "mirror of 90.1's bounded branch"), and the `convexDistance_eq_dual`
        docstring cross-reference (~2440 "cf. `iInf_prop_const_of_not` in the 90.1
        proof") to describe the subtype form.
    - proof: |
        ~12 lines total; the heavy lifting stays in the existing 90.3 helper:

        ```
        haveI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
        haveI : Nonempty (convexHull ℝ M) := ⟨⟨hM.choose, subset_convexHull ℝ M hM.choose_spec⟩⟩
        -- (≥) pointwise: the M-iInf lower-bounds every hull value (90.3 helper)
        have hp : ∀ z : convexHull ℝ M, (⨅ v : M, w ⬝ᵥ v.1) ≤ w ⬝ᵥ z.1 :=
          fun z => iInf_subtype_dot_le_of_mem_convexHull w M hMnn hw z.2
        -- hull-range BddBelow derived from hp (bound = the M-iInf)
        have hB_hull : BddBelow (Set.range (fun z : convexHull ℝ M => w ⬝ᵥ z.1)) := by
          refine ⟨⨅ v : M, w ⬝ᵥ v.1, ?_⟩
          intro b hb
          rcases hb with ⟨z, rfl⟩
          exact hp z
        refine le_antisymm ?_ ?_
        · -- (≤): each v ∈ M embeds into the hull subtype
          refine le_ciInf ?_
          intro v
          exact ciInf_le hB_hull ⟨v.1, subset_convexHull ℝ M v.2⟩
        · -- (≥): le_ciInf over the hull subtype with the pointwise bound
          refine le_ciInf hp
        ```

        Key facts: `ciInf_le hB_hull ⟨v.1, subset_convexHull ℝ M v.2⟩` has RHS
        `w ⬝ᵥ ⟨v.1, …⟩.1`, defeq `w ⬝ᵥ v.1` (closes by rfl); `hp` is the 90.3
        helper instantiated at `z.1` (its `hz : z.1 ∈ convexHull ℝ M` inferred from
        `z.2`). The embedding argument form `⟨v, subset_convexHull ℝ M v.2⟩ :
        convexHull ℝ M` is confirmed (same pattern as `convexMismatchSet_nearest_point`
        ~2353 and `convexDistance_eq_dual` ~2563). No `BddBelow` hypotheses on the
        statement, no prop-indexed fallback, no `mem_convexHull_iff_exists_fintype`
        in the new proof (it lives inside the 90.3 helper).
- **prep**
    - `iInf_subtype_dot_le_of_mem_convexHull` (90.3, main file ~2399) —
      `(hMnn : M ⊆ {v | ∀ i, 0 ≤ v i}) (hw : ∀ i, 0 ≤ w i) {z} (hz : z ∈ convexHull ℝ M) :
      (⨅ v : M, w ⬝ᵥ v.1) ≤ w ⬝ᵥ z`; the (≥) direction IS this helper
    - `le_ciInf` (VERIFIED v4.32) — `[ConditionallyCompleteLattice α] [Nonempty ι]
      (H : ∀ x, c ≤ f x) : c ≤ iInf f` (no BddBelow)
    - `ciInf_le` (VERIFIED v4.32) — `(H : BddBelow (Set.range f)) (c : ι) :
      iInf f ≤ f c`
    - `subset_convexHull` (VERIFIED) — `s ⊆ convexHull 𝕜 s`; embedding
      `⟨v.1, subset_convexHull ℝ M v.2⟩`
    - `Set.Nonempty.choose` / `choose_spec` — `hM.choose : E`, `hM.choose_spec :
      hM.choose ∈ M` (for the two `haveI : Nonempty …`)
    - `convexHull_empty` (VERIFIED) — `(convexHull 𝕜) ∅ = ∅` (only if the hM-free
      empty-case variant is attempted)
    - `iInf_of_isEmpty` (VERIFIED) — `[InfSet α] [IsEmpty ι] (f) : iInf f = sInf ∅`;
      `Real.sInf_empty : sInf (∅ : Set ℝ) = 0` (empty-case fallback)
    - NOT usable (VERIFIED): `ciInf_le'` — needs `[ConditionallyCompleteLinearOrderBot α]`,
      no instance for ℝ; `iInf_le_iInf_of_subset` — `[CompleteLattice α]` + prop-indexed;
      `le_csInf` (v4.32 shape `(h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ sInf s`)
      and `csInf_le_csInf` (`BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s`)
      exist but the le_ciInf/ciInf_le route above is cleaner
    - KEEP (existing private, section ClassicalDualForm): `dot_eq_inner` (~2136),
      `inner_sum_smul` (~2152) — both used by the 90.3 helper
    - DELETE at integration: `iInf_prop_const_of_mem` (~2142), `iInf_prop_const_of_not`
      (~2147), old `iInf_inner_convexHull` (~2177-2263)
- **log**
    | Date | Att | Status | Goal | Proof Feedback | Review Feedback | Tmp |
    |------|-----|--------|------|----------------|-----------------|-----|
    | 2026-08-15 | 1 / 15 | done | Write and prove the specialized subtype form `(⨅ z : convexHull ℝ M, w ⬝ᵥ z.1) = (⨅ v : M, w ⬝ᵥ v.1)` with `(hMnn : M ⊆ {v | ∀ i, 0 ≤ v i}) (hw : ∀ i, 0 ≤ w i) (hM : M.Nonempty)` — (≥) via `le_ciInf` + the 90.3 helper `iInf_subtype_dot_le_of_mem_convexHull` pointwise, hull-range BddBelow derived from that pointwise bound (bound = the M-iInf), (≤) via `le_ciInf` over `M` + `ciInf_le` at the embedded point `⟨v.1, subset_convexHull ℝ M v.2⟩`; Nonempty instances from `hM`; no BddBelow hypotheses, no prop-indexed fallback. | **PROVED** as planned (~24-line theorem, tmp 33 lines). Both `haveI : Nonempty …` instances from `hM` (`hM.choose`/`hM.choose_spec`, hull side via `subset_convexHull ℝ M hM.choose_spec`); (≥) pointwise bound `hp` is exactly the 90.3 helper `iInf_subtype_dot_le_of_mem_convexHull w M hMnn hw z.2` per hull point; hull-range `hB_hull : BddBelow` derived from `hp` (witness = the M-iInf, closes via `rcases hb` + `hp z`); (≤) via `le_ciInf` + `ciInf_le hB_hull ⟨v.1, subset_convexHull ℝ M v.2⟩`; closed with `le_antisymm`. Confirmed `le_ciInf` (mathlib v4.32 source) takes only `[Nonempty ι]` + the pointwise bound, so both `?_`s are the pointwise goals — no hidden BddBelow obligations. | Verified independently. tmp 33 lines (< 500), 0 errors / 0 warnings, no sorry/admit/axiom; axiom check on the theorem = [propext, Classical.choice, Quot.sound] only. Proof read line-by-line: (a) both Nonempty instances from `hM`, (b) (≥) is exactly the existing helper per hull point, (c) derived `hB_hull` sound, (d) `le_antisymm` closes. Integrated into `ConvexDistance.lean` as a REPLACEMENT: deleted old 90.1 set-membership theorem (was ~2162-2263) and private `iInf_prop_const_of_mem`/`iInf_prop_const_of_not` (was ~2141-2149); inserted the renamed `iInf_inner_convexHull` (subtype form, `(hMnn) (hw) (hM)` kept) after `iInf_subtype_dot_le_of_mem_convexHull`, now at line ~2335, before `convexDistance_eq_dual`; new docstring explains subtype form (no `sInf ∅ = 0` fallback), nonneg hypotheses supplying BddBelow-by-0 for free (general form would need explicit BddBelow), GPT-v2-refactor provenance. Section header → "Blueprint Items 90.2, 90.3, 90.5"; helper docstring reworded (dropped "mirror of 90.1's bounded branch"); `convexDistance_eq_dual` docstring cross-ref now cites the 90.5 subtype refactor instead of `iInf_prop_const_of_not`. KEPT `dot_eq_inner`, `inner_sum_smul`, `dot_nonneg`, helper. grep: no dangling references to deleted names. Main file: 0 errors / 0 warnings / 0 sorries; full `lake build` passed. `tmp_bridge.lean` deleted. | `tmp_bridge.lean` |
