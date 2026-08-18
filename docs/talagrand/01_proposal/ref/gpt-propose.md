# Proposal: Talagrand's convex-distance inequality on finite discrete product spaces

## Motivation

I am interested in formalizing Talagrand's convex-distance inequality for product
probability spaces.

This is distinct from the Bousquet--Talagrand inequality for empirical-process
suprema. The proposed result is a geometric concentration inequality for measurable
sets in product spaces, with possible later applications to convex Lipschitz
functions and functions admitting weighted certificates.

Because arbitrary product measurable spaces introduce nontrivial measurability
questions for projections and convex distance, I propose beginning with finite
discrete coordinate spaces.

## Proposed definitions

Let

    x y : Fin n → Ω.

Define the coordinatewise disagreement vector

    mismatchVector x y : EuclideanSpace ℝ (Fin n)

by

    (mismatchVector x y) i = if x i = y i then 0 else 1.

For a nonempty set

    A : Set (Fin n → Ω),

define

    convexMismatchSet A x :=
      convexHull ℝ (mismatchVector x '' A)

and

    convexDistance A x :=
      Metric.infDist 0 (convexMismatchSet A x).

Thus `convexDistance A x` is the Euclidean distance from the origin to the
convex hull of the disagreement vectors between `x` and points of `A`.

A later extension could prove the equivalent weighted-Hamming formulation

    convexDistance A x
      =
      sup_{α ≥ 0, ‖α‖₂ ≤ 1}
        inf_{y ∈ A} ∑ i, α i * 1_{x i ≠ y i}.

I would not require this dual formulation for the first contribution.

## Proposed main theorem

Let `μs : Fin n → Measure Ω` be probability measures and let

    μ := Measure.pi μs.

For a nonempty set `A`, the main target is the exponential-integrability form

    probReal μ A *
      ∫ x, exp (convexDistance A x ^ 2 / 4) ∂μ
      ≤ 1.

The multiplication form avoids dividing by `probReal μ A` and also gives a
meaningful statement when `μ A = 0`.

The main concentration corollary would be

    probReal μ A *
      probReal μ {x | t ≤ convexDistance A x}
      ≤ exp (-(t ^ 2) / 4)

for `t ≥ 0`.

If `probReal μ A ≥ 1 / 2`, this gives

    probReal μ {x | t ≤ convexDistance A x}
      ≤ 2 * exp (-(t ^ 2) / 4).

## Initial scope

For the first contribution, I propose assuming:

* the index type is `Fin n`;
* `Ω` is a finite discrete measurable space;
* the coordinate measures may be different;
* `A` is nonempty.

The finite-discrete assumption should make all relevant sets and functions
measurable and allow the set `A` to be treated internally as a finite set.

Possible later generalizations include dependent finite coordinate types,
countable discrete spaces, or suitably regular Polish spaces.

## Possible location

A possible owning module is

    StatsMLlib/Probability/Concentration/ConvexDistance.lean.

If the development becomes too large, it could instead be split as

    StatsMLlib/Probability/Concentration/ConvexDistance/Defs.lean
    StatsMLlib/Probability/Concentration/ConvexDistance/Inequality.lean
    StatsMLlib/Probability/Concentration/ConvexDistance/Applications.lean.

The first two files would contain the core development. Applications such as
weighted-certificate and convex-Lipschitz concentration could be added later.

## Possible approach

My current plan is to use the standard induction on the number of coordinates.

1. Define disagreement vectors and convex distance using
   `EuclideanSpace ℝ (Fin n)`, `convexHull`, and `Metric.infDist`.
2. Prove basic properties such as nonnegativity, monotonicity in the set, vanishing
   on the set, and the bound `convexDistance A x ≤ sqrt n`.
3. Prove the theorem in dimension zero or one.
4. Identify `Fin (n + 1) → Ω` with `(Fin n → Ω) × Ω`.
5. For `A ⊆ (Fin n → Ω) × Ω`, define its projection

       B := {x | ∃ ω, (x, ω) ∈ A}

   and sections

       A_ω := {x | (x, ω) ∈ A}.

6. Prove the key geometric recursion

       convexDistance A (x, ω) ^ 2
         ≤ (1 - λ) * convexDistance B x ^ 2
           + λ * convexDistance (A_ω) x ^ 2
           + (1 - λ) ^ 2

   for `0 ≤ λ ≤ 1`, treating empty sections separately.

7. Exponentiate this inequality, apply Hölder's inequality, and invoke the
   induction hypotheses for `B` and the nonempty sections `A_ω`.
8. Integrate over the final coordinate and use Fubini to recover the measure of
   `A`.
9. Complete the required scalar optimization.
10. Derive the tail theorem using Markov's inequality.

Relevant Mathlib infrastructure seems to include:

* `MeasureTheory.Measure.pi`;
* `convexHull`;
* `Metric.infDist`;
* `EuclideanSpace`;
* `EuclideanSpace.finAddEquivProd`;
* `Fin.succFunEquiv`;
* Fubini/Tonelli, Hölder, and Markov inequalities.

The main missing ingredients appear to be:

* the disagreement-vector and convex-distance API;
* finite-discrete measurability lemmas;
* compactness/minimizer lemmas for the relevant finite convex hulls;
* the section/projection recursion for convex distance;
* the scalar optimization used in the induction;
* the integral and tail forms of Talagrand's inequality.

Before beginning, I would appreciate guidance on the following API questions:

1. Is a finite-discrete first version an appropriate scope?
2. Should the first theorem use a single finite coordinate type `Ω`, or dependent
   finite coordinate types `Ω : Fin n → Type*`?
3. Is `Fin n` preferable for the induction proof, with an arbitrary `Fintype`
   corollary added later?
4. Should the convex-hull formulation be the primary definition, with the
   weighted-Hamming formulation proved later?
5. Should the primary public theorem be the exponential-integrability form, the
   tail form, or both?
6. Would a single `ConvexDistance.lean` file be preferable initially, or should
   definitions and the inequality be separated from the beginning?

I would keep general measurable spaces, weighted certificates, convex-Lipschitz
applications, transportation inequalities, and empirical-process Talagrand
inequalities out of scope for the first contribution.

## References

* Michel Talagrand, “Concentration of Measure and Isoperimetric Inequalities in
  Product Spaces.”
* Michel Ledoux, “Four Talagrand Inequalities under the Same Umbrella.”
* Michel Ledoux, The Concentration of Measure Phenomenon.
* Stéphane Boucheron, Gábor Lugosi, and Pascal Massart,
  Concentration Inequalities: A Nonasymptotic Theory of Independence.