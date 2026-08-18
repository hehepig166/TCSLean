# Survey Plan — Talagrand's Convex-Distance Inequality

## Goal

Produce a comprehensive proposal for formalizing Talagrand's convex-distance concentration
inequality on finite discrete product spaces in StatsMLlib.

## Reference Documents

- `ref/gpt-propose.md` — GPT-generated proposal with detailed approach
- `ref/note.md` — Links to [#1](https://github.com/Lean-MoDS/StatsMLlib/issues/1) and
  [Tao's blog](https://terrytao.wordpress.com/2009/06/09/talagrands-concentration-inequality/)

## Survey Topics (5 subagents)

### A. Existing Infrastructure Audit
**Output:** `survey/A_existing_infrastructure.md`

- What exists in `Probability/Concentration/` that is relevant?
  - Chernoff.lean, Hoeffding.lean, McDiarmid.lean, EfronStein.lean, Maximal.lean
- What measure-theory infrastructure? (Measure.pi, independence, FinsetPi)
- What topology/analysis infrastructure? (convexHull, Metric.infDist, EuclideanSpace)
- Key lemmas: Hölder, Fubini, Markov, Chernoff bounding pattern
- Fin induction tools in mathlib

### B. Mathlib API Deep Dive
**Output:** `survey/B_mathlib_api.md`

- `EuclideanSpace ℝ (Fin n)` — what's the API? `finAddEquivProd`?
- `convexHull ℝ s` — key lemmas, finite-generation properties
- `Metric.infDist x s` — properties, nonnegativity, triangle inequality
- `MeasureTheory.Measure.pi` — product measure API
- `ProbabilityTheory.iIndepFun` — independence for Fin-indexed families
- `Set.Finite` + measurability for discrete spaces
- `Fin` recursion/induction tools (`Fin.succFunEquiv`, `Fin.induction`, etc.)

### C. Proof Strategy & Gap Analysis
**Output:** `survey/C_proof_strategy.md`

- Detailed induction proof structure (n → n+1)
- Key geometric lemma: convexDistance recursion under projection
- Parameter optimization (the λ choice)
- What lemmas are missing and must be created?
- Mapping of proof steps → Lean declarations needed
- Difficulty assessment per step

### D. Code Patterns & Conventions
**Output:** `survey/D_code_patterns.md`

- File header format (Copyright, Authors, imports, module docstring)
- Naming conventions in existing concentration files
- How existing inequalities structure their proofs (e.g., McDiarmid)
- Variable naming patterns (μ, X, A, etc.)
- How references are cited
- Typeclass usage patterns (IsProbabilityMeasure, MeasurableSpace, etc.)
- How `pos` and `neg` tail variants are structured

### E. Scope & File Planning
**Output:** `survey/E_scope_and_files.md`

- Proposed file(s) and their contents
- Single file vs multi-file split
- Module path: `Probability/Concentration/ConvexDistance.lean` vs alternative
- What goes in Defs vs Inequality vs Applications
- Import dependency analysis (what can/cannot be imported per ARCHITECTURE.md)
- Downstream modules that could use this result
- Future generalization path (Fin n → Fintype, finite Ω → Polish, etc.)

## Checklist

- [ ] A. Existing Infrastructure Audit
- [ ] B. Mathlib API Deep Dive
- [ ] C. Proof Strategy & Gap Analysis
- [ ] D. Code Patterns & Conventions
- [ ] E. Scope & File Planning
- [ ] Final: Integrate into `proposal.md`
