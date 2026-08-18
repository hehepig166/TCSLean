# Survey Plan — Lovász Local Lemma

## Goal

Produce a comprehensive proposal for formalizing the Lovász Local Lemma (LLL) in StatsMLlib.
The simplest version to be settled first is the **asymmetric LLL** (dependency-graph form),
following the classical conditional-probability proof. The proposal must contain:

1. **The theorem to prove** — an explicit statement of the asymmetric LLL (with a candidate
   Lean statement), and the expected proof route (prerequisite definitions, conclusions, lemmas).
2. **Related definitions / dependent results** — what already exists (mathlib v4.32.0,
   StatsMLlib) and what is missing and must be created.
3. **Expected modifications (files)** — concrete new files, and any edits to existing files.

## Reference Documents

- `ref/gpt-notes.md` — self-contained notes on the LLL: dependency graphs, the asymmetric LLL
  with a complete proof via the key conditional-probability lemma (Lemma 4.2), symmetric forms
  (`ep(d+1) ≤ 1`, `4pd ≤ 1`), and applications (bounded-dependency k-SAT, hypergraph coloring).
- `ref/尹一通-lll.pdf` — LLL lecture notes (Chinese) by Yitong Yin; may cover additional
  variants (lopsided, constructive) useful for the future-extensions section.
- `ref/note.md` — goal statement + pointer to the Talagrand proposal
  ([#1](https://github.com/Lean-MoDS/StatsMLlib/issues/1)) and
  [arXiv:0903.0544](https://arxiv.org/html/0903.0544v3) (lopsided-LLL survey, future work).
- Format model: `doc/talagram/01_proposal/proposal.md` and its survey reports
  (`doc/talagram/01_proposal/survey/`).

Environment: mathlib v4.32.0 (sources under
`StatsMLlib/.lake/packages/mathlib/Mathlib/`), Lean 4.32.0, StatsMLlib with 89 modules
(mathlib-style subject refactor; see `StatsMLlib/FILE_TREE.md` and `ARCHITECTURE.md`).

## Survey Topics (4 subagents)

### A. Mathlib API Inventory & Gap Check
**Output:** `survey/A_mathlib_inventory.md`

- **Is the LLL already in mathlib v4.32.0?** Grep the mathlib sources for `Lovasz`/`Lovász`;
  cross-check with loogle / leansearch. Verdict must be unambiguous.
- Probability API: `iIndepSet`, `IndepSet`, `IndepSets`, `iIndepFun` (and the `IndepSet`-level
  lemmas for events), `ProbabilityTheory.cond` and all conditional-probability lemmas relevant
  to the proof (multiplication rule, add-complement/peeling rule, chain rule, comparison,
  zero/one cases).
- Conditional independence: `CondIndepSet`, `CondIndepSets`, lemmas linking independence and
  conditional probability (`cond_eq` under independence).
- `SimpleGraph` API: `neighborSet` / `neighborFinset`, adjacency, degree — is
  `neighborFinset` available for a `[Fintype V]` vertex type?
- Finset machinery: strong induction on `Finset.card`, `∏` bounds
  (`prod_le_prod` variants), `prod_pos`, subset-product monotonicity under factors `∈ [0,1]`.
- ENNReal vs ℝ: `ENNReal.ofReal`, `ofReal_mul`, subtraction laws under finiteness
  (`IsProbabilityMeasure` ⇒ `μ s < ⊤`), `ENNReal.ofReal_le_ofReal`, `probReal` API.
- Real inequalities needed for the symmetric versions: Bernoulli `(1−x)^d ≥ 1−dx`,
  `(1 + 1/d)^d ≤ e`-type bounds, `exp` bounds — exact lemma names if present, ABSENT otherwise.
- StatsMLlib local: contents of `StatsMLlib/Probability/Independence/FinsetPi.lean`
  (`pi_map_eval`, `pi_eval_iIndepFun`, etc.) — the variable-model independence infrastructure.
- For every item: EXISTS (file + line + signature) or ABSENT. Never invent names; verify by
  grepping the sources. Unverified items are marked TBC with a search recipe.

### B. Proof Strategy & Formalization Plan
**Output:** `survey/B_proof_strategy.md`

- Pin down the exact statement to formalize first: **asymmetric LLL**, as in
  `ref/gpt-notes.md` §4 (Theorem 4.1 + Definition 3.1 dependency graph).
- Decide the Lean formulation and justify it:
  - index type: `Fintype ι` vs `Fin n` (note: the peeling induction avoids any total order —
    verify this claim);
  - dependency structure: `SimpleGraph ι` vs a symmetric relation `dep : ι → ι → Prop`;
  - independence hypothesis: classical Definition 1.1 ("independent of the family of
    non-neighbors") vs the weaker-but-sufficient "`A i` independent of `⋂_{j∈S} (A j)ᶜ` for
    every non-neighbor set `S`" — check which is closest to mathlib's API and sufficient for
    the proof;
  - ENNReal (`cond`) vs ℝ (`probReal`) — check the proof of gpt-notes Lemma 4.2 and Theorem
    4.1 and note that all inequalities can be written multiplicatively (no division):
    `μ (A i ∩ B S) ≤ ENNReal.ofReal (x i) * μ (B S)` plus
    `ENNReal.ofReal (∏ j ∈ S, (1 − x j)) ≤ μ (B S)`, both by strong induction on `S.card`;
    positivity `0 < μ (B S)` then follows. Verify this route against the real mathlib API.
- Produce the proof decomposition: each step of gpt-notes §4.1–4.2 mapped to a concrete Lean
  lemma (name suggestion + statement sketch + expected difficulty + which inventory items
  from survey A it consumes). Include the base case, the `N = ∅` independence case, the
  chain-rule/peeling product bound, the `N ⊆ Γ(i)` product monotonicity, and the final
  assembly and positivity step.
- List of new declarations with difficulty ratings (mirroring the Talagrand survey style).
- Symmetric LLL, `4pd` corollary, and applications (k-SAT, hypergraph coloring) as
  follow-ups: what each needs and its incremental cost.
- Open questions / risks (e.g., `IndepSets` vs `iIndepSet` ergonomics, ENNReal subtraction
  finiteness, `SimpleGraph.neighborFinset` availability, cond-chain-rule gap).

### C. External Formalizations & Literature
**Output:** `survey/C_external_formalizations.md`

- Isabelle AFP entry **"Lovász Local Lemma"** (if it exists — verify at
  https://www.isa-afp.org/entries/Lovasz_Local.html): authors, which variants are formalized
  (symmetric/asymmetric?), the formalization route (dependency digraph? measure-theoretic
  probability?), and lessons for our design.
- mathlib4: search GitHub issues/PRs and the docs site for LLL work in progress (any existing
  branch/PR we should know about or coordinate with).
- Other formalizations: search broadly (Lean community projects, Coq, HOL4, Mizar).
- Skim `ref/尹一通-lll.pdf` (PDF, Chinese): which variants are covered (symmetric, asymmetric,
  lopsided, constructive/algorithmic), notation used — feed the future-extensions section.
- arXiv:0903.0544 (Haeupler–Saha–Srinivasan, lopsided LLL survey): scope, what the lopsided
  version adds (future work). Classical references: Erdős–Lovász 1975, Alon–Spencer book.
- Summarize each source and end with takeaways relevant to this proposal (statement choice,
  proof route, what to defer).

### D. Repo Conventions & Expected File Changes
**Output:** `survey/D_repo_conventions.md`

- StatsMLlib layout rules: read `ARCHITECTURE.md`, `CONTRIBUTING.md`, `README.md`,
  `FILE_TREE.md`; sample 2–3 existing file headers (e.g.
  `StatsMLlib/Probability/Concentration/McDiarmid.lean`,
  `StatsMLlib/Probability/Independence/FinsetPi.lean`) for header/naming/style conventions.
- Linter constraints from `lakefile.lean` (already strict: no `λ`, `·` bullets, ≤100 lines,
  `autoImplicit := false`, etc.) — list what a new file must obey.
- Where should the new file(s) go? Evaluate `Probability/LovaszLocal.lean` (flat, like
  McDiarmid/Hoeffding) vs a new subfolder (e.g. `Probability/LovaszLocal/…`). Check
  ARCHITECTURE.md import-direction rules. Note that `FILE_TREE.md` enumerates all 89 modules
  and must be updated.
- Doc workflow precedent: how `doc/talagram` is structured (01_proposal → 02_blueprint →
  03_gpt_review → 04_pr), what `02_blueprint/BLUEPRINT.md` item numbering looks like
  (80.x, 90.x, "done" markers), so `doc/lovasz` can follow the same lifecycle.
- Git conventions: StatsMLlib is a submodule — commits go inside it plus a pointer bump in
  the outer repo; doc/ files are committed in the outer repo.
- Deliver a concrete draft of the **expected modifications (files)** list: new `.lean`
  file(s) with proposed module paths, edits to `FILE_TREE.md`/`README.md` if any, and the
  doc-side files.

## Checklist

- [ ] A. Mathlib API Inventory & Gap Check → `survey/A_mathlib_inventory.md`
- [ ] B. Proof Strategy & Formalization Plan → `survey/B_proof_strategy.md`
- [ ] C. External Formalizations & Literature → `survey/C_external_formalizations.md`
- [ ] D. Repo Conventions & Expected File Changes → `survey/D_repo_conventions.md`
- [ ] Final: proposal document `../proposal.md` containing
  - [ ] the theorem to prove: explicit asymmetric-LLL statement + proof route,
  - [ ] related definitions/results: existing vs missing,
  - [ ] expected modifications (files).

Constraints: the survey is **read-only** with respect to the StatsMLlib code (no edits to
any `.lean` file, no `lake build`); survey outputs go into this directory only. All
documents in English.
