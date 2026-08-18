# Survey Checklist — Moser–Tardos Algorithmic Lovász Local Lemma

Companion to `PLAN.md`. The top section mirrors the user's mandatory proposal contents; the
per-agent sections are the subagent missions. Checked items are expected to appear (with
evidence) in the corresponding survey report and, later, in `proposal.md`.

## 1. 要证的结论 (theorem to prove)

- [ ] **Simplest version pinned, statement written out explicitly** — asymmetric
      Moser–Tardos bound in the variable framework:
      - [ ] full Lean-level statement of the main theorem (hypotheses: variable framework +
            `vbl` determinism + LLL condition with `x i ∈ [0,1)`; conclusion: truncated-table
            expected-resamples bound `E_N[#{t < N : Λ t = i}] ≤ ofReal (x i / (1 - x i))`);
      - [ ] the same statement in informal math, cross-checked against the notes §5.1 and
            arXiv:0903.0544 Theorem 1.2;
      - [ ] the `x i = 0` case stated/absorbed explicitly.
- [ ] **Corollaries decided** (which are in the initial scope?):
      - [ ] total expected resamples ≤ Σ x i/(1−x i);
      - [ ] Markov tail bound / a.s.-termination-in-ε–N-form `μ_N(R = N) ≤ (Σ x i/(1−x i))/N`;
      - [ ] constructive LLL: `R < N` output avoids all bad events ⇒ `∃ σ, ∀ i, σ ∉ A i`;
      - [ ] symmetric form `ep(d+1) ≤ 1 ⇒ E ≤ m/d` (initial scope or follow-up?).
- [ ] **Proof route** (decide required prerequisite definitions, lemmas, and their order):
      - [ ] variable model: product measure on `Π j, Ω j`; `vbl`; overlap dependency graph
            `Γ⁺`; determinism/cylinder formulation of "`A i` determined by `vbl i`";
      - [ ] truncated resampling table `Ω_N` + algorithm (deterministic pick rule; padded
            log `Λ`; stopping time `R`); count `N_i^{(N)}`;
      - [ ] witness-tree data structure + `T(Λ,t)` construction + structural lemmas
            (properness, goodness = same-depth disjoint `vbl`, injectivity Prop 12.1);
      - [ ] coupling lemma 14.1 (abstract τ-check → coupling map → measure-preservation);
      - [ ] Galton–Watson weight formula + `∑_{height ≤ h} Pr_GW(τ) ≤ 1`;
      - [ ] final assembly of the main bound;
      - [ ] each step's difficulty + estimated line count (decomposition table).

## 2. 相关的定义/依赖的结论 (related definitions / dependencies)

- [ ] **Existing — mathlib v4.32.0** (every name verified, `file:line` cited):
      - [ ] `Measure.pi` for Fintype index types (product measure for `Ω_N`);
      - [ ] **countable/infinite product measures** (Kolmogorov extension) — present or
            absent? Decides finite-truncation vs infinite a.s. formulation;
      - [ ] expectation infrastructure: `lintegral_indicator`, `lintegral_finset_sum`,
            measurability of counting functions, `Measure.real`;
      - [ ] independence API: `iIndepFun` / `IndepFun` on products, and a lemma for
            "functions of disjoint coordinate sets are independent" (exists? derivable?
            compile-test);
      - [ ] measurable cylinders / `comap`-formulation of coordinate determinism;
      - [ ] tree data structures (mathlib `Data.Tree`, `SimpleGraph` trees, or custom
            inductive — recommendation with rationale);
      - [ ] finiteness of {proper witness trees with ≤ N vertices} over finite `ι`
            (Finset-summability);
      - [ ] `Real.one_add_inv_pow_le_exp` ((1+1/d)^d ≤ e) and ENNReal glue (`ofReal_div`,
            `ofReal_sub`, …) — same toolbox as the LLL file;
      - [ ] confirmation: **no Moser–Tardos / LLL in mathlib v4.32.0**.
- [ ] **Existing — StatsMLlib**:
      - [ ] `Probability.LovaszLocal` — exact API inventory (what is reusable for MT:
            style, `IsDependencyGraph`?, `ofReal_one_sub`? or is MT self-contained?);
      - [ ] `Probability.Independence.FinsetPi` — exact names for the variable-model
            independence statement;
      - [ ] any other module on the import path (FILE_TREE check).
- [ ] **Missing** (to be created; flagged with a Lean-level statement each):
      - [ ] variable model (product law, `vbl`, overlap graph, determinism);
      - [ ] resampling algorithm on the truncated table + padded log + `R`;
      - [ ] witness tree type + `T(Λ,t)` + structural lemmas;
      - [ ] coupling lemma + τ-check;
      - [ ] Galton–Watson weight formula + sum bound;
      - [ ] main theorem + corollaries.
- [ ] **External prior art** (see agent C): AFP `Lovasz_Local` MT content, Lean repos
      (esp. `EdouardBonnet/moser-tardos`), lessons to reuse.

## 3. 预计做的修改（文件）(expected file modifications)

- [ ] NEW `StatsMLlib/Probability/MoserTardos.lean` — or folder split? (agent D recommends
      based on agent B's line estimate; LLL precedent: single flat file)
      - [ ] module name, namespace, imports (mathlib tiers + optional StatsMLlib);
      - [ ] docstring structure (`## Main definitions` / `## Main results` /
            `## References`) per house style;
- [ ] EDIT `StatsMLlib/FILE_TREE.md` — new line + updated counts (current counts verified);
- [ ] EDIT `StatsMLlib/README.md` — module count + optional "Selected results" mention;
- [ ] UNCHANGED: mathlib, `lakefile.lean`, `ARCHITECTURE.md` (to be confirmed by agent D);
- [ ] NEW (doc, outer repo): this proposal + `02_blueprint/BLUEPRINT.md`,
      `03_gpt_review/*`, `04_pr/PR_DESCRIPTION.md` in later phases;
- [ ] git choreography: submodule commits `feat(MT.NN): attempt N — …` on
      `zzk/moser-tardos`; outer-repo doc commits `doc(MT.NN): …; bump StatsMLlib pointer`.

## A. Agent A — mathlib inventory (report `A_mathlib_inventory.md`)

- [ ] Verify each "existing" item in §2 with MCP `lean_local_search`/`lean_hover_info` or a
      stdin compile test; cite `file:line`.
- [ ] **Countable product measure question answered definitively** (search Kolmogorov /
      infinite product / `Measure.pi` variants).
- [ ] Compile-test the two riskiest claims in a `/tmp` scratch file via
      `lake env lean /dev/stdin` (project root `StatsMLlib`):
      - [ ] disjoint-coordinate independence (mini proof with `Measure.pi` + `iIndepFun`);
      - [ ] witness-tree finiteness argument sketch (inductive type + size bound + Fintype).
- [ ] Best formulation for "`A i` determined by `vbl i`": compare `comap`-measurability vs
      explicit cylinder predicate; recommend one.
- [ ] Report MISSING lemmas explicitly with statements.
- [ ] Confirm no MT/LLL in mathlib; note any in-flight mathlib PRs.

## B. Agent B — proof strategy (report `B_proof_strategy.md`)

- [ ] Validate the finite-truncation architecture (PLAN §3); check the math end-to-end:
      - [ ] Prop 12.1 (injective `t ↦ T(Λ,t)`) — does the proof survive the padded log?
      - [ ] Cor 11.2 (same-depth ⇒ disjoint `vbl`) and the coupling-entry injectivity
            (same-depth disjointness + deeper-vertex-in-`S_X` strict inequality);
      - [ ] GW telescoping (17.3)→(17.2); `∑_{height ≤ h} ≤ 1` induction; `x i = 0` case.
- [ ] Pin the **exact main theorem statement** (Lean-level) and each corollary.
- [ ] Settle design points: deterministic pick rule (least-index vs parameterized
      `pick : {S : Set ι // S.Nonempty} → ι` — recommend one); witness-tree representation;
      `IsGood` tree notion; `Ω_N` vs `N`-rows-per-variable subtleties.
- [ ] Produce a **declaration-level decomposition** (~15–20 items, LLL-proposal style):
      name, informal statement, difficulty, est. lines; mark the critical path.
- [ ] Risk register (top 5 risks + mitigations); expected total line count; PR-split
      recommendation (core vs symmetric vs applications).

## C. Agent C — external formalizations (report `C_external_formalizations.md`)

- [ ] Isabelle AFP `Lovasz_Local` entry: does it formalize Moser–Tardos? List theories;
      extract main statements and modeling choices (how do they handle the resampling table,
      witness trees, the algorithm, expectations?).
- [ ] Edmonds & Paulson CPP 2024 paper — scope check; anything beyond the AFP entry.
- [ ] `EdouardBonnet/moser-tardos` (Lean 4) — current state (active? sorry-free? in mathlib?
      scope: sequential MT bound? distributional/HSS?); what to learn / not to duplicate.
- [ ] Other provers (Coq, Agda, HOL Light, Mizar) — any MT formalizations?
- [ ] Literature anchors with exact references: arXiv:0903.0544 Thm 1.2 (sequential bound),
      Thm 1.3 (parallel, out of scope), Thm 6.1 (lopsided, out of scope); Tao's blog
      exposition or similar, if useful for the proof details.

## D. Agent D — repo conventions (report `D_repo_conventions.md`)

- [ ] Current StatsMLlib conventions: layout/ARCHITECTURE rules, namespace patterns
      (`SmallBall`-style vs `McDiarmid`-style), linters, docstring conventions, copyright
      header — cite the actual files.
- [ ] `LovaszLocal.lean` API inventory: which declarations are reusable by MT (import or
      copy)? Which style elements to mirror?
- [ ] Placement recommendation: single flat `Probability/MoserTardos.lean` vs a folder —
      given agent B's line estimate and the LLL promotion-trigger note.
- [ ] Exact `FILE_TREE.md` / `README.md` current numbers and the expected edits.
- [ ] Doc lifecycle + git choreography on `zzk/moser-tardos` (submodule commits, outer-repo
      doc commits, pointer bumps) — mirror the LLL pattern.
- [ ] Check the branch state: `zzk/moser-tardos` created from
      `zzk/lovasz-local-lemma-gptv2`; confirm what the MT work will stack on.

## Cross-cutting rules (all agents)

- [ ] English only; report paths exactly `survey/{A_…,B_…,C_…,D_…}.md`.
- [ ] No edits to repo code; scratch files only under `/tmp`.
- [ ] Reports end with **Risks** and **Open questions**.
- [ ] Each report is self-contained (orchestrator synthesizes; agents must not assume the
      others' findings).
