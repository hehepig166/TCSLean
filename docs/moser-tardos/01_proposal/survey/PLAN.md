# Survey Plan — Moser–Tardos Algorithmic Lovász Local Lemma

**Date:** 2026-08-16
**Status:** in progress (reports land in this folder as `A_…`–`D_…` files)

## 1. Goal

Produce a comprehensive survey supporting the proposal
`doc/moser-tardos/01_proposal/proposal.md` for formalizing the **Moser–Tardos resampling
algorithm** (asymmetric form, variable framework) in `StatsMLlib`, building on the existing
`StatsMLlib.Probability.LovaszLocal` formalization. The survey must pin down:

1. the simplest target theorem, written out explicitly (Lean-level statement + informal math);
2. the proof route and its prerequisite definitions / lemmas;
3. the dependency inventory — existing (mathlib v4.32.0, StatsMLlib) vs. missing;
4. the expected file modifications.

**Constraints (apply to every agent):**

- **Do not modify any repo code.** Reports may quote code, may compile-test snippets via
  `lake env lean /dev/stdin` (StatsMLlib project root: `/Users/zhuzekai/workspace/StatsLean/StatsMLlib`),
  and may create scratch files under `/tmp` only.
- **English throughout** (proposal, survey reports, plan, checklist).
- **Every Lean-name claim must be verified** (MCP `lean_local_search` / `lean_hover_info`, or a
  compile test), with `file:line` citations where useful. The previous LLL survey found several
  name-level surprises (`probReal` → `Measure.real`, missing lemmas) — re-verify, do not trust
  memory.
- Each report ends with **Risks** and **Open questions** sections.

## 2. Inputs (already read by the orchestrator)

| Input | Path / URL | Content |
|---|---|---|
| GPT proof notes | `ref/moser_tardos_algorithmic_lll_notes.md` | Full witness-tree + Galton–Watson proof, §1–§24: variable framework, execution log, witness trees (Def 8.1, Prop 10.1, Lemma 11.1, Cor 11.2, Prop 12.1), coupling lemma (Lemma 14.1), GW process + formula (Lemma 17.1), main bound (Thm 5.1), symmetric form (§20) |
| Lecture slides (Yin Yitong) | `ref/尹一通-lll.pdf` (text extract `/tmp/yyt_lll_slides.txt`) | k-SAT motivation, LLL forms, CSP variable framework, MT algorithm + theorem (pp. 74–163), execution log, resampling table, witness-tree construction with worked example, coupling Lemma 1, GW process + Lemma 2, convergence; Moser's Fix-It + entropic proof (pp. 165–193, *out of scope for the core*) |
| Paper | arXiv:0903.0544v3 | MT 2010: sequential Algorithm 1.1, Theorem 1.2 (`E[#resamples of A] ≤ x(A)/(1−x(A))`), Theorem 1.3 (parallel), Theorem 6.1 (lopsided, out of scope) |
| Reference proposal | https://github.com/Lean-MoDS/StatsMLlib/issues/1 | Positioning/granularity/format template (motivation → theorem statement → location → approach → dependency inventory → open questions → references) |
| Our LLL proposal + survey | `doc/lovasz/01_proposal/` | The house format for this proposal (sections, decomposition tables, API questions, PR split); survey A–D reports are the model for the reports here |
| Existing formalization | `StatsMLlib/StatsMLlib/Probability/LovaszLocal.lean` (~740 lines) | The classical LLL already in the project; its PR description lists the variable model and Moser–Tardos as follow-ups |
| Harness | `harness/` (README, CONVENTIONS, skills/*) | Workflow that will drive the later blueprint phase (this survey is the pre-blueprint research, same as for LLL/Talagrand) |

Note: `ref/gpt-notes.md` exists but is **empty** (0 bytes) — the 28 KB
`moser_tardos_algorithmic_lll_notes.md` is the GPT-written detailed explanation the user
referred to.

## 3. Architectural seed (orchestrator's synthesis — agents must validate, refine, or refute)

The reference materials agree on the classical witness-tree proof. Its Lean formalization
suggests the following architecture, which survey agents A/B must validate in detail:

**Variable framework.** Events `ι` and variables `κ`, both `[Fintype]`; variable `j` takes
values in a measurable space `Ω j` with probability measure `μ j`; the joint law is the
product measure. Each bad event `A i : Set (Π j, Ω j)` is *determined by* `vbl i : Finset κ`.
The dependency graph is **defined as the variable-overlap graph**
(`Adj i j ↔ (vbl i ∩ vbl j).Nonempty`, `Γ⁺ i = {j | vbl i ∩ vbl j ≠ ∅}`) — no graph parameter
needed.

**Finite-truncation formulation (no infinite product measure).** For each `N`, work on the
truncated resampling table `Ω_N := Π (j : κ), Fin N → Ω j` with the product measure
`Measure.pi (fun p : Σ j, Fin N => μ p.1)`. All statements are on `Ω_N`:

- the deterministic resampling map (pick the least violated event under a fixed order on `ι`,
  consume one fresh row of every `j ∈ vbl i`), the padded execution log `Λ : Ω_N → ℕ → ι`,
  the stopping time `R : Ω_N → ℕ`;
- **main theorem:** `E_N[#{t < N : Λ t = i}] ≤ ENNReal.ofReal (x i / (1 - x i))` under the LLL
  condition `μ (A i) ≤ ofReal (x i * ∏ j ∈ Γ(i) …)` — via
  `lintegral` over `Ω_N` (no finiteness of `Ω j` required);
- corollaries: total resamples bound; Markov tail bound
  `μ_N (R = N) ≤ (∑ᵢ x i/(1−x i)) / N` (a.s. termination in ε–N form); **constructive LLL**:
  if `R < N`, the final assignment avoids all bad events, hence
  `∃ σ, ∀ i, σ ∉ A i` — a new, constructive proof of the variable-model LLL;
- symmetric form: `e·p·(d+1) ≤ 1 ⟹ E_N[#resamples] ≤ m/d` (follow-up corollary).

**Proof chain (as in the notes):** witness trees (inductive data structure; *proper*:
distinct child labels per parent; *good*: proper + same-depth vertices have disjoint `vbl` —
needed for the coupling), tree construction `T(Λ,t)` from the log prefix (deepest-eligible
rule, deterministic tie-break), structural lemmas (goodness of occurring trees, injectivity
`T(Λ,s) ≠ T(Λ,t)`), **coupling lemma** (abstract τ-check with fresh samples → coupling map
`Ω_N → Ω_check` → measure-preservation → `μ_N(∃t, T(Λ,t) = τ) ≤ ∏ᵤ μ(A[u])`), **Galton–Watson
weight formula** on finite trees + `∑_{τ ∈ 𝒯_i, height ≤ h} Pr_GW(τ) ≤ 1` by induction on `h`,
then the final sum. `x i = 0` handled by a trivial case (no division needed there).

Key open design points for agents A/B to settle: (i) does mathlib v4.32.0 have countable
product measures (Kolmogorov) — if yes, the infinite a.s. formulation becomes feasible;
(ii) the best witness-tree representation; (iii) how to state "`A i` determined by `vbl i`";
(iv) whether "functions of disjoint coordinates of a product measure are independent" exists
or must be derived.

## 4. Survey axes (four subagents, launched in parallel)

| Agent | Mission (summary) | Report |
|---|---|---|
| **A — mathlib/project inventory** | Verify every Lean dependency named in §3; find missing lemmas; compile-test the riskiest claims (independence-of-disjoint-coordinates, tree finiteness). See CHECKLIST.md §A. | `survey/A_mathlib_inventory.md` |
| **B — proof strategy** | Validate/refine §3 into a pinned theorem statement + a declaration-level decomposition (~15–20 items) with difficulties and line estimates; risk register; settle design points (ii)–(iv). | `survey/B_proof_strategy.md` |
| **C — external formalizations** | Isabelle AFP `Lovasz_Local` (does it contain Moser–Tardos? structure, statements, modeling), Edmonds–Paulson CPP 2024, `EdouardBonnet/moser-tardos` (Lean, was active 2026-08-08 — check current state), other provers, literature anchors. | `survey/C_external_formalizations.md` |
| **D — repo conventions** | StatsMLlib conventions (layout, linters, namespace, docstrings), `LovaszLocal.lean` API inventory (what is reusable), file placement recommendation (single file vs folder), FILE_TREE/README edit list, git/doc choreography on branch `zzk/moser-tardos`. | `survey/D_repo_conventions.md` |

## 5. Workflow

1. **Write `CHECKLIST.md`** (done next, before any subagent is launched).
2. **Launch agents A–D in parallel** (general-purpose subagents). Each prompt carries: the
   project root, the ref paths, the LLL proposal/survey paths (format templates), this PLAN,
   its section of the checklist, and the constraints above.
3. **Collect reports** into `survey/`.
4. **Orchestrator synthesizes `proposal.md`** (positioning per the reference proposal, format
   per `doc/lovasz/01_proposal/proposal.md`): motivation; explicit simplest theorem statement;
   proof approach with decomposition table; existing vs missing dependencies; expected file
   modifications; API questions; future extensions; references; survey report index.
5. Report to the user, including the empty `ref/gpt-notes.md` observation.

No blueprint is written and no repo code is touched in this phase.
