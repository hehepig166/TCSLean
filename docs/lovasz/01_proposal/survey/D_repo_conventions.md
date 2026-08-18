# Survey D — Repository conventions and expected modifications (Lovász Local Lemma)

Scope: StatsMLlib library conventions (architecture, file style, linters), placement
recommendation for the LLL file(s), the talagram doc workflow, git conventions, and a concrete
"expected modifications (files)" list for the proposal.

All paths below are absolute under `/Users/zhuzekai/workspace/StatsLean`.

---

## 1. Library architecture

Sources: `StatsMLlib/ARCHITECTURE.md`, `CONTRIBUTING.md`, `README.md`, `FILE_TREE.md`.

### Layer-one ownership

Seven layer-one directories; there are **no Lean files directly in `StatsMLlib/`**:

| Layer | Owns |
| --- | --- |
| `MeasureTheory` | Reusable measure, integral, and convergence results (no probabilistic structure). |
| `Topology` | Topological / pseudo-metric constructions, covering and packing numbers. |
| `LinearAlgebra` | Deterministic matrix, operator, singular-value, spectral results. |
| `Analysis` | Deterministic analytic constructions on foundational layers (metric entropy, covering estimates). |
| `Probability` | Random variables and processes, moments, concentration, entropy methods, Gaussian analysis, random matrices. |
| `LearningTheory` | Empirical metrics, complexity measures, uniform convergence, function classes. |
| `Statistics` | Statistical models, estimators, regression, finite-sample/minimax guarantees. |

Current second-level organization (verbatim from ARCHITECTURE.md):

```text
StatsMLlib/
├── Analysis/{MetricEntropy,NormedSpace}
├── LearningTheory/{EmpiricalProcess,FunctionClass,Rademacher,UniformDeviation}
├── LinearAlgebra/Matrix
├── MeasureTheory/{Function,Integral}
├── Probability/{Concentration,Entropy,Gaussian,Independence,Moments,Process,RandomMatrix}
├── Statistics/Regression/LeastSquares
└── Topology/{MetricSpace,SeparableSpace}
```

Note `Probability/SmallBall.lean` is a **flat file directly under `Probability/`** (not in any of
the listed subfolders) — the precedent for standalone named-theorem files.

### Import-direction rules

Tiered acyclic import graph (verbatim):

```text
{MeasureTheory, Topology, LinearAlgebra}
                    ↓
                 Analysis
                    ↓
                Probability
                    ↓
             LearningTheory
                    ↓
                Statistics
```

- A module may import **within its own layer and from any earlier tier**; never from a later tier.
- Downstream modules may bypass an intermediate tier and import an earlier owner directly.
- The LLL (Probability layer) may therefore import MeasureTheory / Topology / LinearAlgebra /
  Analysis / other Probability modules (e.g. `StatsMLlib.Probability.Independence.FinsetPi`), but
  nothing from LearningTheory or Statistics.

### Module-naming rules (ARCHITECTURE.md, "Module naming")

- Do **not** add `Main.lean`, `Infrastructure.lean`, or an unqualified `Defs.lean` under `StatsMLlib/`.
- `Basic.lean` and `Defs.lean` are acceptable **only when their directory gives a precise subject**.
- Prefer full subject names in paths (`RandomMatrix`, `LogSobolev`, `EckartYoungMirsky`), not
  project/provenance abbreviations.
- A whole-library umbrella, if ever needed, must be a declaration-free `StatsMLlib.lean` outside
  `StatsMLlib/`.

### Mathlib imports

- No restriction on importing mathlib: every module imports `Mathlib.*` freely (e.g. McDiarmid.lean
  imports `Mathlib.Tactic.Cases`; FinsetPi.lean imports `Mathlib.Probability.Independence.Basic`).
- Mathlib is pinned in `lakefile.lean`: `require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"` (README: "pinned to Lean and
  Mathlib v4.32.0").
- There is no local `ForMathlib`/`Infra` layer anymore (removed in the 2026-07 refactor); results
  that are "just mathlib-style facts" must go in the subject-owned module, and CONTRIBUTING.md
  requires: "Reuse existing StatsMLlib and Mathlib declarations before adding new infrastructure."

### CONTRIBUTING.md constraints

- Open an issue before a large formalization or architectural change.
- Use the Lean/Mathlib versions pinned by `lean-toolchain` and `lakefile.lean`.
- Place declarations in the subject-owned module described in `ARCHITECTURE.md`.
- **No `sorry`, `axiom`, `admit`, or `native_decide`.**
- **Keep builds free of warning and info messages**; remove unused parameters instead of hiding them.
- Read `AUTHORS.md` and preserve all existing copyright and author attribution.
- Add significant authors to the source-file `Authors` header; when work is co-written, add a
  `Co-authored-by` trailer for every additional author to the commit message.
- New modules must include a Mathlib-style file header and module docstring.
- Contributions are Apache License 2.0 (section 5 of LICENSE).

### FILE_TREE.md: machine-checked or hand-maintained?

**Hand-maintained — must be updated by hand when adding a file.** Evidence:

- No generator script exists anywhere in the repo (the only cross-reference to `FILE_TREE` is the
  link in `README.md`).
- It is **already stale by one file**: it claims "`StatsMLlib/` contains 89 Lean modules" and its
  layer table sums to 89 (Analysis 4 + LearningTheory 13 + LinearAlgebra 5 + MeasureTheory 2 +
  Probability 42 + Statistics 21 + Topology 2), but the tree on disk now contains **90** `.lean`
  files — the in-flight Talagrand work added `Probability/Concentration/ConvexDistance.lean`
  (committed in the submodule) without yet updating FILE_TREE.md. README.md likewise hardcodes
  "The public source contains 89 modules".

So the LLL PR must update both FILE_TREE.md (tree + counts) and README.md (module count), and
should also absorb the pre-existing ConvexDistance.lean drift.

---

## 2. File style (headers, docstrings, namespaces, ℝ vs ℝ≥0∞)

### Copyright / authors header (exact, verbatim)

`StatsMLlib/Probability/Concentration/McDiarmid.lean` and `.../Independence/FinsetPi.lean` (lines 1–5):

```lean
/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda
-/
```

`StatsMLlib/Probability/SmallBall.lean` (lines 1–5):

```lean
/-
Copyright (c) 2026 Yuanhe Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuanhe Zhang, Jason D. Lee, Fanghui Liu
-/
```

So the current author set spans: Kei Tsukamoto (copyright holder of the 2024 files), Kazumi
Kasaura, Naoto Onda, Yuma Mizuno, Sho Sonoda; and (2026 files) Yuanhe Zhang, Jason D. Lee, Fanghui
Liu. AUTHORS.md additionally lists organizers (Fanghui Liu, Jason D. Lee, Peter Bartlett, Weijie
Su, Aleksandar Mijatovic, Taiji Suzuki, Yuekai Sun, Sho Sonoda, …) and stresses that the file-level
`Copyright` and `Authors` lines are authoritative; a new file written for the LLL gets a fresh
header with its own copyright year/holder/authors. (Caveat: the in-flight
`ConvexDistance.lean` has **no** copyright header yet — it starts directly with imports; headers
are evidently finalized at PR time, but CONTRIBUTING.md requires one, so the LLL file should have
its header from the start.)

### Module docstring format

`/-!` block immediately after the imports:

- `# Title` (H1, e.g. `# McDiarmid's Inequality`, `# Small Ball Probabilities`, `# Finite Product Measure Lemmas`);
- one prose paragraph describing the file;
- `## Main definitions` (often "This module introduces no new definitions." / "formulates X directly as hypotheses…");
- `## Main results` — bullet list of declaration names with em-dash descriptions, e.g. McDiarmid:
  ```
  ## Main results

  * `mcdiarmid_inequality_pos`: upper-tail McDiarmid inequality.
  * `mcdiarmid_inequality_neg`: lower-tail McDiarmid inequality.
  * `bounded_difference_iff`: equivalent forms of the bounded-difference condition.
  ```
  (SmallBall.lean writes `## Main Results` with capital R and adds inlined math descriptions;
  the `## Main definitions` / `## Main results` lowercase form is the majority style.)
- optional `## References` section (present in Hoeffding.lean and
  `Statistics/Regression/LeastSquares/L1/CoveringBound.lean`). Citation format — bare key in
  brackets, no in-file bibliography, e.g. Hoeffding.lean lines 24–26:
  ```
  ## References

  We follow [martin2019] and [mehryar2018] for the proof of Hoeffding's lemma.
  ```

### Namespace conventions (mixed — three patterns in use)

- **Top-level, no namespace**: `McDiarmid.lean`, `FinsetPi.lean` — theorem names carry the subject
  prefix themselves: `mcdiarmid_inequality_pos`, `pi_map_eval`, `pi_eval_iIndepFun`.
- **`namespace ProbabilityTheory`**: `Hoeffding.lean` (extends mathlib's namespace; theorem is
  `ProbabilityTheory.hoeffding`).
- **Module-specific namespace**: `SmallBall.lean` uses `namespace SmallBallProbability`
  (contains `mgf_neg_le_inv`, `small_ball_prob`); `ConvexDistance.lean` uses
  `namespace ClassicalDualForm` for its final section.

Files typically start with `open MeasureTheory ProbabilityTheory` (McDiarmid, FinsetPi) or
`open MeasureTheory ProbabilityTheory Real` (Hoeffding) and `open scoped ENNReal NNReal Topology`
(SmallBall). For a standalone flat file the SmallBall pattern (module-specific namespace, or
top-level with a `lovasz_local_*`-style prefix) is the best match; see §4.

### Theorem naming style

lowerCamelCase `snake_case` with subject prefix, mathlib conventions: `mcdiarmid_inequality_pos`,
`pi_map_eval`, `integral_exp_neg_mul_Ioi_zero`, `small_ball_prob`, `hoeffding`. Declarations
living in `namespace ProbabilityTheory` drop the prefix (`hoeffding`, not `hoeffding_lemma`).

### ENNReal vs ℝ

- **Statements (inequalities, integrals of real integrands) are in ℝ** — e.g. McDiarmid bounds are
  `ℝ` inequalities; SmallBall's final result `P(∑ᵢ Xᵢ ≤ εN) ≤ (eε)^N` is an ℝ inequality.
- **Measures (and pdfs) are ENNReal-valued**: `μ : Measure Ω`, densities `f : ℝ → ℝ≥0∞` with
  hypotheses like `hf_le : ∀ x, f x ≤ 1`, converted to ℝ via `.toReal` /
  `ENNReal.toReal_mono` when entering ℝ statements.
- Probability hypotheses appear as `[IsProbabilityMeasure μ]`; independence via mathlib's
  `ProbabilityTheory.IndepFun` / `iIndepFun`.

---

## 3. Linter / style constraints (from `StatsMLlib/lakefile.lean`)

Verbatim lines 4–14:

```lean
abbrev linter : Array LeanOption := #[
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.missingEnd, true⟩,
  ⟨`linter.cdot, true⟩,
  ⟨`linter.dollarSyntax, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.longLine, true⟩,
  ⟨`linter.oldObtain, true,⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.setOption, true⟩
]
```

Verbatim lines 16–27 (options):

```lean
abbrev options := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ -- options that are used in `lake build`
    linter.map fun s ↦ { s with name := `weak ++ s.name }

package «StatsMLlib» where
  leanOptions := options
  moreServerOptions := linter.map fun s ↦ { s with name := `weak ++ s.name }
```

Consequences for a new file:

- `autoImplicit = false`: every free variable must be declared explicitly (`{Ω : Type*}`, `[MeasurableSpace Ω]`, `{μ : Measure Ω}`, …) — no implicit auto-bound variables.
- `pp.unicode.fun = true`: use `fun x ↦ ...` / `↦` pretty-printing.
- `linter.style.lambdaSyntax`: no `λ` — use `fun`.
- `linter.longLine`: lines must be ≤ **100 characters** (mathlib's `linter.style.longLine.maxLineLength`, default 100; URL-containing lines exempt — quoted from mathlib's `Mathlib/Tactic/Linter/Style.lean`: "The \"longLine\" linter emits a warning on lines longer than `linter.style.longLine.maxLineLength` (which defaults to 100) characters. We allow lines containing URLs to be longer, though.").
- Also enforced: no `·`/`cdot` misuses (`linter.cdot`), no `$` syntax (`linter.dollarSyntax`), no `obtain`-as-`rcases` old syntax (`linter.oldObtain`), no unrestricted `refine` syntax (`linter.refine`), no stray `set_option` for pp/profiler/trace/maxHeartbeats (`linter.setOption`), no `#...` hash commands leaking into sources (`linter.hashCommand`), no missing `end` markers (`linter.missingEnd`).
- CONTRIBUTING.md adds: builds must be **free of warnings and info messages** (linters run in `weak` mode during `lake build`; commit 76bf903 "fix(lakefile): weak-prefix linter names in moreServerOptions (LSP was broken on mathlib v4.32)").
- No `sorry`/`axiom`/`admit`/`native_decide` anywhere.
- mathlib's `longFile` (>1500 lines/file) and `nameCheck` linters are **not** enabled in this lakefile, but 1500 lines is still a useful size heuristic (see §4).

---

## 4. Placement recommendation

### Options considered

1. **Flat file**: `StatsMLlib/Probability/LovaszLocal.lean` (module `StatsMLlib.Probability.LovaszLocal`) — like `SmallBall.lean`, `McDiarmid.lean`, `Hoeffding.lean`, `Chernoff.lean`.
2. New subfolder `StatsMLlib/Probability/LovaszLocal/{Basic,Applications}.lean`.
3. Inside an existing subfolder, e.g. `Probability/Independence/LovaszLocal.lean` (the LLL is about event independence).

### Recommendation: option 1 — one flat file `StatsMLlib/Probability/LovaszLocal.lean`

Reasons:

- **Precedent**: `Probability/SmallBall.lean` is exactly this shape — a standalone, named,
  self-contained probability result that fits no existing subfolder, placed flat at the
  Probability layer. The LLL is likewise a named theorem package (not a "Concentration"
  inequality, not an "Entropy" method, not an "Independence" infrastructure piece), so it should
  sit beside SmallBall, not be squeezed into `Concentration/` or `Independence/`.
- **ARCHITECTURE.md does not restrict Probability-layer subfolders** — the listed second-level
  directories are the "current" organization, not a closed set — but its naming rules discourage
  premature structure: `Basic.lean` is acceptable "only when their directory gives a precise
  subject", and the guidance is to prefer full subject names over shallow wrappers. A
  `LovaszLocal/Basic.lean` of one theorem + one corollary is deeper than the content justifies.
- **Import tier**: satisfied. The file will import mathlib
  (`Mathlib.Probability.Independence.*`, `Mathlib.Probability.ConditionalProbability`,
  `Mathlib.Data.Finset.*`) and optionally same-layer StatsMLlib modules (e.g.
  `StatsMLlib.Probability.Independence.FinsetPi`); all allowed for the Probability tier.
- **No mathlib collision**: mathlib v4.32.0 has no Lovász local lemma (its
  `Mathlib/Probability/Combinatorics/` contains only `BinomialRandomGraph/Defs.lean`), so no
  naming conflict; the file is genuinely new content but must reuse mathlib's independence /
  conditional-probability API rather than redevelop it (CONTRIBUTING.md rule).
- **Doc churn**: a flat file means FILE_TREE.md/README.md changes are one line + two counts,
  not a new directory block.

Namespace choice for the flat file: follow the SmallBall pattern — wrap in a module-specific
namespace (e.g. `namespace LovaszLocal` containing `local_lemma`, `symmetric_local_lemma`,
supporting lemmas), or top-level names prefixed `lovasz_local_*` à la McDiarmid. Both are in use;
SmallBall-style is slightly better for keeping short internal lemma names
(`integral_exp_neg_mul_Ioi_zero`-style) from polluting the root namespace.

### Promotion trigger (when to split into `Probability/LovaszLocal/`)

Split `LovaszLocal.lean` into `Probability/LovaszLocal/{Basic,Applications}.lean` when any of:

- the asymmetric LLL, the sparse/bounded-dependence (Erdős–Lovász) version, or the constructive
  Moser–Tardos algorithm is added as a second theorem family;
- applications (k-SAT, hypergraph 2-coloring, van der Waerden-type corollaries) accumulate and
  pull heavier imports (e.g. `Mathlib.Combinatorics.*`) that should stay out of the core
  statement file;
- the single file approaches ~1500 lines (mathlib's `longFile` heuristic — not an enabled linter
  here, but a good size guide).

---

## 5. Doc workflow (talagram lifecycle) and what doc/lovasz should contain

### The talagram lifecycle

Directory layout (verbatim listing):

```
doc/talagram/01_proposal/{proposal.md, proposal_concise.md, ref/{gpt-propose.md, note.md}, survey/}
doc/talagram/01_proposal/survey/{A_existing_infrastructure.md, B_mathlib_api.md,
                               C_proof_strategy.md, D_code_patterns.md,
                               E_scope_and_files.md, PLAN.md}
doc/talagram/02_blueprint/BLUEPRINT.md
doc/talagram/03_gpt_review/{2026_08_14.md, 2026_08_14_v2.md}
doc/talagram/04_pr/PR_DESCRIPTION.md
```

So: `01_proposal` (full proposal + concise version + `ref/` reference notes + `survey/` lettered
reports with a `PLAN.md` index) → `02_blueprint/BLUEPRINT.md` (itemized formalization plan) →
`03_gpt_review/*.md` (dated review files, one per review round, `_v2` for follow-ups) →
`04_pr/PR_DESCRIPTION.md`.

### BLUEPRINT.md numbering and done-marking

- **Numbering**: hierarchical — `## 10. Group`, `### 10.1. item`, `#### 10.1.1. sub-item`; gaps
  allowed for insertion. **Group ranges**: `10`–`19` Definitions, `20`–`39` Basic properties,
  `40`–`59` Core lemmas, `60`–`79` Main theorem, `80`–`99` Corollaries (Talagrand added group
  `90. Classical Equivalence` inside the corollary range).
- **Item format**: `- **meta**` (kind: `def|lemma|theorem`; priority `1|2|3` with 1 =
  nice-to-have, 3 = critical path; status: `pending|working|done`; `attempts: <current> /
  <bucket>` with bucket default 15; `file:` path), `- **informal**` (LaTeX/plain statement +
  proof sketch), `- **prep**` (Lean declaration names with one-line descriptions), and a
  `- **log**` table with columns `Date | Att | Status | Goal | Proof Feedback | Review Feedback |
  Tmp`, newest entries first.
- **Status lifecycle**: `pending → working → done` (retry loops `working`); `attempts =
  bucket/bucket` with status ≠ done ⇒ **blocked** (human intervention). Final status is set by
  Review to `done | pending | stuck`.
- **Done-marking**: edit the item's meta to `status: done` + add a log row; then an outer-repo
  commit of the form `doc(NN.NN): mark <item> as done; bump pointer` (see §6). The Talagrand
  blueprint currently has 34 `### ` items, 32 of them `status: done`.

### Current doc/lovasz state and target state

Current (already mirrors `01_proposal/{ref,survey}`):

```
doc/lovasz/01_proposal/ref/{gpt-notes.md, note.md, 尹一通-lll.pdf}
doc/lovasz/01_proposal/survey/PLAN.md
```

To follow the same lifecycle it should eventually contain:

```
doc/lovasz/01_proposal/proposal.md          (full proposal)
doc/lovasz/01_proposal/proposal_concise.md  (concise version)
doc/lovasz/01_proposal/ref/*                (already present)
doc/lovasz/01_proposal/survey/{A,B,C,D,E}_*.md + PLAN.md   (this report = D_repo_conventions.md)
doc/lovasz/02_blueprint/BLUEPRINT.md        (LLL item plan, numbering per the group ranges above)
doc/lovasz/03_gpt_review/YYYY_MM_DD.md      (one dated file per review round, _v2 for follow-ups)
doc/lovasz/04_pr/PR_DESCRIPTION.md
```

---

## 6. Git conventions and current state

### Submodule (`/Users/zhuzekai/workspace/StatsLean/StatsMLlib`) — code commits

`git log --oneline -10` (verbatim):

```
267f40b feat(90.5): attempt 1 — refactor iInf_inner_convexHull to subtype form
874034c feat(80.25): attempt 1 — drop hA/hAc from two_sided; fix median docstring
e52fb49 feat(90.3): attempt 1 — prove convexDistance_eq_dual (classical dual form)
1e0ccae feat(90.2): attempt 1 — prove nearest-point package (compact hull, variational inequality)
76bf903 fix(lakefile): weak-prefix linter names in moreServerOptions (LSP was broken on mathlib v4.32)
d7bbdb9 feat(90.1): attempt 1 — prove iInf_inner_convexHull (BddBelow split)
0bdf290 feat(90.1): attempt 1 - proof complete, awaiting review (checkpoint)
98dc734 feat(80.20): attempt 1 — prove integral_le_one_div corollary
54c1ea1 feat(80.16): attempt 1 — restructure two_sided into implication pair
df8a6fc chore: remove stray harness/tmp scratch file
```

Style: `feat(NN.NN): attempt N — <summary>` (em-dash separator, blueprint item number),
`fix(...)`, `chore`.

### Outer repo (`/Users/zhuzekai/workspace/StatsLean`) — doc commits + pointer bumps

`git log --oneline -10` (verbatim):

```
e6b426a doc(90.5): mark subtype refactor as done; sync PR description; bump pointer
0482e62 doc(80.25): mark two_sided polish as done; bump pointer
6feeae4 doc: add GPT v2 follow-up items 80.25, 90.5; archive review v2
dda21da doc: PR description for Talagrand convex-distance inequality
a2b0eab doc(90.3): mark convexDistance_eq_dual as done — bridge theorem complete; bump pointer
6d02535 doc(90.2): mark nearest-point package as done; bump StatsMLlib pointer
105edf5 doc(90.1): mark iInf_inner_convexHull as done; bump StatsMLlib pointer
23aedba bump StatsMLlib pointer to 0bdf290 (90.1 checkpoint)
8f36c39 doc(90.1): survey done - verified convex-combination API, attempt 1 working
0fb05f4 doc(80.16,80.20): mark restructure + integral_le_one_div as done; bump StatsMLlib pointer
```

Style: `doc(NN.NN): mark <item> as done; bump pointer` / `doc: <doc milestone>` / `bump
StatsMLlib pointer to <sha> (<note>)`.

**Division of labor**: code commits (`.lean`, lakefile, README, FILE_TREE) go to the **submodule**;
doc-side commits (proposal/survey/blueprint/review/PR files) go to the **outer repo**, and each
doc milestone that consumes code bumps the submodule pointer in the outer repo.

### Dirty state (do NOT commit anything — this report is read-only)

- Submodule `git status --short`: **clean** (empty).
- Outer repo `git status --short` (live): only `?? doc/lovasz/` (untracked). The session-start
  snapshot additionally showed `M StatsMLlib` and `M doc/talagram/02_blueprint/BLUEPRINT.md`;
  those were committed in `e6b426a` since, so the live tree is clean apart from `doc/lovasz/`.

---

## 7. Expected modifications (files) for the proposal

### Code side (submodule `StatsMLlib`)

| Status | File | Description |
| --- | --- | --- |
| NEW | `StatsMLlib/Probability/LovaszLocal.lean` | Module `StatsMLlib.Probability.LovaszLocal`: symmetric Lovász local lemma (statement + proof over finite index sets with a dependency/mutual-independence hypothesis, and the standard ep(1−p) corollary). Mathlib-style header (`/-` Copyright/Authors `-/`), `/-!` docstring with `## Main definitions` / `## Main results` / `## References` (e.g. `[lovasz1975]`, `[alonSpencer]`), namespace per §4. |
| EDIT | `StatsMLlib/FILE_TREE.md` | Add the `LovaszLocal.lean` line under `Probability/`; update the counts table (Probability 42→44, Total 89→91 — the +2 includes the missing `ConvexDistance.lean` line that is currently undocumented drift, see §1). |
| EDIT | `StatsMLlib/README.md` | Update "The public source contains 89 modules" → 91; optionally add the LLL to "Selected results". |
| EDIT | `StatsMLlib/AUTHORS.md` | Only if the LLL work introduces a new significant author (per CONTRIBUTING.md); otherwise untouched. |
| none | mathlib | Nothing in mathlib is modified; the LLL reuses mathlib v4.32.0 (`Mathlib.Probability.Independence.*`, `Mathlib.Probability.ConditionalProbability`) as-is. |
| none | `lakefile.lean`, `ARCHITECTURE.md`, `CONTRIBUTING.md` | Unchanged (flat file fits existing rules; linters/options already in place). |

Note: FILE_TREE.md/README.md edits belong to the submodule (they live in `StatsMLlib/`), so they
are code-side commits even though they are "docs".

### Doc side (outer repo `StatsLean`, under `doc/lovasz/`)

| Status | File | Description |
| --- | --- | --- |
| NEW | `doc/lovasz/01_proposal/proposal.md` | Full LLL proposal (math, scope, file plan — the "expected modifications" section lives here). |
| NEW | `doc/lovasz/01_proposal/proposal_concise.md` | Concise version (talagram parity). |
| EXISTS | `doc/lovasz/01_proposal/ref/{gpt-notes.md, note.md, 尹一通-lll.pdf}` | Already present; keep. |
| NEW | `doc/lovasz/01_proposal/survey/A_*.md` … `E_*.md`, `PLAN.md` | Lettered surveys (existing `PLAN.md` is present; this report is `D_repo_conventions.md`). |
| NEW | `doc/lovasz/02_blueprint/BLUEPRINT.md` | Itemized plan with the talagram meta/informal/prep/log format and the 10–99 group numbering. |
| NEW | `doc/lovasz/03_gpt_review/YYYY_MM_DD.md` | One dated review file per round (`_v2` for follow-ups). |
| NEW | `doc/lovasz/04_pr/PR_DESCRIPTION.md` | PR description drafted before opening the PR. |

### Commit choreography (matches existing workflow)

1. Code attempts: submodule commits `feat(LL.NN): attempt N — <summary>`.
2. Review round done: outer-repo `doc(LL.NN): mark <item> as done; bump StatsMLlib pointer`.
3. At the end: outer-repo `doc: PR description for Lovász local lemma`, followed by the actual PR
   from the submodule (code) with its `Co-authored-by` trailers per CONTRIBUTING.md.
