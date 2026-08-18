# Survey D — Repository conventions and expected modifications (Moser–Tardos)

Scope: StatsMLlib library conventions (architecture, file style, linters) verified against the
**current** repo state (submodule on branch `zzk/moser-tardos` at commit `c6e4461`), the
`LovaszLocal.lean` API inventory (what the Moser–Tardos file can reuse), a placement
recommendation, the expected file modifications, git/doc choreography, and harness integration
notes. All claims below were verified by reading the actual files on 2026-08-16; line numbers are
from the current working tree.

All paths below are absolute under `/Users/zhuzekai/workspace/StatsLean`.

---

## 1. Conventions (verified, current)

### 1.1 Architecture (ARCHITECTURE.md — unchanged since the LLL survey)

Verified verbatim against the current file:

- **Seven layer-one directories; no Lean files directly in `StatsMLlib/`** (ARCHITECTURE.md
  lines 3–4). `Probability` owns "random variables and processes, moments, concentration, entropy
  methods, Gaussian analysis, and random matrices" (line 14).
- **Second-level organization** (lines 20–29): `Probability/{Concentration,Entropy,Gaussian,Independence,Moments,Process,RandomMatrix}`.
  The listed folders are the *current* organization, not a closed set — flat files
  `Probability/LovaszLocal.lean` and `Probability/SmallBall.lean` already sit beside these folders
  as the precedent for standalone named-theorem packages (confirmed on disk:
  `StatsMLlib/Probability/` contains `LovaszLocal.lean`, `SmallBall.lean` plus the seven folders).
- **Import tiers** (lines 35–48): `{MeasureTheory, Topology, LinearAlgebra} → Analysis → Probability → LearningTheory → Statistics`.
  A module may import within its own layer and from any earlier tier; never from a later tier.
  A Moser–Tardos file at the Probability layer may therefore import mathlib freely **and**
  same-tier StatsMLlib modules — in particular `StatsMLlib.Probability.LovaszLocal` and
  `StatsMLlib.Probability.Independence.FinsetPi` (both Probability tier; `LovaszLocal.lean`
  imports only mathlib, so no cycle).
- **Module naming** (lines 63–68): no `Main.lean` / `Infrastructure.lean` / unqualified `Defs.lean`;
  `Basic.lean`/`Defs.lean` only when the directory gives a precise subject; prefer full subject
  names (`RandomMatrix`, `LogSobolev`, …). `MoserTardos.lean` satisfies all of these.

### 1.2 lakefile.lean — linters and options (verbatim identical to the LLL survey)

`StatsMLlib/lakefile.lean` is byte-for-byte what the LLL D report quoted (lines 4–14 linters,
lines 16–27 options). Consequences for the MT file:

- `autoImplicit = false` (line 19): every free variable must be declared explicitly.
- `pp.unicode.fun = true` (line 18): `fun x ↦ …` / `↦` pretty-printing.
- Linters (weak-prefixed during `lake build`, full strength in LSP via `moreServerOptions`):
  `hashCommand` (no `#`-commands in sources), `missingEnd`, `cdot` (bullet style `·`),
  `dollarSyntax`, `style.lambdaSyntax` (no `λ`), `longLine` (**lines ≤ 100 characters**, mathlib
  default for `linter.style.longLine.maxLineLength`), `oldObtain`, `refine`, `setOption`
  (lines 4–14). The LLL blueprint review logs confirm the 100-char check was enforced per
  integration ("no lines over 100 chars").
- CONTRIBUTING.md line 14: builds must be **free of warning and info messages**.
- CONTRIBUTING.md line 13: **no `sorry`, `axiom`, `admit`, or `native_decide`** anywhere.
- CONTRIBUTING.md line 12: "Reuse existing StatsMLlib and Mathlib declarations before adding new
  infrastructure."
- CONTRIBUTING.md line 3: open an issue before a large formalization (satisfied — this proposal
  continues the project's proposal-then-blueprint flow; the LLL work followed the same route).
- CONTRIBUTING.md lines 16–17: add significant authors to the file `Authors` header; add a
  `Co-authored-by` trailer for every additional author to commit messages.
- Mathlib pinned at v4.32.0 (lakefile lines 29–30). mathlib's `longFile` (>1500 lines) and
  `nameCheck` linters are **not** enabled here, but 1500 lines remains the useful size heuristic.

### 1.3 File header and module docstring

`StatsMLlib/Probability/LovaszLocal.lean` lines 1–5 (the file the MT file will sit next to):

```lean
/-
Copyright (c) 2026 Zhu Zekai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhu Zekai
-/
```

The MT file should reuse this header **verbatim** (same author, same year, same license). Note:
`AUTHORS.md` does not list "Zhu Zekai" (its Organizers section lists Fanghui Liu, Jason D. Lee, et
al.); per AUTHORS.md's own statement, file headers are authoritative, and the LLL PR did **not**
edit AUTHORS.md. The MT PR should follow that precedent (flag as open question §8.4).

Module docstring structure (LovaszLocal.lean lines 12–59), the house style:

- `/-!` block immediately after imports: `# Title` (H1), one prose paragraph;
- `## Main definitions` — bullet list of defs with em-dash descriptions;
- `## Main results` — bullet list of theorem names with em-dash descriptions;
- `## References` — bare `[key]` citations, no in-file bibliography
  (LLL: `[alonSpencer2016]`, `[edmondsPaulson2024]`, `[erdosLovasz1975]`).
- `open MeasureTheory ProbabilityTheory` + `open scoped BigOperators ENNReal` (lines 61–62);
  `namespace LovaszLocal` (line 64) with the explicit variable block
  `{Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Fintype ι]
  [DecidableEq ι]` (lines 66–67).

The MT file should mirror: `namespace MoserTardos`, same `open`s, its own variable block
(plus `κ`, `Ω : κ → Type*`, `vbl : ι → Finset κ`, `N : ℕ` as needed), and `## References` with
`[moserTardos2010]` (arXiv:0903.0544), `[alonSpencer2016]`, and the lecture-slide anchor used in
`ref/尹一通-lll.pdf` if cited.

### 1.4 Namespace conventions

Verified current state (unchanged from the LLL survey): the module-specific-namespace pattern
(SmallBall's `namespace SmallBallProbability`, LLL's `namespace LovaszLocal`) is the established
fit for a standalone flat named-theorem file; McDiarmid/FinsetPi use top-level names with subject
prefixes (`mcdiarmid_inequality_pos`, `pi_map_eval`). Recommend `namespace MoserTardos` (keeps
short internal lemma names like `ofReal_one_sub`, `T`, `IsGood`, `weight` from polluting the root
namespace — the exact benefit the LLL run exploited).

### 1.5 ENNReal / μ.real statement conventions

Verified in `LovaszLocal.lean`:

- The main theorem `lovaszLocalLemma` (line 357) is an **ENNReal** inequality:
  `μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ G.neighborFinset i, (1 - x j))` ⟹
  `ENNReal.ofReal (∏ i, (1 - x i)) ≤ μ (⋂ i, (A i)ᶜ)`.
- The ℝ corollary `lovaszLocalLemma_probReal` (line 379) is stated via **`μ.real`**:
  `∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ)`.
- Glue lemmas: `ofReal_one_sub {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal (1 - x) = 1 - ENNReal.ofReal x`
  (line 144).

The MT main bound `E_N[#{t < N : Λ t = i}] ≤ ENNReal.ofReal (x i / (1 - x i))` follows the same
shape: ENNReal `lintegral`-level statement with `ENNReal.ofReal` on the ℝ-arithmetic side; a
`μ.real`-valued corollary only if a ℝ statement is wanted (LLL did exactly this once, for the
existence form).

### 1.6 The `(μ := μ)` discipline

Verified: `LovaszLocal.lean` passes the measure by name at **20 use sites** (`grep -c "(μ := μ)"` =
20), in every theorem hypothesis (`IsDependencyGraph (μ := μ) G A`,
`IsDependencyGraphStrong (μ := μ) G A`) and every independence-API call
(`indepSet_iff_measure_inter_eq_mul (μ := μ) …`, `Indep.indepSet_of_measurableSet (μ := μ) …`,
`IndepSets.indep' (μ := μ) …`). The reason is documented in the
LLL blueprint item 10.5 prep note: `ProbabilityTheory.IndepSet`'s measure is an `autoParam`
defaulting to `volume_tac` (literally `MeasureSpace.volume`), so it **does not** pick up a local
`{μ : Measure Ω}` variable. Any file that has only `[IsProbabilityMeasure μ]` and no
`[MeasureSpace Ω]` instance **must** pass `μ` explicitly. This will bite the MT file at least as
hard: it works with the product measure `μN : Measure Ω_N` (`Measure.pi (fun p : Σ j, Fin N ↦ μ p.1)`)
which is *not* the ambient `volume` — every `IndepSet`/`Indep`/`IndepSets`/`IsDependencyGraph` use
must be `(μ := μN)`-qualified, and every `IsProbabilityMeasure` instance for `μN` must be
instantiated (haveI-style) before use.

### 1.7 Minimized hypotheses via `omit … in`

A distinctive LLL-file pattern worth mirroring: 26 occurrences of `omit [MeasurableSpace Ω]
[Fintype ι] … in` before individual lemmas, keeping each lemma's hypothesis set minimal (e.g.
`bset_empty` at line 81 drops everything but the barest structure). The MT file's structural
lemmas (witness-tree facts, log/tree construction properties) should do the same where the
probability-space structure is unused.

### 1.8 Commit-message conventions (verified in both repos)

- Submodule: `feat(NN.NN): attempt N — <summary>` (em-dash separator, blueprint item number),
  plus `fix(...)`, `chore`; e.g. `c6e4461 refactor(80.30): rename symmetric_sharp to
  symmetric_optimalWeight; reword dependency-graph docstrings`, `e179705 feat(90.5): attempt 1 —
  prove lovaszLocalLemma_cond`. For MT: `feat(MT.NN): attempt N — <summary>`.
- Outer repo: `doc(NN.NN): mark <item> as done; bump StatsMLlib pointer` and `doc: <milestone>`;
  e.g. `32c0baf doc(90.15,80.30): mark global-form rework and rename as done; bump StatsMLlib
  pointer`. For MT: `doc(MT.NN): …; bump StatsMLlib pointer`.
- Both repos' commits carry `Co-Authored-By: Claude <noreply@anthropic.com>` trailers when
  co-written (verified in outer-repo commit bodies).

---

## 2. `LovaszLocal.lean` API inventory and reuse assessment

File: `StatsMLlib/Probability/LovaszLocal.lean` — **786 lines** (the mission's "~740" is stale;
`wc -l` = 786), `namespace LovaszLocal` spans lines 64–786. Outline verified via LSP; all
declarations are public (importable from `StatsMLlib.Probability.LovaszLocal`).

### 2.1 Genuinely reusable declarations

| Declaration | Line | Statement (abbrev.) | Reuse by MT? |
| --- | --- | --- | --- |
| `bset` | 72 | `bset A S = ⋂ j ∈ S, (A j)ᶜ` (avoidance event) | **Yes** — "final assignment avoids all bad events" is `σ ∈ bset A Finset.univ`; the constructive-LLL corollary and the bridge statement are naturally `bset`-shaped. |
| `bset_empty/_insert/_union/_univ_eq_iInter` | 83/91/110/128 | structural `bset` facts | Yes (cheap, `[simp]`-tagged) |
| `measurableSet_bset` | 136 | `bset` of measurable events is measurable | Yes (measurability of the avoidance set on `Ω_N`) |
| `ofReal_one_sub` | 144 | `0 ≤ x ⟹ ENNReal.ofReal (1 - x) = 1 - ENNReal.ofReal x` | **Yes — direct glue** for the MT bound `x/(1-x)` and for `∏ (1 - x j)` manipulations in the GW section. |
| `IsDependencyGraph` | 78 | `∀ i S, i ∉ S → (∀ j ∈ S, ¬ G.Adj i j) → IndepSet (A i) (bset A S) μ` | **Yes — the target of the cross-file bridge theorem** (§2.3). |
| `IsDependencyGraphStrong` | 393 | generated-σ-algebra global form | Yes, optional (only if MT states the bridge in the strong form) |
| `IsDependencyGraph.of_strong` / `.strong` / `isDependencyGraph_iff_strong` | 402/428/502 | equivalence bridge | Yes, optional |
| `lovaszLocalLemma_exists` | 509 | `∃ ω, ∀ i, ω ∉ A i` under `IsDependencyGraph` + smallness | **Yes — the conclusion of the bridge corollary**: instantiate at `Ω := Ω_N`, `μ := μN`. |
| `lovaszLocalLemma_bset_pos` | 753 | `0 < μ (bset A S)` | Maybe (positivity of avoidance events in the constructive-LLL corollary) |
| `lll_prob_bset`, `prob_bset_inter_prod`, `measure_bset_insert(_le)`, `cond_*` | 153–350, 724–743 | conditional-probability/peeling machinery | **No** — the MT witness-tree proof avoids conditional probability and peeling entirely; this is the classical (P1)/(P2) machinery. |
| `lovaszLocalLemma(_pos/_probReal/_symmetric*_/_4pd/_cond)` | 357–786 | the classical LLL theorem family | No — MT *replaces* the classical nonconstructive route with the constructive one; importing them buys nothing except the bridge target `lovaszLocalLemma_exists`. |

### 2.2 Verdict: largely self-contained, with three cross-file touchpoints

The MT file should **not** import the LLL file wholesale for its core: the variable model, the
truncated resampling table, the algorithm, witness trees, the coupling, and the GW formula are all
new constructions that do not use `bset`-peeling. The three genuine touchpoints are:

1. `ofReal_one_sub` (one lemma — cheap, but importing the whole file for it is fine since the
   import is already wanted for (2));
2. the **bridge section** — prove the variable-overlap graph satisfies `IsDependencyGraph` and
   derive `lovaszLocalLemma_exists`'s conclusion as a corollary (§2.3);
3. style patterns to mirror (not import): `namespace`, `omit … in`, `(μ := μ)`, `[simp]`/`[measurability]`
   attributes, the header/docstring shape.

Recommendation: import `StatsMLlib.Probability.LovaszLocal` at the top of the MT file (same-tier,
acyclic — LovaszLocal imports only mathlib), use `ofReal_one_sub` and `bset` in the main proof,
and put the bridge theorem in a final section. If the bridge turns out to be high-risk during the
blueprint, it can be dropped from PR 1 without touching the main bound (LLL precedent: group 90
was optional, priority 1).

### 2.3 Cross-file theorem feasibility: overlap graph satisfies `IsDependencyGraph`

**Statement (informal):** in the MT variable model (`Ω = Π j, Ω j` with product measure `μ`,
`A i` determined by `vbl i`), the overlap graph `G` with `G.Adj i j ↔ (vbl i ∩ vbl j).Nonempty`
satisfies `LovaszLocal.IsDependencyGraph (μ := μ) G A`; hence, if the variable-model LLL condition
`μ (A i) ≤ ENNReal.ofReal (x i * ∏ j ∈ Γ⁺ i, (1 - x j))` holds (with `Γ⁺ i` the overlap
neighborhood), `LovaszLocal.lovaszLocalLemma_exists` applies and gives `∃ σ, ∀ i, σ ∉ A i` — a
**new, constructive variable-model proof of the classical LLL as an MT corollary**, cross-linking
the two files.

**Feasibility assessment: HIGH.** The argument is structurally short:

1. For `S` a set of non-neighbors of `i`, every `j ∈ S` has `vbl i ∩ vbl j = ∅`, so the
   coordinate set `U := ⋃_{j∈S} vbl j` is disjoint from `vbl i`.
2. The determinism hypothesis ("`A i` determined by `vbl i`") makes `A i` measurable w.r.t. the
   coordinates in `vbl i` and `bset A S` measurable w.r.t. coordinates in `U` (via
   `measurableSet_bset` + the determinism plumbing — comap/cylinder formulation, agent A's
   design point (iii)).
3. "Functions of disjoint coordinate sets of a product measure are independent" (the mathlib
   lemma agent A is compile-testing) then gives `IndepSet (A i) (bset A S) μ` — exactly
   `IsDependencyGraph`.

Estimated cost: one bridge lemma of ~30–80 lines (dominated by the determinism→measurability
plumbing) plus a ~10-line corollary instantiating `lovaszLocalLemma_exists` at `(Ω_N, μN)`. The
condition match is definitional **provided** the MT file defines `Γ⁺ i` as the overlap graph's
`neighborFinset` — then `hLLL` of the LLL file and the MT hypothesis are the same formula. This is
a design constraint to pin in the blueprint (agent B): *define the overlap graph `G` first and
state the MT condition with `G.neighborFinset i`, not with a free-standing `Γ⁺`.*

### 2.4 `Probability.Independence.FinsetPi` — partial reuse

`StatsMLlib/Probability/Independence/FinsetPi.lean` has three declarations (outline verified):

- `pi_map_eval {ι} {Ω : ι → Type*} … (k : ι) : (Measure.pi μ).map (Function.eval k) = μ k`
  (line 28) — **heterogeneous**; directly reusable for coordinate marginals of the variable
  model.
- `pi_eval_iIndepFun` (line 48) and `pi_comp_eval_iIndepFun` (line 101) — **homogeneous**
  (`Ω = ι → Ω`, same space per coordinate); only indirectly useful. The MT variable model is
  heterogeneous (`Ω : κ → Type*`), so the disjoint-coordinate independence lemma is either a new
  lemma in the MT file or a generalization of FinsetPi — agent A settles which (its
  compile-test covers exactly this).

---

## 3. Placement recommendation

### Options considered

1. **Flat file** `StatsMLlib/Probability/MoserTardos.lean` (module
   `StatsMLlib.Probability.MoserTardos`) — like `LovaszLocal.lean` and `SmallBall.lean`.
2. Folder `StatsMLlib/Probability/MoserTardos/{Basic,Main}.lean` (or similar split).
3. Nesting under the LLL, e.g. `Probability/LovaszLocal/MoserTardos.lean`.

### Recommendation: option 1 — one flat file `StatsMLlib/Probability/MoserTardos.lean`

Rationale:

- **Precedent, twice over.** `SmallBall.lean` and now `LovaszLocal.lean` are both flat
  named-theorem packages under `Probability/`. The LLL file holds an entire theorem family
  (asymmetric + 3 symmetric forms + conditional form + a definitional bridge) in **786 lines** —
  evidence that a full package fits the flat shape. MT's estimate (agent B: ~1000–1500+ lines) is
  inside the flat envelope; the only enforced constraint is the 100-char line width, and mathlib's
  `longFile` (>1500) linter is not enabled in this lakefile.
- **ARCHITECTURE.md is permissive.** The second-level directory list is descriptive ("The current
  second-level organization is"), and the naming rules actively discourage premature structure
  (`Basic.lean` "only when their directory gives a precise subject"). A `MoserTardos/Basic.lean`
  created before the file's content is known would be exactly the shallow-wrapper move the rules
  warn against.
- **Option 3 is out.** The LLL blueprint's Overview (line 56) explicitly lists "Moser–Tardos" as a
  later PR relative to the LLL file, and promoting `LovaszLocal.lean` into a new `LovaszLocal/`
  folder now would rename a file that is already on an open PR branch — churn with no benefit to
  MT.
- **Doc churn minimal.** FILE_TREE/README edits are one tree line + two counts (§4).
- **No collisions.** `lean_local_search` finds no `MoserTardos` in the project, and a
  leansearch query finds no Moser–Tardos in mathlib v4.32.0 (only unrelated Lovász-form results
  like Kruskal–Katona).

Module: `StatsMLlib.Probability.MoserTardos`; namespace: `namespace MoserTardos` (SmallBall/LLL
pattern, §1.4).

### Split-point if the estimate breaks the flat envelope

Promote to `Probability/MoserTardos/` when any of:

- the file approaches ~1500 lines (mathlib `longFile` heuristic; not enforced here, but the same
  guide the LLL survey used);
- a second MT theorem family lands in the same PR or immediately after (parallel MT
  arXiv:0903.0544 Thm 1.3, lopsided MT Thm 6.1, applications k-SAT / hypergraph 2-coloring);
- applications pull heavy imports (`Mathlib.Combinatorics.*`) that should stay out of the core
  statement file.

Natural seam if a split is forced mid-flight:
`Probability/MoserTardos/Basic.lean` (variable model, resampling table, algorithm, log, stopping
time, witness trees, structural lemmas) + `Probability/MoserTardos/Main.lean` (coupling, GW
formula, main bound, corollaries, LLL bridge). **Decision point: at blueprint time**, once agent
B's decomposition table exists — not during the attempt loop.

---

## 4. Expected modifications (files)

### Code side (submodule `StatsMLlib`)

| Status | File | Description |
| --- | --- | --- |
| NEW | `StatsMLlib/Probability/MoserTardos.lean` | Module `StatsMLlib.Probability.MoserTardos`, `namespace MoserTardos`. Variable model (`Ω : κ → Type*`, product measure, `vbl`, overlap graph, determinism), truncated resampling table `Ω_N`, algorithm + padded log `Λ` + stopping time `R`, witness trees + `T(Λ,t)`, coupling lemma, GW formula, main bound `E_N[#{t < N : Λ t = i}] ≤ ENNReal.ofReal (x i / (1 - x i))`, corollaries (total bound, Markov tail, constructive LLL, symmetric form if in PR 1), LLL bridge section. Header verbatim per §1.3; `/-!` docstring with `## Main definitions` / `## Main results` / `## References` (`[moserTardos2010]`, `[alonSpencer2016]`, slide ref if used). |
| EDIT | `StatsMLlib/FILE_TREE.md` | Insert `│   ├── MoserTardos.lean` between `LovaszLocal.lean` (line 113) and `└── SmallBall.lean` (line 114) — files in the tree are alphabetized. Update counts: "90 Lean modules"→91 (line 4), `Probability` 43→44 (line 14), `Total` 90→91 (line 17). |
| EDIT | `StatsMLlib/README.md` | "The public source contains 90 modules"→91 (line 15). Optionally add Moser–Tardos to "Selected results" (lines 33–46) — note the LLL PR did **not** add its own line there; see §8.3. |
| UNCHANGED | mathlib | Nothing in mathlib is modified; MT reuses v4.32.0 as-is (`Measure.pi`, `lintegral`/`Measure.real`, `iIndepFun`/`Indep`, Finset/ENNReal arithmetic — agent A's inventory). |
| UNCHANGED | `lakefile.lean`, `ARCHITECTURE.md`, `CONTRIBUTING.md`, `AUTHORS.md` | Verified unchanged by the LLL PR and not needed for MT (flat file fits existing rules; linters/options in place). AUTHORS.md untouched per LLL precedent — file header is authoritative. |

**Current-count verification (this branch):** FILE_TREE.md says 90 modules / Probability 43 and
the disk holds exactly **90** `.lean` files, Probability **43** — FILE_TREE is **accurate on this
branch** (the LLL PR updated it; commit `4c7b275`). The LLL survey's "stale by one
(ConvexDistance.lean)" observation no longer applies **on this branch**: `Probability/Concentration/ConvexDistance.lean`
exists only on the unmerged `zzk/talagrand*` branches, not here. **Cross-branch caveat:** if the
Talagrand PR merges before MT, the MT counts become 91→92 / Probability 44→45 and the tree gains
one more line — re-verify against the merge base at PR time.

### Doc side (outer repo `StatsLean`, under `doc/moser-tardos/`)

| Status | File | Description |
| --- | --- | --- |
| NEW | `doc/moser-tardos/01_proposal/proposal.md` | Full MT proposal (the orchestrator synthesizes it from these surveys; LLL-format: Motivation → Proposed Theorem → Location & Expected Modifications → Proof Approach → Relevant Existing Modules → Missing Infrastructure → Code Conventions → API Questions → Future Extensions → References → Survey Reports). **No `proposal_concise.md`** — the LLL cycle dropped the talagram-era concise version; mirror lovasz. |
| EXISTS | `doc/moser-tardos/01_proposal/ref/{gpt-notes.md, moser_tardos_algorithmic_lll_notes.md, note.md, 尹一通-lll.pdf}` | Keep. Note `gpt-notes.md` is 0 bytes (empty) — the 28 KB `moser_tardos_algorithmic_lll_notes.md` is the substantive GPT notes. |
| NEW | `doc/moser-tardos/01_proposal/survey/{A_mathlib_inventory,B_proof_strategy,C_external_formalizations,D_repo_conventions}.md` | The four lettered reports (this one = D); `PLAN.md` + `CHECKLIST.md` already present. |
| NEW | `doc/moser-tardos/02_blueprint/BLUEPRINT.md` | Blueprint phase (later): itemized plan, talagram/LLL format, numbering 10–99 (§5). |
| NEW | `doc/moser-tardos/03_gpt_review/YYYY_MM_DD.md` | One dated review file per round (`_v2` for follow-ups), per the LLL pattern (`2026_08_15.md`, `2026_08_15_v2.md`). |
| NEW | `doc/moser-tardos/04_pr/PR_DESCRIPTION.md` (+ optional `PR_BODY_STACKED.md`) | PR description drafted before opening the PR; `PR_BODY_STACKED.md` if the MT PR stacks on the LLL PR (talagram has this file for its stacked review PR). |

---

## 5. Doc lifecycle & git choreography

### 5.1 Lifecycle (verified against doc/lovasz/ and doc/talagram/)

`doc/lovasz/` now contains the complete four-phase lifecycle:
`01_proposal/{proposal.md, ref/, survey/{A..D,PLAN}.md}` →
`02_blueprint/BLUEPRINT.md` → `03_gpt_review/{2026_08_15.md, 2026_08_15_v2.md}` →
`04_pr/PR_DESCRIPTION.md`. `doc/talagram/` additionally has `04_pr/PR_BODY_STACKED.md`
(untracked) and `01_proposal/proposal_concise.md` (the concise form the LLL/MT cycles drop).
`doc/moser-tardos/` currently has only `01_proposal/{ref,survey}` — the rest lands in later
phases, exactly as the table in §4 shows.

BLUEPRINT.md format (verified from `doc/lovasz/02_blueprint/BLUEPRINT.md`): `## Format` section
defining per-item `- **meta**` (kind / priority 1–3 / status / attempts `current / bucket` with
bucket default 15 / file), `- **informal**` (statement + proof sketch), `- **prep**` (Lean decl
names with one-line descriptions), `- **log**` table (Date | Att | Status | Goal | Proof Feedback
| Review Feedback | Tmp, newest first). Numbering: `## 10. Group` / `### 10.1. item` /
`#### 10.1.1. sub-item`; group ranges 10–19 Definitions, 20–39 Basic properties, 40–59 Core
lemmas, 60–79 Main theorem, 80–99 Corollaries. Status lifecycle `pending → working → done`,
`bucket/bucket` with status ≠ done ⇒ blocked. The MT blueprint will be
`doc/moser-tardos/02_blueprint/BLUEPRINT.md` in the **outer** repo with its own fresh 10–99
numbering.

**Tmp-file rule specific to this repo's blueprints** (LLL blueprint items 10.1/10.5 logs): tmp
files are *continuations of the main module* — `import StatsMLlib.Probability.MoserTardos`,
re-`open` the namespace and re-declare the variable block, because **variables and `open`s are
file-scoped and are NOT carried over by `import`**. First item (the file skeleton) is written by
Setup directly.

### 5.2 Git choreography (branch state verified 2026-08-16)

**Submodule** (`/Users/zhuzekai/workspace/StatsLean/StatsMLlib`):

- Current branch `zzk/moser-tardos` at `c6e4461` — byte-identical to
  `zzk/lovasz-local-lemma-gptv2`'s HEAD (the branch was created from it); **zero commits on the
  MT branch, working tree clean**.
- Remote: `origin = git@github.com:hehepig166/StatsMLlib.git` (the user's fork of
  Lean-MoDS/StatsMLlib). The fork already carries `zzk/lovasz-local-lemma-gptv2` at `c6e4461`
  (verified via `git ls-remote`), so the MT base PR is live on the fork. `zzk/moser-tardos` has
  **no upstream yet** — first push should be `git push -u origin zzk/moser-tardos` after the first
  commit.
- The MT PR therefore **stacks on the LLL gptv2 PR** (fork branch → upstream), exactly like
  `zzk/talagrand-gpt-review` stacks on `zzk/talagrand` — the `PR_BODY_STACKED.md` file in
  `doc/talagram/04_pr/` is the house pattern for announcing that stacking.

**Outer repo** (`/Users/zhuzekai/workspace/StatsLean`):

- StatsMLlib is tracked as a **gitlink** entry (mode `160000`, current `c6e4461`, matching the
  submodule HEAD — pointer is committed and up to date; outer `git status` is clean apart from
  untracked `doc/moser-tardos/` and `doc/talagram/04_pr/PR_BODY_STACKED.md`).
- **Quirk (pre-existing, unchanged by MT):** there is **no `.gitmodules`** file, so
  `git submodule status/update` fails ("no submodule mapping found"); the repo is not a
  registered submodule — just a gitlink. The established "bump StatsMLlib pointer" commits edit
  that gitlink directly (`git add StatsMLlib` inside the outer repo after the submodule advances)
  and work fine; only fresh-clone submodule tooling is affected.
- Rhythm (verified in both logs): code attempts → submodule commits `feat(MT.NN): attempt N —
  <summary>`; review-done → outer `doc(MT.NN): mark <item> as done; bump StatsMLlib pointer`
  (which stages both the doc edit and the gitlink update); milestones → `doc: <milestone>`; at
  the end → `doc: PR description for Moser–Tardos; bump StatsMLlib pointer`, then the stacked PR
  from the fork with `Co-authored-by` trailers per CONTRIBUTING.md.

---

## 6. Harness integration notes

The harness at `/Users/zhuzekai/workspace/StatsLean/harness/` (README.md, CONVENTIONS.md,
BLUEPRINT_TEMPLATE.md, `skills/{orchestrator,planner,survey,setup,proof,review}.md`) applies to
the MT blueprint phase unchanged in substance:

- Attempt loop **Survey → Setup → Proof → Review**; tmp files `tmp_<theme>.lean` **next to the
  target Lean file** (`StatsMLlib/Probability/tmp_<theme>.lean` for MT), 500-line tmp limit
  (split the item if exceeded), integrated-then-deleted on success, kept if viable, deleted if
  broken.
- Review gates verified in the LLL run and applicable to MT: `lake env lean` exits 0, LSP
  diagnostics empty, no `sorry`/`axiom`/`admit`/`native_decide`, no `#`-commands/`λ`, no lines
  over 100 chars, `lake build StatsMLlib.Probability.MoserTardos` clean with weak linters.

**Two deliberate deviations from the generic harness defaults, per established project practice**
(LLL and Talagrand both did this — keep them for MT):

1. **BLUEPRINT.md lives in the outer repo** at `doc/moser-tardos/02_blueprint/BLUEPRINT.md`
   (the generic CONVENTIONS.md says "project root, e.g. StatsMLlib/BLUEPRINT.md" — the project
   instead keeps blueprints with the doc lifecycle, and the submodule tree never contains
   blueprint files; the stray-tmp commit `df8a6fc chore: remove stray harness/tmp scratch file`
   shows how strictly that is enforced).
2. **Commit messages use blueprint item numbers**, `feat(MT.NN): attempt N — …` (not the
   generic `feat(<item-slug>)`), and branches are `zzk/<topic>` (not `blueprint/<item-slug>`).

---

## 7. Risks

1. **Cross-branch count drift in FILE_TREE/README.** Talagrand's `ConvexDistance.lean` (+1
   module) lives only on the unmerged `zzk/talagrand*` branches. MT's edit is 90→91 on the current
   LLL-based stack, but if Talagrand merges first, rebase and re-derive the counts. Mitigation:
   re-verify `find … -name "*.lean" | wc -l` and the FILE_TREE table against the merge base at PR
   time (the LLL run absorbed exactly this class of drift once).
2. **`(μ := μ)` / autoParam traps on `Ω_N`.** `IndepSet`'s measure defaults to `volume_tac`, not
   the local `μ`; on `Ω_N` the relevant measure is the product measure `μN`, which is never the
   ambient volume. Every independence use must be `(μ := μN)`-qualified and the
   `IsProbabilityMeasure μN` instance threaded explicitly. The LLL file hit this and documented
   it (blueprint 10.5); MT will hit it more (coupling lemma, bridge). Mitigation: a prep note +
   compile test in the blueprint's first items.
3. **Outer repo lacks `.gitmodules`.** The gitlink works for pointer bumps but any tooling that
   assumes a registered submodule (fresh clone, `git submodule update`) breaks. Pre-existing,
   out of MT's scope to fix; just don't rely on submodule commands.
4. **Flat-file size pressure.** If agent B's estimate lands at/above ~1500 lines, the flat choice
   must be revisited at blueprint time (folder promotion mid-attempt-loop is churn: item `file:`
   paths, tmp locations, and FILE_TREE all change). Decide before the first attempt.
5. **Bridge section scope creep.** The cross-file `IsDependencyGraph` bridge is the only part of
   MT that depends on the LLL file; if the determinism→measurability plumbing fights back, cut it
   to a follow-up item (group 90-style, priority 1) — the main bound does not need it.
6. **`x i = 0` division hygiene.** The main bound's `x/(1-x)` requires the `x = 0` case handled
   without division (PLAN §3). This is a proof-structure risk for the main theorem, not a
   conventions risk, but it interacts with the convention that hypotheses stay ENNReal/
   `ofReal`-valued — handle it the way the LLL file handles `1 - x i > 0` (explicit `hx₁`-style
   hypotheses plus a separate trivial case).

---

## 8. Open questions

1. **Flat vs folder — confirm with agent B's decomposition table.** Single file
   `Probability/MoserTardos.lean` is recommended for ≤ ~1500 lines. If B's estimate exceeds
   that (or the corollary set grows), adopt the `MoserTardos/{Basic,Main}.lean` split-point from
   §3 — which agent B should endorse or refute explicitly in `B_proof_strategy.md`.
2. **Where does the LLL bridge live?** Recommended: a final section of `MoserTardos.lean` (it is
   a corollary of the MT variable model). Alternative: an appendix in `LovaszLocal.lean` itself.
   If the bridge is sectioned out of PR 1, the MT core loses its only StatsMLlib import and
   becomes fully mathlib-based — is that the preferred PR-1 shape?
3. **README "Selected results" update.** The LLL PR updated counts but did **not** add an LLL
   line to "Selected results" (lines 33–46). Should MT add one, and should the LLL line be added
   retroactively in the same edit? (Needs a user/maintainer call; either way it is one EDIT row
   in §4.)
4. **Header/AUTHORS.md.** Reuse `Copyright (c) 2026 Zhu Zekai` / `Authors: Zhu Zekai` verbatim
   (LLL precedent)? AUTHORS.md stays untouched unless a new significant author joins — and if
   co-written, every commit gets `Co-authored-by` trailers (CONTRIBUTING.md lines 16–17).
5. **Item numbering and commit prefix.** Confirm the MT blueprint gets a fresh 10–99 numbering in
   its own `doc/moser-tardos/02_blueprint/BLUEPRINT.md` and the commit prefix is `MT.NN`
   (CHECKLIST.md already assumes `feat(MT.NN)`); the LLL prefix `LL.NN` stays reserved for the
   LLL branch.
6. **PR stacking mechanics.** `zzk/moser-tardos` is local-only and stacks on
   `zzk/lovasz-local-lemma-gptv2` (pushed). Confirm with the user: push the MT branch after its
   first commit and open the stacked PR immediately, or hold until MT PR 1 is complete (the
   talagrand stack opened its second PR only after review rounds)?
7. **Symmetric form scope.** `ep(d+1) ≤ 1 ⟹ E_N[#resamples] ≤ m/d` — in MT PR 1 or a follow-up
   (LLL precedent: symmetric forms were PR 2, added mid-flight via blueprint items 80.10–80.20)?
   This affects the flat-file line budget and the blueprint's group-80 content.
