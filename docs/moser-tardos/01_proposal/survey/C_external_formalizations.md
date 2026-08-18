# Survey C: External Moser–Tardos Formalizations and Literature

Scope: what machine-checked Moser–Tardos (MT) art exists outside this project, what the
literature says, and what lessons they hold for the StatsMLlib proposal. All facts verified
2026-08-16 (URLs listed with access date 2026-08-16 unless noted).

**Headline findings.**

1. **Isabelle AFP: no Moser–Tardos.** The `Lovasz_Local` entry (Edmonds, 2023) is classical
   (non-constructive) LLL only, still as of the Isabelle2025-2 release (2026-02-06) *and* the
   current `afp-devel` branch. The CPP 2024 paper's "constructive version is future work" is
   still true.
2. **Lean: Moser–Tardos Theorem 1.2 and Haeupler–Saha–Srinivasan Theorem 2.2 are already
   fully formalized, sorry-free**, in `EdouardBonnet/moser-tardos` (Lean v4.30.0, mathlib rev
   `c5ea0035`, last push 2026-08-08, 3.4k lines), registered as submission **lax-41** in the
   "Lax Lean Archive" (laxarchive.org) on 2026-08-04 — the only *registered* (proof-checked)
   submission there. It is **not** in mathlib (loogle/issue-search/docs-search all negative).
3. **Other provers: nothing usable.** No completed MT formalization in Coq, Agda, HOL Light,
   Mizar, or PVS. Two near-misses: a 2010 DIMAP talk sketch (Krčál, Coq, slides only) and a
   2014 bounded-arithmetic thesis formalizing *Moser's* Fix-It for k-SAT in VPV + sWPHP(FP)
   (a complexity-theory framework, not an interactive prover).
4. **Strategic consequence:** the core of our proposed target (MT Thm 1.2 in the variable
   framework) has just been done in Lean, and the existing repo shows the *infinite-table*
   route works smoothly in mathlib (`Measure.infinitePi`, which our v4.32.0 also has). Our
   proposal's differentiator is the **finite-truncation formulation** (PLAN §3) plus
   StatsMLlib integration — but the duplication question must be faced explicitly (see §6, §7).

---

## 1. Isabelle AFP

**The AFP entry exists, and it is classical only.**
[*"General Probabilistic Techniques for Combinatorics and the Lovasz Local Lemma"*](https://www.isa-afp.org/entries/Lovasz_Local.html),
by **Chelsea Edmonds**, submitted **2023-09-20**. Release history spans Isabelle2023
(2023-09-22) to **Isabelle2025-2 (2026-02-06)**.

### Theories (session `Lovasz_Local`)
From the [theory browser](https://www.isa-afp.org/browser_info/current/AFP/Lovasz_Local/):

| Theory | Role |
|---|---|
| `PiE_Rel_Extras` | extras for indexed products / `Π⇩E` relations |
| `Digraph_Extensions` | extras on Noschinski's `Graph_Theory` digraphs |
| `Prob_Events_Extras` | probability-space/events helpers |
| `Cond_Prob_Extensions` | conditional probability, Bayes |
| `Indep_Events` | **mutual independence of events** (the dependency-graph glue) |
| `Basic_Method` | generic probabilistic-method (existence) framework |
| `Lovasz_Local_Lemma` | the LLL itself + variations |
| `Lovasz_Local_Root` | session root (imports the above) |

Dependencies: `Card_Partitions`, `Design_Theory`; used by
[`Hypergraph_Colourings`](https://www.isa-afp.org/entries/Hypergraph_Colourings.html).

### Moser–Tardos: absent — verified three ways
- The entry page and abstract mention no constructive/algorithmic content (the abstract says:
  "the first formalisation of the pivotal Lovász local lemma … Both the original formalisation
  and several of the variations used dependency graphs …").
- The theory list contains no resampling/algorithm theory.
- I downloaded the **current `afp-devel` sources** (ahead of the Feb 2026 release) of
  `Lovasz_Local_Lemma.thy` from
  [Heptapod](https://foss.heptapod.net/isa-afp/afp-devel/-/raw/branch/default/thys/Lovasz_Local/Lovasz_Local_Lemma.thy)
  and grepped: no Moser, no Tardos, no resampling, no witness trees. The main theorem is the
  classical one (see next item).

(The LLL survey's §1 covers this entry's proof route in detail — the strong-induction
`lovasz_inductive` — and remains accurate; not repeated here.)

### What is there — statements we could conceptually reuse
The entry is in the **event model**, not the variable framework: there are no random
variables, no `vbl`, no overlap graph. The dependency condition is a locale assumption of
mutual independence against non-neighbors:

```
locale dependency_digraph = pair_digraph "G :: nat pair_pre_digraph" + prob_space "M :: 'a measure"
  for G M + fixes F :: "nat ⇒ 'a set"
  assumes vss: "F ` (pverts G) ⊆ events"
  assumes mis: "⋀ i. i ∈ (pverts G) ⟹
    mutual_indep_events (F i) F ((pverts G) - ({i} ∪ neighborhood i))"
```

with (in `Indep_Events.thy`):

```
definition mutual_indep_events :: "'a set ⇒ (nat ⇒ 'a set) ⇒ nat set ⇒ bool"
  where "mutual_indep_events A F I ⟷ A ∈ events ∧ (F ` I ⊆ events) ∧
    (∀ J ⊆ I . J ≠ {} ⟶ prob (A ∩ (⋂j ∈ J. F j)) = prob A * prob (⋂j ∈ J. F j))"
```

Main theorem (`Lovasz_Local_Lemma.thy`, `theorem lovasz_local_general`): for finite nonempty
`A`, events `F i`, reals `f i ∈ [0,1)` with
`prob (F Ai) ≤ f Ai * ∏_{Aj ∈ neighborhood G Ai} (1 − f Aj)` and `pverts G = A`,

```
prob (⋂ Ai ∈ A. space M − F Ai) ≥ ∏ Ai ∈ A. (1 − f Ai)   and   ∏ (1 − f Ai) > 0
```

plus `lovasz_local_general_positive`, `lovasz_local_symmetric`, `lovasz_local_symmetric4`
(the `4p(d+1) ≤ 1` constant form).

**Reusable for us:** (i) the *statement shape* `μ(⋂ Āᵢ) ≥ ∏(1−xᵢ) > 0` (our constructive-LLL
corollary should land on exactly this); (ii) the *mutual-independence-as-a-predicate*
formulation — for the variable framework this becomes a *theorem* ("events on disjoint
variable sets are independent") rather than an assumption, but the predicate shape transfers
to mathlib's `ProbabilityTheory.iIndepSets`; (iii) the `S ≠ ∅` conditioning hygiene note
(Isabelle's `P(Ω)=1` pitfall has a mathlib analogue: `μ[|]` on null sets); (iv) the rationale
for **directed** dependency graphs ("multi-edges are irrelevant", comment at line 49 of the
theory). **Not reusable:** the locale/event-model scaffolding itself — MT needs the variable
framework, which the AFP entry does not have.

---

## 2. Edmonds & Paulson, CPP 2024 — scope and follow-ups

**Citation (dblp-verified):** Chelsea Edmonds and Lawrence C. Paulson, *"Formal Probabilistic
Methods for Combinatorial Structures using the Lovász Local Lemma"*, CPP 2024 (13th ACM
SIGPLAN Int. Conf. on Certified Programs and Proofs), pp. 132–146, DOI
[10.1145/3636501.3636946](https://doi.org/10.1145/3636501.3636946);
arXiv:[2310.00513](https://arxiv.org/abs/2310.00513) (v2, 2024-01-08, "accepted to CPP2024").

**Scope: classical LLL only, no algorithmic content.** The paper formalizes the probabilistic
method framework + general LLL + symmetric variants + hypergraph colouring applications
(`Hypergraph_Colourings`). The earlier LLL survey already noted the paper's statement that a
constructive version would "likely benefit from past formalisations of probabilistic
algorithms" (future work). Nothing in the paper or its abstract touches MT, resampling, or
witness trees (re-checked on the arXiv page 2026-08-16).

**Follow-ups: none on the LLL/MT axis.** dblp for Chelsea Edmonds
([link](https://einstein.dagstuhl.de/pid/264/4019.html?view=by-type)) shows no journal version
of the LLL paper and no constructive-Local-Lemma sequel (her recent work is elsewhere, e.g. a
2025 J. Autom. Reasoning paper on Edmonds' blossom algorithm — unrelated). The AFP entry is
maintained (releases through Isabelle2025-2, 2026-02-06) but has not grown an MT theory. So
**the constructive LLL remains open territory in Isabelle** as of 2026-08-16.

---

## 3. Lean: `EdouardBonnet/moser-tardos` — current-state verdict

Repo: https://github.com/EdouardBonnet/moser-tardos — *"Formalization in Lean 4 of the
Moser–Tardos theorem, the effectivization of the Lovász local lemma."*

### Current state (all verified 2026-08-16 via GitHub API + downloaded sources)
- **Created 2026-08-04, last push 2026-08-08** (5 commits: "Formalize the Moser-Tardos
  theorem" → "Separate Moser-Tardos semantic definitions" → "Formalize HSS distributional
  local lemma" → "Finalize submission metadata"). 55 KB, Apache-2.0, 0 stars, not archived.
- **Lean v4.30.0, mathlib rev `c5ea00351c28e24afc9f0f84379aa41082b1188f`** (from
  `manifest.yaml`). ~6 weeks older than our v4.32.0 target; probability APIs used are present
  in v4.32.0 (spot-checked `Measure.infinitePi` et al. — see §6).
- **Part of the "Lax Lean Archive"** (https://laxarchive.org/, org
  https://github.com/lax-archive): an "arXiv for formalization" where each submission splits
  `concepts/` (definitions + theorem *statements*) from `proofs/` (sorry-free derivations).
  This repo is submission **`lax-41` — "Constructive Lovász Local Lemma"**, dated 2026-08-04,
  "4 concepts, 2 proofs", status **Registered** — the *only* registered (machine-checked)
  submission among the archive's 18 (most are drafts). The author (Édouard Bonnet) is an
  active LAX contributor (his fork of `lax-submissions` pushed 2026-08-15).
- **Sorry-free: verified by grep** on the downloaded sources:
  `proofs/Lax41Proofs/MoserTardos.lean` (2109 lines, 90.7 KB): 0 sorry / 0 axiom / 0 admit;
  `proofs/Lax41Proofs/HaeuplerSahaSrinivasanTheorem22.lean` (1013 lines, 47.2 KB): 0/0/0.
  The two `axiom` declarations are in `concepts/` **by LAX design** (concepts = the formal
  interface); the proofs package proves matching `theorem`s (e.g. `theorem moser_tardos` with
  `conclusion: Lax41.MoserTardos.moser_tardos`) without any axiom or sorry.
- **Not in mathlib**: loogle `MoserTardos` → unknown identifier; mathlib4 GitHub issue search
  `moser-tardos` → 0 results; `mathlib4_docs` find page → empty; local project search → empty.

### What it formalizes (exact statements)
Scope per `abstract.md`: MT Theorem 1.2 and HSS Theorem 2.2, with "resampling tables, proper
witness trees, branching-process weight estimates, and a finite-termination argument".

**MT Theorem 1.2** (`concepts/Lax41/MoserTardos.lean`, `axiom moser_tardos`; proved at
`proofs/Lax41Proofs/MoserTardos.lean` line 2071):

```lean
axiom moser_tardos
    {Event : Type} [Fintype Event] [DecidableEq Event]
    {Variable : Type} [Fintype Variable] [DecidableEq Variable]
    (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (distribution i)]
    (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (badEvent_measurable : ∀ A, MeasurableSet (badEvent A))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (x : Event → NNReal)
    (x_positive : ∀ A, 0 < x A)
    (x_less_than_one : ∀ A, x A < 1)
    (local_lemma_hypothesis : ∀ A,
      eventProbability Value distribution variablesOf badEvent A ≤
        ((x A * ∏ B ∈ dependencyNeighborhood variablesOf A, (1 - x B) : NNReal) : ℝ≥0∞)) :
    (∃ assignment : Assignment Value, ∀ A, ¬violates Value variablesOf badEvent assignment A) ∧
    (∀ A, expectedResamplings Value distribution variablesOf badEvent selectionRule A ≤
      ((x A / (1 - x A) : NNReal) : ℝ≥0∞)) ∧
    (∑ A : Event, expectedResamplings … A) ≤ ∑ A : Event, ((x A / (1 - x A) : NNReal) : ℝ≥0∞)
```

**HSS Theorem 2.2** (`concepts/Lax41/HaeuplerSahaSrinivasanTheorem22.lean`; proved at
`proofs/Lax41Proofs/HaeuplerSahaSrinivasanTheorem22.lean` line 900): under the same LLL
hypotheses on a bad-event family `badEvents`, for *any* event `B` determined by the same
variables,

```
probabilityEventEverOccurs … B ≤ eventProbability … B * ∏_{C ∈ Γ(B)} (1 − x C)⁻¹
  ∧ probabilityEventInOutput … B ≤ same bound
```

### Their modeling choices (from the downloaded sources)

**Variable framework** (`MoserTardosDefinitions.lean`, 142 lines):
- `ResamplingTable Value := (i : Variable) × Nat → Value i.1` — the **infinite table** of
  fresh samples, measured by `MeasureTheory.Measure.infinitePi` (countable product measure).
  *No finite truncation.* Termination is almost sure via the expected-bound + a table that
  actually terminates.
- `LocalAssignment Value indices := (i : indices) → Value i.1` — events are **directly** sets
  of local assignments on their own scope: `badEvent A : Set (LocalAssignment Value
  (variablesOf A))`. There is **no separate "A is determined by vbl A" hypothesis** — the
  type of `badEvent` encodes determinism. (Cleaner than PLAN §3's `A i : Set (Π j, Ω j)` +
  determinism side condition — see §6.)
- `dependencyNeighborhood variablesOf A := univ.filter (B ≠ A ∧ ¬Disjoint (variablesOf A)
  (variablesOf B))` — the variable-overlap graph, no graph parameter.
- `ResamplingRule` = deterministic rule `choose : Assignment → Option Event` with
  `measurable_fiber`, `sound` (`choose = some A ⟹ A violated`), `complete` (`choose = none ⟹
  nothing violated`). The algorithm itself is `runCounts` (Nat.rec over `advanceCounts`),
  `resamplingLog : table → Nat → Option Event`, `resamplingCount := ∑' t, indicator {log t =
  some A}`, `expectedResamplings := ∫⁻ table, resamplingCount ∂ tableMeasure`.

**Witness trees** (three representations, each with a job):
- `BTree E n a` (inductive: `BTree E 0 a = Fin 0`; `BTree E (n+1) a = (b : E) → Option
  (BTree E n b)`; Fintype instance) — the **algebraic** tree type for the weight calculus.
  `BTree.weight r p := ∏ vertices p label`; branching-process recurrences
  `sum_weight_succ` and the charge lemma
  `sum_weight_le_of_charge : p a * ∏ b (if r a b then 1 + y b else 1) ≤ y a ⟹
   ∀ n a, ∑_{t : BTree E n a} t.weight r p ≤ y a`
  — the Galton–Watson formula, **without formalizing any stochastic process**: the GW bound
  is a purely combinatorial charge induction over depth-bounded trees.
- `TimedTree E := Finset (Nat × List E)` — the **construction** side (T(Λ,t)): time-stamped
  paths, `deepest`-eligible + `insertEarlier` deterministic tie-break; `TimedTree.Good`
  bundles nine structural properties (pathsUnique, timesUnique, chronological, represents,
  closed, prefixClosed, edgeValid, depthBound, root_mem) proved by one induction
  (`buildTimedTree_good`).
- `ProperTree r root` (extensional: a `Finset (List E)` of paths with `root_mem`,
  `prefixClosed`, `edgeValid`, **`stronglyProper`**: distinct same-length paths have
  *unrelated* end labels) + `ProperTree.weight = ∏_{q ∈ paths} p (pathLabel root q)`,
  `historyTree` (T(Λ,t)), `occurrenceTree`, and injectivity
  `occurrenceTree_injectiveOn` — proved via `labelCount root tree = t` (the root's label
  count equals the time index; cute and effective).
- `r = scopeRelated scope a b := a = b ∨ ¬Disjoint (scope a) (scope b)` (reflexive,
  symmetric) — properness of children = pairwise disjoint scopes, exactly MT's condition.

**Coupling lemma** (`ProperTree.measure_passes`): for each tree vertex v and variable i in its
scope, read the fresh sample at row `cellIndex = (i, sampleNumber)` where
`sampleNumber q i := #{strictly deeper paths p | i ∈ scope (pathLabel p)}` — the count of
deeper vertices using i. Strong properness makes `cellIndex` injective, so `extractCells`
pulls *independent fresh* coordinates out of the infinite product (via
`Measure.map_infinitePi_infinitePi_of_inj`), `MeasurableEquiv.piCurry` regroups cells by
vertex, and `infinitePi_pi` turns the bad product event's measure into
`∏ᵥ eventProbability (bad (label v))` = `t.weight`. Then
`resamplingCount ≤ passingTreeCount := ∑' tree, indicator (tree.passes)` +
`expectedResamplings_le_of_charge` assemble the bound; `exists_table_passingTreeCount_lt_top`
+ `resamplingTimes_finite_of_count_lt_top` give finite termination, and
`exists_good_assignment` yields the constructive LLL conclusion.

**HSS proof** reuses all of this with a distinguished "query" label: `queryHolds`,
`BTree.sum_queryWeight` / `queryWeight`, `charge_allowedDescendants`,
`measure_queryEverOccurs_le_rootProduct`, and finally
`eventOccursInOutput_subset_eventEverOccurs` + `theorem_2_2`. Definitions for the HSS side
(`HaeuplerSahaSrinivasanDefinitions.lean`): `BadEventIndex badEvents := {A // A ∈ badEvents}`
(bad events form a *Finset* here, and B may be outside the family),
`eventOccursAt`/`eventEverOccurs`, `outputTime := Nat.find (∃ n, log n = none)` (0 on the
null non-terminating set), `outputAssignment`, `eventOccursInOutput`,
`probabilityEventEverOccurs`/`probabilityEventInOutput`.

### Verdict — what NOT to duplicate, what to borrow
- **Do not duplicate:** MT Thm 1.2 and HSS Thm 2.2 in the infinite-table formulation, as
  formalized (sorry-free, registered) in lax-41. Any StatsMLlib work that lands the *same*
  theorem in the *same* formulation would be the third Lean MT effort with zero delta except
  house style. (There is one earlier non-formalization: `ugtcs/moser-tardos`, a 2019 Jupyter
  notebook — irrelevant. The two classical-LLL Lean repos from the LLL survey — `nsglover/…`,
  `Mahesh-Ramani/…` — are classical only, no MT.)
- **Borrow freely** (see §6): the `LocalAssignment` event typing, the `ResamplingRule`
  parameterization, the `BTree`/`ProperTree`/`TimedTree` three-layer witness-tree design, the
  `cellIndex`/deeper-paths fresh-sample coupling, the pure charge calculus in place of a GW
  process, and the `labelCount` injectivity trick. All of it is plain mathlib (v4.30.0) code;
  the key dependencies (`Measure.infinitePi`, `MeasurableEquiv.piCurry`,
  `map_infinitePi_infinitePi_of_inj`, `ENNReal.tsum_comp_le_tsum_of_injective`) exist in our
  v4.32.0 (spot-checked via `lean_local_search` on `Mathlib/Probability/ProductMeasure.lean`).

---

## 4. Other provers

- **Coq:** no completed MT formalization. GitHub repository search `moser-tardos coq` → 0
  results; `moser-tardos` (all languages) → only the Lean repo + a 2019 Jupyter notebook.
  **Near-miss:** a talk at the [DIMAP Workshop on Extremal and Probabilistic Combinatorics
  (Warwick, 18–25 July 2010)](https://warwick.ac.uk/fac/cross_fac/dimap/events/webc/) by
  Marek Krčál, slides at
  [Marek.pdf](https://warwick.ac.uk/fac/cross_fac/dimap/events/webc/programme/Marek.pdf)
  (image-only PDF, no text layer; content per search-engine snippet): describes *how to
  formalize* MT's constructive LLL in Coq — the random source as `∏_{P∈P} P^ℕ`, dependency
  graph via `coor(A)`, witness trees `τ_C(t)`. No repository, paper, or artifact is findable;
  treat as a design sketch, not prior art. (Caveat: the programme page lists only "Marek";
  attribution is from the search snippet and could not be re-verified from the un-OCR-able
  PDF.)
- **Bounded arithmetic (complexity theory, not an ITP):** Dai Tri Man Lê, *"Bounded
  Arithmetic and Formalizing Probabilistic Proofs"*, PhD thesis, University of Toronto, 2014
  ([record](https://utoronto.scholaris.ca/items/227182c5-42ae-4232-945d-076b0a5e0a5f)),
  Theorem 75: **VPV + sWPHP(FP)** proves the existence of a random string on which *Moser's*
  recursive solve/locally_fix outputs a satisfying assignment for k-SAT with clause
  neighborhood ≤ 2^{k−3}. This is Moser's Fix-It (the k-SAT special case), not the general
  MT algorithm, in a logical strength framework — interesting for the Fix-It extension but
  no engineering lessons for Lean.
- **Agda, HOL Light, HOL4, Mizar, PVS, Metamath:** nothing found (searches 2026-08-16; same
  conclusion as the LLL survey §3, which see for the Coq `alea`/Infotheo infrastructure notes).
- **Lean 3:** no MT (the only Lean 3 LLL is `nsglover/lean-lovasz-local-lemma`, classical).
- **Related discussion worth citing:** MathOverflow question
  [*"Formalizing Entropy Compression (as used to constructify the Lovász Local Lemma)"*](https://mathoverflow.net/questions/347787/)
  — documents the subtleties of making Moser-style entropy arguments rigorous (prefix-reading,
  truncation), useful background if a Fix-It extension is ever attempted.

---

## 5. Literature anchors

### Moser–Tardos 2010 (the paper we formalize)
R. A. Moser, G. Tardos, *"A constructive proof of the general Lovász Local Lemma"*,
**J. ACM 57(2), Article 11, pp. 11:1–11:15, 2010**, DOI
[10.1145/1667053.1667060](https://doi.org/10.1145/1667053.1667060);
arXiv:[0903.0544](https://arxiv.org/abs/0903.0544) (v3, 2009-05-20, 8 pp.; v3 is the canonical
version). Theorem numbering verified against the arXiv v3 full text:
- **Theorem 1.1** — general (asymmetric) LLL, `Pr[A] ≤ x(A) ∏_{B∈Γ(A)} (1−x(B))` ⟹
  avoidance probability ≥ `∏ (1−x(A))` (their statement uses `vbl`/variable framework and
  `Γ`). Note: the paper's Thm 1.1 is the classical LLL *in the variable framework*; our
  proposal's "constructive LLL" corollary is exactly this, derived constructively.
- **Theorem 1.2** — *the* target: the sequential resampling algorithm resamples each `A` at
  most an expected `x(A)/(1−x(A))` times; total expected resamplings ≤ `∑ x(A)/(1−x(A))`.
- **Theorem 1.3** (out of scope) — parallel version: with slack `Pr[A] ≤ (1−ε)·x(A)·∏(1−x(B))`,
  the parallel algorithm takes expected `O(1/ε · log ∑ x(A)/(1−x(A)))` rounds.
- **Theorem 6.1** (out of scope) — lopsided version with lopsidependency graph `Γ'`: same
  `x(A)/(1−x(A))` bound under the weaker hypothesis `Pr[A] ≤ x(A) ∏_{B∈Γ'(A)} (1−x(B))`.
- Proof structure (paper §2–3): §2 "Execution logs and witness trees" (witness trees from the
  log; Lemma 2.1 bounds the probability a fixed tree occurs by `∏ Pr[[v]]`), §3 "Random
  generation of witness trees" (multitype Galton–Watson process generating proper witness
  trees; Lemma 3.1 gives the tree probability; sums to the Thm 1.2 bound). This is exactly
  the route of our notes (`ref/moser_tardos_algorithmic_lll_notes.md` §8–§17) and of lax-41.

### Haeupler–Saha–Srinivasan 2011 (the lax-41 companion theorem)
B. Haeupler, B. Saha, A. Srinivasan, *"New Constructive Aspects of the Lovász Local Lemma"*,
**J. ACM 58(6), Article 28, pp. 28:1–28:28, 2011**, DOI
[10.1145/2049697.2049702](https://doi.org/10.1145/2049697.2049702);
arXiv:[1001.1231](https://arxiv.org/abs/1001.1231). **Theorem 2.2** (the distributional LLL) is
what lax-41 formalizes: for any event `B` determined by the same variables,
`Pr[B ever occurs] ≤ Pr[B] · ∏_{C∈Γ(B)} (1−x(C))⁻¹`, hence also for `B` in the output.

### Alon–Spencer
N. Alon, J. H. Spencer, *The Probabilistic Method*, **4th edition, Wiley, 2016**, ISBN
978-1-119-06195-3 (Zbl 1333.05001). **Chapter 5 "The Local Lemma"** section list (verified
via publisher/bookseller listings 2026-08-16): 5.1 The Lemma; 5.2 Property B and Multicolored
Sets of Real Numbers; 5.3 Lower Bounds for Ramsey Numbers; 5.4 A Geometric Result; 5.5 The
Linear Arboricity of Graphs; 5.6 Latin Transversals; **5.7 The Algorithmic Aspect**; 5.8
Exercises. The 4th-edition preface (per the MAA review) says a "breakthrough approach to the
Local Lemma" — i.e. Moser–Tardos — is described in Chapter 5, i.e. in §5.7. (The exact
contents of §5.7 in the 4th ed. could not be verified from open listings — see Open
questions.) *There is no lopsided-LLL section in Alon–Spencer;* the lopsided reference is
Erdős–Spencer 1991 (see the LLL survey §5).

### Tao's blog — correction of the expected anchor
There is **no** "Tao, *The lopsided local lemma*" post (searched 2026-08-16). The real Tao
anchor is [*"Moser's entropy compression argument"*](https://terrytao.wordpress.com/2009/08/05/mosers-entropy-compression-argument/)
(2009-08-05): it covers **Moser's Fix-It algorithm for k-SAT** (the `d < 2^{k−3}` regime) and
coins "entropy compression" — relevant only to the *out-of-scope* entropic/Fix-It variant
(slides pp. 165–192), not to the MT witness-tree proof. For a clean witness-tree exposition,
the strongest open anchors are: our local notes, the paper itself (§2–3), the 尹一通 slides,
and (for the framework) lax-41's `abstract.md` which reads as a one-paragraph proof map.

### 尹一通 slides (local)
尹一通 (Yin Yitong), *Basics of Randomized Algorithms*, 南京大学 "计算理论之美" (Beauty of
Computation Theory) summer school, **2025-06-30**; 193 slides. Local:
`doc/moser-tardos/01_proposal/ref/尹一通-lll.pdf` (text extract `/tmp/yyt_lll_slides.txt`).
Pages 73–163: variable framework + MT algorithm, execution log, resampling table, witness
trees with a worked example, coupling Lemma 1, GW process Lemma 2 — matches our proof route;
pp. 165–192 (Fix-It/entropic) are out of scope for the core. Citation as an informal lecture
note; the LLL survey §4 has the full coverage map.

---

## 6. Lessons for our design

1. **The infinite-table route is proven and cheap in mathlib.** lax-41 shows the whole MT
   proof over `Measure.infinitePi` fits in ~2.1k lines of ordinary mathlib measure theory,
   and all the product-measure lemmas it needs exist in v4.32.0 (`Measure.infinitePi`,
   `infinitePi_pi`, `map_infinitePi_infinitePi_of_inj`, `infinitePi_map_piCurry`,
   `MeasurableEquiv.piCurry`). Our PLAN §3 finite-truncation architecture is a valid,
   formally-different formulation, but it is **no longer the forced choice** — the
   a.s.-termination/infinite-table formulation is now precedent-backed. (Decision for the
   orchestrator + agent B; see Open questions.)
2. **Type events as `Set (LocalAssignment Value (vbl A))`, not as subsets of the full product
   space.** lax-41's typing encodes "A is determined by vbl A" for free; PLAN §3's
   `A i : Set (Π j, Ω j)` + determinism hypothesis is strictly more work (the `comap`-or-
   cylinder formulation of determinism then has to be threaded through every lemma). The
   one price: `eventProbability` must be defined on the local product
   `Measure.infinitePi`/`Measure.pi` of the scope — which is exactly what
   `localMeasure` does.
3. **Parameterize the pick rule.** `ResamplingRule` (deterministic `choose : Assignment →
   Option Event`, measurable fibers, sound/complete) matches MT's "arbitrary violated event"
   and costs little; the PLAN's fixed least-index rule is an instance of it. Keep the
   parameterization (also needed for any HSS-style extension later).
4. **Split the witness tree into an algebraic type and a construction type.** `BTree` (weight
   calculus, charge induction, Fintype by depth) vs `TimedTree`/`ProperTree` (history-driven
   construction, extensional Finset-of-paths, `Good` bundling the structural lemmas). The
   two meet at `ProperTree.toBTree`. This separation is what keeps the GW part purely
   combinatorial — **no stochastic process needs formalizing**; the charge lemma
   `p a · ∏(1+y_b) ≤ y a ⟹ Σ weight ≤ y a` is the whole "Galton–Watson" content.
5. **The fresh-sample coupling via `cellIndex`:** assign each tree vertex v and variable
   i ∈ vbl(v) the table row `(i, #{deeper vertices using i})`; strong properness ⟹
   injective ⟹ the extracted cells are independent fresh samples (one
   `map_infinitePi_infinitePi_of_inj` + one `piCurry` + one `infinitePi_pi` give the measure
   of "tree passes" = `∏ᵥ Pr(bad (label v))`). This is the exact MT §2 argument, and it is
   *simpler* than the PLAN's "abstract τ-check → coupling map" sketch because the map is
   concrete. Recommend adopting this construction verbatim in spirit.
6. **Injectivity of `t ↦ T(Λ,t)` via root label count.** `labelCount root (T(Λ,t)) = t`
   makes `occurrenceTree_injectiveOn` a two-line `omega`. Do the same instead of a bespoke
   "deepest-eligible" invariant proof.
7. **`x : Event → NNReal` with strict `0 < x < 1`.** lax-41 excludes `x i = 0` (the LLL
   hypothesis would force `Pr[A i] = 0`, degenerate). PLAN §3 wants to absorb `x i = 0`
   explicitly. Minor divergence; either is fine, but note their choice keeps all products
   strictly positive and division `x/(1−x)` total in NNReal. Recommend matching them unless
   there is a concrete application needing `x = 0`.
8. **Everything is ENNReal.** lax-41 computes in ℝ≥0∞ with NNReal witnesses (coerced), same
   as the LLL file's toolbox — no `.toReal` arithmetic. Follow suit.
9. **Isabelle's reusable ideas are about statement hygiene, not MT.** The `mutual_indep_events`
   predicate shape transfers to our *lemma* "events on disjoint variable sets are
   independent"; the `S ≠ ∅` conditioning note and the directed-graph rationale are worth a
   sentence in our docstring. Nothing else transfers — the AFP has no variable framework.
10. **Do not trust the `axiom`-in-concepts pattern outside LAX.** In StatsMLlib everything
    must be a theorem; lax-41's `concepts/` axioms are interface stubs by submission
    convention (the real work is in `proofs/`, which is sorry-free). If we quote lax-41, quote
    the proofs, and mention the convention to avoid confusion.

---

## 7. Risks

1. **Near-duplication with lax-41.** EdouardBonnet/moser-tardos already delivers MT Thm 1.2 +
   HSS Thm 2.2, sorry-free and registered, on mathlib ~6 weeks behind ours. If our proposal
   targets the same theorem in the infinite-table formulation, reviewers will rightly ask
   "why not upstream lax-41 instead?" Mitigation: the proposal must (a) state the
   finite-truncation formulation as the deliberate, formally-distinct contribution (or adopt
   the infinite-table formulation with explicit attribution and a port+extension plan), and
   (b) position StatsMLlib work as the "mathlib-grade" continuation (house style, docs,
   `x = 0`, symmetric corollary, k-SAT/coloring applications) rather than a re-proof.
2. **Duplicate-then-diverge API trap.** If we make different framework choices (event typing,
   pick-rule parameterization, tree representation) than lax-41 without a reason, future
   reconciliation/upstreaming becomes costly. Every divergence should be justified in the
   blueprint (as §6.2/6.7 do).
3. **Version drift of lax-41's dependencies.** Pinned to mathlib `c5ea0035` (v4.30.0); the
   measure/probability API in v4.32.0 has moved in places (agent A must re-verify each
   `infinitePi*` lemma name before we rely on it — the local search in §3 verified only
   existence of the main ones).
4. **Krčál slides are unverifiable** (image-only PDF, no OCR, attribution from a search
   snippet). Do not cite them as completed work; at most as a historical sketch.
5. **LAX status semantics.** "Registered" indicates the archive checked the proofs, but the
   archive is new (18 submissions, mostly drafts) and its checking pipeline is not publicized
   on the site; independent re-verification (e.g. `lake build` on the repo) would be prudent
   before leaning on lax-41 in the proposal text.
6. **Alon–Spencer §5.7 contents unverified** (see Open questions) — the proposal should cite
   the chapter, not over-claim what §5.7 contains.

---

## 8. Open questions

1. **Formulation decision.** Given lax-41 + mathlib's `Measure.infinitePi`, should the
   proposal (i) keep PLAN §3's finite-truncation `Ω_N` formulation (distinct, self-contained,
   but now *harder than necessary*), (ii) adopt the infinite-table formulation (proven
   route, risk of looking like a port), or (iii) infinite-table with explicit differentiators
   (`x i = 0`, symmetric form `ep(d+1) ≤ 1` with the `(1+1/d)^d ≤ e` constant, a k-SAT
   application, StatsMLlib integration)? Needs orchestrator/agent-B decision; this survey's
   evidence supports (iii).
2. **Coordination with Édouard Bonnet / the LAX archive.** Is there interest in folding
   lax-41 into StatsMLlib (or mathlib) rather than re-doing it? The LAX CLI (`npm install -g
   lax-archive`) and archive site suggest an agent-friendly submission channel; the author is
   clearly active (repo pushes through 2026-08-15 on the archive fork). The proposal should
   record an outreach attempt or an explicit decision not to.
3. **HSS Thm 2.2 placement.** lax-41 proves it as a companion; our PLAN doesn't list it.
   Should it be a stated non-goal ("already in lax-41; future reconciliation") or a stretch
   goal? Its definitions (`outputTime` via `Nat.find`, `eventOccursInOutput`) are small and
   high-value.
4. **Witness `x = 0`.** Adopt lax-41's strict `0 < x A < 1` (simpler, matches them) or the
   PLAN's `x i ∈ [0,1)` with an explicit zero case (more general)? Agent B to decide with a
   concrete application in mind.
5. **Alon–Spencer §5.7 exact contents** (4th ed.): does it state MT Theorem 1.2 fully or only
   the older Beck/Alon algorithmic results + a sketch? Only a physical copy or library record
   can settle it; the proposal can cite "Ch. 5, §5.7 The Algorithmic Aspect" without
   over-claiming.
6. **Citation style for the 尹一通 slides** (informal, Chinese-titled summer school): confirm
   the house convention for informal lecture notes in the proposal's References (the LLL
   proposal cited it; mirror that).
7. **Is `Measure.infinitePi` in v4.32.0 semantically identical to v4.30.0's** (countable index
   type, product of probability measures, cylinder lemmas)? Agent A to pin exact names/statements
   (`Mathlib/Probability/ProductMeasure.lean`) before the blueprint commits to the
   infinite-table formulation.
