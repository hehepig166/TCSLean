# Survey C: External LLL Formalizations and Literature

Scope: what LLL formalizations exist outside this project, what the literature says, and
what lessons they hold for the StatsMLlib proposal. All facts verified 2026-08-15.

---

## 1. Isabelle AFP

**The AFP entry exists.** [*"General Probabilistic Techniques for Combinatorics and the Lovasz Local Lemma"*](https://www.isa-afp.org/entries/Lovasz_Local.html),
by **Chelsea Edmonds**, submitted **2023-09-20**. It is part of her PhD work (with Lawrence C. Paulson
as advisor), written up in:

- C. Edmonds, L. C. Paulson, *"Formal Probabilistic Methods for Combinatorial Structures using the
  Lovász Local Lemma"*, CPP 2024, DOI [10.1145/3636501.3636946](https://doi.org/10.1145/3636501.3636946),
  arXiv:[2310.00513](https://arxiv.org/abs/2310.00513).

This is the **first machine-checked LLL** and, until the Lean projects of §2, the only one.

### Variants formalized
- **General (asymmetric) LLL** — main theorem `lovasz_local_general` (Thm 5.1 of the paper):
  for a finite family of measurable events `A₁…Aₙ`, a dependency **digraph** `D = (V,E)`, and reals
  `0 ≤ xᵢ < 1` with `P[Aᵢ] ≤ xᵢ · ∏_{(i,j)∈E} (1 − xⱼ)`, the conclusion is
  `P[⋀ᵢ Āᵢ] ≥ ∏ᵢ (1 − xᵢ) > 0`.
- **Symmetric version** (`lovasz_local_lemma_symmetric`) as a derived corollary.
- Existence lemmas and a general "probabilistic method" framework (`Basic_Method`), with
  applications in the separate AFP entry [*Hypergraph_Colourings*](https://www.isa-afp.org/entries/Hypergraph_Colourings.html)
  ("Used by" on the entry page).
- **Not** formalized: the constructive/Moser–Tardos proof — the CPP paper explicitly names it as
  future work ("would likely benefit from past formalisations of probabilistic algorithms").

### Proof route
Combinatorial/measure-theoretic **classical induction proof** (Alon–Spencer + Yufei Zhao's notes),
not algorithmic. The heart is the helper `lovasz_inductive`:

```
finite A;  F ` A ⊆ events;  ∀i∈A. 0 ≤ f i < 1;  dependency_digraph G M F;  pverts G = A;
∀Ai∈A. prob (F Ai) ≤ f Ai * (∏ Aj ∈ neighborhood G Ai. 1 - f Aj);
Ai ∈ A; S ⊆ A - {Ai}; S ≠ {}; prob (⋂ Aj∈S. space M - F Aj) > 0
⟹  𝒫(F Ai | ⋂ Aj∈S. space M - F Aj) ≤ f Ai
```

proved by strong induction (`finite_psubset_induct`) on `S`, splitting `S = S₁ ∪ S₂` with
`S₁ = S ∩ neighborhood(Ai)` and `S₂ = S \ S₁`; `S₂` events are mutually independent of `F Ai` by the
dependency-digraph assumption, and the `S₁` part is unwound by a product-of-conditional-probabilities
chain lemma. Base case `lovasz_inductive_base` handles the empty product.

### Key definitions and structure
- Locale `dependency_digraph` (extends `pair_digraph` + `prob_space`): vertices are event indices,
  and each `F i` is **mutually independent of the events indexed outside `{i} ∪ neighborhood(i)`**.
  Comment in the source: "Uses directed graphs. The pair_digraph locale was sufficient as
  multi-edges are irrelevant." (Undirected graphs were rejected because the independence relation
  is asymmetric in general.)
- Theory files in the `Lovasz_Local` session: `PiE_Rel_Extras`, `Digraph_Extensions`,
  `Prob_Events_Extras`, `Cond_Prob_Extensions`, `Indep_Events`, `Basic_Method`,
  `Lovasz_Local_Lemma`, `Lovasz_Local_Root`. Dependencies: `Card_Partitions`, `Design_Theory`,
  Noschinski's `Graph_Theory`.
- Substantial **probability-library extensions** were needed: conditional probability (incl.
  Bayes' theorem) and independence-of-events lemmas.

### Notable formalization tricks / pain points (from the CPP paper + source)
1. **Universal set ≠ sample space.** In Isabelle `P(Ω) = 1` is not automatic, so the paper proof's
   `P(⋂∅) = P(Ω) = 1` step breaks; the formalization deliberately keeps `S ≠ ∅` in the induction
   and conditions only on positive-measure events. (In mathlib, `[IsProbabilityMeasure μ]`
   gives `μ univ = 1`; the analogue is conditioning on measure-zero events, which mathlib's
   `μ[|]` also requires care with.)
2. **Independence claims are where the real work is.** Edmonds: "the mutual independence principle
   was seldom referred to, let alone proven" in paper proofs — proving that monochromatic events of
   disjoint hyperedges are mutually independent was a significant part of the effort. The LLL proof
   itself was comparatively routine.
3. The symmetric corollary is a thin wrapper around the asymmetric statement.

---

## 2. mathlib4 / Lean community

### mathlib itself: nothing
- mathlib4 docs search for `Lovasz`: no declarations (checked
  https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Lovasz).
- GitHub issue search on `leanprover-community/mathlib4` for `lovasz`/`lovász`: 6 hits, all
  incidental (PRs on hypergraphs, Erdős–Ko–Rado #15705, Kruskal–Katona #15000 — mentions of
  Lovász's book/combinatorics, none about the local lemma).
- Lean Zulip: no thread found on an LLL formalization.
- Relevant existing mathlib infrastructure: `ProbabilityTheory.iIndepFun`, `iIndepSets`,
  `IndepFun`, `cond` (kernel-based conditional probability), and `ENNReal` — all present in
  mathlib v4.32.0 (the independence API lives in `Mathlib/Probability/Independence/Basic.lean`).

### Existing Lean projects (3, all standalone — none in mathlib)

**a) `nsglover/lean-lovasz-local-lemma`** — https://github.com/nsglover/lean-lovasz-local-lemma
(5 stars; Lean 3; last push 2023-12-24; 25 KB single file `src/lovasz_local_lemma.lean`).
CMU course project (21-321 ITP, Fall 2022, Jeremy Avigad). Asymmetric LLL + symmetric corollary,
following [Vondrák's Math233A notes](https://theory.stanford.edu/~jvondrak/MATH233A-2018/Math233-lec02.pdf).
Statement style: events `E : Fin n → Set Ω`; dependency digraph `Γ : Fin n → Finset (Fin n)` with
`i ∉ Γ i`; hypothesis `∀ i J, J ⊆ ({i} ∪ Γ i)ᶜ → indep_sets {E i} {⋂ j∈J (E j)ᶜ} ℙ`;
witnesses `X : Fin n → ENNReal`, `0 < X i < 1`; conclusion
`ℙ (⋂ i (E i)ᶜ) ≠ 0 ∧ ∏ i (1 - X i) ≤ ℙ (⋂ i (E i)ᶜ)`.
There is also a Lean 4.0 translation: **`nsglover/Lean-4.0-LLL`** (https://github.com/nsglover/Lean-4.0-LLL).

**b) `Mahesh-Ramani/lovasz-local-lemma-lean4`** — https://github.com/Mahesh-Ramani/lovasz-local-lemma-lean4
(0 stars; Lean **v4.28.0** / mathlib 4.28; last push 2026-03-31; 13 KB single file
`RequestProject/LovaszLocalLemma.lean`). Claims (incorrectly) to be "the first complete
machine-checked proof of the LLL" — the Isabelle entry of 2023 predates it.
- Results: `lovasz_local_lemma` (asymmetric, with the lower bound
  `∏ j∈S (1-x j) ≤ μ(avoidSet A S)`), `lovasz_local_lemma_pos` (strict positivity),
  `lovasz_local_lemma_symmetric` (with the `4p(d+1) ≤ 1` constant).
- Design choices worth stealing or consciously rejecting:
  - Dependency condition phrased **without an explicit graph**, as a `LopsidependenceCondition`:
    for each `i` and each `S` with `j ∉ Γ i` and `j ≠ i` for all `j ∈ S`,
    `μ (A i ∩ ⋂ j∈S (A j)ᶜ) = μ (A i) * μ (⋂ j∈S (A j)ᶜ)`.
    (Despite the name this is the *standard* condition, not the true lopsidependency of §5.)
  - Proof by `Finset.strongInduction` on `S` with a combined invariant `LLL_Statement S`
    (both the conditional bound and the product lower bound), plus a "peeling lemma"
    `lll_peeling` stripping events off `S₁` one at a time. Follows Alon–Spencer ch. 5.
  - **Arithmetic in ℝ via `.toReal`** (with `0 ≤ x i < 1` side conditions), *not* ENNReal.
  - Symmetric case reduced with the witness `x i = 1/(2(d+1))` and Bernoulli's inequality —
    this yields the `4p(d+1) ≤ 1` form and avoids proving `(1+1/d)^d ≤ e`.

**c) `EdouardBonnet/moser-tardos`** — https://github.com/EdouardBonnet/moser-tardos
(0 stars; Lean **v4.30.0**, mathlib pinned at rev `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
**last push 2026-08-08, actively developed**). This is the most important finding of this survey:
- Formalizes **Moser–Tardos Theorem 1.2** (the constructive LLL: existence of a good assignment +
  expected resamplings of event A ≤ `x A / (1 - x A)` + total bound) and
  **Haeupler–Saha–Srinivasan Theorem 2.2** (the "distributional LLL":
  `Pr[B ever occurs / B in output] ≤ Pr[B] · ∏_{C∈Γ(B)} (1 - x C)⁻¹`).
- Structure: `concepts/` (definitions + `axiom` statements of the two theorems, 6.5 KB each) and
  `proofs/` (`Lax41Proofs/MoserTardos.lean` ≈ 90 KB, `HaeuplerSahaSrinivasanTheorem22.lean` ≈ 47 KB,
  **both sorry-free** — verified by grep).
- Framework: finitely many variables `Value i` with independent probability measures; bad events
  as `Set (LocalAssignment Value (variablesOf A))`; a `ResamplingRule` (choice of which event to
  resample); the proof uses **resampling tables, proper witness trees, branching-process weight
  estimates** (the standard Moser–Tardos route), plus a finite-termination argument.

**Takeaway for us:** the classical LLL has already been done twice in Lean (a) (b), and the
constructive Moser–Tardos/HSS route is in active development in (c). A StatsMLlib contribution
should target the classical asymmetric + symmetric LLL done *properly for mathlib* (the two
existing classical efforts are course-quality, single-file, unpinned-to-current-mathlib), and
treat (c) as the natural upstream for any future algorithmic extension rather than duplicating it.

---

## 3. Other provers

- **Coq:** no LLL formalization found anywhere. The Edmonds–Paulson CPP paper itself notes that a
  constructive LLL "would likely benefit from past formalisations of probabilistic algorithms"
  (in Coq). Relevant Coq infrastructure that *exists*:
  - `alea` (Audebaud–Paulin-Mohring, *Proofs of randomized algorithms in Coq*, 2009);
  - Affeldt–Garrigue–Saikawa, *Reasoning with Conditional Probabilities and Joint Distributions in
    Coq* (MathComp/Infotheo; JSSST 37(3), 2020): conditional independence `_|_`, graphoid axioms,
    Bayes — but no local lemma.
- **HOL4:** no LLL (Hurd's measure/probability theory predates it and nothing builds on it).
- **HOL Light:** no LLL found.
- **Mizar / Metamath:** nothing found.
- **Conclusion:** as of 2026-08, the only complete formalizations of the LLL in any system are the
  Isabelle AFP entry (2023) and the three Lean projects of §2. There is no Coq/HOL4/HOL-Light/Mizar
  work to mine.

---

## 4. Lecture notes PDF: 尹一通 (Yin Yitong), *Basics of Randomized Algorithms*

File: `/Users/zhuzekai/workspace/StatsLean/doc/lovasz/01_proposal/ref/尹一通-lll.pdf`.
南京大学, "计算理论之美" (Beauty of Computation Theory) summer school, dated 2025-06-30.
193 slides, Chinese, text-extractable (no TOC; slides build up incrementally with heavy repetition).

### Coverage map
| Pages | Content |
|---|---|
| 1–23 | Warm-up: k-SAT, CNF, union bound, "trivial cases" (`m < 2ᵏ` ⟹ satisfiable) |
| 24–44 | **Symmetric LLL**: `p ≜ maxᵢ Pr[Aᵢ]`, `d ≜ maxᵢ |Γ(Aᵢ)|`, `ep(d+1) ≤ 1 ⟹ Pr[⋀ Āᵢ] > 0`; application: hypergraph coloring (`Δ ≤ q^{k−1}/(ek)` ⟹ q-colorable). Attribution given as "[Lovász and Erdős 1973; Lovász 1977]" |
| 45–71 | **Asymmetric LLL**: `∃α₁,…,αₘ ∈ [0,1): ∀i, Pr[Aᵢ] ≤ αᵢ ∏_{Aⱼ∈Γ(Aᵢ)}(1−αⱼ) ⟹ Pr[⋀ Āᵢ] ≥ ∏(1−αᵢ)`; classical proof: chain rule `Pr[⋀ Āᵢ] = ∏ᵢ Pr[Āᵢ | ⋀_{j<i} Āⱼ]` + induction hypothesis `Pr[Aᵢ | Ā_{j₁}…Ā_{jₖ}] ≤ αᵢ`; symmetric recovered by `α₁=…=αₘ=1/(d+1)` |
| 72 | Teaser: "What's next: tight(er) LLL condition: **Shearer's bound**" (not covered in these notes) |
| 73–163 | **Algorithmic LLL (Moser–Tardos)**: *variable framework* — independent variables `𝒳 = {X₁,…,Xₙ}`, bad events `𝒜` determined by `vbl(Aᵢ)`, dependency graph `Γ(Aᵢ) = {Aⱼ ≠ Aᵢ : vbl(Aᵢ) ∩ vbl(Aⱼ) ≠ ∅}`; MT resampling algorithm; expected resamples `≤ Σ αᵢ/(1−αᵢ)`; proof via execution log, resampling table, witness trees |
| 165–192 | **Moser's Fix-It algorithm + entropic (incompressibility) proof** for k-SAT with `d < 2^{k−3}` |
| 193 | Summary: LLL (probabilistic method) → algorithmic LLL (Moser–Tardos) → Moser's algorithm + entropic proof |

### Relevance to scope decisions
- The notes treat **both** the abstract event model (symmetric/asymmetric LLL) and the
  **variable/CSP model** (for the algorithmic part); the dependency graph is defined *via shared
  variables* only in the variable framework.
- k-SAT and hypergraph coloring appear as applications; **no lopsided LLL** (only the classical
  mutual-independence dependency graph); no tight/Shearer's bound.
- Notation style: bad events `A₁,…,Aₘ`, complements `Āᵢ`, dependency neighborhood `Γ(Aᵢ)`,
  witnesses `αᵢ` (asymmetric), `p`/`d` (symmetric). The proof route presented (chain rule +
  conditional induction) is exactly the route taken by the Isabelle and Mahesh-Ramani
  formalizations, so it is a reliable blueprint.

---

## 5. Literature anchors

### Caveat: the URL given is Moser–Tardos, not a "lopsided survey"
[arXiv:0903.0544v3](https://arxiv.org/html/0903.0544v3) is **Moser & Tardos, "A constructive proof
of the general Lovász Local Lemma"** — not Haeupler–Saha–Srinivasan. Its Section 6 develops the
lopsided extension, and Section 5 a deterministic variant. (The HSS paper is arXiv:1001.1231, below.)

### Classical references (correct full citations)
- **Erdős–Lovász 1975** (original LLL): P. Erdős and L. Lovász, "Problems and results on
  3-chromatic hypergraphs and some related questions", in *Infinite and Finite Sets* (Colloq.,
  Keszthely, 1973; dedicated to P. Erdős on his 60th birthday), ed. A. Hajnal, R. Rado, V. T. Sós,
  Vol. II, pp. 609–627, North-Holland, 1975. [Some lecture notes cite "Lovász 1977" for the
  published refinement.]
- **Alon–Spencer** (standard textbook statement): N. Alon and J. H. Spencer, *The Probabilistic
  Method*, Wiley (1st ed. 1992; 4th ed. 2016), **Chapter 5: The Local Lemma**. Symmetric form
  `ep(d+1) ≤ 1`; general/asymmetric form via `x₁,…,xₙ ∈ (0,1)` with
  `Pr[Aᵢ] ≤ xᵢ ∏_{j∈Γ(i)} (1−xⱼ)`; conclusion `Pr[⋀ Āᵢ] ≥ ∏(1−xᵢ)`.
- **Erdős–Spencer 1991** (lopsided LLL): P. Erdős and J. Spencer, "Lopsided Lovász Local Lemma and
  Latin Transversals", *Discrete Applied Mathematics* 30 (1991) 151–154.
- **Moser–Tardos 2010**: R. A. Moser and G. Tardos, "A constructive proof of the general Lovász
  Local Lemma", *J. ACM* 57(2), Article 11, 2010. arXiv:0903.0544. Theorem 1.2: resampling
  algorithm, expected resamplings of event `A ≤ x(A)/(1−x(A))`, total `≤ Σᵢ xᵢ/(1−xᵢ)`.
- **Haeupler–Saha–Srinivasan 2011**: B. Haeupler, B. Saha, A. Srinivasan, "New Constructive
  Aspects of the Lovász Local Lemma", *J. ACM* 58(6), Article 28, 2011 (FOCS 2010).
  [arXiv:1001.1231](https://arxiv.org/abs/1001.1231). Theorem 2.2 (the "distributional LLL"):
  for any event B determined by the same variables,
  `Pr[B ever holds / B in output] ≤ Pr[B] · ∏_{C∈Γ(B)} (1−x(C))⁻¹`. Also: O(n² log n)
  resampling bound with slack, and a core-subset theorem for implicit bad events.

### What the lopsided version adds — and why it is future work
- The standard LLL dependency graph ties events to *shared variables* (`vbl(A) ∩ vbl(B) ≠ ∅`).
  The **lopsided** version replaces this with a weaker relation (lopsidependency): intuitively,
  two evaluations differing only on shared variables making `A` and `B` violated, "but either f
  does not violate B or g does not violate A". Since `Γ'(A) ⊆ Γ(A)`, the LLL hypotheses become
  weaker and the theorem strictly stronger. For **elementary events** (single assignments)
  lopsidependency collapses to **disjointness** — which is what makes Latin-transversal-type
  applications work. For CNFs, conflicts (opposite literals) matter while mere shared-variable
  overlap does not.
- Why not a first target, per Moser–Tardos §6 and the literature:
  1. The **definition for general events is subtle**: arbitrary events must be decomposed into
     elementary ones, requiring a slightly stronger probability condition;
  2. The **witness-tree swap argument** (Moser–Tardos Lemma 6.2: consecutive non-lopsidependent
     resamplings can be reordered) is substantially harder than the plain coupling;
  3. **No parallelization** is known (only sequential + derandomized variants);
  4. Even the classical (non-lopsided) LLL has only 3–4 formalizations worldwide, all classical —
     the lopsided version multiplies the definitional and proof-engineering risk with little
     library payoff in the first iteration.

---

## 6. Implications for our proposal

1. **Statement choice.** Target the **asymmetric LLL in the event model with an explicit
   dependency graph** (or the equivalent graph-free "independence from the intersection of
   complements" condition used by Mahesh-Ramani), with conclusion
   `μ (⋂ᵢ (A i)ᶜ) ≥ ∏ᵢ (1 - x i) > 0`; get the symmetric version as a corollary. Every existing
   formalization (Isabelle, both Lean classical proofs) uses exactly this shape; it is the
   Alon–Spencer / 尹一通 canonical form and maximizes compatibility with a future
   Moser–Tardos/HSS extension. Phrase the dependency hypothesis directly in mathlib's
   `ProbabilityTheory.iIndepFun`/`iIndepSets` vocabulary (independence of `A i` from the family
   `{(A j)ᶜ | j ∉ Γ i ∪ {i}}`), since that API already exists in mathlib v4.32.0.
2. **Proof route.** Use the classical **strong induction on the index set S with a combined
   invariant** (conditional bound + product lower bound), the "peeling" decomposition
   `S = (S ∩ Γ i) ∪ (S \ Γ i)`. This is proven technology in three prior formalizations
   (Isabelle's `finite_psubset_induct`, Mahesh-Ramani's `Finset.strongInduction` + `lll_peeling`).
   The measure-theoretic formulation is fine — no one needed a combinatorial (counting) route.
   Decide **early between ENNReal and ℝ/.toReal arithmetic** (nsglover used ENNReal,
   Mahesh-Ramani ℝ): ENNReal avoids positivity-of-conditioning pain but makes `1 - x` products
   annoying; either is workable, but the choice propagates through every lemma.
3. **Variants to defer.** (i) **Lopsided LLL** — definitional subtlety + swap argument, no
   parallel version known (§5); (ii) **Shearer's bound / cluster expansion** — much harder
   optimization-flavored statements; (iii) **constructive Moser–Tardos** — already being
   formalized in `EdouardBonnet/moser-tardos` (sorry-free, v4.30.0, active); do not duplicate.
   The symmetric form with the `4p(d+1) ≤ 1` constant (witness `1/(2(d+1))`) is the cheapest
   corollary; the `ep(d+1) ≤ 1` form additionally needs `(1+1/d)^d ≤ e` machinery.
4. **Warnings from prior work.**
   - The LLL proof itself is *not* the hard part; **proving the independence/mutual-independence
     hypotheses for concrete events** (e.g. disjoint-variable events) is where paper proofs are
     sloppy and formal effort concentrates (Edmonds' "notable gaps").
   - Conditioning hygiene: keep `S ≠ ∅` / positive-measure conditioning events explicit
     (Isabelle's sample-space-vs-universe pitfall has a mathlib analogue in `μ[|]` on null sets).
   - Avoid the factual error in Mahesh-Ramani's README ("first machine-checked proof") — the
     Isabelle AFP entry (2023) holds that title.
   - There is **nothing in mathlib** to build on or conflict with, and no mathlib PR in flight —
     green field, but the three standalone Lean repos are precedents worth citing and
     (ideally) upstreaming from rather than re-proving against.
