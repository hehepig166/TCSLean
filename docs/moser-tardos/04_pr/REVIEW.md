# Moser–Tardos Formalization — Full Statement Review (2026-08-18)

Four independent review dimensions over the 7 modules (`VariableModel`, `Algorithm`,
`WitnessTree`, `Coupling`, `GaltonWatson`, `Basic`, `Symmetric`): paper fidelity,
hypothesis hygiene, API/consistency, and mathematical spot-check of the 8 load-bearing
theorems.

## Verdict

**No mathematical errors.** All 8 load-bearing statements are correct in quantifiers,
directions, and boundary behavior (x i = 0, N = 0, d = 0 excluded-by-convention), verified
against arXiv:0903.0544 and the project notes. The issues found are statement-shape gaps
and housekeeping, ranked below.

## Major findings (statement-level)

| # | Finding | File:line | Suggested fix |
|---|---|---|---|
| M1 | **`moserTardos_symmetric` concludes only existence**; the source (notes Cor 20.1 / arXiv Thm 1.3) and the project plan pin the symmetric expected-resampling bound `∫⁻ R ≤ ofReal (card ι / d)`. The hLLL instantiation for `x = 1/(d+1)` is already discharged in the proof, so the quantitative form is one `exact` on `moserTardos_total`. | `Symmetric.lean:58` | Add `moserTardos_symmetric_total : ∫⁻ ω : ΩN N Ω, (R … ω : ℝ≥0∞) ∂ μN N μ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / d)` (with the same hypotheses), reusing the existing instantiation chain. |
| M2 | **`[Inhabited ι]` leaks into all five public theorems** (`moserTardos_bound/total/tail/exists/symmetric`) via `treeAt`'s padded dummy root (`WitnessTree.mk (t, default) []`). Mathematically unnecessary (empty ι is vacuous); not wrapper-removable. | `WitnessTree.lean:1154` | Either make `T`/`treeAt` partial (`if t < R then … else <Prop-fallback>`, or `Option`-valued), or document the restriction in the theorem docstrings. |
| M3 | **`pick`/`hpick` appear in the existence theorems** though the conclusion `∃ σ, ∀ i, σ ∉ A i` is tie-breaking-independent. Legitimate in `moserTardos_bound` (uniformity over pick is the point), a statement-level smell in the corollaries. | `Basic.lean:2353`, `Symmetric.lean:58` | Add the one-liner pick-free wrappers `moserTardos_exists`/`moserTardos_symmetric` with `pick := fun S => Classical.choose S.2`. |
| M4 | **`treesFinset`/`treesFintype`/`fintypeProperSizeLE` (50.2) are dead weight** — zero consumers since the canonical-domain re-shaping (60.1's log records the supersession). | `GaltonWatson.lean:288,349,364` | Delete the chain (keep `size_le_sum_of_mem`, consumed by Basic) or mark deprecated; update the module docstring. |

## Minor findings

- **`gwWeight_telescope` carries `hx0 : ∀ j ∈ labels τ, j ≠ i → x j ≠ 0`** — a proof artifact (notes Lemma 17.1 needs only `hxi`); the stronger division-free identity `gwWeight_mul_x_eq` (Basic.lean:1882, hypotheses `hroot`/`hprop`/`hwit` only) is already proven. Restate the telescope without `hx0`, or relabel it a variant. (`GaltonWatson.lean:172`)
- **No cross-N statements**: the truncation design (finite table, no infinite product) captures the paper's bound for all N, the per-N tail, and existence — but `lim_N μN{R = N} = 0` / `E[R_∞] ≤ C` (the paper's "terminates a.s.") has no analogue. Documented design decision; note it in the module docstring. (`VariableModel.lean`)
- **No divided ε–N tail form** `μN{R = N} ≤ (Σ x i/(1-x i))/N` — a one-line corollary of the multiplicative form for `N > 0`. (`Basic.lean:2288`)
- **Docstring gaps**: Algorithm's module docstring omits the entire measurability half (18 public declarations); Basic's omits `moserTardos_tail` + the `MeasurableOccurrence` block; WitnessTree's omits the public 30.4–30.7 surface; Coupling has a duplicated section header (both "40.2: the measure of the τ-check…") and omits the G1–G6 glue; GaltonWatson's omits the stepping stones + domain invariants.
- **Duplicated private helpers across modules** (`maxOption`/`mtMaxOption`/`mtMaxOption'` ×5, the `exists_eq_or_imp_swap` pair ×2, `foldl_*_eq_some` under two names) — promote one canonical public version in WitnessTree.
- **Section-variable block duplicated 3×** (`MainTheorem`, `Exists`, `Symmetric`) — drift risk; fold where possible.
- **`[Fintype κ]` in all public theorems** is a modeling artifact (the paper needs only finite `vbl i`) — a conscious pinned restriction; note it in docstrings.
- **Unjustified `noncomputable section`** in GaltonWatson.lean and Symmetric.lean (no Classical/choice usage) — remove.

## Nits

- `hA` in the existence theorems is route-essential but house-consistent (LovaszLocal carries the same) — keep.
- `hx₀`/`hx₁` split is deliberate and better than `Set.Ioo (0) 1` (absorbs x i = 0) — keep.
- `hd1 : 1 ≤ d` in the symmetric form is needed as stated (x = 1/(d+1) violates hx₁ at d = 0); a stronger d = 0-inclusive theorem exists via a separate branch.
- `hN` in `occurrence_implies_check` is derivable from `ht + hT` (T_size_le_N) — redundant but harmless (needed for the check's well-formedness).
- `coupling_canon` / `occurrence_canon_le_treeProd` pair deserves cross-reference docstrings.
- Leftover section-marker labels in Basic.lean ("(A cont.)" without an "(A)").

## Verified-correct highlights (no action)

- `check_probability` = notes (14.2): right product, right event (profile-reading rows = |S_X(u)| counts), `IsGood` load-bearing and faithful (non-good trees never occur).
- `coupling` = Lemma 14.1 with the honest `t < R` truncation; the by_cases-on-IsGood empty-event branch is legitimate.
- `gwWeight_telescope` = (17.2) with the right factor; `gwWeight_sum_le_one` over `gwFinsetHeight` genuinely fixes the d! overcount; the recurrence is the exact multinomial identity.
- `countLog_eq_sum_card` = (13.1) via the canon partition — fiber-card identities are injectivity-free; N = 0 boundary clean.
- `moserTardos_bound` = notes (5.1)/Thm 1.2 with the exact hLLL shape (`ofReal (x' i)`, open neighborhood Γ); the x i = 0 case is absorbed by the division-free bridge — a sound generalization of the paper's (0,1).
- `moserTardos_total/tail/exists`: sum form, multiplicative tail (correct at N = 0), existence route sound (hR step + `exists_nat_gt`).
- `moserTardos_symmetric`: the constant chain e·p·(d+1) ≤ 1 → x = 1/(d+1) is correct (non-strict version, strictly more general than the paper's strict ep(d+1) < 1).

## Fix status (applied 2026-08-18, full build 8752 jobs, zero warnings)

- **M1 FIXED** — `moserTardos_symmetric_total : ∫⁻ R ≤ ofReal (card ι / d)` added (Symmetric.lean), via a factored `symmetric_hLLL` + `moserTardos_total`.
- **M3 FIXED** — `moserTardos_exists` / `moserTardos_symmetric` restated pick-free (public API); the pick-carrying versions are private lemmas instantiated with `Classical.choose`.
- **M2 FIXED (existence theorems)** — both existence theorems are now `[Inhabited ι]`-free via `by_cases Nonempty ι` wrappers (empty case: Ω-nonemptiness from the probability instances + vacuous ∀). The quantitative theorems keep `[Inhabited ι]` with docstring notes: verified TRUE at empty ι (`R ω = 0` vacuously) but the current route cannot discharge it — a proof-infrastructure artifact, not a mathematical restriction.
- **M4 FIXED** — the dead 50.2 chain (`treesFinset`/`treesFintype`/`fintypeProperSizeLE`/`length_le_sizeSum`) deleted; `size_le_sum_of_mem` kept.
- **Docstring sweep FIXED** — Algorithm measurability block, Basic tail + MeasurableOccurrence + `canonLiftCert` + normalized (60.x) tags + marker renames, Coupling header rename + G1–G6 listing, GaltonWatson stepping stones + hx0 note, VariableModel truncation-design paragraph, `coupling_canon` cross-refs, unjustified `noncomputable section` removed from GaltonWatson (kept in Symmetric — now justified).
- **Deferred** (documented): the divided ε–N tail form (one-line corollary), the cross-N limit statements (no countable product in mathlib), private-helper dedup (`maxOption` family promotion), and making the quantitative theorems `Inhabited`-free (needs the T partial rework).
