# Claim ledger --- "Strong Majority Edge-Coloring with Four Colors for Graphs with Degrees in {3,4}: A Machine-Checked Program" (main.tex)

Rule (house doctrine): every factual sentence in the paper has a row here; no claim without a row.

Status codes:
- **KERNEL** = kernel-checked Lean artifact (axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`)
- **KERNEL-COND** = body sorry-free but inherits `sorryAx` solely via the one open descent lemma (stated as conditional in the paper)
- **PRIMARY** = verified against a primary external source
- **INTERNAL** = verified internal artifact (exact computation, audit record, mining/probe output) --- evidence, not kernel
- **TOK** = "to our knowledge" with a documented search scope
- **PENDING-PACKAGING** = resolves when the release artifact is assembled/rebuilt in a clean environment; do not release before closing
- **ELEM** = elementary / definitional bridge, checked by hand

Source pointers are into `problems/p5-strongmajority/rung4-moonshot/`: KILL-CHECK-R4.md (@17bc7cc, BINDING on all novelty wording), CHRONICLE-DRAFT.md, constructive_route/PINS2.md, constructive_route/Pins2.lean, constructive_route/AuditPins2.lean, STRIKE-A.md, STRIKE-B.md, WITNESS-MINING.md, L4-PROBES.md, PROBE-I.md, CODEX-DESCENT.md.

**RE-ANCHOR 2026-07-12 (kill-check verdict applied):** the original draft's contribution (a) ("unconditional 4-regular... first infinite class") was FALSE — 4-regular Maj′≤4 is KNOWN (KKPW Prop 21 + their regular-graph remark for r∈{4,8}); cubic is known twice (KKPW Prop 15, APS Thm 4). Contributions rebuilt: (a) mixed degrees-{3,4} at bound 4 (conditional) = the mathematical headline; (b) R4_four_regular = machine-checked proof of KKPW Prop 21's 4-regular case, different argument; (c) toolkit. All rows below reflect the re-anchored wording.

**RE-ANCHOR 2026-07-13 (v2 flip, t≤2 unconditional):** `R4_three_four_t2` (Pins3.lean L10624) is UNCONDITIONAL and kernel-checked at commit `121821a` — every finite simple graph with all degrees in {3,4} and at most two degree-3 vertices has Maj′ ≤ 4. Contributions re-lettered: (a) the unconditional t≤2 theorem (NEW mathematics on the t=2 mixed slice; previous best there = APS Thm 2's 5); (b) R4_four_regular (machine-checked KKPW Prop 21 4-regular case); (c) general degrees-{3,4} theorem, still CONDITIONAL on the Pins2-L2932 descent lemma; (d) toolkit + falsification record. BINDING SCOPE (mirrors OVERNIGHT-REPORT headline + TRIAGE CONSUMER-REWIRE addendum §5): NOT the full mixed class (general t open); NOT "first machine-verified result in the field" (our released five-color theorem E5 is prior); the correct firsts are "first machine-checked strong-majority bound of FOUR" and "first bound-4 theorem covering any mixed degree-{3,4} graphs". Rows T1–T6 below carry the new theorem's evidence; the old §5.3 NAVIGATE rows (53–54) are superseded as noted in place.

## Kill-check row (binding source verdicts)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 0 | KKPW Prop 15 (verbatim): "If each vertex of a graph G has degree divisible by 3, then Maj'(G) ≤ 4." KKPW Prop 21 (verbatim): "If all vertices of a graph G have even degrees, then Maj'(G) ≤ 4. Moreover, if G is connected and the size of G satisfies ‖G‖ ≡ 0 mod 3, then Maj'(G) ≤ 3." Regular-graph remark (verbatim): "Maj'(G) ≤ 4 for r ∈ {3,6} by Proposition 15, and for r ∈ {4,8} by Proposition 21." APS Thm 4: no degrees 2 or 4 ⇒ Maj'≤4. VERDICTS: 4-regular KNOWN; cubic KNOWN twice; MIXED degrees-{3,4} open at bound 4, best prior bound 5 (APS Thm 2); formalization first OK if framed as machine-checked only | KILL-CHECK-R4.md (arXiv HTML verbatim pulls + 2026-07-12 literature sweep) | PRIMARY (BINDING) |

## The t≤2 theorem (v2 flip rows, 2026-07-13)

| # | Claim | Evidence | Status |
|---|---|---|---|
| T1 | `R4_three_four_t2`: every finite simple graph with all degrees in {3,4} and at most two degree-3 vertices admits a strong majority 4-coloring; UNCONDITIONAL; axioms exactly [propext, Classical.choice, Quot.sound]; ZERO sorry-sources in the transitive dependency cone | Pins3.lean L10624 (statement quoted verbatim in §3.1); theorem bytes landed at commit `121821a` and are unchanged at repo HEAD `6c7f364`; fresh G1 Modal farm call `fc-01KXEC3Z42KZZGRX2J5SD5V5MR`: `lake build Pins3` = 8029 jobs, all 7 release decls exactly [propext, Classical.choice, Quot.sound]; AuditPins3.lean per-decl audit; RewireWalker.lean transitive-closure walker: ZERO sorry-sources for all three new decls | KERNEL |
| T2 | Independent double-confirmation of T1 in a third environment (fresh scratch audits, not the author's audit file) | C:\t\r4final double-confirm lane (TRIAGE-W12-15.md CONSUMER-REWIRE addendum §4; OVERNIGHT-REPORT headline) | KERNEL (confirmation) |
| T3 | Novelty scope of T1: t=2 graphs are mixed and covered by no published bound-4 result (Prop 15 fails 3∤4; Prop 21 fails 3 odd; APS Thm 4 excludes deg-4; Thm 18 δ≥7; Prop 20 bipartite), so previous best = APS Thm 2's 5; T1 = first bound-4 theorem covering ANY mixed degree-{3,4} graphs, and (with R4_four_regular) first machine-checked strong-majority bound of four; NOT the full mixed class; NOT the first machine-checked strong-majority result (E5 five-color is prior, ours) | KILL-CHECK-R4.md verdict (b) applied to the t=2 slice; 2026-07-12 literature sweep; E5 artifact | PRIMARY + TOK |
| T4 | Migration route (§2.7): consumer map — the final assembly needs only the EXISTENTIAL placement statement; `poisoned_t2_shape` forces the poisoned triangle configuration; even path-parity case void by `canonical_strict_of_ellP_even`; odd case migrates (`mig_unpoisons` poison-exit, `migration_step`, `migration_descent`); `nonbip_void_t2` + `placement_of_clean_transversal` + `strongMajority_of_safe_defects` finish; component lift via `numDeg3_induce_le` | Pins3.lean L9164 (mig_unpoisons), L9202 (migration_step), L9335 (migration_descent), L9371 (migration_safe_split_placement_t2), L10587 (connected), L10605 (numDeg3_induce_le); all standard triple per AuditPins3 | KERNEL |
| T5 | `mig_unpoisons` closed TWICE independently (direct transplant, commit `43f70c9`; structured `mig_unpoisons_core` return gated GREEN separately); accepted artifact = direct proof, structured proof retained as confirmation | TRIAGE-W12-15.md addendum §3 (pin race record); Aristotle run d927c059 | KERNEL + INTERNAL (provenance) |
| T6 | Pins3.lean still contains sorry-pins (navigation + general-t program: crossing_selection family, exists_low_birth_freestop_cocircuit(_odd), exists_mt_decomposition, anchored_cut_of_poisoned, genxsel_general, nonbip_pierced_general + threads); NONE in the cone of R4_three_four_t2 / R4_three_four_connected_t2 / numDeg3_induce_le; `R4_three_four` (general t) byte-unchanged and still conditional on Pins2 L2932 | TRIAGE addendum §4 sorryAx census (no strays, no regressions); walker output | KERNEL (audit) + on-disk |

## Abstract + Section 1 (Introduction)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 1 | KKPW def of strong majority edge-coloring; row size d(u)+d(v)-2; cap ⌊(d(u)+d(v)-2)/2⌋ | KKPW [arXiv:2605.23828]; PROBLEM.md frozen dossier; base defs in Maj5Base | PRIMARY + ELEM |
| 2 | Coloring exists iff admissible (no degree-1 adjacent to degree-2); Maj′ well-defined | KKPW; equivalence in the five-color transplant record | PRIMARY + ELEM |
| 3 | KKPW proved Maj′ ≤ 8 (Thm 12); conjectured Maj′ ≤ 4 (Conj 14), best possible; paw is smallest Maj′=4 | KKPW paper.txt (frozen dossier) | PRIMARY |
| 4 | APS improved the GENERAL bound to Maj′ ≤ 5; strongest general result known; we separately machine-checked it | APS [arXiv:2607.00212]; our five-color artifact zenodo 21316623 | PRIMARY + KERNEL (prior work) |
| 5 | The conjectured bound 4 is open IN GENERAL; known on classes: KKPW Prop 15 (deg ÷3, covers cubic), Prop 21 (even degrees, covers 4-regular; Euler-tour proof), Thm 18 (δ≥7), Prop 20 (bipartite δ≥4); APS Thm 4 (no deg 2/4, covers cubic again, δ≥5 threshold) — §1.1 credits all | KILL-CHECK-R4.md verbatim quotes (row 0) | PRIMARY |
| 6 | (b-contribution, unchanged in v2) R4_four_regular: kernel-checked, axioms exactly [propext,Classical.choice,Quot.sound], no sorry in cone; THE STATEMENT IS KKPW's (Prop 21, 4-regular case) — paper says so explicitly in abstract, §1.2(b), §2, §2.5, §7; our contribution = the machine-checked proof by a different argument (capacitated-Hall avoidance vs Euler tour) | `R4_four_regular` (Pins2.lean L3447, sorry-free body verified on disk); AuditPins2.lean L135; KILL-CHECK verdict (a) | KERNEL (rebuild gate G1) + PRIMARY (attribution) |
| 7 | The 4-regular route applies to ANY edge split, needs no minimality/connectivity; every vertex clean; capacitated-Hall avoidance places defects | `R4_four_regular` proof (Pins2.lean L3447-3479+): `exists_edge_split_pin` → `cap_eq_three_iff` (all clean) → `Avoid.avoidance_core` ×2 → placement | KERNEL |
| 8 | "To our knowledge, the first machine-checked proofs of a strong-majority bound of FOUR for any nontrivial class" — now said of R4_four_regular AND R4_three_four_t2 jointly (v2); for the 4-regular case framed as formalization first ONLY, math credited to KKPW; for the t≤2 case the t=2 slice statement is itself new (row T3); E5 (five colors) named as the prior machine-checked Maj′ result | KILL-CHECK verdict (c); five-color priority search; E5 artifact; rows T1/T3 | TOK (scope in §3.2) |
| 8a | STRUCK (re-anchor): former row 8 claim "first infinite family for which KKPW bound 4 is machine-checked-established" — FALSE as a math-novelty claim (4-regular known, KKPW Prop 21); removed from paper everywhere | KILL-CHECK verdict (a) | CLOSED AS CORRECTION; never reuse |
| 9 | (c-contribution in v2; was (a)) General mixed degrees-{3,4} theorem modulo one descent lemma — "the first bound of 4 for the MIXED degree-{3,4} class (graphs carrying both degree-3 and degree-4 vertices), where the previously best general bound was 5 (APS Thm 2); the pure sub-cases were already known (cubic: KKPW Prop 15 / APS Thm 4; 4-regular: KKPW Prop 21)" (kill-check paste-ready wording); every step kernel-checked except one; use confined to degree-3 regime; CONDITIONAL everywhere | KILL-CHECK verdict (b) + recommended wording; PINS2.md rounds 12-13; Pins2.lean sole `sorry` at L2949; `R4_three_four` inherits sorryAx solely via it | KERNEL-COND + PRIMARY (novelty scope) |
| 9a | Mixed-slice openness argument: Prop 15 fails (4∤3), Prop 21 fails (3 odd), APS Thm 4 excludes deg-4, Thm 18 needs δ≥7, Prop 20 needs bipartite; best prior bound = APS Thm 2 (5); 2026-07-12 sweep: only the two source papers address Maj′; strong-chromatic-index literature is a different invariant | KILL-CHECK verdict (b) + literature sweep | PRIMARY + TOK |
| 10 | Degree-{3,4} = all degrees in {3,4} (cubic, 4-regular, mixed); all such graphs admissible | definitional; min degree 3 ⇒ no {1,2} edge | ELEM |
| 11 | The descent lemma is supported by exhaustive verification (all minimal splits through 9 vertices, zero failures) but NOT proved; stated exactly as in Lean | PROBE-I.md (1,380 minimal split-halves, 0 failures); Pins2.lean L2932-2949 | INTERNAL + KERNEL(statement) |
| 12 | (c) Toolkit of >100 kernel-checked declarations (split/defect/trail calculus) | PINS2.md round 13: 105 decls standard-triple; AuditPins2.lean | KERNEL |
| 13 | ePot architecture proposed, passed a gate, refuted by our own machine-checked counterexamples; 8 refuted hypotheses each with a witness | §4; L3-VERIFY, L1-CODEX, L4-PROBES; CHRONICLE §2b table | INTERNAL |
| 14 | Builds on and reuses frozen defs of the five-color verification | Pins2.lean imports `Maj5Base` only (frozen base of E5); PINS2.md environment note | KERNEL + on-disk |
| 15 | Nothing resolves the KKPW conjecture; (a) unconditional but only the t≤2 slice, (b) machine-checked proof of a KNOWN theorem, (c) conditional on the open slice; both regular sub-cases settled by KKPW/APS before this work; no priority on conjecture, 5-color bound, or any known partial result | calibration statement (§1.3, v2 lettering); KILL-CHECK | ELEM + PRIMARY |

## Section 2 (the constructive route)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 16 | Theorem 2.1 = R4_three_four (conditional on the descent lemma; stated first as the headline target) | `R4_three_four` (Pins2.lean L3410); sorryAx via descent only | KERNEL-COND |
| 17 | Theorem 2.2 = R4_four_regular, bracket-labeled "= the 4-regular case of KKPW Proposition 21; kernel-checked here"; §2.5 re-credits Prop 21 (one-paragraph Euler-tour proof) and notes our route recovers it without special-casing | `R4_four_regular` (Pins2.lean L3447); KILL-CHECK verdict (a) | KERNEL + PRIMARY (attribution) |
| 18 | Count identity nColor(u,v,α)+2[c(uv)=α] = cnt(u,α)+cnt(v,α); ⇒ SM when all cnt ≤ 1; cap ∈ {2,3} for degree-{3,4} | `nColor_add_two_mul`, `isStrongMajority_of_cnt`, `E1_of_cnt_le_one` (kernel; PINS2.md L709) | KERNEL |
| 19 | IsProper4 = incidence-proper (cnt ≤ 1); class I = admits IsProper4; class I arm kernel-checked | `IsProper4` (Pins2.lean L443); `classI_arm`, `classI_strongMajority` (kernel) | KERNEL |
| 20 | Edge split = partition into two spanning max-deg-2 subgraphs; exists (Euler-partition); each half = paths+cycles | `IsEdgeSplit` (Pins2.lean L130); `exists_edge_split_pin` (kernel, round 4) | KERNEL |
| 21 | Class-I ⟺ zero-odd split exists (both directions kernel-checked); alternate {0,1}/{2,3} on halves | `P2_equiv` (`P2_equiv_fwd` round 3 + `P2_equiv_bwd` round 5, kernel) | KERNEL |
| 22 | Min-alternating coloring: one defect per odd cycle, free sign; any (D,σ) realizable by a Boolean coloring | `exists_isMinAlternating` + 20-decl realizability toolbox (Fable lane, kernel, round 6) | KERNEL |
| 23 | cap = ⌊(d(u)+d(v)-2)/2⌋ = 3 iff both endpoints degree 4, else 2; DefectSafe ⟺ CrossSafe; safe defects (arbitrary finite set) ⇒ SM | `cap` (L1165), `cap_eq_three_iff`, `defectSafe_iff_crossSafe`, `strongMajority_of_safe_defects` (kernel, round 3) | KERNEL |
| 24 | No bound on # defects; chained K5-e forces unboundedly many odd cycles | PINS2.md §P3; STRIKE-B B3 | INTERNAL + PRIMARY(construction) |
| 25 | CleanVertex = every cross edge has cap 3 (u and cross-neighbours degree 4); clean transversal def; minimal split def; minimizer exists | `CleanVertex` (L2893), `cleanSet`, `IsOddCycleMinimalSplit` (L1547), `exists_oddCycleMinimal_split` (kernel) | KERNEL |
| 26 | 4-regular: every vertex clean; odd-cycle supports pairwise disjoint, ≥3 vertices; avoidance core = capacitated Hall (`Finset.all_card_le_biUnion_card_iff_existsInjective'`) | `Avoid.avoidance_core`, `oddCycleSupports_pairwise_disjoint`, `oddCycleSupports_three_le_card` (kernel, round 13) | KERNEL |
| 27 | Degree-3 vertex ⇒ poisoning possible; fully-poisoned odd cycle breaks avoidance; that's where the descent lemma is consumed | Pins2.lean `clean_transversal_case_deg3` (L2956, via descent core); §2.6 | KERNEL-COND |

## Section 3 (formal verification)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 28 | Quoted Lean defs (IsProper4, IsEdgeSplit, cap, CleanVertex) + statements (R4_four_regular, R4_three_four) are verbatim from Pins2.lean (docstrings abbreviated) | Pins2.lean L443, L130, L1165, L2893, L3447, L3410 (quoted directly) | KERNEL / on-disk |
| 29 | SMaj.IsStrongMajority + row/cap arithmetic are frozen defs of E5, checked against source papers there; cap uses Lean nat arithmetic (truncated sub harmless) | E5 §3.1; Maj5Base (frozen) | KERNEL + ELEM |
| 30 | §3.2 rewritten as "Known results, novelty scope, and prior formalization": per-sub-case verdicts (cubic known ×2, 4-regular known, mixed open with per-theorem failure reasons); formalization search (nothing besides our E5); TOK = "first machine-checked proof of a strong-majority bound of four", explicitly framed as formalization first only; classical-analogue sweep shows no theorem implies the descent lemma | KILL-CHECK all verdicts; five-color priority_search.md; STRIKE-B §4 | TOK + PRIMARY |
| 31 | Toolkit = single file Pins2.lean over frozen base; 105 decls at standard triple (audited checkpoint), + 4-regular theorem & parallel chain added after; AuditPins2 prints each layer incl R4_four_regular | PINS2.md round 13 (105 decls); AuditPins2.lean L122-141 | KERNEL |
| 32 | Toolkit theme breakdown (count identity, class-I core, P2_equiv 11+6 lemmas, defect calculus ~10 helpers, component lift, 20-decl realizability, structure theory, surgery engine, avoidance core, transversal scaffold) | PINS2.md §2a inventory (rounds 3-13) | KERNEL |
| 33 | Toolchain: Lean v4.28.0, mathlib 8f9d9cff6bd728b17a24e163c9402775d9e6a365 (same pin as E5) | PINS2.md compile-gate section; lean-toolchain / lake-manifest | on-disk |
| 34 | Verbatim axiom lines (nColor_add_two_mul, E1_of_cnt_le_one, E1_split, classI_strongMajority) each [propext,Classical.choice,Quot.sound] | PINS2.md L709-718 (quoted verbatim) | KERNEL |
| 35 | R4_four_regular expected + audit-asserted to print the triple with no sorryAx | AuditPins2.lean L132-135 (assertion in script); source sorry-free on disk | KERNEL (rebuild gate row 40) |
| 36 | R4_three_four + every degree-3 critical-path decl reports sorryAx SOLELY from strict_descent_of_no_clean_transversal; R4_three_four body sorry-free (component lift); file has exactly one sorry, at the descent lemma | AuditPins2.lean L163-169; Pins2.lean grep: only `sorry` at L2949 | KERNEL-COND / on-disk |
| 37 | Double/triple confirmations: E1_split (2), P2_equiv (2 each), exists_oddCycleMinimal_split (2), strongMajority_of_crossSafe_split (3), placement_of_clean_transversal (2) | PINS2.md rounds 3-11 (DC/triple notes); appendix job table | KERNEL |
| 38 | Two corrected premature "false" verdicts: ePot_recolor_diff (truncated-quote refutation; TRUE as pinned, 4440/4440); defectSafe_iff reverse (missed degree-sum clause; kernel-provable) | L3-VERIFY §5.1; PINS2.md round 3 | INTERNAL + KERNEL |

## Section 4 (the falsification record)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 39 | ePot(c) = Σ_{u,v adj} Σ_α nColor(u,v,α)²; pilot conjectured every local minimizer is SM on degree-{3,4}; scaffolding sorry-free + gated; base byte-identical; crux isolated | ATTACK-R4.md §find; L3-VERIFY §1; SUBMISSIONS.md pilot | INTERNAL |
| 40 | Crux refuted 3 ways: 4^13 brute-force 7-vertex family (312 minimizers, 96 non-SM); two 7-vertex graphs (18/42, 60/312); partition-DP (global min ⇒ Δ≥0 every recolor, yet non-SM); no stationarity rescue | L1-CODEX round 1; L3-VERIFY §2a-2b; exact Lean defns | INTERNAL |
| 41 | Architecture abandoned; scaffolding banked+re-audited; crux stays refuted; prover "0 counterexamples exhaustive" summary was wrong (twice) | OVERNIGHT-REPORT ~06:30; BANKED.md; measured-law ledger | INTERNAL |
| 42 | Refuted-hypotheses table (8 rows) each with witness | CHRONICLE §2b; L4-PROBES A/B/C; L1-CODEX; FABLE-CRUX; CODEX-PARITY-KERNEL | INTERNAL |
| 42a | Row: ePot crux — n=7 minimizers non-SM (188/18-42, 192/60-312, 248/96-312) | L3-VERIFY §2a; L1-CODEX | INTERNAL |
| 42b | Row: ePot not viable — global min Δ≥0 yet non-SM, no rescue | L3-VERIFY §2b | INTERNAL |
| 42c | Row: Conjecture P — traps F?qaw, F?rF_; Hamming-3; ≥3-edge moves (0/24, 0/48) | L4-PROBES Probe A | INTERNAL |
| 42d | Row: color-elim supports not always forests — false at m=14, G?zfFo, GCZbsw (C4/K2,2) | L4-PROBES Probe B ext | INTERNAL |
| 42e | Row: bounded-move stationarity k=1,2 — EFzo (n=6), E]zo (n=6, m=11) | L4-PROBES Probe C | INTERNAL |
| 42f | Row: P2″ zero-odd-iff — false at n=10, two K5-e port-joined, 72 splits 0 zero-odd | PINS2.md §STOP; L1-CODEX §Warning | INTERNAL |
| 42g | Row: naive one-swap descent — star swap only non-increasing | FABLE-CRUX §3 | INTERNAL |
| 42h | Row: 3rd-order — a 2-edge exchange DOES strictly decrease at the FABLE witness | CODEX-PARITY-KERNEL §3 | INTERNAL |
| 43 | Single/single-edge locality fails, small coordinated multi-edge moves succeed (3 independent probes) | L4-PROBES A/B/C; measured-law ledger 05:40 | INTERNAL |
| 44 | Random hardening ≠ adversarial: P2″ passed ~317 random graphs then fell to structured K5-e construction; adversarial construction now required pre-formalization | PINS2.md round-3 lessons; ledger ~10:50 | INTERNAL |
| 45 | Third-order exchange re-localized difficulty to degree-3/cap-2, where the descent lemma lives; every turn kernel-or-witness-checked | CODEX-PARITY-KERNEL §3; FABLE-CRUX §3 | INTERNAL |

## Section 5 (the descent lemma)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 46 | strict_descent_of_no_clean_transversal quoted verbatim; carries the file's only sorry | Pins2.lean L2932-2949 (quoted directly) | on-disk (statement) |
| 47 | By minimality equivalent to "every total-odd-minimal split admits a clean transversal"; 3-line contradiction gives clean_transversal_of_minimal; 4-regular branch closes unconditionally; consumed only with a degree-3 vertex | Pins2.lean `clean_transversal_case_deg3` (L2956), `clean_transversal_of_minimal` (L2983); STRIKE-A Lemma 1.1 | KERNEL(reduction) + INTERNAL |
| 48 | Two failure modes: empty-domain (fully-poisoned odd cycle) and non-bipartite-forced | PROBE-I.md; STRIKE-B §1 | INTERNAL |
| 49 | Reduction to the lemma + everything downstream kernel-checked (bridge ×2, classII_arm, connected theorem, component lift, surgery engine); a proof closes R4_three_four the same instant | PINS2.md rounds 10-13; AuditPins2 headline chain | KERNEL |
| 50 | t = #degree-3 vertices, always even | STRIKE-A §0 (H-path-end double counting) | PRIMARY(proof) |
| 51 | t≤2: non-bipartite mode void (Thm B2, capacitated Hall); empty-domain reduces to a poisoned triangle in 2 configs (Thm B1); v2 UPGRADE: both now cited via their kernel-checked forms `nonbip_void_t2` and `poisoned_t2_shape` (§5.3, §2.7) | STRIKE-B §5-6 (B1, B2); Pins3.lean + AuditPins3 (standard triple) | KERNEL (formalized) + PRIMARY |
| 52 | Supply lemma (blocking parity manufactures a 2nd odd component) + debris-linkage ledger Δω = 1_{a odd} − a − b (connected-debris trail) | STRIKE-A Lemma 6.4, Thm 6.5 / Cor 6.6 (Codex-audited) | PRIMARY(proof) |
| 53 | SUPERSEDED IN v2 (kept for the record): the four routing theorems / REACH / NAVIGATE narrative no longer appears in the paper as the t≤2 residual — §5.3 now describes the lemma-ladder status generically ("reduced the t≤2 restriction of the lemma to a single named open pin at its last audited checkpoint; general-t scaffold modulo three named pins") | STRIKE-A §6.10; OVERNIGHT-REPORT "FINAL NIGHT STATE" (walker EXACT: t≤2 → odd sub-pin; general → +genxsel_general, nonbip_pierced_general) | INTERNAL (ladder status) |
| 54 | §5.3 v2 claims: (i) the THEOREM at t≤2 no longer depends on the descent lemma (migration route, rows T1–T6); (ii) the descent LEMMA remains unproved even restricted to t≤2; (iii) no open pin touches R4_three_four_t2's cone | rows T1/T4/T6; OVERNIGHT-REPORT headline ("SCOPE-HONEST: t ≤ 2 only — general t stays open; Pins2 L2932 undischarged") | KERNEL + INTERNAL |
| 55 | t≥4: class-II degree-{3,4} graphs with arbitrarily many degree-3 vertices exist (B3); general lemma does not reduce to t≤2 | STRIKE-B B3 (§6.4, explicit construction) | PRIMARY(construction) |
| 56 | B1/B2/B3 as stated; config (iii) impossible by handshake | STRIKE-B §5 (B1), §6 (B2), §6.4 (B3); WITNESS-MINING §0A | PRIMARY(proofs) |
| 57 | Complexity fence: deciding 4-edge-colorability of 4-regular (= minimal split odd-count 0) is NP-complete (Leven-Galil); no poly-verifiable local optimality characterization; lemma must fire on a certificate; vacuous on 4-regular core | STRIKE-B §0.2, §2, §4.2; Leven-Galil J. Algorithms 4 (1983) | PRIMARY |
| 58 | Objective = two-class analogue of cubic oddness / even 2-factorizations; snark/CDC territory | STRIKE-B §0.1, §4 items 1-2 | PRIMARY |
| 59 | Literature sweep (Euler partitions; equitable/evenly-equitable colorings de Werra, Hilton-de Werra, Erzurumluoğlu-Rodger; oddness Huck-Kochol, Steffen; even 2-factorizations Markström; Fournier; compatible tours Kotzig, Fleischner, Sabidussi): no theorem implies the lemma; missing = parity-controlled compatible-rerouting | STRIKE-B §4 (verified citations, exact deltas) | PRIMARY + TOK |
| 60 | Four aggregate shortcuts each failed with a concrete class-II witness | CODEX-DESCENT §3 (averaging/T-join, △-trails, saturation, whole-cut parity) | INTERNAL |
| 61 | Evidence: 1,380 minimal split-halves through 9 vertices, zero failures, incl. chained-K5-e to 25 vertices (7,776 splits exhaustive) | PROBE-I.md | INTERNAL |
| 62 | 1,376/1,376 exhaustive n≤8 seeded-trail strict descents; crossing rule 131/131 on complete blocked corpus (the corner cases behind NAVIGATE never fire) | WITNESS-MINING §1, §0C; STRIKE-A §5, §6.10 | INTERNAL |
| 63 | Codex-2 alt reduction validated 1,090,339/1,090,339 omitted-root comparisons through n=9 + targeted order 10/11, zero failures | CODEX-DESCENT-2.md §14.1 | INTERNAL |
| 64 | The 15,525-instance tally is NOT reproducible from disk (corpus not saved); we do not rely on it; the cited numbers are reproducible | WITNESS-MINING §1 caveat; CHRONICLE lesson 10 | INTERNAL (honest caveat) |
| 65 | None of the evidence is a proof; lemma not presented as established | honest framing throughout §5 | ELEM |

## Section 6 (methods) + Section 7 (open problems)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 66 | Tools: Aristotle, Codex (GPT), Claude; no claim accepted solely on model output; formal by kernel, computational by stated procedures | ops/METHODS-STATEMENT.md (deflated adaptation, per E5 §5 doctrine) | INTERNAL |
| 67 | Pin-audit-reject protocol; an architecture + 8 hypotheses rejected on counterexamples | §4; transplant-gate (PINS2.md §4 methodology) | INTERNAL |
| 68 | Reproduction: single rebuild command prints audit incl R4_four_regular AND R4_three_four_t2 = triple no sorryAx, and exhibits the remaining sorries exactly at the descent lemma + general-t pins (outside both unconditional cones); clean-env rebuild is a release gate | Fresh G1 Modal farm call `fc-01KXEC3Z42KZZGRX2J5SD5V5MR` at HEAD `6c7f364` (theorem bytes from `121821a`): 8029 jobs, all 7 release decls exactly [propext, Classical.choice, Quot.sound]; AuditPins2.lean; AuditPins3.lean; RewireWalker.lean; TRIAGE addendum §4 | KERNEL (G1 CLOSED) |
| 69 | Author identity block: John Erlbacher, Independent Researcher, erlbacher.research@gmail.com, ORCID 0009-0003-6851-4139 | project identity record (CLAUDE.md) | INTERNAL (owner confirms at review) |
| 70 | Open: conjecture untouched (regular sub-cases credited to KKPW/APS; our unconditional content = the t≤2 theorem + machine-checked proof of the known 4-regular case); descent lemma open at named pins (general-t classification+supply beyond the t≤2 residue; possible general-t migration analogue named as the other attack); degree-3 chain zone (local repair); higher degrees (different decomposition; E5 route uses one extra color) | §7 (v2); STRIKE-A §8; STRIKE-B §6.4; OVERNIGHT-REPORT final-night state | ELEM + INTERNAL |
| 71 | Bibliography entries (APS, KKPW, Hilton-de Werra, Leven-Galil, Kotzig, Fleischner, Stiebitz et al., mathlib, E5) details correct | standard citations verified in STRIKE-B sources list; E5 = zenodo 21316623 | PRIMARY |

## Pre-release gates (must close before any external surface)

- **G1 CLOSED (2026-07-13; rows 6/35/68/T1):** fresh clean-environment Modal farm call `fc-01KXEC3Z42KZZGRX2J5SD5V5MR` at repo HEAD `6c7f364` (release-theorem bytes unchanged from `121821a`), `lake build Pins3` = 8029 jobs; all 7 release declarations printed exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Earlier campaign gates remain recorded at `C:\t\r4cdx` and `C:\t\r4final`.
- **G2 (rows 0/8/9/30/T3):** re-confirm at send time: (i) the mixed slice (incl. the t=2 sub-slice) is still open in the literature (re-run the Maj′ sweep), (ii) the "first machine-checked proofs of a strong-majority bound of four" wording, (iii) no new KKPW/APS versions changed the proposition numbering quoted from KILL-CHECK-R4.md.
- **G3 (row 4):** confirm the E5 artifact DOI resolves publicly (concept DOI 10.5281/zenodo.21316623) and that the self-citation is correct at deposit.
- **G4:** owner review of identity block, methods paragraph, the unconditional t≤2 framing (Theorem 2.2 = thm:t2), and the conditional framing of the general theorem (never present general degrees-{3,4} as established).
- **G5:** KERNEL-OR-HOLD — the two unconditional theorems (4-regular, t≤2) are self-verifying by rebuild; the GENERAL degrees-{3,4} theorem is CONDITIONAL and must never be sent as a positive general-n result without the descent lemma closed.

## Prohibited wordings (checked absent from main.tex; kill-check FORBIDDEN list folded in)

- **"first proof that 4-regular graphs satisfy Maj′ ≤ 4"** — FORBIDDEN (KKPW Prop 21); absent. The 4-regular result is always attributed to KKPW; only "first machine-checked proof" is claimed.
- **"first proof for cubic graphs"** — FORBIDDEN (KKPW Prop 15; APS Thm 4); absent (cubic never claimed).
- **"resolves/advances Conjecture 14 for regular graphs"** — FORBIDDEN (both regular sub-cases were done); absent.
- **Any phrasing implying degrees-{3,4} was wholly open** — FORBIDDEN; absent (§1.2 and §3.2 state the mixed-only novelty with per-theorem failure reasons).
- "first infinite family/class" for the 4-regular theorem — STRUCK in the re-anchor (row 8a); absent.
- Degrees-{3,4} theorem stated as proved/established/kernel-complete — absent (always "conditional", "modulo one lemma", "not proved").
- "solves"/"resolves" the KKPW conjecture — absent.
- Unqualified priority ("first ...") without "to our knowledge" + scope — absent (every "first" audited against the kill-check verdicts in the re-anchor pass).
- Reliance on the 15,525 tally — absent (row 64 caveat stated).
- Any claim the evidence supports the lemma as true — absent ("evidence only", "not a proof").
- **(v2) Any phrasing implying the t≤2 theorem covers the full mixed class** — FORBIDDEN; the paper says "a slice, not the mixed class" explicitly (abstract, §1.2(a), §1.3, §3.2, §7).
- **(v2) "first machine-checked/machine-verified strong-majority result" or "first in the field"** — FORBIDDEN (our own E5 five-color verification is prior); only "first machine-checked bound of FOUR" is claimed, with E5 always named.
- **(v2) The descent lemma described as closed at t≤2** — FORBIDDEN; §5.3 states the lemma "remains unproved even restricted to t ≤ 2"; only the THEOREM is closed there, by bypass.
