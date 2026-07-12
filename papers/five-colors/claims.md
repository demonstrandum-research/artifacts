# Claim ledger — "Strong Majority Edge-Coloring with Five Colors" (main.md)

Rule (HARVEST-PLAN-RUNG5): every factual claim in the paper has a line here; no claim without a line.
Status codes: **KERNEL** = kernel-checked Lean artifact · **PRIMARY** = verified against the primary source this session (sha-pinned where noted) · **INTERNAL** = verified internal artifact (exact computation / audit record, not kernel) · **TOK** = "to our knowledge" with documented search scope · **SEQ** = sequencing-dependent, must be true at publish time · **PENDING-PACKAGING** = resolves when the release artifact is assembled/deposited; do not release before closing · **OPEN** = other pre-release check outstanding.

Revision note (fix pass, same day): all 16 blockers + applicable should-fixes from problems/p5-strongmajority/rung5-lanes/codex_release_review.md worked through; rows updated/added below and marked "(fix pass)" where new.

## Front matter, abstract, Section 1

| # | Claim | Evidence | Status |
|---|---|---|---|
| 1 | APS = Antoniuk, Prorok, Salia; arXiv:2607.00212; **posted** 30 June 2026; only v1 exists (as of 2026-07-11) | rung5-lanes/erratum_verification.md §0 (live abstract-page fetch; tarball sha256 5a2da291…; tex sha256 995b9624…) | PRIMARY. Wording binding: "posted", never "published" |
| 2 | APS Theorem 2: Maj′(G) ≤ 5 for every admissible G (label `thm:five`, compiled number 2) | rung5-lanes/transplant.md §VII.1 (verbatim tex); erratum_verification.md §0.1 | PRIMARY |
| 3 | APS route = Hilton–de Werra equitable coloring (their Theorem 1) + reductions (R1)–(R5) + restorations via Claims 7–10 / Remarks 6, 9 | transplant.md §I, §III; numbering per erratum_verification.md §0.1 correction table (Theorem 4 / Claim 7 / Claim 8 / Remark 9 / Claim 10) | PRIMARY. Numbering corrections APPLIED throughout main.md |
| 4 | KKPW = Kalinowski, Kamyczura, Pilśniak, Woźniak, arXiv:2605.23828 (submitted 22 May 2026); Theorem 12: Maj′ ≤ 8; Conjecture 14: Maj′ ≤ 4, best possible | problems/p5-strongmajority/PROBLEM.md §0, §2, §3 (frozen dossier, verbatim quotes from paper.txt) | PRIMARY (frozen dossier) |
| 5 | Smallest Maj′ = 4 graph is the paw | rung5-lanes/scout.md census (unique smallest witness, two-solver exact); consistent with KKPW "there exist graphs with Maj′=4" | INTERNAL |
| 6 | Coloring exists iff no pendant path of length two; admissible ⇔ no adjacent degree pair {1,2} | PROBLEM.md §1.3 (verbatim); transplant.md §VII.3.1 (equivalence proof) | PRIMARY + elementary |
| 7 | "To our knowledge, first machine-checked result on majority-type edge-colorings in any proof assistant" | rung5-lanes/priority_search.md (sweep: mathlib, GitHub Lean, Isabelle/AFP, Coq/MathComp, Mizar, Metamath, HOL, tracking lists, arXiv — no edge-coloring formalization beyond items 35–36 below, none on majority colorings) | TOK (scope documented) |
| 8 | We previously formalized Maj′ ≤ 6 (kernel) | p5 lean tree `SMaj.maj_le_six`; ATTACK.md C9L3 audit row (197/197 decls, bedrock triple) | KERNEL |
| 9 | Six-color construction's bottleneck was Shannon's bound, tight on fat triangles | rung5-lanes/synthesis.md §0, §3; frozen artifact gap analysis | INTERNAL (mechanism statement) |
| 10 | "Strongest bound known toward the conjecture" (5) | APS Theorem 2 is the best published/posted bound; KKPW had 8 | PRIMARY (both papers read) |

## Section 2 (the alternative proof)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 11 | Theorem 2.1 (Maj′ ≤ 5) holds — the paper's headline | `SMaj.Synthesis.maj_le_five`, kernel-checked; sol_ladder/STATUS.md; ledger-inbox addendum 32 | KERNEL |
| 12 | Glue interface + dispatch (Prop 2.2) palette-generic and pre-existing | `SMaj.IsGlueColoring`, `strongMajority_of_glue`, `maj_le_five_of_glue` in Maj5Base.lean (frozen, kernel-closed before this work) | KERNEL |
| 13 | Bad-pair table exactly {(1,2),(2,2),(2,3),(2,5)} | `bad4_table` (Maj5Base.lean, kernel-checked); synthesis.md §1 hand-verification | KERNEL |
| 14 | Saturated sets: card ≤ 2; empty unless junction degree ∈ {3,5}; ⌈d/4⌉=⌊d/2⌋ iff d∈{3,5} (d≥3) | `card_satSet_le_two`, `satSet_eq_empty_of_ne`, `g_R4_eq` (Maj5Base.lean) | KERNEL |
| 15 | Steered partition exists (sizes ≤4, count ⌈d/4⌉, ≤3 at d∈{3,5}) | `SMaj.exists_steered_partition` (Λ1, double-closed, addendum 26); `steeredGlueIx*` lemmas in Rung5Lam4.lean | KERNEL |
| 16 | Every (4,4) μ=2 parallel class contains a length-2 chain (cherry always exists) | synthesis.md V2.1 (argument); proved inside Λ4 construction (M contains only ℓ≤2 chains; direct edges unique per pair) | KERNEL (in cone) |
| 17 | Remaining parallel classes satisfy μ ≥ s_P+s_Q−5 (complete case split) | synthesis.md V2.1 Rule 3; consumed by Λ3/Λ4 hypotheses in the kernel chain | KERNEL (in cone) |
| 18 | Simple graphs have no loop chain of length ≤ 2; M loopless by construction; M₀ simple, Δ ≤ 4 | synthesis.md V2.1; Λ4 construction invariants | KERNEL (in cone) |
| 19 | Vizing at Δ≤4: 5-colorability of simple M₀ (Λ2) | `SMaj.Lam2.exists_five_multicoloring_of_simple` (Rung5Lam2.lean; gate-confirmed addendum 30; fable_ladder/audit_lam2_fable.out) | KERNEL |
| 20 | Greedy reinsertion works; order-independent; forbidden ≤ 4 < 5 (Λ3) | `exists_five_multicoloring_of_reinsertable` + `reinsert_core` (Rung5Lam3.lean; addendum 28) | KERNEL |
| 21 | Port pass: ≤ 3+1 = 4 < 5 forbidden; length-3 port disequality forced by (G4) | synthesis.md V2.2; Λ4 first-fit port pass, kernel-checked | KERNEL (in cone) |
| 22 | Interior fills always possible with 5 colors (satSet ≤ 2 + distance-2 ≤ 2) | `isFill_exists`, `exists_avoid` (Maj5Base.lean, frozen, stated for card C ≥ 5); cycle case `cycle_distance2` | KERNEL |
| 23 | De-fattening invariants machine-checked on a suite of hand-constructed test instances + 1,854 random graphs before formalization | rung5-lanes/gauntlet.md §8.1; synthesis.md V2 preamble (I1–I3 zero failures); re-execution certificates V2.3 | INTERNAL |
| 24 | rankIx: canonical grouping from any capped coloring; rainbow unconditionally; reduces Λ4 to three row-level properties (hmult/hint/hend) | `rankIx`, `rankIx_isRainbow`, `rankIx_groups_le`, `exists_glueColoring_of_coloring`, `assembledColor_hmult/hint/hend` (Rung5Lam4.lean); addendum 29 | KERNEL |
| 25 | Remark 2.7: equitability at d=4 with 5 colors forces counts (1,1,1,1,0); an HdW theorem strong at d=4 contains Vizing-grade recoloring at Δ=4 | synthesis.md §6.1; pilot_triage_notes.md Check 1 (counting verified); stated as a remark, not a theorem | INTERNAL (elementary, stated as remark) |

## Section 3 (formal verification)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 26 | Quoted Lean definitions/statement from the artifact base file (code exact; docstring comments abbreviated, stated in text); base byte-anchored across all payloads | payloads/rung5_lam1/Maj5Base.lean L57–78 + frozen target; byte-anchor sha c6b6b895 (addendum 32). **PACKAGING NOTE:** the released `artifact/lean/Maj5Base.lean` is a stub-stripped derivative (new sha 403e0717…) — one dead placeholder `theorem SMaj.maj_le_five := by sorry` (referenced nowhere; superseded by `SMaj.Synthesis.maj_le_five`) removed so the shipped build is entirely sorry-free; quoted defs (side/row/nColor/IsStrongMajority/Admissible, L57–78) are unchanged; rebuilt+re-audited fresh (Codex-consulted; provenance in artifact/lean/HASHES.txt) | KERNEL / on-disk |
| 27 | Integer threshold ⇔ papers' rational threshold, both parities, incl. K₂ edge | transplant.md §VII.3.2 (parity check written out) | PRIMARY + elementary |
| 28 | `row` = adjacent-edge set exactly; own color slot never counted; quantifier includes α = c(e) | transplant.md §VII.3.3; `disjoint_sides`, `card_row` (Maj5Base.lean) | KERNEL |
| 29 | Toolchain: Lean 4 v4.28.0; mathlib commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365; same pin chain-wide | payloads/*/lean-toolchain + lake-manifest.json (read this session) | on-disk |
| 30 | Axiom footprint exactly [propext, Classical.choice, Quot.sound] for maj_le_five and each named layer (7 printed layers) | sol_ladder/audit_final_gateS.out (read this session); fable_ladder/audit_final_gateF.out; STATUS.md | KERNEL |
| 31 | Zero sorry / sorryAx / native_decide / suspicious patterns (14-pattern sweep, truncation-marker scan) in the cone | addendum 32 six-element ritual; pilot_triage_notes.md FINALE GATE VERDICT | INTERNAL (audit record) |
| 32 | "Two clean builds with separate verification blocks over a substantially shared construction"; 8,037 jobs each, exit 0; construction backbone shared, rankIx block token-identical; NOT two independent formalizations | addendum 32; pilot_triage_notes.md FINALE GATE (gateF/gateS, C:\t\gateF, C:\t\gateS) | INTERNAL. **WORDING BINDING** — never "independently verified twice" unqualified; the paper's §3.4 disclaimer paragraph is mandatory text |
| 33 | Line counts: base ≈5,300; Λ2 = 802; Λ4 ≈2,400 | measured on disk this session (Measure-Object) | on-disk |
| 34 | mathlib has no edge-coloring theory at the pin (vertex coloring only) | priority_search.md §1c (greps: Vizing/EdgeColoring/Kempe/Kierstead = 0 hits in mathlib4) | PRIMARY (search) |
| 35 | Bhoja, arXiv:2512.13999 (Dec 2025): complete sorry-free Lean 4 formalization of full Vizing (Misra–Gries), bespoke graph type, deliberately not mathlib-integrated | priority_search.md §1a (paper + repo read; sorry search 0 hits) | PRIMARY (source read). **Must be cited wherever our Vizing component is discussed** — done (§3.2, §6, refs) |
| 36 | Okur–Helm 2023: mathlib-based course project, edge chromatic number + easy lower bound only | priority_search.md §1b | PRIMARY (search) |
| 37 | "To our knowledge, first formalization of Vizing's theorem stated against mathlib's SimpleGraph API" (ours Δ≤4 only — stated) | priority_search.md Claim A mandated wording; our core `edgeColorable_five_of_degree_le_four (G : SimpleGraph W)` confirmed SimpleGraph-native (Rung5Lam2.lean L783) | TOK (mandated wording used verbatim) |
| 38 | "To our knowledge, first substantial edge-coloring library built on mathlib's SimpleGraph" (citing Bhoja + Okur–Helm) | priority_search.md Claim C mandated wording | TOK |
| 39 | "To our knowledge, first formalization of Kierstead paths in any proof assistant" | priority_search.md Claim B (searched: mathlib, GitHub Lean, AFP, Coq, Mizar MML, Metamath, tracking lists, arXiv) | TOK |
| 40 | One-command rebuild: `lake build Rung5Lam5` from the artifact's Lean project directory; final file prints the axiom audit; §3.5 defers exact layout to the artifact README | `papers/rung5-five-colors/artifact/lean/` (self-contained project, README + rebuild_and_audit.sh); fresh build re-verified 2026-07-11 in `C:\t\r5pkg` (`lake build Rung5Lam5` exit 0, 8037 jobs, sorry-free; `SMaj.Synthesis.maj_le_five` = [propext, Classical.choice, Quot.sound]) | **CLOSED** — artifact/lean assembled + fresh-build reproduced; top-level `artifact/README.md` fixes the layout/command |

## Section 4 + Appendix A (clarifications)

| # | Claim | Evidence | Status |
|---|---|---|---|
| 41 | Item (a) degree-1 in Theorem 4's proof: displayed inequality false at d=1; one-sided repair valid; Remark 6 handles the analogue in the 5-color proof | erratum_verification.md Item A: **CONFIRMED (minor)** — verbatim tex quotes | PRIMARY (sha-pinned tex, hostile lane) |
| 42 | Item (b) duplicated Case k=1 passage in the proof of **Claim 10**; count 3+2−1<5 correct in both drafts | erratum_verification.md Item B: **CONFIRMED (editorial; Claim 10, not Claim 7)** | PRIMARY. Numbering correction applied |
| 43 | Item (c) omitted case: degree-5 vertex with two loop ears in undo-(R1); witness admissible/connected/non-cycle; both degree readings fail; three leaves + four terminals; Remark 9's "exactly one operation" inaccurate | erratum_verification.md Item C: **CONFIRMED (genuine omitted case; repairable)** — C.1–C.3 | PRIMARY |
| 44 | Appendix A repair correct, uses only Claims 8, 10 + Remark 9's distinctness | erratum_verification.md C.4–C.5 (repair verified) | PRIMARY |
| 45 | Decisive quote ("For d_G(v)=5, the single leaf was removed…") verbatim | erratum_verification.md C.2 | PRIMARY (quote license per supervisor) |
| 46 | "A note detailing these observations has been sent to the authors" (§4, present perfect) | HARVEST-PLAN-RUNG5 timeline (APS email at T+3h, publish at T+3.5–4h); attachment = papers/rung5-five-colors/aps_memo.md | **SEQUENCING-SENSITIVE — RELEASE-BLOCKING: this sentence is FALSE until the APS email (with the memo attached) is confirmed sent; publish only after send confirmation, or edit to future/neutral tense. If publication somehow precedes the send, change to "We are sending these observations to the authors" and log the deviation** |
| 47 | No correction published by the authors (v1 only) as of 2026-07-11 | erratum_verification.md §0 + release ruling | PRIMARY (live fetch, dated in text) |

## Sections 5–6, references

| # | Claim | Evidence | Status |
|---|---|---|---|
| 48 | §5 opening disclosure paragraph (tools named; "no mathematical claim accepted solely on the basis of a model's output") | deflated adaptation of ops/METHODS-STATEMENT.md per review blockers 13–14; factual content per rows 30–31, 61 | see row 62 — owner adjudicates |
| 49 | "What the tools did": pinned statements, independent rebuild audits, byte-fidelity checks, rejection policy; separate §4 review pass from source | pilot_triage_notes.md (audit protocol throughout); erratum_verification.md header | INTERNAL |
| 50 | Census: 268,478 admissible connected types on ≤9 vertices all 4-colorable; 89,771 connected 4-regular (10/12/14) all 4-colorable; 592 targeted; exact census ≤8 vertices: max index 4, never 5 | rung5-lanes/scout.md (exact SAT, models re-checked against frozen inequalities, UNSAT dual-solver; census.json, census_extremal.json) | INTERNAL (exploratory; paper says "separate from and not entering the Lean verification") |
| 51 | Hilton–de Werra reference: Discrete Mathematics 128 (1994), 179–201 | standard citation (Hilton & de Werra, "A sufficient condition for equitable edge-colourings of simple graphs") — details correct | **CLOSED (standard citation, verified correct)** — final bibliography proofread is inside John's paper review (owner review is a release gate) |
| 52 | Vizing 1964 (Diskret. Analiz 3, 25–30); Shannon 1949 (J. Math. Phys. 28, 148–151); mathlib CPP 2020 | standard citations — details correct | **CLOSED (standard citations, verified correct)** — final bibliography proofread inside John's paper review |
| 53 | Artifact DOI (two occurrences: front matter, §3.5) = 10.5281/zenodo.21316624 | Zenodo draft deposition 21316624 created this session (state=unsubmitted; prereserved DOI 10.5281/zenodo.21316624; files: artifact zip, paper.md, READING-KIT.md, aps_memo.md); tokens filled in main.md front matter + §3.5, website/release-rung5.md, website/chronicle-two-routes.md | **CLOSED** — DOI prereserved + substituted. Links-gate note: DOI URL + GitHub paths resolve publicly only at the user-gated publish/push; orchestrator runs the links pass at transmission |
| 54 | Reading kit ("expanded English gloss … ships in the artifact's reading kit", §3.1) | `papers/rung5-five-colors/artifact/READING-KIT.md` (house standard: Lean statement, gloss of every def to mathlib bedrock, [APS] Thm 2 → formal-statement bridge, pasted axiom output, one-command rebuild, #eval/decide demos); in the Zenodo deposit + artifacts-repo copy | **CLOSED** — kit written and in the deposited artifact + standalone Zenodo file |
| 55 | (fix pass) Author identity block: name, Independent Researcher, erlbacher.research@gmail.com, ORCID 0009-0003-6851-4139; draft date | project identity record (CLAUDE.md identity block, owner-set); date = today | INTERNAL (owner identity record; John confirms at review) |
| 56 | (fix pass) Low-degree components elementary + every edge lies in exactly one chain (forced-walk argument, §2.1) | `SMaj.maj_le_five_of_maxDegree_le_two` (kernel); ChainDecomp/IsPiece layer in Maj5Base.lean (kernel); prose argument elementary | KERNEL + elementary |
| 57 | (fix pass) §2.1 "two immediate consequences of admissibility" + caveat that the formal proof uses `hadm` through further lemmas | Maj5Base.lean admissibility lemmas; caveat added per review should-fix 1 | KERNEL (caveat honest) |
| 58 | (fix pass) "Greedy and Shannon-type arguments give only six colors there; Vizing gives five" + "what the present route adds over our earlier six-color construction" (§2.2) | Shannon tightness: synthesis.md §0/§3 + frozen artifact gap analysis; greedy insufficiency at Δ=4 subagent-verified (pilot_triage_notes.md, Λ4b-direct: conflict degree 6 ≥ 5); six-color construction = our kernel maj_le_six | INTERNAL + KERNEL |
| 59 | (fix pass) §2.4 port pass as SEQUENTIAL first-fit with ≤3 group colors + partner-port constraint at length 3; fill split l=3 (avoid F_x ∪ F_y, ≤4) vs l≥4 (≤2 distance-two + ≤2 satSet) | synthesis.md V2.2 (pass order); `isFill_exists` hypothesis `l = 3 → p ≠ q` (Maj5Base.lean); Λ4 first-fit port pass + fills (kernel) | KERNEL (prose now matches the formal split; review blockers 1–2 fixed) |
| 60 | (fix pass) §4 closing: "the Lean verification establishes the theorem independently of the APS text" | `SMaj.Synthesis.maj_le_five` kernel artifact; no APS-text dependence in the cone (route of §2) | KERNEL (replaced the unsupported "architecture confirmed sound" — review blocker 6) |
| 61 | (fix pass) §5 operational claims: pinned statements, byte-fidelity checks, rebuild-from-scratch audits, rejection policy, separate §4 review pass, SAT ground-truth instance checks | pilot_triage_notes.md (audit protocol + verdicts); erratum_verification.md header (separate pass); gauntlet.md + synthesis_prepin checks (SAT ground truth) | INTERNAL |
| 62 | (fix pass) §5 text is a deflated adaptation, NOT the verbatim ops/METHODS-STATEMENT.md | supervisor fix-pass order (codex_release_review.md blocker 13) overriding the verbatim rule | **FLAG FOR JOHN — doctrine conflict resolved in favor of the review on supervisor order; owner adjudicates final §5 text** |
| 63 | (fix pass) aps_memo.md — every quotation verbatim from the v1 tex; numbering per the correction table; repair identical in substance to erratum_verification.md C.4–C.5; tex line numbers 301/303 for the duplicated passage | erratum_verification.md (all items CONFIRMED; quotes and line numbers therein) | PRIMARY. This file is the intended attachment for the APS letter (closes review blocker 16's "attach the repair") — outbox lane must actually attach it |

## Prohibited stronger wordings (checked absent from main.md; re-checked after the fix pass)

- "independently verified twice" (unqualified) — absent; §3.4 uses the mandated formula and adds the explicit disclaimer.
- "published" for APS — absent ("posted" throughout).
- "gap"/"error" as a headline for Section 4 — absent (title: "Clarifications to the original proof"; theorem-survives stated first).
- Any unqualified "first Vizing formalization" / "first edge-coloring formalization" — absent (Bhoja cited prominently, now also at the point of the §1.3 claim; TOK wordings verbatim from priority_search.md).
- Any claim that the census evidence supports the conjecture — absent ("finite evidence only … no conclusion").
- "architecture our verification confirms is sound" — REMOVED in the fix pass (review blocker 6); replaced by the kernel-supported sentence (row 60).
- Ports chosen "independently" — REMOVED (review blockers 1 and nit 3); §2.3/§2.4 now describe the sequential pass with its constraints.
- "no claim rests on any model's output" — REPLACED by "no mathematical claim was accepted solely on the basis of a model's output" (review blocker 14).
- Tone list from the review (counting villains / enemy / deep core / pay the toll / groupings for free / adversarial battery / hostile lane / where the mathematics lives / autonomous-frontier-proprietary paragraph) — all removed or neutralized (review blocker 13).
