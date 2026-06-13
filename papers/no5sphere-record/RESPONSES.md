# Referee report and responses — `note.tex` (C(13) >= 36, no-5-on-a-sphere)

Hostile-referee pass of 2026-06-12 (second pass; the first is logged in
BUILD.md). Referee 1: Claude (this session); Referee 2: Codex GPT-5.5,
thread `019ebb24-3caf-7622-b70a-386709d4571e` (initial review) with a
follow-up re-review of the revision in the same thread. Every numerical
claim in the note was recomputed from scratch by *both* referees with
independent code (`referee_recompute.py` in this directory, report in
`referee_recompute_report.json`; Codex wrote its own checker in-session);
every bibliography entry was re-verified against live sources.

**Both referees' final verdict: SURVIVES.** The theorem and certificate are
correct; all defects found were calibration/citation/wording issues, all
fixed below. `note.pdf` recompiled (6 pages, log clean: 0 overfull, 0
warnings).

## A. What was independently re-verified and CONFIRMED (no change needed)

1. **The theorem.** All C(36,5) = 376,992 lifted 5x5 determinants of the
   36-point set (parsed from the note's own verbatim block, not from the
   bundle) are nonzero — recomputed by full 120-term permutation expansion
   (Claude) and by a separate method (Codex). min |det| = 2,
   max |det| = 198,750, exactly 200 subsets with |det| <= 10.
2. **Table 1.** All 18 rows: sigma(p) = (12,12,12) - p correct, 4rho^2
   values correct, sorted, pairwise distinct; union of the pairs equals the
   verbatim 36-point list, which equals the bundle certificate
   (sha256 `333d36ec...` matches the note; byte-identical to the discovering
   run's `FOUND36_sym.json`).
3. **Structure claims.** Layer profiles (x/y/z) exactly as printed,
   palindromic, max 4 per axis plane; 16 of 36 points on the cube surface;
   center cell absent; 13^3 = 2197; C(36,5) = 376,992;
   24*12^3*432 = 17,915,904 < 2^25; 4*13 = 52.
4. **Saturation.** No 37th point: all 2161 non-member cells blocked
   (recomputed, both referees). The published 33-point set: 0 addable cells
   for all 8 translates of the 12-cube in the 13-cube (recomputed; ~127M
   determinants, Claude vectorized int64 engine cross-checked against the
   permutation expansion on 2000 random 5-subsets).
5. **Convention anchor.** All six official AlphaEvolve record sets
   (21/23/26/28/31/33 for n = 7..12, from `data/records.json`) re-verified
   valid with fresh code; known-bad 34-set rejected; n=12 set's min |det| = 2.
6. **Mutation testing.** All 7 corruptions rejected by fresh code; the cell
   (1,8,0) indeed completes coplanar zero 5-subsets with the orbit pairs
   named in the bundle.
7. **Quoted program.** The verbatim block matches `check_cert.py` exactly
   (machine diff).
8. **Run-log numbers.** 840.9 s / 611,969 iterations / 627 restarts / 8
   threads / seed 20260612 (`runs/central-symmetric/main-run/STATUS.json`);
   4.0 s smoke (2 threads); 22-min baseline snapshot with 198 distinct 34s,
   182 from the fixed-bug arm, 1 distinct 35 at t = 538.2 s; blocker-repair
   55+48+48 min with 4068/2528/2833 34s, 20/30/47 35s, dead-end histogram
   {34: 510, 35: 18} for run 1; 4126 symmetric 34s in 14 min. Epochs
   confirm 11 June (34, 35) and 12 June 00:29:19 (36); dossier freeze to 36
   was 2h47m ("roughly three hours" OK). Rust crate: 28 unit tests, re-run,
   28/28 pass, including the 5 degenerate-quadruple traps.
9. **Citations confirmed as claimed:** Suk–White (SoCG 2025, LIPIcs 332,
   76:1–76:8, n^{3/4-o(1)} for d=3); Dong–Xu 2506.18113 (n - o(n));
   Szabó 2511.03526 (title/author/content); AlphaEvolveMath 2511.02864
   (title, 4 authors, v3 dated 22 Dec 2025; values 21/23/26/28/31/33 and the
   verbatim harness-bug quote re-checked in the official notebook);
   AlphaEvolve 2506.13131 (all 18 authors in order); Ball, JEMS 14 (2012)
   733–748 (q+1 bound for k <= p, so 14-point cap in PG(4,13) is a correct
   inference); Thiele 1995 FU Berlin dissertation (c sqrt(n) and 4n bounds
   corroborated by PatternBoost and Suk–White); problem-60 page statement
   verbatim against the archived live fetch. Openness re-checked 2026-06-12
   by both referees independently: no public C(13) >= 34 (or C(12) >= 34)
   claim found anywhere.

## B. Defects found and FIXED in this revision

| # | Found by | Defect | Fix in note.tex |
|---|---|---|---|
| 1 | Claude | "22-line program" / "22 lines of Python": the quoted accept path is **21** lines (machine count) | Both occurrences now "21" |
| 2 | Claude | "in about two seconds": measured 0.73–0.79 s | "in about a second"; "Running it" -> "Running `check_cert.py`" (the quoted function alone prints nothing) |
| 3 | Claude | Timeline: "baseline ILS (t = 47 s)" was the *main* run; the pilot's first 34 was 53.8 s into its *smoke* run (23:18, 11 June); also the finite-field pilot's first 34 was 00:23 on 12 June, so dating "two further pilots" to 11 June was loose | Row now reads "baseline ILS, 53.8 s into its own smoke run; both further pilots followed within hours" |
| 4 | Claude | "rejected by every route" overclaimed: per `gate45_report.json` the float corruption is "n/a" for the integer-only Rust parser | Now "rejected by every applicable route", with the float/Rust parse caveat spelled out |
| 5 | Claude | Table 3 finite-field row "71" was the cross-run union, contradicting the caption's "deduplicated within each run, not across runs"; "8.5 min" was a mid-run harvest, final STATUS says 705.4 s | Row now "5.5 + 11.8 min", "69 / 71"; caption notes the overlap (all 69 of run 1's sets recur among run 2's 71 — Codex verified this set-theoretically from the JSONL pools) |
| 6 | Claude | "reproducible from the archived search binary": the archived prebuilt `symsearch.exe` is the phase-1 binary *without* `--target`; reproduction requires building the archived crate snapshot | "archived search-code snapshot and command line" |
| 7 | Claude | BMP2005 locator "[Chapter 10, Problem 4]" imprecise and attached to the wrong problem (the circle problem); Dong–Xu cite the *sphere* problem as "Problem 4 of Chapter 10.1" | Citation moved onto the no-(d+2)-on-a-sphere problem with locator "Problem 4 of Chapter 10.1" |
| 8 | Claude | Lemma 2.2 proof sentence "any five vectors in its span plus one more vector..." garbled | Rewritten: "Together with the lift of any fifth point they therefore lie in a subspace of dimension at most 4, and the 5x5 determinant vanishes." |
| 9 | Codex | "no floating point is used anywhere in search or verification" literally false: the Rust search uses f64 for branch probabilities and timers (never validity) | Methods paragraph and Section 4 opener now claim exact integer arithmetic for every geometric test / validity decision only |
| 10 | Codex | PatternBoost citation: the printed n=10 witness in arXiv:2411.00566 (only version: v1) is corrupt — 7 coordinates exceed 10 (up to 13) and the set contains a vanishing 5-subset. Both referees verified this, and that the n=3..9 witnesses all pass | "gave" -> "reported" + a footnote documenting the n=3..9 re-check, the corrupt n=10 list, and that the value is superseded by AlphaEvolve's verified C(10) >= 28 |
| 11 | Codex | "No bound for any n >= 13 has been published" literally false (Thiele's 4n and the asymptotic lower bounds are published bounds covering n = 13); same looseness in the abstract | Intro now "Beyond the general bounds above and the monotone consequence ... no published bound for any specific n >= 13"; abstract now "nothing specific to n = 13 has been published ... best previously known lower bound" |
| 12 | Codex | "Every number appearing in this note was recomputed..." overbroad (bibliographic numbers were not "recomputed"); same phrase recurred in Section 3 | Both now scoped to certificate- and run-derived numbers |
| 13 | Codex | "Four independent pilots ran in parallel (Table 2)" pointed only at the timeline table | Now cites Tables 2 and 3 |

## C. Flagged, deliberately NOT changed

1. **[AUTHOR] and [REPOSITORY/ARCHIVE URL] placeholders** (Codex defect):
   intentional pre-submission placeholders; must be filled before submission.
2. **"Codex, GPT-5.5" model label** (Codex flagged as unverifiable from the
   bundle alone): retained — the orchestration configuration on this machine
   pins the Codex MCP server to `gpt-5.5`, and the bundle's WRITEUP.md and
   PROBLEM.md record the same label. The author should confirm before
   submission.
3. **WRITEUP.md / PROBLEM.md stale snapshots** (bundle, not the note): the
   WRITEUP's blocker-repair counts (4068+1655+1031 / 20+23+43) are a mid-run
   harvest superseded by the final STATUS.json values used in the note (see
   BUILD.md caveat); PROBLEM.md mis-groups arXiv:2511.03526 under "Dong-Xu".
   The note is correct; the bundle files were left as historical records.

## D. Verdict

**SURVIVES.** Theorem 1.1 (C(13) >= 36) is fully machine-verified by four
independent implementations plus two fresh referee recomputations from the
note's own text; the certificate, its symmetry structure, the saturation
claims, the run-log numbers, and all citations now check out exactly as
stated. Codex's final line on the revision: "VERDICT: SURVIVES".
