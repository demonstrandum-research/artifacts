# Referee report and responses — `papers/sun-46/note.tex`

Hostile-referee pass 2, 2026-06-12. Referee: Claude (independent of the
drafting session), with Codex (GPT-5.5, hostile framing, full file access)
as second referee (thread `019ebb32-26d3-7253-ac28-486b79691413`). Every
finding below was fixed in `note.tex` in this session; the PDF was rebuilt
(6 pages, zero overfull/underfull boxes).

## What the referee verified independently (not taken from the bundle)

1. **Every number recomputed.** A fresh pipeline written for this pass
   (`referee/ref_perm_modq.c` — OpenMP Montgomery Gray-code Ryser permanent
   mod q, no code shared with any bundle program; `referee/ref_check.py`)
   recomputed all 52 integers in the note's three tables via the cyclotomic
   identity of Lemma 3.1 (re-derived by hand by both referees), evaluated
   in F_q at verified roots of exact order 4n, for fresh random primes in
   [2^61, 2^62) (seed 20260612 — disjoint by construction from the
   bundle's 57-bit, 59-bit, and [2^60, 2^61) prime sets), with rigorous
   magnitude bounds (exact `Fraction` chord bound for csc), prod(q) > 4B
   CRT-uniqueness reconstruction, and one extra held-out prime per value.
   The expected values were transcribed from `note.tex` itself, so any
   transcription error in the note would have surfaced. **All 52 match
   exactly.** The kernel was self-tested against brute-force permutation
   sums (m ≤ 7) and an independent pure-Python Ryser (m = 10, 13). Logs:
   `referee/ref_check_2026-06-12.log` (~7 min wall clock; the one FAIL
   line is the referee's own audit check that exposed finding R3) and,
   after the revisions, `referee/ref_check_rev2_2026-06-12.log` — the
   full recomputation re-run against the corrected claims, final line
   `REFEREE: ALL CHECKS PASS` (exit 0).
2. **Every numerical side-claim audited** (same log): the nine primes and
   fifteen odd composites are exactly the claimed sets; Table 1's mod-12 /
   mod-8 residue columns and the "violates" column recomputed from the
   values; Table 2's quotients s_n/n; Sun's proven congruences
   s_p ≡ (−1)^((p+1)/2), s'_p ≡ 1 (mod p) on every prime value in the
   note; the kill-pair residues "s_29 ≡ 28, s'_29 ≡ 1 (mod 29)" as quoted;
   the sign-pattern claims of the remarks (all s_p > 0 for 29 ≤ p ≤ 61;
   negative s'_p exactly at {29, 31, 47, 61}; Sun-table negatives exactly
   {s_5, s_17, s'_7, s'_23}); "values grow to 31 digits" (max digit count
   is exactly 31, at s'_59); "m up to 32"; "thirty new exact values";
   "nineteen"/"eight primes" counts; |s_n| ≤ 2^m m! for every sin value.
3. **Statement provenance re-checked** against the frozen
   `attacks/sun-46/paper.tex` and the independent PDF text extraction:
   verbatim conjecture text, Theorem 1.6(i)–(iii) including the `s_p'=:`
   typo, Remark 1.6's nineteen values, and the numbering (the paper's
   conjecture environments all sit in Section 4 and are displayed
   section-prefixed; the sixth is "Conjecture 4.6" in the compiled PDF).
4. **All five citations fetched live** (2026-06-12): Sun arXiv:2108.07723
   still v7 (2022-06-06), no journal ref; Gao–Guo arXiv:2512.24012 (title,
   authors Liwen Gao / Xuejun Guo, 30 Dec 2025 — and see R1); Glynn,
   Eur. J. Combin. 31 (2010) 1887–1891 (DOI 10.1016/j.ejc.2010.01.010);
   Ryser, Carus Mathematical Monographs 14, MAA 1963; Berndt–Evans–
   Williams, CMS Series of Monographs and Advanced Texts **21**, Wiley
   1998 — and "Thm. 1.5.2" is confirmed as the classical quadratic
   Gauss-sum evaluation via an independent source citing it as such
   (Strömberg, arXiv:1108.0202, Lemma 3.5 cites [BEW, Prop. 1.5.3 and
   Thm. 1.5.2] for exactly this statement).
5. **OEIS re-checked** via the JSON API with a positive control
   (Fibonacci): both signatures still return zero results.
6. **Bundle reproducibility re-run**: `snippet_check.py` (expected output,
   ~1 s), `mycheck_2026-06-12.py` (exit 0 — in 3.6 s, see R9), extended
   `_recompute_sun46.py` (ALL NOTE CHECKS PASS).

## Findings and resolutions

| # | Severity | Finding | Resolution in note.tex |
|---|----------|---------|------------------------|
| R1 | **Substantive (citation)** | The intro said Gao–Guo (arXiv:2512.24012) "resolve a conjecture of Sun on a trigonometric **csc**-determinant". The paper actually proves Sun's **sec**-determinant conjecture (its Conjecture 1.1, D(p) = det[sec 2πjk/p]); the csc case (c_p, its Conjecture 1.2) was resolved in the authors' *earlier* paper (their ref. [2]). Verified directly from the PDF text. | "…resolve a conjecture of Sun on a trigonometric $\sec$-determinant (the $\csc$ analogue having been settled in earlier work of the same authors, cited there)." |
| R2 | **Substantive (math, found by Codex)** | Remark "Why the pattern broke" claimed "the permanent is not an eigenvector of the action of Gal(Q(ζ_p)/Q)". False: σ_a multiplies per M by the Legendre symbol (a/p) — this computation appears verbatim in Sun's proof of Theorem 1.6 (it is *why* s_p is an integer), and follows from column permutation + sign flips + Gauss's lemma. | Sentence replaced: Galois equivariance does not distinguish permanent from determinant (the permanent *is* a Galois eigenvector); what the determinant analogues additionally possess is a character factorization (into character sums / Dirichlet L-values in Gao–Guo), which is the kind of mechanism that can force residue-class behaviour; no analogous factorization is known for the permanent. |
| R3 | Minor (accuracy) | "including the prime squares 25, 49" — 9 = 3² is also a prime square in the test set (caught by the referee's exhaustiveness audit). | "the prime squares $9$, $25$, $49$". |
| R4 | Minor (overclaim) | Abstract: "Every value is certified exactly, by at least two independently written programs, via a cyclotomic identity evaluated in two ways: big-integer …, and finite-field …" reads as if each value got *both* routes; only the kill pair and the small cases got the big-integer route. Same implication in the intro's methods paragraph. Also "every new value satisfies his proven congruences" — the congruences are proven for primes only. | Abstract: "at least two of four independently written exact programs … big-integer arithmetic in Z[x]/(x^{4n}−1) (the counterexample pair, among others), and finite-field specialization with a CRT uniqueness proof (every value)"; "every new **prime** value satisfies his proven congruences". Intro: routes annotated "(for the counterexample pair and the small cases)" / "(for every value)". |
| R5 | Minor (over-attribution) | §3 said "Each value was additionally confirmed at a held-out prime…" then introduced the three CRT programs, implying all three use held-out primes; §4 said "the CRT layers verified every value at a held-out prime". In fact `driver.py` (every value) and `mycheck_2026-06-12.py` (its values) use held-out primes; the clean-room `crt_verify.py` proves uniqueness by prod(q) > 4B with **no** held-out prime (verified in source). | Held-out checks now attributed per program in §3; §4 now reads "the first and third CRT programs confirmed each of their values — between them, every value in this note — at a held-out prime". |
| R6 | Minor (over-attribution, found by Codex) | §3 described B as "a rigorous bound … evaluated in exact rational arithmetic" for all three CRT programs; `driver.py`'s bound is a padded floating-point bound (log-domain, +0.05/+0.1/+10 slack), not exact-rational. | Bound provenance now stated per program: first program "generously padded floating-point bounds" + held-out primes; second and third "exact rational arithmetic"; the uniqueness statement now says "provided B itself is rigorous". (Every value retains at least one exact-rational-bound certification: crt_verify covers the kill pair and everything ≥ 31, mycheck the calibration set + kill pair + s_41, implementation A — no bounds needed — the small composites; the referee's own run adds a second for all 52.) |
| R7 | Minor (scope, found by Codex) | AI-disclosure paragraph: "independently recomputed the headline values at 100–120-digit precision" could be read to include s_53/s'_61, contradicting the §4 footnote (those were not part of the 100-digit audit). | Now "recomputed the kill pair $(s_{29}, s'_{29})$ and $s_{41}$ at 100–120-digit precision" (also defines "kill pair" at first use). |
| R8 | Nit (accuracy) | "delivers s_29 in about four minutes" — the log says 268.4 s; "a 40-line floating-point script" — `snippet_check.py` is 47 lines. | "about four and a half minutes"; "a one-page floating-point script". |
| R9 | Nit (stale timing) | "in about 75 seconds" for the pure-Python exact reproduction — two fresh measurements today (referee: 3.6 s; Codex: 3.34 s) show it runs in seconds; the 75 s figure was stale (measured under load). | "in under a minute" (robust under any machine load); BUILD.md updated with the measurement. |
| R10 | Nit (claim/artifact sync) | "recomputed … all entries with m ≤ 18 (s_p, s'_p for p=29,31,37; s_n for n=25,27,33,35)" — Table 2's n = 9, 15, 21 and the nineteen calibration entries also have m ≤ 18 but were not covered by `_recompute_sun46.py`. | `_recompute_sun46.py` part B extended to all nineteen calibration values (re-run: ALL NOTE CHECKS PASS); note now says "every table entry with m ≤ 18 (all nineteen calibration values; s_p, s'_p for p=29,31,37; s_n for n=25,27,33,35)". |
| R11 | Minor (consistency, Codex round 2) | After R6, the AI-disclosure sentence "All accept paths use exact integer arithmetic; floating point appears only in advisory cross-checks" contradicted the newly disclosed padded floating-point bounds of the first CRT program. | Sentence now: accept paths run on exact integer and finite-field arithmetic; floating point appears only in advisory cross-checks and in one CRT program's padded magnitude bounds — and every value is also certified by a layer with exact-rational bounds or needing no magnitude bound (coverage verified: s_25/s_27 by implementation A; calibration by mycheck + A; kill pair and all values ≥ 31 by crt_verify; s_41 also by mycheck). |
| R12 | Minor (overclaim, Codex round 2) | Abstract/intro "finite-field specialization with a CRT uniqueness proof (every value)" — for s_25/s_27 the only finite-field cover is the padded-float-bound program, so the *rigorous* CRT-uniqueness claim did not extend to literally every value. | "(every value)" removed; abstract and intro now claim CRT uniqueness proofs as a route, with per-value certification carried by the "at least two of four exact programs" sentence. |

Checked and found **correct** (no change): all 52 table values; both
identities of Lemma 3.1 and its proof (both referees re-derived it,
including the Z[ζ]-integrality of U and the Gauss-sum normalization
G̃ = ζ^{-n}G for n ≡ 3 (mod 4)); the finite-field protocol of §3 (order-4n
root ⇒ root of Φ_4n; g² ≡ n assert; B = x^{nm}G̃(x)); the description of
implementation A against its source (Kronecker packing, L¹ digit bound,
decode/re-encode asserts, solve-for-t, Φ by exact division, extended
Euclid + back-multiplication for U); the per-program prime-set claims
(59-bit / [2^60,2^61) / 57-bit, disjoint); the coverage footnote in §4
(verified against `results.json`, `crt_verify_results.json` — exactly the
32 values claimed — and the implementation-A and mycheck logs); the
calibration claims (three programs reproduce all nineteen; clean-room CRT
validated on {s_17, s_23, s'_17, s'_23}; Glynn on p = 17, 23 anchors);
the "22 minutes" (1336 s) and "about seven minutes" (402 s) timings; the
conjecture-numbering footnote; the `=:` typo footnote; the OEIS and
arXiv-v7 status claims; the 100–120-digit audit residual claim
("below 10^{-86}": the largest is ~4·10^{-87}).

## Verdict

**ACCEPT (after the revisions above, all implemented).** The mathematical
content — the counterexamples, Lemma 3.1, and the verification
architecture — survived two independent hostile recomputations and a
line-by-line claims audit. The remaining placeholders (`[AUTHOR]`,
`[REPOSITORY/ARCHIVE URL TO BE INSERTED]`) are intentional per the
commissioning spec and must be filled before submission; the archive
placeholder is load-bearing for a computational note and should be
resolved at submission time.

Codex round-1 verdict on the pre-revision text: **MINOR REVISIONS**
(findings R1–R2 and confirmations of R3–R9; "The counterexample and
Lemma 3.1 survive my attack. I would not reject on the mathematics or
the numbers."). Round 2, on the revised text, raised R11–R12 as the only
remaining must-fix items. Round 3, after those fixes: **"ACCEPT. … No
remaining must-fix items."** All listed revisions were implemented and
the note recompiled cleanly (6 pages, zero overfull/underfull boxes).
