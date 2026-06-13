# Refutation of Conjecture 4.6 of Zhi-Wei Sun, "Arithmetic properties of some permanents" (arXiv:2108.07723)

Gate-5 write-up, 2026-06-12. Bundle:
`C:\Users\jacks\source\repos\maths\problems\p2-factory\kills\sun-46\`
Canonical attack + clean-room artifacts (all code, logs, raw data):
`C:\Users\jacks\source\repos\maths\problems\p2-factory\attacks\sun-46\`

---

## Abstract (~120 words)

In *Arithmetic properties of some permanents* (arXiv:2108.07723), Zhi-Wei Sun
proved that s_n := (2^((n−1)/2)/√n)·per[sin(2πjk/n)]_{1≤j,k≤(n−1)/2} and
s′_p := (√p/2^((p−1)/2))·per[csc(2πjk/p)]_{1≤j,k≤(p−1)/2} are integers, and
conjectured (Conjecture 4.6) that (i) n | s_n for odd composite n, and (ii)
for odd primes, s_p < 0 ⟺ p ≡ 5 (mod 12) and s′_p < 0 ⟺ p ≡ 7 (mod 8). We
refute part (ii) — hence the conjecture as stated — at p = 29, the first
prime beyond Sun's published table: s_29 = 1053859 > 0 despite 29 ≡ 5
(mod 12), and s′_29 = −4806838304 < 0 despite 29 ≡ 5 (mod 8). Both values
are certified by four algorithmically independent exact methods plus
adversarial recomputation, and satisfy Sun's proven congruences mod 29. The
mod-12 clause fails again at p = 41, 53; the mod-8 clause at p = 61. Part (i)
survives all tests (all 15 odd composites n ≤ 65).

---

## Result (claim-standard form, FRAMEWORK.md §9)

> **Result.** Conjecture 4.6 of Zhi-Wei Sun, arXiv:2108.07723v7 (*Arithmetic
> properties of some permanents*, last revised 6 Jun 2022) — verbatim from
> the arXiv TeX source (`attacks/sun-46/paper.tex`, the conjecture
> environment at line 1109, sixth conjecture of Section 4 = "Conjecture 4.6"
> in the compiled PDF; numbering double-checked against the PDF and an
> independent PyMuPDF re-extraction):
>
> *"(i) If n>1 is odd and composite, then s_n ≡ 0 (mod n).*
> *(ii) Let p be an odd prime. Then s_p < 0 ⟺ p ≡ 5 (mod 12), and
> s′_p < 0 ⟺ p ≡ 7 (mod 8)."*
>
> with s_n, s′_p defined in the same paper's Theorem 1.6 (both proved there
> to be integers):
> s_n := (2^((n−1)/2)/√n)·per[sin(2πjk/n)]_{1≤j,k≤(n−1)/2} (odd n > 1),
> s′_p := (√p/2^((p−1)/2))·per[csc(2πjk/p)]_{1≤j,k≤(p−1)/2} (odd prime p) —
> is **FALSE**. Part (ii) fails at p = 29 on **both** iff clauses
> simultaneously: s_29 = 1 053 859 > 0 although 29 ≡ 5 (mod 12) (the ⟸
> direction of the first clause demands s_29 < 0), and
> s′_29 = −4 806 838 304 < 0 although 29 ≡ 5 (mod 8) ≢ 7 (the ⟹ direction
> of the second clause demands s′_29 ≥ 0; in fact s′_29 > 0 would follow,
> since the proven congruence s′_p ≡ 1 (mod p) excludes 0). Since the
> conjecture is the conjunction of (i) and (ii), Conjecture 4.6 as stated is
> false. Further failures: s_41 = 5 574 476 521 > 0 and
> s_53 = 1 540 679 755 916 971 > 0 (both ≡ 5 mod 12), and
> s′_61 = −2 904 784 276 786 469 053 142 518 062 479 < 0 (61 ≡ 5 mod 8).
> Part (i) was tested and **not** refuted (see "What this does not show").
>
> **Status before this work.** Open. Posed in arXiv:2108.07723 (v1
> 2021-08-17; statement unchanged through v7, 2022-06-06, still the latest
> version as of 2026-06-12; no journal reference on arXiv). Sun's published
> data (Remark 1.6) stop at p = 23 / n = 23. OEIS contains neither sequence
> (rechecked via the OEIS JSON API 2026-06-12: zero results for both
> signatures), so no public extension of the data existed. Citation scans
> (selection-time 2026-06-11, again 2026-06-12) found no proof, refutation,
> or correction; the nearest hits resolve *different* Sun conjectures
> (determinants, not permanents — see "Final kill-check").
>
> **Artifact.** `kill-certificate.json` (attack side; also at
> `attacks/sun-46/kill-certificate.json`): exact integer values of s_p and
> s′_p for all primes 29 ≤ p ≤ 61 and of s_n for all 15 odd composites
> n ≤ 65, the five violated instances with the clause each violates, and
> the verification provenance of every value.
> `verification-certificate.json` (clean-room side; also at
> `attacks/sun-46/independent/verification-certificate.json`).
>
> **Verification.** Two clean-room methods written from scratch by an
> independent verifier agent (no code or algorithm shared with the attack):
> Layer 1 — `independent/independent_checker.py`, exact integer arithmetic
> in Z[x]/(x^(4n)−1) ≅ Z-span of ζ_4n powers; Ryser permanent via
> Kronecker-substitution big integers with rigorous a-priori digit bounds;
> √n realized as the quadratic Gauss sum (sign pinned by Gauss's theorem);
> the integer **solved** from per(M) ≡ s_n·i^m·√n mod Φ_4n(x); no floats, no
> finite fields, no CRT. Layer 2 — `independent/crt_verify.py` +
> `perm_modq.c` (own C, plain uint128, OpenMP; fresh random primes in
> [2^60, 2^61), seed 20260611, disjoint from the attack's 59-bit primes),
> with exact-rational magnitude bounds and prod(q) > 4·bound, giving a CRT
> **uniqueness proof** of all 38 claimed integers: "ALL PROVED EXACT", zero
> mismatches (`crt_full_stdout.log`). Layer 1 reproduced all 19 of Sun's
> published values (including all four negatives) before touching any
> claim; Layer 2 validated on Sun ground truth (s_17, s_23, s′_17, s′_23)
> first. Attack side (three more independent methods): CRT/finite-field
> Gray-code Ryser in C (`driver.py` + `ryser_mod.c`, held-out-prime check
> per value), mpmath 60-digit Glynn (`checker.py`), and a 2026-06-12
> fourth exact layer (`mycheck_2026-06-12.py`: pure-Python subset-DP
> permanent — not Ryser, not Glynn — fresh 57-bit primes, rigorous bounds,
> held-out primes; re-run fresh for this Gate-5 pass, log
> `gate5_rerun_mycheck_2026-06-12.log`). Codex (GPT-5.5, hostile-referee
> framing, full access) audited the statement reading, both clean-room
> layers, and the 2026-06-12 layer line by line, recomputed the kill pair
> itself at 100–120-digit precision by both Glynn and Ryser (errors
> ~1e-89…1e-112), and returned "kill VALID, verification SOUND" / "KILL
> STANDS" in three separate audits. Every computed s_p, s′_p satisfies
> Sun's *proven* Theorem 1.6(iii) congruences s_p ≡ (−1)^((p+1)/2),
> s′_p ≡ 1 (mod p).
>
> **Openness re-check.** 2026-06-12, this session (queries and results in
> "Final kill-check" below): no prior or concurrent resolution found.
>
> **What this does not show.** See final section — in particular, part (i)
> is *not* refuted.

---

## Exact statement and provenance

* **Source:** Zhi-Wei Sun, *Arithmetic properties of some permanents*,
  arXiv:2108.07723. Versions v1 (2021-08-17) … v7 (2022-06-06); v7 is still
  the latest as of 2026-06-12 (live arXiv abs page re-checked). PDF and TeX
  source frozen in `attacks/sun-46/` (`sun-permanents.pdf`, `paper.tex`);
  the verifier agent independently re-extracted the PDF text
  (`independent/pdf_extract_independent.txt`).
* **Definitions** (Theorem 1.6, proved in the paper), verbatim TeX:

  ```tex
  s_n := \frac{2^{(n-1)/2}}{\sqrt n}\,
         \mathrm{per}\left[\sin 2\pi\frac{jk}{n}\right]_{1\le j,k\le(n-1)/2} \in \mathbb Z
         \quad (n>1 \text{ odd}),
  s'_p := \frac{\sqrt p}{2^{(p-1)/2}}\,
         \mathrm{per}\left[\csc 2\pi\frac{jk}{p}\right]_{1\le j,k\le(p-1)/2} \in \mathbb Z
         \quad (p \text{ odd prime}).
  ```

  (The paper's TeX has a typo `s_p'=:` for the csc case; the intended `:=`
  reading is unambiguous from the surrounding theorem and was confirmed in
  the Codex audit.) Theorem 1.6(iii) — also proved — gives
  s_p ≡ (−1)^((p+1)/2) (mod p) and s′_p ≡ 1 (mod p), which we use as a
  consistency check on every computed value.
* **Conjecture 4.6**, verbatim TeX from `paper.tex` (line 1109; introduced
  by "Motivated by Theorem \ref{Th-sin} and Remark \ref{Rem-sin}, we pose
  the following conjecture."):

  ```tex
  \begin{conjecture} {\rm (i)} If $n>1$ is odd and composite, then $s_n\eq0\pmod n$.

  {\rm (ii)} Let $p$ be an odd prime. Then
  $$s_p<0\iff p\eq5\pmod{12},$$
   and $$s_p'<0\iff p\eq7\pmod8.$$
  \end{conjecture}
  ```

  The TeX conjecture environments are unnumbered; this is the sixth
  conjecture environment of Section 4, hence "Conjecture 4.6" in the
  compiled paper — confirmed independently against the compiled PDF by the
  attacker, the clean-room verifier, and Codex.
* **Disambiguation.** Not to be confused with (a) Conjecture 4.7 of the
  *same* paper (the analogous statement for tan/cot permanents t_n, t′_p —
  untouched here), or (b) "Conjecture 4.6" of *other* Sun papers: the 2026
  paper arXiv:2605.19502 resolves conjectures 4.6/4.7 of a *different* 2024
  Sun paper (flagged as a trap at harvest time; re-confirmed 2026-06-11 and
  2026-06-12).
* **Grounding data.** Sun's Remark 1.6 publishes s_3…s_23 (11 values) and
  s′_3…s′_23 (8 values), including four negatives (s_5, s_17, s′_7,
  s′_23). Every layer of this kill reproduced all 19 before computing
  anything new — this is what pins the sign conventions end-to-end.

## The counterexample (p = 29)

p = 29 is the **first prime beyond Sun's published table**. Residues:
29 ≡ 5 (mod 12) and 29 ≡ 5 (mod 8).

| quantity | exact value | conjecture demands | actual | clause violated |
|---|---|---|---|---|
| s_29  | **1 053 859** | < 0 (since 29 ≡ 5 mod 12) | > 0 | s_p < 0 ⟸ p ≡ 5 (mod 12) |
| s′_29 | **−4 806 838 304** | ≥ 0 (since 29 ≡ 5 mod 8, ≢ 7) | < 0 | s′_p < 0 ⟹ p ≡ 7 (mod 8) |

Both violations are sign violations of nonzero integers — no boundary or
strictness subtlety exists. Consistency with the *proved* part of the paper:
s_29 ≡ 28 ≡ (−1)^15 (mod 29) and s′_29 ≡ 1 (mod 29), exactly as Theorem
1.6(iii) requires; the kill values pass the only theorem available to test
them against.

**Supplementary counterexamples** (each independently sufficient to kill the
clause named):

| p | residues | value | violated clause |
|---|---|---|---|
| 41 | 41 ≡ 5 (mod 12) | s_41 = 5 574 476 521 > 0 | mod-12 (⟸) |
| 53 | 53 ≡ 5 (mod 12) | s_53 = 1 540 679 755 916 971 > 0 | mod-12 (⟸) |
| 61 | 61 ≡ 5 (mod 8) | s′_61 = −2 904 784 276 786 469 053 142 518 062 479 < 0 | mod-8 (⟹) |

**Full computed data** (all exact; `kill-certificate.json` →
`full_data`, raw in `attacks/sun-46/results.json`):

s_p for p = 29…61:
1053859 (29), 10542977 (31), 1519663259 (37), 5574476521 (41),
453435884081 (43), 4570760060257 (47), 1540679755916971 (53),
493044351638203633 (59), 3864901746617921299 (61).

s′_p for p = 29…61:
−4806838304 (29), −1518806869720 (31), 43041655439377 (37),
88188655594502880 (41), 7817331967711147274 (43),
−208210243110377949730 (47), 1364915376262405923148317 (53),
7313054784852201235037895089487 (59),
−2904784276786469053142518062479 (61).

s_n for the 15 odd composites n ≤ 65 (part (i) test set):
9 (9), 45 (15), 2835 (21), 63125 (25), 59049 (27), −1643895 (33),
334186125 (35), 9154298673 (39), 696741294375 (45), 3078195713761 (49),
113109498706113 (51), 9553828212328125 (55), 89237136634668369 (57),
14357464732984700313 (63), 23595726326056828125 (65).
**n | s_n holds in every one of these 15 cases.**

**Why Sun's pattern broke.** Each sign "law" of part (ii) was fitted on
eight primes with only two negatives each (s: p = 5, 17; s′: p = 7, 23). In
the extended range every s_p for 29 ≤ p ≤ 61 is positive — the mod-12 law
fails at *every* tested prime ≡ 5 (mod 12) beyond the published table (29,
41, 53) — and negative s′_p occur at p = 29, 31, 47, 61, breaking the mod-8
law at 29 and 61 while 31 and 47 happen to conform. The conjectured laws
appear to be small-sample artifacts; permanents (unlike the determinants
Sun treats elsewhere) carry no Galois equivariance that could enforce such
a residue-class sign rule.

## Verification

Six layers, four of them exact, sharing no code; the permanent is computed
by three distinct algorithm families across five independent
implementations (Ryser: Gray-code Montgomery C, Kronecker-bigint Python,
plain-uint128 C; Glynn: mpmath; subset-DP: pure Python). All paths below
are relative to `attacks/sun-46/`.

**Clean-room layer 1 — exact cyclotomic, no floats, no finite fields, no
CRT** (`independent/independent_checker.py`; logs
`independent_checker.log`, `full_run_stdout.log`, `sprime_kill_stdout.log`).
Works in Z[x]/(x^(4n)−1) with x ↦ ζ_4n: sin entries as ζ^(4jk) − ζ^(−4jk)
over 2i, csc entries inverted exactly mod Φ_4n via Fraction extended Euclid
(each inverse re-verified by exact back-multiplication), √n as the
quadratic Gauss sum with sign fixed by Gauss's theorem, permanent by Ryser
over Kronecker-substitution big-integer pairs with rigorous a-priori L1
digit bounds and decode/re-encode integrity asserts. The integer is
**solved** from per(M) ≡ t·i^m·√n (mod Φ_4n(x)) — the checker computes
s_n itself rather than verifying a claimed value. Self-tested against
brute-force permutation-sum permanents (n ≤ 17) and float64 Ryser.
Reproduced all 19 published values, then s_29 = 1053859 (268 s) and
s′_29 = −4806838304 (402 s) exactly.

**Clean-room layer 2 — CRT uniqueness proof over fresh primes**
(`independent/crt_verify.py` + `independent/perm_modq.c`; logs
`crt_verify.log`, `crt_full_stdout.log`, results
`crt_verify_results.json`). Own C permanent (plain __uint128 mulmod,
OpenMP — not derived from the attack's Montgomery code), random primes
q ≡ 1 (mod 4n) in [2^60, 2^61) from an own Miller-Rabin (seed 20260611,
disjoint from the attack's primes), Gauss-sum image asserted to satisfy
g² ≡ n (mod q), and **rigorous** exact-rational magnitude bounds (chord
inequality |sin πx| ≥ 2·dist(x, Z) for csc rows) with prod(q) > 4·bound —
so agreement mod prod(q) *proves* each integer exactly, it does not just
spot-check it. Validated on Sun's ground truth first; then certified all
38 claimed values (kill pair + every s_n, odd n ≤ 65 + every s′_p,
p ≤ 61): "OVERALL: ALL PROVED EXACT (1336s)", zero mismatches.

**Attack layers (independent of the above, three distinct methods):**
(1) `driver.py` + `ryser_mod.c` — CRT/finite-field Gray-code Ryser in C
(Montgomery arithmetic, OpenMP), 59-bit primes, conservative magnitude
bounds, plus a held-out extra prime per value; (2) `checker.py` — Glynn's
formula (different permanent algorithm), pure Python + mpmath at 60 digits,
entries direct from `mpmath.sin`: agrees with the exact values to < 1e−15
on the kill pair and (s_41, s′_41) (`checker_big.log`); (3)
`mycheck_2026-06-12.py` — fourth exact layer from the re-verification
session: subset-DP permanent (f[S] = Σ_{j∈S} A[|S|−1][j]·f[S∖{j}] — not
Ryser, not Glynn), fresh 57-bit primes, own Miller-Rabin, rigorous
CRT-uniqueness bounds, held-out prime per value; reproduces all 19
published values, the kill pair, and s_41 (`mycheck_2026-06-12.log`;
fresh Gate-5 re-run 2026-06-12: `gate5_rerun_mycheck_2026-06-12.log` in
this bundle, byte-identical to the original log, exit 0).

**Adversarial audits (Codex, GPT-5.5 xhigh, hostile-referee framing, full
shell access).** Three rounds across 2026-06-11/12: probed the statement
reading (permanent vs determinant, half-range indices, 2πjk/n argument,
conjecture numbering, the `=:` typo, confusion traps with other Sun
papers), the global-sign-flip hole (closed by Sun's four published
negatives), both clean-room layers' mathematics (Gauss-sum signs for
n ≡ 1, 3 mod 4, Kronecker digit-overflow bounds, the Φ_4n-root argument,
CRT-uniqueness logic), and `mycheck_2026-06-12.py` line by line (DP
recurrence brute-checked to m = 6). Independently recomputed
s_29 = 1053859, s′_29 = −4806838304, s_41 = 5574476521 at 100–120-digit
precision by both Glynn and Ryser (errors ~1e−89…1e−112). Verdicts: "kill
VALID, verification SOUND"; "KILL STANDS" (both rounds of the 2026-06-12
audit; thread 019eba3a-b136-7dd2-bb7b-a5df569b6ff3).

**Cross-cutting checks.** Sun's proven congruences hold on every computed
value; Sun's published values reproduced by every layer before it computed
anything new; held-out-prime agreement on every CRT-based value; the three
CRT-based layers use disjoint prime sets (59-bit attack, 60–61-bit
clean-room, 57-bit re-verification) and pairwise independent
implementations.

## How to verify

Quick orientation (~1 s, stdlib only — float sanity, not the proof):

```
cd problems\p2-factory\kills\sun-46
python snippet_check.py
# expect:  -239 -6 -7094142
#          1053859 -4806838304
```

(`snippet_check.py` reproduces three of Sun's published values — all
negatives: s_17, s′_7, s′_23 — first, validating the sign conventions, then
the kill pair. Run fresh 2026-06-12, exit 0.)

Exact verification (pure Python, no dependencies; ~75 s on this machine):

```
cd problems\p2-factory\attacks\sun-46
python mycheck_2026-06-12.py
# expect: "all 19 reproduced exactly.", s_29 = 1053859, s'_29 = -4806838304,
#         both clauses "-> VIOLATED", s_41 = 5574476521, final VERDICT lines;
#         any failure raises AssertionError (exit != 0)
```

Clean-room layers (heavier): `independent/independent_checker.py` (exact
cyclotomic; kill pair in ~11 min) and `independent/crt_verify.py` (needs
WSL + gcc for `perm_modq.c`; certifies all 38 values, ~22 min). Logs of
the original runs are preserved next to each script.

## Final kill-check (Gate-5, dated 2026-06-12)

Searches run this session, after verification, looking for any prior or
concurrent resolution of Conjecture 4.6 of arXiv:2108.07723:

1. Web search `Sun "arithmetic properties of some permanents" conjecture
   4.6 counterexample refuted` → the paper itself, citing papers from 2022
   (2109.11506, 2206.02592, 2206.05021, 2208.12167 — identities /
   *other* conjectures), generic permanent literature. **Nothing.**
2. Web search `Zhi-Wei Sun permanent sin csc conjecture s_p sign p mod 12
   refutation 2026` → nearest hit arXiv:2512.24012 (Gao–Guo, Dec 2025),
   examined below. **Nothing on 4.6.**
3. arXiv abs page 2108.07723 fetched live → still **v7 (2022-06-06)**, no
   journal reference, no comment about resolved conjectures.
4. arXiv:2512.24012 (*Integrality of a trigonometric determinant arising
   from a conjecture of Sun*) — full PDF downloaded and machine-scanned:
   resolves a csc **determinant** conjecture (Sun's c_p, det not per);
   zero occurrences of "permanent", "s_n", or "2108.07723". Adjacent but
   distinct. **Not a resolution.**
5. arXiv:2206.02592 (eigenvector-eigenvalue identity / Sun conjectures) —
   abstract checked: proves a **2018** Sun conjecture; predates and does
   not touch the 2021 permanents paper's 4.6. **Not a resolution.**
6. Web search `"2108.07723" cited 2025 OR 2026 conjecture permanent proof`
   → only 2022-era citing papers. **Nothing.**
7. Web search `arXiv 2026 Sun conjecture permanent "p ≡ 5 (mod 12)" sign`
   → arXiv:1812.08080 (Jacobi-symbol determinants, 2020, unrelated).
   **Nothing.**
8. OEIS JSON API, both signatures
   (`1,-1,1,9,1,51,45,-239,913,2835,12145` and
   `1,1,-6,111,261,6784,245101,-7094142`) → **0 results each**; the
   sequences are still not in OEIS, and no public extension of Sun's
   table was found anywhere.
9. Web search `"conjecture 4.6" Sun permanent 2026 refute OR disprove OR
   counterexample arXiv` → unrelated quantum-channel counterexample paper;
   nothing on this conjecture. **Nothing.**
10. arXiv math.NT recent listing scanned → no papers on trigonometric
    permanents or Sun permanent conjectures. **Nothing.**

Also standing from 2026-06-11 (attack + clean-room sessions): OEIS rejects
both sequences; Codex prior-art search found no refutation; the
arXiv:2605.19502 trap (resolves "Conjecture 4.6/4.7" of a *different* 2024
Sun paper) re-confirmed not to apply. **Conclusion: no prior or concurrent
resolution found. The kill stands as of 2026-06-12.**

## What this does not show

* **Part (i) is NOT refuted.** It *was* tested, honestly and exactly:
  n | s_n was verified for **all 15 odd composite n ≤ 65** (values above;
  exact layer for 9–27, CRT-proof layer for 33–65), including the
  mechanism-motivated targets 25, 35, 49, 55, 65 coprime to 3 and the
  prime squares 25, 49. The divisibility held **every time**. Part (i)
  therefore survives this attack unrefuted, looks genuinely plausible, and
  remains **open**. Our refutation of the conjunction rests entirely on
  part (ii). A proof (or deeper test) of part (i) would be a separate
  contribution.
* **No replacement sign law is claimed.** The observed pattern (all s_p > 0
  for 29 ≤ p ≤ 61; s′_p < 0 at p = 29, 31, 47, 61) is a description of the
  computed range, not a conjecture we endorse.
* **Finite range.** Values are certified exactly for p ≤ 61 (and odd
  composite n ≤ 65) only. Nothing is claimed beyond that range.
* **Provenance note on supplementary values.** The kill needs only p = 29
  (verified by all four exact layers *and* three independent
  float/high-precision recomputations). Backup counterexample p = 41 has
  the same coverage except clean-room layer 1, which computed only the
  kill pair and small composites exactly (p = 41 is covered by the other
  three exact layers plus the float layers and Codex's 100-digit
  recomputation). The supplementary values s_53 and s′_61 rest on
  two independent exact CRT layers (attack 59-bit primes; clean-room
  60–61-bit primes, disjoint sets, rigorous uniqueness bounds, held-out
  primes) but were not float-recomputed in the 2026-06-12 audit — a
  provenance asymmetry, not a doubt.
* **Nothing is claimed about Conjecture 4.7** (tan/cot permanents) or any
  other conjecture of arXiv:2108.07723, nor about the determinant analogues
  treated in the Gao–Guo line of work.
* The "first prime beyond Sun's table" framing is about Sun's *published*
  data; whether Sun privately computed further is unknowable from the
  paper.

## Publication grouping

Standalone number-theory kill — the only one of this campaign's kills in
number theory (the others are graph-theoretic or group-theoretic). Natural
venue: a
short note ("The sign pattern of Sun's trigonometric permanents s_p, s′_p
and a counterexample to his Conjecture 4.6"), citing arXiv:2108.07723 and
reporting the table for 29 ≤ p ≤ 61 plus the part-(i) evidence — the
extended table (30 new exact values of 2^m-time trigonometric permanents,
matrices up to 32×32) has independent data value since neither sequence is
in OEIS.
