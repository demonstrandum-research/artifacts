# Build instructions — `note.tex` / `note.pdf`

Short research note: *The sign pattern of Sun's trigonometric permanents and
a counterexample to his Conjecture 4.6* (disproof of Conjecture 4.6 of
Z.-W. Sun, arXiv:2108.07723; source bundle in
`problems/p2-factory/kills/sun-46/`, full attack + clean-room artifacts in
`problems/p2-factory/attacks/sun-46/`).

## Toolchain

Reuses the WSL Ubuntu TeX Live toolchain installed for the sibling note
`papers/graffiti-143-154/` (see that directory's BUILD.md for the one-time
install command). pdfTeX 3.141592653-2.6-1.40.28 (TeX Live 2025/Debian).
The *default* WSL distro on this machine is `docker-desktop`, so `-d Ubuntu`
is required on every `wsl` invocation. Packages used by `note.tex`:
`geometry`, `amsmath`/`amssymb`/`amsthm`, `booktabs`, `microtype`,
`hyperref`, `xurl`, and `lmodern` (required — `[T1]{fontenc}` + `microtype`
abort without scalable Latin Modern fonts). The bibliography is a manual
`thebibliography`; no BibTeX run is needed.

## Compile

From PowerShell (two passes for cross-references):

```powershell
cd C:\Users\jacks\source\repos\maths\papers\sun-46
wsl -d Ubuntu -- sh -c "cd /mnt/c/Users/jacks/source/repos/maths/papers/sun-46 && pdflatex -interaction=nonstopmode note.tex && pdflatex -interaction=nonstopmode note.tex"
```

Output: `note.pdf` (6 pages) in this directory. The build is clean of
overfull/underfull boxes (`grep -cE '^(Overfull|Underfull)' note.log`
returns 0).

## Verifying the numbers in the note

Every quantity in the note is reproducible from the kill bundle:

```powershell
# ~1 s float sanity (3 published negatives + the kill pair):
cd C:\Users\jacks\source\repos\maths\problems\p2-factory\kills\sun-46
python snippet_check.py            # expect: -239 -6 -7094142 / 1053859 -4806838304

# exact reproduction (all 19 published values, kill pair, s_41, with CRT
# uniqueness proofs; any failure raises AssertionError).  Runs in seconds
# on an idle machine (3.6 s measured 2026-06-12; the "~75 s" figure in an
# earlier revision of this file was measured under heavy load):
cd C:\Users\jacks\source\repos\maths\problems\p2-factory\attacks\sun-46
python mycheck_2026-06-12.py       # expect: "all 19 reproduced exactly." ... VERDICT lines
```

Both were re-run during preparation of this note (2026-06-12; the mycheck
output was byte-identical to `gate5_rerun_mycheck_2026-06-12.log` in the
kill bundle, exit 0). The heavier clean-room layers
(`attacks/sun-46/independent/independent_checker.py`, exact cyclotomic,
kill pair in ~11 min; `independent/crt_verify.py` + `perm_modq.c`, WSL +
gcc, 32-value CRT uniqueness certification in ~22 min) were not re-run for
the note; their original logs sit next to the scripts and the 32-entry run
is summarized in `independent/crt_full_stdout.log` ("OVERALL: ALL PROVED
EXACT (1336s)").

Headline and table numbers were additionally recomputed from scratch by the
helper script in this directory:

- `_recompute_sun46.py` — re-checks, from
  `attacks/sun-46/results.json`: Sun's proven congruences
  s_p ≡ (−1)^((p+1)/2), s′_p ≡ 1 (mod p) on all 18 new prime values; the
  part-(i) divisibility n | s_n and the quotients s_n/n for all 15 odd
  composites n ≤ 65; the residues mod 12 / mod 8 and the sign-violation
  bookkeeping of Table 1; and then *recomputes from scratch* (fresh numpy
  float64 Gray-code Ryser) every table entry with m = (n−1)/2 ≤ 18: all
  nineteen calibration values, s_p, s′_p for p = 29, 31, 37, and s_n for
  n = 25, 27, 33, 35 (the calibration entries were added in the second
  referee pass so the note's coverage claim is literally exhaustive). Run:
  `python _recompute_sun46.py` — expect final line `ALL NOTE CHECKS PASS`
  (exit 0). Re-run successfully 2026-06-12 (both before and after the
  extension).

Caveat (inherited from the sibling note's BUILD.md): do not run Python
scripts from `%TEMP%` on this machine — a stray `re.py` there shadows the
stdlib `re` module and breaks numpy imports.

## Referee pass

The note was refereed adversarially by Codex (GPT-5.5, hostile-referee
framing, full file access) on 2026-06-12 (thread
019ebb01-a97c-7923-8876-62cec09090cb). Round 1 found six substantive
issues (verification-coverage overclaims in the abstract/intro/proof/
cross-checks; an incorrect "five programs agree on every value" claim; an
incorrect "every program reproduced all nineteen" calibration claim; a
wrong Gauss-sum normalization formula B = x^{nm} G(x), valid only for
n ≡ 1 (mod 4); an overstated exact-algorithm-diversity count; and a false
footnote claiming Sun's conjecture environments are unnumbered) — all
fixed in revision; all three data tables, Lemma 3.1, the verbatim quotes,
and all five references were checked clean in both rounds. Round 2
verdict: **ACCEPT**.

All five bibliography entries were fetched and verified live on 2026-06-12
(arXiv abs pages for 2108.07723 and 2512.24012; publisher/index records
for Berndt–Evans–Williams 1998, Glynn EJC 31 (2010) 1887–1891, and Ryser,
Carus Monograph 14, MAA 1963).

## Referee pass 2 (hostile re-verification, 2026-06-12)

A second, independent hostile-referee pass re-verified the note from
scratch; full report and point-by-point responses in `RESPONSES.md`.

* **Recomputation.** All 52 integers in the note's three tables (19
  calibration, 18 new prime values, 15 composites) were recomputed by a
  freshly written pipeline in `referee/` (`ref_perm_modq.c`, an OpenMP
  Montgomery Gray-code Ryser kernel sharing no code with the bundle;
  `ref_check.py`, fresh random primes in [2^61, 2^62), seed 20260612 —
  disjoint from all three bundle prime sets — rigorous bounds,
  prod(q) > 4B CRT-uniqueness reconstruction, one held-out prime per
  value). All 52 match exactly; every numerical side-claim of the note
  (residues, quotients, congruences, sign sets, digit counts, set
  cardinalities) was audited and passes. Logs:
  `referee/ref_check_2026-06-12.log` (pre-revision run; its single FAIL
  line is the referee's own audit check that exposed the prime-squares
  wording fix below) and `referee/ref_check_rev2_2026-06-12.log`
  (post-revision re-run against the corrected claims: final line
  `REFEREE: ALL CHECKS PASS`, exit 0). Total runtime ≈ 7 min per run.
* **Citations.** All five references re-fetched live. One substantive
  error found and fixed: arXiv:2512.24012 (Gao–Guo) proves Sun's
  *sec*-determinant conjecture (its Conjecture 1.1); the *csc* case
  (c_p, its Conjecture 1.2) was resolved in the authors' earlier paper.
  The note had said "csc-determinant".
* **Codex second referee** (GPT-5.5, hostile framing, thread
  019ebb32-26d3-7253-ac28-486b79691413; three rounds, final verdict
  **ACCEPT, "no remaining must-fix items"**): round 1 MINOR REVISIONS, no
  mathematical errors in Lemma 3.1 or the protocol; confirmed the
  citation fix and found two further substantive issues, both fixed:
  the Galois-equivariance sentence in the "Why the pattern broke" remark
  was false as stated (the permanent *is* a Galois eigenvector — Sun's
  own integrality proof shows σ_a multiplies per M by (a/p); the remark
  now makes the correct factorization-based point), and the blanket
  "rigorous bound" description of the CRT programs over-attributed exact
  rational bounds to `driver.py` (which uses padded floating-point
  bounds plus held-out primes; now attributed per program).
* **Smaller fixes** (all verified against bundle logs): abstract no
  longer implies every value got both evaluation routes, and says "every
  new *prime* value" for the congruences; held-out-prime checks
  attributed to the first and third CRT programs only (`crt_verify.py`
  proves uniqueness by prod(q) > 4B with no held-out prime); "prime
  squares 9, 25, 49" (9 = 3^2 was omitted); implementation A timing
  "about four and a half minutes" (268 s); "one-page" script (47 lines);
  mycheck timing "under a minute" (3.6 s measured); float-recompute
  coverage claim now matches the extended `_recompute_sun46.py`; the
  100–120-digit audit recomputation now named as the kill pair and s_41
  (not "headline values", which could be read to include s_53/s'_61);
  and, from Codex rounds 2–3: the "floating point only in advisory
  cross-checks" disclosure now also names the first CRT program's padded
  magnitude bounds (with the fact that every value is also certified by
  a layer with exact-rational bounds or none needed), and the
  "CRT uniqueness proof (every value)" parenthetical was dropped from
  the abstract/intro (s_25/s_27's only finite-field cover is the
  padded-bound program; their rigorous certificates are implementation
  A's).
* Rebuilt: `note.pdf` is now 6 pages, still zero overfull/underfull
  boxes. `snippet_check.py`, `mycheck_2026-06-12.py` (exit 0, 3.6 s) and
  the extended `_recompute_sun46.py` (ALL NOTE CHECKS PASS) all re-run
  clean on 2026-06-12.

## Placeholders

`[AUTHOR]` (author block) and `[REPOSITORY/ARCHIVE URL TO BE INSERTED]`
(data availability) are intentional, per the commissioning spec, and must
be replaced before submission.
