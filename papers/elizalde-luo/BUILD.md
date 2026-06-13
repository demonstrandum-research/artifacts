# Build instructions — `note.tex` / `note.pdf`

Full paper (17 pp): *A proof of the Elizalde–Luo conjecture for nonnesting
permutations avoiding 1132 and 3312*. Source bundle:
`problems/p3-moonshot/elizalde-luo/` (audit-passed proof drafts
`drafts/recurrence-structural.md` (primary) and `drafts/bijection.md`
(bijective endgame), pinned conventions `DEFINITIONS.md`, audit record
`final-results.json`, ground-truth data `data/`, verification suites
`work/`).

## Toolchain

Same toolchain as `papers/graffiti-143-154` (see the BUILD.md there for the
one-time install command): TeX Live 2025/Debian inside the existing WSL
Ubuntu distribution. **The default WSL distro on this machine is
`docker-desktop`, so `-d Ubuntu` is required on every `wsl` invocation.**
pdfTeX 3.141592653-2.6-1.40.28; packages used: `geometry`,
`amsmath`/`amssymb`/`amsthm`, `booktabs`, `array`, `microtype`, `hyperref`,
`xurl`, `lmodern` (required — `[T1]{fontenc}` + `microtype` abort without
scalable fonts). The bibliography is a manual `thebibliography`; no BibTeX
run is needed. The toolchain was already present from the graffiti-143-154
workflow; nothing new was installed for this paper.

## Compile

From PowerShell (two passes for cross-references):

```powershell
cd C:\Users\jacks\source\repos\maths\papers\elizalde-luo
wsl -d Ubuntu -- sh -c "cd /mnt/c/Users/jacks/source/repos/maths/papers/elizalde-luo && pdflatex -interaction=nonstopmode note.tex && pdflatex -interaction=nonstopmode note.tex"
```

Output: `note.pdf` (17 pages) in this directory. The build is clean: zero
errors, zero overfull `\hbox`es, zero pdfTeX warnings (check with
`grep -iE "^!|overfull|pdfTeX warning" note.log`).

## Verifying the numbers in the paper

`_recompute.py` (this directory, Python 3.11, stdlib only) is a clean-room
re-derivation of the small-`n` layer of Appendix A from the literal
biconditional containment definition alone — it shares no code with the
proof drafts or the earlier verification suites:

```powershell
cd C:\Users\jacks\source\repos\maths\papers\elizalde-luo
python _recompute.py          # R1–R9, ~15 s, expect: OVERALL: ALL CHECKS PASS
python _recompute.py --n7     # full n=7 Theorem A sweep (2,162,160 pairs), ~5 s
```

(Timings measured 2026-06-12 under CPython 3.11.9 on the preparation
machine.)

What it re-checks (R1–R9 map to Appendix A of the note): avoider counts
over *all* words of [n]_2 for n ≤ 5 (113,400 words at n = 5) from the
literal definition; fast predicates ≡ literal definition on every word
n ≤ 5; Theorem A (predicted ⟺ actual) on every (shape, permutation) pair
n ≤ 6 (n ≤ 7 with `--n7`), 0 mismatches; the shape classification and
per-shape count 2^|F(s)| by brute force over all sign words per shape
n ≤ 9, and the classification totals = 3^n − 3·2^(n−1) + 1 for n ≤ 12
(525,298 at n = 12); the tail recurrences; the summation identity to
n = 60; |W_n| and predicate-vs-complement on the full 3^n cube n ≤ 10; the
bijection Φ/Ψ (injective, image = W_n, two-sided inverse) n ≤ 8 plus
word-level set equality n ≤ 6; and all three worked examples of the paper
(the 16-row n = 3 table, the shape UUDUDD, and CBCCAC ↔ 234523145616).

Heavy checks quoted in Appendix A but not re-run here live in the source
bundle: the exhaustive n = 8 run (all 57,657,600 pairs, clean-room Rust)
is `problems/p3-moonshot/elizalde-luo/work/codex_review/adversarial_referee.rs`;
shape-level checks to n = 13 are `work/verify_shapes.py`; the bijection
end-to-end on all 85,513 ground-truth avoiders n ≤ 10 is
`work/bij/verify_bijection.py` with the avoider lists in `explore/`
(the total 85,513 was recounted from those files for this paper;
one draft's prose says 85,514, an off-by-one not propagated here).

## Referee record

Hostile referee pass on the finished paper: Codex (GPT-5.5, xhigh
reasoning, full access), thread `019ebb12-5c08-70b0-bf07-872774bd14c6`,
2026-06-12. Verdict: **"ACCEPT WITH MINOR FIXES"** — five findings, all
minor/presentational (author placeholder [intentional]; Σ₂ edge-case
wording; F(s) notation in the Appendix A table; exact scope sentence for
`_recompute.py`; DMTCS publication month). All except the intentional
[AUTHOR] placeholder were fixed and the paper recompiled; no mathematical
error was found ("I found no mathematical error in the proof chain").
Codex independently re-ran `_recompute.py` (pass) and the clean-room Rust
n = 8 exhaustive check (0 mismatches), reproduced the n = 3 and n = 6
examples, and verified the OEIS / ECA / thesis citations.

Second hostile referee round on the finished paper, 2026-06-12 (after the
above): a Claude referee/reviser pass with a fresh clean-room suite
(`maths/.scratch/elref/`), plus an independent Codex (GPT-5.5, xhigh)
referee pass, thread `019ebb2d-6b6c-7542-9b66-da77581f1c95`.
Codex verdict: **"ACCEPT WITH MINOR FIXES"**; no mathematical error found by
either referee. The Rust n = 8 harness was recompiled from source and re-run
(57,657,600 pairs, 0 mismatches); randomized hunts at n = 9,10,11 re-run
with fresh seeds (0 mismatches); the bijection was run end-to-end on the
n = 9,10 ground-truth lists (codes = W_9, W_10 exactly); A168583's
combinatorial name was verified against its closed form for m ≤ 10; all
citations re-fetched. Nine minor/presentational findings were fixed in
`note.tex` and the paper recompiled (now 17 pp). Full record: `RESPONSES.md`
in this directory.

## Citation provenance (all fetched and verified 2026-06-12)

- Elizalde–Luo: arXiv:2412.00336 abs page (v6, 2026-01-16; journal ref
  DMTCS 27:1, Permutation Patterns 2024, #13, published 2025-10-17;
  DOI 10.46298/dmtcs.14885); Table 4 row checked in the v6 HTML and in the
  published LaTeX source at `problems/p3-moonshot/elizalde-luo/src/formatted.tex`
  (line 1614).
- OEIS A168583: fetched (internal format); name, offset 3, data
  1,4,16,58,196,634,1996,6178,18916,57514,174076,525298,…, formula
  3^(n−2) − 3·2^(n−3) + 1, o.g.f. x^3(1−2x+3x^2)/((1−x)(1−2x)(1−3x)).
- Archer–Laudone: ECA 6:1 (2026) Article #S2R1, DOI
  10.54550/ECA2026V6S1R1 (PDF header fetched); treats single length-3
  patterns, does not touch Table 4.
- Luo thesis: PDF fetched from math.dartmouth.edu (May 28, 2024); contains
  a related conjecture table but not the {1132,3312} row.
- Remaining entries (Archer et al. 2019, Elizalde 2021/2024, Gessel–Stanley
  1978, Simion–Schmidt 1985) verified against the published paper's own
  bibliography (`src/nonnesting_references.bib`) and web checks.
