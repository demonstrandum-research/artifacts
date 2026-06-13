# Build instructions — `note.tex` / `note.pdf`

Short announcement note: *A 36-point subset of the 13 x 13 x 13 grid with no
five points on a sphere or a plane* (C(13) >= 36 for the "no 5 on a sphere"
grid problem, AlphaEvolve Problem 6.60; source bundle in
`problems/p1-records/no-5-on-a-sphere-grid/`).

## Toolchain

Built with the same WSL Ubuntu TeX Live toolchain installed for the sibling
note `papers/graffiti-143-154/` (see its BUILD.md for the one-time install
command). pdfTeX 3.141592653-2.6-1.40.28 (TeX Live 2025/Debian). The
*default* WSL distro on this machine is `docker-desktop`, so `-d Ubuntu` is
required on every `wsl` invocation. Packages used: `geometry`,
`amsmath`/`amssymb`/`amsthm`, `booktabs`, `microtype`, `hyperref`, `xurl`,
`lmodern` (+`[T1]{fontenc}`; lmodern is required or pdfTeX aborts during
microtype font expansion). Manual `thebibliography` — no BibTeX run.

If the toolchain is missing, install once (~5 min, as root):

```powershell
wsl -d Ubuntu -u root -- sh -c "apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends texlive-latex-recommended texlive-latex-extra lmodern"
```

## Compile

From PowerShell (two passes for cross-references):

```powershell
wsl -d Ubuntu -- sh -c "cd /mnt/c/Users/jacks/source/repos/maths/papers/no5sphere-record && pdflatex -interaction=nonstopmode note.tex && pdflatex -interaction=nonstopmode note.tex"
```

Output: `note.pdf` (6 pages) in this directory. The build is clean of
overfull `\hbox`es (`grep -i overfull note.log`).

## Verifying the numbers in the note

Every quantity in the note was recomputed on 2026-06-12 during preparation,
directly from the certificate bundle at
`problems/p1-records/no-5-on-a-sphere-grid/`:

```powershell
cd C:\Users\jacks\source\repos\maths\problems\p1-records\no-5-on-a-sphere-grid
python code/check_cert.py certificates/record36_centralsym.json 13
# expect: VALID m=36 n=13, exit code 0   (<2 s; ~0.8 s measured 2026-06-12)

python verification/gate45_fresh_verify.py
# expect: GATE-4/5 FRESH VERIFICATION PASSED   (needs the Rust binary
# code/core/target/release/no5core.exe; `cargo build --release` if absent)
```

The full battery (three checker routes on all banked certificates, central
symmetry + shell distinctness, 7 mutation tests, saturation of the 36-set,
convention anchor on all six official AlphaEvolve record sets, saturation of
the published 33-set for all 8 translates) was re-run successfully on
2026-06-12 before the note was compiled; results land in
`verification/gate45_report.json`.

Independently of the bundle's own scripts, the following were recomputed from
scratch in plain Python while drafting the note (this session): all 376,992
lifted determinants of the 36-set (0 zeros, min |det| 2, max 198,750, 200
subsets with |det| <= 10), central symmetry (18 pairs, 0 fixed points, 18
pairwise-distinct shells 44..432), layer profiles, 16 surface points, parity
profile, saturation of the 36-set (0 addable cells), validity of all six
official record sets from `data/records.json`, and the 33-set's 0 addable
cells for all 8 translates (C(33,5) = 237,336 subsets, min |det| 2). Run-log
numbers (timings, iteration/restart counts, distinct-set counts) were taken
from the runs' STATUS.json files:
`runs/central-symmetric/{main-run,smoke}/STATUS.json`,
`runs/baseline-ils/main/STATUS.json`,
`runs/blocker-repair/{STATUS.json,run2-kick46/STATUS.json,run2-kick49/STATUS.json}`,
`runs/finite-field-f13/STATUS.json`.

## Citation verification (2026-06-12)

All bibliography entries were fetched and verified live while drafting:
arXiv abs pages for 2511.02864 (v3, 2025-12-22, Georgiev/Gomez-Serrano/Tao/
Wagner), 2411.00566 (PatternBoost), 2506.18113 (Dong-Xu), 2511.03526 (Szabo
— note: NOT Dong-Xu; the bundle's PROBLEM.md mis-attributes this one),
2506.13131 (Novikov et al., 18 authors), 2412.02866 + the Dagstuhl LIPIcs
page for Suk-White (SoCG 2025, LIPIcs 332, 76:1-76:8); the Thiele thesis and
Brass-Moser-Pach entries were taken from Suk-White's reference list
(extracted from the arXiv PDF); Ball JEMS 14 (2012) 733-748 via EMS Press;
the problem-page quote against the archived live fetch
`verification/provenance/problem60_20260612.html` (the live page is
JS-rendered; the embedded data object contains the verbatim statement). The
PatternBoost small-n values and the AlphaEvolve record values/harness-bug
quote were verified verbatim against the local `data/paper.pdf`
(arXiv:2511.02864v3, p. 63-64) and `data/no_5_on_a_sphere.ipynb`.

## Hostile-referee pass (2026-06-12)

The compiled note was refereed adversarially by Codex (GPT-5.5, thread
`019ebb07-dc5f-7180-bcb1-6aa2753933c9`), which re-verified the certificate
with its own from-scratch checker (376,992 subsets, 0 zero determinants,
min |det| 2, max 198,750, 200 with |det| <= 10, 18 pairs / distinct shells,
no addable 37th point), re-checked every citation online, and re-ran a
priority sweep (no public C(13) >= 34 or C(12) >= 34 claim found). Its
initial report flagged (1) a malformed statement of Lemma 2.3(i) — "two
orbit pairs not collinear with c" was vacuous since every orbit pair is
collinear with c — and (2) an abstract overstatement ("thousands of 34- and
35-point sets" vs. 98 logged 35s). Both were fixed (Lemma 2.3(i) restated as
"c plus at least two orbit pairs is invalid", proof split on collinearity;
abstract now "thousands of distinct 34-point sets and dozens of 35-point
sets") and the note recompiled; Codex re-reviewed the changes and returned
**"VERDICT: SURVIVES"**. The [AUTHOR] and [REPOSITORY/ARCHIVE URL] blocks
are intentional pre-submission placeholders.

## Second hostile-referee pass (2026-06-12, post-draft revision)

A full second referee-and-revise pass (Claude referee + Codex GPT-5.5 second
referee, thread `019ebb24-3caf-7622-b70a-386709d4571e`) re-verified every
number from the tex alone with fresh independent code
(`referee_recompute.py` / `referee_recompute_report.json` in this directory)
and every citation online, then revised `note.tex` and recompiled. 13 wording
/calibration defects were fixed (no mathematical defect found); the full
report-and-response log is `RESPONSES.md`. Both referees' final verdict:
**SURVIVES**. Notable for posterity: the printed PatternBoost n=10 witness in
arXiv:2411.00566v1 is corrupt (out-of-range coordinates and a vanishing
5-subset) — the note now cites that value as "reported" with a footnote.

## Caveats

- Do not run Python scripts from `%TEMP%` on this machine — a stray `re.py`
  there shadows the stdlib `re` module and breaks imports (numpy, pypdf).
- The blocker-repair distinct-set counts in the note (4068/2528/2833 34s,
  20/30/47 35s) are the *final* STATUS.json values; the source WRITEUP.md
  quotes an earlier mid-run harvest (4068+1655+1031 / 20+23+43) for runs 2-3,
  which were still running when it was written. The note uses the final
  values, re-read on 2026-06-12.
