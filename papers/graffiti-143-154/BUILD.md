# Build instructions — `note.tex` / `note.pdf`

Short research note: *Counterexamples to two conjectures of Graffiti on graph
eigenvalues* (refutations of WoW conjectures 143 and 154; source bundles in
`problems/p2-factory/kills/graffiti-143/` and `.../graffiti-154/`).

## Toolchain

The canonical build uses TeX Live from the existing WSL Ubuntu distribution
(Ubuntu 26.04 LTS; note that the *default* WSL distro on this machine is
`docker-desktop`, so `-d Ubuntu` is required on every `wsl` invocation).
A user-scope MiKTeX 25.12 was additionally installed on the Windows host via
`winget install --id MiKTeX.MiKTeX` during preparation (pdflatex at
`%LOCALAPPDATA%\Programs\MiKTeX\miktex\bin\x64\pdflatex.exe`, not on PATH);
it can serve as an alternative engine, but `note.pdf` as shipped was built
with the WSL TeX Live route below.

Install (one-time, ~5 min; run as root to avoid a sudo password prompt):

```powershell
wsl -d Ubuntu -u root -- sh -c "apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends texlive-latex-recommended texlive-latex-extra lmodern"
```

This installs pdfTeX 3.141592653-2.6-1.40.28 (TeX Live 2025/Debian,
Debian packages `2025.20260124-1`). Packages used by `note.tex`:
`geometry`, `amsmath`/`amssymb`/`amsthm`, `booktabs`, `microtype`,
`hyperref`, `xurl` (the last from `texlive-latex-extra`), and `lmodern`.
**`lmodern` is required**: the note uses `[T1]{fontenc}` + `microtype`, and
without scalable Latin Modern fonts pdfTeX aborts with
`pdfTeX error (font expansion): auto expansion is only possible with scalable
fonts` (this was hit during the first build and fixed by installing `lmodern`
and adding `\usepackage{lmodern}`). The bibliography is a manual
`thebibliography` — no BibTeX run is needed.

## Compile

From PowerShell (two passes for cross-references):

```powershell
cd C:\Users\jacks\source\repos\maths\papers\graffiti-143-154
wsl -d Ubuntu -- sh -c "cd /mnt/c/Users/jacks/source/repos/maths/papers/graffiti-143-154 && pdflatex -interaction=nonstopmode note.tex && pdflatex -interaction=nonstopmode note.tex"
```

Output: `note.pdf` in this directory. The build is warning-clean with respect
to overfull `\hbox`es (check with `grep -i overfull note.log`); the only
expected log notes are the usual microtype/hyperref info lines.

## Verifying the numbers in the note

Every quantity in the note is reproducible from the kill bundles:

```powershell
cd C:\Users\jacks\source\repos\maths\problems\p2-factory\kills\graffiti-143
python checker_g143.py certificate_g143.json   # expect: CHECKER VERDICT: ACCEPT

cd C:\Users\jacks\source\repos\maths\problems\p2-factory\kills\graffiti-154
python check_graffiti154.py                    # expect: OVERALL: ALL CHECKS PASS
```

(Python 3.11 with numpy/sympy/mpmath; both re-run successfully on
2026-06-11/12 during preparation of the note, together with
`mutation_tests.py` (143: `MUTATION TESTS: ALL KILLED`) and
`scan_dumbbells.py` (143 family-minimality scan).)

Referee-driven revision 2026-06-12: `checker_g143.py` now additionally
asserts, for every convention an instance does *not* claim to violate, that
both routes' certified upper bounds on Var+ lie strictly below the RHS —
this certifies the "dash" (non-violation) entries of Table 1 of the note.
Checker (`ACCEPT`) and mutation suite (`ALL KILLED`) re-run after the change;
see the dated entry at the end of `verification_log.txt` in the 143 bundle.

Headline numbers were additionally recomputed from scratch by the helper
scripts in this directory:

- `_recompute143.py` — rebuilds all five dumbbells plus `D(40,10,40)` by
  independent float spectral computation, and checks the lollipop integer
  criterion and the closed-form Wiener index for `L(t,t)`,
  `t = 70, 71, 72, 100, 200`.
- `_ratio800.py` — recomputes the `D(800,40,800)` violation ratio
  (~1.81) quoted as the numerical illustration after
  Proposition 2.4.

Caveat on `_recompute143.py`-style helpers: do not run Python scripts from
`%TEMP%` on this machine — a stray `re.py` there shadows the stdlib `re`
module and breaks numpy imports.
