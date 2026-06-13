# Build instructions — `note.tex` / `note.pdf`

Short research note: *Counterexamples to a conjectured characterization of
cubes by the lattice Borsuk number, formally verified in Lean 4* (disproof of
Conjecture 3 of arXiv:2508.20009; source bundle in
`problems/p3-moonshot/borsuk/` — `STATUS.md`, the Lean project under `lean/`,
and the frozen arXiv v1 source under `paper/`).

## Toolchain

Same toolchain as the sibling note `papers/graffiti-143-154` (see its
BUILD.md for the one-time install): TeX Live 2025 from the existing WSL
Ubuntu distribution (`texlive-latex-recommended`, `texlive-latex-extra`,
`lmodern`; pdfTeX 3.141592653-2.6-1.40.28). The default WSL distro on this
machine is `docker-desktop`, so `-d Ubuntu` is required on every `wsl`
invocation. No additional packages were needed for this note; on top of the
graffiti note's package set it additionally uses `listings` (for the Lean
code blocks, with `literate` mappings for the Unicode characters
∧ ∀ ℕ ¬ ℝ ∃ ↔ ℤ × β) — `listings` ships with `texlive-latex-recommended`.
The bibliography is a manual `thebibliography`; no BibTeX run is needed.

## Compile

From PowerShell (two passes for cross-references):

```powershell
cd C:\Users\jacks\source\repos\maths\papers\borsuk
wsl -d Ubuntu -- sh -c "cd /mnt/c/Users/jacks/source/repos/maths/papers/borsuk && pdflatex -interaction=nonstopmode note.tex && pdflatex -interaction=nonstopmode note.tex"
```

Output: `note.pdf` (8 pages) in this directory. The build is error-clean and
overfull-`\hbox`-clean (`grep -ci 'overfull' note.log` → 0).

## Verifying the numbers in the note

**Theorem 1.1 / Section 2 (witness A)** — the authority is the Lean project
(Lean 4 toolchain `leanprover/lean4:v4.30.0`, mathlib release tag `v4.30.0`,
pinned in-tree). Re-run during preparation of this note (2026-06-12), both
commands exiting 0:

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
cd C:\Users\jacks\source\repos\maths\problems\p3-moonshot\borsuk\lean
lake build                                # "Build completed successfully (8483 jobs)"
lake env lean scripts\CheckAxioms.lean    # all 16 theorems: at most
                                          # [propext, Classical.choice, Quot.sound]
```

(Lean rejects UTF-8 BOM files — keep scripts BOM-less. If `.lake` was
deleted, run `lake exe cache get` first; see `lean/SETUP.md`.)

**Theorem 1.2 / Section 3 (witnesses T and C) and all witness-A numbers
again** — exact integer/rational arithmetic, Python 3 standard library only:

```powershell
cd C:\Users\jacks\source\repos\maths\papers\borsuk
python _recompute.py         # expect: 27 x PASS, then "ALL CHECKS PASS"
python _referee_recheck.py   # expect: 37 x PASS, then "REFEREE RECHECK: ALL CHECKS PASS"
```

`_referee_recheck.py` was written during the hostile-referee pass of
2026-06-12 and recomputes the same quantities by deliberately different
algorithms (exact Caratheodory hull membership over Q instead of
H-representations; vertices by the "not in the hull of the others"
criterion; volume by a divergence-style signed surface sum; full census of
coinciding pair-sums). Both scripts must pass.

The script re-verifies the 6+6+28 primitivity checks, the H-representation
and 7-point enumeration for conv(S_A) with exact convex-combination
certificates, conv(T) ∩ Z² = T with area 3/2, the supporting-halfspace
certificate for conv(C) ∩ Z³ = C (those halfspaces it derives from scratch)
with exact volume 5/2, and the pair-sum invariants N(C) = 2 vs
N({0,1}³) = 12. (Caveat from the sibling note
applies: do not run Python scripts from `%TEMP%` on this machine — a stray
`re.py` there shadows the stdlib.)

**Citations** — all seven references were fetched and verified against
their sources on 2026-06-12 (arXiv abs page for 2508.20009 — still v1-only;
publisher/indexer pages for the rest). The verbatim Conjecture 3 quote was
checked against the frozen arXiv v1 LaTeX source at
`problems/p3-moonshot/borsuk/paper/sections/Borsuk.tex` (line 76; it is the
third `conjecture` environment in the compiled paper).

Referee-driven revision 2026-06-12 (see `RESPONSES.md` for the full report):
the degenerate-conventions sentence in §4 was corrected (a singleton plus
`m = 0` does falsify the formal biconditional; the Lean proof provably never
uses that route — `conjecture3_false` instantiates the conjecture only at
`S_A`), the axiom-audit excerpt is now quoted exactly (one line per theorem),
Lemma 2.1 no longer uses an undefined `u` in the `x = y` case, two
overstatements ("documented line by line", "re-derives from scratch") were
calibrated down, and the second verification script `_referee_recheck.py`
was added to the bundle. A stale development comment ("remaining sorries")
in `lean/Borsuk/Main.lean` was fixed (comment-only); `lake build` re-run
after the change — still "Build completed successfully (8483 jobs)", exit 0,
axiom audit unchanged. Note rebuilt: 8 pages, 0 overfull, 0 LaTeX warnings.
