# RESPONSES.md — hostile-referee report and revisions for `note.tex`

**Date:** 2026-06-12.
**Referees:** Claude agent (this pass) as referee #1; Codex (GPT-5.5, xhigh,
full access, thread `019ebb20-ecbc-7193-8440-227e88ce0618`) as independent
referee #2, instructed to kill the note. Codex's verdict, verbatim:
**"VERDICT: ACCEPT WITH MINOR REVISIONS"** — "I could not kill the
mathematical counterexample."

All revisions below are implemented in `note.tex` (and one comment-only fix
in the Lean artifact). The note was recompiled after the changes: 8 pages,
0 overfull boxes, 0 LaTeX warnings.

---

## 1. What was re-verified (everything passed)

### 1.1 Mathematics, recomputed from the tex alone

Two independent recomputation runs on 2026-06-12:

- `_recompute.py` (the note's own script, stdlib-only, exact arithmetic):
  **27/27 PASS, "ALL CHECKS PASS", exit 0.**
- `_referee_recheck.py` (written fresh for this pass, deliberately different
  algorithms: exact Carathéodory hull membership over Q instead of
  H-representations; vertices via "not in conv of the others"; volume via a
  divergence-style signed surface sum over an independently derived facet
  list; full census of coinciding pair-sums): **37/37 PASS, exit 0.**

Every number in the note was hit by at least one of these, most by both:

| Claim in note | Status |
|---|---|
| S_A differences = {(1,0),(0,1),(3,5),(-1,1),(2,5),(3,4)}, all primitive | PASS |
| H-rep of conv(S_A): x≥0, y≥0, 5x−2y≤5, 3y−4x≤3; 16 evaluations; 4 edge incidences as listed | PASS |
| Case chase 15x−15 ≤ 6y ≤ 8x+6 ⇒ x ≤ 3; y pinned per x as listed | PASS |
| conv(S_A) ∩ Z² = the 7 listed points (also re-derived H-rep-free by Carathéodory) | PASS |
| The 3 convex-combination certificates for (1,1),(1,2),(2,3) | PASS (exact) |
| (m+1)² ≠ 7; 4 < 7 < 9 | PASS |
| T differences primitive; (1,1) = centroid; conv(T) ∩ Z² = T; area 3/2; vertex count 3; T case chase incl. x ≤ −1 impossibility | PASS |
| C: 28 differences primitive; bounding box [0,3]×[0,2]×[1,3]; conv(C) ∩ Z³ = C; full-dimensionality; vol = 5/2; N(C)=2 with exactly the two displayed coincidences; N({0,1}³)=12 with exactly the claimed 6+6 decomposition; (m+1)³ ∈ {1,8,27,...} | PASS |
| N invariance under unimodular-affine images (sanity-tested on a concrete map) | PASS |

### 1.2 Lean artifact

- `lake build` re-run 2026-06-12: **"Build completed successfully (8483
  jobs)"**, exit 0, no warnings — exactly as claimed in §4 of the note.
- Axiom audit (`lake env lean scripts\CheckAxioms.lean`) re-run: all **16**
  audited theorems report an axiom set contained in
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. Output matches
  STATUS.md verbatim.
- Hygiene grep over `lean/Borsuk/*.lean` + `scripts/*.lean`: zero `sorry` /
  `admit` terms (only prose mentions in comments), no `axiom` declarations,
  no `native_decide`, no `unsafe`, no `partial def`.
- File/line-count table in §4 verified exactly: Defs 282, SegmentGcd 252,
  WitnessA 148, HullSeven 176, Unimodular 167, Main 59, Smoke 44 — total
  1128 ("about 1100" ✓).
- The three Lean listings in §4 match `Main.lean` / `Defs.lean` verbatim.
- All nine "supporting lemma" names in §4 exist and are audited.
- Pins verified: `lean-toolchain` = `leanprover/lean4:v4.30.0`;
  `lakefile.toml` mathlib `rev = "v4.30.0"`; `lake-manifest.json` mathlib
  `inputRev v4.30.0`. Cache size claim (~1.6 GB) matches `SETUP.md`.

### 1.3 Citations and claims about the target paper

Against the frozen arXiv v1 source (`problems/p3-moonshot/borsuk/paper/`):

- Conjecture quote: character-for-character match with
  `sections/Borsuk.tex:76`; it is the **third** global `conjecture`
  environment (NP-hard §2 → QP §3 → Borsuk §4.2), so "Conjecture 3" ✓, in
  subsection 4.2 ✓.
- "Theorem 4.8": confirmed two ways — by counting the shared theorem counter
  in §4 (Rabinowitz 4.1, hyp-dir 4.2, diam-dir 4.3, example 4.4, remark 4.5,
  MaxDegree 4.6, Brooks 4.7, Borsuk **4.8**) and by the paper's own intro,
  which states it as "Theorem 4.8" in a `manualthm` ✓.
- "Definition 1.3" for β_Z ✓ (third `definition` env in §1). Lattice Borsuk
  graph, chromatic-number remark, Rabinowitz collinearity lemma + Brooks
  route ✓ (Borsuk.tex:23–72, diam-dir.tex:5). The d=2 remark quoting
  Bárány–Füredi Theorem 2(iii) ✓ verbatim (Borsuk.tex:79).

Web checks 2026-06-12:

- arXiv:2508.20009 — exists, title/authors exactly as cited, **still
  v1-only** (submitted 2025-08-27). Codex independently confirmed.
- Bárány–Füredi, Discrete Math. 241 (2001) 41–50 — confirmed (DOI
  10.1016/S0012-365X(01)00145-5; also in Bárány's own survey reference list
  and a citing LIPIcs paper). *Caveat:* the internal statement of their
  Theorem 2(iii) was not independently retrievable (paywalled); the note
  only attributes its description to BDLT's own citation, which is the
  honest framing, and the paper is verifiably about convex lattice polygons.
- Borsuk, Fund. Math. 20 (1933) 177–190 ✓ (EuDML/IMPAN).
- Kahn–Kalai, Bull. AMS 29 (1993) 60–62 ✓.
- Rabinowitz, Utilitas Math. 36 (1989) 93–95 ✓ (author's bibliography +
  citing papers).
- mathlib, CPP 2020, pp. 367–381 ✓ (ACM DL). de Moura–Ullrich, CADE-28,
  LNCS 12699, pp. 625–635 ✓ (Springer).
- Kill-check: Semantic Scholar reports **zero** citing papers for
  2508.20009; targeted searches found no resolution of Conjecture 3. The
  note's openness claim ("most recently on 2026-06-12") is accurate as of
  this pass.

---

## 2. Defects found and fixed

**D1 (MAJOR — found by referee #1, independently confirmed by Codex as its
#1). Degenerate-conventions sentence was false as written.**
Old text: degenerate conventions "cannot make the formal conjecture easier
to refute". In fact, under the formal encoding (ℕ ∋ 0, `sInf ∅ = 0`,
`cube 0` = a point) a singleton S falsifies `Conjecture3For2D` by itself:
betaZ = 0 ≠ 2² while its hull *is* unimodularly equivalent to `[0,0]²`.
**Fix:** §4 now states the junk corner explicitly and makes the correct,
checkable claim: the proof of `conjecture3_false` instantiates the
conjecture **only at S_A** (verified in `Main.lean`: `(hconj SA).mp h4`),
whose diameter is an honest 1 and whose betaZ is an honestly attained
minimum 4, so the disproof never uses the degenerate route; Theorem 2.3
(betaZ = 4 ∧ ∀m ¬equiv) is convention-free.

**D2 (MINOR — referee #1). The axiom-audit excerpt was not verbatim.**
The note's quote block wrapped each output line onto two lines; the real
output is one line per theorem. **Fix:** quoted exactly, one line per
theorem, at `\scriptsize` (fits the measure; the rebuild is overfull-free).

**D3 (MINOR — Codex #2). Lemma 2.1 used `u = (y−x)/g` which is undefined
for x = y (g = 0).** **Fix:** the display is now stated for x ≠ y, with the
x = y case (count 1, f = 0 = gcd(0)) handled in a separate clause; the proof
opening adjusted accordingly.

**D4 (MINOR — Codex #3). "Re-derives from scratch" overstated
`_recompute.py`** (for witness A the H-representation is hard-coded and
verified, not derived). **Fix:** now "re-verifies by direct recomputation",
with the one genuinely from-scratch part (the witness-C supporting
halfspaces) credited precisely; the new `_referee_recheck.py`
(H-representation-free Carathéodory route) is described and shipped, so the
"derived independently" property is now actually true of the bundle.

**D5 (NIT — Codex #4). "Documented line by line" too strong.** **Fix:**
abstract now says "documented against the verbatim text of the paper"
(§1's existing phrasing, which is accurate, is unchanged).

**D6 (NIT — Codex #5). Provenance claims ("triple-verified") not
substantiated by the shipped artifact.** **Fix:** rephrased to "three
independent recomputations" and the Data-availability paragraph now
promises the discovery-time verification records (which exist:
`problems/p3-moonshot/gate0-results.json`, STATUS.md).

**D7 (NIT — referee #1). §1 defined unimodular equivalence for arbitrary
sets while saying "all notions are those of [BDLT2025]"** (the paper defines
it for lattice polytopes). **Fix:** parenthetical added in §1; §4 already
discussed the widening.

**D8 (NIT — referee #1, artifact not note). Stale development comment in
`lean/Borsuk/Main.lean`** ("... which contain the remaining sorries") could
mislead an artifact reader. **Fix:** comment-only edit; `lake build` re-run
after the change (still 8483 jobs, exit 0) and axiom audit unchanged, so
every build claim in the note remains true post-edit.

**Not fixed (deliberate):** the `[AUTHOR]` and `[REPOSITORY/ARCHIVE URL]`
placeholders (Codex #6) are intentional pre-submission placeholders.

---

## 3. What the note does NOT claim (calibration confirmed)

- Theorem 1.2 (witnesses T, C) is explicitly *not formalized* — stated in
  the abstract, §1, §3, and §5.
- The "if" direction of Conjecture 3 is explicitly not addressed.
- The combined repair (full lattice set AND diam ≥ 2) is explicitly left
  open (Remark 3.3).
- The faithfulness of formal definitions is explicitly identified as the
  one link the kernel cannot check, with the mitigation documented.

## 4. Verdict

**ACCEPT (after the above revisions).** Both referees independently failed
to break any mathematical claim; every number reproduces; every citation
checks out; the one substantive faithfulness overstatement (D1) is fixed
with a precise, machine-checkable replacement. Remaining to-dos before
submission are non-mathematical: fill the author and artifact-URL
placeholders.
