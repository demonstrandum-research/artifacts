# Responses to the referee reports — `note.tex` (Graffiti 143 & 154)

Revision date: 2026-06-12. Three reports were received (mathematical
re-verification; citations/history/prior-art; claim-calibration &
presentation). Every required change is either implemented or explicitly
deferred to the author with reasoning. Line references are to the revised
`note.tex`; the revised `note.pdf` builds warning-clean (11 pages).

---

## Report 1 — mathematical re-verification (verdict: minor)

**1.1 Replace the [AUTHOR]/affiliation placeholder.**
DEFERRED TO AUTHOR (cannot be done by the revision pipeline: the author's
name, affiliation and contact details are not ours to invent). The
placeholder is retained, clearly marked, and is the first item of the
pre-submission checklist in `SUBMIT.md`.

**1.2 Insert the repository/archive URL and deposit the bundles.**
DEFERRED TO AUTHOR for the same reason: the deposit target (GitHub repo,
Zenodo DOI, institutional archive) is an account-level decision. The
placeholder is retained; `SUBMIT.md` lists the exact bundle contents to
deposit (both kill bundles, checkers, mutation suites, frozen WoW PDF +
decoder, archived search code, verification logs) and recommends
Zenodo (DOI) with a GitHub mirror. Until deposit, the Section 4 process
claims remain reproducible from the local bundles
(`problems/p2-factory/kills/graffiti-143/`, `.../graffiti-154/`).

**1.3 Remark on the lollipop scan: mention n = 119.**
IMPLEMENTED. Remark `rem:154min` now states: at n = 119 exactly seven
lollipops, L(t, 119−t) for 47 ≤ t ≤ 53, violate the distinct-pairs reading
and none the all-entries reading. Re-verified during this revision by a
fresh integer scan (n = 117: 0 violators; n = 118: exactly the four stated;
n = 119: exactly those seven, ld-only; n = 120: exactly L(50,70), L(51,69)
under both readings).

**1.4 The "within 0.35" near-saturation in Remark 2.2 (`rem:143min`).**
IMPLEMENTED (both suggested options at once): weakened to "within 0.3" and
the actual closest approach is now quoted — D(6,12,18) on n = 36 vertices,
falling short by about 0.355. Re-verified by a fresh float scan of all
dumbbells with n ≤ 36: max margin = −0.35458... at D(6,12,18), ld reading.

---

## Report 2 — citations / history / prior art (verdict: minor)

**2.1 "July 2004 compilation" dating of the WoW source.**
IMPLEMENTED in all five locations. The PDF metadata was re-extracted during
this revision (`/CreationDate (D:20060726173645-05'00')`, Acrobat Distiller
5.0, dvips(k)). The note now says the file is "the compilation archived by
Roucairol and Cazenave as `wow-july2004.pdf`" and states explicitly that the
filename suggests July 2004 while the PDF metadata records a creation date
of 26 July 2006, with the SHA-256 pin doing the identification (Intro);
"frozen source of Section 4" (Methods); "decoded WoW source" (Section 3
lead); "compilation ... archived as wow-july2004.pdf ... pinned here by the
checksum below" (Statement provenance); and the `\bibitem{WOW}` now carries
the metadata date.

**2.2 Population-standard-deviation code-provenance claim.**
IMPLEMENTED via the "soften and cite the public implementation" option. We
confirmed directly that the bundle's archived `GenerateGraph.rs` calls
`invariants::std_dev` / `invariants::mean` from a module absent from the
published tree, and that the repository's only published deviation routine
(`tools/calc.rs`, `fn std`) divides by the length (population convention).
The Conventions paragraph now claims only that "the only deviation routine
published in the search-code repository ... uses the same convention", and
Section 3 now says the scoring function "calls a statistics helper module
that is absent from the published tree; the one deviation routine the
repository does publish, in `tools/calc.rs`, is a population standard
deviation". The all-n²-entries mean-distance claim is unchanged (directly
visible in the public `GenerateGraph.rs`). Requesting the missing
`invariants.rs` from the authors is flagged in `SUBMIT.md` as an optional
follow-up.

**2.3 RC-2022 "refuted Graffiti conjectures" overstatement.**
IMPLEMENTED, essentially with the suggested wording: "Roucairol and Cazenave
applied Monte-Carlo search to spectral graph conjectures, among them
Graffiti's Conjecture 137 [RC2022], and then attacked the Graffiti list with
a portfolio of eight search algorithms [RC2025]".

**Optional (a) — FMS deviation defined for the Laplacian spectrum.**
ADOPTED: Section 3 now reads "define the eigenvalue deviation (there for the
Laplacian spectrum) by a root-mean-square formula".

**Optional (b) — nod to Wagner (arXiv:2104.14516).**
NOT ADOPTED (reasoned): the history paragraph is deliberately confined to
work on the Graffiti/WoW list itself; Wagner's deep-RL refutations concern
other conjectures and would require an extra bibliography item without
supporting any claim made here. Left to the author's taste; noted in
`SUBMIT.md`.

**Optional (c) — IASE-2025 locator.** No change needed (the bibitem already
uses arXiv:2409.18626 as the durable locator).

---

## Report 3 — claim calibration & presentation (verdict: minor)

**3.1 "Two independent checkers" wording for Conjecture 143.**
IMPLEMENTED everywhere. The note now distinguishes, in the abstract
("two algorithmically independent routes per result (for Conjecture 154, by
two independently written checkers)"), Methods ("for Conjecture 143, a
single clean-room checker that accepts only if two algorithmically
independent exact routes agree; for Conjecture 154, two independently
written checkers..."), the proof of Theorem 2.1 ("The clean-room checker
accepts the certificate only after two algorithmically independent exact
routes certify every claimed inequality"), the Section 4 lead ("for
Conjecture 143 the two routes live inside a single clean-room checker, while
Conjecture 154 has two independently written checkers"), and Data
availability ("all checkers" instead of "both checkers per result").

**3.2 "Every number ... recomputed from scratch by a separate script".**
IMPLEMENTED with the suggested division of labour. The "Independent
recomputation" paragraph now credits the checker + mutation-test re-runs
with certifying Tables 1–2, the lollipop scan and the MAD bounds, and the
separate helper scripts with the dumbbell scan re-execution and the headline
quantities (Table 1 values, D(40,10,40), D(800,40,800), L(t,t)). The
Methods sentence was aligned.

**3.3 Table 1 caption: dashes "(certified as well)".**
IMPLEMENTED the strong way (the report's first option): `checker_g143.py`
now asserts, for every convention an instance does *not* claim to violate,
that **both** routes' certified upper bounds on Var⁺ lie strictly below the
right-hand side. The patched checker was re-run on the pristine certificate
(`CHECKER VERDICT: ACCEPT`; D(6,12,20) and D(6,12,19) print "certified NOT
violated" for the all-entries reading with margins −0.401... and −0.766...)
and the full mutation suite was re-run (`MUTATION TESTS: ALL KILLED`,
M1–M10 all rejected). A dated entry was appended to the bundle's
`verification_log.txt` and `BUILD.md` documents the revision. The caption
now states exactly what is checked; the Conjecture-143 verification
paragraph describes the added assertion.

**3.4 Unscoped "This note refutes both conjectures."**
IMPLEMENTED with the suggested sentence: "This note refutes Conjecture 143,
and refutes Conjecture 154 under the standard-deviation reading of
'deviation' fixed in Section 3."

**3.5 "between 51 and 117 vertices" mis-implication.**
IMPLEMENTED: "a smaller, non-lollipop violator of any order up to 117 is not
excluded --- the prior search for this conjecture reached size 50, but it
was a heuristic search, not an exhaustive enumeration."

**3.6 AI-methods disclosure incomplete.**
IMPLEMENTED. The paragraph is now titled "Methods and AI-use disclosure" and
names the systems and roles: Claude language models (Anthropic) for the
discovery/verification pipeline and for drafting the manuscript text; Codex
(GPT-5.5, OpenAI) as the adversarial referee agent that authored the second
Conjecture-154 checker; and the author's role ("directed the work and takes
responsibility for its content"). Section 4 also names Codex for Checker B.

**3.7 Abstract "survived the 1990s computational attacks".**
IMPLEMENTED: now singular and calibrated — "survived the 1990–91
computational attack of Brewster, Dinneen and Faber (exhaustive only through
ten-vertex graphs)". The introduction adds the same scope with the explicit
calibration that survival there carries limited information since the
counterexamples exhibited need at least 37 vertices (verified against the
BDF 1995 text: "exhaustive search of the over 12 million nonisomorphic
graphs with 10 or fewer vertices").

**3.8 Abstract minimality phrasing.**
IMPLEMENTED: "the smallest counterexample certified here has 39 vertices
under both conventions for average distance (37 under the distinct-pairs
convention alone)"; the intro now also says "certified here". No minimality
over all connected graphs is claimed anywhere (Remark 2.2 and Remark 3.6
retain the honest scoping).

**3.9 Journal-prose polish.**
IMPLEMENTED: "an adversarial referee agent from a different model family
(Codex, GPT-5.5)" replaces "a hostile referee agent..."; "for completeness"
replaces "for honesty". The two placeholders are intentionally retained for
the author (see 1.1/1.2) and are the top items in `SUBMIT.md`.

---

## Revision-time re-verification summary

- `checker_g143.py certificate_g143.json` → `CHECKER VERDICT: ACCEPT`
  (with the new non-violation assertions active).
- `mutation_tests.py` (143) → pristine ACCEPT, M1–M10 REJECT,
  `MUTATION TESTS: ALL KILLED`.
- `check_graffiti154.py` → `OVERALL: ALL CHECKS PASS` (incl. its six
  internal mutation self-tests).
- Fresh independent scans during this revision confirmed the two new
  numeric claims added to the note (n = 119 lollipop violators; closest
  dumbbell approach −0.35458 at D(6,12,18), n = 36).
- `wow-july2004.pdf` metadata re-extracted: CreationDate 2006-07-26.
- `note.tex` recompiled twice (TeX Live 2025, WSL Ubuntu): 11 pages, no
  overfull/underfull boxes, zero LaTeX warnings.
