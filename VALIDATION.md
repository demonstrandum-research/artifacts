# VALIDATION — how to verify this repository as an outside mathematician

You are assumed hostile and assumed to trust no AI system. Everything below is
designed so that the only things you end up trusting are: your own Python
interpreter, the Lean 4 kernel (for one result), your own reading of a handful
of short programs, and your own comparison of frozen statement quotes against
their public sources.

**Honest time budget.** One hour suffices to (a) run every mechanical check,
(b) do one full skeptic loop on a result of your choice, and (c) do the
statement-faithfulness pass over the twelve certificate-based results. The
thirteenth result (Elizalde–Luo) is an **audited proof, not a certificate**:
its mechanical checks run in minutes, but refereeing the written proof is a
separate, conventional mathematical task (budget a further session; see §5).

Companion files: [`RESULTS.md`](RESULTS.md) (one section per result: exact
claim, prior status, artifacts, commands, expected output) and
[`verify_all.py`](verify_all.py) (runs every mechanical check, prints a
PASS/FAIL table).

---

## 1. The trust model — read this first

Every result here is of the form: **a finite object on disk + a short program
that checks the object against a mathematical statement.** That architecture
has exactly three remaining failure modes, and your hour should be spent on
them in this order:

1. **Statement faithfulness** (the most common failure of AI "solutions to
   open problems"): the checker might test a *different statement* than the
   one in the literature — a misremembered variant, a strict/non-strict slip, a
   convention mismatch. Mitigation here: every result freezes the statement
   **verbatim** from the authoritative source (PDF/LaTeX/HTML archived in-repo,
   with URLs, access dates, and often sha256 hashes), and every write-up
   documents how each ambiguity was resolved — usually by refuting *all*
   defensible readings. **This step is irreducibly yours**: open the frozen
   quote, open the public source, compare; then read the checker's test
   condition against the quote. Pointers per result are in §4.
2. **Checker soundness**: a buggy checker can accept garbage. Mitigation:
   independent dual checkers (different agents, often different languages) and
   **mutation testing** (targeted corruptions of each certificate must all be
   rejected — a checker that never rejects anything proves nothing; the
   mutation suites are runnable). Strongest mitigation: the checkers are short.
   Write your own — for most results 20–40 lines suffice, and each RESULTS.md
   section tells you exactly what condition to implement.
3. **Priority**: the result may have been published before. Mitigation: dated,
   documented search logs per result (queries + outcomes, in each WRITEUP.md).
   You can rerun the queries. This is evidence, never proof.

What a green PASS table does **not** establish: that the problems matter, that
the statements were open (see the logs), or — for the one audited-proof result
(Elizalde–Luo) — that the written proofs are correct (see §5).

## 2. Step one: run everything (10 minutes)

Requirements: Python 3.10+ with numpy and sympy. Optional: Rust/cargo (all
needed binaries are prebuilt in-tree; cargo is only used to rebuild if missing)
and elan/Lean (the two Lean checks are skipped with a message if `lake` is
absent — install elan and the pinned toolchain builds itself on first run).

```
cd C:\Users\jacks\source\repos\maths
python verify_all.py           # 33 checks; 4-13 minutes depending on machine load
python verify_all.py --full    # 36 checks; ~25-40 minutes (adds redundant long layers)
python verify_all.py --strict  # SKIPs become failures (use this for a zero-trust audit)
```

Expected: `TOTAL: 33 PASS, 0 FAIL, 0 SKIP` (36 with `--full`). **A SKIP means
the corresponding result was NOT verified on your machine** (e.g. the two Lean
checks skip if `lake` is absent — and then the Borsuk result is unverified for
you); the summary names the affected results, and `--strict` makes SKIPs fatal.

Every check is a subprocess running a banked, human-readable script;
`verify_all.py` itself only matches exit codes and verdict strings. Two
consequences you should internalize: (1) read `verify_all.py` (~500 lines,
mostly a table) to confirm it cannot manufacture a PASS; (2) a green row is
only as strong as the banked checker behind it — `verify_all.py` trusts each
checker's verdict line, so the checkers themselves (not the harness) are what
you audit in §3. This is by design: the harness is a convenience, not the
evidence.

## 3. Step two: spot-verify one result end to end (15 minutes)

Pick the result nearest your expertise and do the full loop once: source quote
→ checker condition → run → mutate by hand (corrupt the certificate yourself,
re-run, watch it fail). Two good first picks:

- **C(13) ≥ 36** (`problems\p1-records\no-5-on-a-sphere-grid\`): the condition
  is one sentence — every 5-subset of 36 integer points has nonzero 5×5 lifted
  determinant. The 36 points are printed in WRITEUP.md. Write your own checker
  in 20 lines; integer arithmetic is exact (|det| < 2²⁵).
- **IRIS 6.1** (`problems\p0-iris\`): one certificate line, two checkers
  (Python/Rust) that rebuild the polytope from scratch; the inequality test is
  4 integers.

For the Lean result (Borsuk), the loop is different: you read
`lean\Borsuk\Defs.lean` (each definition is documented line-by-line against the
paper's LaTeX, which is also in-repo under `borsuk\paper\sections\`), confirm
the three theorem statements in `Main.lean` say what RESULTS.md §2 claims, and
then `lake build` + the axiom audit do the rest — you trust the Lean kernel,
not any prose.

## 4. Statement-faithfulness pointers (where the verbatim quote lives)

| result | frozen verbatim statement | public source to compare against |
|---|---|---|
| IRIS 6.1 | `problems\p0-iris\WRITEUP.md` §2 | openreview.net/pdf?id=v6Ulp3U1ZT, Conj. 6.1 |
| Borsuk C3 | `borsuk\STATUS.md` header + `lean\Borsuk\Defs.lean` docstrings; LaTeX at `borsuk\paper\sections\Borsuk.tex` line 76 | arXiv:2508.20009 v1, §4.2 Conjecture 3 |
| Graffiti 143 | `kills\graffiti-143\PROVENANCE.md` (+ archived `wow-july2004.pdf`, glyph decode documented) | WoW July 2004 compilation, item 143 |
| Graffiti 154 | `kills\graffiti-154\PROVENANCE.txt` + `wow-decoded.txt` | WoW July 2004 compilation, item 154 |
| Davila C9 | `kills\davila-conj9\WRITEUP.md` §1 + archived `source_2406.19231v2.html` | arXiv:2406.19231v2, Conjecture 9 |
| Pandey 4.1 | `kills\pandey-parity\WRITEUP.md` §1 | arXiv:2601.03293 v1, Conjecture 4.1 |
| Solubilizer A.1 | `kills\solubilizer-a1\WRITEUP.md` (main.tex lines 445–447) | arXiv:2412.16177 v1, Appendix A |
| Solubilizer A.13 | `kills\solubilizer-a13\WRITEUP.md` + frozen `paper-2412.16177v1.pdf` p. 60 | arXiv:2412.16177 v1, Appendix A.5.6 |
| Solubilizer A.16 | `kills\solubilizer-a16\WRITEUP.md` + frozen `paper.pdf` p. 13 | arXiv:2412.16177 v1, Appendix A.5.6 |
| Sun 4.6 | `kills\sun-46\WRITEUP.md` (TeX verbatim, `paper.tex` line 1109, frozen in `attacks\sun-46\`) | arXiv:2108.07723 v7, Conjecture 4.6 |
| Koch–Narayan C1 | `kills\koch-narayan\WRITEUP.md` (PaperDraft.tex lines 145–148, tarball in-repo) | arXiv:2511.01719 v1, Conjecture 1 |
| C(13) ≥ 36 | `no-5-on-a-sphere-grid\PROBLEM.md` + hashed live HTML in `verification\provenance\` | AlphaEvolve repository of problems, #60; arXiv:2511.02864 Problem 6.60 |
| Elizalde–Luo | `elizalde-luo\DEFINITIONS.md` (quotes `src\formatted.tex` by line number; LaTeX in-repo) | DMTCS 27:1 #13, DOI 10.46298/dmtcs.14885, Table 4 |

(`kills\...` = `problems\p2-factory\kills\...`; paths relative to repo root.)

Where a statement was ambiguous (average-distance conventions in Graffiti
143/154, the Φ sign typo in Koch–Narayan, "diamond" in Davila C9, quantifier
readings in solubilizer A.1/A.13), the write-up enumerates every defensible
reading and the certificates violate **all** of them — check that claim, it is
the load-bearing answer to "you solved the wrong variant".

## 5. What each verification grade does and does not give you

- **kernel** (Borsuk): if you accept the Lean kernel and confirm Defs.lean
  matches the paper, there is nothing else to take on faith — no `sorry`, no
  extra axioms, no `native_decide` (the axiom audit check enforces this
  mechanically). Residual risk lives only in definition faithfulness (§4).
- **dual-checker** (IRIS, Graffiti 143/154, Davila C9, Pandey, A.1, Sun 4.6,
  Koch–Narayan, C(13) ≥ 36): two-plus independently written programs agree, and
  mutation suites show they actually reject corrupted certificates. Residual
  risks: correlated misreading of the statement by all checker authors
  (mitigated by §4 and by hostile cross-model audits, but ultimately yours to
  re-check), and for koch-narayan the disclosed caveat that both clean-room
  checkers are Python.
- **audit-panel** (A.13, A.16, Elizalde–Luo): for the two solubilizer kills,
  one banked checker + a logged independent recomputation by another model
  family — the easy fix as a skeptic is to recompute in GAP (G = A5×S3 resp.
  A5×S4; minutes of work). For **Elizalde–Luo**, understand precisely what is
  mechanical and what is not: the enumeration checks (formula matches brute
  force for n ≤ 8 by three independent implementations) only reproduce the
  paper authors' own evidence; the *theorem* rests on two written proofs
  (`drafts\recurrence-structural.md`, `drafts\bijection.md`) that were
  adversarially audited (five panel reports in `final-results.json`, each with
  clean-room verification code banked under `work\`) with every lemma
  exhaustively machine-tested beyond its use range. That is strong evidence —
  it is not a kernel proof. If you referee one thing in this repo as a
  mathematician, referee those two drafts; the audit reports list the five
  subtlest steps and where each was machine-checked.

## 6. Suggested one-hour schedule

| time | action |
|---|---|
| 0:00–0:10 | `python verify_all.py`; skim the table; read `verify_all.py` itself |
| 0:10–0:25 | full loop on one result (§3), including a hand-made mutation |
| 0:25–0:40 | statement-faithfulness pass over the results nearest your field (§4) |
| 0:40–0:50 | Borsuk: read `Defs.lean` + `Main.lean` against `Borsuk.tex`; confirm the axiom audit |
| 0:50–1:00 | skim two WRITEUP.md "What this does not show" + kill-check sections; spot-rerun one openness query |

If you have a second hour, spend it on the Elizalde–Luo recurrence-structural
draft with `final-results.json`'s audit reports beside it.

## 7. Known limits of the bundle (read before citing)

1. Openness/priority claims are dated 2026-06-11/12 search logs, nothing more.
2. The exhaustive-sweep side claims of two results (minimality/uniqueness of
   the n = 13 Koch–Narayan counterexample; IRIS census beyond the 5 minimal
   certificates) are single-implementation or discovery-side corroborated —
   each write-up flags exactly which claims those are. The refutations
   themselves never depend on them.
3. The Elizalde–Luo theorem is not kernel-checked (the `lean\` directory there
   is incomplete scaffolding, not a claim).
4. Two solubilizer kills have only one banked checker each (§5).
5. Several kills target machine-generated conjectures of modest weight; each
   write-up's "What this does not show" section calibrates this explicitly.
