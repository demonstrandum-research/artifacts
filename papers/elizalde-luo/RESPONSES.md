# Referee responses — `note.tex` (final hostile-referee round, 2026-06-12)

This file records the second full referee round on the finished paper
*A proof of the Elizalde–Luo conjecture for nonnesting permutations avoiding
1132 and 3312* (`note.tex`), performed after the first round already recorded
in `BUILD.md`. Two referees: (R) a Claude hostile-referee/reviser pass with a
clean-room verification suite, and (X) an independent Codex (GPT-5.5, xhigh)
referee pass, thread `019ebb2d-6b6c-7542-9b66-da77581f1c95`. Both verdicts:
**no mathematical error found**; Codex verdict verbatim: **"ACCEPT WITH MINOR
FIXES"**. All findings and the revisions made are listed below. The paper was
recompiled after the fixes (17 pp, build clean: 0 errors, 0 overfull boxes,
0 pdfTeX warnings, 0 undefined references).

## What was re-verified (recomputed from the tex alone)

Referee R wrote a fresh clean-room suite
(`maths/.scratch/elref/referee_recheck.py` + `addendum_checks.py`,
independent of `_recompute.py` and of the source bundle), implementing the
literal biconditional containment definition and every lemma statement
directly from the tex. All checks pass (16 s):

- Literal-definition avoider counts over **all** words of `[n]_2`, n ≤ 5
  (113,400 words at n = 5): 1, 4, 16, 58, 196 = 3^n − 3·2^(n−1) + 1;
  nonnesting totals 1, 4, 30, 336, 5040 = n!·Cat_n. Fast predicates
  (Lemma 2.1 FIFO, arc test, Corollary 2.4 positional criterion) ≡ literal
  definition on every word (full ∀r,s biconditional at n ≤ 4 and on 1,500
  sampled words at n = 5; direct quadruple specialization on all 113,400).
- Lemma 2.1 bijection: set equality with the literal nonnesting words n ≤ 5,
  count + distinctness + nonnesting at n = 6.
- Theorem 4.1 at word level: predicted ⟺ actual on **every**
  (shape, permutation) pair n ≤ 6 (95,040 pairs at n = 6), 0 mismatches.
- Lemma 4.5 (local form) ≡ condition (C) for every sign word on every shape
  n ≤ 8; brute-force valid-sign-word count = 2^|F(s)| (0 if inadmissible) on
  every shape n ≤ 9; admissible-shape parameter map bijective with rebuilt
  shapes equal to the originals for all shapes n ≤ 12; classification parses
  all 742,900 shapes at n = 13; totals Σ 2^|F| = 3^n − 3·2^(n−1) + 1 for
  n ≤ 12 (525,298 at n = 12).
- Summation algebra: identity (5.2), Σ₁, Σ₂ closed forms, total, n ≤ 60;
  OGF x(1−2x+3x²)/((1−x)(1−2x)(1−3x)) expands to the formula (n < 40);
  A168583 offset-3 shift consistency.
- |W_n| and predicate ≡ complement (X₁ ⊔ X₂) on the full 3^n cube n ≤ 10;
  the 11 excluded strings at n = 3 as listed.
- Φ/Ψ: bijective onto W_n with two-sided inverse for n ≤ 8 (6,178 valid
  pairs at n = 8); word-level end-to-end set equality with the avoiders for
  n ≤ 6; **and** end-to-end on the independent DFS ground-truth lists at
  n = 9, 10 (18,916 + 57,514 words, all re-validated as avoiders; codes
  exactly W_9, W_10; total n ≤ 10 = 85,513).
- All three worked examples re-derived (n = 3 16-row table with case labels,
  UUDUDD, CBCCAC ↔ 234523145616).
- The n = 8 exhaustive claim: the clean-room Rust harness was **recompiled
  from source** (rustc 1.93.0) and re-run: 1,430 shapes, 57,657,600 pairs,
  predicted = actual = 6,178, 0 mismatches (1.5 s).
- Randomized hunts re-run with fresh seeds: n = 9, 10, 11, 2,000,000 uniform
  (shape, permutation) samples + 2,000,000 (shape, prefix-interval) samples
  each: 0 mismatches in all six runs.
- A168583's combinatorial name (partitions of {1,1,2,3,…,m−1} into exactly
  three nonempty parts) was verified against the closed form by brute force
  for m ≤ 10 — closing the chain behind the "equinumerosity" remark.
- `_recompute.py` re-run: ALL CHECKS PASS (15.6 s default; `--n7` full
  2,162,160-pair sweep, 0 mismatches, 4–6 s).
- The six-audit record in the bundle (`final-results.json`) was inspected:
  3 audits per route, all `overall: sound`, `fatal: false`.

Citations re-verified online on 2026-06-12: arXiv:2412.00336 v6 dated
2026-01-16 with journal ref DMTCS 27:1 PP2024 #13 published 2025-10-17; the
v6 HTML still contains the Table 4 row `{1132,3312} | 3^n−3·2^(n−1)+1 |
A168583` and the "All the conjectures have been checked for n up to 8"
preamble (also confirmed in the published LaTeX source, line 1614/1600);
OEIS A168583 (JSON API): name, offset 3,2, data through 525298+, formula,
o.g.f. — all as quoted; Archer–Laudone ECA 6:1 (2026) #S2R1, DOI
10.54550/ECA2026V6S1R1, PDF header fetched (treats single length-3 patterns
— "advanced" is the right calibration); Luo thesis PDF fetched (Dartmouth,
May 28, 2024, advisor Elizalde); Archer et al. AJC 74 (2019) 389–407,
Elizalde JCTA 180 (2021) 105429, Elizalde EJC 121 (2024) 103846
(arXiv:2204.00165), Gessel–Stanley JCTA 24 (1978) 24–33, Simion–Schmidt EJC
6 (1985) 383–406 all match the published paper's own bibliography. Fresh web
searches found no announcement of any other proof.

## Findings and revisions

| # | Referee | Severity | Finding | Resolution in `note.tex` |
|---|---------|----------|---------|--------------------------|
| 1 | R+X | MINOR | "recalled **verbatim** in Section 2" (intro) and "recall **exactly**" (§2.1) overclaim: the convention is restated with adapted notation (π→w), not verbatim. | Intro now says "recalled in Section 2"; §2.1 says "which we now recall". Footnote 2 and Appendix B reworded to make precise *what* was verbatim (the pinned quotations in the frozen definitions file, not the displayed prose). |
| 2 | R | MINOR | Quoted preamble had lowercase "all the conjectures…"; the source sentence reads "All the conjectures have been checked for n up to 8." | Quote capitalized to match the source exactly. |
| 3 | R+X | NIT | "Theorem 1.1 proves this equinumerosity" could be read as claiming a bijection to the OEIS partition objects, and the OEIS entry's index variable clashed with the paper's n. | Rewritten: the entry's own indexing is made explicit (m-th term, m ≥ 3, counts partitions of {1,1,2,3,…,m−1}); the byproduct is stated as an equality of cardinalities for {1,1,2,3,…,n+1}, "we exhibit no direct bijection". (The closed form behind the OEIS name was verified by brute force m ≤ 10.) |
| 4 | X | MINOR | Novelty sentence: "we found no announcement of a proof in the literature or on the web" is a search report, better phrased as awareness. | Now: "we are aware of no announcement of a proof (literature and web searches last performed June 12, 2026)". The verifiable facts (conjecture status in the published version and in v6) are kept. |
| 5 | R | MINOR | Appendix A runtime claim "a few minutes for the n = 7 sweep" is wrong on the reference machine: measured 4–6 s (CPython 3.11.9); default suite 15.6 s. The stale estimates in `_recompute.py`'s header were also wrong (claimed 2–4 min / 15–40 min). | Appendix A now states the measured timings ("about fifteen seconds … and a few seconds", with machine/Python qualifier); `_recompute.py` header comments corrected. |
| 6 | X | MINOR | The heavy verification artifacts cited in Appendix A (Rust n = 8 harness, n = 13 shape sweep, DFS lists, audit logs) were not pointed to from the paper. | Sentence added at the end of Appendix A: the artifacts are preserved in the verification bundle accompanying the paper's source, and the Rust harness was recompiled from source and re-run during the final referee pass (57,657,600 pairs, 0 mismatches). |
| 7 | X | NIT | Closing remark of §6: "each position j ≥ 2 of σ is a three-way choice **for arc j**" ignores the one-slot shift of case (I). | Remark reworded: position-to-arc correspondence per Definition 6.3, with the case-(I) shift stated; "position 1 absorbs the case distinction" now scoped to cases (S) and (II). |
| 8 | X | NIT | `[AUTHOR]` placeholder. | Intentional (kept from the first round); to be filled by the human operator before submission. |
| 9 | R | NIT | Appendix B's "Every number quoted … recomputed by the accompanying script or copied from the verification logs" did not cover the numbers added by the final referee passes. | Sentence extended to include the final hostile-referee recomputations. |

No FATAL or MAJOR findings. Neither referee found any error in the
mathematics: every lemma, the two endgames, all worked examples, and all
quoted numbers were independently recomputed and confirmed.

## Verdict

**ACCEPT WITH MINOR FIXES — all fixes applied and recompiled** (this round;
consistent with the first round recorded in `BUILD.md`). The mathematical
content stands as printed; remaining open item is the intentional `[AUTHOR]`
placeholder.
