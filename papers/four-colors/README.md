# Strong Majority Edge-Coloring with Four Colors for Graphs with Degrees in {3,4}: A Machine-Checked Program

Two kernel-checked (Lean 4) four-color strong-majority theorems:

- **`R4_three_four_t2`** — every finite simple graph with all degrees in {3,4} and **at most
  two degree-3 vertices** satisfies Maj′(G) ≤ 4. To our knowledge this is the first bound-4
  theorem covering any part of the mixed degree-{3,4} class. It is a **slice** of the mixed
  class, not the class: the general case, with arbitrarily many degree-3 vertices, remains
  open, and nothing here claims Conjecture 14 of Kalinowski, Kamyczura, Pilśniak & Woźniak
  ([arXiv:2605.23828](https://arxiv.org/abs/2605.23828)).
- **`R4_four_regular`** — every finite simple 4-regular graph satisfies Maj′(G) ≤ 4. The
  mathematics is **known** (the 4-regular case of KKPW's Proposition 21); this is a
  formalization by a different argument (capacitated-Hall defect avoidance, not an Euler tour).

The best published bound on the mixed class is the general Maj′ ≤ 5 of Antoniuk, Prorok &
Salia ([arXiv:2607.00212](https://arxiv.org/abs/2607.00212), Theorem 2). Together with the
program's earlier five-color verification (the prior machine-checked strong-majority result),
these two theorems are, to our knowledge, the first machine-checked strong-majority bounds
of **four**.

**Author:** John Erlbacher (Independent Researcher) · erlbacher.research@gmail.com ·
[ORCID 0009-0003-6851-4139](https://orcid.org/0009-0003-6851-4139)
**Writeup:** https://demonstrandum-research.org/p/strong-majority/four-colors/
**Citable archive:** [doi:10.5281/zenodo.21344300](https://doi.org/10.5281/zenodo.21344300) (resolves to the latest version)

## Contents

| Path | What it is |
|---|---|
| [`main.pdf`](main.pdf) / [`main.tex`](main.tex) | The paper (typeset PDF and TeX source) |
| [`claims.md`](claims.md) | The claim ledger: every factual claim in the paper with its verification status and evidence pointer |
| [`artifact/`](artifact/README.md) | The Lean 4 verification: reading kit, sources, axiom audits, confirmation records, source hashes |
| [`../five-colors/census/`](../five-colors/census/README.md) | The exhaustive four-colorability census (≤ 9 vertices) released with the five-color paper |

## Verification in one command

See [`artifact/README.md`](artifact/README.md). Both theorems are accepted by the Lean kernel
with axioms exactly `[propext, Classical.choice, Quot.sound]`, no `sorry` anywhere in their
dependency cones, no `native_decide`. The remaining `sorry`-pins in `Pins3.lean` are the openly
declared general-t program (the conditional route toward the full mixed class) and lie outside
both release theorems' cones — see the reading kit and `artifact/lean/AuditPins3.lean`.

## Status

Kernel-checked; statement fidelity human-reviewed against the source papers (see the reading
kit); not externally refereed. The four-color conjecture of KKPW remains open, as does the
mixed degree-{3,4} case with more than two degree-3 vertices. Corrections, if any, will be
logged here and on the writeup page — never silently.
