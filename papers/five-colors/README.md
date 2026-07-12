# Strong Majority Edge-Coloring with Five Colors

A Lean 4 verification and an alternative proof of the theorem of Antoniuk, Prorok & Salia
([arXiv:2607.00212](https://arxiv.org/abs/2607.00212)): every admissible graph admits a strong
majority edge-coloring with five colors.

**Author:** John Erlbacher (Independent Researcher) · erlbacher.research@gmail.com ·
[ORCID 0009-0003-6851-4139](https://orcid.org/0009-0003-6851-4139)
**Writeup:** https://demonstrandum-research.org/p/strong-majority/
**Citable archive:** [doi:10.5281/zenodo.21316623](https://doi.org/10.5281/zenodo.21316623) (resolves to the latest version)

## Contents

| Path | What it is |
|---|---|
| [`main.pdf`](main.pdf) / [`main.tex`](main.tex) / [`main.md`](main.md) | The paper (typeset PDF, TeX source, and Markdown source) |
| [`abstract.md`](abstract.md) | Abstract |
| [`claims.md`](claims.md) | The claim ledger: every factual claim in the paper with its verification status and evidence pointer |
| [`aps_memo.md`](aps_memo.md) | The memo sent privately to the original paper's authors: three observations on the written proof, with a repair |
| [`artifact/`](artifact/README.md) | The Lean 4 verification: reading kit, pinned toolchain, one-command rebuild and axiom audit, source hashes |
| [`census/`](census/README.md) | Exhaustive computation: all 268,478 admissible graphs on ≤ 9 vertices satisfy Maj′ ≤ 4 — data, scripts, verification |
| [`six-color-artifact/`](six-color-artifact/README.md) | The program's earlier kernel-checked six-color theorem, source of the glue-coloring interface the five-color proof reuses |

## Verification in one command

See [`artifact/README.md`](artifact/README.md). The final theorem `SMaj.Synthesis.maj_le_five`
is accepted by the Lean kernel with axioms exactly `[propext, Classical.choice, Quot.sound]`,
no `sorry`, no `native_decide`.

## Status

Kernel-checked; statement fidelity human-reviewed against the source papers (see the reading kit);
not externally refereed. The four-color conjecture of Kalinowski, Kamyczura, Pilśniak & Woźniak
remains open. Corrections, if any, will be logged here and on the writeup page — never silently.
