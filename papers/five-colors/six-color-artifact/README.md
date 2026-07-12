# Six-color strong-majority artifact — `maj_le_six` (kernel-checked)

A self-contained Lean 4 project that formally verifies

> **`SMaj.maj_le_six`** — every *admissible* finite simple graph `G` admits a
> strong-majority 6-edge-coloring, i.e. `∃ c : Sym2 V → Fin 6, IsStrongMajority G c`.

The theorem is checked by the Lean kernel with a clean axiom footprint (see
[Axiom audit](#axiom-audit)). It is **not** externally refereed.

## What this is, and how it relates to the five-color result

This is the Demonstrandum strong-majority program's **earlier** theorem. It
bounds the strong-majority edge-chromatic number `Maj′(G) ≤ 6` for admissible
graphs, via a chain-decomposition / glue construction whose per-piece colorings
are supplied by **Shannon's bound** (a Δ ≤ 4 multigraph is 6-edge-colorable).
It improves the value 8 of the source paper (arXiv:2605.23828, Thm 12).

- **Mathematically superseded.** The public five-colors result proves the
  sharper `Maj′(G) ≤ 5` for every admissible graph
  (`../artifact/` in this bundle; the informal bound `≤ 5` also appears in
  Antoniuk–Prorok–Salia, arXiv:2607.00212). The six-color bound is therefore
  no longer the program's best value.
- **Historically load-bearing.** This proof is where the program's
  **glue-coloring interface** — the palette-generic dispatch that stitches
  per-chain colorings into a global strong-majority coloring across junctions —
  was first developed. The five-color proof *reuses that same interface*
  (`Maj5Base.lean`'s palette-generic glue/dispatch/chain machinery in
  `../artifact/lean/`), instantiated with a sharper per-piece coloring. We
  release the six-color predecessor because it is the source of that shared
  architecture and stands on its own as a kernel-checked theorem.

The two artifacts are **independent Lean projects** on different pins
(this one: Lean `v4.30.0` + mathlib `v4.30.0`; the five-color artifact:
Lean `v4.28.0` + a pinned mathlib commit). They share no source files.

## Layout

```
lean/
  SMaj.lean                 root module
  SMaj/Defs, Counting,      base definitions, counting lemmas, arithmetic,
    Arith, Master, Greedy     the Master coloring theorem, greedy pipeline
  SMaj/Six/*.lean           the ≤ 6 construction: Shannon multigraph engine,
                              Euler 2-split, chain decomposition (pieces /
                              linkage / ports), partition & slot calculus,
                              the fill / cycle / port colorings, the glue
                              assembly, and the headline in Final.lean
  scripts/CheckAxioms.lean  prints the axiom footprint of every declaration
  lakefile.toml, lean-toolchain, lake-manifest.json   exact pins
axioms.log                  banked output of the axiom audit (this checkout)
HASHES.txt                  sha256 of every staged source / config / audit file
```

The headline theorem is `SMaj.maj_le_six` in `lean/SMaj/Six/Final.lean`. One
`proof_wanted` remains in the library (`rainbow_of_groupSizes`, an instance of
Vizing's theorem) — it is **not** on the `maj_le_six` proof path; the greedy
route in `SMaj/Greedy.lean` supplies an unconditional substitute.

## Axiom audit

Every declaration in the library depends only on Lean/mathlib's standard
classical axioms — `propext`, `Classical.choice`, `Quot.sound` — with several
lemmas needing a strict subset (and `g_R4_eq` no axioms at all). **No `sorryAx`
appears anywhere.** In particular:

```
'SMaj.maj_le_six' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The full 204-declaration audit is banked in [`lean/axioms.log`](lean/axioms.log).

## Rebuild + re-audit

```sh
cd lean
lake exe cache get        # fetch the pinned mathlib build cache
lake build SMaj           # kernel-checks the whole library
lake env lean scripts/CheckAxioms.lean   # reprints the axiom footprint
```

A clean run reproduces `lean/axioms.log` (204 lines, no `sorryAx`).

## Provenance

Authored by John Erlbacher (Independent Researcher, ORCID
0009-0003-6851-4139) under the Demonstrandum research operation.
Kernel-checked; not externally refereed.
