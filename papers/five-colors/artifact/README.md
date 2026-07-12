# Artifact — Strong Majority Edge-Coloring with Five Colors

Machine-checked (Lean 4) proof that every admissible graph `G` satisfies
`Maj'(G) ≤ 5`, plus the reading kit, axiom audits, and source hashes.
Companion to the paper *Strong Majority Edge-Coloring with Five Colors: A Lean
Verification and an Alternative Proof* (John Erlbacher, Independent Researcher).

## Contents

```
artifact/
├── README.md              — this file
├── READING-KIT.md         — one-page self-checking guide (theorem, glosses,
│                            source bridge, axiom output, one command)
└── lean/                  — self-contained Lean 4 project
    ├── lakefile.toml        build config (mathlib pin baked in)
    ├── lean-toolchain       leanprover/lean4:v4.28.0
    ├── lake-manifest.json   resolved dependency versions
    ├── Maj5Base.lean        frozen definitions + glue interface/dispatch (≈5,300 lines)
    ├── Rung5Lam1.lean       Λ1 — steered partitions
    ├── Rung5Lam2.lean       Λ2 — Vizing at Δ ≤ 4
    ├── Rung5Lam3.lean       Λ3 — de-fattened multigraph coloring
    ├── Rung5Lam4.lean       Λ4 — the construction (≈2,400 lines)
    ├── Rung5Lam5.lean       Λ5 — assembly ⇒ maj_le_five  (ends with #print axioms)
    ├── SMKernel.lean        edge-coloring library root
    ├── SMKernel/EdgeColoring/*.lean  Kempe chains/swaps, Kierstead paths, linkage
    ├── audit_final_gateS.lean/.out   per-layer axiom audit (script + recorded output)
    ├── audit_final_gateF.lean/.out   second lane's audit (identical footprint)
    ├── rebuild_and_audit.sh          one command: build + re-print the audit
    └── HASHES.txt                    SHA-256 of every source file
```

## Reproduce (one command)

From `lean/` (needs `elan`/`lake` — https://leanprover-community.github.io/get_started.html;
the pinned toolchain and mathlib commit are fetched automatically):

```
lake exe cache get     # optional but recommended: prebuilt mathlib oleans
lake build Rung5Lam5
```

`Rung5Lam5.lean` ends with `#print axioms SMaj.Synthesis.maj_le_five`, so a
successful build prints the axiom footprint of the headline theorem on its last
line. For the full per-layer audit run `lake env lean audit_final_gateS.lean`, or
`./rebuild_and_audit.sh` to do both.

## What the build establishes

`SMaj.Synthesis.maj_le_five` (and every named layer of the chain) depends on
axioms exactly `[propext, Classical.choice, Quot.sound]` — the standard mathlib
triple, no `sorryAx`, no `native_decide`, no custom axioms. See `READING-KIT.md`
for the theorem statement, the gloss of every definition down to mathlib bedrock,
and the bridge from [APS] Theorem 2 to the formal statement.

- **Toolchain:** Lean 4 `v4.28.0`; mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- **License:** MIT (see the deposit record / repository `LICENSE`).
