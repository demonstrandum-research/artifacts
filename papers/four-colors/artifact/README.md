# Artifact — Strong Majority Edge-Coloring with Four Colors (degrees {3,4}, t ≤ 2; and 4-regular)

Machine-checked (Lean 4) proofs of the two release theorems, plus the reading kit,
axiom audits, confirmation records, and source hashes. Companion to the paper
*Strong Majority Edge-Coloring with Four Colors for Graphs with Degrees in {3,4}:
A Machine-Checked Program* (John Erlbacher, Independent Researcher).

## Contents

```
artifact/
├── README.md               — this file
├── READING-KIT.md          — self-checking guide for BOTH theorems (statement,
│                             glosses to mathlib bedrock, source bridge, axiom
│                             output, rebuild command)
├── CONFIRM-R4FOURREG.md    — independent double-confirmation of R4_four_regular
│                             (provenance hashes, fresh-harness build, audit)
├── KILL-CHECK-R4.md        — binding claim calibration: what is known (KKPW
│                             Prop 21) vs. new (the t ≤ 2 slice; the machine check)
├── RELEASE-PREP-RECORD.md  — release record incl. the clean-environment rebuild
│                             (8029 jobs, exit 0) and per-declaration axiom audit
└── lean/
    ├── Maj5Base.lean         frozen base definitions (side/row/nColor/
    │                         IsStrongMajority) — byte-identical to the published
    │                         five-color artifact
    ├── Pins2.lean            toolkit + R4_four_regular (line 3447); one declared
    │                         sorry (the descent lemma, line 2949, conditional
    │                         route only — outside both release theorems' cones)
    ├── Pins3.lean            migration route + R4_three_four_t2 (line 10624);
    │                         remaining sorry-pins are the general-t program,
    │                         outside both release theorems' cones
    ├── AuditPins2.lean       #print axioms audit script for Pins2
    ├── AuditPins3.lean       #print axioms audit script for Pins3
    ├── Demos.lean            executable sanity demos of the definitions (K5/K3)
    └── HASHES.txt            SHA-256 of every Lean source file
```

## The theorems

```lean
theorem R4_three_four_t2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (ht2 : numDeg3 G ≤ 2) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c

theorem R4_four_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c
```

Both audit to axioms exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`,
no `native_decide`. See READING-KIT.md §4 (4-regular) and the addendum §3 (t ≤ 2) for
the verbatim per-declaration output, and RELEASE-PREP-RECORD.md §6 for the fresh
clean-environment rebuild.

## Reproduce

Pinned toolchain: `leanprover/lean4:v4.28.0`, mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
Build a lake project containing `Maj5Base.lean`, `Pins2.lean`, `Pins3.lean` against that pin,
run `lake build Pins3` (expect green, ~8029 jobs; the only `declaration uses sorry` warnings
are the declared pins outside the release cones), then build the audit files
(`AuditPins2.lean`, `AuditPins3.lean`) and check that every release declaration prints
axioms exactly `[propext, Classical.choice, Quot.sound]`. The exact recipe, including the
harness layout, is in READING-KIT.md §5 (both kits) and CONFIRM-R4FOURREG.md §7.
