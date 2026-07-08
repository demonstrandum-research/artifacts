# UCFrankl Lean project — toolchain setup (lens L5, Program UC)

Lean 4 + mathlib formalization bridgehead for the Frankl union-closed sets
program (`problems/p6-moonshot/PROGRAM.md`, T2). Pattern and pins are inherited
verbatim from `problems/p3-moonshot/borsuk/lean` (see its `SETUP.md` for the
full provenance of the toolchain choices).

## Versions (pinned, identical to borsuk)

| Component | Version |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.30.0` (pinned in `lean-toolchain`) |
| mathlib | release tag `v4.30.0` (pinned in `lakefile.toml` + `lake-manifest.json`) |
| elan | `%USERPROFILE%\.elan\bin` (on user PATH) |

The `.lake/packages` tree (mathlib + transitive deps, with compiled `.olean`s)
was copied directly from the borsuk project (same manifest, same revisions), so
no `lake update` / `lake exe cache get` was needed. If `.lake` is ever deleted:
`lake exe cache get` then `lake build` (never `lake update` — the pins are the
source of truth).

## Build and verify

```powershell
cd problems\p6-moonshot\lenses\L5-lean-entropy\lean
lake build                              # builds the UCFrankl library
lake env lean scripts\CheckAxioms.lean  # axiom audit of all closed theorems
```

Accept criterion for the audit: every `#print axioms` line reports only
`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no extra axioms.

## Layout

```
lean/
  UCFrankl.lean        # root module
  UCFrankl/
    Frankl.lean        # conjecture statement (D1-D3) + singleton-class theorem
    Entropy.lean       # discrete Shannon entropy core (absent from mathlib)
    Gilmer.lean        # Gilmer engine statement + kernel-checked reduction + psi lemmas
  scripts/
    CheckAxioms.lean   # axiom audit
```

Every mathematical statement in the `.lean` files carries an EPISTEMIC-STATUS
LEDGER tag in its docstring (program law; see `PROGRAM.md` CREATIVITY DOCTRINE).
