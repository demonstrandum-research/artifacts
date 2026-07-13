# CONFIRM-R4FOURREG — independent double-confirmation of `Rung4Moonshot.R4_four_regular`

**Verdict: CONFIRMED.** Every finite simple 4-regular graph admits a four-color strong
majority edge-coloring, kernel-clean, sorry-free, in a fresh isolated harness.

- Date: 2026-07-12
- Target commit: `420ba1e` ("rung4 round 16: R4_four_regular — the campaign's first
  unconditional kernel-clean theorem"); confirmed ancestor of working HEAD `66c9ec4`.
- Fresh harness: `C:\t\r4final` (NOT reusing r4cdx/r4pin working state).
- Toolchain: `leanprover/lean4:v4.28.0`; Lake 5.0.0-src+7e01a1b; mathlib rev
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- Cache: only the immutable `.lake/packages` mathlib olean cache was junctioned from
  `C:\t\r4pin` (`mklink /J`); `.lake/build` was fresh (Maj5Base + Pins2 rebuilt from source).

## 1. Provenance / hashes (sha256)

| file | source | sha256 |
|---|---|---|
| Maj5Base.lean | `420ba1e:papers/rung5-five-colors/artifact/lean/Maj5Base.lean` | `403e071720ac8b8b0e9652b26168b762f35f0ded7efca995bed70fbd5b55b718` |
| Maj5Base.lean | HEAD working tree (same path) | `403e071720…5b55b718` (IDENTICAL) |
| Maj5Base.lean | `C:\t\r4pin\Maj5Base.lean` harness copy | `403e071720…5b55b718` (IDENTICAL) |
| Pins2.lean | `420ba1e:…/constructive_route/Pins2.lean` | `2506573e52f0e3d210ff3f033e30232b42ffebf80bcb2552389e97c5b5a68658` |
| Pins2.lean | `C:\t\r4pin\Pins2.lean` harness working copy | `4a486acb…` (DIFFERS — harness had drifted; NOT used) |

Pins2 was extracted fresh from `420ba1e` (`git show`), NOT from the drifted r4pin copy.
Maj5Base `IsStrongMajority` definition (lines 72-74) is byte-identical to the published
five-colors artifact (line-slice sha256 `da728245…`; whole-file sha256 identical):
```
def IsStrongMajority (c : Sym2 V → C) : Prop :=
  ∀ u v, G.Adj u v → ∀ α : C, nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2
```

## 2. Build (`lake build Pins2`)

Command (in `C:\t\r4final`): `lake build Pins2`
Result: **green, exit 0, 8028 jobs.** `Built Maj5Base (20s)`, `Built Pins2 (47s)`.
Only warnings emitted (linter: unused section vars / simp args; one `declaration uses
sorry` at `Pins2.lean:2932` — see §4). No errors.

## 3. Per-declaration `#print axioms` (file `AuditR4Final.lean`, `lake build AuditR4Final`)

FLAGSHIP + stated chain — all report EXACTLY `[propext, Classical.choice, Quot.sound]`,
NO `sorryAx`:
```
'Rung4Moonshot.R4_four_regular'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.exists_edge_split_pin'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.Avoid.avoidance_core'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.placement_of_clean_transversal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.strongMajority_of_safe_defects' depends on axioms: [propext, Classical.choice, Quot.sound]
```

10 random spot-check declarations — all clean (no sorryAx):
```
IsEdgeSplit.swap, reachable_two_odd, P2_equiv, halfCount_le_degree,
exists_oddCycleMinimal_split, path_edge_color_interior, cap_comm,
Avoid.biUnion_slotTarget_eq, glue_edge      -> [propext, Classical.choice, Quot.sound]
crossOnSet_support_subset                    -> [propext, Quot.sound]   (subset, still clean)
```

CONTROL (audit-machinery validity): the KNOWN open-crux lemma is correctly flagged, and
R4 provably does NOT route through it:
```
'Rung4Moonshot.strict_descent_of_no_clean_transversal'
    depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```
This proves `#print axioms` here does detect `sorryAx` — so R4's clean result is meaningful.

## 4. The one `sorry` in the file is quarantined from R4

`Pins2.lean:2932` `strict_descent_of_no_clean_transversal` (OPEN-CRUX-DESCENT-CORE)
contains the file's only real `sorry` (token at line 2949; `lake build` reported exactly
one "declaration uses sorry"). R4_four_regular runs a PARALLEL chain
(`exists_edge_split_pin → Avoid.avoidance_core ×2 → placement_of_clean_transversal ×2 →
strongMajority_of_safe_defects`) — for 4-regular graphs every vertex is clean, so no
minimality/descent lemma is invoked. §3's axiom audit confirms this at the kernel level.

## 5. Statement fidelity

```lean
variable {V : Type*} [Fintype V] [DecidableEq V]   -- file header
theorem R4_four_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c
```
Matches the claim: every finite (`Fintype V`) simple graph that is 4-regular
(`∀ v, G.degree v = 4`) admits `c : Sym2 V → Fin 4` with `SMaj.IsStrongMajority G c`.
Empty-`V` case handled explicitly (constant coloring); no vacuity. `IsStrongMajority` is
the published artifact definition (§1).

## 6. Subversion scan (Pins2.lean and Maj5Base.lean)

NONE found of: `axiom` declarations, `native_decide`, `implemented_by`/`@[extern]`/
`extern`/`opaque`/`unsafe`, `macro`/`macro_rules`/`elab`/`syntax`, `ofReduceBool`/
`reduceBool`/`addDecl`/`evalExpr`. Only `set_option` uses are `autoImplicit false` and
`maxHeartbeats` bumps (time-limit only, no soundness impact). Maj5Base has zero `sorry`
tokens (all textual "sorry" are prose comments asserting sorry-freeness).

## 7. Reproduce

```
mkdir C:\t\r4final && cd C:\t\r4final
# lakefile.toml (mathlib rev 8f9d9cff…, libs Maj5Base + Pins2 + AuditR4Final),
# lean-toolchain v4.28.0, lake-manifest.json copied from a built r4* harness
git show 420ba1e:papers/rung5-five-colors/artifact/lean/Maj5Base.lean > Maj5Base.lean
git show 420ba1e:problems/p5-strongmajority/rung4-moonshot/constructive_route/Pins2.lean > Pins2.lean
mklink /J .lake\packages <built-harness>\.lake\packages     # immutable mathlib cache only
lake build Pins2            # green, 8028 jobs
lake build AuditR4Final     # emits the #print axioms lines in §3
```
