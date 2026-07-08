# Erdős #866 Lean extension project — toolchain setup

Lean 4 + mathlib project extending van Doorn's public development for
Erdős #866 (Choi–Erdős–Szemerédi pairwise sums). Mathematical context:
`../PROBLEM.md` (frozen dossier); program: `../PROGRAM.md` (T4 track).

## Design decision: pin to the UPSTREAM toolchain, vendor byte-identical

The upstream file (github.com/Woett/Lean-files/ErdosProblem866.lean, frozen
copy `.scratch/ErdosProblem866.lean`, sha256 `043731e3...9845e`) declares in
its header:

> Lean version: leanprover/lean4:v4.28.0
> Mathlib version: 8f9d9cff6bd728b17a24e163c9402775d9e6a365

We pin to exactly these (NOT the repo-standard v4.30.0 used by the borsuk
project) so the 3494-line Aristotle-generated proof script compiles without
any porting risk; its tactic soup (`grind`, `aesop`, `simp_all +decide`,
`nlinarith`) is fragile under mathlib drift. Verified: 8f9d9cff is a real
mathlib master commit (2026-02-16, "chore: bump toolchain to v4.28.0") with
CI build cache available.

`Erdos866/Upstream.lean` is byte-identical to the frozen copy — re-verify:

```powershell
(Get-FileHash .\Erdos866\Upstream.lean -Algorithm SHA256).Hash
# must be 043731E35444D446AD8EFFEB8A5F1FEBDC904991BF9B9312C3ACC2C17CA9845E
```

Consequence: `autoImplicit` stays at default `true` (upstream relies on an
auto-bound `n` in `HasPairwiseSums_succ_to_HasPosPairwiseSums`); our own
modules are written with all variables explicitly bound.

## Versions (pinned)

| Component | Version |
|---|---|
| OS | Windows 11 (native) |
| elan | 4.2.3 (`%USERPROFILE%\.elan\bin`) |
| Lean toolchain | `leanprover/lean4:v4.28.0` (pinned in `lean-toolchain`) |
| mathlib | commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (pinned in `lakefile.toml` + `lake-manifest.json`) |

## Build

```powershell
$env:Path = "$env:USERPROFILE\.elan\bin;" + $env:Path
cd C:\Users\jacks\source\repos\maths\problems\p4-erdos866\lean
# fresh checkout only (manifest is source of truth; never casually re-run):
#   lake update        # resolves pins; post-update hook runs `cache get`
lake exe cache get     # idempotent; ~8010 cache files for this commit
lake build             # builds the Erdos866 library
lake build Erdos866.G5Small   # stretch module (not in root import yet)
lake env lean scripts\CheckAxioms.lean   # axiom audit (no sorryAx anywhere)
```

All long-running compute at IDLE priority (Start-Process + PriorityClass).

## Layout

```
lean-toolchain        # leanprover/lean4:v4.28.0
lakefile.toml         # mathlib pinned to 8f9d9cff (upstream's exact commit)
lake-manifest.json    # exact dependency revisions
Erdos866.lean         # root module
Erdos866/
  Upstream.lean       # van Doorn's development, BYTE-IDENTICAL vendored copy
  Statements.lean     # dossier §5 standing-bounds index + rfl def-checks + T1 target Props
  Warmup.lean         # NEW: HasPairwiseSums.mono, one_le_gFun, one_le_hFun
  G5Small.lean        # NEW (stretch): five_le_gFun_five_five (g₅(5) ≥ 5)
scripts/
  CheckAxioms.lean    # #print axioms audit
```

Policy: `Erdos866/Upstream.lean` is never edited. All extensions live in
sibling modules that import it. Any T1 improvement (h₄ < 2270 / g₅ < 1.2e8)
is developed as `Erdos866/H4Improved.lean` etc. with its own axiom audit.
