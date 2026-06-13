# ElizaldeLuo Lean project — setup and skeleton map

Lean 4 + mathlib project for the Elizalde–Luo conjecture for `{1132, 3312}`
(arXiv:2412.00336, DMTCS 27:1 (2025), Table 4): nonnesting permutations of
`{1,1,…,n,n}` avoiding 1132 and 3312 are counted by `3^n - 3·2^(n-1) + 1`.

* Pinned conventions: `../DEFINITIONS.md` (quoted verbatim in docstrings — do not
  change definitions without re-checking against it).
* Designated proof: `../drafts/bijection.md` (FIFO normal form → sign-word encoding
  → explicit bijection Φ/Ψ onto a ternary language `W_n` → `|W_n|` by a two-line
  disjointness count). Backup endgame: `../drafts/recurrence-structural.md`.
* Audit trail: `../final-results.json` (all six drafts audited sound; the flagged
  presentational fixes are incorporated as comments/docstrings here).

## Versions (pinned — identical to ../../borsuk/lean)

| Component | Version |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.30.0` (pinned in `lean-toolchain`) |
| mathlib | release tag `v4.30.0` (pinned in `lakefile.toml`; exact revs in `lake-manifest.json`) |
| elan | at `%USERPROFILE%\.elan\bin` (prepend to PATH in fresh shells) |

The `.lake/packages` tree was copied wholesale from `../../borsuk/lean/.lake`
(same manifest), so no network was needed. If `.lake` is ever deleted:
`lake exe cache get` then `lake build` (never run `lake update` casually).

## Build

```powershell
$env:Path = "$env:USERPROFILE\.elan\bin;" + $env:Path
cd C:\Users\jacks\source\repos\maths\problems\p3-moonshot\elizalde-luo\lean
lake build          # full build; sorries are expected (40 of them, see below)
```

`lake build` also *runs the sanity checks*: `ElizaldeLuo/Sanity.lean` contains
kernel `decide` examples and `#guard` commands that fail the build if any
definition drifts. A slower one-time check lives in `scripts/SlowSanity.lean`
(run via `lake env lean scripts\SlowSanity.lean`; not part of the library).

## File map (= sorry packages)

| File | Content (bijection.md section) | Sorries |
|---|---|---|
| `ElizaldeLuo/Defs.lean` | core definitions per DEFINITIONS.md: `baseWord`, `IsMultisetPerm`, `Contains` (biconditional equality-pattern containment), `Avoids`, `Nonnesting` (avoid 1221 & 2112), `IsAvoider`, `words`, `avoiders`, `ConjectureStatement`; generic `strings` enumerator + proved membership lemmas | 0 |
| `ElizaldeLuo/WLang.lean` | §7: alphabet `ABC`, language `W`, complement families `X1`, `X2`, count `card_W` | 6 (pkg **wlang**) |
| `ElizaldeLuo/Fifo.lean` | §1 Lemma 0: `IsDyck`, `dycks`, positions (`oPos`/`qPos`/`heightAt`/`firstAscent`), `openerShape`, `openerLabels`, `wd`, FIFO normal-form lemmas | 7 (pkg **fifo**) |
| `ElizaldeLuo/SignWord.lean` | §3: `IsPrefixInterval`, `signWordOf`, `permOfSigns`, Fact 3.1 (bijection), Fact 3.2 (comparison rule), Lemma 2 | 7 (pkg **signword**) |
| `ElizaldeLuo/TheoremA.lean` | §2 + §4: Lemma 1 positional criteria, `ValidSign`, `validPairs`, Theorem A, chain step 1 `card_avoiders_eq_card_validPairs` | 4 (pkg **theoremA**) |
| `ElizaldeLuo/Shapes.lean` | §5–6: `tailWord`, `shapeS`/`shapeI`/`shapeII`, Lemma 5 converse + injectivity, Lemmas 4+5 classification, Lemma 6 local validity (`TailConstraint`, the two iffs) | 11 (pkg **shapes**) |
| `ElizaldeLuo/Bijection.lean` | §7–8: `ltr`, `phi`, `psi` (executable!), Theorem B steps 1–4, chain step 2 `card_validPairs_eq_card_W` | 5 (pkg **bijection**) |
| `ElizaldeLuo/Main.lean` | §9: `elizalde_luo_1132_3312` composed from the three chain steps (no sorry of its own) | 0 |
| `ElizaldeLuo/Sanity.lean` | sanity instances n ≤ 4 (+ some n = 5): kernel `decide` + `#guard` (see below) | 0 |

Proof chain composed in `Main.lean`:
`(avoiders n).card = (validPairs n).card` (theoremA) `= (W n).card` (bijection)
`= 3^n - 3·2^(n-1) + 1` (wlang).

## Encoding conventions (0-based; the drafts are 1-based)

* Words: `List ℕ`, values `1..n`, positions 0-based.
* Shapes: `List Bool`, `true` = U/opener, `false` = D/closer. Draft arc `J` ↦
  0-based arc `J-1`; draft `o_J, q_J` ↦ `oPos s (J-1)`, `qPos s (J-1)` (0-based
  positions). `q_1` = `qPos s 0`.
* Signs: `Bool`, `false` = L ↦ `A`, `true` = H ↦ `B`. Sign word `ε : List Bool` of
  length `n-1`; draft `ε_J` (J = 2..n) ↦ `ε.getD (J-2) false`, i.e. 0-based arc `j ≥ 1`
  has sign `ε.getD (j-1) false`.
* Case parameters `a, i` are *counts* (not positions) and keep the draft's values.
  `δ : List Bool` of length `n-a-1`, entry `r` = height bit of 0-based tail arc `a+1+r`.

## Sanity status (all pass; build fails if they regress)

* Kernel `decide`: `(avoiders 1).card = 1`, `(avoiders 2).card = 4`;
  `(validPairs n).card = 1, 4, 16, 58` (n = 1..4);
  `(W n).card = 1, 4, 16, 58, 196` (n = 1..5).
  (`avoiders` n ≥ 3 is kernel-infeasible in reasonable time; `List.permutations`
  was avoided in `words` precisely so that the kernel can reduce it at all.)
* `#guard` (interpreter, native-free; same `Decidable` instances): real-definition
  avoider counts 1, 4, 16 for n ≤ 3 and pointwise `avoiderFast = IsAvoider`;
  n = 4 count 58 via the cross-checked quadruple checker, with all 58 survivors
  re-verified against the real `IsAvoider`; nonnesting totals 30, 336;
  encode (`openerShape`/`signWordOf`) image = `validPairs` (n = 3 real, n = 4);
  `phi` image = `W` with `psi` two-sided inverse (n = 3, 4); end-to-end decode
  `W → avoiders` set equality (n = 3, 4); Fact 3.1 inverses (n = 4); Lemma 5/6
  statement sweeps at n = 5; the worked examples of bijection.md §10 (n = 3 table
  rows, the `CBCCAC` n = 6 example).
* `scripts/SlowSanity.lean` (one-time, slow): kernel `decide` for
  `(avoiders 3).card = 16` and the full real-definition interpreted count at n = 4.
