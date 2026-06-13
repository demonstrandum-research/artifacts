# STATUS — Lean disproof of Conjecture 3 of arXiv:2508.20009

**Date:** 2026-06-11
**Project:** `problems/p3-moonshot/borsuk/lean` (Lean 4 `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`)
**Claim formalized:** Conjecture 3 of Brose, De Loera, Lopez-Campos, Torres,
*"On Lattice Diameter Segments and A Discrete Borsuk Partition Problem"*, arXiv:2508.20009 (v1, 27 Aug 2025 — confirmed still v1-only on arxiv.org as of 2026-06-11), is **false as stated**.

Paper text (verbatim, `paper/sections/Borsuk.tex` line 76, §4.2, label `conj:Borsuk` = Conjecture 3 in the compiled paper):

> Let $S \subset \Z^d$ be a bounded set. Then $\beta_\Z(S) =2^d$ if and only if $\conv(S)$ is unimodularly equivalent to a $d$-cube $[0,m]^d$ for any $m \in \N$.

Refutation witness (A), d = 2: `S_A = {(0,0), (1,0), (0,1), (3,5)}` — all six pairwise differences primitive ⇒ `diam_ℤ(S_A) = 1` ⇒ Borsuk parts must be singletons ⇒ `β_ℤ(S_A) = 4 = 2²`; but `|conv(S_A) ∩ ℤ²| = 7`, unimodular affine equivalence preserves the lattice-point count, and `|[0,m]² ∩ ℤ²| = (m+1)²` is never `7`.

---

## 1. Build state: CLEAN ✅

- `lake build` (full project, all 7 library files + root): **Build completed successfully (8483 jobs), exit 0**, no warnings, run 2026-06-11.
- Sorry audit: `grep -n "sorry|admit"` across `lean/Borsuk/` matches **only prose in comments** ("ONLY the lemmas marked `sorry` may be edited…", "(proved below, no sorry)"). **Zero `sorry`/`admit` terms in code.**
- Hygiene grep: no `axiom` declarations, no `native_decide`, no `unsafe`, no `implemented_by`, no `partial def`, no custom `macro_rules`/`elab` anywhere in `lean/Borsuk/`. All decidable checks use kernel-checked `decide`.
- All four work packages (P1-segment-gcd, P2-beta-four, P3-hull-seven, P4-unimodular-cube) report done; frozen statements in `Defs.lean` were never edited.

## 2. Axiom audit ✅ (run `lake env lean scripts\CheckAxioms.lean`, 2026-06-11)

Every theorem depends on **at most `[propext, Classical.choice, Quot.sound]`** — the three standard mathlib axioms. **No `sorryAx`, no extra axioms.** Verbatim output:

```
'Borsuk.Smoke.SA_pairwise_differences_primitive' does not depend on any axioms
'Borsuk.Smoke.card_Icc_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.Smoke.seven_not_square' depends on axioms: [propext]
'Borsuk.ncard_segLatticePts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.latticeLength_eq_gcd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.latticeDiam_SA' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.betaZ_eq_card_of_latticeDiam_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.betaZ_SA' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.mem_hullSA_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.latticeCount_hullSA' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.UnimodEquiv.latticeCount_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.latticeCount_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.succ_sq_ne_seven' depends on axioms: [propext, Quot.sound]
'Borsuk.witnessA_kills_conjecture3' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.conjecture3_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound]
'Borsuk.conjecture3_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. The verified theorems (`lean/Borsuk/Main.lean`)

```lean
theorem witnessA_kills_conjecture3 :
    betaZ SA = 4 ∧
      ∀ m : ℕ, ¬ UnimodEquiv (convexHull ℝ (toR '' (SA : Set Z2))) (cube m)

theorem conjecture3_counterexample :
    ∃ S : Finset Z2, betaZ S = 2 ^ 2 ∧
      ∀ m : ℕ, ¬ UnimodEquiv (convexHull ℝ (toR '' (S : Set Z2))) (cube m)

theorem conjecture3_false : ¬ Conjecture3For2D
```

with `Conjecture3For2D` (in `Defs.lean`) the d = 2 instance of the paper's iff:
`∀ S : Finset Z2, (betaZ S = 2 ^ 2 ↔ ∃ m : ℕ, UnimodEquiv (convexHull ℝ (toR '' S)) (cube m))`.
Refuting the d = 2 instance refutes the conjecture, which asserts all dimensions.

## 4. Faithfulness review: FAITHFUL ✅

Definitions were written against the **local copy of the actual arXiv v1 LaTeX source** (`paper/sections/`, the arXiv tarball). All verbatim quotes in `Defs.lean`/`Main.lean` re-checked against the source on 2026-06-11:
- Conjecture 3: `Borsuk.tex:76` (3rd `conjecture` env in compiled order NP-hard → QP → Borsuk; section order makes `Borsuk.tex` = §4.2). ✓
- `f(x,y) = |[x,y] ∩ ℤ^d| − 1`: `Borsuk.tex:5–9`. ✓  `ldiam` (Def 1.1): `1_introduction.tex:10`. ✓
- `β_ℤ` (Def 1.3 "minimal size of a partition … smaller lattice diameter"; §4.2 "strictly smaller"): `1_introduction.tex:104`, `Borsuk.tex:11`. ✓
- Unimodular equivalence (`A ∈ GL(d,ℤ)`, `t ∈ ℤ^d`, `P = AQ + t`) and primitive vectors: `1_introduction.tex:119–120`. ✓

**Hostile referee verdict (Codex GPT-5.5, xhigh, read-only review, 2026-06-11): PASS on all nine probe points; overall "FAITHFUL — the Lean theorems genuinely refute Conjecture 3 as stated."** Specifically reviewed and passed:
1. `segLatticePts`/`latticeLength` = paper's `|[x,y] ∩ ℤ²| − 1`; no ncard-infinite or ℕ-truncation trap (exact value `gcd + 1` proved).
2. `latticeDiam` double `Finset.sup` = max over pairs; empty-set convention harmless (witness nonempty, diam 1).
3. `Finpartition` + strict `<` + `sInf` = "minimal size of partition with strictly smaller diameter"; forbidding empty parts cannot change a minimum; achievable set nonempty for the witness.
4. `UnimodMap` (explicit det ±1 matrix + integer translation acting on ℝ², `P = φ '' Q`) = paper's `P = AQ + t`; direction matches the paper's; maps have integral affine inverses so no direction escape hatch; widening from lattice polytopes to arbitrary subsets only strengthens the non-equivalence claim.
5. `cube m` = `[0,m]²`; the `∀ m` refutation covers both ℕ-with-0 and positive-ℕ conventions.
6. "for any m ∈ ℕ" rendered `∃ m`; the proof gives `∀ m, ¬equiv`, negating the RHS under **both** the existential and the literal universal reading — nothing hinges on the ambiguity. Refuting d = 2 refutes the all-d statement.
7. "bounded set" as `Finset`: no reading of "bounded" excludes the 4-point witness (explicit coordinate bound recorded in `SA_bounded`).
8. Witness honest: `betaZ SA = 4` via primitive differences; `hullSA` definitionally `convexHull ℝ (toR '' SA)` = paper's `conv(S)`.
9. No invalidating definitional drift. Nonfatal caveats noted: degenerate-`betaZ` docstring discussion slightly muddy; `m = 0` under an existential reading is awkward for singleton sets — neither is used by the refutation. The only manufactured "escape" — reading an unstated hypothesis `S = conv(S) ∩ ℤ^d` into the conjecture — is **not what Conjecture 3 says** (and witnesses B/C below are designed to kill exactly that repair).

## 5. File inventory

| File | Role | State |
|---|---|---|
| `lean/Borsuk/Defs.lean` | Frozen definitions, documented line-by-line against paper text | complete, never edited |
| `lean/Borsuk/SegmentGcd.lean` | P1: `|[x,y] ∩ ℤ²| = gcd(y−x) + 1` (Bezout) | sorry-free |
| `lean/Borsuk/WitnessA.lean` | P2: `latticeDiam SA = 1`, `betaZ SA = 4` | sorry-free |
| `lean/Borsuk/HullSeven.lean` | P3: H-representation, `latticeCount hullSA = 7` | sorry-free |
| `lean/Borsuk/Unimodular.lean` | P4: count invariance, `latticeCount (cube m) = (m+1)²`, `(m+1)² ≠ 7` | sorry-free |
| `lean/Borsuk/Main.lean` | Final assembly (3 theorems above) | sorry-free |
| `lean/Borsuk/Smoke.lean` | Toolchain smoke tests | sorry-free |
| `lean/scripts/CheckAxioms.lean` | Axiom audit script (`lake env lean scripts\CheckAxioms.lean`) | output above |

## 6. What remains (stretch goals — NOT required for the kill)

The literal disproof is **done**. Stretch targets from the vetted gate0 entry, in priority order:

1. **Witness (B), full-set d = 2 repair-killer:** `T = {(0,1),(1,0),(1,1),(2,2)} = conv(T) ∩ ℤ²`, all differences primitive ⇒ `β_ℤ = 4`; hull is a triangle (3 vertices, area 3/2), so not equivalent to any `[0,m]²`. Kills the "S must be the full lattice-point set of its hull" repair the authors' d = 2 claim implicitly assumes. Reuses everything: the `betaZ_eq_card_of_latticeDiam_eq_one` lemma, the H-representation pattern, the count invariance (lattice count 4 forces m = 1, then distinguish triangle from square by lattice count of the hull — 4 vs 4 — needs the vertex-count or an interior-point invariant instead; plan: `(1,1)` is in T's hull boundary… use the paper-side argument: equivalence would force `conv(T)` = unimodular image of `[0,1]²`, but `[0,1]²` has 4 vertices and `conv(T)` has 3 — formalize via extreme points, or count lattice points of the *boundary*/interior, both unimodular invariants).
2. **Witness (C), full-set d = 3:** 8-point set, `β_ℤ = 8 = 2³`; rule out m ≥ 2 by count (8 < 27) and m = 1 by the pair-sum coincidence invariant (2 vs 12). Requires re-doing Defs for d = 3 (`ℤ × ℤ × ℤ` or `Fin 3 → ℤ`) — a separate package.
3. Write-up: short arXiv note with the Lean artifact.

## 7. Reproduction

```powershell
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
cd <repo>\problems\p3-moonshot\borsuk\lean
lake build                                # exit 0, no warnings
lake env lean scripts\CheckAxioms.lean    # axiom audit, output as in §2
```

Note: Lean rejects UTF-8 BOM files — keep scripts BOM-less.
