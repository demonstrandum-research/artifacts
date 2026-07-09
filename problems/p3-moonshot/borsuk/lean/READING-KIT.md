# READING-KIT — Discrete Borsuk Conjecture 3 disproof (kernel-checked)

*A one-page, trust-nothing reader for the Lean 4 formalization. Every claim below is
either a verbatim quote of the source paper, a verbatim Lean statement, or the
verbatim output of a command you can rerun. Kit regenerated + all checks freshly
reproduced 2026-07-08 (Lean 4.30.0 / mathlib, on the build machine).*

---

## 1. The theorem, as stated in Lean

`Borsuk/Main.lean`:

```lean
/-- Conjecture 3 of arXiv:2508.20009 is false: its d = 2 instance fails, hence the
    conjecture (which asserts all dimensions) fails as stated. -/
theorem conjecture3_false : ¬ Conjecture3For2D := by
  intro hconj
  have h4 : betaZ SA = 2 ^ 2 := by rw [betaZ_SA]; norm_num
  obtain ⟨m, hm⟩ := (hconj SA).mp h4
  exact witnessA_kills_conjecture3.2 m hm

/-- The witness-A kill: β_ℤ(S_A) = 4 = 2², yet conv(S_A) is unimodularly
    equivalent to no cube [0,m]². -/
theorem witnessA_kills_conjecture3 :
    betaZ SA = 4 ∧
      ∀ m : ℕ, ¬ UnimodEquiv (convexHull ℝ (toR '' (SA : Set Z2))) (cube m) := …

/-- Existential form. -/
theorem conjecture3_counterexample :
    ∃ S : Finset Z2, betaZ S = 2 ^ 2 ∧
      ∀ m : ℕ, ¬ UnimodEquiv (convexHull ℝ (toR '' (S : Set Z2))) (cube m) := …
```

Witness: `SA = {(0,0), (1,0), (0,1), (3,5)} ⊆ ℤ²`. Refuting the d = 2 instance
refutes the all-dimensions conjecture.

---

## 2. English gloss of every definition in the statement's dependency chain

Walking outward from `conjecture3_false`. All definitions live in `Borsuk/Defs.lean`
(marked FROZEN), each docstring-pinned to the verbatim arXiv v1 LaTeX. The Lean
kernel checks the *proofs*; faithfulness of these *definitions* to the paper is the
one thing it cannot check, so each docstring quotes the paper and justifies the
encoding. Bottoms out in mathlib bedrock (`Set.ncard`, `Finpartition`, `sInf`,
`convexHull`, `segment`, `Int.gcd`).

- **`Conjecture3For2D : Prop`** — the d = 2 instance of the printed conjecture:
  `∀ S : Finset Z2, (betaZ S = 2^2 ↔ ∃ m : ℕ, UnimodEquiv (convexHull ℝ (toR '' S)) (cube m))`.
  `conjecture3_false` proves its negation.
- **`Z2 := ℤ × ℤ`, `R2 := ℝ × ℝ`** — the lattice ℤ² and plane ℝ² (product module
  structure = standard plane). **`toR : Z2 → R2`** — coordinatewise `Int.cast`, the
  injective inclusion ℤ² ↪ ℝ² (`toR_injective`). A **bounded** set `S ⊂ ℤ²` is
  encoded as `Finset Z2`: bounded subsets of ℤ² are exactly the finite ones (and
  the 4-point witness is bounded under any reading, so the encoding is safe).
- **`betaZ S : ℕ`** — the **lattice Borsuk number** `β_ℤ(S)`. Paper Def 1.3: "the
  smallest number of subsets into which S can be partitioned such that each subset
  has strictly smaller lattice diameter than diam_ℤ(S)."
  `betaZ S := sInf {n | ∃ P : Finpartition S, IsBorsukPartition S P ∧ P.parts.card = n}`.
  `sInf` is mathlib's infimum on ℕ (bedrock). Degenerate-case audit (∅/singleton give
  junk value 0 ≠ 2², never easing the refutation) is in the Defs.lean docstring.
- **`Finpartition S`** — mathlib: pairwise-disjoint nonempty parts whose sup is `S`
  (the standard notion of a set partition).
- **`IsBorsukPartition S P := ∀ p ∈ P.parts, latticeDiam p < latticeDiam S`** — every
  part strictly shrinks the diameter.
- **`latticeDiam S : ℕ`** — Paper Def 1.1: `ldiam(S) = max_{x,y ∈ S∩ℤ^d} |conv({x,y})∩ℤ^d| − 1`.
  `latticeDiam S := S.sup (fun x => S.sup (fun y => latticeLength x y))` (double
  `Finset.sup`).
- **`latticeLength x y : ℕ`** — Paper §4.2: `f(x,y) = nvol([x,y]) = |[x,y]∩ℤ^d| − 1`.
  `latticeLength x y := (segLatticePts x y).ncard - 1`.
- **`segLatticePts x y : Set Z2`** — `{p : Z2 | toR p ∈ segment ℝ (toR x) (toR y)}`,
  the lattice points on the closed segment `[x,y]`. Faithfulness bridge
  `segLatticePts_eq_pullback_convexHull` **proves** (not assumes) this equals the
  paper's `[x,y] := conv({x,y})`: mathlib `segment ℝ a b = convexHull ℝ {a,b}`.
  `Set.ncard` = cardinality of a finite set (bedrock; 0 on infinite sets, but every
  set counted here is proved finite).
- **`UnimodEquiv P Q : Prop`** — Paper Notation: "P and Q are unimodularly equivalent
  if there is a unimodular `A ∈ GL(d,ℤ)` and `t ∈ ℤ^d` with `P = AQ + t`."
  `UnimodEquiv P Q := ∃ φ : UnimodMap, φ.realMap '' Q = P`.
- **`UnimodMap`** — a 2×2 integer matrix `a b c d` + translation `t1 t2` with
  `det_eq : a*d − b*c = 1 ∨ = −1` (over ℤ, invertible ⟺ det is a unit ⟺ det = ±1;
  this is `GL(2,ℤ)`). `realMap`/`intMap` are the action `p ↦ Ap + t` on ℝ²/ℤ²;
  `realMap_toR` proves it is lattice-preserving.
- **`cube m : Set R2`** — the d-cube `[0,m]²`: `{p | 0 ≤ p.1 ≤ m ∧ 0 ≤ p.2 ≤ m}`.
- **`convexHull ℝ (toR '' S)`** — mathlib convex hull of the image of `S` in ℝ² =
  the paper's `conv(S)`.
- **`Primitive v := Int.gcd v.1 v.2 = 1`** — Paper Notation: a vector is primitive
  iff its coordinate gcd is 1 (used in the β_ℤ computation via `Borsuk/SegmentGcd.lean`).

**Why the witness kills it** (`Borsuk/Main.lean` docstring): all six pairwise
differences of `SA` are primitive ⇒ `latticeDiam SA = 1` ⇒ every Borsuk partition
needs singleton parts ⇒ `betaZ SA = 4 = 2²`; but `|conv(SA) ∩ ℤ²| = 7`
(`latticeCount_hullSA`), unimodular maps preserve lattice-point count, and
`|[0,m]² ∩ ℤ²| = (m+1)²` is never 7 — so `conv(SA)` is equivalent to no cube. The
"only if" direction of the iff fails.

---

## 3. Source claim (verbatim) → formal statement bridge

Paper: A. E. Brose, J. A. De Loera, G. López-Campos, A. J. Torres, *On Lattice
Diameter Segments and A Discrete Borsuk Partition Problem*, arXiv:2508.20009v1
(27 Aug 2025), §4.2. **Conjecture 3**, verbatim from the arXiv LaTeX source
(`paper/sections/Borsuk.tex` line 76):

> *"Let S ⊂ ℤ^d be a bounded set. Then β_ℤ(S) = 2^d if and only if conv(S) is
> unimodularly equivalent to a d-cube [0,m]^d for any m ∈ ℕ."*

**Bridge.** `S ⊂ ℤ^d` bounded ↦ `S : Finset Z2` (finite = bounded, d = 2);
`β_ℤ(S) = 2^d` ↦ `betaZ S = 2 ^ 2`; `conv(S)` ↦ `convexHull ℝ (toR '' S)`;
"unimodularly equivalent to a d-cube `[0,m]^d` for any `m`" ↦
`∃ m : ℕ, UnimodEquiv … (cube m)` ("for any m" reads as "for some m", since one
polytope fits one cube size; the refutation in fact proves `∀ m, ¬ equiv`, which
negates the RHS under either reading). Refuting d = 2 refutes the all-d conjecture.
The whole iff is `Conjecture3For2D`; `conjecture3_false : ¬ Conjecture3For2D` is the
verbatim negation. Prior status: arXiv:2508.20009 was v1-only, conjecture open
(STATUS.md §4).

---

## 4. Small-n / concrete validation (definitions need no trust)

The witness arithmetic is checked concretely in `Borsuk/Smoke.lean` (built as part
of the library, kernel `decide`, no `native_decide`):

- `SA_pairwise_differences_primitive` — all six pairwise differences of `SA` are
  primitive (gcd = 1) — the input to `latticeDiam SA = 1`.
- `card_Icc_int`, `seven_not_square` / `succ_sq_ne_seven` — `(m+1)² ≠ 7` for all `m`,
  the arithmetic core of "hull has 7 points, cube has a perfect square of points".

The substantive counts are full theorems, not just examples: `latticeDiam_SA`
(= 1), `betaZ_SA` (= 4), `latticeCount_hullSA` (= 7), `latticeCount_cube`
(= (m+1)²). See §5 — each is in the axiom audit.

---

## 5. Axiom audit (rerun fresh this pass — exit 0)

`lake env lean scripts/CheckAxioms.lean`, 2026-07-08, verbatim output:

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

Only the standard mathlib triple `[propext, Classical.choice, Quot.sound]` (or less)
— **no `sorryAx`, no extra axioms.** A grep for `sorry`/`admit` over `Borsuk/*.lean`
matches only comments; no `axiom`/`native_decide`/`unsafe`/`partial def` anywhere.

---

## 6. One command that rebuilds + re-audits

Toolchain pinned by `lean-toolchain` (`leanprover/lean4:v4.30.0`); needs
`elan`/`lake` on PATH (`%USERPROFILE%\.elan\bin`).

```
cd problems\p3-moonshot\borsuk\lean
lake build                                 && ^
lake env lean scripts\CheckAxioms.lean
```

Expect: `Build completed successfully (8483 jobs).`, exit 0, no warnings, then the
16 axiom lines of §5 (in particular `Borsuk.conjecture3_false` must appear with only
the standard triple). Incremental build is a no-op with the `.lake` cache present;
a cold first build compiles mathlib and can take hours (pinned by `lean-toolchain`).
**Build reproduced green this pass (8483 jobs, exit 0).**
