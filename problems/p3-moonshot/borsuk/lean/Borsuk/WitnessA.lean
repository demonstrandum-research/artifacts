/-
# Borsuk/WitnessA.lean — witness A and `β_ℤ(S_A) = 4`  [WORK PACKAGE 2]

The counterexample set

  `S_A = {(0,0), (1,0), (0,1), (3,5)} ⊆ ℤ²`.

All six pairwise differences are primitive vectors, so every pair of distinct
points is at lattice length exactly `1` (via `latticeLength_eq_one_iff` from
Package 1).  Hence `diam_ℤ(S_A) = 1`; every part of a Borsuk partition must
have lattice diameter `0`, i.e. be a singleton (any two distinct lattice points
have `f ≥ 1`); so a Borsuk partition has exactly `|S_A| = 4` parts, and the
partition into singletons achieves it: `β_ℤ(S_A) = 4 = 2²`.

## Proof plan (for the package owner)

* `latticeDiam_SA`: upper bound — `Finset.sup_le` twice; for `x = y` use
  `latticeLength_self`; for `x ≠ y` rewrite with `latticeLength_eq_gcd` and
  discharge the six gcd computations with `decide` (cf. `SA_pairwise_primitive`).
  Lower bound — exhibit one pair, e.g. `latticeLength (0,0) (1,0) = 1` via
  `latticeLength_eq_gcd`, and `Finset.le_sup` twice.
* `betaZ_eq_card_of_latticeDiam_eq_one`:
  - every Borsuk partition `P` of `S` has all parts of diameter `0 < 1`;
    a part `p` with two distinct elements `a ≠ b` has
    `latticeDiam p ≥ latticeLength a b ≥ 1` (`one_le_latticeLength_of_ne`,
    `Finset.le_sup`), contradiction; parts are nonempty
    (`Finpartition.not_bot_mem`, `Finset.bot_eq_empty`), so each part is a
    singleton, `p.card = 1` (`Finset.card_eq_one`).
  - therefore `P.parts.card = ∑ p ∈ P.parts, p.card = S.card`
    (`Finset.card_eq_sum_ones` / `Finpartition.sum_card_parts`).
  - existence: the discrete partition into singletons.  mathlib: `⊥` in the
    `OrderBot (Finpartition S)` instance is the partition into singletons —
    see `Finpartition.parts_bot` / `Finpartition.card_bot`
    (`(⊥ : Finpartition S).parts.card = S.card`) and
    `Finpartition.mem_bot_iff`; its parts are singletons, of diameter `0`
    (`latticeDiam_singleton`), and `0 < 1`.
  - conclude `{n | ∃ P, IsBorsukPartition S P ∧ P.parts.card = n} = {S.card}`,
    and `sInf {S.card} = S.card` (`csInf_singleton`), or use
    `Nat.sInf_le` + `le_csInf`/`Nat.sInf_mem` for the two inequalities.

ONLY the lemmas marked `sorry` may be edited; do not change any statement or
definition.
-/
import Borsuk.SegmentGcd

namespace Borsuk

/-- **Witness A**: `S_A = {(0,0), (1,0), (0,1), (3,5)} ⊆ ℤ²`.  A bounded
(finite) subset of `ℤ²` with `β_ℤ(S_A) = 2²` whose convex hull is not
unimodularly equivalent to any square `[0,m]²`. -/
def SA : Finset Z2 := {(0, 0), (1, 0), (0, 1), (3, 5)}

@[simp] theorem SA_card : SA.card = 4 := by decide

/-- `S_A` is bounded (explicitly, coordinatewise by `5`) — the hypothesis
"bounded set" of Conjecture 3, recorded for the record over and above
finiteness. -/
theorem SA_bounded : ∀ p ∈ SA, |p.1| ≤ 5 ∧ |p.2| ≤ 5 := by decide

/-- All six pairwise differences of distinct points of `S_A` are primitive
vectors.  (`(3,5) − (0,0) = (3,5)`, `(3,5) − (1,0) = (2,5)`,
`(3,5) − (0,1) = (3,4)`, `(1,0) − (0,0) = (1,0)`, `(0,1) − (0,0) = (0,1)`,
`(0,1) − (1,0) = (−1,1)` — all have coprime coordinates.) -/
theorem SA_pairwise_primitive :
    ∀ p ∈ SA, ∀ q ∈ SA, p ≠ q → Primitive (q - p) := by decide

/-- `diam_ℤ(S_A) = 1`: every pair of distinct points of `S_A` is at lattice
length exactly `1` (primitive difference), and `S_A` has at least two points. -/
theorem latticeDiam_SA : latticeDiam SA = 1 := by
  unfold latticeDiam
  apply le_antisymm
  · -- Upper bound: every pair has lattice length ≤ 1.
    apply Finset.sup_le
    intro x hx
    apply Finset.sup_le
    intro y hy
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · rw [latticeLength_eq_gcd]
      have hprim := SA_pairwise_primitive x hx y hy hxy
      unfold Primitive at hprim
      simp only [Prod.fst_sub, Prod.snd_sub] at hprim
      exact le_of_eq hprim
  · -- Lower bound: the pair `(0,0), (1,0)` has lattice length `1`.
    have h1 : ((0, 0) : Z2) ∈ SA := by decide
    have h2 : ((1, 0) : Z2) ∈ SA := by decide
    have hlen : latticeLength (0, 0) (1, 0) = 1 := by
      rw [latticeLength_eq_gcd]
      decide
    calc (1 : ℕ) = latticeLength (0, 0) (1, 0) := hlen.symm
      _ ≤ SA.sup fun y => latticeLength (0, 0) y := Finset.le_sup h2
      _ ≤ SA.sup fun x => SA.sup fun y => latticeLength x y :=
          Finset.le_sup (f := fun x => SA.sup fun y => latticeLength x y) h1

/-- **The singleton-parts argument.**  If `diam_ℤ(S) = 1` then every part of a
Borsuk partition must be a singleton (two distinct lattice points already have
`f ≥ 1`), so the minimum number of parts is exactly `|S|`:
`β_ℤ(S) = |S|`. -/
theorem betaZ_eq_card_of_latticeDiam_eq_one
    (S : Finset Z2) (h : latticeDiam S = 1) :
    betaZ S = S.card := by
  -- Step 1: every Borsuk partition of `S` has singleton parts, hence `S.card` parts.
  have hpart : ∀ P : Finpartition S, IsBorsukPartition S P → P.parts.card = S.card := by
    intro P hP
    have hcard1 : ∀ p ∈ P.parts, p.card = 1 := by
      intro p hp
      have hlt := hP p hp
      rw [h] at hlt
      refine le_antisymm ?_ (Finset.one_le_card.2 (P.nonempty_of_mem_parts hp))
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      have h1 : 1 ≤ latticeLength a b := one_le_latticeLength_of_ne hab
      have h2 : latticeLength a b ≤ p.sup fun y => latticeLength a y := Finset.le_sup hb
      have h3 : (p.sup fun y => latticeLength a y) ≤ latticeDiam p :=
        Finset.le_sup (f := fun x => p.sup fun y => latticeLength x y) ha
      omega
    calc P.parts.card = ∑ p ∈ P.parts, 1 := Finset.card_eq_sum_ones _
      _ = ∑ p ∈ P.parts, p.card := Finset.sum_congr rfl fun p hp => (hcard1 p hp).symm
      _ = S.card := P.sum_card_parts
  -- Step 2: the discrete partition `⊥` (into singletons) is a Borsuk partition
  -- with `S.card` parts, so `S.card` is achievable.
  have hbot : IsBorsukPartition S ⊥ := by
    intro p hp
    rw [Finpartition.mem_bot_iff] at hp
    obtain ⟨a, -, rfl⟩ := hp
    rw [latticeDiam_singleton, h]
    exact Nat.zero_lt_one
  have hmem : S.card ∈
      {n : ℕ | ∃ P : Finpartition S, IsBorsukPartition S P ∧ P.parts.card = n} :=
    ⟨⊥, hbot, Finpartition.card_bot S⟩
  -- Step 3: the achievable-count set is therefore `{S.card}`, and its `sInf` is `S.card`.
  obtain ⟨P, hP, hPcard⟩ := Nat.sInf_mem ⟨S.card, hmem⟩
  unfold betaZ
  rw [← hPcard]
  exact hpart P hP

/-- **First half of the disproof:** `β_ℤ(S_A) = 4 = 2²`. -/
theorem betaZ_SA : betaZ SA = 4 := by
  rw [betaZ_eq_card_of_latticeDiam_eq_one SA latticeDiam_SA]
  exact SA_card

/-- `conv(S_A) ⊆ ℝ²` — the convex hull of witness A.  (An `abbrev` so that
statements about `hullSA` are definitionally statements about
`convexHull ℝ (toR '' S_A)`.) -/
abbrev hullSA : Set R2 := convexHull ℝ (toR '' (SA : Set Z2))

end Borsuk
