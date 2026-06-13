/-
Smoke test: validates the toolchain + mathlib end-to-end.

Exercises the APIs the real development will lean on:
* `Int.gcd` and `decide` over bounded integer data (primitivity of difference
  vectors of witness A from the disproof of Conjecture 3 of arXiv:2508.20009),
* `Finset.Icc` cardinality over `ℤ` (the `(m+1)^d` cube lattice-point count),
* `convexHull` over `ℝ` (the hull machinery for the H-representation step).
-/
import Mathlib

namespace Borsuk.Smoke

/-- Witness A from the disproof: `S = {(0,0), (1,0), (0,1), (3,5)} ⊆ ℤ²`. -/
def SA : List (ℤ × ℤ) := [(0, 0), (1, 0), (0, 1), (3, 5)]

/-- All pairwise differences of distinct points of witness A are primitive
vectors (gcd of coordinates is 1).  This is the key computation behind
`diam_ℤ(S_A) = 1` and hence `β_ℤ(S_A) = 4`. -/
theorem SA_pairwise_differences_primitive :
    ∀ p ∈ SA, ∀ q ∈ SA, p ≠ q → Int.gcd (q.1 - p.1) (q.2 - p.2) = 1 := by
  decide

/-- `|[0, m] ∩ ℤ| = m + 1` — the 1-dimensional ingredient of the
`(m+1)^d` lattice-point count of the cube `[0,m]^d`. -/
theorem card_Icc_int (m : ℕ) : (Finset.Icc (0 : ℤ) (m : ℤ)).card = m + 1 := by
  rw [Int.card_Icc]
  omega

/-- The convex-hull API from mathlib is available and usable. -/
example : ((0, 0) : ℝ × ℝ) ∈ convexHull ℝ {((0, 0) : ℝ × ℝ)} :=
  subset_convexHull ℝ _ (Set.mem_singleton _)

/-- `7` is not a perfect square — the arithmetic heart of the witness-A
contradiction (`|conv(S_A) ∩ ℤ²| = 7 ≠ (m+1)²`). -/
theorem seven_not_square (n : ℕ) : n * n ≠ 7 := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> decide
  · have h9 : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
    intro h
    rw [h] at h9
    exact absurd h9 (by decide)

end Borsuk.Smoke
