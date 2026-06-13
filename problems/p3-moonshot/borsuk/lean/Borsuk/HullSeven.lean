/-
# Borsuk/HullSeven.lean — `|conv(S_A) ∩ ℤ²| = 7`  [WORK PACKAGE 3]

The lattice-point count of the hull of witness A.  `conv(S_A)` is the convex
quadrilateral with vertices (counterclockwise) `(0,0), (1,0), (3,5), (0,1)`;
its H-representation is the four halfspaces

  `0 ≤ x`,  `0 ≤ y`,  `5x − 2y ≤ 5`,  `3y − 4x ≤ 3`,

(edges `x = 0` through `(0,1),(0,0)`; `y = 0` through `(0,0),(1,0)`;
`5x − 2y = 5` through `(1,0),(3,5)`; `3y − 4x = 3` through `(0,1),(3,5)`),
and it contains exactly 7 lattice points:

  `(0,0), (1,0), (0,1), (1,1), (1,2), (2,3), (3,5)`.

## Proof plan (for the package owner)

* `hullSA_subset_halfspaces` (hull ⊆ H-representation): the intersection of the
  four halfspaces is convex (`convex_halfspace_le`, `convex_halfspace_ge` with
  the linear functionals `p ↦ p.1`, `p ↦ p.2`, `p ↦ 5*p.1 − 2*p.2`,
  `p ↦ 3*p.2 − 4*p.1`; `IsLinearMap` is immediate; intersections via
  `Convex.inter`) and contains the four points of `S_A` (16 numeric checks,
  `norm_num`), so `convexHull_min` applies.
* `hullSeven_subset_hullSA`: the four vertices are in the hull by
  `subset_convexHull`.  The three interior points have explicit convex
  combination certificates over `S_A`:
    `(1,1) = (2/5)·(0,0) + (2/5)·(1,0) + (1/5)·(3,5)`
    `(1,2) = (1/3)·(0,0) + (1/3)·(0,1) + (1/3)·(3,5)`
    `(2,3) = (1/5)·(0,0) + (1/5)·(1,0) + (3/5)·(3,5)`
  Route: `convexHull ℝ (toR '' SA)` is convex (`convex_convexHull`); use
  `Convex.add_smul_le_mem`-style API, or directly
  `Finset.centerMass_mem_convexHull`, or two nested `segment` memberships
  (`Convex.segment_subset`); finish coordinates with `norm_num`.
* `halfspace_lattice_enum` (integer enumeration): from the four integer
  inequalities, `omega` derives the 7-fold disjunction after `simp [hullSeven]`
  turns the goal `p ∈ hullSeven` into component equalities
  (`Finset.mem_insert`, `Prod.ext_iff`, `Prod.mk.injEq`).
  (Bound chase: `x ≥ 0`, `y ≥ 0`, `2y ≥ 5x − 5`, `3y ≤ 4x + 3` force
  `15x − 15 ≤ 6y ≤ 8x + 6`, so `x ≤ 3`, and then `y` is pinned per `x`.)

ONLY the lemmas marked `sorry` may be edited; do not change any statement or
definition.
-/
import Borsuk.WitnessA

namespace Borsuk

/-- The 7 lattice points of `conv(S_A)`. -/
def hullSeven : Finset Z2 :=
  {(0, 0), (1, 0), (0, 1), (1, 1), (1, 2), (2, 3), (3, 5)}

@[simp] theorem hullSeven_card : hullSeven.card = 7 := by decide

/-- `S_A ⊆ hullSeven` (sanity check, proved by computation). -/
theorem SA_subset_hullSeven : SA ⊆ hullSeven := by decide

/-- H-representation, soundness half: the hull lies in the four halfspaces.
Each halfspace is convex and contains all four points of `S_A`, so
`convexHull_min` applies. -/
theorem hullSA_subset_halfspaces :
    hullSA ⊆ {p : R2 |
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 5 * p.1 - 2 * p.2 ≤ 5 ∧ 3 * p.2 - 4 * p.1 ≤ 3} := by
  apply convexHull_min
  · -- the four points of `S_A` satisfy the four inequalities (16 numeric checks)
    rintro q ⟨p, hp, rfl⟩
    rw [Finset.mem_coe] at hp
    simp only [SA, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_setOf_eq, toR_fst, toR_snd] <;> norm_num
  · -- the intersection of the four halfspaces is convex
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := mul_nonneg ha hp1
      have := mul_nonneg hb hq1
      linarith
    · have := mul_nonneg ha hp2
      have := mul_nonneg hb hq2
      linarith
    · have := mul_le_mul_of_nonneg_left hp3 ha
      have := mul_le_mul_of_nonneg_left hq3 hb
      linarith
    · have := mul_le_mul_of_nonneg_left hp4 ha
      have := mul_le_mul_of_nonneg_left hq4 hb
      linarith

/-- Completeness half: each of the 7 candidate lattice points lies in the hull
(explicit convex-combination certificates; see the file header). -/
theorem hullSeven_subset_hullSA : ∀ p ∈ hullSeven, toR p ∈ hullSA := by
  -- the four vertices are in the hull
  have hSA : ∀ p ∈ SA, toR p ∈ hullSA := fun p hp =>
    subset_convexHull ℝ _ ⟨p, Finset.mem_coe.mpr hp, rfl⟩
  have h00 : toR (0, 0) ∈ hullSA := hSA _ (by decide)
  have h10 : toR (1, 0) ∈ hullSA := hSA _ (by decide)
  have h01 : toR (0, 1) ∈ hullSA := hSA _ (by decide)
  have h35 : toR (3, 5) ∈ hullSA := hSA _ (by decide)
  have hc : Convex ℝ hullSA := convex_convexHull ℝ _
  -- midpoints of two edges at the origin
  have hmx : ((1 : ℝ) / 2) • toR (0, 0) + ((1 : ℝ) / 2) • toR (1, 0) ∈ hullSA :=
    hc h00 h10 (by norm_num) (by norm_num) (by norm_num)
  have hmy : ((1 : ℝ) / 2) • toR (0, 0) + ((1 : ℝ) / 2) • toR (0, 1) ∈ hullSA :=
    hc h00 h01 (by norm_num) (by norm_num) (by norm_num)
  -- (1,1) = (4/5)·(1/2, 0) + (1/5)·(3,5)
  have h11 : toR (1, 1) ∈ hullSA := by
    have h := hc hmx h35
      (by norm_num : (0 : ℝ) ≤ 4 / 5) (by norm_num : (0 : ℝ) ≤ 1 / 5) (by norm_num)
    have heq : ((4 : ℝ) / 5) • (((1 : ℝ) / 2) • toR (0, 0) + ((1 : ℝ) / 2) • toR (1, 0))
        + ((1 : ℝ) / 5) • toR (3, 5) = toR (1, 1) := by
      simp only [toR, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, smul_eq_mul]
      norm_num
    rwa [heq] at h
  -- (1,2) = (2/3)·(0, 1/2) + (1/3)·(3,5)
  have h12 : toR (1, 2) ∈ hullSA := by
    have h := hc hmy h35
      (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
    have heq : ((2 : ℝ) / 3) • (((1 : ℝ) / 2) • toR (0, 0) + ((1 : ℝ) / 2) • toR (0, 1))
        + ((1 : ℝ) / 3) • toR (3, 5) = toR (1, 2) := by
      simp only [toR, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, smul_eq_mul]
      norm_num
    rwa [heq] at h
  -- (2,3) = (2/5)·(1/2, 0) + (3/5)·(3,5)
  have h23 : toR (2, 3) ∈ hullSA := by
    have h := hc hmx h35
      (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num)
    have heq : ((2 : ℝ) / 5) • (((1 : ℝ) / 2) • toR (0, 0) + ((1 : ℝ) / 2) • toR (1, 0))
        + ((3 : ℝ) / 5) • toR (3, 5) = toR (2, 3) := by
      simp only [toR, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, smul_eq_mul]
      norm_num
    rwa [heq] at h
  intro p hp
  simp only [hullSeven, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h00
  · exact h10
  · exact h01
  · exact h11
  · exact h12
  · exact h23
  · exact h35

/-- Integer enumeration of the H-representation: an integer point satisfying
the four halfspace inequalities is one of the 7 points. -/
theorem halfspace_lattice_enum (p : Z2)
    (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2)
    (h3 : 5 * p.1 - 2 * p.2 ≤ 5) (h4 : 3 * p.2 - 4 * p.1 ≤ 3) :
    p ∈ hullSeven := by
  obtain ⟨x, y⟩ := p
  dsimp only at h1 h2 h3 h4
  simp only [hullSeven, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- The lattice points of `conv(S_A)` are exactly `hullSeven`. -/
theorem mem_hullSA_iff (p : Z2) : toR p ∈ hullSA ↔ p ∈ hullSeven := by
  constructor
  · intro hp
    obtain ⟨h1, h2, h3, h4⟩ := hullSA_subset_halfspaces hp
    simp only [toR_fst, toR_snd] at h1 h2 h3 h4
    refine halfspace_lattice_enum p ?_ ?_ ?_ ?_
    · exact_mod_cast h1
    · exact_mod_cast h2
    · exact_mod_cast h3
    · exact_mod_cast h4
  · exact hullSeven_subset_hullSA p

/-- **Second pillar of the disproof:** `|conv(S_A) ∩ ℤ²| = 7`. -/
theorem latticeCount_hullSA : latticeCount hullSA = 7 := by
  have h : {p : Z2 | toR p ∈ hullSA} = (hullSeven : Set Z2) := by
    ext p
    simpa using mem_hullSA_iff p
  unfold latticeCount
  rw [h, Set.ncard_coe_finset, hullSeven_card]

end Borsuk
