/-
# Borsuk/SegmentGcd.lean — the segment-lattice-point / gcd bridge  [WORK PACKAGE 1]

The one genuinely mathematical lemma of the development:

  `|[x,y] ∩ ℤ²| = gcd(y₁ − x₁, y₂ − x₂) + 1`

equivalently `f(x,y) = latticeLength x y = Int.gcd (y-x).1 (y-x).2`.

This is the elementary Bezout fact: writing `v = y − x = g • u` with
`g = gcd(v) ∈ ℕ` and `u` primitive, the lattice points on the segment `[x,y]`
are exactly `x, x + u, x + 2u, …, x + gu`.

## Proof plan (for the package owner)

Main decomposition: `segLatticePts_eq_image` below.

* `⊇` (easy): `x + k • u` for `k ∈ [0,g]` lies on the segment — it is the convex
  combination with parameter `t = k/g` (handle `g = 0`, i.e. `x = y`, separately:
  then the image is `{x}` because `Set.Icc 0 0 = {0}` and `primVec` smul'd by 0
  vanishes).
* `⊆` (Bezout): a point `p` on the segment satisfies
  `toR p = (1−t) • toR x + t • toR y` for some `t ∈ [0,1]` (mathlib: `segment`
  membership), so `toR (p − x) = t • toR (y − x) = (t*g) • toR u`.
  Both coordinates of `(t*g) • toR u` are integers and `u` is primitive:
  Bezout (`Int.gcd_eq_gcd_ab : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b`)
  gives integers `α β` with `α * u.1 + β * u.2 = 1`, hence
  `t * g = α * (t*g*u.1) + β * (t*g*u.2)` is an integer `k`; from `0 ≤ t ≤ 1`
  conclude `0 ≤ k ≤ g`, and `p = x + k • u`.
* Cardinality: the map `k ↦ x + k • u` is injective for `u ≠ 0`
  (`g ≠ 0` case), and `(Set.Icc (0:ℤ) g).ncard = g + 1`
  (`Set.Icc` over `ℤ` is `↑(Finset.Icc 0 g)` via `Finset.coe_Icc`;
  then `Set.ncard_coe_finset` and `Int.card_Icc`).

Useful mathlib API: `segment_eq_image'` / `segment_eq_image` (parametrize the
segment), `Int.gcd_eq_gcd_ab`, `Int.gcd_dvd_left/right` (to define `u` via
exact division and recover `v = g • u`), `Int.ediv_mul_cancel`,
`Set.ncard_image_of_injective`, `Set.ncard_coe_Finset`, `Int.card_Icc`,
`Int.toNat_of_nonneg`.

ONLY the lemmas marked `sorry` may be edited; do not change any statement.
-/
import Borsuk.Defs

namespace Borsuk

/-- The primitive direction vector of the segment from `x` to `y`:
`(y − x) / gcd(y − x)` by exact integer division.  For `x = y` (gcd `0`) integer
division by `0` returns `0`, and every statement below remains true. -/
def primVec (x y : Z2) : Z2 :=
  ((y.1 - x.1) / (Int.gcd (y.1 - x.1) (y.2 - x.2) : ℤ),
   (y.2 - x.2) / (Int.gcd (y.1 - x.1) (y.2 - x.2) : ℤ))

/-- The exact-division identity `g • primVec = y − x`. -/
theorem gcd_smul_primVec (x y : Z2) :
    (Int.gcd (y.1 - x.1) (y.2 - x.2) : ℤ) • primVec x y = (y.1 - x.1, y.2 - x.2) := by
  have h1 : (Int.gcd (y.1 - x.1) (y.2 - x.2) : ℤ) ∣ y.1 - x.1 := Int.gcd_dvd_left _ _
  have h2 : (Int.gcd (y.1 - x.1) (y.2 - x.2) : ℤ) ∣ y.2 - x.2 := Int.gcd_dvd_right _ _
  unfold primVec
  apply Prod.ext
  · simpa using Int.mul_ediv_cancel' h1
  · simpa using Int.mul_ediv_cancel' h2

/-- `primVec x y` is primitive whenever `x ≠ y`. -/
theorem primVec_primitive {x y : Z2} (h : x ≠ y) : Primitive (primVec x y) := by
  have hg : 0 < Int.gcd (y.1 - x.1) (y.2 - x.2) := by
    rcases Nat.eq_zero_or_pos (Int.gcd (y.1 - x.1) (y.2 - x.2)) with h0 | h1
    · exfalso
      rw [Int.gcd_eq_zero_iff] at h0
      exact h (Prod.ext (by omega) (by omega))
    · exact h1
  unfold Primitive primVec
  exact Int.gcd_div_gcd_div_gcd hg

/-- **Structure of the lattice points on a segment**: they are exactly
`x + k • u`, `0 ≤ k ≤ g`, where `u = primVec x y` and `g = gcd(y − x)`. -/
theorem segLatticePts_eq_image (x y : Z2) :
    segLatticePts x y =
      (fun k : ℤ => x + k • primVec x y) ''
        Set.Icc (0 : ℤ) (Int.gcd (y.1 - x.1) (y.2 - x.2) : ℤ) := by
  by_cases hxy : x = y
  · -- degenerate case `x = y`: both sides are `{x}`
    subst hxy
    have hg : (Int.gcd (x.1 - x.1) (x.2 - x.2) : ℤ) = 0 := by simp
    rw [segLatticePts_self, hg, Set.Icc_self, Set.image_singleton]
    simp
  · -- main case: abbreviate `g` and `u`, collect the arithmetic facts
    set g : ℕ := Int.gcd (y.1 - x.1) (y.2 - x.2) with hgdef
    set u : Z2 := primVec x y with hudef
    have hgu := gcd_smul_primVec x y
    rw [← hgdef, ← hudef] at hgu
    have hgu1 : (g : ℤ) * u.1 = y.1 - x.1 := by
      have := congrArg Prod.fst hgu
      simpa using this
    have hgu2 : (g : ℤ) * u.2 = y.2 - x.2 := by
      have := congrArg Prod.snd hgu
      simpa using this
    have hgpos : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h0 | h1
      · exfalso
        rw [hgdef, Int.gcd_eq_zero_iff] at h0
        exact hxy (Prod.ext (by omega) (by omega))
      · exact h1
    have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
    have hgne : (g : ℝ) ≠ 0 := ne_of_gt hgR
    have c1 : (g : ℝ) * (u.1 : ℝ) = (y.1 : ℝ) - (x.1 : ℝ) := by exact_mod_cast hgu1
    have c2 : (g : ℝ) * (u.2 : ℝ) = (y.2 : ℝ) - (x.2 : ℝ) := by exact_mod_cast hgu2
    ext p
    constructor
    · -- ⊆ : Bezout direction
      intro hp
      have hp' : toR p ∈ segment ℝ (toR x) (toR y) := hp
      rw [segment_eq_image'] at hp'
      obtain ⟨θ, hθmem, hθeq⟩ := hp'
      rw [Set.mem_Icc] at hθmem
      obtain ⟨hθ0, hθ1⟩ := hθmem
      have e1 : (x.1 : ℝ) + θ * ((y.1 : ℝ) - (x.1 : ℝ)) = (p.1 : ℝ) := by
        have := congrArg Prod.fst hθeq
        simpa using this
      have e2 : (x.2 : ℝ) + θ * ((y.2 : ℝ) - (x.2 : ℝ)) = (p.2 : ℝ) := by
        have := congrArg Prod.snd hθeq
        simpa using this
      -- Bezout coefficients for the primitive vector `u`
      obtain ⟨a, b, hbez⟩ : ∃ a b : ℤ, u.1 * a + u.2 * b = 1 := by
        refine ⟨Int.gcdA u.1 u.2, Int.gcdB u.1 u.2, ?_⟩
        have hprim : Int.gcd u.1 u.2 = 1 := primVec_primitive hxy
        have h := (Int.gcd_eq_gcd_ab u.1 u.2).symm
        rwa [hprim, Nat.cast_one] at h
      have hbezR : (u.1 : ℝ) * (a : ℝ) + (u.2 : ℝ) * (b : ℝ) = 1 := by exact_mod_cast hbez
      -- the integer parameter `k = a(p₁−x₁) + b(p₂−x₂)`, with `(k : ℝ) = θ·g`
      have hk : ((a * (p.1 - x.1) + b * (p.2 - x.2) : ℤ) : ℝ) = θ * (g : ℝ) := by
        push_cast
        linear_combination (-(a : ℝ)) * e1 - (b : ℝ) * e2 - (a : ℝ) * θ * c1
          - (b : ℝ) * θ * c2 + θ * (g : ℝ) * hbezR
      rw [Set.mem_image]
      refine ⟨a * (p.1 - x.1) + b * (p.2 - x.2), Set.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · -- `0 ≤ k`
        have h0R : (0 : ℝ) ≤ ((a * (p.1 - x.1) + b * (p.2 - x.2) : ℤ) : ℝ) := by
          rw [hk]
          exact mul_nonneg hθ0 (le_of_lt hgR)
        exact_mod_cast h0R
      · -- `k ≤ g`
        have h1R : ((a * (p.1 - x.1) + b * (p.2 - x.2) : ℤ) : ℝ) ≤ (g : ℝ) := by
          rw [hk]
          exact mul_le_of_le_one_left (le_of_lt hgR) hθ1
        exact_mod_cast h1R
      · -- `x + k • u = p`, checked coordinatewise over ℝ then cast down to ℤ
        show x + (a * (p.1 - x.1) + b * (p.2 - x.2)) • u = p
        have q1 : (x.1 : ℝ) + ((a * (p.1 - x.1) + b * (p.2 - x.2) : ℤ) : ℝ) * (u.1 : ℝ)
            = (p.1 : ℝ) := by
          rw [hk]
          linear_combination e1 + θ * c1
        have q2 : (x.2 : ℝ) + ((a * (p.1 - x.1) + b * (p.2 - x.2) : ℤ) : ℝ) * (u.2 : ℝ)
            = (p.2 : ℝ) := by
          rw [hk]
          linear_combination e2 + θ * c2
        have q1' : x.1 + (a * (p.1 - x.1) + b * (p.2 - x.2)) * u.1 = p.1 := by
          exact_mod_cast q1
        have q2' : x.2 + (a * (p.1 - x.1) + b * (p.2 - x.2)) * u.2 = p.2 := by
          exact_mod_cast q2
        apply Prod.ext
        · simpa using q1'
        · simpa using q2'
    · -- ⊇ : `x + k • u` is the convex combination with parameter `k/g`
      rintro ⟨k, hkmem, rfl⟩
      rw [Set.mem_Icc] at hkmem
      obtain ⟨hk0, hkg⟩ := hkmem
      show toR (x + k • u) ∈ segment ℝ (toR x) (toR y)
      rw [segment_eq_image', Set.mem_image]
      refine ⟨(k : ℝ) / (g : ℝ), Set.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · exact div_nonneg (by exact_mod_cast hk0) (le_of_lt hgR)
      · rw [div_le_one hgR]
        exact_mod_cast hkg
      · show toR x + ((k : ℝ) / (g : ℝ)) • (toR y - toR x) = toR (x + k • u)
        have q1 : (x.1 : ℝ) + (k : ℝ) / (g : ℝ) * ((y.1 : ℝ) - (x.1 : ℝ))
            = (x.1 : ℝ) + (k : ℝ) * (u.1 : ℝ) := by
          rw [← c1, ← mul_assoc, div_mul_cancel₀ _ hgne]
        have q2 : (x.2 : ℝ) + (k : ℝ) / (g : ℝ) * ((y.2 : ℝ) - (x.2 : ℝ))
            = (x.2 : ℝ) + (k : ℝ) * (u.2 : ℝ) := by
          rw [← c2, ← mul_assoc, div_mul_cancel₀ _ hgne]
        apply Prod.ext
        · simpa using q1
        · simpa using q2

/-- **KEY LEMMA (the faithfulness bridge):** the number of lattice points on the
closed segment `[x,y]` is `gcd(y − x) + 1`.

Paper-side meaning: `|[x, y] ∩ ℤ²| = gcd(y₁−x₁, y₂−x₂) + 1`, the classical
segment lattice-point count.  Everything downstream consumes `f` only through
this lemma. -/
theorem ncard_segLatticePts (x y : Z2) :
    (segLatticePts x y).ncard = Int.gcd (y.1 - x.1) (y.2 - x.2) + 1 := by
  by_cases hxy : x = y
  · subst hxy
    rw [segLatticePts_self]
    simp
  · rw [segLatticePts_eq_image]
    -- the parametrization `k ↦ x + k • u` is injective because `u ≠ 0`
    have hu : primVec x y ≠ 0 := by
      intro h0
      have hprim : Int.gcd (primVec x y).1 (primVec x y).2 = 1 := primVec_primitive hxy
      rw [h0] at hprim
      simp at hprim
    have hor : (primVec x y).1 ≠ 0 ∨ (primVec x y).2 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu (Prod.ext hcon.1 hcon.2)
    have hinj : Function.Injective (fun k : ℤ => x + k • primVec x y) := by
      intro k₁ k₂ hkk
      have hkk' : x + k₁ • primVec x y = x + k₂ • primVec x y := hkk
      have h' : k₁ • primVec x y = k₂ • primVec x y := add_left_cancel hkk'
      have h1 : k₁ * (primVec x y).1 = k₂ * (primVec x y).1 := by
        have := congrArg Prod.fst h'
        simpa using this
      have h2 : k₁ * (primVec x y).2 = k₂ * (primVec x y).2 := by
        have := congrArg Prod.snd h'
        simpa using this
      rcases hor with hne | hne
      · exact mul_right_cancel₀ hne h1
      · exact mul_right_cancel₀ hne h2
    rw [Set.ncard_image_of_injective _ hinj, ← Finset.coe_Icc, Set.ncard_coe_finset,
      Int.card_Icc]
    omega

/-- `f(x,y) = gcd(y − x)`: the computational form of the lattice length. -/
theorem latticeLength_eq_gcd (x y : Z2) :
    latticeLength x y = Int.gcd (y.1 - x.1) (y.2 - x.2) := by
  unfold latticeLength
  rw [ncard_segLatticePts]
  omega

/-- `f(x,y) = 1` iff the difference vector is primitive. -/
theorem latticeLength_eq_one_iff (x y : Z2) :
    latticeLength x y = 1 ↔ Primitive (y - x) := by
  rw [latticeLength_eq_gcd]
  exact Iff.rfl

/-- Distinct lattice points are at lattice length `≥ 1` (any two distinct points
of `ℤ²` are joined by a segment containing both as lattice points). -/
theorem one_le_latticeLength_of_ne {x y : Z2} (h : x ≠ y) :
    1 ≤ latticeLength x y := by
  rw [latticeLength_eq_gcd]
  rcases Nat.eq_zero_or_pos (Int.gcd (y.1 - x.1) (y.2 - x.2)) with h0 | h1
  · exfalso
    rw [Int.gcd_eq_zero_iff] at h0
    apply h
    have e1 : x.1 = y.1 := by omega
    have e2 : x.2 = y.2 := by omega
    exact Prod.ext e1 e2
  · exact h1

end Borsuk
