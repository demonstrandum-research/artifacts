/-
# Borsuk/Unimodular.lean — unimodular invariance and the cube count  [WORK PACKAGE 4]

Two facts and their combination:

1. Unimodular affine equivalence preserves the number of lattice points of a
   plane set (a unimodular affine map is a bijection of `ℝ²` restricting to a
   bijection of `ℤ²`).
2. `|[0,m]² ∩ ℤ²| = (m+1)²`.

Combined with `(m+1)² ≠ 7` (proved below, no sorry), any plane set with exactly
7 lattice points is unimodularly equivalent to no cube `[0,m]²`.

## Proof plan (for the package owner)

* Explicit inverse: for `φ` with `ε := a*d − b*c ∈ {1,−1}` (note `ε * ε = 1`,
  so `1/ε = ε` over `ℤ`), the inverse affine map has matrix
  `ε * [[d, −b], [−c, a]]` and translation `−A⁻¹t`; define it as a private
  `UnimodMap` (its determinant is `ε² * ε = ε`, again `±1`) and verify the two
  composition identities by `rcases φ.det_eq` + `ring_nf`/`nlinarith` or plain
  algebra: from `u = a*x + b*y + t1`, `v = c*x + d*y + t2` one solves
  `x = ε*(d*(u − t1) − b*(v − t2))`, `y = ε*(−c*(u − t1) + a*(v − t2))`.
  This yields `intMap_bijective` (Function.Bijective via explicit two-sided
  inverse, `Function.LeftInverse.injective` etc.) and `realMap_injective`
  (same computation over `ℝ`, or: injectivity alone by solving linearly).
* `UnimodEquiv.latticeCount_eq`: with `h : φ.realMap '' Q = P`, show
  `{p : Z2 | toR p ∈ P} = φ.intMap '' {p : Z2 | toR p ∈ Q}`:
  `⊇` is `UnimodMap.realMap_toR` plus membership chasing; for `⊆`, given
  `toR p = φ.realMap z` with `z ∈ Q`, surjectivity of `intMap` gives `q` with
  `intMap q = p`, then `φ.realMap (toR q) = toR p = φ.realMap z` and
  `realMap_injective` force `z = toR q`.  Conclude with
  `Set.ncard_image_of_injective` (injectivity of `intMap`).
* `latticeCount_cube`: `{p : Z2 | toR p ∈ cube m} = ↑(Finset.Icc (0,0) (m,m))`
  — membership unfolds to the four coordinate inequalities; bridge `ℝ`/`ℤ` with
  `Int.cast_nonneg`, `Int.cast_le` / `push_cast`; `Finset.mem_Icc` on the
  product order (`Prod.mk_le_mk` / `Prod.le_def`).  Then
  `Set.ncard_coe_finset`, `Prod.card_Icc` (the product `Icc` card; if the name
  differs try `Finset.card_Icc` after `Finset.Icc_prod_eq` — in current mathlib
  `Prod.Icc_eq` / `Prod.card_Icc` live in Order/Interval/Finset/Prod or
  similar), and `Int.card_Icc : (Finset.Icc a b).card = (b + 1 - a).toNat`,
  finishing with `omega`/`Int.toNat_of_nonneg` and `pow_two`.

ONLY the lemmas marked `sorry` may be edited; do not change any statement or
definition.
-/
import Borsuk.Defs

namespace Borsuk

namespace UnimodMap

/-- A unimodular affine map restricts to a bijection of the lattice `ℤ²`
("lattice preserving maps", paper Notation §1). -/
theorem intMap_bijective (φ : UnimodMap) : Function.Bijective φ.intMap := by
  -- The square of the determinant `ε := a*d − b*c ∈ {1, −1}` is `1`.
  have hε : (φ.a * φ.d - φ.b * φ.c) * (φ.a * φ.d - φ.b * φ.c) = 1 := by
    rcases φ.det_eq with h | h <;> rw [h] <;> ring
  -- Explicit two-sided inverse `q ↦ ε • A⁻ᵃᵈʲ(q − t)`.
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun q : Z2 =>
      ((φ.a * φ.d - φ.b * φ.c) * (φ.d * (q.1 - φ.t1) - φ.b * (q.2 - φ.t2)),
       (φ.a * φ.d - φ.b * φ.c) * (-φ.c * (q.1 - φ.t1) + φ.a * (q.2 - φ.t2))),
     ?_, ?_⟩
  · -- left inverse: `ψ (φ p) = p`
    rintro ⟨x, y⟩
    simp only [intMap, Prod.mk.injEq]
    constructor
    · linear_combination x * hε
    · linear_combination y * hε
  · -- right inverse: `φ (ψ q) = q`
    rintro ⟨u, v⟩
    simp only [intMap, Prod.mk.injEq]
    constructor
    · linear_combination (u - φ.t1) * hε
    · linear_combination (v - φ.t2) * hε

/-- A unimodular affine map of the plane is injective on `ℝ²`. -/
theorem realMap_injective (φ : UnimodMap) : Function.Injective φ.realMap := by
  -- The determinant squares to `1` already over `ℤ`, hence over `ℝ` by casting.
  have hεZ : (φ.a * φ.d - φ.b * φ.c) * (φ.a * φ.d - φ.b * φ.c) = 1 := by
    rcases φ.det_eq with h | h <;> rw [h] <;> ring
  have hε : ((φ.a : ℝ) * φ.d - (φ.b : ℝ) * φ.c) *
      ((φ.a : ℝ) * φ.d - (φ.b : ℝ) * φ.c) = 1 := by exact_mod_cast hεZ
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩ h
  simp only [realMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  -- linear elimination: `ε·(d·h1 − b·h2)` and `ε·(−c·h1 + a·h2)` recover the
  -- coordinates, using `ε² = 1`.
  have e1 : p1 = q1 := by
    linear_combination (((φ.a : ℝ) * φ.d - (φ.b : ℝ) * φ.c) * φ.d) * h1
      - (((φ.a : ℝ) * φ.d - (φ.b : ℝ) * φ.c) * φ.b) * h2 - (p1 - q1) * hε
  have e2 : p2 = q2 := by
    linear_combination (-(((φ.a : ℝ) * φ.d - (φ.b : ℝ) * φ.c) * φ.c)) * h1
      + (((φ.a : ℝ) * φ.d - (φ.b : ℝ) * φ.c) * φ.a) * h2 - (p2 - q2) * hε
  rw [e1, e2]

end UnimodMap

/-- **Unimodular invariance of the lattice-point count**: if `P = AQ + t` for a
unimodular `A` and integral `t`, then `|P ∩ ℤ²| = |Q ∩ ℤ²|`. -/
theorem UnimodEquiv.latticeCount_eq {P Q : Set R2} (h : UnimodEquiv P Q) :
    latticeCount P = latticeCount Q := by
  obtain ⟨φ, hφ⟩ := h
  -- The lattice points of `P = φ(Q)` are exactly the `intMap`-image of the
  -- lattice points of `Q`.
  have hset : {p : Z2 | toR p ∈ P} = φ.intMap '' {p : Z2 | toR p ∈ Q} := by
    ext p
    constructor
    · intro hp
      rw [← hφ] at hp
      obtain ⟨z, hzQ, hz⟩ := hp
      obtain ⟨q, hq⟩ := φ.intMap_bijective.surjective p
      refine ⟨q, ?_, hq⟩
      have hq' : φ.realMap (toR q) = toR p := by rw [φ.realMap_toR, hq]
      have hz' : z = toR q := φ.realMap_injective (by rw [hq', hz])
      show toR q ∈ Q
      rw [← hz']
      exact hzQ
    · rintro ⟨q, hqQ, rfl⟩
      rw [Set.mem_setOf_eq, ← hφ]
      exact ⟨toR q, hqQ, φ.realMap_toR q⟩
  rw [latticeCount, latticeCount, hset,
    Set.ncard_image_of_injective _ φ.intMap_bijective.injective]

/-- **The cube count**: `|[0,m]² ∩ ℤ²| = (m+1)²`. -/
theorem latticeCount_cube (m : ℕ) : latticeCount (cube m) = (m + 1) ^ 2 := by
  -- The lattice points of `[0,m]²` form the finite box `Icc (0,0) (m,m)` in `ℤ²`.
  have hset : {p : Z2 | toR p ∈ cube m} =
      ↑(Finset.Icc ((0 : ℤ), (0 : ℤ)) ((m : ℤ), (m : ℤ))) := by
    ext ⟨x, y⟩
    simp only [cube, Set.mem_setOf_eq, toR_fst, toR_snd, Finset.coe_Icc,
      Set.mem_Icc, Prod.mk_le_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h3⟩,
             ⟨by exact_mod_cast h2, by exact_mod_cast h4⟩⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      exact ⟨⟨by exact_mod_cast h1, by exact_mod_cast h2⟩,
             ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩⟩
  rw [latticeCount, hset, Set.ncard_coe_finset, Finset.card_Icc_prod]
  simp only [Int.card_Icc]
  have hm : ((m : ℤ) + 1 - 0).toNat = m + 1 := by omega
  rw [hm, sq]

/-- `7` is not a positive perfect square — the arithmetic heart of the
contradiction. -/
theorem succ_sq_ne_seven (m : ℕ) : (m + 1) ^ 2 ≠ 7 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> decide
  · intro hEq
    have h9 : 3 * 3 ≤ (m + 1) * (m + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [pow_two] at hEq
    omega

/-- **The obstruction**: a plane set with exactly `7` lattice points is
unimodularly equivalent to no cube `[0,m]²`, because the count is a unimodular
invariant and the cube's count `(m+1)²` is a perfect square while `7` is not. -/
theorem not_unimodEquiv_cube_of_latticeCount_seven
    {P : Set R2} (hP : latticeCount P = 7) (m : ℕ) :
    ¬ UnimodEquiv P (cube m) := by
  intro h
  have hc := h.latticeCount_eq
  rw [hP, latticeCount_cube] at hc
  exact succ_sq_ne_seven m hc.symm

end Borsuk
