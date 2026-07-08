/-
Campaign-2 / P3 day-one spike: the f*-recursion (Lemma A) route to an improved
Lean bound for g₅  (charter: ATTACK.md P3; math source: lenses/recursion-engineering/
new-recursion.md, Campaign 1, paper-grade; certificates certificate_report.json).

Frozen definitions: PROBLEM.md §3 = Erdos866/Upstream.lean (byte-pinned, untouched).

CONTENT
1. `fStar` — the re-engineered recursion f*_k(x, φ) (forbidden-set parameter φ
   replaces van Doorn's disjoint-representation extraction; lens Lemma A).
2. `HasSubsetSumsAvoiding` (the Lemma-A structure) + the empty-forbidden-set
   bridge to upstream `HasSubsetSumsContaining`.  The Lemma A induction itself
   and the Theorem-8 assembly live in `Erdos866/G5Port.lean` (C3-P1), keeping
   this file sorry-free.
3. The numeric side, SORRY-FREE: `key_ineq_star` — the (xineq*)-shaped lemma
       fStar 5 x 0 < x/12 + (B-1)/2 - 2   for all x ≥ 1,   B = 3,600,000
   via the u := x^(1/8) substitution, which turns the whole chain into
   sqrt-free polynomial inequalities (no 196k-interval certificate replay).
   B = 3,600,000 is the SAFE spike constant (exact-arithmetic margin 27,878.2);
   the lens-optimal constant is 3,519,219 (certified minimal for this route).
   Tightening path: see lenses/P3-lean-g5/ROADMAP.md.

Axioms: every lemma in this file closes over [propext, Classical.choice,
Quot.sound] only (no sorryAx anywhere since the C3-P1 restructure).
-/
import Erdos866.Upstream

namespace Erdos866

open Finset

/-! ## 1. The f*-recursion (lens new-recursion.md §2)

f*_3(x, φ) := φ + 1/2 + √(x + 1 + (φ - 1/2)²)
f*_k(x, φ) := φ + 1/2 + √(x · f*_{k-1}(x, φ+1) + (φ - 1/2)²)   (k ≥ 4)

Equivalently: r ≥ f*_k(x, φ) iff (r-1)(r-2φ) ≥ x · f*_{k-1}(x, φ+1)
(resp. ≥ x + 1 at the base); f*_k(·, φ) is the larger root.
Note the forbidden-set size φ INCREASES down the recursion: the k = 5 chain
at top level is f*_5(x,0) → f*_4(x,1) → f*_3(x,2). -/
noncomputable def fStar : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ | 1, _, _ | 2, _, _ => 0
  | 3, x, φ => φ + 1 / 2 + Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2)
  | k + 4, x, φ => φ + 1 / 2 + Real.sqrt (x * fStar (k + 3) x (φ + 1) + (φ - 1 / 2) ^ 2)

/-! ## 2. The Lemma-A structure (the induction itself is in G5Port.lean) -/

/-- Subset-sums structure avoiding a forbidden set: b₀, …, b_{k-1} with
    bᵢ ≠ 0 (i ≥ 1), bᵢ pairwise distinct (i ≥ 1), bᵢ ∉ F (i ≥ 1), and every
    subset sum containing b₀ lies in A.  With F = ∅ this is exactly upstream
    `HasSubsetSumsContaining`. -/
def HasSubsetSumsAvoiding (A F : Finset ℤ) : (k : ℕ) → Prop
  | 0 => True
  | k + 1 => ∃ b : Fin (k + 1) → ℤ,
      (∀ i : Fin (k + 1), 1 ≤ i.val → b i ≠ 0) ∧
      (∀ i j : Fin (k + 1), 1 ≤ i.val → 1 ≤ j.val → i ≠ j → b i ≠ b j) ∧
      (∀ i : Fin (k + 1), 1 ≤ i.val → b i ∉ F) ∧
      (∀ S : Finset (Fin (k + 1)), (0 : Fin (k + 1)) ∈ S → ∑ i ∈ S, b i ∈ A)

/-- With an empty forbidden set, the avoiding structure is upstream's
    `HasSubsetSumsContaining`. -/
lemma HasSubsetSumsAvoiding.toContaining {A : Finset ℤ} {k : ℕ}
    (h : HasSubsetSumsAvoiding A ∅ k) : HasSubsetSumsContaining A k := by
  cases k with
  | zero => trivial
  | succ k =>
    obtain ⟨b, h1, h2, _, h4⟩ := h
    exact ⟨b, h1, h2, h4⟩

/-! ## 3. The numeric side (sorry-free): (xineq*) at the safe spike constant

Strategy (validated in exact arithmetic, lenses/P3-lean-g5/):
substitute x = u⁸.  Then the whole f*_5(x,0)-chain collapses to polynomial
inequalities in u — each sqrt-step is `√z ≤ p(u)` with `z ≤ p(u)²` a plain
polynomial fact.  Chain bound (all u ≥ 1):

  f*_3(u⁸, 2) ≤ u⁴ + 9/2
  f*_4(u⁸, 1) ≤ u⁶ + (9/4)u² + 3/2
  f*_5(u⁸, 0) ≤ u⁷ + (9/8)u³ + (3/4)u + 1/2

then two tangent-line (Young/AM-GM) facts at rational tangent points:

  u⁷ ≤ (175/2102)·u⁸ + 1051⁷/(8·10¹⁴)        [tangent u₀ = 10.51]
  u³ ≤ (3/800000)·u⁸ + 625                    [tangent u₀ = 10]

Total slope 175/2102 + (19/8)(3/800000) ≤ 1/12 (gap 7.04e-5) and total
constant 1,770,634.92 + 1,484.375 < (3600000-1)/2 - 2 (margin 27,878.2). -/

/-- Helper: √z ≤ y from z ≤ y² and 0 ≤ y. -/
private lemma sqrt_le_of_sq_ge {z y : ℝ} (hy : 0 ≤ y) (h : z ≤ y ^ 2) :
    Real.sqrt z ≤ y := by
  calc Real.sqrt z ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- Young-type polynomial fact for the u³ term: 3w⁸ - 8w³ + 5 ≥ 0 for w ≥ 0
    (= 3(w⁴-1)² + (6w² + 4w + 2)(w-1)²; companion to upstream `poly_nonneg`,
    `poly_nonneg58`). -/
lemma poly_nonneg38 (w : ℝ) (hw : 0 ≤ w) : 0 ≤ 3 * w ^ 8 - 8 * w ^ 3 + 5 := by
  nlinarith [sq_nonneg (w ^ 4 - 1), mul_nonneg (mul_nonneg hw hw) (sq_nonneg (w - 1)),
    mul_nonneg hw (sq_nonneg (w - 1)), sq_nonneg (w - 1)]

/-- Tangent line to u⁷ under slope budget 175/2102 (tangent point 1051/100). -/
lemma young_u7 (u : ℝ) (hu : 0 ≤ u) :
    u ^ 7 ≤ 175 / 2102 * u ^ 8 + 1416507936636696284851 / 800000000000000 := by
  have h := poly_nonneg (100 * u / 1051) (by positivity)
  have key : 175 / 2102 * u ^ 8 + (1416507936636696284851 / 800000000000000 : ℝ) - u ^ 7
      = 1416507936636696284851 / 800000000000000 *
        (7 * (100 * u / 1051) ^ 8 - 8 * (100 * u / 1051) ^ 7 + 1) := by
    ring
  have h2 : (0 : ℝ) ≤ 175 / 2102 * u ^ 8
      + (1416507936636696284851 / 800000000000000 : ℝ) - u ^ 7 := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Tangent line to u³ under slope budget 3/800000 (tangent point 10). -/
lemma young_u3 (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ 3 / 800000 * u ^ 8 + 625 := by
  have h := poly_nonneg38 (u / 10) (by positivity)
  have key : 3 / 800000 * u ^ 8 + (625 : ℝ) - u ^ 3
      = 125 * (3 * (u / 10) ^ 8 - 8 * (u / 10) ^ 3 + 5) := by ring
  have h2 : (0 : ℝ) ≤ 3 / 800000 * u ^ 8 + (625 : ℝ) - u ^ 3 := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Chain bound, base: f*_3(u⁸, 2) ≤ u⁴ + 9/2 for u ≥ 1. -/
lemma fStar3_le_poly (u : ℝ) (hu : 1 ≤ u) : fStar 3 (u ^ 8) 2 ≤ u ^ 4 + 9 / 2 := by
  have e : fStar 3 (u ^ 8) 2
      = 2 + 1 / 2 + Real.sqrt (u ^ 8 + 1 + ((2 : ℝ) - 1 / 2) ^ 2) := rfl
  have h : Real.sqrt (u ^ 8 + 1 + ((2 : ℝ) - 1 / 2) ^ 2) ≤ u ^ 4 + 2 :=
    sqrt_le_of_sq_ge (by positivity) (by nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ u) 4])
  rw [e]; linarith

/-- Chain bound, level 4: f*_4(u⁸, 1) ≤ u⁶ + (9/4)u² + 3/2 for u ≥ 1. -/
lemma fStar4_le_poly (u : ℝ) (hu : 1 ≤ u) :
    fStar 4 (u ^ 8) 1 ≤ u ^ 6 + 9 / 4 * u ^ 2 + 3 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have e : fStar 4 (u ^ 8) 1
      = 1 + 1 / 2 + Real.sqrt (u ^ 8 * fStar 3 (u ^ 8) (1 + 1) + ((1 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((1 : ℝ) + 1) = 2 by norm_num] at e
  have h3 := fStar3_le_poly u hu
  have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
  have hu4 : (1 : ℝ) ≤ u ^ 4 := by nlinarith [hu2]
  have hmul : u ^ 8 * fStar 3 (u ^ 8) 2 ≤ u ^ 8 * (u ^ 4 + 9 / 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h : Real.sqrt (u ^ 8 * fStar 3 (u ^ 8) 2 + ((1 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 6 + 9 / 4 * u ^ 2 :=
    sqrt_le_of_sq_ge (by positivity) (by nlinarith [hmul, hu4])
  rw [e]; linarith

/-- Chain bound, level 5 — THE template lemma of the spike:
    f*_5(u⁸, 0) ≤ u⁷ + (9/8)u³ + (3/4)u + 1/2 for u ≥ 1. -/
lemma fStar5_le_poly (u : ℝ) (hu : 1 ≤ u) :
    fStar 5 (u ^ 8) 0 ≤ u ^ 7 + 9 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have e : fStar 5 (u ^ 8) 0
      = 0 + 1 / 2 + Real.sqrt (u ^ 8 * fStar 4 (u ^ 8) (0 + 1) + ((0 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((0 : ℝ) + 1) = 1 by norm_num] at e
  have h4 := fStar4_le_poly u hu
  have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
  have hmul : u ^ 8 * fStar 4 (u ^ 8) 1 ≤ u ^ 8 * (u ^ 6 + 9 / 4 * u ^ 2 + 3 / 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h : Real.sqrt (u ^ 8 * fStar 4 (u ^ 8) 1 + ((0 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 7 + 9 / 8 * u ^ 3 + 3 / 4 * u :=
    sqrt_le_of_sq_ge (by positivity)
      (by nlinarith [hmul, hu2, pow_nonneg hu0 6, pow_nonneg hu0 4])
  rw [e]; linarith

/-- Polynomial core of (xineq*) at the safe constant B = 3,600,000:
    u⁷ + (9/8)u³ + (3/4)u + 1/2 < u⁸/12 + (B-1)/2 - 2 for u ≥ 1.
    Exact-arithmetic margins: slope gap 1/12 - 175/2102 - 57/6400000 > 0,
    constant margin 27,878.2. -/
lemma key_ineq_star_poly (u : ℝ) (hu : 1 ≤ u) :
    u ^ 7 + 9 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2
      < u ^ 8 / 12 + ((3600000 : ℝ) - 1) / 2 - 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h7 := young_u7 u hu0
  have h3 := young_u3 u hu0
  have hcube : 3 / 4 * u + 1 / 2 ≤ 5 / 4 * u ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg u),
      mul_nonneg (sub_nonneg.mpr hu) hu0, sub_nonneg.mpr hu]
  have h8 : (0 : ℝ) ≤ u ^ 8 := by positivity
  linarith

/-- **(xineq*) at the safe spike constant** — the f*-analogue of upstream
    `key_ineq`:  f*_5(x, 0) < x/12 + (3600000 - 1)/2 - 2 for all x ≥ 1.
    This is the complete numeric side of a gFun 5 n < 3,600,000 port
    (33.3× below the standing Lean constant 120,000,000); the lens-certified
    minimum for this route is 3,519,219 — tightening is constant-tuning in
    `young_u7`/`young_u3` plus a sharper `fStar3_le_poly`, no new structure. -/
theorem key_ineq_star (x : ℝ) (hx : 1 ≤ x) :
    fStar 5 x 0 < x / 12 + ((3600000 : ℝ) - 1) / 2 - 2 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set u : ℝ := x ^ ((1 : ℝ) / 8) with hu_def
  have hu : 1 ≤ u := Real.one_le_rpow hx (by norm_num)
  have hux : u ^ (8 : ℕ) = x := by
    rw [hu_def, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 8)) 8, ← Real.rpow_mul hx0]
    norm_num
  calc fStar 5 x 0 = fStar 5 (u ^ 8) 0 := by rw [hux]
    _ ≤ u ^ 7 + 9 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 := fStar5_le_poly u hu
    _ < u ^ 8 / 12 + ((3600000 : ℝ) - 1) / 2 - 2 := key_ineq_star_poly u hu
    _ = x / 12 + ((3600000 : ℝ) - 1) / 2 - 2 := by rw [hux]

/-! ## 4. Tightening demonstration (roadmap Phase C de-risk)

Same structure, tuned tangent points (main 21001/2000 ≈ the true maximizer
u* = x*^{1/8} ≈ 10.50042; lower-order terms at 21/2): B = 3,520,600.
Exact margins: slope gap 6.559e-7, constant margin 14.25.  The remaining
~1,380 to the lens-optimal 3,519,219 is the (9/8)u³ coefficient of
`fStar5_le_poly` (true asymptotic coefficient 5/8); recovering it needs a
two-regime fStar3 bound (√x + 5/2 + 13/(8√X₀) for x ≥ X₀) — Phase C. -/

/-- Young-type polynomial fact for the u term: w⁸ - 8w + 7 ≥ 0 for w ≥ 0
    (= (w-1)²(w⁶ + 2w⁵ + 3w⁴ + 4w³ + 5w² + 6w + 7)). -/
lemma poly_nonneg18 (w : ℝ) (hw : 0 ≤ w) : 0 ≤ w ^ 8 - 8 * w + 7 := by
  nlinarith [mul_nonneg (pow_nonneg hw 6) (sq_nonneg (w - 1)),
    mul_nonneg (pow_nonneg hw 5) (sq_nonneg (w - 1)),
    mul_nonneg (pow_nonneg hw 4) (sq_nonneg (w - 1)),
    mul_nonneg (pow_nonneg hw 3) (sq_nonneg (w - 1)),
    mul_nonneg (mul_nonneg hw hw) (sq_nonneg (w - 1)),
    mul_nonneg hw (sq_nonneg (w - 1)), sq_nonneg (w - 1)]

/-- Tuned tangent to u⁷ at u₀ = 21001/2000 (slope 1750/21001). -/
lemma young_u7_tuned (u : ℝ) (hu : 0 ≤ u) :
    u ^ 7 ≤ 1750 / 21001 * u ^ 8
      + 1801688989619928159144261147001 / 1024000000000000000000000 := by
  have h := poly_nonneg (2000 * u / 21001) (by positivity)
  have key : 1750 / 21001 * u ^ 8
      + (1801688989619928159144261147001 / 1024000000000000000000000 : ℝ) - u ^ 7
      = 1801688989619928159144261147001 / 1024000000000000000000000 *
        (7 * (2000 * u / 21001) ^ 8 - 8 * (2000 * u / 21001) ^ 7 + 1) := by ring
  have h2 : (0 : ℝ) ≤ 1750 / 21001 * u ^ 8
      + (1801688989619928159144261147001 / 1024000000000000000000000 : ℝ) - u ^ 7 := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Tuned tangent to u³ at u₀ = 21/2 (slope 4/1361367). -/
lemma young_u3_tuned (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ 4 / 1361367 * u ^ 8 + 46305 / 64 := by
  have h := poly_nonneg38 (2 * u / 21) (by positivity)
  have key : 4 / 1361367 * u ^ 8 + (46305 / 64 : ℝ) - u ^ 3
      = 9261 / 64 * (3 * (2 * u / 21) ^ 8 - 8 * (2 * u / 21) ^ 3 + 5) := by ring
  have h2 : (0 : ℝ) ≤ 4 / 1361367 * u ^ 8 + (46305 / 64 : ℝ) - u ^ 3 := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Tuned tangent to u at u₀ = 21/2 (slope 16/1801088541). -/
lemma young_u1_tuned (u : ℝ) (hu : 0 ≤ u) :
    u ≤ 16 / 1801088541 * u ^ 8 + 147 / 16 := by
  have h := poly_nonneg18 (2 * u / 21) (by positivity)
  have key : 16 / 1801088541 * u ^ 8 + (147 / 16 : ℝ) - u
      = 21 / 16 * ((2 * u / 21) ^ 8 - 8 * (2 * u / 21) + 7) := by ring
  have h2 : (0 : ℝ) ≤ 16 / 1801088541 * u ^ 8 + (147 / 16 : ℝ) - u := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- **(xineq*) at the tuned constant B = 3,520,600** — same proof shape,
    0.04% above the lens-optimal 3,519,219.  Margins: slope 6.559e-7,
    constant 14.25 (exact arithmetic, lenses/P3-lean-g5/). -/
theorem key_ineq_star_tuned (x : ℝ) (hx : 1 ≤ x) :
    fStar 5 x 0 < x / 12 + ((3520600 : ℝ) - 1) / 2 - 2 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set u : ℝ := x ^ ((1 : ℝ) / 8) with hu_def
  have hu : 1 ≤ u := Real.one_le_rpow hx (by norm_num)
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hux : u ^ (8 : ℕ) = x := by
    rw [hu_def, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 8)) 8, ← Real.rpow_mul hx0]
    norm_num
  have h7 := young_u7_tuned u hu0
  have h3 := young_u3_tuned u hu0
  have h1 := young_u1_tuned u hu0
  have h8 : (0 : ℝ) ≤ u ^ 8 := by positivity
  calc fStar 5 x 0 = fStar 5 (u ^ 8) 0 := by rw [hux]
    _ ≤ u ^ 7 + 9 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 := fStar5_le_poly u hu
    _ < u ^ 8 / 12 + ((3520600 : ℝ) - 1) / 2 - 2 := by linarith
    _ = x / 12 + ((3520600 : ℝ) - 1) / 2 - 2 := by rw [hux]

/-! ## Axiom audit -/

-- Expected: NO sorryAx anywhere in this file; the mathlib base axioms
-- [propext, Classical.choice, Quot.sound] are of course present.
#print axioms key_ineq_star       -- no sorryAx
#print axioms key_ineq_star_tuned -- no sorryAx
#print axioms fStar5_le_poly      -- no sorryAx
#print axioms young_u7            -- no sorryAx
#print axioms poly_nonneg38       -- no sorryAx

end Erdos866
