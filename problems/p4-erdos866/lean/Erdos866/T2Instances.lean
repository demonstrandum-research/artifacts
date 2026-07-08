/-
C6-P3 (retry of C5P3): T2 Lean instantiation beyond k = 5.

CONTENT
1. `gk_upper_star` — THE GENERAL-k WRAPPER (T2-ALLK.md §7 "cheapest path"):
       gFun k n ≤ ⌈f*_k(2n, 0)⌉₊   for every k ≥ 3, n ≥ 1,
   on top of the kernel-verified general-k `ceslemgeneral_star` (C3-P1).
   This is the formal surplus→evens reduction of T2-ALLK.md §4; together
   with any closed-form bound on `fStar` it yields T2(g) instances.
2. Explicit instances beyond the k = 5 T1 closure (charter: k = 6, 7 first):
       `g6upper_t2` : gFun 6 n < 2·n^(15/16)  for n ≥ 2^15 = 32768
       `g7upper_t2` : gFun 7 n < 2·n^(31/32)  for n ≥ 2^31 = 2147483648
   via division-free polynomial chains under x = u^16 (resp. u^32) —
   the same squaring route as `fStar5_le_poly` (G5FStar.lean §3).
   Thresholds are FAR below T2-ALLK.md's N(k) = k⁴·2^(4k+27); the paper
   theorem is only strengthened, never contradicted, by these instances.
3. The fibCnt-vs-log₂ comparison (C3→C6 hygiene carry, CLOSED here):
       `log2_succ_le_fibCnt`  : Nat.log 2 n + 1 ≤ fibCnt n  (n ≥ 1)
       `log2_succ_lt_hFun_five` : Nat.log 2 n + 1 < hFun 5 n (n ≥ 1) —
   strictly improving upstream `h5lower` (Nat.log 2 n < hFun 5 n).

Machine verification (exact rationals, before proving):
lenses/C6P3-t2-lean-retry/verify_c6p3.py — ALL PASS (every squared step
inequality below, both endgames, 267^16 ≤ 2·256^16, 261^32 ≤ 2·256^32,
end-to-end ceiling checks at both thresholds, fib(j+2) ≤ 2^j, and the
fibCnt bound brute-forced on [1, 10^6]).

Axioms: every theorem here must close over [propext, Classical.choice,
Quot.sound] only (audit: scripts/AuditC6P3.lean).
-/
import Erdos866.G5Port
import Erdos866.LowerBounds

namespace Erdos866

open Finset

set_option maxHeartbeats 1600000

/-! ## 1. The general-k wrapper on `ceslemgeneral_star` -/

/-- Surplus→evens reduction at the f*-chain bound (T2-ALLK.md §4 "Reduction
    to the chains", g-side): if `|A| ≥ n + ⌈f*_k(2n,0)⌉₊` then A has the
    k-pairwise-sums structure. -/
theorem gk_upper_star_aux (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (A : Finset ℤ) (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + ⌈fStar k (2 * (n : ℝ)) 0⌉₊ ≤ A.card) :
    HasPairwiseSums A k := by
  set m := ⌈fStar k (2 * (n : ℝ)) 0⌉₊ with hm_def
  have h2n : (2 : ℝ) ≤ 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hf2 : (2 : ℝ) ≤ fStar k (2 * (n : ℝ)) 0 :=
    fStar_ge_two k hk _ 0 h2n le_rfl
  have hm2 : 2 ≤ m := by
    have hfm : fStar k (2 * (n : ℝ)) 0 ≤ (m : ℝ) := Nat.le_ceil _
    have h : (2 : ℝ) ≤ (m : ℝ) := le_trans hf2 hfm
    exact_mod_cast h
  -- the even part E carries the surplus
  have hE_card : m ≤ (A.filter (fun x => Even x)).card :=
    even_count_ge_c_star m n A hA hcard
  set E := A.filter (fun x => Even x) with hE_def
  have hE_card2 : 2 ≤ E.card := le_trans hm2 hE_card
  have hE_ne : E.Nonempty := Finset.card_pos.mp (by omega)
  have hE_sub : E ⊆ A := Finset.filter_subset _ _
  have hE_even : ∀ a ∈ E, (2 : ℤ) ∣ a :=
    fun a ha => even_iff_two_dvd.mp (Finset.mem_filter.mp ha).2
  have hE_pos : ∀ a ∈ E, (2 : ℤ) ≤ a := by
    intro a ha
    have h1 := (Finset.mem_Icc.mp (hA (hE_sub ha))).1
    have h2 := hE_even a ha
    omega
  have hE_range : 2 ≤ E.max' hE_ne - E.min' hE_ne :=
    even_range_ge_two' E hE_ne hE_even hE_card2
  have hE_range_le : E.max' hE_ne - E.min' hE_ne ≤ 2 * (n : ℤ) := by
    have hmax := (Finset.mem_Icc.mp (hA (hE_sub (E.max'_mem hE_ne)))).2
    have hmin := (Finset.mem_Icc.mp (hA (hE_sub (E.min'_mem hE_ne)))).1
    omega
  have hcard_real : fStar k (↑(E.max' hE_ne - E.min' hE_ne)) 0 ≤ (E.card : ℝ) := by
    calc fStar k (↑(E.max' hE_ne - E.min' hE_ne)) 0
        ≤ fStar k (2 * (n : ℝ)) 0 := by
          apply fStar_mono_x k hk _ _ 0 le_rfl
          · exact_mod_cast hE_range
          · push_cast
            exact_mod_cast hE_range_le
      _ ≤ (m : ℝ) := Nat.le_ceil _
      _ ≤ (E.card : ℝ) := by exact_mod_cast hE_card
  obtain ⟨b, hb_inj, hb_sums⟩ :=
    ceslemgeneral_star k hk E hE_ne hE_even hE_pos hE_range hcard_real
  exact ⟨b, hb_inj, fun i j hij => hE_sub (hb_sums i j hij)⟩

/-- **The general-k wrapper** (T2-ALLK.md §7 ledger, "cheapest path" item):
    gFun k n ≤ ⌈f*_k(2n, 0)⌉₊ for all k ≥ 3, n ≥ 1.  The k-uniform formal
    backbone of Theorem T2(g); the upstream analogue is `hk_upper`. -/
theorem gk_upper_star (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    gFun k n ≤ ⌈fStar k (2 * (n : ℝ)) 0⌉₊ := by
  unfold gFun
  refine Nat.sInf_le ?_
  intro A hA hcard
  exact gk_upper_star_aux k hk n hn A hA hcard

/-! ## 2. The k = 6 chain (x = u^16; machine-tested in verify_c6p3.py) -/

/-- √z ≤ y from z ≤ y² (copy of G5FStar's private helper). -/
private lemma sqrt_le_of_sq_ge' {z y : ℝ} (hy : 0 ≤ y) (h : z ≤ y ^ 2) :
    Real.sqrt z ≤ y := by
  calc Real.sqrt z ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

lemma fStar3_le_poly16 (u : ℝ) (hu : 1 ≤ u) :
    fStar 3 (u ^ 16) 3 ≤ u ^ 8 + 11 / 2 := by
  have h8 : (1 : ℝ) ≤ u ^ 8 := one_le_pow₀ hu
  have e : fStar 3 (u ^ 16) 3
      = 3 + 1 / 2 + Real.sqrt (u ^ 16 + 1 + ((3 : ℝ) - 1 / 2) ^ 2) := rfl
  have h : Real.sqrt (u ^ 16 + 1 + ((3 : ℝ) - 1 / 2) ^ 2) ≤ u ^ 8 + 2 :=
    sqrt_le_of_sq_ge' (by positivity) (by nlinarith [h8])
  rw [e]; linarith

lemma fStar4_le_poly16 (u : ℝ) (hu : 1 ≤ u) :
    fStar 4 (u ^ 16) 2 ≤ u ^ 12 + 11 / 4 * u ^ 4 + 5 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h8 : (1 : ℝ) ≤ u ^ 8 := one_le_pow₀ hu
  have e : fStar 4 (u ^ 16) 2
      = 2 + 1 / 2 + Real.sqrt (u ^ 16 * fStar 3 (u ^ 16) (2 + 1) + ((2 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((2 : ℝ) + 1) = 3 by norm_num] at e
  have h3 := fStar3_le_poly16 u hu
  have hmul : u ^ 16 * fStar 3 (u ^ 16) 3 ≤ u ^ 16 * (u ^ 8 + 11 / 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h : Real.sqrt (u ^ 16 * fStar 3 (u ^ 16) 3 + ((2 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 12 + 11 / 4 * u ^ 4 :=
    sqrt_le_of_sq_ge' (by positivity) (by nlinarith [hmul, h8])
  rw [e]; linarith

lemma fStar5_le_poly16 (u : ℝ) (hu : 1 ≤ u) :
    fStar 5 (u ^ 16) 1 ≤ u ^ 14 + 11 / 8 * u ^ 6 + 3 / 2 * u ^ 2 + 3 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h16 : (1 : ℝ) ≤ u ^ 16 := one_le_pow₀ hu
  have e : fStar 5 (u ^ 16) 1
      = 1 + 1 / 2 + Real.sqrt (u ^ 16 * fStar 4 (u ^ 16) (1 + 1) + ((1 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((1 : ℝ) + 1) = 2 by norm_num] at e
  have h4 := fStar4_le_poly16 u hu
  have hmul : u ^ 16 * fStar 4 (u ^ 16) 2 ≤ u ^ 16 * (u ^ 12 + 11 / 4 * u ^ 4 + 5 / 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h : Real.sqrt (u ^ 16 * fStar 4 (u ^ 16) 2 + ((1 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 14 + 11 / 8 * u ^ 6 + 3 / 2 * u ^ 2 :=
    sqrt_le_of_sq_ge' (by positivity)
      (by nlinarith [hmul, h16, pow_nonneg hu0 12, pow_nonneg hu0 8, pow_nonneg hu0 4])
  rw [e]; linarith

lemma fStar6_le_poly16 (u : ℝ) (hu : 1 ≤ u) :
    fStar 6 (u ^ 16) 0 ≤ u ^ 15 + 11 / 16 * u ^ 7 + 3 / 4 * u ^ 3 + 3 / 4 * u + 1 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h14 : (1 : ℝ) ≤ u ^ 14 := one_le_pow₀ hu
  have e : fStar 6 (u ^ 16) 0
      = 0 + 1 / 2 + Real.sqrt (u ^ 16 * fStar 5 (u ^ 16) (0 + 1) + ((0 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((0 : ℝ) + 1) = 1 by norm_num] at e
  have h5 := fStar5_le_poly16 u hu
  have hmul : u ^ 16 * fStar 5 (u ^ 16) 1
      ≤ u ^ 16 * (u ^ 14 + 11 / 8 * u ^ 6 + 3 / 2 * u ^ 2 + 3 / 2) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h : Real.sqrt (u ^ 16 * fStar 5 (u ^ 16) 1 + ((0 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 15 + 11 / 16 * u ^ 7 + 3 / 4 * u ^ 3 + 3 / 4 * u :=
    sqrt_le_of_sq_ge' (by positivity)
      (by nlinarith [hmul, h14, pow_nonneg hu0 10, pow_nonneg hu0 8, pow_nonneg hu0 6,
        pow_nonneg hu0 4, pow_nonneg hu0 2])
  rw [e]; linarith

/-- Endgame polynomial fact, k = 6 (machine check "K6 endgame poly"). -/
lemma key6_endgame (u : ℝ) (hu : 2 ≤ u) :
    u ^ 15 + 11 / 16 * u ^ 7 + 3 / 4 * u ^ 3 + 3 / 4 * u + 1 / 2 + 1
      < 267 / 256 * u ^ 15 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have h8 : (256 : ℝ) ≤ u ^ 8 := by
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu 8
  have h37 : u ^ 3 ≤ u ^ 7 := pow_le_pow_right₀ hu1 (by norm_num)
  have h17 : u ≤ u ^ 7 := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 7 := pow_le_pow_right₀ hu1 (by norm_num)
  have h07 : (1 : ℝ) ≤ u ^ 7 := one_le_pow₀ hu1
  have h15 : 256 * u ^ 7 ≤ u ^ 15 := by
    have h := mul_le_mul_of_nonneg_left h8 (pow_nonneg hu0 7)
    nlinarith [h]
  linarith

/-- 267/256 ≤ 2^(1/16) (machine check "root16": 267^16 ≤ 2·256^16). -/
lemma rt16_two : (267 : ℝ) / 256 ≤ (2 : ℝ) ^ ((1 : ℝ) / 16) := by
  have h0 : (0 : ℝ) ≤ 267 / 256 := by norm_num
  have h : ((267 : ℝ) / 256) ^ (16 : ℕ) ≤ 2 := by norm_num
  have key := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 1 / 16)
  rw [← Real.rpow_natCast ((267 : ℝ) / 256) 16, ← Real.rpow_mul h0] at key
  norm_num at key
  exact key

/-- **T2(g) instance k = 6, kernel route**: gFun 6 n < 2·n^(15/16) for
    n ≥ 2^15 (vs paper threshold N(6) = 6⁴·2^51 ≈ 2.9·10^18). -/
theorem g6upper_t2 (n : ℕ) (hn : 32768 ≤ n) :
    (gFun 6 n : ℝ) < 2 * (n : ℝ) ^ ((15 : ℝ) / 16) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (32768 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx2 : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  set u : ℝ := (2 * (n : ℝ)) ^ ((1 : ℝ) / 16) with hu_def
  have hux : u ^ (16 : ℕ) = 2 * (n : ℝ) := by
    rw [hu_def, ← Real.rpow_natCast ((2 * (n : ℝ)) ^ ((1 : ℝ) / 16)) 16,
      ← Real.rpow_mul hx0]
    norm_num
  have hu2 : (2 : ℝ) ≤ u := by
    have h216 : ((2 : ℝ) ^ (16 : ℕ)) ≤ 2 * (n : ℝ) := by norm_num; linarith
    have h := Real.rpow_le_rpow (by positivity) h216 (by norm_num : (0 : ℝ) ≤ 1 / 16)
    rw [← Real.rpow_natCast (2 : ℝ) 16, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num at h
    exact h
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hpoly : fStar 6 (2 * (n : ℝ)) 0
      ≤ u ^ 15 + 11 / 16 * u ^ 7 + 3 / 4 * u ^ 3 + 3 / 4 * u + 1 / 2 := by
    have h := fStar6_le_poly16 u hu1
    rwa [hux] at h
  have hwrap : (gFun 6 n : ℝ) ≤ (⌈fStar 6 (2 * (n : ℝ)) 0⌉₊ : ℝ) := by
    exact_mod_cast gk_upper_star 6 (by norm_num) n hn1
  have hf0 : (0 : ℝ) ≤ fStar 6 (2 * (n : ℝ)) 0 :=
    le_trans (by norm_num) (fStar_ge_two 6 (by norm_num) _ 0 hx2 le_rfl)
  have hceil : (⌈fStar 6 (2 * (n : ℝ)) 0⌉₊ : ℝ) < fStar 6 (2 * (n : ℝ)) 0 + 1 :=
    Nat.ceil_lt_add_one hf0
  have hkey := key6_endgame u hu2
  have hu15 : u ^ (15 : ℕ) = (2 * (n : ℝ)) ^ ((15 : ℝ) / 16) := by
    rw [hu_def, ← Real.rpow_natCast ((2 * (n : ℝ)) ^ ((1 : ℝ) / 16)) 15,
      ← Real.rpow_mul hx0]
    norm_num
  have htarget : 2 * (n : ℝ) ^ ((15 : ℝ) / 16)
      = (2 : ℝ) ^ ((1 : ℝ) / 16) * (2 * (n : ℝ)) ^ ((15 : ℝ) / 16) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ (n : ℝ)),
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc (gFun 6 n : ℝ) ≤ (⌈fStar 6 (2 * (n : ℝ)) 0⌉₊ : ℝ) := hwrap
    _ < fStar 6 (2 * (n : ℝ)) 0 + 1 := hceil
    _ ≤ u ^ 15 + 11 / 16 * u ^ 7 + 3 / 4 * u ^ 3 + 3 / 4 * u + 1 / 2 + 1 := by linarith
    _ < 267 / 256 * u ^ 15 := hkey
    _ ≤ (2 : ℝ) ^ ((1 : ℝ) / 16) * u ^ 15 :=
        mul_le_mul_of_nonneg_right rt16_two (pow_nonneg hu0 15)
    _ = 2 * (n : ℝ) ^ ((15 : ℝ) / 16) := by rw [hu15]; exact htarget.symm

/-! ## 3. The k = 7 chain (x = u^32) -/

lemma fStar3_le_poly32 (u : ℝ) (hu : 1 ≤ u) :
    fStar 3 (u ^ 32) 4 ≤ u ^ 16 + 15 / 2 := by
  have h16 : (1 : ℝ) ≤ u ^ 16 := one_le_pow₀ hu
  have e : fStar 3 (u ^ 32) 4
      = 4 + 1 / 2 + Real.sqrt (u ^ 32 + 1 + ((4 : ℝ) - 1 / 2) ^ 2) := rfl
  have h : Real.sqrt (u ^ 32 + 1 + ((4 : ℝ) - 1 / 2) ^ 2) ≤ u ^ 16 + 3 :=
    sqrt_le_of_sq_ge' (by positivity) (by nlinarith [h16])
  rw [e]; linarith

lemma fStar4_le_poly32 (u : ℝ) (hu : 1 ≤ u) :
    fStar 4 (u ^ 32) 3 ≤ u ^ 24 + 15 / 4 * u ^ 8 + 7 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h16 : (1 : ℝ) ≤ u ^ 16 := one_le_pow₀ hu
  have e : fStar 4 (u ^ 32) 3
      = 3 + 1 / 2 + Real.sqrt (u ^ 32 * fStar 3 (u ^ 32) (3 + 1) + ((3 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((3 : ℝ) + 1) = 4 by norm_num] at e
  have h3 := fStar3_le_poly32 u hu
  have hmul : u ^ 32 * fStar 3 (u ^ 32) 4 ≤ u ^ 32 * (u ^ 16 + 15 / 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h : Real.sqrt (u ^ 32 * fStar 3 (u ^ 32) 4 + ((3 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 24 + 15 / 4 * u ^ 8 :=
    sqrt_le_of_sq_ge' (by positivity) (by nlinarith [hmul, h16])
  rw [e]; linarith

lemma fStar5_le_poly32 (u : ℝ) (hu : 1 ≤ u) :
    fStar 5 (u ^ 32) 2 ≤ u ^ 28 + 15 / 8 * u ^ 12 + 2 * u ^ 4 + 5 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h24 : (1 : ℝ) ≤ u ^ 24 := one_le_pow₀ hu
  have h32 : (1 : ℝ) ≤ u ^ 32 := one_le_pow₀ hu
  have e : fStar 5 (u ^ 32) 2
      = 2 + 1 / 2 + Real.sqrt (u ^ 32 * fStar 4 (u ^ 32) (2 + 1) + ((2 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((2 : ℝ) + 1) = 3 by norm_num] at e
  have h4 := fStar4_le_poly32 u hu
  have hmul : u ^ 32 * fStar 4 (u ^ 32) 3
      ≤ u ^ 32 * (u ^ 24 + 15 / 4 * u ^ 8 + 7 / 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h : Real.sqrt (u ^ 32 * fStar 4 (u ^ 32) 3 + ((2 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 28 + 15 / 8 * u ^ 12 + 2 * u ^ 4 :=
    sqrt_le_of_sq_ge' (by positivity)
      (by nlinarith [hmul, h24, h32, pow_nonneg hu0 16, pow_nonneg hu0 8])
  rw [e]; linarith

lemma fStar6_le_poly32 (u : ℝ) (hu : 1 ≤ u) :
    fStar 6 (u ^ 32) 1 ≤ u ^ 30 + 15 / 16 * u ^ 14 + u ^ 6 + 5 / 4 * u ^ 2 + 3 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h28 : (1 : ℝ) ≤ u ^ 28 := one_le_pow₀ hu
  have e : fStar 6 (u ^ 32) 1
      = 1 + 1 / 2 + Real.sqrt (u ^ 32 * fStar 5 (u ^ 32) (1 + 1) + ((1 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((1 : ℝ) + 1) = 2 by norm_num] at e
  have h5 := fStar5_le_poly32 u hu
  have hmul : u ^ 32 * fStar 5 (u ^ 32) 2
      ≤ u ^ 32 * (u ^ 28 + 15 / 8 * u ^ 12 + 2 * u ^ 4 + 5 / 2) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have h : Real.sqrt (u ^ 32 * fStar 5 (u ^ 32) 2 + ((1 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 30 + 15 / 16 * u ^ 14 + u ^ 6 + 5 / 4 * u ^ 2 :=
    sqrt_le_of_sq_ge' (by positivity)
      (by nlinarith [hmul, h28, pow_nonneg hu0 20, pow_nonneg hu0 16, pow_nonneg hu0 12,
        pow_nonneg hu0 8, pow_nonneg hu0 4])
  rw [e]; linarith

lemma fStar7_le_poly32 (u : ℝ) (hu : 1 ≤ u) :
    fStar 7 (u ^ 32) 0
      ≤ u ^ 31 + 15 / 32 * u ^ 15 + 1 / 2 * u ^ 7 + 5 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h22 : (1 : ℝ) ≤ u ^ 22 := one_le_pow₀ hu
  have e : fStar 7 (u ^ 32) 0
      = 0 + 1 / 2 + Real.sqrt (u ^ 32 * fStar 6 (u ^ 32) (0 + 1) + ((0 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((0 : ℝ) + 1) = 1 by norm_num] at e
  have h6 := fStar6_le_poly32 u hu
  have hmul : u ^ 32 * fStar 6 (u ^ 32) 1
      ≤ u ^ 32 * (u ^ 30 + 15 / 16 * u ^ 14 + u ^ 6 + 5 / 4 * u ^ 2 + 3 / 2) :=
    mul_le_mul_of_nonneg_left h6 (by positivity)
  have h : Real.sqrt (u ^ 32 * fStar 6 (u ^ 32) 1 + ((0 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 31 + 15 / 32 * u ^ 15 + 1 / 2 * u ^ 7 + 5 / 8 * u ^ 3 + 3 / 4 * u :=
    sqrt_le_of_sq_ge' (by positivity)
      (by nlinarith [hmul, h22, pow_nonneg hu0 30, pow_nonneg hu0 18, pow_nonneg hu0 16,
        pow_nonneg hu0 14, pow_nonneg hu0 10, pow_nonneg hu0 8, pow_nonneg hu0 6,
        pow_nonneg hu0 4, pow_nonneg hu0 2])
  rw [e]; linarith

/-- Endgame polynomial fact, k = 7 (machine check "K7 endgame poly"). -/
lemma key7_endgame (u : ℝ) (hu : 2 ≤ u) :
    u ^ 31 + 15 / 32 * u ^ 15 + 1 / 2 * u ^ 7 + 5 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 + 1
      < 261 / 256 * u ^ 31 := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have h16 : (65536 : ℝ) ≤ u ^ 16 := by
    calc (65536 : ℝ) = 2 ^ 16 := by norm_num
      _ ≤ u ^ 16 := pow_le_pow_left₀ (by norm_num) hu 16
  have h715 : u ^ 7 ≤ u ^ 15 := pow_le_pow_right₀ hu1 (by norm_num)
  have h315 : u ^ 3 ≤ u ^ 15 := pow_le_pow_right₀ hu1 (by norm_num)
  have h115 : u ≤ u ^ 15 := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 15 := pow_le_pow_right₀ hu1 (by norm_num)
  have h015 : (1 : ℝ) ≤ u ^ 15 := one_le_pow₀ hu1
  have h31 : 65536 * u ^ 15 ≤ u ^ 31 := by
    have h := mul_le_mul_of_nonneg_left h16 (pow_nonneg hu0 15)
    nlinarith [h]
  linarith

/-- 261/256 ≤ 2^(1/32) (machine check "root32": 261^32 ≤ 2·256^32). -/
lemma rt32_two : (261 : ℝ) / 256 ≤ (2 : ℝ) ^ ((1 : ℝ) / 32) := by
  have h0 : (0 : ℝ) ≤ 261 / 256 := by norm_num
  have h : ((261 : ℝ) / 256) ^ (32 : ℕ) ≤ 2 := by norm_num
  have key := Real.rpow_le_rpow (by positivity) h (by norm_num : (0 : ℝ) ≤ 1 / 32)
  rw [← Real.rpow_natCast ((261 : ℝ) / 256) 32, ← Real.rpow_mul h0] at key
  norm_num at key
  exact key

/-- **T2(g) instance k = 7, kernel route**: gFun 7 n < 2·n^(31/32) for
    n ≥ 2^31 (vs paper threshold N(7) = 7⁴·2^55 ≈ 8.6·10^19). -/
theorem g7upper_t2 (n : ℕ) (hn : 2147483648 ≤ n) :
    (gFun 7 n : ℝ) < 2 * (n : ℝ) ^ ((31 : ℝ) / 32) := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnR : (2147483648 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx2 : (2 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ 2 * (n : ℝ) := by linarith
  set u : ℝ := (2 * (n : ℝ)) ^ ((1 : ℝ) / 32) with hu_def
  have hux : u ^ (32 : ℕ) = 2 * (n : ℝ) := by
    rw [hu_def, ← Real.rpow_natCast ((2 * (n : ℝ)) ^ ((1 : ℝ) / 32)) 32,
      ← Real.rpow_mul hx0]
    norm_num
  have hu2 : (2 : ℝ) ≤ u := by
    have h232 : ((2 : ℝ) ^ (32 : ℕ)) ≤ 2 * (n : ℝ) := by norm_num; linarith
    have h := Real.rpow_le_rpow (by positivity) h232 (by norm_num : (0 : ℝ) ≤ 1 / 32)
    rw [← Real.rpow_natCast (2 : ℝ) 32, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    norm_num at h
    exact h
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hpoly : fStar 7 (2 * (n : ℝ)) 0
      ≤ u ^ 31 + 15 / 32 * u ^ 15 + 1 / 2 * u ^ 7 + 5 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 := by
    have h := fStar7_le_poly32 u hu1
    rwa [hux] at h
  have hwrap : (gFun 7 n : ℝ) ≤ (⌈fStar 7 (2 * (n : ℝ)) 0⌉₊ : ℝ) := by
    exact_mod_cast gk_upper_star 7 (by norm_num) n hn1
  have hf0 : (0 : ℝ) ≤ fStar 7 (2 * (n : ℝ)) 0 :=
    le_trans (by norm_num) (fStar_ge_two 7 (by norm_num) _ 0 hx2 le_rfl)
  have hceil : (⌈fStar 7 (2 * (n : ℝ)) 0⌉₊ : ℝ) < fStar 7 (2 * (n : ℝ)) 0 + 1 :=
    Nat.ceil_lt_add_one hf0
  have hkey := key7_endgame u hu2
  have hu31 : u ^ (31 : ℕ) = (2 * (n : ℝ)) ^ ((31 : ℝ) / 32) := by
    rw [hu_def, ← Real.rpow_natCast ((2 * (n : ℝ)) ^ ((1 : ℝ) / 32)) 31,
      ← Real.rpow_mul hx0]
    norm_num
  have htarget : 2 * (n : ℝ) ^ ((31 : ℝ) / 32)
      = (2 : ℝ) ^ ((1 : ℝ) / 32) * (2 * (n : ℝ)) ^ ((31 : ℝ) / 32) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ (n : ℝ)),
      ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc (gFun 7 n : ℝ) ≤ (⌈fStar 7 (2 * (n : ℝ)) 0⌉₊ : ℝ) := hwrap
    _ < fStar 7 (2 * (n : ℝ)) 0 + 1 := hceil
    _ ≤ u ^ 31 + 15 / 32 * u ^ 15 + 1 / 2 * u ^ 7 + 5 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 + 1 := by
        linarith
    _ < 261 / 256 * u ^ 31 := hkey
    _ ≤ (2 : ℝ) ^ ((1 : ℝ) / 32) * u ^ 31 :=
        mul_le_mul_of_nonneg_right rt32_two (pow_nonneg hu0 31)
    _ = 2 * (n : ℝ) ^ ((31 : ℝ) / 32) := by rw [hu31]; exact htarget.symm

/-! ## 4. fibCnt vs log₂ (hygiene carry, closed) -/

/-- fib(j+2) ≤ 2^j (machine check "fib(j+2) <= 2^j"). -/
lemma fib_add_two_le_two_pow (j : ℕ) : Nat.fib (j + 2) ≤ 2 ^ j := by
  induction j using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more j ih1 ih2 =>
    have e : Nat.fib (j + 2 + 2) = Nat.fib (j + 2) + Nat.fib (j + 2 + 1) :=
      Nat.fib_add_two
    calc Nat.fib (j + 2 + 2) = Nat.fib (j + 2) + Nat.fib (j + 3) := by
          rw [e]
      _ ≤ 2 ^ j + 2 ^ (j + 1) := Nat.add_le_add ih1 ih2
      _ ≤ 2 ^ (j + 2) := by
          have e1 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
          have e2 : (2 : ℕ) ^ (j + 2) = 4 * 2 ^ j := by ring
          omega

open scoped Classical in
/-- **The comparison lemma** (C3→C6 hygiene carry, closed): the Fibonacci
    count strictly dominates the binary logarithm count, Nat.log 2 n + 1 ≤
    fibCnt n for n ≥ 1.  Witnesses: fib 2 < fib 3 < … < fib (log₂ n + 2)
    are log₂ n + 1 distinct Fibonacci values in [1, n]. -/
theorem log2_succ_le_fibCnt (n : ℕ) (hn : 1 ≤ n) :
    Nat.log 2 n + 1 ≤ fibCnt n := by
  unfold fibCnt
  set L := Nat.log 2 n with hL_def
  have hL : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hinj : Function.Injective (fun j : ℕ => Nat.fib (j + 2)) :=
    Nat.fib_add_two_strictMono.injective
  have hsub : (Finset.range (L + 1)).image (fun j : ℕ => Nat.fib (j + 2))
      ⊆ (Finset.Icc 1 n).filter IsFib := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    have hjL : j ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ⟨j + 2, rfl⟩⟩
    · exact Nat.fib_pos.mpr (by omega)
    · exact le_trans (fib_add_two_le_two_pow j)
        (le_trans (Nat.pow_le_pow_right (by norm_num) hjL) hL)
  calc L + 1
      = ((Finset.range (L + 1)).image (fun j : ℕ => Nat.fib (j + 2))).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ ((Finset.Icc 1 n).filter IsFib).card := Finset.card_le_card hsub

/-- Strict improvement of upstream `h5lower` (which gives Nat.log 2 n <
    hFun 5 n): chaining the comparison through `fibCnt_lt_hFun_five`. -/
theorem log2_succ_lt_hFun_five (n : ℕ) (hn : 1 ≤ n) :
    Nat.log 2 n + 1 < hFun 5 n :=
  lt_of_le_of_lt (log2_succ_le_fibCnt n hn) (fibCnt_lt_hFun_five n)

/-! ## Axiom audit (expect NO sorryAx anywhere) -/

#print axioms gk_upper_star
#print axioms g6upper_t2
#print axioms g7upper_t2
#print axioms log2_succ_le_fibCnt
#print axioms log2_succ_lt_hFun_five

end Erdos866
