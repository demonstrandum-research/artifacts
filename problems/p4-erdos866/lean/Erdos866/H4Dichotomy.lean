/-
# Triangle-dichotomy exact-value theorem, kernel-grade:  h₄(n) = 4  (n ≥ 331 777)

C3-P2 built the port scaffold (dense regime, 92-structure endgame, both (K)
double-counts) with ONE load-bearing sorry (`structural_case`).
C4-P1 closed it on the KC1 = 2 corrected chain (C3-P3 GTRANSFER §5) — and the
per-o-pair form of the corrected (K) (`K_epairs_le2`) collapses the zone
machinery to a single balanced-window lemma, giving validity n ≥ 8d + 8
(slope 1/8) and the kernel constant **N₀ = 331 777 = 24⁴ + 1**, BELOW the
paper-grade 4 593 324.  CAP (Fibonacci growth) kills every d ≥ 0, so the
92-structure endgame is no longer on the proof path (kept as belt).
Sources of truth: lenses/P4-frontier/DICHOTOMY.md (C2 hand proof),
lenses/C3P3-frontier-transfer/GTRANSFER.md §5 (corrected constants).

Target, CLOSED sorry-free: `h4_eq_4 : ∀ n, 331777 ≤ n → hFun 4 n = 4`
(+ corollaries at the C3 charter constant 4 593 324 and the C2 8·10⁷).
This file is imported from the root module since C4-P1 (de-quarantined).
Upstream byte-pinned files untouched.

## Decomposition (per DICHOTOMY.md §6 port plan)

  (c)+(d) DENSE REGIME — CLOSED sorry-free here:
    * `fFunPos_four_lt_crossover` : exact crossover F₄(x) < (n−9)/32 + 4 for
      x ≤ 2n−2, n ≥ 8·10⁷.  Key idea: substitute v := (x/2)^(1/4); then
      F₃(x) = 2v² + 4v + 11 EXACTLY and the whole chain is sqrt-free polynomial
      (same trick as P3's u := x^(1/8)).  Avoids upstream's private
      `fFunPos_mono_early` and the far-too-lossy `boundPos` (whose 15·x^(5/8)
      term is ≈2·10⁶ at n = 8·10⁷ — boundPos can NOT prove this crossover).
    * `hasPosPairwiseSums_of_dense` : wiring to upstream `ceslemgeneral_pos` (k=4).
    * `card_odds_Icc`, `evens_card_lower` : the |E| = d+4 counting.
    * `dense_case` : the d > (n−10)/32 branch of the theorem, fully closed.

  (b) ENDGAME — CLOSED sorry-free here, via a NEW certificate format:
    every one of the 92 residual structures admits d+1 (2+2)-combos with
    PAIRWISE DISJOINT cross-sum sets (verified by packing_cert.py, re-checked
    by the kernel via `dichoCerts_ok : decide`).  A |D| ≤ d hitting set cannot
    hit d+1 pairwise disjoint sets (`pigeonhole_disjoint_hits`), so some combo
    survives and fires (`hasPPS_of_combo`): `endgame_no_survivor`.
    This REPLACES the branch-and-bound hitting-set search of endgame.py with a
    pigeonhole certificate — nothing exponential is replayed in the kernel.

  (a) the (K) double-count — CLOSED sorry-free here, BOTH directions:
    `K_opairs_le` (fixed e-pair, bounds o-pairs — X1's form) and
    `K_epairs_le` (fixed o-pair, bounds e-pairs — X'a's form): the kill map
    (pair) ↦ (m ∈ D, cross position ∈ {0..3}) is injective, so ≤ 4|D|.
    This was the charter-identified hardest object (DICHOTOMY.md §6: "the
    hardest genuinely new Lean object is the (K) double-counting");
    formalizing it doubles as the hostile check on the hand reduction — it
    survived.  X2 still needs the triangular-index refinement of (K)
    (combos over a+b ≤ q, not a full product) — roadmap phase P2a.

## Sorry inventory
  NONE since C4-P1.  `structural_case` is proven on the corrected chain
  (Part 3b); `#print axioms` at EOF audits every declaration.
-/
import Erdos866.Upstream
import Erdos866.LowerBounds

open Finset

namespace Erdos866
namespace Dicho

/-! ## Part 1 — the dense regime (sorry-free)

### 1a. The exact-rational crossover

`fFunPos 4 x < (n−9)/32 + 4` for `2 ≤ x ≤ 2n−2`, `n ≥ 8·10⁷`.

With v := (x/2)^(1/4) ≥ 1 (so v⁴ = x/2, √(x/2) = v²):
  fFunPos 3 x = 2v² + 4v + 11 exactly, and
  2x·fFunPos 3 x + 1/4 = 8v⁶ + 16v⁵ + 44v⁴ + 1/4 ≤ p(v)²
for p(v) = (17/6)v³ + (17/6)v² + 7v, since
  p(v)² − (8v⁶+16v⁵+44v⁴) = v⁶/36 + v⁵/18 + 133v⁴/36 + (119/3)v³ + 49v² ≥ 49 > 1/4.
p is monotone, v ≤ u := (n−1)^(1/4), and for u ≥ 94 (94⁴ = 78 074 896 ≤ n−1):
  p(u) + 1/2 < (u⁴−8)/32 + 4  ⟺  3u⁴ − 272u³ − 272u² − 672u + 312 > 0,
which holds for u ≥ 94 (value 5 839 592 at u = 94, increasing).
All constants machine-verified in exact rationals (lens dir, packing_cert run). -/

private lemma fFunPos_three_eq (x : ℝ) :
    fFunPos 3 x = 2 * Real.sqrt (x / 2) + 4 * (x / 2) ^ ((1:ℝ)/4) + 11 := by
  rfl

private lemma fFunPos_four_eq (x : ℝ) :
    fFunPos 4 x = Real.sqrt (2 * x * fFunPos 3 x + 1/4) + 1/2 := by
  rfl

theorem fFunPos_four_lt_crossover (n : ℕ) (hn : 8 * 10 ^ 7 ≤ n)
    (x : ℝ) (hx2 : 2 ≤ x) (hxle : x ≤ 2 * (n : ℝ) - 2) :
    fFunPos 4 x < ((n : ℝ) - 9) / 32 + 4 := by
  have hnR : (8 * 10 ^ 7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hw0 : (0:ℝ) ≤ x / 2 := by linarith
  have hw1 : (1:ℝ) ≤ x / 2 := by linarith
  have hn0 : (0:ℝ) ≤ (n:ℝ) - 1 := by linarith
  set v : ℝ := (x / 2) ^ ((1:ℝ)/4) with hvdef
  set u : ℝ := ((n:ℝ) - 1) ^ ((1:ℝ)/4) with hudef
  have hv0 : 0 ≤ v := Real.rpow_nonneg hw0 _
  have hu0 : 0 ≤ u := Real.rpow_nonneg hn0 _
  have hv1 : 1 ≤ v := Real.one_le_rpow hw1 (by norm_num)
  have hv4 : v ^ 4 = x / 2 := by
    rw [hvdef, ← Real.rpow_natCast ((x/2) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hw0]
    norm_num
  have hu4 : u ^ 4 = (n:ℝ) - 1 := by
    rw [hudef, ← Real.rpow_natCast (((n:ℝ)-1) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hn0]
    norm_num
  have hv2 : Real.sqrt (x/2) = v ^ 2 := by
    rw [hvdef, ← Real.rpow_natCast ((x/2) ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hw0,
      Real.sqrt_eq_rpow]
    norm_num
  have hvu : v ≤ u := by
    rw [hvdef, hudef]
    exact Real.rpow_le_rpow hw0 (by linarith) (by norm_num)
  have hu94 : (94:ℝ) ≤ u := by
    by_contra hlt
    push_neg at hlt
    have h94 : u ^ 4 ≤ 94 ^ 4 := by gcongr
    rw [hu4] at h94
    norm_num at h94
    linarith
  have hF3 : fFunPos 3 x = 2 * v ^ 2 + 4 * v + 11 := by
    rw [fFunPos_three_eq, hv2, ← hvdef]
  have hx4 : x = 2 * v ^ 4 := by rw [hv4]; ring
  have hp0 : (0:ℝ) ≤ 17/6 * v^3 + 17/6 * v^2 + 7*v := by positivity
  have hkey : Real.sqrt (2 * x * fFunPos 3 x + 1/4) ≤ 17/6 * v^3 + 17/6 * v^2 + 7*v := by
    have hv2ge : (1:ℝ) ≤ v ^ 2 := by nlinarith [hv1]
    have harg : 2 * x * fFunPos 3 x + 1/4 ≤ (17/6 * v^3 + 17/6 * v^2 + 7*v) ^ 2 := by
      rw [hF3, hx4]
      nlinarith [hv2ge, pow_nonneg hv0 3, pow_nonneg hv0 4, pow_nonneg hv0 5,
        pow_nonneg hv0 6, sq_nonneg v]
    calc Real.sqrt (2 * x * fFunPos 3 x + 1/4)
        ≤ Real.sqrt ((17/6 * v^3 + 17/6 * v^2 + 7*v) ^ 2) := Real.sqrt_le_sqrt harg
      _ = 17/6 * v^3 + 17/6 * v^2 + 7*v := Real.sqrt_sq hp0
  have hmono : 17/6 * v^3 + 17/6 * v^2 + 7*v ≤ 17/6 * u^3 + 17/6 * u^2 + 7*u := by
    gcongr
  have hfinal : 17/6 * u^3 + 17/6 * u^2 + 7*u + 1/2 < (u^4 - 8)/32 + 4 := by
    have hs : (0:ℝ) ≤ u - 94 := by linarith
    nlinarith [hs, mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs,
      mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs]
  have hn9 : ((n:ℝ) - 9)/32 + 4 = (u^4 - 8)/32 + 4 := by rw [hu4]; ring
  rw [fFunPos_four_eq, hn9]
  linarith [hkey, hmono, hfinal]

/-! ### 1b. Wiring to upstream `ceslemgeneral_pos` (k = 4) -/

theorem hasPosPairwiseSums_of_dense (n : ℕ) (hn : 8 * 10 ^ 7 ≤ n)
    (E : Finset ℤ)
    (hsub : ∀ a ∈ E, (2:ℤ) ≤ a ∧ a ≤ 2 * (n:ℤ))
    (heven : ∀ a ∈ E, (2:ℤ) ∣ a)
    (hcard : ((n:ℝ) - 9) / 32 + 4 ≤ (E.card : ℝ)) :
    HasPosPairwiseSums E 4 := by
  have hnR : (8 * 10 ^ 7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcard2 : 2 ≤ E.card := by
    have h2 : (2:ℝ) ≤ (E.card : ℝ) := by linarith
    exact_mod_cast h2
  have hne : E.Nonempty := Finset.card_pos.mp (by omega)
  have hmaxmem := E.max'_mem hne
  have hminmem := E.min'_mem hne
  have hrange : 2 ≤ E.max' hne - E.min' hne := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < E.card)
    obtain ⟨ka, hka⟩ := heven a ha
    obtain ⟨kb, hkb⟩ := heven b hb
    have h1 := E.min'_le a ha
    have h2 := E.le_max' a ha
    have h3 := E.min'_le b hb
    have h4 := E.le_max' b hb
    omega
  apply ceslemgeneral_pos 4 (by norm_num) E hne heven (fun a ha => (hsub a ha).1) hrange
  -- card side: fFunPos 4 (range) < (n−9)/32 + 4 ≤ E.card
  have hxle : ((E.max' hne - E.min' hne : ℤ) : ℝ) ≤ 2 * (n:ℝ) - 2 := by
    have h1 := (hsub _ hmaxmem).2
    have h2 := (hsub _ hminmem).1
    have h1' : ((E.max' hne : ℤ) : ℝ) ≤ 2 * (n:ℝ) := by exact_mod_cast h1
    have h2' : (2:ℝ) ≤ ((E.min' hne : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast
    push_cast at h1' h2'
    linarith
  have hx2 : (2:ℝ) ≤ ((E.max' hne - E.min' hne : ℤ) : ℝ) := by exact_mod_cast hrange
  have := fFunPos_four_lt_crossover n hn _ hx2 hxle
  linarith

/-! ### 1c. The |E| ≥ d + 4 counting -/

/-- The set of odd numbers of the window [1, 2n] missing from A ("D" in
DICHOTOMY.md §0).  d := (missingOdds n A).card. -/
def missingOdds (n : ℕ) (A : Finset ℤ) : Finset ℤ :=
  (Finset.Icc (1:ℤ) (2*(n:ℤ))).filter (fun x => x % 2 = 1 ∧ x ∉ A)

/-- There are exactly n odd numbers in [1, 2n]. -/
lemma card_odds_Icc (n : ℕ) :
    ((Finset.Icc (1:ℤ) (2*(n:ℤ))).filter (fun x => x % 2 = 1)).card = n := by
  induction n with
  | zero => simp
  | succ m ih =>
      have hins : Finset.Icc (1:ℤ) (2*((m:ℤ)+1)) =
          insert (2*(m:ℤ)+1) (insert (2*(m:ℤ)+2) (Finset.Icc (1:ℤ) (2*(m:ℤ)))) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hcast : (((m+1 : ℕ)):ℤ) = (m:ℤ) + 1 := by push_cast; ring
      rw [hcast, hins, Finset.filter_insert, Finset.filter_insert,
        if_pos (by omega : (2*(m:ℤ)+1) % 2 = 1), if_neg (by omega : ¬(2*(m:ℤ)+2) % 2 = 1),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_filter, Finset.mem_Icc]
          omega), ih]

/-- |E| ≥ d + 4 when |A| ≥ n + 4 (DICHOTOMY.md §0: |A| = (n−d) + |E|). -/
lemma evens_card_lower (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc (1:ℤ) (2*(n:ℤ))) (hcard : n + 4 ≤ A.card) :
    (missingOdds n A).card + 4 ≤ (A.filter (fun x => x % 2 = 0)).card := by
  classical
  have hsplit : (A.filter (fun x => x % 2 = 1)).card
      + (A.filter (fun x => x % 2 = 0)).card = A.card := by
    have hneg : A.filter (fun x => ¬ x % 2 = 1) = A.filter (fun x => x % 2 = 0) := by
      apply Finset.filter_congr
      intro x _
      constructor
      · intro h; omega
      · intro h; omega
    rw [← hneg, Finset.filter_card_add_filter_neg_card_eq_card]
  have hsub : (A.filter (fun x => x % 2 = 1)) ∪ missingOdds n A
      ⊆ (Finset.Icc (1:ℤ) (2*(n:ℤ))).filter (fun x => x % 2 = 1) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨hxA, hxo⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hA hxA, hxo⟩
    · obtain ⟨hxI, hxo, _⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨hxI, hxo⟩
  have hdisj : Disjoint (A.filter (fun x => x % 2 = 1)) (missingOdds n A) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact ((Finset.mem_filter.mp hx').2).2 ((Finset.mem_filter.mp hx).1)
  have hunion := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_card hsub
  rw [hunion, card_odds_Icc] at hle
  omega

/-- The DENSE branch of the dichotomy, fully closed: if n ≥ 8·10⁷ and the
missing-odd count d satisfies 32d + 10 > n, surplus 4 forces a positive
4-configuration. -/
theorem dense_case (n : ℕ) (hn : 8 * 10 ^ 7 ≤ n) (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc (1:ℤ) (2*(n:ℤ))) (hcard : n + 4 ≤ A.card)
    (hd : n < 32 * (missingOdds n A).card + 10) :
    HasPosPairwiseSums A 4 := by
  classical
  have hEcard := evens_card_lower n A hA hcard
  have hpps : HasPosPairwiseSums (A.filter (fun x => x % 2 = 0)) 4 := by
    apply hasPosPairwiseSums_of_dense n hn
    · intro a ha
      obtain ⟨haA, hae⟩ := Finset.mem_filter.mp ha
      have hbounds := Finset.mem_Icc.mp (hA haA)
      constructor <;> omega
    · intro a ha
      have hae := (Finset.mem_filter.mp ha).2
      omega
    · have h1 : (n:ℝ) ≤ 32 * ((missingOdds n A).card : ℝ) + 9 := by
        exact_mod_cast (by omega : n ≤ 32 * (missingOdds n A).card + 9)
      have h2 : ((missingOdds n A).card : ℝ) + 4
          ≤ ((A.filter (fun x => x % 2 = 0)).card : ℝ) := by exact_mod_cast hEcard
      linarith
  obtain ⟨b, hinj, hpos, hsums⟩ := hpps
  exact ⟨b, hinj, hpos, fun i j hij => Finset.filter_subset _ _ (hsums i j hij)⟩

/-! ### 1d. The slope-1/8 dense regime for the KC1 = 2 corrected chain (C4-P1)

With the corrected kill count (GTRANSFER §5: one missing odd kills at most TWO
e-pairs per fixed (s,t,o-pair), not four — `K_epairs_le2` below), the
structural regime needs only n ≥ 8d+8, so the dense branch fires at
d > (n−8)/8 and the coverage condition becomes (n−7)/8 + 4 > F₄(2n−2).
Same v-substitution; final polynomial 3u⁴ − 68u³ − 68u² − 168u + 66 > 0 for
u ≥ 24 (value 12 162 at u = 24; in s := u−24 the polynomial is
3s⁴ + 220s³ + 5404s² + 44952s + 12162, all coefficients positive).
24⁴ = 331 776, so the crossover constant is N₀ = 331 777. -/

theorem fFunPos_four_lt_crossover8 (n : ℕ) (hn : 331777 ≤ n)
    (x : ℝ) (hx2 : 2 ≤ x) (hxle : x ≤ 2 * (n : ℝ) - 2) :
    fFunPos 4 x < ((n : ℝ) - 7) / 8 + 4 := by
  have hnR : (331777 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hw0 : (0:ℝ) ≤ x / 2 := by linarith
  have hw1 : (1:ℝ) ≤ x / 2 := by linarith
  have hn0 : (0:ℝ) ≤ (n:ℝ) - 1 := by linarith
  set v : ℝ := (x / 2) ^ ((1:ℝ)/4) with hvdef
  set u : ℝ := ((n:ℝ) - 1) ^ ((1:ℝ)/4) with hudef
  have hv0 : 0 ≤ v := Real.rpow_nonneg hw0 _
  have hu0 : 0 ≤ u := Real.rpow_nonneg hn0 _
  have hv1 : 1 ≤ v := Real.one_le_rpow hw1 (by norm_num)
  have hv4 : v ^ 4 = x / 2 := by
    rw [hvdef, ← Real.rpow_natCast ((x/2) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hw0]
    norm_num
  have hu4 : u ^ 4 = (n:ℝ) - 1 := by
    rw [hudef, ← Real.rpow_natCast (((n:ℝ)-1) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hn0]
    norm_num
  have hv2 : Real.sqrt (x/2) = v ^ 2 := by
    rw [hvdef, ← Real.rpow_natCast ((x/2) ^ ((1:ℝ)/4)) 2, ← Real.rpow_mul hw0,
      Real.sqrt_eq_rpow]
    norm_num
  have hvu : v ≤ u := by
    rw [hvdef, hudef]
    exact Real.rpow_le_rpow hw0 (by linarith) (by norm_num)
  have hu24 : (24:ℝ) ≤ u := by
    by_contra hlt
    push_neg at hlt
    have h24 : u ^ 4 < 24 ^ 4 := by
      have h2 : u ^ 2 < 24 ^ 2 := by nlinarith [hu0, hlt]
      have h2n : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
      nlinarith [h2, h2n]
    rw [hu4] at h24
    norm_num at h24
    linarith
  have hF3 : fFunPos 3 x = 2 * v ^ 2 + 4 * v + 11 := by
    rw [fFunPos_three_eq, hv2, ← hvdef]
  have hx4 : x = 2 * v ^ 4 := by rw [hv4]; ring
  have hp0 : (0:ℝ) ≤ 17/6 * v^3 + 17/6 * v^2 + 7*v := by positivity
  have hkey : Real.sqrt (2 * x * fFunPos 3 x + 1/4) ≤ 17/6 * v^3 + 17/6 * v^2 + 7*v := by
    have hv2ge : (1:ℝ) ≤ v ^ 2 := by nlinarith [hv1]
    have harg : 2 * x * fFunPos 3 x + 1/4 ≤ (17/6 * v^3 + 17/6 * v^2 + 7*v) ^ 2 := by
      rw [hF3, hx4]
      nlinarith [hv2ge, pow_nonneg hv0 3, pow_nonneg hv0 4, pow_nonneg hv0 5,
        pow_nonneg hv0 6, sq_nonneg v]
    calc Real.sqrt (2 * x * fFunPos 3 x + 1/4)
        ≤ Real.sqrt ((17/6 * v^3 + 17/6 * v^2 + 7*v) ^ 2) := Real.sqrt_le_sqrt harg
      _ = 17/6 * v^3 + 17/6 * v^2 + 7*v := Real.sqrt_sq hp0
  have hmono : 17/6 * v^3 + 17/6 * v^2 + 7*v ≤ 17/6 * u^3 + 17/6 * u^2 + 7*u := by
    gcongr
  have hfinal : 17/6 * u^3 + 17/6 * u^2 + 7*u + 1/2 < (u^4 - 6)/8 + 4 := by
    have hs : (0:ℝ) ≤ u - 24 := by linarith
    nlinarith [hs, mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs,
      mul_nonneg (mul_nonneg (mul_nonneg hs hs) hs) hs]
  have hn7 : ((n:ℝ) - 7)/8 + 4 = (u^4 - 6)/8 + 4 := by rw [hu4]; ring
  rw [fFunPos_four_eq, hn7]
  linarith [hkey, hmono, hfinal]

theorem hasPosPairwiseSums_of_dense8 (n : ℕ) (hn : 331777 ≤ n)
    (E : Finset ℤ)
    (hsub : ∀ a ∈ E, (2:ℤ) ≤ a ∧ a ≤ 2 * (n:ℤ))
    (heven : ∀ a ∈ E, (2:ℤ) ∣ a)
    (hcard : ((n:ℝ) - 7) / 8 + 4 ≤ (E.card : ℝ)) :
    HasPosPairwiseSums E 4 := by
  have hnR : (331777 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcard2 : 2 ≤ E.card := by
    have h2 : (2:ℝ) ≤ (E.card : ℝ) := by linarith
    exact_mod_cast h2
  have hne : E.Nonempty := Finset.card_pos.mp (by omega)
  have hmaxmem := E.max'_mem hne
  have hminmem := E.min'_mem hne
  have hrange : 2 ≤ E.max' hne - E.min' hne := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < E.card)
    obtain ⟨ka, hka⟩ := heven a ha
    obtain ⟨kb, hkb⟩ := heven b hb
    have h1 := E.min'_le a ha
    have h2 := E.le_max' a ha
    have h3 := E.min'_le b hb
    have h4 := E.le_max' b hb
    omega
  apply ceslemgeneral_pos 4 (by norm_num) E hne heven (fun a ha => (hsub a ha).1) hrange
  have hxle : ((E.max' hne - E.min' hne : ℤ) : ℝ) ≤ 2 * (n:ℝ) - 2 := by
    have h1 := (hsub _ hmaxmem).2
    have h2 := (hsub _ hminmem).1
    have h1' : ((E.max' hne : ℤ) : ℝ) ≤ 2 * (n:ℝ) := by exact_mod_cast h1
    have h2' : (2:ℝ) ≤ ((E.min' hne : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast
    push_cast at h1' h2'
    linarith
  have hx2 : (2:ℝ) ≤ ((E.max' hne - E.min' hne : ℤ) : ℝ) := by exact_mod_cast hrange
  have := fFunPos_four_lt_crossover8 n hn _ hx2 hxle
  linarith

/-- The DENSE branch of the corrected chain: n ≥ 331 777 and 8d + 8 > n force
a positive 4-configuration at surplus 4. -/
theorem dense_case8 (n : ℕ) (hn : 331777 ≤ n) (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc (1:ℤ) (2*(n:ℤ))) (hcard : n + 4 ≤ A.card)
    (hd : n < 8 * (missingOdds n A).card + 8) :
    HasPosPairwiseSums A 4 := by
  classical
  have hEcard := evens_card_lower n A hA hcard
  have hpps : HasPosPairwiseSums (A.filter (fun x => x % 2 = 0)) 4 := by
    apply hasPosPairwiseSums_of_dense8 n hn
    · intro a ha
      obtain ⟨haA, hae⟩ := Finset.mem_filter.mp ha
      have hbounds := Finset.mem_Icc.mp (hA haA)
      constructor <;> omega
    · intro a ha
      have hae := (Finset.mem_filter.mp ha).2
      omega
    · have h1 : (n:ℝ) ≤ 8 * ((missingOdds n A).card : ℝ) + 7 := by
        exact_mod_cast (by omega : n ≤ 8 * (missingOdds n A).card + 7)
      have h2 : ((missingOdds n A).card : ℝ) + 4
          ≤ ((A.filter (fun x => x % 2 = 0)).card : ℝ) := by exact_mod_cast hEcard
      linarith
  obtain ⟨b, hinj, hpos, hsums⟩ := hpps
  exact ⟨b, hinj, hpos, fun i j hij => Finset.filter_subset _ _ (hsums i j hij)⟩

/-! ## Part 2 — the 92-structure endgame as a packing certificate (sorry-free)

The hand proof (DICHOTOMY.md §3, Endgame (b)) shows: in the structural regime
with TOP = ∅, E = 2Λ for one of exactly 92 triangle-free Λ (d ∈ {1,2,3,4}),
and config-freeness forces D to HIT every (2+2)-combo's cross-sum set —
impossible because no hitting set of size d exists (endgame.py).

Lean-side reformulation (this lens): for each structure we certify d+1 combos
with PAIRWISE DISJOINT cross-sum sets (packing_cert.py, 92/92).  Then a
|D| ≤ d hitting set loses by pigeonhole — no search is replayed in the kernel,
only the certificate is checked (`decide`). -/

/-- A (2+2) witness: (s, t, o₁, o₂, e₁, e₂). -/
abbrev W := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

/-- The four (odd) cross sums of a witness. -/
def crossOf : W → List ℤ
  | (_, _, o₁, o₂, e₁, e₂) => [o₁ + e₁, o₁ + e₂, o₂ + e₁, o₂ + e₂]

/-- Validity of one witness against the structure's even set:
positivity, ordering, parities, sums in 2Λ, and the cap o₂+e₂ ≤ 49
(so cross sums fit below 2n−1 for every n ≥ 25). -/
def wOk (evens : List ℤ) (s t o₁ o₂ e₁ e₂ : ℤ) : Prop :=
  0 < o₁ ∧ o₁ < o₂ ∧ 0 < e₁ ∧ e₁ < e₂ ∧
  o₁ % 2 = 1 ∧ o₂ % 2 = 1 ∧ e₁ % 2 = 0 ∧ e₂ % 2 = 0 ∧
  o₁ + o₂ = s ∧ e₁ + e₂ = t ∧ o₂ + e₂ ≤ 49 ∧ s ∈ evens ∧ t ∈ evens

instance (evens : List ℤ) (s t o₁ o₂ e₁ e₂ : ℤ) :
    Decidable (wOk evens s t o₁ o₂ e₁ e₂) := by
  unfold wOk; infer_instance

def wOkB (evens : List ℤ) : W → Bool
  | (s, t, o₁, o₂, e₁, e₂) => decide (wOk evens s t o₁ o₂ e₁ e₂)

/-- l and l' share no element. -/
def disjB (l l' : List ℤ) : Bool := l.all (fun x => decide (x ∉ l'))

def pwDisjB : List (List ℤ) → Bool
  | [] => true
  | l :: ls => ls.all (disjB l) && pwDisjB ls

/-- One endgame structure: deficiency d, low evens E = 2Λ, and d+1 witnesses. -/
structure EndgameCert where
  d : ℕ
  evens : List ℤ
  ws : List W

def certOkB (c : EndgameCert) : Bool :=
  decide (c.ws.length = c.d + 1) && c.ws.all (wOkB c.evens) && pwDisjB (c.ws.map crossOf)

/-- Bool-to-Prop bridge for the pairwise-disjointness checker. -/
lemma pwDisjB_spec : ∀ L : List (List ℤ), pwDisjB L = true →
    L.Pairwise (fun l l' => ∀ x ∈ l, x ∉ l') := by
  intro L
  induction L with
  | nil => intro _; exact List.Pairwise.nil
  | cons l ls ih =>
      intro h
      simp only [pwDisjB, Bool.and_eq_true, List.all_eq_true, disjB,
        decide_eq_true_eq] at h
      exact List.Pairwise.cons (fun l' hl' x hx => h.1 l' hl' x hx) (ih h.2)

/-- Pigeonhole: pairwise-disjoint nonempty hits need |D| ≥ length. -/
lemma pigeonhole_disjoint_hits :
    ∀ (L : List (List ℤ)) (D : Finset ℤ),
      L.Pairwise (fun l l' => ∀ x ∈ l, x ∉ l') →
      (∀ l ∈ L, ∃ x ∈ l, x ∈ D) → L.length ≤ D.card := by
  intro L
  induction L with
  | nil => intro D _ _; simp
  | cons l ls ih =>
      intro D hpw hhit
      obtain ⟨x, hxl, hxD⟩ := hhit l (by simp)
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
      have htl : ∀ l' ∈ ls, ∃ y ∈ l', y ∈ D.erase x := by
        intro l' hl'
        obtain ⟨y, hyl', hyD⟩ := hhit l' (List.mem_cons_of_mem l hl')
        refine ⟨y, hyl', Finset.mem_erase.mpr ⟨fun hyx => ?_, hyD⟩⟩
        exact hhead l' hl' x hxl (hyx ▸ hyl')
      have h1 := ih (D.erase x) htail htl
      have h2 := Finset.card_erase_of_mem hxD
      have h3 : 0 < D.card := Finset.card_pos.mpr ⟨x, hxD⟩
      simp only [List.length_cons]
      omega

/-- The (2+2) machine fires: an explicit positive 4-configuration. -/
lemma hasPPS_of_combo {A : Finset ℤ} {o₁ o₂ e₁ e₂ : ℤ}
    (ho1 : 0 < o₁) (ho12 : o₁ < o₂) (he1 : 0 < e₁) (he12 : e₁ < e₂)
    (hop1 : o₁ % 2 = 1) (hop2 : o₂ % 2 = 1) (hep1 : e₁ % 2 = 0) (hep2 : e₂ % 2 = 0)
    (hs : o₁ + o₂ ∈ A) (ht : e₁ + e₂ ∈ A)
    (h11 : o₁ + e₁ ∈ A) (h12 : o₁ + e₂ ∈ A) (h21 : o₂ + e₁ ∈ A) (h22 : o₂ + e₂ ∈ A) :
    HasPosPairwiseSums A 4 := by
  refine ⟨fun i : Fin 4 =>
    if i = 0 then o₁ else if i = 1 then o₂ else if i = 2 then e₁ else e₂, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp at hij; omega)
  · intro i
    fin_cases i <;> simp <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp only []; norm_num; assumption)

/-- ENDGAME, certified: if A contains all in-window odds outside D plus the
structure's evens, |D| ≤ d, and the certificate checks, A has a positive
4-configuration.  (Contrapositive of "D must hit every combo".) -/
theorem endgame_no_survivor (n : ℕ) (hn : 25 ≤ n) (A D : Finset ℤ)
    (c : EndgameCert) (hc : certOkB c = true) (hDcard : D.card ≤ c.d)
    (hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A)
    (hE : ∀ s ∈ c.evens, s ∈ A) :
    HasPosPairwiseSums A 4 := by
  by_contra hfree
  have hnZ : (25:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
  simp only [certOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨hlen, hall⟩, hpw⟩ := hc
  have hhit : ∀ l ∈ c.ws.map crossOf, ∃ x ∈ l, x ∈ D := by
    intro l hl
    rw [List.mem_map] at hl
    obtain ⟨w, hw, rfl⟩ := hl
    by_contra hno
    push_neg at hno
    obtain ⟨s, t, o₁, o₂, e₁, e₂⟩ := w
    have hwk : wOk c.evens s t o₁ o₂ e₁ e₂ := by
      have := hall _ hw
      simpa only [wOkB, decide_eq_true_eq] using this
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hwk
    have hcr : ∀ y ∈ crossOf (s, t, o₁, o₂, e₁, e₂), y ∈ A := by
      intro y hy
      have hyD := hno y hy
      simp only [crossOf, List.mem_cons, List.not_mem_nil, or_false] at hy
      refine hodd y ?_ ?_ ?_ hyD
      all_goals rcases hy with rfl | rfl | rfl | rfl <;> omega
    refine hfree (hasPPS_of_combo h1 h2 h3 h4 h5 h6 h7 h8 ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [h9]; exact hE s h12
    · rw [h10]; exact hE t h13
    · exact hcr _ (by simp [crossOf])
    · exact hcr _ (by simp [crossOf])
    · exact hcr _ (by simp [crossOf])
    · exact hcr _ (by simp [crossOf])
  have hpwP := pwDisjB_spec _ hpw
  have hlen2 : (c.ws.map crossOf).length = c.d + 1 := by
    rw [List.length_map, hlen]
  have := pigeonhole_disjoint_hits (c.ws.map crossOf) D hpwP hhit
  omega

/-! ### 2b. The 92 certificates (generated from packing_certs.json;
7 / 42 / 42 / 1 structures for d = 1 / 2 / 3 / 4 — counts match
DICHOTOMY.md §3 Endgame (b) exactly). -/

def dichoCerts : List EndgameCert := [
  ⟨1, [2, 4, 6, 10, 16], [(4, 6, 1, 3, 2, 4), (10, 16, 3, 7, 6, 10)]⟩,
  ⟨1, [2, 4, 6, 10, 18], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10)]⟩,
  ⟨1, [2, 4, 6, 10, 20], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12)]⟩,
  ⟨1, [2, 4, 6, 12, 18], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10)]⟩,
  ⟨1, [2, 4, 6, 12, 20], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12)]⟩,
  ⟨1, [2, 4, 6, 14, 20], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12)]⟩,
  ⟨1, [2, 4, 8, 12, 20], [(4, 8, 1, 3, 2, 6), (8, 20, 3, 5, 8, 12)]⟩,
  ⟨2, [2, 4, 6, 10, 16, 26], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (16, 26, 3, 13, 8, 18)]⟩,
  ⟨2, [2, 4, 6, 10, 16, 28], [(4, 6, 1, 3, 2, 4), (6, 28, 1, 5, 12, 16), (10, 28, 1, 9, 10, 18)]⟩,
  ⟨2, [2, 4, 6, 10, 16, 30], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (16, 6, 7, 9, 2, 4)]⟩,
  ⟨2, [2, 4, 6, 10, 16, 32], [(4, 6, 1, 3, 2, 4), (6, 32, 1, 5, 14, 18), (10, 16, 3, 7, 6, 10)]⟩,
  ⟨2, [2, 4, 6, 10, 16, 34], [(4, 6, 1, 3, 2, 4), (4, 34, 1, 3, 16, 18), (16, 6, 7, 9, 2, 4)]⟩,
  ⟨2, [2, 4, 6, 10, 16, 36], [(4, 6, 1, 3, 2, 4), (6, 36, 1, 5, 16, 20), (10, 36, 1, 9, 14, 22)]⟩,
  ⟨2, [2, 4, 6, 10, 18, 28], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (10, 28, 3, 7, 12, 16)]⟩,
  ⟨2, [2, 4, 6, 10, 18, 30], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16)]⟩,
  ⟨2, [2, 4, 6, 10, 18, 32], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 32, 1, 5, 14, 18)]⟩,
  ⟨2, [2, 4, 6, 10, 18, 34], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 34, 1, 3, 16, 18)]⟩,
  ⟨2, [2, 4, 6, 10, 18, 36], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 36, 1, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 10, 20, 30], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (20, 30, 3, 17, 8, 22)]⟩,
  ⟨2, [2, 4, 6, 10, 20, 32], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12), (6, 32, 1, 5, 14, 18)]⟩,
  ⟨2, [2, 4, 6, 10, 20, 34], [(4, 6, 1, 3, 2, 4), (4, 34, 1, 3, 16, 18), (20, 6, 9, 11, 2, 4)]⟩,
  ⟨2, [2, 4, 6, 10, 20, 36], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12), (10, 20, 3, 7, 8, 12)]⟩,
  ⟨2, [2, 4, 6, 10, 22, 32], [(4, 6, 1, 3, 2, 4), (4, 22, 1, 3, 10, 12), (10, 32, 3, 7, 14, 18)]⟩,
  ⟨2, [2, 4, 6, 10, 22, 34], [(4, 6, 1, 3, 2, 4), (4, 22, 1, 3, 10, 12), (4, 34, 1, 3, 16, 18)]⟩,
  ⟨2, [2, 4, 6, 10, 22, 36], [(4, 6, 1, 3, 2, 4), (4, 22, 1, 3, 10, 12), (6, 36, 1, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 10, 24, 34], [(4, 6, 1, 3, 2, 4), (4, 34, 1, 3, 16, 18), (24, 34, 3, 21, 8, 26)]⟩,
  ⟨2, [2, 4, 6, 10, 24, 36], [(4, 6, 1, 3, 2, 4), (6, 24, 1, 5, 10, 14), (6, 36, 1, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 10, 26, 36], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (10, 36, 3, 7, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 12, 18, 30], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16)]⟩,
  ⟨2, [2, 4, 6, 12, 18, 32], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 32, 1, 5, 14, 18)]⟩,
  ⟨2, [2, 4, 6, 12, 18, 34], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 34, 1, 3, 16, 18)]⟩,
  ⟨2, [2, 4, 6, 12, 18, 36], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 36, 1, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 12, 20, 32], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12), (6, 32, 1, 5, 14, 18)]⟩,
  ⟨2, [2, 4, 6, 12, 20, 34], [(4, 6, 1, 3, 2, 4), (4, 34, 1, 3, 16, 18), (12, 34, 1, 11, 12, 22)]⟩,
  ⟨2, [2, 4, 6, 12, 20, 36], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12), (36, 6, 17, 19, 2, 4)]⟩,
  ⟨2, [2, 4, 6, 12, 22, 34], [(4, 6, 1, 3, 2, 4), (4, 22, 1, 3, 10, 12), (4, 34, 1, 3, 16, 18)]⟩,
  ⟨2, [2, 4, 6, 12, 22, 36], [(4, 6, 1, 3, 2, 4), (4, 22, 1, 3, 10, 12), (6, 36, 1, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 12, 24, 36], [(4, 6, 1, 3, 2, 4), (6, 24, 1, 5, 10, 14), (6, 36, 1, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 14, 20, 34], [(4, 6, 1, 3, 2, 4), (4, 34, 1, 3, 16, 18), (20, 6, 9, 11, 2, 4)]⟩,
  ⟨2, [2, 4, 6, 14, 20, 36], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12), (14, 36, 5, 9, 16, 20)]⟩,
  ⟨2, [2, 4, 6, 14, 22, 36], [(4, 6, 1, 3, 2, 4), (4, 22, 1, 3, 10, 12), (6, 36, 1, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 8, 12, 20, 32], [(4, 8, 1, 3, 2, 6), (4, 32, 1, 3, 10, 22), (4, 32, 1, 3, 14, 18)]⟩,
  ⟨2, [2, 4, 8, 12, 20, 34], [(4, 34, 1, 3, 16, 18), (12, 34, 1, 11, 12, 22), (20, 34, 1, 19, 8, 26)]⟩,
  ⟨2, [2, 4, 8, 12, 20, 36], [(4, 8, 1, 3, 2, 6), (4, 36, 1, 3, 10, 26), (4, 36, 1, 3, 14, 22)]⟩,
  ⟨2, [2, 4, 8, 12, 22, 34], [(4, 22, 1, 3, 10, 12), (4, 34, 1, 3, 16, 18), (4, 8, 1, 3, 2, 6)]⟩,
  ⟨2, [2, 4, 8, 12, 22, 36], [(4, 22, 1, 3, 10, 12), (12, 22, 1, 11, 6, 16), (22, 36, 1, 21, 8, 28)]⟩,
  ⟨2, [2, 4, 8, 12, 24, 36], [(4, 8, 1, 3, 2, 6), (4, 24, 1, 3, 10, 14), (8, 36, 3, 5, 16, 20)]⟩,
  ⟨2, [2, 4, 8, 14, 22, 36], [(4, 14, 1, 3, 6, 8), (8, 22, 3, 5, 10, 12), (14, 36, 5, 9, 16, 20)]⟩,
  ⟨2, [2, 6, 8, 14, 22, 36], [(6, 8, 1, 5, 2, 6), (6, 36, 1, 5, 16, 20), (22, 36, 1, 21, 8, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 26, 42], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (4, 42, 1, 3, 20, 22), (16, 42, 3, 13, 16, 26)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 26, 44], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (6, 44, 1, 5, 20, 24), (10, 44, 1, 9, 18, 26)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 26, 46], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (4, 46, 1, 3, 22, 24), (16, 26, 3, 13, 8, 18)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 26, 48], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (6, 48, 1, 5, 22, 26), (10, 48, 1, 9, 20, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 26, 50], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (4, 50, 1, 3, 24, 26), (16, 26, 3, 13, 8, 18)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 26, 52], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (6, 52, 1, 5, 24, 28), (10, 52, 1, 9, 22, 30)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 28, 44], [(4, 6, 1, 3, 2, 4), (6, 28, 1, 5, 12, 16), (10, 28, 1, 9, 10, 18), (10, 44, 1, 9, 14, 30)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 28, 46], [(4, 6, 1, 3, 2, 4), (4, 46, 1, 3, 22, 24), (6, 28, 1, 5, 12, 16), (16, 46, 7, 9, 22, 24)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 28, 48], [(4, 6, 1, 3, 2, 4), (6, 28, 1, 5, 12, 16), (6, 48, 1, 5, 22, 26), (10, 48, 3, 7, 22, 26)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 28, 50], [(4, 6, 1, 3, 2, 4), (4, 50, 1, 3, 24, 26), (6, 28, 1, 5, 12, 16), (10, 28, 3, 7, 12, 16)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 28, 52], [(4, 6, 1, 3, 2, 4), (6, 28, 1, 5, 12, 16), (6, 52, 1, 5, 24, 28), (10, 28, 1, 9, 10, 18)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 30, 46], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (4, 46, 1, 3, 22, 24), (16, 6, 7, 9, 2, 4)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 30, 48], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (6, 48, 1, 5, 22, 26), (10, 48, 1, 9, 20, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 30, 50], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (4, 50, 1, 3, 24, 26), (16, 6, 7, 9, 2, 4)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 30, 52], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (6, 52, 1, 5, 24, 28), (10, 52, 1, 9, 22, 30)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 32, 48], [(4, 6, 1, 3, 2, 4), (6, 32, 1, 5, 14, 18), (10, 16, 3, 7, 6, 10), (10, 48, 1, 9, 20, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 32, 50], [(4, 6, 1, 3, 2, 4), (4, 50, 1, 3, 24, 26), (6, 32, 1, 5, 14, 18), (10, 16, 3, 7, 6, 10)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 32, 52], [(4, 6, 1, 3, 2, 4), (6, 32, 1, 5, 14, 18), (6, 52, 1, 5, 24, 28), (10, 16, 3, 7, 6, 10)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 34, 50], [(4, 6, 1, 3, 2, 4), (4, 34, 1, 3, 16, 18), (4, 50, 1, 3, 24, 26), (16, 6, 7, 9, 2, 4)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 34, 52], [(4, 6, 1, 3, 2, 4), (4, 34, 1, 3, 16, 18), (6, 52, 1, 5, 24, 28), (10, 52, 1, 9, 22, 30)]⟩,
  ⟨3, [2, 4, 6, 10, 16, 36, 52], [(4, 6, 1, 3, 2, 4), (6, 36, 1, 5, 16, 20), (10, 36, 1, 9, 14, 22), (16, 6, 7, 9, 2, 4)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 28, 46], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 46, 1, 3, 22, 24), (28, 6, 13, 15, 2, 4)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 28, 48], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 48, 1, 5, 22, 26), (10, 48, 1, 9, 20, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 28, 50], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 50, 1, 3, 24, 26), (10, 28, 3, 7, 12, 16)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 28, 52], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 52, 1, 5, 24, 28), (10, 28, 3, 7, 12, 16)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 30, 48], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16), (6, 48, 1, 5, 22, 26)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 30, 50], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16), (4, 50, 1, 3, 24, 26)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 30, 52], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 32, 50], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 50, 1, 3, 24, 26), (6, 32, 1, 5, 14, 18)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 32, 52], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 32, 1, 5, 14, 18), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 18, 34, 52], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 34, 1, 3, 16, 18), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 6, 10, 20, 30, 50], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (4, 50, 1, 3, 24, 26), (20, 50, 3, 17, 18, 32)]⟩,
  ⟨3, [2, 4, 6, 10, 20, 30, 52], [(4, 6, 1, 3, 2, 4), (4, 30, 1, 3, 14, 16), (6, 52, 1, 5, 24, 28), (10, 52, 1, 9, 22, 30)]⟩,
  ⟨3, [2, 4, 6, 10, 20, 32, 52], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12), (6, 32, 1, 5, 14, 18), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 6, 12, 18, 30, 48], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16), (6, 48, 1, 5, 22, 26)]⟩,
  ⟨3, [2, 4, 6, 12, 18, 30, 50], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16), (4, 50, 1, 3, 24, 26)]⟩,
  ⟨3, [2, 4, 6, 12, 18, 30, 52], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 30, 1, 3, 14, 16), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 6, 12, 18, 32, 50], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 50, 1, 3, 24, 26), (6, 32, 1, 5, 14, 18)]⟩,
  ⟨3, [2, 4, 6, 12, 18, 32, 52], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (6, 32, 1, 5, 14, 18), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 6, 12, 18, 34, 52], [(4, 6, 1, 3, 2, 4), (4, 18, 1, 3, 8, 10), (4, 34, 1, 3, 16, 18), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 6, 12, 20, 32, 52], [(4, 6, 1, 3, 2, 4), (6, 20, 1, 5, 8, 12), (6, 32, 1, 5, 14, 18), (6, 52, 1, 5, 24, 28)]⟩,
  ⟨3, [2, 4, 8, 12, 20, 32, 52], [(4, 8, 1, 3, 2, 6), (4, 32, 1, 3, 10, 22), (4, 32, 1, 3, 14, 18), (8, 52, 3, 5, 24, 28)]⟩,
  ⟨4, [2, 4, 6, 10, 16, 26, 42, 68], [(4, 6, 1, 3, 2, 4), (4, 26, 1, 3, 12, 14), (4, 42, 1, 3, 20, 22), (6, 68, 1, 5, 32, 36), (10, 68, 1, 9, 30, 38)]⟩
]

set_option maxHeartbeats 4000000 in
/-- Kernel check of all 92 packing certificates. -/
theorem dichoCerts_ok : dichoCerts.all certOkB = true := by decide

theorem certOkB_of_mem {c : EndgameCert} (hc : c ∈ dichoCerts) : certOkB c = true := by
  have h := dichoCerts_ok
  rw [List.all_eq_true] at h
  exact h c hc

/-! ## Part 3 — the structural regime: scaffold + the load-bearing sorry -/

/-- (K) — THE hardest genuinely new object of the port (DICHOTOMY.md §0/§6),
CLOSED: for fixed even s, t ∈ A and a fixed admissible e-pair of t, in a
4-config-free A every o-pair of s is killed by some m ∈ D at one of 4 cross
positions, and (m, position) determines the o-pair (o_i = m − e_j, companion
via s).  Hence |o-pairs| ≤ 4|D|.  Engine of zone lemmas X1/X'a/X'b; X2 needs
the triangular-index refinement (lens STATUS, phase P2a). -/
theorem K_opairs_le (n : ℕ) (A D : Finset ℤ)
    (hfree : ¬ HasPosPairwiseSums A 4)
    (hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A)
    (s t e₁ e₂ : ℤ) (hs : s ∈ A) (ht : t ∈ A) (het : e₁ + e₂ = t)
    (he1 : 0 < e₁) (he12 : e₁ < e₂) (hep1 : e₁ % 2 = 0) (hep2 : e₂ % 2 = 0)
    (OP : Finset (ℤ × ℤ))
    (hOP : ∀ p ∈ OP, 0 < p.1 ∧ p.1 < p.2 ∧ p.1 % 2 = 1 ∧ p.2 % 2 = 1 ∧
      p.1 + p.2 = s ∧ p.2 + e₂ ≤ 2*(n:ℤ) - 1) :
    OP.card ≤ 4 * D.card := by
  classical
  -- Step 1: every o-pair has a cross sum in D (else the combo fires).
  have hkill : ∀ p ∈ OP, p.1 + e₁ ∈ D ∨ p.1 + e₂ ∈ D ∨ p.2 + e₁ ∈ D ∨ p.2 + e₂ ∈ D := by
    intro p hp
    by_contra hno
    push_neg at hno
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hno
    obtain ⟨ho1, ho12, hop1, hop2, hsum, hcap⟩ := hOP p hp
    refine hfree (hasPPS_of_combo ho1 ho12 he1 he12 hop1 hop2 hep1 hep2 ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hsum]; exact hs
    · rw [het]; exact ht
    · exact hodd _ (by omega) (by omega) (by omega) hn1
    · exact hodd _ (by omega) (by omega) (by omega) hn2
    · exact hodd _ (by omega) (by omega) (by omega) hn3
    · exact hodd _ (by omega) (by omega) (by omega) hn4
  -- Step 2: the kill map (value, position) is injective into D × {0,1,2,3}.
  set f : ℤ × ℤ → ℤ × ℕ := fun p =>
    if p.1 + e₁ ∈ D then (p.1 + e₁, 0)
    else if p.1 + e₂ ∈ D then (p.1 + e₂, 1)
    else if p.2 + e₁ ∈ D then (p.2 + e₁, 2)
    else (p.2 + e₂, 3) with hfdef
  have hmaps : ∀ p ∈ OP, f p ∈ D ×ˢ Finset.range 4 := by
    intro p hp
    simp only [hfdef, Finset.mem_product, Finset.mem_range]
    split_ifs with h1 h2 h3
    · exact ⟨h1, by norm_num⟩
    · exact ⟨h2, by norm_num⟩
    · exact ⟨h3, by norm_num⟩
    · rcases hkill p hp with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact ⟨h, by norm_num⟩
  have hinj : Set.InjOn f OP := by
    intro p hp q hq hfq
    have hps : p.1 + p.2 = s := (hOP p hp).2.2.2.2.1
    have hqs : q.1 + q.2 = s := (hOP q hq).2.2.2.2.1
    simp only [hfdef] at hfq
    split_ifs at hfq <;> injection hfq with hval hidx <;>
      first
        | omega
        | (exfalso; omega)
        | (have h1 : p.1 = q.1 := by omega
           have h2 : p.2 = q.2 := by omega
           exact Prod.ext h1 h2)
        | (have h2 : p.2 = q.2 := by omega
           have h1 : p.1 = q.1 := by omega
           exact Prod.ext h1 h2)
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  omega

/-- (K) dual — fixed o-pair version (the form X'a actually consumes;
Codex C3-P2 gate finding 1): for fixed even s, t ∈ A and a fixed admissible
o-pair of s, the admissible e-pairs of t number at most 4|D|.  Symmetric
kill map (e-pair) ↦ (m, position); e_j = m − o_i, companion via t. -/
theorem K_epairs_le (n : ℕ) (A D : Finset ℤ)
    (hfree : ¬ HasPosPairwiseSums A 4)
    (hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A)
    (s t o₁ o₂ : ℤ) (hs : s ∈ A) (ht : t ∈ A) (hos : o₁ + o₂ = s)
    (ho1 : 0 < o₁) (ho12 : o₁ < o₂) (hop1 : o₁ % 2 = 1) (hop2 : o₂ % 2 = 1)
    (EP : Finset (ℤ × ℤ))
    (hEP : ∀ p ∈ EP, 0 < p.1 ∧ p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0 ∧
      p.1 + p.2 = t ∧ o₂ + p.2 ≤ 2*(n:ℤ) - 1) :
    EP.card ≤ 4 * D.card := by
  classical
  have hkill : ∀ p ∈ EP, o₁ + p.1 ∈ D ∨ o₁ + p.2 ∈ D ∨ o₂ + p.1 ∈ D ∨ o₂ + p.2 ∈ D := by
    intro p hp
    by_contra hno
    push_neg at hno
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hno
    obtain ⟨he1, he12, hep1, hep2, hsum, hcap⟩ := hEP p hp
    refine hfree (hasPPS_of_combo ho1 ho12 he1 he12 hop1 hop2 hep1 hep2 ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hos]; exact hs
    · rw [hsum]; exact ht
    · exact hodd _ (by omega) (by omega) (by omega) hn1
    · exact hodd _ (by omega) (by omega) (by omega) hn2
    · exact hodd _ (by omega) (by omega) (by omega) hn3
    · exact hodd _ (by omega) (by omega) (by omega) hn4
  set f : ℤ × ℤ → ℤ × ℕ := fun p =>
    if o₁ + p.1 ∈ D then (o₁ + p.1, 0)
    else if o₁ + p.2 ∈ D then (o₁ + p.2, 1)
    else if o₂ + p.1 ∈ D then (o₂ + p.1, 2)
    else (o₂ + p.2, 3) with hfdef
  have hmaps : ∀ p ∈ EP, f p ∈ D ×ˢ Finset.range 4 := by
    intro p hp
    simp only [hfdef, Finset.mem_product, Finset.mem_range]
    split_ifs with h1 h2 h3
    · exact ⟨h1, by norm_num⟩
    · exact ⟨h2, by norm_num⟩
    · exact ⟨h3, by norm_num⟩
    · rcases hkill p hp with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact ⟨h, by norm_num⟩
  have hinj : Set.InjOn f EP := by
    intro p hp q hq hfq
    have hps : p.1 + p.2 = t := (hEP p hp).2.2.2.2.1
    have hqs : q.1 + q.2 = t := (hEP q hq).2.2.2.2.1
    simp only [hfdef] at hfq
    split_ifs at hfq <;> injection hfq with hval hidx <;>
      first
        | omega
        | (exfalso; omega)
        | (have h1 : p.1 = q.1 := by omega
           have h2 : p.2 = q.2 := by omega
           exact Prod.ext h1 h2)
        | (have h2 : p.2 = q.2 := by omega
           have h1 : p.1 = q.1 := by omega
           exact Prod.ext h1 h2)
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  omega

/-! ## Part 3b — the KC1 = 2 corrected chain (C4-P1, closes the sorry)

GTRANSFER §5 (C3-P3): in the (2+2) machine, one missing odd m kills at most
**2** e-pairs per fixed (s, t, o-pair) — m and the killing oᵢ determine the
e-pair as {m − oᵢ, t − (m − oᵢ)} — so the kill-map position index collapses
from {0..3} to {0,1}.  `K_epairs_le2` below is the corrected (K).

Consequence (this lens): the per-o-pair form of the corrected (K) replaces
BOTH X1 and the triangular-grid X2 of DICHOTOMY.md §1 (the roadmap's named
"hardest residual") by a single balanced-window lemma `balanced_kill`:
a fixed balanced o-pair of s plus the 2d+1 balanced e-pairs of t beat the
2d kill budget whenever t ≥ 8d+8 and s/2 + t/2 + 4d + 4 ≤ 2n − 1.  Chain:

* MID:   s = t ⇒ E ∩ [8d+8, 2n−4d−5] = ∅                      (balanced_kill)
* LOW×TOP: s ∈ [4, 8d+6], t ≥ 2n−4d−4 ⇒ impossible           (balanced_kill)
* TT:    three TOP elements give a positive triangle with z ≤ n+2d+1,
         fatal by (T★) with the 3d+1 anchor count               (T_star)
* TOP ≠ ∅ endgame: E ⊆ {2} ∪ TOP, |TOP| ≤ 2 ⇒ |E| ≤ 3 < d+4.  ∎
* TOP = ∅: Λ = E/2 ⊆ [1, 4d+3] triangle-free (T_star), so the largest
  element dominates fib(|Λ|+1) ≥ fib(d+5) > 4d+3: CAP kills ALL d ≥ 0 —
  the 92-structure enumeration is no longer needed (kept above as belt).  ∎

Validity collection: n ≥ 8d+8 suffices for every step (checked per-lemma);
coverage d ≤ (n−8)/8, dense branch `dense_case8` covers the rest from
n ≥ 331 777 = 24⁴ + 1. -/

/-- (K), CORRECTED (KC1 = 2, GTRANSFER §5): for a fixed o-pair the admissible
e-pairs of t number at most 2|D| in a config-free A.  Kill map
(e-pair) ↦ (m, which oᵢ): given m and oᵢ, the e-pair is
{m − oᵢ, t − (m − oᵢ)}, regardless of which slot m − oᵢ occupies. -/
theorem K_epairs_le2 (n : ℕ) (A D : Finset ℤ)
    (hfree : ¬ HasPosPairwiseSums A 4)
    (hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A)
    (s t o₁ o₂ : ℤ) (hs : s ∈ A) (ht : t ∈ A) (hos : o₁ + o₂ = s)
    (ho1 : 0 < o₁) (ho12 : o₁ < o₂) (hop1 : o₁ % 2 = 1) (hop2 : o₂ % 2 = 1)
    (EP : Finset (ℤ × ℤ))
    (hEP : ∀ p ∈ EP, 0 < p.1 ∧ p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0 ∧
      p.1 + p.2 = t ∧ o₂ + p.2 ≤ 2*(n:ℤ) - 1) :
    EP.card ≤ 2 * D.card := by
  classical
  have hkill : ∀ p ∈ EP, o₁ + p.1 ∈ D ∨ o₁ + p.2 ∈ D ∨ o₂ + p.1 ∈ D ∨ o₂ + p.2 ∈ D := by
    intro p hp
    by_contra hno
    push_neg at hno
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hno
    obtain ⟨he1, he12, hep1, hep2, hsum, hcap⟩ := hEP p hp
    refine hfree (hasPPS_of_combo ho1 ho12 he1 he12 hop1 hop2 hep1 hep2 ?_ ?_ ?_ ?_ ?_ ?_)
    · rw [hos]; exact hs
    · rw [hsum]; exact ht
    · exact hodd _ (by omega) (by omega) (by omega) hn1
    · exact hodd _ (by omega) (by omega) (by omega) hn2
    · exact hodd _ (by omega) (by omega) (by omega) hn3
    · exact hodd _ (by omega) (by omega) (by omega) hn4
  set f : ℤ × ℤ → ℤ × ℕ := fun p =>
    if o₁ + p.1 ∈ D then (o₁ + p.1, 0)
    else if o₁ + p.2 ∈ D then (o₁ + p.2, 0)
    else if o₂ + p.1 ∈ D then (o₂ + p.1, 1)
    else (o₂ + p.2, 1) with hfdef
  have hmaps : ∀ p ∈ EP, f p ∈ D ×ˢ Finset.range 2 := by
    intro p hp
    simp only [hfdef, Finset.mem_product, Finset.mem_range]
    split_ifs with h1 h2 h3
    · exact ⟨h1, by norm_num⟩
    · exact ⟨h2, by norm_num⟩
    · exact ⟨h3, by norm_num⟩
    · rcases hkill p hp with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact ⟨h, by norm_num⟩
  have hinj : Set.InjOn f EP := by
    intro p hp q hq hfq
    have hps : p.1 + p.2 = t := (hEP p hp).2.2.2.2.1
    have hqs : q.1 + q.2 = t := (hEP q hq).2.2.2.2.1
    have hpo : p.1 < p.2 := (hEP p hp).2.1
    have hqo : q.1 < q.2 := (hEP q hq).2.1
    simp only [hfdef] at hfq
    split_ifs at hfq <;> injection hfq with hval hidx <;>
      first
        | omega
        | (exfalso; omega)
        | (have h1 : p.1 = q.1 := by omega
           have h2 : p.2 = q.2 := by omega
           exact Prod.ext h1 h2)
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  omega

/-- Generic firing lemma: four pairwise-distinct positives with all six
pairwise sums in A give a positive 4-configuration.  (`hasPPS_of_combo`
derives distinctness from parity; the triangle machine needs this form.) -/
lemma hasPPS_of_quad {A : Finset ℤ} {w₁ w₂ w₃ w₄ : ℤ}
    (h1 : 0 < w₁) (h2 : 0 < w₂) (h3 : 0 < w₃) (h4 : 0 < w₄)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h14 : w₁ ≠ w₄)
    (h23 : w₂ ≠ w₃) (h24 : w₂ ≠ w₄) (h34 : w₃ ≠ w₄)
    (s12 : w₁ + w₂ ∈ A) (s13 : w₁ + w₃ ∈ A) (s14 : w₁ + w₄ ∈ A)
    (s23 : w₂ + w₃ ∈ A) (s24 : w₂ + w₄ ∈ A) (s34 : w₃ + w₄ ∈ A) :
    HasPosPairwiseSums A 4 := by
  refine ⟨fun i : Fin 4 =>
    if i = 0 then w₁ else if i = 1 then w₂ else if i = 2 then w₃ else w₄, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp at hij; omega)
  · intro i
    fin_cases i <;> simp <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp only []; norm_num; assumption)

/-- The triangle machine (T★, kill count 3): a positive triangle x < y < z
(same parity, pairwise sums in A) with z + 6d + 3 ≤ 2n is fatal in a
config-free A — the 3d+1 opposite-parity anchors w = 2j − (1 − x % 2),
j = 1..3d+1, each need a killer m ∈ D at one of 3 positions, and
(m, position) determines w. -/
theorem T_star (n : ℕ) (A D : Finset ℤ)
    (hfree : ¬ HasPosPairwiseSums A 4)
    (hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A)
    (x y z : ℤ) (h0x : 0 < x) (hxy : x < y) (hyz : y < z)
    (hpxy : x % 2 = y % 2) (hpyz : y % 2 = z % 2)
    (hxyA : x + y ∈ A) (hxzA : x + z ∈ A) (hyzA : y + z ∈ A)
    (hcap : z + 6*(D.card:ℤ) + 3 ≤ 2*(n:ℤ)) :
    False := by
  classical
  set dZ : ℤ := (D.card : ℤ) with hdZ
  have hd0 : (0:ℤ) ≤ dZ := by rw [hdZ]; exact_mod_cast Nat.zero_le D.card
  set WS : Finset ℤ := (Finset.Icc (1:ℤ) (3*dZ+1)).image (fun j => 2*j - (1 - x % 2))
    with hWS
  have hWcard : WS.card = 3 * D.card + 1 := by
    rw [hWS, Finset.card_image_of_injOn (fun a _ b _ h => by omega), Int.card_Icc]
    omega
  have hkill : ∀ w ∈ WS, x + w ∈ D ∨ y + w ∈ D ∨ z + w ∈ D := by
    intro w hw
    rw [hWS, Finset.mem_image] at hw
    obtain ⟨j, hj, hwj⟩ := hw
    rw [Finset.mem_Icc] at hj
    by_contra hno
    push_neg at hno
    obtain ⟨k1, k2, k3⟩ := hno
    have hw1 : 1 ≤ w := by omega
    have hwub : w ≤ 2*(n:ℤ) - 1 - z := by omega
    have hwpar : w % 2 = 1 - x % 2 := by omega
    refine hfree (hasPPS_of_quad (w₁ := x) (w₂ := y) (w₃ := z) (w₄ := w)
      h0x (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hxyA hxzA ?_ hyzA ?_ ?_)
    · exact hodd _ (by omega) (by omega) (by omega) k1
    · exact hodd _ (by omega) (by omega) (by omega) k2
    · exact hodd _ (by omega) (by omega) (by omega) k3
  set f : ℤ → ℤ × ℕ := fun w =>
    if x + w ∈ D then (x + w, 0)
    else if y + w ∈ D then (y + w, 1)
    else (z + w, 2) with hfdef
  have hmaps : ∀ w ∈ WS, f w ∈ D ×ˢ Finset.range 3 := by
    intro w hw
    simp only [hfdef, Finset.mem_product, Finset.mem_range]
    split_ifs with hh1 hh2
    · exact ⟨hh1, by norm_num⟩
    · exact ⟨hh2, by norm_num⟩
    · rcases hkill w hw with h | h | h
      · exact absurd h hh1
      · exact absurd h hh2
      · exact ⟨h, by norm_num⟩
  have hinj : Set.InjOn f WS := by
    intro p hp q hq hfq
    simp only [hfdef] at hfq
    split_ifs at hfq <;> injection hfq with hval hidx <;> omega
  have hcard := Finset.card_le_card_of_injOn (s := WS) (t := D ×ˢ Finset.range 3)
    f hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  omega

/-- Triangle-free positive sets grow at Fibonacci speed: the two largest
elements of a p-element set dominate fib (p+1) and fib p
(F₁, F₂, F₃, … = 1, 2, 3, 5, … is fib shifted by one). -/
lemma triangle_free_fib : ∀ (p : ℕ), 2 ≤ p → ∀ (Λ : Finset ℤ), Λ.card = p →
    (∀ a ∈ Λ, 1 ≤ a) →
    (∀ a ∈ Λ, ∀ b ∈ Λ, ∀ c ∈ Λ, a < b → b < c → a + b ≤ c) →
    ∃ M ∈ Λ, ∃ M' ∈ Λ, M' < M ∧ (Nat.fib (p+1) : ℤ) ≤ M ∧ (Nat.fib p : ℤ) ≤ M' := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base =>
      intro Λ hcard hpos _
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
      have ha := hpos a (by simp)
      have hb := hpos b (by simp)
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨b, by simp, a, by simp, h, by simp [Nat.fib]; omega, by simp [Nat.fib]; omega⟩
      · exact ⟨a, by simp, b, by simp, h, by simp [Nat.fib]; omega, by simp [Nat.fib]; omega⟩
  | succ p hp ih =>
      intro Λ hcard hpos htf
      have hne : Λ.Nonempty := Finset.card_pos.mp (by omega)
      set M : ℤ := Λ.max' hne with hM
      have hMmem : M ∈ Λ := Λ.max'_mem hne
      set Λ' : Finset ℤ := Λ.erase M with hΛ'
      have hΛ'card : Λ'.card = p := by
        rw [hΛ', Finset.card_erase_of_mem hMmem, hcard]
        omega
      have hΛ'sub : Λ' ⊆ Λ := Finset.erase_subset _ _
      obtain ⟨M₁, hM₁, M₂, hM₂, h21, hf1, hf2⟩ := ih Λ' hΛ'card
        (fun a ha => hpos a (hΛ'sub ha))
        (fun a ha b hb c hc => htf a (hΛ'sub ha) b (hΛ'sub hb) c (hΛ'sub hc))
      have hM₁M : M₁ < M := by
        have hle := Λ.le_max' M₁ (hΛ'sub hM₁)
        have hne' := Finset.ne_of_mem_erase hM₁
        omega
      have hsum : M₂ + M₁ ≤ M := htf M₂ (hΛ'sub hM₂) M₁ (hΛ'sub hM₁) M hMmem h21 hM₁M
      refine ⟨M, hMmem, M₁, hΛ'sub hM₁, hM₁M, ?_, hf1⟩
      have hadd : Nat.fib (p+1+1) = Nat.fib p + Nat.fib (p+1) := Nat.fib_add_two
      have hcast : (Nat.fib (p+1+1) : ℤ) = (Nat.fib p : ℤ) + (Nat.fib (p+1) : ℤ) := by
        exact_mod_cast hadd
      omega

/-- CAP arithmetic: fib (d+5) > 4d + 3 for every d ≥ 0, so a triangle-free
Λ ⊆ [1, 4d+3] can never have d + 4 elements — the corrected chain needs NO
endgame enumeration at any d. -/
lemma cap_fib : ∀ d : ℕ, 4*d + 3 < Nat.fib (d+5) := by
  intro d
  induction d with
  | zero => decide
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · decide
      · have h5 : 5 ≤ Nat.fib (k+4) := by
          calc 5 = Nat.fib 5 := by decide
          _ ≤ Nat.fib (k+4) := Nat.fib_mono (by omega)
        have hadd : Nat.fib (k+1+5) = Nat.fib (k+4) + Nat.fib (k+5) := by
          have h := Nat.fib_add_two (n := k+4)
          rw [show k+4+2 = k+1+5 from by omega, show k+4+1 = k+5 from by omega] at h
          exact h
        omega

/-- The balanced-window kill (replaces X1 AND the triangular-grid X2 of
DICHOTOMY.md §1 under KC1 = 2): s, t ∈ A even with s ≥ 4, t ≥ 8d+8 and
s/2 + t/2 + 4d + 4 ≤ 2n − 1 is impossible in a config-free A.  The fixed
balanced o-pair of s (o₂ ≤ s/2 + 2) admits the 2d+1 balanced e-pairs of t
(e₂ even in (t/2, t/2 + 4d+2]), beating the 2d kill budget of
`K_epairs_le2`.  Instantiations: s = t (middle exclusion) and
s ∈ LOW, t ∈ TOP. -/
lemma balanced_kill (n : ℕ) (A D : Finset ℤ)
    (hfree : ¬ HasPosPairwiseSums A 4)
    (hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A)
    (s t : ℤ) (hs : s ∈ A) (ht : t ∈ A)
    (hse : s % 2 = 0) (hte : t % 2 = 0)
    (hs4 : 4 ≤ s)
    (htlb : 8*(D.card:ℤ) + 8 ≤ t)
    (hcap : s/2 + t/2 + 4*(D.card:ℤ) + 4 ≤ 2*(n:ℤ) - 1) :
    False := by
  classical
  set dZ : ℤ := (D.card : ℤ) with hdZ
  have hd0 : (0:ℤ) ≤ dZ := by rw [hdZ]; exact_mod_cast Nat.zero_le D.card
  set τs : ℤ := s / 2 with hτs
  set τt : ℤ := t / 2 with hτt
  have hτs2 : 2 * τs = s := by omega
  have hτt2 : 2 * τt = t := by omega
  set μ : ℤ := τt / 2 with hμ
  have hμlb : 2*μ ≤ τt := by omega
  have hμub : τt ≤ 2*μ + 1 := by omega
  set o₂ : ℤ := τs + 1 + τs % 2 with ho2def
  set o₁ : ℤ := s - o₂ with ho1def
  set EP : Finset (ℤ × ℤ) := (Finset.Icc (1:ℤ) (2*dZ+1)).image
    (fun j => (t - 2*(μ + j), 2*(μ + j))) with hEPdef
  have hEPcard : EP.card = 2 * D.card + 1 := by
    rw [hEPdef, Finset.card_image_of_injOn (fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h; omega), Int.card_Icc]
    omega
  have hEPmem : ∀ p ∈ EP, 0 < p.1 ∧ p.1 < p.2 ∧ p.1 % 2 = 0 ∧ p.2 % 2 = 0 ∧
      p.1 + p.2 = t ∧ o₂ + p.2 ≤ 2*(n:ℤ) - 1 := by
    intro p hp
    rw [hEPdef, Finset.mem_image] at hp
    obtain ⟨j, hj, rfl⟩ := hp
    rw [Finset.mem_Icc] at hj
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hK := K_epairs_le2 n A D hfree hodd s t o₁ o₂ hs ht (by omega)
    (by omega) (by omega) (by omega) (by omega) EP hEPmem
  omega

/-- TOP-triple contradiction (TT): three evens of A in [2n−4d−4, 2n] form a
positive triangle with z ≤ n + 2d + 1, fatal by `T_star` once n ≥ 8d + 4. -/
lemma tt_aux (n : ℕ) (A D : Finset ℤ)
    (hfree : ¬ HasPosPairwiseSums A 4)
    (hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A)
    (hnd : 8*(D.card:ℤ) + 8 ≤ (n:ℤ))
    (a b c : ℤ) (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
    (hae : a % 2 = 0) (hbe : b % 2 = 0) (hce : c % 2 = 0)
    (hab : a < b) (hbc : b < c)
    (halb : 2*(n:ℤ) - 4*(D.card:ℤ) - 4 ≤ a) (hcub : c ≤ 2*(n:ℤ)) :
    False := by
  set dZ : ℤ := (D.card : ℤ) with hdZ
  have hd0 : (0:ℤ) ≤ dZ := by rw [hdZ]; exact_mod_cast Nat.zero_le D.card
  obtain ⟨x, hx⟩ : ∃ x, a + b - c = 2*x := ⟨(a+b-c)/2, by omega⟩
  obtain ⟨y, hy⟩ : ∃ y, a + c - b = 2*y := ⟨(a+c-b)/2, by omega⟩
  obtain ⟨z, hz⟩ : ∃ z, b + c - a = 2*z := ⟨(b+c-a)/2, by omega⟩
  refine T_star n A D hfree hodd x y z (by omega) (by omega) (by omega)
    (by omega) (by omega) ?_ ?_ ?_ (by omega)
  · have h : x + y = a := by omega
    rwa [h]
  · have h : x + z = b := by omega
    rwa [h]
  · have h : y + z = c := by omega
    rwa [h]

/-- STRUCTURAL CASE on the KC1 = 2 corrected chain — formerly the single
load-bearing sorry of this port.  Regime n ≥ 8d + 8, all d covered without
any endgame enumeration (CAP kills every d ≥ 0). -/
theorem structural_case (n : ℕ) (hn : 331777 ≤ n) (A : Finset ℤ)
    (hA : A ⊆ Finset.Icc (1:ℤ) (2*(n:ℤ))) (hcard : A.card = n + 4)
    (hd : 8 * (missingOdds n A).card + 8 ≤ n) :
    HasPosPairwiseSums A 4 := by
  classical
  by_contra hfree
  set D : Finset ℤ := missingOdds n A with hD
  set dZ : ℤ := (D.card : ℤ) with hdZ
  have hd0 : (0:ℤ) ≤ dZ := by rw [hdZ]; exact_mod_cast Nat.zero_le D.card
  have hnd : 8 * dZ + 8 ≤ (n:ℤ) := by rw [hdZ]; exact_mod_cast hd
  have hodd : ∀ x : ℤ, 1 ≤ x → x ≤ 2*(n:ℤ) → x % 2 = 1 → x ∉ D → x ∈ A := by
    intro x h1 h2 h3 h4
    by_contra hxA
    exact h4 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, h3, hxA⟩)
  set E : Finset ℤ := A.filter (fun x => x % 2 = 0) with hE
  have hEcard : D.card + 4 ≤ E.card := evens_card_lower n A hA (le_of_eq hcard.symm)
  have hEfacts : ∀ s ∈ E, s ∈ A ∧ s % 2 = 0 ∧ 2 ≤ s ∧ s ≤ 2*(n:ℤ) := by
    intro s hsE
    obtain ⟨hsA, hse⟩ := Finset.mem_filter.mp hsE
    have hbounds := Finset.mem_Icc.mp (hA hsA)
    exact ⟨hsA, hse, by omega, by omega⟩
  -- MID: no even of A in [8d+8, 2n−4d−5]
  have hmid : ∀ s ∈ E, ¬(8*dZ + 8 ≤ s ∧ s ≤ 2*(n:ℤ) - 4*dZ - 5) := by
    rintro s hsE ⟨hlb, hub⟩
    obtain ⟨hsA, hse, -, -⟩ := hEfacts s hsE
    exact balanced_kill n A D hfree hodd s s hsA hsA hse hse
      (by omega) (by omega) (by omega)
  by_cases htop : ∃ t ∈ E, 2*(n:ℤ) - 4*dZ - 4 ≤ t
  · -- TOP ≠ ∅
    obtain ⟨t, htE, htlb⟩ := htop
    obtain ⟨htA, hte, -, htub⟩ := hEfacts t htE
    -- LOW ⊆ {2}
    have hlow : ∀ s ∈ E, s ≤ 8*dZ + 6 → s = 2 := by
      intro s hsE hsub
      by_contra hs2
      obtain ⟨hsA, hse, hs2', -⟩ := hEfacts s hsE
      exact balanced_kill n A D hfree hodd s t hsA htA hse hte
        (by omega) (by omega) (by omega)
    set TOP : Finset ℤ := E.filter (fun x => 2*(n:ℤ) - 4*dZ - 4 ≤ x) with hTOPdef
    have hTOPcard : TOP.card ≤ 2 := by
      by_contra hgt
      push_neg at hgt
      obtain ⟨S, hSsub, hS3⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ TOP.card)
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS3
      have hfacts : ∀ u ∈ ({a, b, c} : Finset ℤ),
          u ∈ A ∧ u % 2 = 0 ∧ 2*(n:ℤ) - 4*dZ - 4 ≤ u ∧ u ≤ 2*(n:ℤ) := by
        intro u hu
        obtain ⟨huE, hulb⟩ := Finset.mem_filter.mp (hSsub hu)
        obtain ⟨huA, hue, -, huub⟩ := hEfacts u huE
        exact ⟨huA, hue, hulb, huub⟩
      obtain ⟨haA, hae, halb, haub⟩ := hfacts a (by simp)
      obtain ⟨hbA, hbe, hblb, hbub⟩ := hfacts b (by simp)
      obtain ⟨hcA, hce, hclb, hcub⟩ := hfacts c (by simp)
      rcases lt_trichotomy a b with h1 | h1 | h1
      · rcases lt_trichotomy b c with h2 | h2 | h2
        · exact tt_aux n A D hfree hodd hnd a b c haA hbA hcA hae hbe hce h1 h2 halb hcub
        · exact hbc h2
        · rcases lt_trichotomy a c with h3 | h3 | h3
          · exact tt_aux n A D hfree hodd hnd a c b haA hcA hbA hae hce hbe h3 h2 halb hbub
          · exact hac h3
          · exact tt_aux n A D hfree hodd hnd c a b hcA haA hbA hce hae hbe h3 h1 hclb hbub
      · exact hab h1
      · rcases lt_trichotomy a c with h2 | h2 | h2
        · exact tt_aux n A D hfree hodd hnd b a c hbA haA hcA hbe hae hce h1 h2 hblb hcub
        · exact hac h2
        · rcases lt_trichotomy b c with h3 | h3 | h3
          · exact tt_aux n A D hfree hodd hnd b c a hbA hcA haA hbe hce hae h3 h2 hblb haub
          · exact hbc h3
          · exact tt_aux n A D hfree hodd hnd c b a hcA hbA haA hce hbe hae h3 h1 hclb haub
    have hsub2 : E ⊆ insert 2 TOP := by
      intro s hsE
      obtain ⟨hsA, hse, hs2, hsub⟩ := hEfacts s hsE
      rcases le_or_gt s (8*dZ + 6) with hsmall | hbig
      · rw [hlow s hsE hsmall]
        exact Finset.mem_insert_self _ _
      · rcases le_or_gt s (2*(n:ℤ) - 4*dZ - 5) with hmidr | htopr
        · exact absurd ⟨by omega, hmidr⟩ (hmid s hsE)
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hsE, by omega⟩)
    have hle3 : E.card ≤ 3 := by
      calc E.card ≤ (insert 2 TOP).card := Finset.card_le_card hsub2
        _ ≤ TOP.card + 1 := Finset.card_insert_le _ _
        _ ≤ 3 := by omega
    omega
  · -- TOP = ∅
    push_neg at htop
    have hEsmall : ∀ s ∈ E, s ≤ 8*dZ + 6 := by
      intro s hsE
      by_contra hbig
      push_neg at hbig
      have hub := htop s hsE
      obtain ⟨-, hse, -, -⟩ := hEfacts s hsE
      exact hmid s hsE ⟨by omega, by omega⟩
    set Λ : Finset ℤ := E.image (fun s => s / 2) with hΛdef
    have hΛcard : Λ.card = E.card := Finset.card_image_of_injOn (by
      intro u hu v hv huv
      have hue : u % 2 = 0 := (Finset.mem_filter.mp hu).2
      have hve : v % 2 = 0 := (Finset.mem_filter.mp hv).2
      have huv' : u / 2 = v / 2 := huv
      omega)
    have hΛmem : ∀ g ∈ Λ, 2*g ∈ A ∧ 1 ≤ g ∧ g ≤ 4*dZ + 3 := by
      intro g hg
      rw [hΛdef, Finset.mem_image] at hg
      obtain ⟨s, hsE, rfl⟩ := hg
      obtain ⟨hsA, hse, hs2, -⟩ := hEfacts s hsE
      have hsmall := hEsmall s hsE
      have h2g : 2 * (s/2) = s := by omega
      exact ⟨by rwa [h2g], by omega, by omega⟩
    have hΛtf : ∀ g₁ ∈ Λ, ∀ g₂ ∈ Λ, ∀ g₃ ∈ Λ, g₁ < g₂ → g₂ < g₃ → g₁ + g₂ ≤ g₃ := by
      intro g1 hg1 g2 hg2 g3 hg3 h12 h23
      by_contra hgt
      push_neg at hgt
      obtain ⟨hA1, hp1, hu1⟩ := hΛmem g1 hg1
      obtain ⟨hA2, hp2, hu2⟩ := hΛmem g2 hg2
      obtain ⟨hA3, hp3, hu3⟩ := hΛmem g3 hg3
      refine T_star n A D hfree hodd (g1+g2-g3) (g1+g3-g2) (g2+g3-g1)
        (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_ (by omega)
      · have h : (g1+g2-g3) + (g1+g3-g2) = 2*g1 := by ring
        rw [h]; exact hA1
      · have h : (g1+g2-g3) + (g2+g3-g1) = 2*g2 := by ring
        rw [h]; exact hA2
      · have h : (g1+g3-g2) + (g2+g3-g1) = 2*g3 := by ring
        rw [h]; exact hA3
    have hp2 : 2 ≤ Λ.card := by omega
    obtain ⟨M, hM, M', hM', hMM', hfib1, hfib2⟩ :=
      triangle_free_fib Λ.card hp2 Λ rfl (fun a ha => (hΛmem a ha).2.1) hΛtf
    have hcapM : M ≤ 4*dZ + 3 := (hΛmem M hM).2.2
    have hfibmono : (Nat.fib (D.card + 5) : ℤ) ≤ (Nat.fib (Λ.card + 1) : ℤ) := by
      exact_mod_cast Nat.fib_mono (by omega)
    have hcapfib : (4*(D.card:ℤ) + 3 : ℤ) < (Nat.fib (D.card + 5) : ℤ) := by
      exact_mod_cast cap_fib D.card
    omega

end Dicho

/-! ## Part 4 — assembly (sorry-free, KC1 = 2 corrected chain) -/

/-- h₄(n) ≤ 4 for n ≥ 331 777.  Normalizes to |A'| = n + 4 exactly before
branching (config-freeness is inherited by subsets; DICHOTOMY.md §0,
Codex C3-P2 gate finding 2), then splits at d ≤ (n−8)/8: structural chain
(`structural_case`, corrected constants) vs dense regime (`dense_case8`). -/
theorem h4_le_4 (n : ℕ) (hn : 331777 ≤ n) : hFun 4 n ≤ 4 := by
  unfold hFun
  apply Nat.sInf_le
  intro A hA hcard
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hcard
  have h4' : HasPosPairwiseSums A' 4 := by
    by_cases hd : 8 * (Dicho.missingOdds n A').card + 8 ≤ n
    · exact Dicho.structural_case n hn A' (hA'sub.trans hA) hA'card hd
    · exact Dicho.dense_case8 n hn A' (hA'sub.trans hA) hA'card.ge (by omega)
  obtain ⟨b, hinj, hpos, hsums⟩ := h4'
  exact ⟨b, hinj, hpos, fun i j hij => hA'sub (hsums i j hij)⟩

/-- THE TARGET: **h₄(n) = 4 for all n ≥ 331 777** (lower half: C2-P2's
`four_le_hFun_four`).  The kernel constant 331 777 = 24⁴ + 1 sits BELOW the
paper-grade N₀ = 4 593 324 of GTRANSFER §5: the per-o-pair corrected (K)
needs only n ≥ 8d + 8 in the structural regime (slope 1/8, not 1/16). -/
theorem h4_eq_4 (n : ℕ) (hn : 331777 ≤ n) : hFun 4 n = 4 :=
  le_antisymm (h4_le_4 n hn) (Erdos866.four_le_hFun_four n (by omega))

/-- The C3-P3 charter constant (GTRANSFER §5), now a corollary. -/
theorem h4_eq_4_charter (n : ℕ) (hn : 4593324 ≤ n) : hFun 4 n = 4 :=
  h4_eq_4 n (by omega)

/-- The C2-P4 constant (DICHOTOMY.md), now a corollary. -/
theorem h4_eq_4_c2 (n : ℕ) (hn : 8 * 10 ^ 7 ≤ n) : hFun 4 n = 4 :=
  h4_eq_4 n (by omega)

end Erdos866

-- Axiom audit (in-file, P3 style).  Expected after C4-P1: EVERYTHING on
-- [propext, Classical.choice, Quot.sound] (or fewer), zero sorryAx.
#print axioms Erdos866.Dicho.fFunPos_four_lt_crossover
#print axioms Erdos866.Dicho.hasPosPairwiseSums_of_dense
#print axioms Erdos866.Dicho.evens_card_lower
#print axioms Erdos866.Dicho.dense_case
#print axioms Erdos866.Dicho.fFunPos_four_lt_crossover8
#print axioms Erdos866.Dicho.hasPosPairwiseSums_of_dense8
#print axioms Erdos866.Dicho.dense_case8
#print axioms Erdos866.Dicho.pigeonhole_disjoint_hits
#print axioms Erdos866.Dicho.hasPPS_of_combo
#print axioms Erdos866.Dicho.endgame_no_survivor
#print axioms Erdos866.Dicho.dichoCerts_ok
#print axioms Erdos866.Dicho.K_opairs_le
#print axioms Erdos866.Dicho.K_epairs_le
#print axioms Erdos866.Dicho.K_epairs_le2
#print axioms Erdos866.Dicho.hasPPS_of_quad
#print axioms Erdos866.Dicho.T_star
#print axioms Erdos866.Dicho.triangle_free_fib
#print axioms Erdos866.Dicho.cap_fib
#print axioms Erdos866.Dicho.balanced_kill
#print axioms Erdos866.Dicho.tt_aux
#print axioms Erdos866.Dicho.structural_case
#print axioms Erdos866.h4_le_4
#print axioms Erdos866.h4_eq_4
#print axioms Erdos866.h4_eq_4_charter
#print axioms Erdos866.h4_eq_4_c2
