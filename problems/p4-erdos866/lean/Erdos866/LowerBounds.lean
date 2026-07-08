/-
Erdős #866 — Campaign-2 P2: Lean ports of the two C1 lower-bound theorems
(NEW, not in the upstream development; upstream untouched).

1. `Erdos866.four_le_hFun_four` : 4 ≤ hFun 4 n for all n ≥ 3.
   Witness A_n = {odds in [1,2n]} ∪ {2, 2n−2, 2n}, |A_n| = n+3, h₄-config-free
   by a 2-step parity argument (C1 lower-bounds lens, theorem-h4-lower.md;
   co-discovered by the extremal-structure lens, PROOFS.md Thm 1).
   Improves the standing formal lower bound 3 ≤ hFun 4 n (only via gFun 4 n = 3)
   and gives the strict separation gFun 4 n < hFun 4 n (n ≥ 3).

2. `Erdos866.fibCnt_lt_hFun_five` : fibCnt n < hFun 5 n for all n, where
   fibCnt n = #{m ∈ [1,n] : m is a Fibonacci number} (values {1,2,3,5,8,…}).
   Witness B_n = {odds in [1,2n]} ∪ {2f : f Fibonacci, f ≤ n}, |B_n| = n + fibCnt n,
   h₅-config-free by parity + the Fibonacci addition identity
   F_{m−2} + F_{m−1} = F_m (C1 extremal-structure lens, PROOFS.md Thm 2).
   Beats the upstream-formalized bound `h5lower` (Nat.log 2 n < hFun 5 n)
   pointwise for n ≥ 2 and by the asymptotic factor 1/log₂ φ = 1.4404….

Definitions gFun/hFun/HasPosPairwiseSums are the UPSTREAM ones
(Erdos866/Upstream.lean, byte-identical vendored copy of
Woett/Lean-files/ErdosProblem866.lean) — nothing is restated.
-/
import Erdos866.Upstream

open Finset
open scoped Classical

namespace Erdos866

/-! ## Common ingredient: the odd numbers in [1, 2n], as a Finset ℤ of card n -/

/-- The n odd numbers in {1,…,2n}. -/
def oddPart (n : ℕ) : Finset ℤ :=
  (Icc (1 : ℤ) (2 * (n : ℤ))).filter (fun x => x % 2 = 1)

lemma oddPart_card (n : ℕ) : (oddPart n).card = n := by
  have himg : oddPart n = (Finset.range n).image (fun a : ℕ => (2 * (a : ℤ) + 1)) := by
    ext x
    simp only [oddPart, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(x / 2).toNat, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  have hinj : Function.Injective (fun a : ℕ => (2 * (a : ℤ) + 1)) := by
    intro a b hab
    dsimp only at hab
    omega
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-! ## Theorem 1: 4 ≤ h₄(n) for n ≥ 3

Witness family A_n := odds ∪ {2, 2n−2, 2n} (the vD26 g₄ lower-bound set with
the "free element" 2 adjoined: 2 is not a sum of two distinct positive
integers, so adjoining it preserves h-configuration-freeness). -/

/-- The h₄ lower-bound witness A_n = {odds in [1,2n]} ∪ {2, 2n−2, 2n}. -/
def H4Witness (n : ℕ) : Finset ℤ :=
  (Icc (1 : ℤ) (2 * (n : ℤ))).filter
    (fun x => x % 2 = 1 ∨ x = 2 ∨ x = 2 * (n : ℤ) - 2 ∨ x = 2 * (n : ℤ))

lemma H4Witness_subset (n : ℕ) : H4Witness n ⊆ Icc (1 : ℤ) (2 * (n : ℤ)) :=
  Finset.filter_subset _ _

lemma H4Witness_card (n : ℕ) (hn : 3 ≤ n) : (H4Witness n).card = n + 3 := by
  have hset : H4Witness n
      = (Finset.range n).image (fun a : ℕ => (2 * (a : ℤ) + 1))
        ∪ {(2 : ℤ), 2 * (n : ℤ) - 2, 2 * (n : ℤ)} := by
    ext x
    simp only [H4Witness, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3 | h3 | h3 | h3⟩
      · exact Or.inl ⟨(x / 2).toNat, by omega, by omega⟩
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr h3))
    · rintro (⟨a, ha, rfl⟩ | rfl | rfl | rfl)
      · exact ⟨⟨by omega, by omega⟩, Or.inl (by omega)⟩
      · exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inl rfl)⟩
      · exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨⟨by omega, by omega⟩, Or.inr (Or.inr (Or.inr rfl))⟩
  have hinj : Function.Injective (fun a : ℕ => (2 * (a : ℤ) + 1)) := by
    intro a b hab
    dsimp only at hab
    omega
  have hdisj : Disjoint ((Finset.range n).image (fun a : ℕ => (2 * (a : ℤ) + 1)))
      ({(2 : ℤ), 2 * (n : ℤ) - 2, 2 * (n : ℤ)} : Finset ℤ) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image, Finset.mem_range] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    obtain ⟨a, _, rfl⟩ := hx
    rcases hx' with h | h | h <;> omega
  have htriple : ({(2 : ℤ), 2 * (n : ℤ) - 2, 2 * (n : ℤ)} : Finset ℤ).card = 3 :=
    Finset.card_eq_three.mpr
      ⟨2, 2 * (n : ℤ) - 2, 2 * (n : ℤ), by omega, by omega, by omega, rfl⟩
  rw [hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj, Finset.card_range, htriple]

/-- A_n admits no 4 distinct positive integers with all six pairwise sums in it.
Two-step parity argument: (1) three same-parity bᵢ would give three distinct
even sums ≥ 3, but only two even values ≥ 3 exist in A_n; (2) in the 2+2 parity
split both same-parity sums are ≥ 2n−2, forcing the larger even and larger odd
bᵢ to be ≥ n each, so their (odd) cross sum is ≥ 2n+1 > 2n — outside A_n. -/
lemma H4Witness_no_pps (n : ℕ) (hn : 3 ≤ n) : ¬ HasPosPairwiseSums (H4Witness n) 4 := by
  rintro ⟨b, hinj, hpos, hsum⟩
  have m01 := hsum 0 1 (by decide)
  have m02 := hsum 0 2 (by decide)
  have m03 := hsum 0 3 (by decide)
  have m12 := hsum 1 2 (by decide)
  have m13 := hsum 1 3 (by decide)
  have m23 := hsum 2 3 (by decide)
  simp only [H4Witness, Finset.mem_filter, Finset.mem_Icc] at m01 m02 m03 m12 m13 m23
  have ne01 : b 0 ≠ b 1 := fun h => absurd (hinj h) (by decide)
  have ne02 : b 0 ≠ b 2 := fun h => absurd (hinj h) (by decide)
  have ne03 : b 0 ≠ b 3 := fun h => absurd (hinj h) (by decide)
  have ne12 : b 1 ≠ b 2 := fun h => absurd (hinj h) (by decide)
  have ne13 : b 1 ≠ b 3 := fun h => absurd (hinj h) (by decide)
  have ne23 : b 2 ≠ b 3 := fun h => absurd (hinj h) (by decide)
  have p0 := hpos 0
  have p1 := hpos 1
  have p2 := hpos 2
  have p3 := hpos 3
  omega

/-- **h₄(n) ≥ 4 for all n ≥ 3** (C1 lower-bounds + extremal-structure lenses).
Previously the formal record had only 3 ≤ hFun 4 n via gFun 4 n = 3. -/
theorem four_le_hFun_four (n : ℕ) (hn : 3 ≤ n) : 4 ≤ hFun 4 n := by
  unfold hFun
  apply le_csInf
  · refine ⟨2 * n + 1, fun A hA hcard => absurd hcard (not_le.mpr ?_)⟩
    have h1 := Finset.card_le_card hA
    have h2 : (Finset.Icc (1 : ℤ) (2 * (n : ℤ))).card = 2 * n := by
      rw [Int.card_Icc]; omega
    omega
  · intro m hm
    by_contra hcon
    push_neg at hcon
    refine H4Witness_no_pps n hn (hm (H4Witness n) (H4Witness_subset n) ?_)
    rw [H4Witness_card n hn]
    omega

/-- Strict g/h separation at k = 4: gFun 4 n = 3 < 4 ≤ hFun 4 n for n ≥ 3.
(Whether h₄ > g₄ was open; this is the first constant-row separation beyond
the known h₃ = 2 > g₃ = 1.) -/
theorem gFun_four_lt_hFun_four (n : ℕ) (hn : 3 ≤ n) : gFun 4 n < hFun 4 n := by
  have h4 := four_le_hFun_four n hn
  have hg := g4 n (by omega)
  omega

/-! ## Theorem 2: fibCnt n < h₅(n)

Witness family B_n := odds ∪ {2f : f Fibonacci ≤ n}. Three same-parity bᵢ
(pigeonhole among five) have pairwise sums 2g₁, 2g₂, 2g₃ with g₁ < g₂ < g₃
Fibonacci; then the smallest of the three bᵢ equals g₁ + g₂ − g₃ ≤ 0 by the
Fibonacci addition identity — contradicting positivity. -/

/-- m is a Fibonacci number (mathlib's `Nat.fib`; values 0, 1, 1, 2, 3, 5, 8, …). -/
def IsFib (m : ℕ) : Prop := ∃ j, Nat.fib j = m

/-- fibCnt n = #{m ∈ [1,n] : m is a Fibonacci number}: the number of distinct
Fibonacci VALUES {1, 2, 3, 5, 8, 13, 21, …} not exceeding n.
E.g. fibCnt 1 = 1, fibCnt 21 = 7. -/
noncomputable def fibCnt (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter IsFib).card

/-- The doubled-Fibonacci even part {2f : f ∈ [1,n], f Fibonacci} ⊆ ℤ. -/
noncomputable def fibPart (n : ℕ) : Finset ℤ :=
  ((Finset.Icc 1 n).filter IsFib).image (fun g : ℕ => (2 * (g : ℤ)))

/-- The h₅ lower-bound witness B_n = {odds in [1,2n]} ∪ {2f : f Fibonacci ≤ n}. -/
noncomputable def H5Witness (n : ℕ) : Finset ℤ := oddPart n ∪ fibPart n

lemma H5Witness_subset (n : ℕ) : H5Witness n ⊆ Icc (1 : ℤ) (2 * (n : ℤ)) := by
  refine Finset.union_subset (Finset.filter_subset _ _) ?_
  intro x hx
  simp only [fibPart, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨g, ⟨⟨hg1, hg2⟩, _⟩, rfl⟩ := hx
  simp only [Finset.mem_Icc]
  omega

lemma H5Witness_card (n : ℕ) : (H5Witness n).card = n + fibCnt n := by
  have hinj : Function.Injective (fun g : ℕ => (2 * (g : ℤ))) := by
    intro a b hab
    dsimp only at hab
    omega
  have hdisj : Disjoint (oddPart n) (fibPart n) := by
    rw [Finset.disjoint_right]
    intro x hx hx'
    simp only [fibPart, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hx
    simp only [oddPart, Finset.mem_filter, Finset.mem_Icc] at hx'
    obtain ⟨g, _, rfl⟩ := hx
    omega
  rw [H5Witness, Finset.card_union_of_disjoint hdisj, oddPart_card, fibPart,
    Finset.card_image_of_injective _ hinj, fibCnt]

/-- Even members of B_n are doubled Fibonacci numbers in [2, 2n]. -/
lemma even_mem_H5Witness {n : ℕ} {x : ℤ} (hx : x ∈ H5Witness n) (hpar : x % 2 = 0) :
    ∃ g : ℕ, IsFib g ∧ 1 ≤ g ∧ g ≤ n ∧ x = 2 * (g : ℤ) := by
  rcases Finset.mem_union.mp hx with h | h
  · exfalso
    simp only [oddPart, Finset.mem_filter, Finset.mem_Icc] at h
    omega
  · simp only [fibPart, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at h
    obtain ⟨g, ⟨⟨hg1, hg2⟩, hfib⟩, rfl⟩ := h
    exact ⟨g, hfib, hg1, hg2, rfl⟩

/-- The Fibonacci addition identity, packaged for triples of distinct Fibonacci
values: if u < v < w are all Fibonacci then u + v ≤ w
(u ≤ F_{m−2}, v ≤ F_{m−1}, w = F_m and F_{m−2} + F_{m−1} = F_m). -/
lemma fib_triple_bound {u v w : ℕ} (hu : IsFib u) (hv : IsFib v) (hw : IsFib w)
    (huv : u < v) (hvw : v < w) : u + v ≤ w := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨c, rfl⟩ := hv
  obtain ⟨e, rfl⟩ := hw
  have hac : a < c := by
    by_contra hle
    exact absurd (Nat.fib_mono (not_lt.mp hle)) (not_le.mpr huv)
  have hce : c < e := by
    by_contra hle
    exact absurd (Nat.fib_mono (not_lt.mp hle)) (not_le.mpr hvw)
  have h1 : Nat.fib a ≤ Nat.fib (e - 2) := Nat.fib_mono (by omega)
  have h2 : Nat.fib c ≤ Nat.fib (e - 2 + 1) := Nat.fib_mono (by omega)
  have h3 : Nat.fib (e - 2) + Nat.fib (e - 2 + 1) = Nat.fib e := by
    rw [← Nat.fib_add_two]
    congr 1
    omega
  omega

/-- No positive triangle among distinct Fibonacci values: for pairwise-distinct
Fibonacci u, v, w, the two smaller ones sum to at most the largest. -/
lemma fib_no_triangle {g₁ g₂ g₃ : ℕ} (h₁ : IsFib g₁) (h₂ : IsFib g₂) (h₃ : IsFib g₃)
    (h12 : g₁ ≠ g₂) (h13 : g₁ ≠ g₃) (h23 : g₂ ≠ g₃) :
    g₁ + g₂ ≤ g₃ ∨ g₁ + g₃ ≤ g₂ ∨ g₂ + g₃ ≤ g₁ := by
  rcases lt_or_gt_of_ne h12 with h | h <;> rcases lt_or_gt_of_ne h13 with h' | h' <;>
    rcases lt_or_gt_of_ne h23 with h'' | h''
  all_goals first
    | omega
    | (have := fib_triple_bound h₁ h₂ h₃ (by omega) (by omega); omega)
    | (have := fib_triple_bound h₁ h₃ h₂ (by omega) (by omega); omega)
    | (have := fib_triple_bound h₂ h₁ h₃ (by omega) (by omega); omega)
    | (have := fib_triple_bound h₂ h₃ h₁ (by omega) (by omega); omega)
    | (have := fib_triple_bound h₃ h₁ h₂ (by omega) (by omega); omega)
    | (have := fib_triple_bound h₃ h₂ h₁ (by omega) (by omega); omega)

/-- B_n admits no 5 distinct positive integers with all ten pairwise sums in it. -/
lemma H5Witness_no_pps (n : ℕ) : ¬ HasPosPairwiseSums (H5Witness n) 5 := by
  rintro ⟨b, hinj, hpos, hsum⟩
  -- pigeonhole: among 5 integers, three share a parity
  obtain ⟨i, j, k, hij, hjk, hp1, hp2⟩ :
      ∃ i j k : Fin 5, i < j ∧ j < k ∧ b i % 2 = b j % 2 ∧ b j % 2 = b k % 2 := by
    by_contra hcon
    push_neg at hcon
    have h012 := hcon 0 1 2 (by decide) (by decide)
    have h013 := hcon 0 1 3 (by decide) (by decide)
    have h014 := hcon 0 1 4 (by decide) (by decide)
    have h023 := hcon 0 2 3 (by decide) (by decide)
    have h024 := hcon 0 2 4 (by decide) (by decide)
    have h034 := hcon 0 3 4 (by decide) (by decide)
    have h123 := hcon 1 2 3 (by decide) (by decide)
    have h124 := hcon 1 2 4 (by decide) (by decide)
    have h134 := hcon 1 3 4 (by decide) (by decide)
    have h234 := hcon 2 3 4 (by decide) (by decide)
    omega
  have hik : i < k := hij.trans hjk
  -- the three same-parity pairwise sums are doubled Fibonacci numbers
  obtain ⟨g₁, hf₁, _, _, he₁⟩ := even_mem_H5Witness (hsum i j hij) (by omega)
  obtain ⟨g₂, hf₂, _, _, he₂⟩ := even_mem_H5Witness (hsum i k hik) (by omega)
  obtain ⟨g₃, hf₃, _, _, he₃⟩ := even_mem_H5Witness (hsum j k hjk) (by omega)
  -- the b's are distinct, so the g's are distinct
  have nij : b i ≠ b j := fun h => absurd (hinj h) hij.ne
  have nik : b i ≠ b k := fun h => absurd (hinj h) hik.ne
  have njk : b j ≠ b k := fun h => absurd (hinj h) hjk.ne
  have hg12 : g₁ ≠ g₂ := by intro h; apply njk; omega
  have hg13 : g₁ ≠ g₃ := by intro h; apply nik; omega
  have hg23 : g₂ ≠ g₃ := by intro h; apply nij; omega
  have pi := hpos i
  have pj := hpos j
  have pk := hpos k
  -- 2·bᵢ = 2g₁ + 2g₂ − 2g₃ etc.: positivity contradicts the Fibonacci bound
  rcases fib_no_triangle hf₁ hf₂ hf₃ hg12 hg13 hg23 with h | h | h <;> omega

/-- **h₅(n) > fibCnt n for all n** (C1 extremal-structure lens):
the number of Fibonacci values ≤ n is a strict lower bound for hFun 5 n.
Beats the upstream-formalized `h5lower` (Nat.log 2 n < hFun 5 n) pointwise for
n ≥ 2 — fibCnt n ≥ Nat.log 2 n + 1 there (C1 exact check to 10⁶, min margin 1;
that comparison is NOT formalized here) — and improves the asymptotic lower
constant by the factor 1/log₂ φ = 1.4404…. -/
theorem fibCnt_lt_hFun_five (n : ℕ) : fibCnt n < hFun 5 n := by
  unfold hFun
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  apply le_csInf
  · refine ⟨2 * n + 1, fun A hA hcard => absurd hcard (not_le.mpr ?_)⟩
    have h1 := Finset.card_le_card hA
    have h2 : (Finset.Icc (1 : ℤ) (2 * (n : ℤ))).card = 2 * n := by
      rw [Int.card_Icc]; omega
    omega
  · intro m hm
    by_contra hcon
    push_neg at hcon
    refine H5Witness_no_pps n (hm (H5Witness n) (H5Witness_subset n) ?_)
    rw [H5Witness_card n]
    omega

/-! ## Sanity anchors (definitional faithfulness of IsFib/fibCnt) -/

example : IsFib 1 := ⟨1, rfl⟩
example : IsFib 2 := ⟨3, rfl⟩
example : IsFib 21 := ⟨8, rfl⟩
example : ¬ IsFib 4 := by
  rintro ⟨j, hj⟩
  have hub : j ≤ 5 := by
    have := Nat.le_fib_add_one j
    omega
  interval_cases j <;> revert hj <;> decide

/-! ## Axiom audit (must be [propext, Classical.choice, Quot.sound] only) -/

#print axioms four_le_hFun_four
#print axioms gFun_four_lt_hFun_four
#print axioms fibCnt_lt_hFun_five

end Erdos866
