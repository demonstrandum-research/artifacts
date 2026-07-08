-- C4-P3 (all-k T2 write-up) axiom audit: every formal anchor cited by
-- lenses/C4P3-allk-writeup/T2-ALLK.md must close over exactly
-- [propext, Classical.choice, Quot.sound] with NO sorryAx.
-- Run: lake env lean scripts/AuditC4P3.lean   (from lean/)
import Erdos866

-- Statement pins (compile-time checks that the cited claims say what the
-- write-up says they say).

-- [K1] Lemma A, general k ≥ 3 (g-chain, forbidden-set parameter):
example : ∀ (k : ℕ), 3 ≤ k → ∀ (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (F : Finset ℤ), (∀ f ∈ F, 0 < f) → (∀ a ∈ A₀, 2 ∣ a) → (∀ a ∈ A₀, 2 ≤ a) →
    2 ≤ A₀.max' hne - A₀.min' hne →
    Erdos866.fStar k (↑(A₀.max' hne - A₀.min' hne)) (F.card : ℝ) ≤ (A₀.card : ℝ) →
    Erdos866.HasSubsetSumsAvoiding A₀ F k :=
  fun k hk A₀ hne F hF he hp hr hc => Erdos866.lemmaA k hk A₀ hne F hF he hp hr hc

-- [K2] φ = 0 corollary (pairwise sums), general k ≥ 3:
example : ∀ (k : ℕ), 3 ≤ k → ∀ (A₀ : Finset ℤ) (hne : A₀.Nonempty),
    (∀ a ∈ A₀, 2 ∣ a) → (∀ a ∈ A₀, 2 ≤ a) →
    2 ≤ A₀.max' hne - A₀.min' hne →
    Erdos866.fStar k (↑(A₀.max' hne - A₀.min' hne)) 0 ≤ (A₀.card : ℝ) →
    HasPairwiseSums A₀ k :=
  fun k hk A₀ hne he hp hr hc => Erdos866.ceslemgeneral_star k hk A₀ hne he hp hr hc

-- [K3] fStar monotonicity in x and the ≥ 2 floor (used in the assembly):
example : ∀ (k : ℕ), 3 ≤ k → ∀ x y φ : ℝ, 0 ≤ φ → 2 ≤ x → x ≤ y →
    Erdos866.fStar k x φ ≤ Erdos866.fStar k y φ :=
  fun k hk x y φ h0 h2 hxy => Erdos866.fStar_mono_x k hk x y φ h0 h2 hxy
example : ∀ (k : ℕ), 3 ≤ k → ∀ x φ : ℝ, 2 ≤ x → 0 ≤ φ →
    2 ≤ Erdos866.fStar k x φ :=
  fun k hk x φ hx hφ => Erdos866.fStar_ge_two k hk x φ hx hφ

-- [K4] kernel-verified k = 5 instance (T1 closure, charter constant):
example : ∀ n : ℕ, gFun 5 n < 3519220 := Erdos866.g5upper_star_charter

-- [K5] kernel-verified k = 4 h-side instance (T1 closure):
example : ∀ n : ℕ, 0 < n → hFun 4 n ≤ 1000 := fun n h => h4_le_1000 n h

-- [K6] upstream baseline being improved (old Thm 9, constant 4):
example : ∀ (k : ℕ), 3 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    gFun k n ≤ hFun k n ∧
    (hFun k n : ℝ) < 4 * (↑n : ℝ) ^ ((1:ℝ) - 1 / 2 ^ ((k:ℝ) - 2)) :=
  fun k hk => generalupper k hk

-- [K7] g ≤ h bridge and the subset-sums → pairwise-sums bridge:
example : ∀ k n : ℕ, gFun k n ≤ hFun k n := fun k n => gFun_le_hFun k n

-- Axiom audit (expect exactly [propext, Classical.choice, Quot.sound] each):
#print axioms Erdos866.lemmaA
#print axioms Erdos866.lemmaA_pigeonhole
#print axioms Erdos866.lemmaA_extend
#print axioms Erdos866.ceslemgeneral_star
#print axioms Erdos866.fStar_mono_x
#print axioms Erdos866.fStar_ge_two
#print axioms Erdos866.fStar_succ
#print axioms Erdos866.fStar_root_base
#print axioms Erdos866.fStar_root_step
#print axioms Erdos866.g5upper_star_charter
#print axioms Erdos866.key_ineq_star_charter
#print axioms h4_le_1000
#print axioms generalupper
#print axioms hk_upper
#print axioms gFun_le_hFun
#print axioms subsetsums_to_pairwise
