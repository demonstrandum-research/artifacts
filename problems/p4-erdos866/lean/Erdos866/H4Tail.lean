/-
Erdős #866, Campaign 2, P1 — tail certificate (t > 400000) for h₄(n) ≤ 1000.

NEW module (not in the upstream development). Formalizes the Tail Lemma of the
central-interval lens (PROOF.md §7.1): for t > 400000 the explicit tuple
  u_S = ⌈√N₀_S⌉ (here: Nat.sqrt N₀ + 1, which suffices),
  Φ_S = 2u_S, ν_S = 4u_S, ψ_S = Nat.sqrt (4·x_S·u_S) + 2
satisfies the same (V2)-(V5) certificate shape as the finite block table
(`cert_lookup` in Erdos866/H4Cert.lean), with x_L = 8t+2, x_H = 4t+2,
N₀_L = 4t+2, N₀_H = 2t+2.
-/
import Mathlib

set_option maxHeartbeats 800000

namespace ErdosH4Tail

/-- (T1) The energy violation for the tail tuple: if N ≤ u² and u ≥ 7 then
(N + 4u − 1)(3·2u + 4u − 1) < (2u)²·(4u) = 16u³. -/
lemma tail_V (N u : ℕ) (hu : 7 ≤ u) (hN : N ≤ u * u) :
    (N + 4*u - 1) * (3*(2*u) + 4*u - 1) < (2*u)*(2*u)*(4*u) := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 7 := ⟨u - 7, by omega⟩
  have h1 : N + 4*(w+7) - 1 = N + (4*w + 27) := by omega
  have h2 : 3*(2*(w+7)) + 4*(w+7) - 1 = 10*w + 69 := by omega
  rw [h1, h2]
  have h3 : (N + (4*w+27)) * (10*w+69) ≤ ((w+7)*(w+7) + (4*w+27)) * (10*w+69) :=
    mul_le_mul_right' (Nat.add_le_add_right hN _) _
  refine lt_of_le_of_lt h3 ?_
  nlinarith [Nat.zero_le w]

/-- (T2) The popularity threshold for the tail tuple:
2x(2u − 1) < ψ(ψ−1) with ψ = √(4xu) + 2. -/
lemma tail_W (x u : ℕ) (hx : 0 < x) (hu : 0 < u) :
    2*x*(2*u-1) < (Nat.sqrt (4*x*u) + 2) * ((Nat.sqrt (4*x*u) + 2) - 1) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
  have h : 4*x*(v+1) < (Nat.sqrt (4*x*(v+1)) + 1) * (Nat.sqrt (4*x*(v+1)) + 1) :=
    Nat.lt_succ_sqrt _
  have e1 : (Nat.sqrt (4*x*(v+1)) + 2) - 1 = Nat.sqrt (4*x*(v+1)) + 1 := by omega
  have e2 : 2*(v+1) - 1 = 2*v + 1 := by omega
  rw [e1, e2]
  nlinarith [h, hx]

/-- Cauchy–Schwarz for two naturals: (a+b)² ≤ 2(a²+b²). -/
lemma sq_add_le (a b : ℕ) : (a+b)*(a+b) ≤ 2*(a*a + b*b) := by
  rcases le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith [Nat.zero_le c]
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    nlinarith [Nat.zero_le c]

/-- (T3) The surplus bound for the tail: ψ_L + ψ_H ≤ 1001 + t for t > 400000,
with ψ_L = √(4·(8t+2)·u_L)+2, u_L = √(4t+2)+1, ψ_H = √(4·(4t+2)·u_H)+2,
u_H = √(2t+2)+1. -/
lemma tail_psi_sum (t : ℕ) (ht : 400000 < t) :
    (Nat.sqrt (4*(8*t+2)*(Nat.sqrt (4*t+2) + 1)) + 2) +
      (Nat.sqrt (4*(4*t+2)*(Nat.sqrt (2*t+2) + 1)) + 2) ≤ 1001 + t := by
  have hb1 : Nat.sqrt t * Nat.sqrt t ≤ t := Nat.sqrt_le t
  have hb2 : t < (Nat.sqrt t + 1) * (Nat.sqrt t + 1) := Nat.lt_succ_sqrt t
  have hb3 : 632 ≤ Nat.sqrt t := Nat.le_sqrt.mpr (by omega)
  set b := Nat.sqrt t with hb_def
  -- u_L − 1 = √(4t+2) ≤ 2b+2
  have ha1' : Nat.sqrt (4*t+2) * Nat.sqrt (4*t+2) ≤ 4*t+2 := Nat.sqrt_le _
  have ha1le : Nat.sqrt (4*t+2) ≤ 2*b+2 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (2*b+3)*(2*b+3) ≤ Nat.sqrt (4*t+2) * Nat.sqrt (4*t+2) :=
      Nat.mul_le_mul hcon hcon
    nlinarith [hb2, ha1', h1]
  set a1 := Nat.sqrt (4*t+2) with ha1_def
  -- u_H − 1 = √(2t+2) ≤ 2b
  have ha2' : Nat.sqrt (2*t+2) * Nat.sqrt (2*t+2) ≤ 2*t+2 := Nat.sqrt_le _
  have ha2le : Nat.sqrt (2*t+2) ≤ 2*b := by
    by_contra hcon
    push_neg at hcon
    have h1 : (2*b+1)*(2*b+1) ≤ Nat.sqrt (2*t+2) * Nat.sqrt (2*t+2) :=
      Nat.mul_le_mul hcon hcon
    nlinarith [hb2, ha2', h1, hb3]
  set a2 := Nat.sqrt (2*t+2) with ha2_def
  -- the two outer square roots
  have hs1 : Nat.sqrt (4*(8*t+2)*(a1+1)) * Nat.sqrt (4*(8*t+2)*(a1+1)) ≤ 4*(8*t+2)*(a1+1) :=
    Nat.sqrt_le _
  have hs2 : Nat.sqrt (4*(4*t+2)*(a2+1)) * Nat.sqrt (4*(4*t+2)*(a2+1)) ≤ 4*(4*t+2)*(a2+1) :=
    Nat.sqrt_le _
  set s1 := Nat.sqrt (4*(8*t+2)*(a1+1)) with hs1_def
  set s2 := Nat.sqrt (4*(4*t+2)*(a2+1)) with hs2_def
  -- s1² ≤ (32t+8)(2b+3), s2² ≤ (16t+8)(2b+1)
  have hs1' : s1*s1 ≤ (32*t+8)*(2*b+3) := by
    refine le_trans hs1 ?_
    have : 4*(8*t+2)*(a1+1) ≤ 4*(8*t+2)*(2*b+3) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith [this]
  have hs2' : s2*s2 ≤ (16*t+8)*(2*b+1) := by
    refine le_trans hs2 ?_
    have : 4*(4*t+2)*(a2+1) ≤ 4*(4*t+2)*(2*b+1) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith [this]
  -- (s1+s2)² ≤ 192tb + 224t + 64b + 64
  have hsum_sq : (s1+s2)*(s1+s2) ≤ 192*(t*b) + 224*t + 64*b + 64 := by
    refine le_trans (sq_add_le s1 s2) ?_
    have h1 : s1*s1 + s2*s2 ≤ (32*t+8)*(2*b+3) + (16*t+8)*(2*b+1) :=
      Nat.add_le_add hs1' hs2'
    nlinarith [h1]
  -- 192tb + 224t + 64b + 64 ≤ (t−3)²
  have hkey : 192*(t*b) + 224*t + 64*b + 64 ≤ (t-3)*(t-3) := by
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 3 := ⟨t - 3, by omega⟩
    have e : m + 3 - 3 = m := by omega
    rw [e]
    have h632 : 632*b ≤ b*b := Nat.mul_le_mul_right b hb3
    have hbb : b*b ≤ m+3 := hb1
    have h1 : 632*(m*b) ≤ m*m + 3*m := by
      have c1 : 632*(m*b) = m*(632*b) := by ring
      have c2 : m*(632*b) ≤ m*(m+3) := Nat.mul_le_mul_left m (le_trans h632 hbb)
      nlinarith [c2]
    have h2 : 632*b ≤ m+3 := le_trans h632 hbb
    have h3 : 399998 ≤ m := by omega
    have h4 : 399998*m ≤ m*m := Nat.mul_le_mul_right m h3
    nlinarith [h1, h2, h4]
  -- conclude s1 + s2 ≤ t − 3
  have hfin : s1 + s2 ≤ t - 3 := by
    by_contra hcon
    push_neg at hcon
    have hlt : (t-3)*(t-3) < (s1+s2)*(s1+s2) := Nat.mul_self_lt_mul_self hcon
    exact absurd (le_trans hsum_sq hkey) (Nat.not_le.mpr hlt)
  omega

set_option maxHeartbeats 1600000 in
/-- Tail certificate: for t > 400000 the explicit tail tuple satisfies the same
certificate interface as `cert_lookup` (with t2 = t). -/
lemma tail_cert (t : ℕ) (ht : 400000 < t) :
    ∃ t2 ΦL νL ψL ΦH νH ψH : ℕ,
      t ≤ t2 ∧ 0 < ΦL ∧ 0 < νL ∧ 0 < ΦH ∧ 0 < νH ∧
      (4*t2 + 1 + νL) * (3*ΦL + νL - 1) < ΦL*ΦL*νL ∧
      (2*t2 + 1 + νH) * (3*ΦH + νH - 1) < ΦH*ΦH*νH ∧
      2*(8*t2+2)*(ΦL-1) < ψL*(ψL-1) ∧
      2*(4*t2+2)*(ΦH-1) < ψH*(ψH-1) ∧
      ψL + ψH ≤ 1001 + t := by
  refine ⟨t, 2*(Nat.sqrt (4*t+2) + 1), 4*(Nat.sqrt (4*t+2) + 1),
    Nat.sqrt (4*(8*t+2)*(Nat.sqrt (4*t+2) + 1)) + 2,
    2*(Nat.sqrt (2*t+2) + 1), 4*(Nat.sqrt (2*t+2) + 1),
    Nat.sqrt (4*(4*t+2)*(Nat.sqrt (2*t+2) + 1)) + 2,
    le_refl t, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · -- (V2), low side: N₀ = 4t+2
    have h7 : 7 ≤ Nat.sqrt (4*t+2) + 1 := by
      have : 6 ≤ Nat.sqrt (4*t+2) := Nat.le_sqrt.mpr (by omega)
      omega
    have hN : 4*t+2 ≤ (Nat.sqrt (4*t+2) + 1) * (Nat.sqrt (4*t+2) + 1) :=
      le_of_lt (Nat.lt_succ_sqrt _)
    have := tail_V (4*t+2) (Nat.sqrt (4*t+2) + 1) h7 hN
    have e : 4*t+2 + 4*(Nat.sqrt (4*t+2) + 1) - 1
        = 4*t + 1 + 4*(Nat.sqrt (4*t+2) + 1) := by omega
    rwa [e] at this
  · -- (V3), high side: N₀ = 2t+2
    have h7 : 7 ≤ Nat.sqrt (2*t+2) + 1 := by
      have : 6 ≤ Nat.sqrt (2*t+2) := Nat.le_sqrt.mpr (by omega)
      omega
    have hN : 2*t+2 ≤ (Nat.sqrt (2*t+2) + 1) * (Nat.sqrt (2*t+2) + 1) :=
      le_of_lt (Nat.lt_succ_sqrt _)
    have := tail_V (2*t+2) (Nat.sqrt (2*t+2) + 1) h7 hN
    have e : 2*t+2 + 4*(Nat.sqrt (2*t+2) + 1) - 1
        = 2*t + 1 + 4*(Nat.sqrt (2*t+2) + 1) := by omega
    rwa [e] at this
  · -- (V4), low side: x = 8t+2
    exact tail_W (8*t+2) (Nat.sqrt (4*t+2) + 1) (by omega) (by omega)
  · -- (V4), high side: x = 4t+2
    exact tail_W (4*t+2) (Nat.sqrt (2*t+2) + 1) (by omega) (by omega)
  · -- (V5)
    exact tail_psi_sum t ht

end ErdosH4Tail
