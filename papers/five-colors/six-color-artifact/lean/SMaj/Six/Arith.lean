/-
SMaj/Six/Arith.lean — the arithmetic of the T1 ≤ 6 proof
(`lenses/L2-chain-grouping/WRITEUP.md` Lemma 2: rules R1–R4 for the
junction group count g(d) = ⌈d/4⌉), proved for ALL degrees — strictly
stronger than the L2 battery `battery_arith` (enumerated to 400).

L2's g(d) (defined there for junctions, d ≥ 3) is `hfun 4 d` of
`SMaj/Arith.lean` (h_s with s = 4): for d ≥ 2, hfun 4 d = ⌈d/4⌉.
All proofs are kernel-checked integer arithmetic (`omega` after unfolding;
division by the literals 2 and 4 is in omega's fragment).

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12.  Machine pretest:
`lenses/C3L4-lean-six/pretest_claims.py` (P3) re-pinned R1–R4 to 2000
before these proofs were written.
-/
import Mathlib
import SMaj.Arith

namespace SMaj

/-- R1: two junction group counts fit under the junction–junction row cap:
g(a) + g(b) ≤ ⌊(a+b−2)/2⌋ for all a, b ≥ 3 (L2 Lemma 2, R1). -/
theorem g_R1 {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    hfun 4 a + hfun 4 b ≤ (a + b - 2) / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R1 in `Crit` form: every degree pair with both entries ≥ 3 — and more
generally avoiding degree 2 entirely — satisfies CRIT₄ (the s = 4 bad pairs
(1,2), (2,2), (2,3), (2,5) all contain a 2).  This is the arithmetic behind
L2's case (b) rows including pendant ends. -/
theorem crit4_of_ne_two {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha2 : a ≠ 2) (hb2 : b ≠ 2) : Crit 4 a b := by
  unfold Crit hfun; split_ifs <;> omega

/-- R2: a junction group count fits under a junction–pendant row cap:
g(b) ≤ ⌊(b−1)/2⌋ for b ≥ 3 (L2 Lemma 2, R2). -/
theorem g_R2 {b : ℕ} (hb : 3 ≤ b) : hfun 4 b ≤ (b - 1) / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R3: a junction group count fits under the chain-end row cap:
g(d) ≤ ⌊d/2⌋ for d ≥ 3 (L2 Lemma 2, R3). -/
theorem g_R3 {d : ℕ} (hd : 3 ≤ d) : hfun 4 d ≤ d / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R4, strict part: away from degrees 3 and 5 the group count sits STRICTLY
below the chain-end cap — g(d) + 1 ≤ ⌊d/2⌋ for d ≥ 3, d ∉ {3,5}
(L2 Lemma 2, R4; the source of "F_x = ∅ unless d(x) ∈ {3,5}"). -/
theorem g_R4 {d : ℕ} (hd : 3 ≤ d) (h3 : d ≠ 3) (h5 : d ≠ 5) :
    hfun 4 d + 1 ≤ d / 2 := by
  unfold hfun; split_ifs <;> omega

/-- R4, saturation part: at the two exceptional degrees the group count
exactly meets the cap (g(3) = 1 = ⌊3/2⌋, g(5) = 2 = ⌊5/2⌋). -/
theorem g_R4_eq {d : ℕ} (h : d = 3 ∨ d = 5) : hfun 4 d = d / 2 := by
  rcases h with rfl | rfl <;> rfl

end SMaj
