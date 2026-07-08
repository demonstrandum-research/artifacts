/-
Erdős #866 — index of the standing bounds (frozen dossier
problems/p4-erdos866/PROBLEM.md §5, freeze date 2026-06-12).

This module is the auditable bridge between the dossier and the vendored
upstream development (Erdos866/Upstream.lean = Woett/Lean-files/
ErdosProblem866.lean, byte-identical). Every `standing_*` theorem below is
proved BY DIRECT REFERENCE to the upstream theorem, so elaborating this file
checks that the dossier's claimed statements match the formal ones exactly.

Definitional anchors (dossier §3, ambiguities A1–A10):
- gFun k n : minimal surplus m s.t. every A ⊆ Icc 1 (2n) (A : Finset ℤ) with
  n + m ≤ |A| admits k DISTINCT INTEGERS b_i (need not be in A, need not be
  positive) with all pairwise sums b_i + b_j ∈ A   [g_k(n)]
- hFun k n : same with k distinct POSITIVE integers [h_k(n)]
-/
import Erdos866.Upstream

namespace Erdos866

/-! ## Definitional cross-checks (dossier §3 ↔ upstream, by `rfl`)

These `example`s fail to elaborate if the vendored definitions ever drift
from the dossier's frozen definitions. -/

example : ∀ (A : Finset ℤ) (k : ℕ),
    HasPairwiseSums A k =
      ∃ b : Fin k → ℤ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A :=
  fun _ _ => rfl

example : ∀ (A : Finset ℤ) (k : ℕ),
    HasPosPairwiseSums A k =
      ∃ b : Fin k → ℤ, Function.Injective b ∧ (∀ i : Fin k, 0 < b i) ∧
        ∀ i j : Fin k, i < j → b i + b j ∈ A :=
  fun _ _ => rfl

example : ∀ k n : ℕ,
    gFun k n = sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Finset.Icc (1 : ℤ) (2 * ↑n) →
      n + m ≤ A.card → HasPairwiseSums A k} :=
  fun _ _ => rfl

example : ∀ k n : ℕ,
    hFun k n = sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Finset.Icc (1 : ℤ) (2 * ↑n) →
      n + m ≤ A.card → HasPosPairwiseSums A k} :=
  fun _ _ => rfl

/-! ## Structure: the sandwich g_k ≤ h_k ≤ g_{k+1}  (dossier §5 "structure") -/

theorem standing_sandwich (k n : ℕ) :
    gFun k n ≤ hFun k n ∧ hFun k n ≤ gFun (k + 1) n :=
  gFun_le_hFun_le_gFun_succ k n

/-! ## k = 3  (dossier §5 rows 1–2) -/

/-- g₃(n) = 1 for n ≥ 3 [vD26 Thm 1, Lean `g3`]. -/
theorem standing_g3 (n : ℕ) (hn : 3 ≤ n) : gFun 3 n = 1 := g3 n hn

/-- g₃(1) = g₃(2) = 2 [vD26 Remark 1, Lean `g3small`]. -/
theorem standing_g3small : gFun 3 1 = 2 ∧ gFun 3 2 = 2 := g3small

/-- h₃(n) = 2 for n ≥ 4 [CES75 Thm 1, Lean `h3`]. -/
theorem standing_h3 (n : ℕ) (hn : 4 ≤ n) : hFun 3 n = 2 := h3 n hn

/-! ## k = 4  (dossier §5 rows 3–4) -/

/-- g₄(n) = 3 for n ≥ 2 [vD26 Thm 3, Lean `g4`]. -/
theorem standing_g4 (n : ℕ) (hn : 2 ≤ n) : gFun 4 n = 3 := g4 n hn

/-- h₄(n) ≤ 2270 for n ≥ 1 [vD26 §7 + Aristotle, Lean `h4upper`].
    THE T1 TARGET CONSTANT: any Lean-verified B < 2270 here is progress. -/
theorem standing_h4_upper (n : ℕ) (hn : 0 < n) : hFun 4 n ≤ 2270 := h4upper n hn

/-- h₄(n) ≥ 3 for n ≥ 2 (only via g₄ = 3 and the sandwich; true value unknown,
    gap [3, 2270]) [dossier §5 row 4]. -/
theorem standing_h4_lower (n : ℕ) (hn : 2 ≤ n) : 3 ≤ hFun 4 n := by
  have h := (gFun_le_hFun_le_gFun_succ 4 n).1
  rw [standing_g4 n hn] at h
  exact h

/-! ## k = 5  (dossier §5 rows 5–6) -/

/-- g₅(n) < 1.2·10⁸ for all n [vD26 Thm 8, Lean `g5upper`].
    THE OTHER T1 TARGET CONSTANT (paper-internal C = 113,591,719). -/
theorem standing_g5_upper (n : ℕ) : gFun 5 n < 120000000 := g5upper n

/-- g₅(n) ≥ 4 for n ≥ 3 [vD26 Thm 5, Lean `g5lower`]. -/
theorem standing_g5_lower (n : ℕ) (hn : 3 ≤ n) : 4 ≤ gFun 5 n := g5lower n hn

/-- h₅(n) > log₂ n for all n [CES75 example repaired for h, vD26 Thm 4,
    Lean `h5lower`]; with CES75 Thm 3 (h₅ ≪ log n, not formalized anywhere)
    this gives h₅ ≍ log n. -/
theorem standing_h5_lower (n : ℕ) : Nat.log 2 n < hFun 5 n := h5lower n

/-! ## General k  (dossier §5 rows 7–8) -/

/-- Effective general upper bound: h_k(n) ≤ ⌈boundPos k (2n)⌉ + 1 for k ≥ 3,
    n ≥ 1 [Lean `hk_upper`], where `boundPos` is the closed-form solution of
    the F_k recursion (dossier §6). -/
theorem standing_hk_upper (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    hFun k n ≤ Nat.ceil (boundPos k (2 * ↑n)) + 1 := hk_upper k hk n hn

/-- Asymptotic form: g_k(n) ≤ h_k(n) < 4·n^(1 − 2^(2−k)) for n ≥ N(k)
    (ineffective N) [vD26 Thm 9, Lean `generalupper`]. -/
theorem standing_general_upper (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      gFun k n ≤ hFun k n ∧
      (hFun k n : ℝ) < 4 * (↑n : ℝ) ^ ((1 : ℝ) - 1 / 2 ^ ((k : ℝ) - 2)) :=
  generalupper k hk

/-! ## T1 targets (dossier §10), as formal Props

A future campaign proves `T1TargetH4 B` for some B < 2270 and/or
`T1TargetG5 B'` for some B' < 120000000. Stated here so the goal itself is
pinned formally. Campaign-1 paper-grade targets (ATTACK.md, exact-integer
optimized): B = 1000 via the energy-form asymmetric-central-interval route,
fallback B = 1529 from published-Ruzsa ingredients only (the older
Codex-sketched figure 1530 came from the real-valued sup 1529.74 with window
8t+4; the correct integer optimum with diameters 8t+2/4t+2 is 1529 — do not
port 1530-era threshold arithmetic); g₅ target B' = 3519220 (gFun 5 n <
3519220, i.e. ≤ 3519219). -/

/-- "h₄ improved to B": B beats 2270 and is a uniform upper bound for hFun 4. -/
def T1TargetH4 (B : ℕ) : Prop :=
  B < 2270 ∧ ∀ n : ℕ, 0 < n → hFun 4 n ≤ B

/-- "g₅ improved to B'": B' beats 1.2·10⁸ and is a uniform strict upper bound
    for gFun 5. -/
def T1TargetG5 (B' : ℕ) : Prop :=
  B' < 120000000 ∧ ∀ n : ℕ, gFun 5 n < B'

/-- The standing bound is exactly the degenerate (non-improving) instance:
    the baseline the T1 campaign must beat. -/
theorem h4_baseline : ∀ n : ℕ, 0 < n → hFun 4 n ≤ 2270 := h4upper

end Erdos866
