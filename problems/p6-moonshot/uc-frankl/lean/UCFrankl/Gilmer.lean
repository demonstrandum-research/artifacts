import Mathlib
import UCFrankl.Frankl
import UCFrankl.Entropy

/-!
# The Gilmer entropy reduction, kernel-checked

Program UC, lens L5 (Lean bridgehead, T2). This file formalizes the *scheme* of
Gilmer's 2022 entropy breakthrough (arXiv:2211.09055; = D6 of
`problems/p6-moonshot/PROBLEM.md`) and kernel-checks its combinatorial half.

Gilmer's argument splits exactly in two:

1. **The reduction** (combinatorial, this file, MACHINE-VERIFIED):
   if the "entropic engine" holds at threshold `c` — every distribution `p` on
   `2^[n]` with positive entropy and all marginals `< c` satisfies
   `H(p) < H(p ⊔ p)`, where `p ⊔ p` is the pushforward of the independent
   coupling under union — then the union-closed conjecture holds with
   constant `c`. The contradiction: take `p` uniform on a union-closed `F`;
   union-closure keeps `p ⊔ p` supported inside `F`, so its entropy is at most
   `log |F| = H(p)`, while the engine forces it strictly above.

2. **The engine** (analytic, NOT formalized here): `GilmerEngine c` for a
   concrete `c`. Provenance, stated precisely (hostile-pass correction
   2026-06-13): the literature proves sharper *non-strict* forms — AHS
   (arXiv:2211.11731) and Boppana (arXiv:2301.09664) give
   `H(A∪B) ≥ H(A)`-type endpoint inequalities, Chase–Lovett (arXiv:2211.11689)
   gives `H(A∪B) ≥ (p/(2φ))(H(A)+H(B))` when all zero-marginals are `≥ p`,
   Sawin (arXiv:2211.11504) a multiplier form. `GilmerEngine ψ` as stated here
   (strict inequality, arbitrary pmf) is DERIVABLE from these via a short
   bridge: with finitely many marginals all `< ψ`, the maximum marginal is some
   `u < ψ`, and the Chase–Lovett/Sawin multiplier at `u` exceeds 1 strictly
   when `H(p) > 0`. So the honest tag is PROVED-in-literature-modulo-bridge,
   not verbatim-in-literature. It is FALSE for every `c > ψ` (Pebody
   arXiv:2211.13139 — the one-step functional's optimum is exactly `ψ`).

## EPISTEMIC-STATUS LEDGER

* `pushforward₂`, `marginal`, `GilmerEngine`, `psi` — definitions [PROVED].
* `isPMF_pushforward₂`, `pushforward₂_eq_zero`, `marginal_uniformOn`,
  `franklWithConstant_of_gilmerEngine` — MACHINE-VERIFIED (kernel-checked;
  axiom audit in `scripts/CheckAxioms.lean`).
* `two_mul_psi_sub_sq`, `binEntropy_at_psi`, `psi_pos`, `psi_lt_half`,
  `binEntropy_le_binEntropy_union` — MACHINE-VERIFIED (kernel-checked).
  `binEntropy_le_binEntropy_union` is the Bernoulli (product-measure) shadow of
  the engine inequality: `h(x) ≤ h(2x − x²)` for `x ∈ [0, ψ]`, with equality at
  `x = ψ` (`binEntropy_at_psi`) — the exact place the golden constant enters.
* `GilmerEngine psi` — (C1 entry; STATUS UPDATED at C3L1 2026-06-13:
  `GilmerEngine c` is now kernel-PROVED for every `c < psi` —
  `gilmerEngine_of_lt_psi` in `DiagonalReduction.lean`; the endpoint Prop
  `GilmerEngine psi` itself is intentionally not derived — sup-closure at the
  Frankl level absorbs the endpoint, `franklWithConstant_of_forall_lt`.)
  Original: PROVED-in-literature-modulo-bridge (see point 2 above:
  the cited papers prove non-strict/multiplier forms), NOT yet formalized.
  `GilmerEngine c` for `c > psi` — FALSE (Pebody; not formalized).
* `FranklWithConstant psi` — **kernel-PROVED at C3L1 (2026-06-13):
  `franklWithConstant_psi` in `DiagonalReduction.lean`, axioms-clean.**
  (Original C1 entry — "PROVED in literature; no kernel-checked claim is
  made" — superseded.)
-/

namespace UCFrankl

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Pushforward of the independent coupling `p ⊗ q` under a binary operation
`f`: the law of `f(A,B)` for `A ~ p`, `B ~ q` independent. [PROVED: definition.] -/
noncomputable def pushforward₂ (f : α → α → α) (p q : α → ℝ) : α → ℝ :=
  fun c => ∑ a, ∑ b, if f a b = c then p a * q b else 0

/-- The pushforward of a product of pmfs is a pmf. [MACHINE-VERIFIED.] -/
theorem isPMF_pushforward₂ (f : α → α → α) {p q : α → ℝ}
    (hp : IsPMF p) (hq : IsPMF q) : IsPMF (pushforward₂ f p q) where
  nonneg c := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs with h
    · exact mul_nonneg (hp.nonneg a) (hq.nonneg b)
    · exact le_rfl
  sum_one := by
    unfold pushforward₂
    calc ∑ c, ∑ a, ∑ b, (if f a b = c then p a * q b else 0)
        = ∑ a, ∑ c, ∑ b, (if f a b = c then p a * q b else 0) := Finset.sum_comm
      _ = ∑ a, ∑ b, ∑ c, (if f a b = c then p a * q b else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ a, ∑ b, p a * q b := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_ite_eq]
          simp
      _ = 1 := by rw [← Finset.sum_mul_sum, hp.sum_one, hq.sum_one, mul_one]

/-- If `p`, `q` are supported in `S` and `S` is closed under `f`, the
pushforward is supported in `S`. This is the ONLY place union-closure enters
Gilmer's argument. [MACHINE-VERIFIED.] -/
theorem pushforward₂_eq_zero {f : α → α → α} {p q : α → ℝ} {S : Finset α}
    (hpS : ∀ a, p a ≠ 0 → a ∈ S) (hqS : ∀ b, q b ≠ 0 → b ∈ S)
    (hfS : ∀ a ∈ S, ∀ b ∈ S, f a b ∈ S) {c : α} (hc : c ∉ S) :
    pushforward₂ f p q c = 0 := by
  unfold pushforward₂
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · by_contra hne
    rcases mul_ne_zero_iff.mp hne with ⟨hpa, hqb⟩
    exact hc (h ▸ hfS a (hpS a hpa) b (hqS b hqb))
  · rfl

/-- The `i`-th marginal of a distribution on `2^[n]`: `Pr[i ∈ A]` for `A ~ p`.
[PROVED: definition.] -/
noncomputable def marginal {n : ℕ} (p : Finset (Fin n) → ℝ) (i : Fin n) : ℝ :=
  ∑ A, if i ∈ A then p A else 0

/-- Marginals of the uniform distribution are the normalized frequencies.
[MACHINE-VERIFIED.] -/
theorem marginal_uniformOn {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n) :
    marginal (uniformOn F) i = (freq F i : ℝ) * ((F.card : ℝ))⁻¹ := by
  unfold marginal uniformOn freq
  simp_rw [← ite_and]
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter fun A : Finset (Fin n) => i ∈ A ∧ A ∈ F)
      = F.filter (fun A => i ∈ A) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hset, Finset.sum_const, nsmul_eq_mul]

/-- **Gilmer's entropic engine** at marginal threshold `c`: every distribution
on `2^[n]` with positive entropy and all marginals `< c` strictly gains entropy
under the independent-union pushforward.

LEDGER: this is a *statement* (a `Prop`), not a claim. For `c ≤ ψ = (3−√5)/2`
it is PROVED-in-literature-modulo-bridge (AHS 2211.11731, Chase–Lovett
2211.11689, Boppana 2301.09664 prove non-strict/multiplier forms; see the file
header for the bridge) and NOT YET formalized; for `c > ψ` it is FALSE
(Pebody 2211.13139). -/
def GilmerEngine (c : ℝ) : Prop :=
  ∀ (n : ℕ) (p : Finset (Fin n) → ℝ), IsPMF p → 0 < entropy p →
    (∀ i : Fin n, marginal p i < c) →
    entropy p < entropy (pushforward₂ (· ∪ ·) p p)

/-- **The Gilmer reduction, kernel-checked**: the entropic engine at threshold
`c ≤ 1` implies the union-closed conjecture with constant `c`. This is the
complete combinatorial half of Gilmer's argument (arXiv:2211.09055); the
analytic half is exactly `GilmerEngine c`. [MACHINE-VERIFIED.] -/
theorem franklWithConstant_of_gilmerEngine {c : ℝ} (hc1 : c ≤ 1)
    (hE : GilmerEngine c) : FranklWithConstant c := by
  intro n F hUC hne hne'
  classical
  rcases eq_or_lt_of_le (Finset.one_le_card.mpr hne) with h1 | h2
  · -- |F| = 1: F = {A} with A ≠ ∅; any i ∈ A has frequency 1 = |F|.
    obtain ⟨A, hA⟩ := Finset.card_eq_one.mp h1.symm
    have hAne : A ≠ (∅ : Finset (Fin n)) := by
      rintro rfl
      exact hne' hA
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hAne
    refine ⟨i, ?_⟩
    have hfreq : freq F i = 1 := by
      rw [hA]
      unfold freq
      rw [Finset.filter_singleton, if_pos hi, Finset.card_singleton]
    rw [hfreq, hA, Finset.card_singleton]
    simpa using hc1
  · -- |F| ≥ 2: uniform distribution + engine + support bound = contradiction.
    by_contra hcon
    push Not at hcon
    set p := uniformOn F with hp
    have hpmf : IsPMF p := isPMF_uniformOn hne
    have hcard0 : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
    have hent : entropy p = Real.log (F.card : ℝ) := entropy_uniformOn hne
    have hpos : 0 < entropy p := by
      rw [hent]
      apply Real.log_pos
      exact_mod_cast h2
    have hmarg : ∀ i, marginal p i < c := by
      intro i
      rw [hp, marginal_uniformOn]
      rw [show (freq F i : ℝ) * ((F.card : ℝ))⁻¹ = (freq F i : ℝ) / (F.card : ℝ) from by ring]
      rw [div_lt_iff₀ hcard0]
      exact hcon i
    have hkey := hE n p hpmf hpos hmarg
    have hsupp : ∀ C, C ∉ F → pushforward₂ (· ∪ ·) p p C = 0 := by
      intro C hC
      refine pushforward₂_eq_zero ?_ ?_ ?_ hC
      · intro A hA
        by_contra hAF
        exact hA (by rw [hp]; unfold uniformOn; rw [if_neg hAF])
      · intro B hB
        by_contra hBF
        exact hB (by rw [hp]; unfold uniformOn; rw [if_neg hBF])
      · intro A hA B hB
        exact hUC hA hB
    have hub : entropy (pushforward₂ (· ∪ ·) p p) ≤ Real.log (F.card : ℝ) :=
      entropy_le_log_card_of_support_subset (isPMF_pushforward₂ _ hpmf hpmf) hsupp
    rw [hent] at hkey
    linarith

/-! ## The golden constant and the Bernoulli shadow of the engine -/

/-- `ψ = (3 − √5)/2 ≈ 0.38197`, the optimum of the one-step Gilmer method
(D7 of PROBLEM.md). [PROVED: definition.] -/
noncomputable def psi : ℝ := (3 - Real.sqrt 5) / 2

theorem psi_pos : 0 < psi := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold psi
  nlinarith

theorem psi_lt_half : psi < 1 / 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold psi
  nlinarith

/-- The defining identity of `ψ` in union form: `2ψ − ψ² = 1 − ψ`
(equivalently `(1−ψ)² = ψ`, i.e. `p = (1−p)²`). [MACHINE-VERIFIED.] -/
theorem two_mul_psi_sub_sq : 2 * psi - psi ^ 2 = 1 - psi := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold psi
  linear_combination (-1 / 4 : ℝ) * h5

/-- At `x = ψ` the Bernoulli engine inequality is an *equality*:
`h(2ψ − ψ²) = h(ψ)`. This is where the golden constant enters the Gilmer line.
[MACHINE-VERIFIED.] -/
theorem binEntropy_at_psi : Real.binEntropy (2 * psi - psi ^ 2) = Real.binEntropy psi := by
  rw [two_mul_psi_sub_sq, Real.binEntropy_one_sub]

/-- **Bernoulli shadow of the engine**: for `x ∈ [0, ψ]`,
`h(x) ≤ h(2x − x²)`. If `A, B` are iid with iid `Bernoulli(x)` coordinates,
this is coordinate-wise `H(A) ≤ H(A ∪ B)`; the optimality of `ψ` (Pebody) says
this inequality — hence the engine — fails beyond `ψ`. Proof: split at
`2x − x² ≤ 1/2`, using monotonicity of `h` on `[0, 1/2]` and the symmetry
`h(1−t) = h(t)`; the quadratic fact `x ≤ (1−x)²` for `x ≤ ψ` is exactly
`x ≤ ψ ⇒ x² − 3x + 1 ≥ 0`. [MACHINE-VERIFIED.] -/
theorem binEntropy_le_binEntropy_union {x : ℝ} (hx0 : 0 ≤ x) (hxψ : x ≤ psi) :
    Real.binEntropy x ≤ Real.binEntropy (2 * x - x ^ 2) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hψ : x < 1 / 2 := lt_of_le_of_lt hxψ psi_lt_half
  -- the quadratic barrier: x ≤ (1−x)² for x ≤ ψ
  have hq : x ≤ (1 - x) ^ 2 := by
    have hfac : 0 ≤ ((3 - Real.sqrt 5) / 2 - x) * ((3 + Real.sqrt 5) / 2 - x) := by
      have h1 : 0 ≤ (3 - Real.sqrt 5) / 2 - x := by
        have := hxψ
        unfold psi at this
        linarith
      have h2 : 0 ≤ (3 + Real.sqrt 5) / 2 - x := by nlinarith
      exact mul_nonneg h1 h2
    nlinarith [hfac]
  have hx1 : x ≤ 1 := by linarith
  by_cases hhalf : 2 * x - x ^ 2 ≤ 2⁻¹
  · -- monotone case: x ≤ 2x − x² ≤ 1/2
    have hle : x ≤ 2 * x - x ^ 2 := by nlinarith
    exact Real.binEntropy_strictMonoOn.monotoneOn
      (Set.mem_Icc.mpr ⟨hx0, by linarith⟩)
      (Set.mem_Icc.mpr ⟨by nlinarith, hhalf⟩) hle
  · -- reflected case: h(2x − x²) = h((1−x)²) and x ≤ (1−x)² ≤ 1/2
    push Not at hhalf
    have hrw : 2 * x - x ^ 2 = 1 - (1 - x) ^ 2 := by ring
    rw [hrw, Real.binEntropy_one_sub]
    have hsq_le : (1 - x) ^ 2 ≤ 2⁻¹ := by nlinarith
    exact Real.binEntropy_strictMonoOn.monotoneOn
      (Set.mem_Icc.mpr ⟨hx0, by linarith⟩)
      (Set.mem_Icc.mpr ⟨by positivity, hsq_le⟩) hq

end UCFrankl
