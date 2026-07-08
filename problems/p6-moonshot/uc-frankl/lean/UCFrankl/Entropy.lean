import Mathlib

/-!
# Discrete Shannon entropy for finitely supported distributions

Program UC, lens L5 (Lean bridgehead, T2). Mathlib as of `v4.30.0` has
`Real.negMulLog` (with concavity), `Real.binEntropy` (with strict concavity
and monotonicity on `[0, 1/2]`), `PMF` with `PMF.uniformOfFinset`, and
measure-theoretic KL divergence with a chain rule
(`InformationTheory/KullbackLeibler/`); but it has **no Shannon entropy of a
discrete random variable / pmf** — no `H(X)`, no conditional Shannon entropy,
no Shannon chain rule, no subadditivity/submodularity (that development lives
in the PFR project, `teorth/pfr`, and has not been upstreamed; hostile-pass
correction 2026-06-13). This file builds the minimal discrete-entropy core
that Gilmer's argument scheme consumes, over bare `α → ℝ` weights to keep the
combinatorial half measure-theory-free.

Convention: entropy in **nats** (`Real.log`). Gilmer's argument is scale
invariant — every inequality it uses is homogeneous in the choice of logarithm
base — so nothing is lost against the literature's `log₂`.

## EPISTEMIC-STATUS LEDGER

* `IsPMF`, `entropy`, `uniformOn` — definitions [PROVED: standard].
* `IsPMF.le_one`, `entropy_nonneg`, `negMulLog_inv`, `isPMF_uniformOn`,
  `entropy_uniformOn` — MACHINE-VERIFIED (kernel-checked below).
* `entropy_le_log_card_of_support_subset` — MACHINE-VERIFIED (kernel-checked
  below; Jensen for `Real.negMulLog` with uniform weights). This is the exact
  upper bound Gilmer's contradiction consumes: a distribution supported on a
  family `F` has entropy at most `log |F|`.
-/

namespace UCFrankl

open Finset

variable {α : Type*} [Fintype α]

/-- `p : α → ℝ` is a probability mass function on the finite type `α`.
[PROVED: definition.] -/
structure IsPMF (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_one : ∑ a, p a = 1

/-- Shannon entropy (in nats) of a finitely supported distribution:
`H(p) = ∑ₐ −p(a)·log p(a)`. [PROVED: definition.] -/
noncomputable def entropy (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

theorem IsPMF.le_one {p : α → ℝ} (hp : IsPMF p) (a : α) : p a ≤ 1 := by
  have h := Finset.single_le_sum (f := p) (fun b _ => hp.nonneg b) (Finset.mem_univ a)
  rwa [hp.sum_one] at h

/-- Entropy of a pmf is nonnegative. [MACHINE-VERIFIED.] -/
theorem entropy_nonneg {p : α → ℝ} (hp : IsPMF p) : 0 ≤ entropy p :=
  Finset.sum_nonneg fun a _ => Real.negMulLog_nonneg (hp.nonneg a) (hp.le_one a)

/-- `−x⁻¹·log x⁻¹ = x⁻¹·log x` (also at `x = 0`, where both sides vanish).
[MACHINE-VERIFIED.] -/
theorem negMulLog_inv (x : ℝ) : Real.negMulLog x⁻¹ = x⁻¹ * Real.log x := by
  unfold Real.negMulLog
  rw [Real.log_inv]
  ring

/-- **Support bound** (the inequality Gilmer's contradiction consumes): a pmf
supported inside a finite set `S` has entropy at most `log |S|`. Proof: Jensen's
inequality for the concave `Real.negMulLog` with uniform weights `1/|S|`.
[MACHINE-VERIFIED.] -/
theorem entropy_le_log_card_of_support_subset {p : α → ℝ} (hp : IsPMF p)
    {S : Finset α} (hS : ∀ a, a ∉ S → p a = 0) :
    entropy p ≤ Real.log (S.card : ℝ) := by
  classical
  have hSne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exfalso
      have hzero : ∑ a, p a = 0 :=
        Finset.sum_eq_zero fun a _ => hS a (by simp [h])
      rw [hp.sum_one] at hzero
      norm_num at hzero
    · exact h
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  have hcard' : (S.card : ℝ) ≠ 0 := ne_of_gt hcard
  have hsum : ∑ a ∈ S, p a = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) fun a _ ha => hS a ha]
    exact hp.sum_one
  have hent : entropy p = ∑ a ∈ S, Real.negMulLog (p a) := by
    rw [entropy]
    exact (Finset.sum_subset (Finset.subset_univ S) fun a _ ha => by
      rw [hS a ha, Real.negMulLog_zero]).symm
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := S)
      (w := fun _ => ((S.card : ℝ))⁻¹) (p := p)
      (fun _ _ => inv_nonneg.mpr hcard.le)
      (by simp only [Finset.sum_const, nsmul_eq_mul]; exact mul_inv_cancel₀ hcard')
      (fun a _ => Set.mem_Ici.mpr (hp.nonneg a))
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one, negMulLog_inv] at hJ
  calc entropy p
      = (S.card : ℝ) * ((S.card : ℝ)⁻¹ * ∑ a ∈ S, Real.negMulLog (p a)) := by
        rw [hent]; field_simp
    _ ≤ (S.card : ℝ) * ((S.card : ℝ)⁻¹ * Real.log (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hJ (le_of_lt hcard)
    _ = Real.log (S.card : ℝ) := by field_simp

/-- The uniform distribution on a finite set `F`. [PROVED: definition.] -/
noncomputable def uniformOn [DecidableEq α] (F : Finset α) : α → ℝ :=
  fun a => if a ∈ F then ((F.card : ℝ))⁻¹ else 0

theorem isPMF_uniformOn [DecidableEq α] {F : Finset α} (hF : F.Nonempty) :
    IsPMF (uniformOn F) := by
  have hcard' : ((F.card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hF).ne'
  constructor
  · intro a
    unfold uniformOn
    split_ifs
    · positivity
    · exact le_rfl
  · unfold uniformOn
    rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard']

/-- `H(uniform on F) = log |F|` — the entropy of the uniform sample from a
family, the left anchor of Gilmer's contradiction. [MACHINE-VERIFIED.] -/
theorem entropy_uniformOn [DecidableEq α] {F : Finset α} (hF : F.Nonempty) :
    entropy (uniformOn F) = Real.log (F.card : ℝ) := by
  have hcard' : ((F.card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hF).ne'
  unfold entropy uniformOn
  simp_rw [apply_ite Real.negMulLog, Real.negMulLog_zero]
  rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, negMulLog_inv,
    ← mul_assoc, mul_inv_cancel₀ hcard', one_mul]

end UCFrankl
