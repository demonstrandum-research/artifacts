import Mathlib
import UCFrankl.Entropy

/-!
# Conditional entropy of one bit, division-free

Program UC, lens C2L4 (Lean bridge, campaign C2). This file builds the minimal
conditional-entropy layer that the Gilmer engine reduction consumes, organized
around a single division-free scalar object:

  `condBit s t = nML s + nML t − nML (s+t)`   (`nML = Real.negMulLog`)

`condBit s t` is the entropy mass contributed by splitting a cell of mass
`s + t` into sub-cells `s` and `t` — i.e. `(s+t)·h(t/(s+t))` in perspective
form (`condBit_eq`), where `h = Real.binEntropy`. Working with `condBit`
instead of conditional probabilities removes every division and every
zero-mass case split from the downstream engine proof:

* the chain rule `H(p) = H(fst-marginal p) + condH p` on `γ × Bool` becomes a
  per-cell ring identity (`entropy_eq_fstMarg_add_condH`);
* "conditioning on a coarser variable cannot decrease conditional entropy"
  becomes superadditivity of `condBit` (`sum_condBit_le`), i.e. concavity of
  the perspective of `h` — this is the only place concavity enters.

## EPISTEMIC-STATUS LEDGER (program law)

* `condBit`, `fstMarg`, `condH` — definitions [PROVED: standard objects in
  disguise; `condBit` is the perspective of binary entropy].
* `condBit_zero_zero`, `condBit_eq`, `condBit_nonneg`,
  `condBit_add_condBit_le`, `sum_condBit_le`, `isPMF_fstMarg`,
  `entropy_eq_fstMarg_add_condH`, `condH_nonneg` — MACHINE-VERIFIED
  (kernel-checked; axiom audit in `scripts/CheckAxioms.lean`).
-/

namespace UCFrankl

open Finset

/-- Entropy mass of splitting a cell of mass `s + t` into sub-cells `s`, `t`:
`condBit s t = nML s + nML t − nML (s+t)`. Division-free perspective of binary
entropy (see `condBit_eq`). [PROVED: definition.] -/
noncomputable def condBit (s t : ℝ) : ℝ :=
  Real.negMulLog s + Real.negMulLog t - Real.negMulLog (s + t)

@[simp] theorem condBit_zero_zero : condBit 0 0 = 0 := by
  simp [condBit]

/-- Perspective form: `condBit s t = (s+t) · h(t/(s+t))` for nonnegative masses
with positive total. [MACHINE-VERIFIED.] -/
theorem condBit_eq {s t : ℝ} (hst : 0 < s + t) :
    condBit s t = (s + t) * Real.binEntropy (t / (s + t)) := by
  have hne : s + t ≠ 0 := ne_of_gt hst
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have h1 : (1 : ℝ) - t / (s + t) = s / (s + t) := by field_simp; ring
  rw [h1, div_eq_mul_inv t, div_eq_mul_inv s, Real.negMulLog_mul, Real.negMulLog_mul,
    negMulLog_inv]
  unfold condBit Real.negMulLog
  field_simp
  ring

/-- `condBit` is nonnegative on nonnegative masses. [MACHINE-VERIFIED.] -/
theorem condBit_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : 0 ≤ condBit s t := by
  rcases eq_or_lt_of_le (add_nonneg hs ht) with h | h
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0, ht0]
  · rw [condBit_eq h]
    have h01 : 0 ≤ t / (s + t) := div_nonneg ht h.le
    have h11 : t / (s + t) ≤ 1 := by
      rw [div_le_one h]; linarith
    exact mul_nonneg h.le (Real.binEntropy_nonneg h01 h11)

/-- Two-point superadditivity of `condBit` (concavity of the perspective of
binary entropy). This is the "conditioning on a coarser variable cannot
decrease conditional entropy" principle in mass form. [MACHINE-VERIFIED.] -/
theorem condBit_add_condBit_le {s₁ t₁ s₂ t₂ : ℝ} (hs₁ : 0 ≤ s₁) (ht₁ : 0 ≤ t₁)
    (hs₂ : 0 ≤ s₂) (ht₂ : 0 ≤ t₂) :
    condBit s₁ t₁ + condBit s₂ t₂ ≤ condBit (s₁ + s₂) (t₁ + t₂) := by
  rcases eq_or_lt_of_le (add_nonneg hs₁ ht₁) with h₁ | h₁
  · have hs0 : s₁ = 0 := by linarith
    have ht0 : t₁ = 0 := by linarith
    simp [hs0, ht0]
  rcases eq_or_lt_of_le (add_nonneg hs₂ ht₂) with h₂ | h₂
  · have hs0 : s₂ = 0 := by linarith
    have ht0 : t₂ = 0 := by linarith
    simp [hs0, ht0]
  have hW : 0 < (s₁ + s₂) + (t₁ + t₂) := by linarith
  rw [condBit_eq h₁, condBit_eq h₂, condBit_eq hW]
  set w₁ := s₁ + t₁ with hw₁
  set w₂ := s₂ + t₂ with hw₂
  set W := (s₁ + s₂) + (t₁ + t₂) with hWdef
  have hWsum : W = w₁ + w₂ := by rw [hWdef, hw₁, hw₂]; ring
  have hWpos' : (0 : ℝ) < W := by linarith
  have hw₁0 : w₁ ≠ 0 := ne_of_gt h₁
  have hw₂0 : w₂ ≠ 0 := ne_of_gt h₂
  have hW0 : W ≠ 0 := ne_of_gt hWpos'
  have hconc := Real.strictConcave_binEntropy.concaveOn
  have hmem₁ : t₁ / w₁ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg ht₁ h₁.le
    · rw [div_le_one h₁]; linarith
  have hmem₂ : t₂ / w₂ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg ht₂ h₂.le
    · rw [div_le_one h₂]; linarith
  have ha : (0 : ℝ) ≤ w₁ / W := div_nonneg h₁.le hWpos'.le
  have hb : (0 : ℝ) ≤ w₂ / W := div_nonneg h₂.le hWpos'.le
  have hab : w₁ / W + w₂ / W = 1 := by
    field_simp
    linarith [hWsum]
  have key := hconc.2 hmem₁ hmem₂ ha hb hab
  simp only [smul_eq_mul] at key
  have harg : w₁ / W * (t₁ / w₁) + w₂ / W * (t₂ / w₂) = (t₁ + t₂) / W := by
    field_simp
  rw [harg] at key
  have hmul := mul_le_mul_of_nonneg_left key hWpos'.le
  have hexp : W * (w₁ / W * Real.binEntropy (t₁ / w₁) + w₂ / W * Real.binEntropy (t₂ / w₂))
      = w₁ * Real.binEntropy (t₁ / w₁) + w₂ * Real.binEntropy (t₂ / w₂) := by
    field_simp
  linarith [hmul, hexp]

/-- Finset superadditivity of `condBit`: merging any finite family of cells
fiberwise can only increase total conditional entropy. [MACHINE-VERIFIED.] -/
theorem sum_condBit_le {ι : Type*} (u : Finset ι) (s t : ι → ℝ)
    (hs : ∀ i ∈ u, 0 ≤ s i) (ht : ∀ i ∈ u, 0 ≤ t i) :
    ∑ i ∈ u, condBit (s i) (t i) ≤ condBit (∑ i ∈ u, s i) (∑ i ∈ u, t i) := by
  classical
  induction u using Finset.cons_induction with
  | empty => simp
  | cons a u ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Finset.sum_cons]
    have hsu : ∀ i ∈ u, 0 ≤ s i := fun i hi => hs i (Finset.mem_cons_of_mem hi)
    have htu : ∀ i ∈ u, 0 ≤ t i := fun i hi => ht i (Finset.mem_cons_of_mem hi)
    have h1 := ih hsu htu
    have h2 := condBit_add_condBit_le (hs a (Finset.mem_cons_self a u))
      (ht a (Finset.mem_cons_self a u))
      (Finset.sum_nonneg hsu) (Finset.sum_nonneg htu)
    linarith

/-! ## The product layer `γ × Bool` -/

variable {γ : Type*} [Fintype γ]

/-- First-component marginal of a distribution on `γ × Bool`.
[PROVED: definition.] -/
noncomputable def fstMarg (p : γ × Bool → ℝ) : γ → ℝ :=
  fun c => p (c, false) + p (c, true)

/-- Conditional entropy of the Bool coordinate given the `γ` coordinate, in
division-free mass form. [PROVED: definition.] -/
noncomputable def condH (p : γ × Bool → ℝ) : ℝ :=
  ∑ c, condBit (p (c, false)) (p (c, true))

/-- The marginal of a pmf is a pmf. [MACHINE-VERIFIED.] -/
theorem isPMF_fstMarg {p : γ × Bool → ℝ} (hp : IsPMF p) : IsPMF (fstMarg p) where
  nonneg c := add_nonneg (hp.nonneg _) (hp.nonneg _)
  sum_one := by
    have h := hp.sum_one
    rw [Fintype.sum_prod_type] at h
    calc ∑ c, fstMarg p c = ∑ c, ∑ b, p (c, b) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Fintype.sum_bool]
          show p (c, false) + p (c, true) = _
          ring
      _ = 1 := h

/-- **Chain rule** on `γ × Bool`: `H(p) = H(fst-marginal) + H(bit | fst)`.
With `condBit` this is a per-cell ring identity. [MACHINE-VERIFIED.] -/
theorem entropy_eq_fstMarg_add_condH (p : γ × Bool → ℝ) :
    entropy p = entropy (fstMarg p) + condH p := by
  unfold entropy condH fstMarg
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_bool]
  unfold condBit
  ring

/-- Conditional entropy of a nonnegative weight function is nonnegative.
[MACHINE-VERIFIED.] -/
theorem condH_nonneg {p : γ × Bool → ℝ} (hp : ∀ x, 0 ≤ p x) : 0 ≤ condH p :=
  Finset.sum_nonneg fun _c _ => condBit_nonneg (hp _) (hp _)

end UCFrankl
