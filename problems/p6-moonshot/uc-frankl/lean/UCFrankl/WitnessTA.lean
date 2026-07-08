import UCFrankl.Entropy
import UCFrankl.Frankl

/-!
# T-A formalization, layer 0: ULC weights and the Gibbs engine identity

Program UC, lens C4L4 (campaign C4, 2026-06-13). Charter: ATTACK.md T2 target
"T-A or T-G5 formalized — start". This file is the START: the definitional
layer of C2L2's witness characterization T-A (NOTEBOOK N8.2) plus its proof
engine, each piece kernel-checked. The full T-A statement
(`U_sep(μ) = H(μ) ↔ supp μ union-closed ∧ μ ULC`) additionally needs the
separable-coupling envelope `U_sep`, which is NOT yet defined here — that is
the next layer, not this one. No claim beyond the lemmas below is made.

Contents:

1. `UnionMonotoneOn`, `ULCOn` — the witness-side conditions of T-A
   (monotone-along-inclusion weights; union-log-concavity
   `w(a)·w(b) ≤ w(a∪b)²`).
2. `ulcOn_of_unionMonotoneOn` — on a union-closed family, monotone ⟹ ULC
   (one half of T-A's equivalence between its two witness descriptions).
3. `ulcOn_uniformOn` — the uniform pmf on a union-closed family is ULC (the
   witness instance that makes `c_wit ≤ c_F` in T-C).
4. `klDiv`, `entropy_eq_crossEntropy_sub_klDiv`,
   `entropy_sub_entropy_eq_inner_sub_klDiv` — the Gibbs/engine identity
   `H(ν) − H(μ) = ⟨ν−μ, −log μ⟩ − D(ν‖μ)` (N8.2's engine), finite-sum form.

## EPISTEMIC-STATUS LEDGER (program law)

* All definitions [PROVED: definitions, faithful to C2L2 LENS.md §2].
* All theorems: MACHINE-VERIFIED once `lake build` + the axiom audit pass.
* T-A itself, `U_sep`, and everything involving couplings: NOT HERE — open
  formalization work (next layer).
-/

namespace UCFrankl

open Finset

/-! ## Witness-side conditions -/

/-- `w` is monotone along inclusion on the family `F`. [PROVED: definition.] -/
def UnionMonotoneOn {n : ℕ} (F : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℝ) : Prop :=
  ∀ ⦃a⦄, a ∈ F → ∀ ⦃b⦄, b ∈ F → a ⊆ b → w a ≤ w b

/-- `w` is **union-log-concave (ULC)** on `F`: `w(a)·w(b) ≤ w(a∪b)²` for all
members. The witness condition of T-A (N8.2). [PROVED: definition.] -/
def ULCOn {n : ℕ} (F : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℝ) : Prop :=
  ∀ ⦃a⦄, a ∈ F → ∀ ⦃b⦄, b ∈ F → w a * w b ≤ w (a ∪ b) ^ 2

/-- On a union-closed family, nonnegative monotone-along-inclusion weights are
ULC — the easy half of T-A's equivalence of witness descriptions.
[MACHINE-VERIFIED.] -/
theorem ulcOn_of_unionMonotoneOn {n : ℕ} {F : Finset (Finset (Fin n))}
    {w : Finset (Fin n) → ℝ} (hUC : UnionClosed F) (hnn : ∀ a ∈ F, 0 ≤ w a)
    (hmono : UnionMonotoneOn F w) : ULCOn F w := by
  intro a ha b hb
  have hab : a ∪ b ∈ F := hUC ha hb
  have h1 : w a ≤ w (a ∪ b) := hmono ha hab Finset.subset_union_left
  have h2 : w b ≤ w (a ∪ b) := hmono hb hab Finset.subset_union_right
  have hb0 : 0 ≤ w b := hnn b hb
  have hu0 : 0 ≤ w (a ∪ b) := le_trans (hnn a ha) h1
  calc w a * w b ≤ w (a ∪ b) * w (a ∪ b) := mul_le_mul h1 h2 hb0 hu0
    _ = w (a ∪ b) ^ 2 := (sq (w (a ∪ b))).symm

/-- The uniform distribution on a union-closed family is ULC on it (it is
constant there) — the witness instance behind `c_wit ≤ c_F` in T-C.
[MACHINE-VERIFIED.] -/
theorem ulcOn_uniformOn {n : ℕ} {F : Finset (Finset (Fin n))} (hUC : UnionClosed F) :
    ULCOn F (uniformOn F) := by
  intro a ha b hb
  have hab : a ∪ b ∈ F := hUC ha hb
  unfold uniformOn
  simp only [ha, hb, hab, if_true]
  rw [sq]

/-! ## The Gibbs engine identity -/

variable {α : Type*} [Fintype α]

/-- Discrete Kullback–Leibler divergence (nats), junk-value convention
`0·log(0/p) = 0` via `log 0 = 0`. [PROVED: definition.] -/
noncomputable def klDiv (q p : α → ℝ) : ℝ := ∑ a, q a * Real.log (q a / p a)

/-- Pointwise Gibbs decomposition under absolute continuity:
`negMulLog q = q·(−log p) − q·log(q/p)`. [MACHINE-VERIFIED.] -/
lemma negMulLog_eq_mul_neg_log_sub {q p : ℝ} (h : p = 0 → q = 0) :
    Real.negMulLog q = q * (-Real.log p) - q * Real.log (q / p) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [Real.negMulLog]
  · have hp : p ≠ 0 := fun h0 => hq (h h0)
    rw [Real.log_div hq hp]
    unfold Real.negMulLog
    ring

/-- Cross-entropy decomposition: `H(ν) = ⟨ν, −log μ⟩ − D(ν‖μ)` for finitely
supported weights with `supp ν ⊆ supp μ`. [MACHINE-VERIFIED.] -/
theorem entropy_eq_crossEntropy_sub_klDiv {q p : α → ℝ}
    (hsupp : ∀ a, p a = 0 → q a = 0) :
    entropy q = (∑ a, q a * (-Real.log (p a))) - klDiv q p := by
  unfold entropy klDiv
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => negMulLog_eq_mul_neg_log_sub (hsupp a)

/-- **The T-A engine identity** (N8.2):
`H(ν) − H(μ) = ⟨ν − μ, −log μ⟩ − D(ν‖μ)` whenever `supp ν ⊆ supp μ`.
Every step of the T-A witness characterization is bookkeeping on this
identity. [MACHINE-VERIFIED.] -/
theorem entropy_sub_entropy_eq_inner_sub_klDiv {q p : α → ℝ}
    (hsupp : ∀ a, p a = 0 → q a = 0) :
    entropy q - entropy p
      = (∑ a, (q a - p a) * (-Real.log (p a))) - klDiv q p := by
  have h := entropy_eq_crossEntropy_sub_klDiv hsupp
  have hp : entropy p = ∑ a, p a * (-Real.log (p a)) := by
    unfold entropy
    exact Finset.sum_congr rfl fun a _ => by unfold Real.negMulLog; ring
  have hsplit : ∑ a, (q a - p a) * (-Real.log (p a))
      = (∑ a, q a * (-Real.log (p a))) - ∑ a, p a * (-Real.log (p a)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [h, hp, hsplit]
  ring

end UCFrankl
