import Mathlib

/-!
# The Frankl union-closed sets conjecture: formal statement

Program UC (`problems/p6-moonshot/PROGRAM.md`), lens L5 (Lean bridgehead, T2).

## EPISTEMIC-STATUS LEDGER (program law)

* `UnionClosed`, `freq`, `FranklWithConstant`, `FranklConjecture` — definitions
  [PROVED: faithful to D1–D3 of `problems/p6-moonshot/PROBLEM.md`; the universe is
  normalized to `Fin n`, which is WLOG by relabeling — elements outside `⋃ F` have
  frequency 0 and only hurt the adversary].
* `FranklConjecture` itself — CONJECTURED (the open problem, Frankl 1979).
* `card_le_two_mul_freq_of_singleton_mem`, `frankl_of_singleton_mem` —
  MACHINE-VERIFIED below (kernel-checked; axiom audit in `scripts/CheckAxioms.lean`).
  Mathematical content is the classical singleton case of the known-true class
  catalogue (Sarvate–Renaud; see PROBLEM.md §4), reproved here from scratch.

Statement-design notes:
* The exclusion `F ≠ {∅}` is necessary: `{∅}` has no elements at all.
* `F.Nonempty` excludes the empty family (vacuous quantification trap).
* For `n = 0` every nonempty family equals `{∅}`, so the statement has no
  degenerate vacuously-false instance.
* Frequencies are stated as `c * |F| ≤ freq` over `ℝ` so that one definition
  serves every constant `c` on the Gilmer line (`0.01`, `ψ = (3-√5)/2`, …, `1/2`).

Prior art note: Hachimori–Kashiwabara (arXiv:2504.13454, 2025) formalized in
Lean 4 an *averaged* rarity statement for ideal families. The statements below
(full conjecture, constant-`c` versions, Gilmer reduction in `Gilmer.lean`) do
not overlap with that fragment.
-/

namespace UCFrankl

open Finset

/-- A finite family `F` of subsets of `Fin n` is **union-closed** if it contains
the union of any two of its members. [PROVED: definition, = D1 of PROBLEM.md.] -/
def UnionClosed {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ∪ B ∈ F

/-- `freq F i` = the number of members of `F` that contain the element `i`.
[PROVED: definition.] -/
def freq {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n) : ℕ :=
  (F.filter fun A => i ∈ A).card

/-- "The union-closed sets conjecture holds with constant `c`": every finite
union-closed family other than `{∅}` has an element in at least `c·|F|` of its
sets. [PROVED: definition, = D3 of PROBLEM.md.] -/
def FranklWithConstant (c : ℝ) : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin n))), UnionClosed F → F.Nonempty → F ≠ {∅} →
    ∃ i : Fin n, c * (F.card : ℝ) ≤ (freq F i : ℝ)

/-- **The Frankl union-closed sets conjecture** (1979): constant `1/2`.
[CONJECTURED — the open problem; this `def` is a statement, not a claim.] -/
def FranklConjecture : Prop := FranklWithConstant (1 / 2)

/-- Singleton class, counting form: if a union-closed family contains the
singleton `{i}`, then `i` lies in at least half the members. Proof: `A ↦ A ∪ {i}`
injects the non-containers into the containers (union-closure keeps it in `F`).
[MACHINE-VERIFIED: kernel-checked below.] -/
theorem card_le_two_mul_freq_of_singleton_mem {n : ℕ} {F : Finset (Finset (Fin n))}
    (hUC : UnionClosed F) {i : Fin n} (hi : ({i} : Finset (Fin n)) ∈ F) :
    F.card ≤ 2 * freq F i := by
  classical
  have hsplit : (F.filter fun A => i ∈ A).card + (F.filter fun A => ¬ i ∈ A).card = F.card :=
    Finset.card_filter_add_card_filter_not _
  have hinj : (F.filter fun A => ¬ i ∈ A).card ≤ (F.filter fun A => i ∈ A).card := by
    apply Finset.card_le_card_of_injOn (fun A => A ∪ {i})
    · intro A hA
      simp only [Finset.mem_coe, Finset.mem_filter] at hA ⊢
      exact ⟨hUC hA.1 hi, by simp⟩
    · intro A hA B hB hAB
      rw [Finset.mem_coe, Finset.mem_filter] at hA hB
      dsimp only at hAB
      have hA' : A = (A ∪ {i}).erase i := by
        rw [Finset.union_singleton, Finset.erase_insert hA.2]
      have hB' : B = (B ∪ {i}).erase i := by
        rw [Finset.union_singleton, Finset.erase_insert hB.2]
      rw [hA', hB', hAB]
  unfold freq
  omega

/-- Singleton class, frequency form: the Frankl bound `1/2` holds at any `i`
with `{i} ∈ F`. This is the classical easy known-true class (Sarvate–Renaud).
[MACHINE-VERIFIED: kernel-checked below.] -/
theorem frankl_of_singleton_mem {n : ℕ} {F : Finset (Finset (Fin n))}
    (hUC : UnionClosed F) {i : Fin n} (hi : ({i} : Finset (Fin n)) ∈ F) :
    (1 / 2 : ℝ) * (F.card : ℝ) ≤ (freq F i : ℝ) := by
  have h := card_le_two_mul_freq_of_singleton_mem hUC hi
  have h' : (F.card : ℝ) ≤ 2 * (freq F i : ℝ) := by exact_mod_cast h
  linarith

end UCFrankl
