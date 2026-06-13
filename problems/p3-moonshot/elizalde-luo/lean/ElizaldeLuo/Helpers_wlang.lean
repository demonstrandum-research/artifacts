/-
# Generic helpers for the "wlang" package (`WLang.lean`)

List-decomposition and arithmetic lemmas that do not mention the `ABC` alphabet:

* `sum_two_pow` — the geometric sum `∑_{m<n} 2^m = 2^n - 1`;
* `absorb_decomp` — a list in which every letter strictly after an occurrence of `c`
  is again `c` decomposes as `v ++ replicate k c` with `c ∉ v` (the `{A,B}^* C^*`
  normal form of bijection.md Lemma 7);
* `prefix_replicate_length_eq` — the length of the `c`-free prefix in such a
  decomposition is determined by the list (the "(m,k) is determined by σ" step of
  bijection.md Lemma 7).
-/
import Mathlib

namespace ElizaldeLuo

/-- Geometric sum: `∑_{m<n} 2^m = 2^n - 1`. -/
theorem sum_two_pow (n : ℕ) : ∑ m ∈ Finset.range n, 2 ^ m = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    have h1 : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
    rw [Finset.sum_range_succ, ih]
    omega

/-- If in `ρ` every letter strictly after an occurrence of `c` is again `c`, then
`ρ = v ++ replicate k c` for some `v` with `c ∉ v` (bijection.md Lemma 7:
`ρ ∈ {A,B}^* C^*`). -/
theorem absorb_decomp {α : Type*} {c : α} :
    ∀ ρ : List α,
      (∀ i j (hi : i < ρ.length) (hj : j < ρ.length),
        i < j → ρ[i]'hi = c → ρ[j]'hj = c) →
      ∃ v k, c ∉ v ∧ ρ = v ++ List.replicate k c := by
  intro ρ
  induction ρ with
  | nil => exact fun _ => ⟨[], 0, by simp, rfl⟩
  | cons a ρ ih =>
    intro h
    by_cases ha : a = c
    · -- the head is already `c`: everything after it is `c`, so `v = []`.
      subst ha
      refine ⟨[], ρ.length + 1, by simp, ?_⟩
      rw [List.nil_append, List.replicate_succ]
      congr 1
      apply List.eq_replicate_of_mem
      intro b hb
      obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.mp hb
      have hC := h 0 (j + 1) (by simp) (by simpa using Nat.succ_lt_succ hj)
        (Nat.succ_pos j) rfl
      rw [List.getElem_cons_succ] at hC
      rw [← hjb]
      exact hC
    · -- the head is free: recurse on the tail and prepend.
      obtain ⟨v, k, hv, hρ⟩ := ih (fun i j hi hj hij hc => by
        have := h (i + 1) (j + 1) (by simpa using Nat.succ_lt_succ hi)
          (by simpa using Nat.succ_lt_succ hj) (by omega) (by simpa using hc)
        simpa using this)
      refine ⟨a :: v, k, ?_, by simp [hρ]⟩
      simp only [List.mem_cons, not_or]
      exact ⟨fun hca => ha hca.symm, hv⟩

/-- Auxiliary strict form: a decomposition with a strictly shorter `c`-free prefix
would force a `c` inside the longer prefix. -/
private theorem no_overlap {α : Type*} {c : α} {v₁ v₂ : List α} {k₁ k₂ : ℕ}
    (h₂ : c ∉ v₂) (hlt : v₁.length < v₂.length)
    (heq : v₁ ++ List.replicate k₁ c = v₂ ++ List.replicate k₂ c) : False := by
  have hlen : v₁.length + k₁ = v₂.length + k₂ := by
    simpa using congrArg List.length heq
  have hk₁ : 0 < k₁ := by omega
  have h1 : (v₁ ++ List.replicate k₁ c)[v₁.length]? = some c := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_replicate, if_pos hk₁]
  rw [heq, List.getElem?_append_left hlt] at h1
  exact h₂ (List.mem_of_getElem? h1)

/-- In a `(c-free) ++ c^*` decomposition, the length of the `c`-free prefix is
determined by the list (bijection.md Lemma 7: "within `X₂` the pair `(m,k)` is
determined by `σ`"). -/
theorem prefix_replicate_length_eq {α : Type*} {c : α} {v₁ v₂ : List α} {k₁ k₂ : ℕ}
    (h₁ : c ∉ v₁) (h₂ : c ∉ v₂)
    (heq : v₁ ++ List.replicate k₁ c = v₂ ++ List.replicate k₂ c) :
    v₁.length = v₂.length := by
  rcases Nat.lt_trichotomy v₁.length v₂.length with h | h | h
  · exact (no_overlap h₂ h heq).elim
  · exact h
  · exact (no_overlap h₁ h heq.symm).elim

end ElizaldeLuo
