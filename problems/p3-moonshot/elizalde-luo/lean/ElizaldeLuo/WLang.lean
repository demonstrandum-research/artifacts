/-
# The target ternary language `W n` (drafts/bijection.md §7) and its cardinality

`W n ⊆ {A,B,C}^n` is the explicit language onto which the avoiders biject; its
cardinality is `3^n - 3·2^(n-1) + 1` by a two-line disjointness count
(bijection.md, Lemma 7).

SORRY PACKAGE "wlang": `card_strings`, `compl_W`, `card_X1`, `card_X2`,
`X1_disjoint_X2`, `card_W`. This package is nearly pure `Finset.card` algebra and is
independent of all word-level combinatorics.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Helpers_wlang

namespace ElizaldeLuo

/-- The ternary alphabet `{A, B, C}` of bijection.md §7. `A` encodes the sign L
("new low"), `B` encodes the sign H ("new high"), `C` marks a structurally
forced/marker position. -/
inductive ABC : Type where
  | A : ABC
  | B : ABC
  | C : ABC
deriving DecidableEq, Repr, Fintype

/-- `|α^n| = |α|^n`. (Sorry package "wlang".) -/
theorem card_strings (α : Type) [DecidableEq α] [Fintype α] (n : ℕ) :
    (strings α n).card = Fintype.card α ^ n := by
  induction n with
  | zero => simp [strings]
  | succ n ih =>
    have hdisj : ((Finset.univ : Finset α) : Set α).PairwiseDisjoint
        fun a => (strings α n).image (a :: ·) := by
      intro a _ b _ hab
      rw [Function.onFun, Finset.disjoint_left]
      rintro l hla hlb
      obtain ⟨wa, -, rfl⟩ := Finset.mem_image.mp hla
      obtain ⟨wb, -, hwb⟩ := Finset.mem_image.mp hlb
      injection hwb with h1 _
      exact hab (h1.symm)
    rw [strings, Finset.card_biUnion hdisj]
    calc ∑ a : α, ((strings α n).image (a :: ·)).card
        = ∑ _a : α, Fintype.card α ^ n := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.card_image_of_injective _ List.cons_injective, ih]
      _ = Fintype.card α ^ (n + 1) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, pow_succ, mul_comm]

/-! ### `C`-free strings: the `{A,B}^m` building block of Lemma 7 -/

/-- Encode a `C`-free letter as a `Bool` (`A ↦ true`, `B ↦ false`). -/
def abToBool : ABC → Bool
  | ABC.A => true
  | ABC.B => false
  | ABC.C => false

/-- Decode a `Bool` to a `C`-free letter. -/
def boolToAB : Bool → ABC
  | true => ABC.A
  | false => ABC.B

/-- The `C`-free strings of length `m` (the `{A,B}^m` of bijection.md Lemma 7). -/
def stringsAB (m : ℕ) : Finset (List ABC) :=
  (strings ABC m).filter fun σ => ABC.C ∉ σ

theorem mem_stringsAB {m : ℕ} {σ : List ABC} :
    σ ∈ stringsAB m ↔ σ.length = m ∧ ABC.C ∉ σ := by
  rw [stringsAB, Finset.mem_filter, mem_strings]

/-- `|{A,B}^m| = 2^m`, via the evident bijection with `Bool^m`. -/
theorem card_stringsAB (m : ℕ) : (stringsAB m).card = 2 ^ m := by
  have h : (stringsAB m).card = (strings Bool m).card := by
    apply Finset.card_nbij' (fun σ => σ.map abToBool) (fun l => l.map boolToAB)
    · intro σ hσ
      simp only [Finset.mem_coe, mem_stringsAB] at hσ
      simp only [Finset.mem_coe, mem_strings, List.length_map]
      exact hσ.1
    · intro l hl
      simp only [Finset.mem_coe, mem_strings] at hl
      simp only [Finset.mem_coe, mem_stringsAB, List.length_map]
      refine ⟨hl, ?_⟩
      simp only [List.mem_map, not_exists, not_and]
      intro b _
      cases b <;> simp [boolToAB]
    · intro σ hσ
      simp only [Finset.mem_coe, mem_stringsAB] at hσ
      simp only [List.map_map]
      have hid : ∀ x ∈ σ, (boolToAB ∘ abToBool) x = id x := by
        intro x hx
        cases x with
        | A => rfl
        | B => rfl
        | C => exact absurd hx hσ.2
      rw [List.map_congr_left hid, List.map_id]
    · intro l _
      simp only [List.map_map]
      have hid : ∀ b ∈ l, (abToBool ∘ boolToAB) b = id b := by
        intro b _
        cases b <;> rfl
      rw [List.map_congr_left hid, List.map_id]
  rw [h, card_strings, Fintype.card_bool]

/-- Membership predicate of the language `W_n`, verbatim per bijection.md §7
(0-based positions: the draft's 1-based positions `2 ≤ r < t ≤ n` become
`1 ≤ r < t ≤ n-1`, and the draft's `σ₁` is `σ.head?`):

"**Definition.** $W_n \subseteq \{A,B,C\}^n$ is the set of strings $\sigma$ such that:
- if $\sigma$ contains no $C$, then $\sigma_1 = A$;
- if $\sigma_1 = C$, then there are positions $2 \le r < t \le n$ with $\sigma_r = C$
  and $\sigma_t \ne C$;
- (if $\sigma_1 \ne C$ and $\sigma$ contains a $C$: no condition.)" -/
def InW (σ : List ABC) : Prop :=
  (ABC.C ∉ σ → σ.head? = some ABC.A) ∧
  (σ.head? = some ABC.C →
    ∃ r t : Fin σ.length, 0 < (r : ℕ) ∧ r < t ∧ σ.get r = ABC.C ∧ σ.get t ≠ ABC.C)

instance (σ : List ABC) : Decidable (InW σ) := by
  unfold InW; infer_instance

/-- The language `W_n` as a finite set: length-`n` strings over `{A,B,C}`
satisfying `InW`. -/
def W (n : ℕ) : Finset (List ABC) :=
  (strings ABC n).filter InW

/-- First excluded family (bijection.md Lemma 7):
`X1 = B{A,B}^(n-1)`, i.e. strings starting with `B` and containing no `C`. -/
def X1 (n : ℕ) : Finset (List ABC) :=
  (strings ABC n).filter fun σ => σ.head? = some ABC.B ∧ ABC.C ∉ σ

/-- Second excluded family (bijection.md Lemma 7):
`X2 = { C v C^k : v ∈ {A,B}^m, m,k ≥ 0, 1+m+k = n }`, i.e. strings starting with `C`
in which every `C` at a position `≥ 2` (1-based) is followed only by `C`s. -/
def X2 (n : ℕ) : Finset (List ABC) :=
  (strings ABC n).filter fun σ =>
    σ.head? = some ABC.C ∧
    ∀ r t : Fin σ.length, r < t → 0 < (r : ℕ) → σ.get r = ABC.C → σ.get t = ABC.C

/-- Lemma 7 (complement description): "The complement of $W_n$ in $\{A,B,C\}^n$ is the
disjoint union of $X_1 = B\{A,B\}^{n-1}$ and
$X_2 = \{Cv C^k : v \in \{A,B\}^m, m,k≥0, 1+m+k=n\}$." (Sorry package "wlang".)

The hypothesis `1 ≤ n` matches the draft's "(n ≥ 1)": at `n = 0` the empty string is
in neither `W 0` (it has no first letter) nor `X1 0 ∪ X2 0`, so the statement would
be false there (and Lemma 7 never claims it). -/
theorem compl_W (n : ℕ) (hn : 1 ≤ n) : (strings ABC n) \ W n = X1 n ∪ X2 n := by
  ext σ
  simp only [Finset.mem_sdiff, Finset.mem_union, W, X1, X2, Finset.mem_filter,
    mem_strings]
  constructor
  · rintro ⟨hlen, hW⟩
    have hnInW : ¬ InW σ := fun h => hW ⟨hlen, h⟩
    rw [InW, not_and_or] at hnInW
    rcases hnInW with h1 | h2
    · -- `C`-free with first letter ≠ A: the string lies in `X1`
      push Not at h1
      obtain ⟨hCfree, hheadA⟩ := h1
      cases σ with
      | nil => simp at hlen; omega
      | cons a ρ =>
        left
        refine ⟨hlen, ?_, hCfree⟩
        cases a with
        | A => simp at hheadA
        | B => rfl
        | C => simp at hCfree
    · -- first letter `C`, no later `C` followed by a non-`C`: the string lies in `X2`
      push Not at h2
      obtain ⟨hheadC, hno⟩ := h2
      right
      exact ⟨hlen, hheadC, fun r t hrt hr hrC => hno r t hr hrt hrC⟩
  · rintro (⟨hlen, hheadB, hCfree⟩ | ⟨hlen, hheadC, habsorb⟩)
    · refine ⟨hlen, fun hmem => ?_⟩
      have hA := hmem.2.1 hCfree
      rw [hheadB] at hA
      simp at hA
    · refine ⟨hlen, fun hmem => ?_⟩
      obtain ⟨r, t, hr, hrt, hrC, htC⟩ := hmem.2.2 hheadC
      exact htC (habsorb r t hrt hr hrC)

/-- Structural characterization of `X2`: exactly the strings `C v C^k` with
`v` a `C`-free word and `1 + |v| + k = n`. -/
theorem mem_X2_iff {n : ℕ} {σ : List ABC} :
    σ ∈ X2 n ↔ ∃ v k, ABC.C ∉ v ∧ σ = ABC.C :: (v ++ List.replicate k ABC.C) ∧
      1 + v.length + k = n := by
  simp only [X2, Finset.mem_filter, mem_strings]
  constructor
  · rintro ⟨hlen, hheadC, habsorb⟩
    obtain ⟨ρ, rfl⟩ : ∃ ρ, σ = ABC.C :: ρ := by
      cases σ with
      | nil => simp at hheadC
      | cons a ρ =>
        simp only [List.head?_cons, Option.some.injEq] at hheadC
        exact ⟨ρ, by rw [hheadC]⟩
    obtain ⟨v, k, hv, hρ⟩ := absorb_decomp ρ (fun i j hi hj hij hC => by
      have := habsorb ⟨i + 1, by simpa using Nat.succ_lt_succ hi⟩
        ⟨j + 1, by simpa using Nat.succ_lt_succ hj⟩
        (by simpa using Nat.succ_lt_succ hij) (Nat.succ_pos i)
        (by simpa [List.get_eq_getElem] using hC)
      simpa [List.get_eq_getElem] using this)
    refine ⟨v, k, hv, by rw [hρ], ?_⟩
    subst hρ
    simp only [List.length_cons, List.length_append, List.length_replicate] at hlen
    omega
  · rintro ⟨v, k, hv, rfl, hsum⟩
    refine ⟨?_, rfl, ?_⟩
    · simp only [List.length_cons, List.length_append, List.length_replicate]
      omega
    · rintro ⟨r, hr⟩ ⟨t, ht⟩ hrt hrpos hrC
      have hrt' : r < t := hrt
      have hrpos' : 0 < r := hrpos
      obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
      simp only [List.get_eq_getElem, List.getElem_cons_succ] at hrC ⊢
      have hvi : v.length ≤ i := by
        by_contra hlt
        push Not at hlt
        rw [List.getElem_append_left hlt] at hrC
        exact hv (hrC ▸ List.getElem_mem hlt)
      have hvj : v.length ≤ j := by omega
      rw [List.getElem_append_right hvj]
      exact List.getElem_replicate _

/-- The slice of `X2` whose `C`-free middle block has length `m`:
`{ C v C^(n-1-m) : v ∈ {A,B}^m }`. -/
def X2block (n m : ℕ) : Finset (List ABC) :=
  (stringsAB m).image fun v => ABC.C :: (v ++ List.replicate (n - 1 - m) ABC.C)

theorem card_X2block (n m : ℕ) : (X2block n m).card = 2 ^ m := by
  have hinj : Function.Injective fun v : List ABC =>
      ABC.C :: (v ++ List.replicate (n - 1 - m) ABC.C) := by
    intro v₁ v₂ h
    simp only [List.cons.injEq, true_and] at h
    exact List.append_cancel_right h
  rw [X2block, Finset.card_image_of_injective _ hinj, card_stringsAB]

/-- `X2` decomposes by the length `m` of the `C`-free middle block. -/
theorem X2_eq (n : ℕ) : X2 n = (Finset.range n).biUnion (X2block n) := by
  ext σ
  rw [mem_X2_iff]
  simp only [Finset.mem_biUnion, Finset.mem_range, X2block, Finset.mem_image,
    mem_stringsAB]
  constructor
  · rintro ⟨v, k, hv, rfl, hsum⟩
    refine ⟨v.length, by omega, v, ⟨rfl, hv⟩, ?_⟩
    have hk : n - 1 - v.length = k := by omega
    rw [hk]
  · rintro ⟨m, hm, v, ⟨hvlen, hv⟩, rfl⟩
    exact ⟨v, n - 1 - m, hv, rfl, by omega⟩

/-- Distinct slices of `X2` are disjoint: the middle-block length `m` is determined
by the string (bijection.md Lemma 7: "the pair `(m,k)` is determined by `σ`"). -/
theorem X2block_disjoint (n : ℕ) {m₁ m₂ : ℕ} (hne : m₁ ≠ m₂) :
    Disjoint (X2block n m₁) (X2block n m₂) := by
  rw [Finset.disjoint_left]
  rintro σ h1 h2
  simp only [X2block, Finset.mem_image, mem_stringsAB] at h1 h2
  obtain ⟨v₁, ⟨hl₁, hv₁⟩, rfl⟩ := h1
  obtain ⟨v₂, ⟨hl₂, hv₂⟩, heq⟩ := h2
  simp only [List.cons.injEq, true_and] at heq
  have := prefix_replicate_length_eq hv₂ hv₁ heq
  omega

/-- Lemma 7: `|X1| = 2^(n-1)`. (Sorry package "wlang".) -/
theorem card_X1 (n : ℕ) (hn : 1 ≤ n) : (X1 n).card = 2 ^ (n - 1) := by
  have hX1 : X1 n = (stringsAB (n - 1)).image (ABC.B :: ·) := by
    ext σ
    simp only [X1, Finset.mem_filter, mem_strings, Finset.mem_image, mem_stringsAB]
    constructor
    · rintro ⟨hlen, hhead, hC⟩
      cases σ with
      | nil => simp at hhead
      | cons a ρ =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        refine ⟨ρ, ⟨?_, fun h => hC (List.mem_cons_of_mem _ h)⟩, rfl⟩
        simp only [List.length_cons] at hlen
        omega
    · rintro ⟨ρ, ⟨hlen, hC⟩, rfl⟩
      refine ⟨?_, rfl, ?_⟩
      · simp only [List.length_cons]
        omega
      · simpa using hC
  rw [hX1, Finset.card_image_of_injective _ List.cons_injective, card_stringsAB]

set_option linter.unusedVariables false in
/-- Lemma 7: `|X2| = ∑_{m=0}^{n-1} 2^m = 2^n - 1`. (Sorry package "wlang".) -/
theorem card_X2 (n : ℕ) (hn : 1 ≤ n) : (X2 n).card = 2 ^ n - 1 := by
  rw [X2_eq n,
    Finset.card_biUnion fun m₁ _ m₂ _ hne => X2block_disjoint n hne,
    Finset.sum_congr rfl fun m _ => card_X2block n m]
  exact sum_two_pow n

/-- Lemma 7: `X1` and `X2` are disjoint (first letter `B` vs `C`).
(Sorry package "wlang".) -/
theorem X1_disjoint_X2 (n : ℕ) : Disjoint (X1 n) (X2 n) := by
  rw [Finset.disjoint_left]
  intro σ h1 h2
  rw [X1, Finset.mem_filter] at h1
  rw [X2, Finset.mem_filter] at h2
  rw [h1.2.1] at h2
  simp at h2

/-- **Lemma 7 (count)**: `|W_n| = 3^n - 2^(n-1) - (2^n - 1) = 3^n - 3·2^(n-1) + 1`
for `n ≥ 1`. "Two-line disjointness count": `W n = strings \ (X1 ∪ X2)` with
`X1, X2` disjoint, `|X1| = 2^(n-1)`, `|X2| = 2^n - 1`, `|strings| = 3^n`.
(Sorry package "wlang" — headline.) -/
theorem card_W (n : ℕ) (hn : 1 ≤ n) :
    (W n).card = 3 ^ n - 3 * 2 ^ (n - 1) + 1 := by
  have hsub : W n ⊆ strings ABC n := Finset.filter_subset _ _
  have hABC : Fintype.card ABC = 3 := by decide
  have hstr : (strings ABC n).card = 3 ^ n := by rw [card_strings, hABC]
  have hX : (X1 n ∪ X2 n).card = 2 ^ (n - 1) + (2 ^ n - 1) := by
    rw [Finset.card_union_of_disjoint (X1_disjoint_X2 n), card_X1 n hn, card_X2 n hn]
  have hsd : (strings ABC n \ W n).card = 3 ^ n - (W n).card := by
    rw [Finset.card_sdiff_of_subset hsub, hstr]
  have hle : (W n).card ≤ 3 ^ n := hstr ▸ Finset.card_le_card hsub
  have heq : 3 ^ n - (W n).card = 2 ^ (n - 1) + (2 ^ n - 1) := by
    rw [← hsd, compl_W n hn, hX]
  have h2n : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
    ring
  have h3le : 2 ^ (n - 1) ≤ 3 ^ (n - 1) := Nat.pow_le_pow_left (by norm_num) _
  have h3eq : (3 : ℕ) ^ n = 3 * 3 ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
    ring
  have h2pos : 0 < (2 : ℕ) ^ (n - 1) := Nat.two_pow_pos _
  omega

end ElizaldeLuo
