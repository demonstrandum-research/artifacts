/-
# Helpers for the "fifo" sorry package (Fifo.lean)

Generic list-level helpers that do not depend on the definitions in `Fifo.lean`:
counts in `baseWord`, a permutation criterion for nodup lists, `getD`/append
arithmetic, and the index form `HasNesting` of "two arcs nest" together with its
equivalence to `Nonnesting` (avoidance of 1221 and 2112, per DEFINITIONS.md §3)
and its monotonicity under sublists.

Everything lives in the sub-namespace `ElizaldeLuo.FifoH` to avoid clashing with
the helper files of the other sorry packages (which import `ElizaldeLuo.Fifo`).
-/
import Mathlib
import ElizaldeLuo.Defs

namespace ElizaldeLuo

open scoped List

namespace FifoH

/-! ## Counts in `baseWord` -/

theorem count_flatMap_pair (v : ℕ) : ∀ (m s : ℕ),
    ((List.range' s m).flatMap fun u => [u, u]).count v
      = if s ≤ v ∧ v < s + m then 2 else 0
  | 0, s => by simp
  | m + 1, s => by
    have hpair : ∀ u : ℕ, ([u, u] : List ℕ).count v = if v = u then 2 else 0 := by
      intro u
      by_cases h : v = u <;> simp [h, eq_comm]
    rw [List.range'_succ, List.flatMap_cons, List.count_append, hpair,
      count_flatMap_pair v m (s + 1)]
    split_ifs <;> omega

/-- `baseWord n = [1,1,2,2,…,n,n]` has each value in `1..n` exactly twice. -/
theorem count_baseWord' (n v : ℕ) :
    (baseWord n).count v = if 1 ≤ v ∧ v ≤ n then 2 else 0 := by
  rw [baseWord, count_flatMap_pair]
  split_ifs <;> omega

theorem count_le_two_of_perm_baseWord {n : ℕ} {w : List ℕ}
    (hw : w.Perm (baseWord n)) (v : ℕ) : w.count v ≤ 2 := by
  rw [hw.count_eq, count_baseWord']
  split <;> omega

theorem count_eq_two_of_perm_baseWord {n : ℕ} {w : List ℕ}
    (hw : w.Perm (baseWord n)) {v : ℕ} (hv : v ∈ w) : w.count v = 2 := by
  have hb : v ∈ baseWord n := hw.mem_iff.mp hv
  rw [hw.count_eq, count_baseWord', if_pos (mem_baseWord.mp hb)]

/-! ## Boolean counts -/

theorem count_true_add_count_false' (s : List Bool) :
    s.count true + s.count false = s.length := by
  induction s with
  | nil => rfl
  | cons b t ih => cases b <;> simp <;> omega


/-! ## A permutation criterion for nodup lists -/

theorem perm_of_nodup_of_mem_iff {l₁ l₂ : List ℕ} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁.Perm l₂ := by
  rw [List.perm_iff_count]
  intro a
  by_cases ha : a ∈ l₁
  · rw [List.count_eq_one_of_mem h₁ ha, List.count_eq_one_of_mem h₂ ((h a).mp ha)]
  · rw [List.count_eq_zero_of_not_mem ha,
      List.count_eq_zero_of_not_mem (fun hh => ha ((h a).mpr hh))]

/-! ## A subperm bound: a word with all counts `≤ 2` has length `≤ 2·#values` -/

theorem length_le_two_mul_of_count_le_two {u L : List ℕ} (hN : L.Nodup)
    (hmem : ∀ x ∈ u, x ∈ L) (hc : ∀ v, u.count v ≤ 2) :
    u.length ≤ 2 * L.length := by
  have hsub : u <+~ L ++ L := by
    rw [List.subperm_ext_iff]
    intro x hx
    rw [List.count_append, List.count_eq_one_of_mem hN (hmem x hx)]
    have := hc x
    omega
  have := hsub.length_le
  rw [List.length_append] at this
  omega

/-! ## `getD` over append -/

theorem getD_append_left {l l' : List ℕ} {n : ℕ} (h : n < l.length) :
    (l ++ l').getD n 0 = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

theorem getD_append_right {l l' : List ℕ} {n : ℕ} (h : l.length ≤ n) :
    (l ++ l').getD n 0 = l'.getD (n - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right h]

/-! ## The index form of nesting

`HasNesting w` says there are positions `i₁ < i₂ < i₃ < i₄` carrying values
`a, b, b, a` with `a ≠ b` — i.e. two arcs of `w` nest (bijection.md §0). It is
equivalent to `¬ Nonnesting w` for arbitrary words (Lemma 0, Step 1: the
equality pattern of 1221/2112 forces exactly this index shape). -/

def HasNesting (w : List ℕ) : Prop :=
  ∃ i₁ i₂ i₃ i₄ : ℕ, i₁ < i₂ ∧ i₂ < i₃ ∧ i₃ < i₄ ∧ i₄ < w.length ∧
    w.getD i₁ 0 = w.getD i₄ 0 ∧ w.getD i₂ 0 = w.getD i₃ 0 ∧
    w.getD i₁ 0 ≠ w.getD i₂ 0

theorem length_pat1221 : pat1221.length = 4 := rfl

theorem length_pat2112 : pat2112.length = 4 := rfl

theorem not_nonnesting_of_hasNesting {w : List ℕ} (h : HasNesting w) :
    ¬ Nonnesting w := by
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h4, e14, e23, hne⟩ := h
  have h1 : i₁ < w.length := by omega
  have h2 : i₂ < w.length := by omega
  have h3 : i₃ < w.length := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h4] at e14
  rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h3] at e23
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hne
  rintro ⟨hav1, hav2⟩
  rcases Nat.lt_or_ge (w[i₁]) (w[i₂]) with hab | hab
  · -- the indices form a 1221 occurrence
    apply hav1
    refine ⟨fun r => if r.1 = 0 then ⟨i₁, h1⟩ else if r.1 = 1 then ⟨i₂, h2⟩
      else if r.1 = 2 then ⟨i₃, h3⟩ else ⟨i₄, h4⟩, ?_, ?_, ?_⟩
    · rintro ⟨r, hr⟩ ⟨s, hs⟩ hrs
      have hr4 : r < 4 := length_pat1221 ▸ hr
      have hs4 : s < 4 := length_pat1221 ▸ hs
      rw [Fin.mk_lt_mk] at hrs
      interval_cases r <;> interval_cases s <;>
        simp_all [Fin.mk_lt_mk] <;> omega
    · rintro ⟨r, hr⟩ ⟨s, hs⟩
      have hr4 : r < 4 := length_pat1221 ▸ hr
      have hs4 : s < 4 := length_pat1221 ▸ hs
      interval_cases r <;> interval_cases s <;>
        simp_all [pat1221, List.get_eq_getElem] <;> omega
    · rintro ⟨r, hr⟩ ⟨s, hs⟩
      have hr4 : r < 4 := length_pat1221 ▸ hr
      have hs4 : s < 4 := length_pat1221 ▸ hs
      interval_cases r <;> interval_cases s <;>
        simp_all [pat1221, List.get_eq_getElem] <;> omega
  · -- the indices form a 2112 occurrence
    have hab' : w[i₂] < w[i₁] := by omega
    apply hav2
    refine ⟨fun r => if r.1 = 0 then ⟨i₁, h1⟩ else if r.1 = 1 then ⟨i₂, h2⟩
      else if r.1 = 2 then ⟨i₃, h3⟩ else ⟨i₄, h4⟩, ?_, ?_, ?_⟩
    · rintro ⟨r, hr⟩ ⟨s, hs⟩ hrs
      have hr4 : r < 4 := length_pat2112 ▸ hr
      have hs4 : s < 4 := length_pat2112 ▸ hs
      rw [Fin.mk_lt_mk] at hrs
      interval_cases r <;> interval_cases s <;>
        simp_all [Fin.mk_lt_mk] <;> omega
    · rintro ⟨r, hr⟩ ⟨s, hs⟩
      have hr4 : r < 4 := length_pat2112 ▸ hr
      have hs4 : s < 4 := length_pat2112 ▸ hs
      interval_cases r <;> interval_cases s <;>
        simp_all [pat2112, List.get_eq_getElem]
    · rintro ⟨r, hr⟩ ⟨s, hs⟩
      have hr4 : r < 4 := length_pat2112 ▸ hr
      have hs4 : s < 4 := length_pat2112 ▸ hs
      interval_cases r <;> interval_cases s <;>
        simp_all [pat2112, List.get_eq_getElem] <;> omega

theorem hasNesting_of_contains_pat1221 {w : List ℕ} (h : Contains w pat1221) :
    HasNesting w := by
  obtain ⟨f, hmono, _, heq⟩ := h
  refine ⟨f ⟨0, by decide⟩, f ⟨1, by decide⟩, f ⟨2, by decide⟩, f ⟨3, by decide⟩,
    hmono _ _ (by decide), hmono _ _ (by decide), hmono _ _ (by decide),
    (f ⟨3, by decide⟩).2, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (f ⟨0, by decide⟩).2,
      List.getD_eq_getElem _ _ (f ⟨3, by decide⟩).2]
    have := (heq ⟨0, by decide⟩ ⟨3, by decide⟩).mpr (by decide)
    simpa [List.get_eq_getElem] using this
  · rw [List.getD_eq_getElem _ _ (f ⟨1, by decide⟩).2,
      List.getD_eq_getElem _ _ (f ⟨2, by decide⟩).2]
    have := (heq ⟨1, by decide⟩ ⟨2, by decide⟩).mpr (by decide)
    simpa [List.get_eq_getElem] using this
  · rw [List.getD_eq_getElem _ _ (f ⟨0, by decide⟩).2,
      List.getD_eq_getElem _ _ (f ⟨1, by decide⟩).2]
    intro hcon
    have := (heq ⟨0, by decide⟩ ⟨1, by decide⟩).mp
      (by simpa [List.get_eq_getElem] using hcon)
    revert this
    decide

theorem hasNesting_of_contains_pat2112 {w : List ℕ} (h : Contains w pat2112) :
    HasNesting w := by
  obtain ⟨f, hmono, _, heq⟩ := h
  refine ⟨f ⟨0, by decide⟩, f ⟨1, by decide⟩, f ⟨2, by decide⟩, f ⟨3, by decide⟩,
    hmono _ _ (by decide), hmono _ _ (by decide), hmono _ _ (by decide),
    (f ⟨3, by decide⟩).2, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ (f ⟨0, by decide⟩).2,
      List.getD_eq_getElem _ _ (f ⟨3, by decide⟩).2]
    have := (heq ⟨0, by decide⟩ ⟨3, by decide⟩).mpr (by decide)
    simpa [List.get_eq_getElem] using this
  · rw [List.getD_eq_getElem _ _ (f ⟨1, by decide⟩).2,
      List.getD_eq_getElem _ _ (f ⟨2, by decide⟩).2]
    have := (heq ⟨1, by decide⟩ ⟨2, by decide⟩).mpr (by decide)
    simpa [List.get_eq_getElem] using this
  · rw [List.getD_eq_getElem _ _ (f ⟨0, by decide⟩).2,
      List.getD_eq_getElem _ _ (f ⟨1, by decide⟩).2]
    intro hcon
    have := (heq ⟨0, by decide⟩ ⟨1, by decide⟩).mp
      (by simpa [List.get_eq_getElem] using hcon)
    revert this
    decide

/-- Lemma 0, Step 1 (bijection.md §1): a word is nonnesting iff no two of its
arcs nest, in index form. -/
theorem nonnesting_iff_not_hasNesting {w : List ℕ} :
    Nonnesting w ↔ ¬ HasNesting w := by
  constructor
  · exact fun hnn h => not_nonnesting_of_hasNesting h hnn
  · intro h
    exact ⟨fun hc => h (hasNesting_of_contains_pat1221 hc),
           fun hc => h (hasNesting_of_contains_pat2112 hc)⟩

/-- Nesting indices survive passing to a superword (sublist monotonicity). -/
theorem HasNesting.sublist {l w : List ℕ} (h : HasNesting l) (hsub : l <+ w) :
    HasNesting w := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_orderEmbedding_getElem?_eq.mp hsub
  obtain ⟨i₁, i₂, i₃, i₄, h12, h23, h34, h4, e14, e23, hne⟩ := h
  have key : ∀ i, i < l.length → f i < w.length ∧ w.getD (f i) 0 = l.getD i 0 := by
    intro i hi
    have hfi := hf i
    rw [List.getElem?_eq_getElem hi] at hfi
    have hlt : f i < w.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hfi
      simp at hfi
    refine ⟨hlt, ?_⟩
    rw [List.getElem?_eq_getElem hlt] at hfi
    rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    exact (Option.some_inj.mp hfi).symm
  have k1 := key i₁ (by omega)
  have k2 := key i₂ (by omega)
  have k3 := key i₃ (by omega)
  have k4 := key i₄ h4
  refine ⟨f i₁, f i₂, f i₃, f i₄, f.strictMono h12, f.strictMono h23,
    f.strictMono h34, k4.1, ?_, ?_, ?_⟩
  · rw [k1.2, k4.2]; exact e14
  · rw [k2.2, k3.2]; exact e23
  · rw [k1.2, k2.2]; exact hne

end FifoH

end ElizaldeLuo
