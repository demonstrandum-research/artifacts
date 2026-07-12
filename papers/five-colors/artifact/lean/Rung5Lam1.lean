import Maj5Base

set_option maxRecDepth 8000

namespace SMaj

/-- TARGET Λ1 (VERBATIM from synthesis.md §4). -/
lemma exists_steered_partition (d : ℕ) (hd : 3 ≤ d) :
    ∃ sizes : Multiset ℕ, sizes.card = hfun 4 d ∧ sizes.sum = d ∧
      (∀ s ∈ sizes, 0 < s ∧ s ≤ 4) ∧
      ((d = 3 ∨ d = 5) → ∀ s ∈ sizes, s ≤ 3) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hsmall : d ≤ 6
      · interval_cases d
        · exact ⟨{3}, by decide⟩
        · exact ⟨{4}, by decide⟩
        · exact ⟨{3, 2}, by decide⟩
        · exact ⟨{4, 2}, by decide⟩
      · have hd' : 3 ≤ d - 4 := by omega
        obtain ⟨sizes, hcard, hsum, hbounds, hsteer⟩ := ih (d - 4) (by omega) hd'
        refine ⟨4 ::ₘ sizes, ?_, ?_, ?_, ?_⟩
        · simp only [Multiset.card_cons, hcard, hfun,
            if_neg (show ¬d ≤ 1 by omega), if_neg (show ¬(d - 4) ≤ 1 by omega)]
          omega
        · simp [hsum]
          omega
        · simp only [Multiset.mem_cons]
          intro s hs
          rcases hs with rfl | hs
          · omega
          · exact hbounds s hs
        · intro h
          omega

end SMaj

#print axioms SMaj.exists_steered_partition
