/-
Erdős #866 — stretch warm-up: gFun 5 5 ≥ 5 (NEW to the formal development).

The dossier (PROBLEM.md §5 row g₅) records g₅(5) ≥ 5 via the extremal set
A = {1,2,4,5,…,10} (= {1,…,10} \ {3}), verified exhaustively by the lab
(lab/data/cells/g5_n005.json: M = 9, value = 5, extremal set
[1,2,4,5,6,7,8,9,10]). Upstream formalizes only the uniform bound
`g5lower : 4 ≤ gFun 5 n` (n ≥ 3); the n = 5 spike to 5 is not formalized
anywhere. This module closes that gap.

Math content of `not_hps_A95`: A = [1,10] \ {3}, so every pairwise sum s of
five distinct integers satisfies 1 ≤ s ≤ 10 ∧ s ≠ 3; sorting the five values
(via `Finset.orderEmbOfFin` on their image) turns distinctness into a chain
c0 < c1 < c2 < c3 < c4, and the resulting linear system is infeasible (omega).
Shape of the infeasibility (machine-checked twice: omega here, and an
independent integer brute force in the hostile review): the interval
constraints 1 ≤ c0+c1 and c3+c4 ≤ 10 alone force c0 ∈ [-1,1], c1 ∈ [1,2],
c2 ∈ [2,3], c3 ∈ [3,4], c4 ∈ [4,7] — only 14 chains survive — and every one
of them contains a pair summing to the forbidden value 3.
-/
import Erdos866.Upstream

namespace Erdos866

/-- The (lab-verified) extremal set for n = 5: {1,…,10} \ {3}. -/
def A95 : Finset ℤ := {1, 2, 4, 5, 6, 7, 8, 9, 10}

lemma A95_mem_bounds : ∀ x ∈ A95, 1 ≤ x ∧ x ≤ 10 ∧ x ≠ 3 := by decide

lemma A95_card : A95.card = 9 := by decide

lemma A95_subset : A95 ⊆ Finset.Icc (1 : ℤ) (2 * ((5 : ℕ) : ℤ)) := by
  intro x hx
  have h := A95_mem_bounds x hx
  rw [Finset.mem_Icc]
  push_cast
  omega

/-- No 5 distinct integers have all 10 pairwise sums in {1,…,10} \ {3}. -/
lemma not_hps_A95 : ¬ HasPairwiseSums A95 5 := by
  rintro ⟨b, hinj, hsum⟩
  -- symmetrize the sum condition to unordered distinct index pairs
  have hsum' : ∀ u v : Fin 5, u ≠ v → b u + b v ∈ A95 := by
    intro u v huv
    rcases lt_or_gt_of_ne huv with h | h
    · exact hsum u v h
    · rw [add_comm]; exact hsum v u h
  -- sort the five values: c : Fin 5 ↪o ℤ enumerates the image in order
  have hcard : (Finset.image b Finset.univ).card = 5 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set c := (Finset.image b Finset.univ).orderEmbOfFin hcard with hc
  have hcsum : ∀ i j : Fin 5, i < j → c i + c j ∈ A95 := by
    intro i j hij
    obtain ⟨u, -, hu⟩ := Finset.mem_image.mp
      ((Finset.image b Finset.univ).orderEmbOfFin_mem hcard i)
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp
      ((Finset.image b Finset.univ).orderEmbOfFin_mem hcard j)
    have hne : u ≠ v := by
      intro h
      have : c i = c j := by rw [← hu, h, hv]
      exact absurd this (ne_of_lt (c.strictMono hij))
    rw [← hu, ← hv]
    exact hsum' u v hne
  have key : ∀ i j : Fin 5, i < j → 1 ≤ c i + c j ∧ c i + c j ≤ 10 ∧ c i + c j ≠ 3 :=
    fun i j hij => A95_mem_bounds _ (hcsum i j hij)
  have h01 := key 0 1 (by decide)
  have h02 := key 0 2 (by decide)
  have h03 := key 0 3 (by decide)
  have h04 := key 0 4 (by decide)
  have h12 := key 1 2 (by decide)
  have h13 := key 1 3 (by decide)
  have h14 := key 1 4 (by decide)
  have h23 := key 2 3 (by decide)
  have h24 := key 2 4 (by decide)
  have h34 := key 3 4 (by decide)
  have m01 : c 0 < c 1 := c.strictMono (by decide)
  have m12 : c 1 < c 2 := c.strictMono (by decide)
  have m23 : c 2 < c 3 := c.strictMono (by decide)
  have m34 : c 3 < c 4 := c.strictMono (by decide)
  omega

/-- **Stretch warm-up.** g₅(5) ≥ 5: the surplus-4 set {1,…,10} \ {3} has no
configuration. Sharpens upstream `g5lower` (4 ≤ gFun 5 n) at n = 5; matches
the lab's exhaustive value gFun 5 5 = 5. -/
theorem five_le_gFun_five_five : 5 ≤ gFun 5 5 := by
  unfold gFun
  apply le_csInf
  · refine ⟨2 * 5 + 1, fun A hA hcard => absurd hcard (not_le.mpr ?_)⟩
    have h1 := Finset.card_le_card hA
    have h2 : (Finset.Icc (1 : ℤ) (2 * ((5 : ℕ) : ℤ))).card = 10 := by
      rw [Int.card_Icc]
      omega
    omega
  · intro m hm
    by_contra hlt
    push_neg at hlt
    exact not_hps_A95 (hm A95 A95_subset (by rw [A95_card]; omega))

end Erdos866
