/-
Erdős #866 — bridgehead warm-up lemmas (NEW, not in the upstream development).

Main result: `one_le_gFun` — the parity floor g_k(n) ≥ 1 for ALL k ≥ 3 and all
n (dossier PROBLEM.md §3: "g_k(n) ≥ 1 for all n ≥ 1 (all-odds example …); the
site's 'g_k ≥ 0' is the weaker version"). Upstream proves this only for k = 3
(inside `g3`) and k = 5 (`g5lower`); the general-k statement is new to the
formal development. The proof factors through a new API lemma
`HasPairwiseSums.mono` (anti-monotonicity in k), reusing upstream `g3_lower`
(the all-odds construction) for the counterexample set.
-/
import Erdos866.Upstream

/-! ## Anti-monotonicity of HasPairwiseSums in k (new API) -/

/-- If A contains the pairwise sums of k distinct integers, it contains the
pairwise sums of j ≤ k distinct integers: restrict along `Fin.castLE`. -/
lemma HasPairwiseSums.mono {A : Finset ℤ} {j k : ℕ} (hjk : j ≤ k)
    (h : HasPairwiseSums A k) : HasPairwiseSums A j := by
  obtain ⟨b, hinj, hsum⟩ := h
  refine ⟨b ∘ Fin.castLE hjk, hinj.comp (Fin.castLE_injective hjk), ?_⟩
  intro i₁ i₂ hi
  exact hsum (Fin.castLE hjk i₁) (Fin.castLE hjk i₂)
    ((Fin.castLE_lt_castLE_iff hjk).mpr hi)

/-- Positive variant of `HasPairwiseSums.mono`. -/
lemma HasPosPairwiseSums.mono {A : Finset ℤ} {j k : ℕ} (hjk : j ≤ k)
    (h : HasPosPairwiseSums A k) : HasPosPairwiseSums A j := by
  obtain ⟨b, hinj, hpos, hsum⟩ := h
  refine ⟨b ∘ Fin.castLE hjk, hinj.comp (Fin.castLE_injective hjk),
    fun i => hpos _, ?_⟩
  intro i₁ i₂ hi
  exact hsum (Fin.castLE hjk i₁) (Fin.castLE hjk i₂)
    ((Fin.castLE_lt_castLE_iff hjk).mpr hi)

/-! ## The parity floor: g_k(n) ≥ 1 for every k ≥ 3 -/

/-- **Warm-up theorem.** For every k ≥ 3 and every n, g_k(n) ≥ 1: the set of
all n odd numbers in {1,…,2n} has size n but admits no k distinct integers
with all pairwise sums in it (two of the bᵢ share a parity, so some pairwise
sum is even, while the set is all odd). Strengthens the problem page's
"g_k(N) ≥ 0" for every k, and generalizes upstream's k ∈ {3,5} lower bounds. -/
theorem one_le_gFun (k n : ℕ) (hk : 3 ≤ k) : 1 ≤ gFun k n := by
  unfold gFun
  apply le_csInf
  · -- the defining set is nonempty: m = 2n+1 is (vacuously) a member
    refine ⟨2 * n + 1, fun A hA hcard => absurd hcard (not_le.mpr ?_)⟩
    have h1 := Finset.card_le_card hA
    have h2 : (Finset.Icc (1 : ℤ) (2 * (n : ℤ))).card = 2 * n := by
      rw [Int.card_Icc]; omega
    omega
  · -- every member is ≥ 1, i.e. m = 0 fails, via the all-odds set
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exfalso
      obtain ⟨A, hAsub, hAcard, hAneg⟩ := g3_lower n
      exact hAneg (HasPairwiseSums.mono hk (hm A hAsub (by omega)))
    · exact hpos

/-- The parity floor transfers to h_k via g_k ≤ h_k. -/
theorem one_le_hFun (k n : ℕ) (hk : 3 ≤ k) : 1 ≤ hFun k n :=
  le_trans (one_le_gFun k n hk) (gFun_le_hFun k n)
