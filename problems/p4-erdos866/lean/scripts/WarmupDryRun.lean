/- DRY RUN ONLY (never part of the library): re-declares the upstream
definitions + a sorry'd g3_lower so the NEW proof scripts in Warmup.lean and
G5Small.lean can be tactic-debugged in parallel with the big Upstream build.
The real modules import the real upstream; this file is throwaway. -/
import Mathlib

open Finset

def HasPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

noncomputable def gFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPairwiseSums A k}

-- ===== revised mono lemma (Warmup.lean) =====

lemma HasPairwiseSums.mono {A : Finset ℤ} {j k : ℕ} (hjk : j ≤ k)
    (h : HasPairwiseSums A k) : HasPairwiseSums A j := by
  obtain ⟨b, hinj, hsum⟩ := h
  refine ⟨b ∘ Fin.castLE hjk, hinj.comp (Fin.castLE_injective hjk), ?_⟩
  intro i₁ i₂ hi
  exact hsum (Fin.castLE hjk i₁) (Fin.castLE hjk i₂)
    ((Fin.castLE_lt_castLE_iff hjk).mpr hi)

-- ===== revised G5Small.lean content =====

def A95 : Finset ℤ := {1, 2, 4, 5, 6, 7, 8, 9, 10}

lemma A95_mem_bounds : ∀ x ∈ A95, 1 ≤ x ∧ x ≤ 10 ∧ x ≠ 3 := by decide

lemma A95_card : A95.card = 9 := by decide

lemma A95_subset : A95 ⊆ Finset.Icc (1 : ℤ) (2 * ((5 : ℕ) : ℤ)) := by
  intro x hx
  have h := A95_mem_bounds x hx
  rw [Finset.mem_Icc]
  push_cast
  omega

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
