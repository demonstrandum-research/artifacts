import Mathlib

/-!
# The leakage scale (C6L4 layer): sub-λ mass, `ℓ_θ`, and the T-E0 statement shape

Program UC, lens C6L4 (campaign C6, 2026-07-08). Charter: "formalize
T-E0/T-E1 statements — even statements + small lemmas advance T2" over the
WitnessTA bridgehead (N5.8 pattern).

This file is the exact finite-combinatorics layer of the C6L4 leakage-scale
object `ℓ_θ(μ)` (LENS.md D-LS): the sub-λ mass `subMass`, the admissible
candidate grid, `leakScale` as an attained maximum, and the LK1/LK5 lemmas
(attainment, range, positivity floor, budget monotonicity) — all over ℚ
weights, kernel-checked, no analysis. The analytic content of T-E0
(entropy, `Λ*`, `U_sep`) is NOT formalized here; `TE0Statement` records the
faithful statement SHAPE of C5L4's T-E0/T-E4(i), parametrized by a future
separability-gain functional `Lam` (the `U_sep` layer is still open work,
exactly as WitnessTA.lean declares). No claim beyond the lemmas below.

## EPISTEMIC-STATUS LEDGER (program law)

* `subMass`, `leakCands`, `leakAdmissible`, `leakScale`, `freqOn`,
  `TE0Statement` — definitions [PROVED: definitions, faithful to C6L4
  LENS.md D-LS and C5L4 T-E0].
* All theorems: MACHINE-VERIFIED once `lake build` + the axiom audit pass.
* T-E0 itself (the truth of `TE0Statement` for the real `Λ*`): NOT claimed
  here — pencil-and-paper PROVED in C5L4, formalization open.
-/

namespace UCFrankl

open Finset

variable {α : Type*} {S : Finset α} {w : α → ℚ} {θ : ℚ}

/-- `subMass S w lam` = total `w`-mass of members of `S` with mass `< lam`
(the function `T_μ(λ)` of C6L4 D-LS). [PROVED: definition.] -/
def subMass (S : Finset α) (w : α → ℚ) (lam : ℚ) : ℚ :=
  ∑ x ∈ S.filter (fun x => w x < lam), w x

/-- Sub-λ mass is nonnegative for nonnegative weights. [MACHINE-VERIFIED.] -/
theorem subMass_nonneg (h0 : ∀ x ∈ S, 0 ≤ w x) (lam : ℚ) :
    0 ≤ subMass S w lam :=
  Finset.sum_nonneg fun x hx => h0 x (Finset.mem_filter.mp hx).1

/-- Sub-λ mass is nondecreasing in the scale (T_μ is nondecreasing).
[MACHINE-VERIFIED.] -/
theorem subMass_mono (h0 : ∀ x ∈ S, 0 ≤ w x) {l l' : ℚ} (hll : l ≤ l') :
    subMass S w l ≤ subMass S w l' := by
  unfold subMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hll⟩
  · intro x hx _
    exact h0 x (Finset.mem_filter.mp hx).1

/-- If every mass is `≥ lam`, the sub-`lam` mass vanishes. [MACHINE-VERIFIED.] -/
theorem subMass_eq_zero_of_forall_le {lam : ℚ} (h : ∀ x ∈ S, lam ≤ w x) :
    subMass S w lam = 0 := by
  have hf : S.filter (fun x => w x < lam) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx => not_lt.mpr (h x hx)
  unfold subMass
  rw [hf, Finset.sum_empty]

/-- The candidate grid: the budget `θ` together with the atom masses `≤ θ`.
`T_μ` is a step function jumping only at atom masses, so the supremum
defining `ℓ_θ` is realized on this grid (LK1). [PROVED: definition.] -/
def leakCands (S : Finset α) (w : α → ℚ) (θ : ℚ) : Finset ℚ :=
  insert θ ((S.image w).filter (fun m => m ≤ θ))

/-- The admissible candidates: positive grid scales with sub-scale mass
within budget. [PROVED: definition.] -/
def leakAdmissible (S : Finset α) (w : α → ℚ) (θ : ℚ) : Finset ℚ :=
  (leakCands S w θ).filter (fun l => 0 < l ∧ subMass S w l ≤ θ)

/-- Membership unfolding for `leakAdmissible`. [MACHINE-VERIFIED.] -/
theorem mem_leakAdmissible {l : ℚ} :
    l ∈ leakAdmissible S w θ ↔
      (l = θ ∨ (l ∈ S.image w ∧ l ≤ θ)) ∧ (0 < l ∧ subMass S w l ≤ θ) := by
  simp only [leakAdmissible, leakCands, Finset.mem_filter, Finset.mem_insert]

/-- LK1 (floor witness): `min(θ, λ_min(μ))` is always admissible.
[MACHINE-VERIFIED.] -/
theorem min_budget_minMass_mem (hS : S.Nonempty) (hpos : ∀ x ∈ S, 0 < w x)
    (hθ : 0 < θ) :
    min θ ((S.image w).min' (hS.image w)) ∈ leakAdmissible S w θ := by
  obtain ⟨x0, hx0S, hx0⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (S.image w) (hS.image w))
  have hmpos : 0 < (S.image w).min' (hS.image w) := hx0 ▸ hpos x0 hx0S
  have hle : ∀ x ∈ S, (S.image w).min' (hS.image w) ≤ w x := fun x hx =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem w hx)
  rcases le_total ((S.image w).min' (hS.image w)) θ with hmθ | hθm
  · rw [min_eq_right hmθ]
    exact mem_leakAdmissible.mpr ⟨Or.inr ⟨Finset.min'_mem _ _, hmθ⟩, hmpos, by
      rw [subMass_eq_zero_of_forall_le hle]; exact hθ.le⟩
  · rw [min_eq_left hθm]
    exact mem_leakAdmissible.mpr ⟨Or.inl rfl, hθ, by
      rw [subMass_eq_zero_of_forall_le fun x hx => hθm.trans (hle x hx)]
      exact hθ.le⟩

/-- LK1 (nonemptiness): for positive weights and a positive budget the
admissible set is nonempty — `min(θ, λ_min)` always works.
[MACHINE-VERIFIED.] -/
theorem leakAdmissible_nonempty (hpos : ∀ x ∈ S, 0 < w x) (hθ : 0 < θ) :
    (leakAdmissible S w θ).Nonempty := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact ⟨θ, mem_leakAdmissible.mpr ⟨Or.inl rfl, hθ, by simp [subMass, hθ.le]⟩⟩
  · exact ⟨_, min_budget_minMass_mem hS hpos hθ⟩

/-- The leakage scale `ℓ_θ(μ)`: the LARGEST admissible scale (an attained
maximum, LK1). [PROVED: definition, faithful to D-LS via the grid remark.] -/
def leakScale (S : Finset α) (w : α → ℚ) (θ : ℚ)
    (h : (leakAdmissible S w θ).Nonempty) : ℚ :=
  (leakAdmissible S w θ).max' h

theorem leakScale_mem (h : (leakAdmissible S w θ).Nonempty) :
    leakScale S w θ h ∈ leakAdmissible S w θ :=
  Finset.max'_mem _ h

/-- LK1 (attainment): the leakage scale itself is admissible —
`T_μ(ℓ_θ) ≤ θ`. [MACHINE-VERIFIED.] -/
theorem subMass_leakScale_le (h : (leakAdmissible S w θ).Nonempty) :
    subMass S w (leakScale S w θ h) ≤ θ :=
  (mem_leakAdmissible.mp (leakScale_mem h)).2.2

/-- LK1 (positivity): `ℓ_θ(μ) > 0`. [MACHINE-VERIFIED.] -/
theorem leakScale_pos (h : (leakAdmissible S w θ).Nonempty) :
    0 < leakScale S w θ h :=
  (mem_leakAdmissible.mp (leakScale_mem h)).2.1

/-- LK1 (range): `ℓ_θ(μ) ≤ θ`. [MACHINE-VERIFIED.] -/
theorem leakScale_le_budget (h : (leakAdmissible S w θ).Nonempty) :
    leakScale S w θ h ≤ θ := by
  apply Finset.max'_le
  intro a ha
  rcases (mem_leakAdmissible.mp ha).1 with rfl | ⟨_, haθ⟩
  · exact le_rfl
  · exact haθ

/-- LK1 (floor): `min(θ, λ_min(μ)) ≤ ℓ_θ(μ)`. [MACHINE-VERIFIED.] -/
theorem min_le_leakScale (hS : S.Nonempty) (hpos : ∀ x ∈ S, 0 < w x)
    (hθ : 0 < θ) (h : (leakAdmissible S w θ).Nonempty) :
    min θ ((S.image w).min' (hS.image w)) ≤ leakScale S w θ h :=
  Finset.le_max' _ _ (min_budget_minMass_mem hS hpos hθ)

/-- LK5 (budget monotonicity): `θ ≤ θ'` gives `ℓ_θ(μ) ≤ ℓ_{θ'}(μ)`.
The proof crosses the grid change: an admissible atom mass transfers
directly; the budget candidate `θ` transfers to the smallest atom mass in
`[θ, θ']` (whose sub-mass equals `T_μ(θ)`), or to `θ'` itself if none
exists. [MACHINE-VERIFIED.] -/
theorem leakScale_mono_budget {θ' : ℚ} (hθ : 0 < θ) (hθθ : θ ≤ θ')
    (h : (leakAdmissible S w θ).Nonempty)
    (h' : (leakAdmissible S w θ').Nonempty) :
    leakScale S w θ h ≤ leakScale S w θ' h' := by
  have ha := leakScale_mem (S := S) (w := w) (θ := θ) h
  rcases (mem_leakAdmissible.mp ha).1 with haθ | ⟨haimg, haleθ⟩
  · -- the maximum is the budget candidate `θ` itself
    have hsub : subMass S w θ ≤ θ := by
      have h2 := (mem_leakAdmissible.mp ha).2.2
      rw [haθ] at h2
      exact h2
    rw [haθ]
    rcases ((S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ')).eq_empty_or_nonempty
      with hMe | hMne
    · -- no atom mass in [θ, θ']: T_μ(θ') = T_μ(θ), so θ' is admissible
      have hfe : S.filter (fun x => w x < θ') = S.filter (fun x => w x < θ) := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hxS, hlt⟩
          refine ⟨hxS, ?_⟩
          by_contra hnl
          push_neg at hnl
          have hxM : w x ∈ (S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ') :=
            Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem w hxS, hnl, hlt.le⟩
          rw [hMe] at hxM
          exact absurd hxM (Finset.notMem_empty _)
        · rintro ⟨hxS, hlt⟩
          exact ⟨hxS, lt_of_lt_of_le hlt hθθ⟩
      have hsub' : subMass S w θ' ≤ θ' := by
        unfold subMass
        rw [hfe]
        exact hsub.trans hθθ
      have hmem : θ' ∈ leakAdmissible S w θ' :=
        mem_leakAdmissible.mpr ⟨Or.inl rfl, hθ.trans_le hθθ, hsub'⟩
      exact hθθ.trans (Finset.le_max' _ _ hmem)
    · -- smallest atom mass m₀ in [θ, θ']: T_μ(m₀) = T_μ(θ), m₀ admissible
      have hm0M := Finset.min'_mem _ hMne
      have hm0parts := Finset.mem_filter.mp hm0M
      have hm0img : ((S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ')).min' hMne
          ∈ S.image w := hm0parts.1
      have hθm0 : θ ≤ ((S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ')).min' hMne :=
        hm0parts.2.1
      have hm0θ' : ((S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ')).min' hMne ≤ θ' :=
        hm0parts.2.2
      have hfe : S.filter
            (fun x => w x < ((S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ')).min' hMne)
          = S.filter (fun x => w x < θ) := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hxS, hlt⟩
          refine ⟨hxS, ?_⟩
          by_contra hnl
          push_neg at hnl
          have hxM : w x ∈ (S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ') :=
            Finset.mem_filter.mpr
              ⟨Finset.mem_image_of_mem w hxS, hnl, hlt.le.trans hm0θ'⟩
          exact absurd hlt (not_lt.mpr (Finset.min'_le _ (w x) hxM))
        · rintro ⟨hxS, hlt⟩
          exact ⟨hxS, lt_of_lt_of_le hlt hθm0⟩
      have hsub0 : subMass S w
          (((S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ')).min' hMne) ≤ θ' := by
        unfold subMass
        rw [hfe]
        exact hsub.trans hθθ
      have hmem : ((S.image w).filter (fun m => θ ≤ m ∧ m ≤ θ')).min' hMne
          ∈ leakAdmissible S w θ' :=
        mem_leakAdmissible.mpr
          ⟨Or.inr ⟨hm0img, hm0θ'⟩, hθ.trans_le hθm0, hsub0⟩
      exact hθm0.trans (Finset.le_max' _ _ hmem)
  · -- the maximum is an atom mass ≤ θ: it transfers verbatim
    have hmem : leakScale S w θ h ∈ leakAdmissible S w θ' :=
      mem_leakAdmissible.mpr
        ⟨Or.inr ⟨haimg, haleθ.trans hθθ⟩, (mem_leakAdmissible.mp ha).2.1,
          (mem_leakAdmissible.mp ha).2.2.trans hθθ⟩
    exact Finset.le_max' _ _ hmem

/-! ## The T-E0 statement shape -/

/-- Element frequency `Pr_μ[i ∈ A]` for ℚ-weights on a set family.
[PROVED: definition.] -/
def freqOn {n : ℕ} (F : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℚ)
    (i : Fin n) : ℚ :=
  ∑ a ∈ F.filter (fun a => i ∈ a), w a

/-- The faithful statement SHAPE of C5L4's T-E0 (= T-E4(i)), parametrized
by a separability-gain functional `Lam` (bits): for every pmf with
frequencies `≤ c < cF`, vacuum `≤ 9/10`, and a scale `λ ≤ θ(Δ)` whose
sub-λ mass is within the `θ`-budget, `Lam ≥ λ³/(448 ln 2)`. The intended
`Lam` is `Λ* = U_sep − H`, whose formalization (couplings layer) is open
work — this is a STATEMENT, not a claim; T-E0 is pencil-and-paper PROVED
in C5L4. [PROVED: definition.] -/
def TE0Statement {n : ℕ}
    (Lam : Finset (Finset (Fin n)) → (Finset (Fin n) → ℚ) → ℝ)
    (cF : ℚ) : Prop :=
  ∀ (F : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℚ) (c lam : ℚ),
    c < cF →
    (∀ a ∈ F, 0 < w a) → (∀ a ∉ F, w a = 0) → (∑ a ∈ F, w a) = 1 →
    (∀ i : Fin n, freqOn F w i ≤ c) →
    w ∅ ≤ 9 / 10 →
    0 < lam → lam ≤ min ((cF - c) / 3) (1 / 20) →
    subMass F w lam ≤ min ((cF - c) / 3) (1 / 20) →
    (lam : ℝ) ^ 3 / (448 * Real.log 2) ≤ Lam F w

end UCFrankl
