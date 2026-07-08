/-
Campaign-3 / P1: the full g₅ port (Lemma A induction + Theorem-8 assembly).

Phase B (Lemma A, lens new-recursion.md §2): the f*-recursion replaces van
Doorn's disjoint-representation extraction (upstream `ceslemprelim`) by a
forbidden-set parameter F.  The repaired statement carries `hrange : 2 ≤ max −
min` (the C1 prose was false for singletons; see G5FStar.lean / P3 STATUS).

Phase C (assembly): the upstream `g5upper_*` case tree, written ONCE
parameterized over the constant c and a key-inequality hypothesis (Codex gate
finding 2, adopted), instantiated at the tuned fallback constant
B = 3,520,600 whose numeric lemma `key_ineq_star_tuned` is already
kernel-grade in G5FStar.lean.

Exit: `g5upper_star : ∀ n, gFun 5 n < 3520600` and
`T1TargetG5_closed_3520600 : T1TargetG5 3520600` — T1 CLOSED on the g₅ side
(34.1× below the standing Lean constant 120,000,000).

Upstream byte-pinned file untouched; reused verbatim from it:
`subsetsums_to_pairwise`, `g5special`, `exists_good_p`, `g5_from_evens_low`,
`g5_from_evens_high`, `nat_div2_cast_ge`, `HasPairwiseSums`, `gFun`.

Axioms: every theorem here closes over [propext, Classical.choice, Quot.sound]
only (audited at end of file; no sorryAx).
-/
import Erdos866.G5FStar
import Erdos866.Statements

namespace Erdos866

open Finset

/-! ## B2 — fStar algebra: unfolding, lower bound, monotonicity, root algebra -/

/-- Unfolding lemma: for k ≥ 3, `fStar (k+1)` is the recursion step. -/
lemma fStar_succ (k : ℕ) (hk : 3 ≤ k) (x φ : ℝ) :
    fStar (k + 1) x φ = φ + 1 / 2 + Real.sqrt (x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  rfl

/-- f*ₖ(x, φ) ≥ 2 for k ≥ 3, x ≥ 2, φ ≥ 0 (the vacuity guard restored by
    the repaired `hrange` hypothesis). -/
lemma fStar_ge_two (k : ℕ) (hk : 3 ≤ k) :
    ∀ x φ : ℝ, 2 ≤ x → 0 ≤ φ → 2 ≤ fStar k x φ := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro x φ hx hφ
    have e : fStar 3 x φ = φ + 1 / 2 + Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2) := rfl
    have h : (3 / 2 : ℝ) ≤ Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (φ - 1 / 2)])
    rw [e]; linarith
  | succ k hk ih =>
    intro x φ hx hφ
    rw [fStar_succ k hk]
    have hf := ih x (φ + 1) hx (by linarith)
    have h : (3 / 2 : ℝ) ≤ Real.sqrt (x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (φ - 1 / 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ x - 2) (by linarith : (0:ℝ) ≤ fStar k x (φ + 1) - 2)]
    linarith

/-- Monotonicity of f*ₖ in the range argument (fixed φ ≥ 0), 2 ≤ x ≤ y. -/
lemma fStar_mono_x (k : ℕ) (hk : 3 ≤ k) :
    ∀ x y φ : ℝ, 0 ≤ φ → 2 ≤ x → x ≤ y → fStar k x φ ≤ fStar k y φ := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro x y φ _hφ hx hxy
    have e₁ : fStar 3 x φ = φ + 1 / 2 + Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2) := rfl
    have e₂ : fStar 3 y φ = φ + 1 / 2 + Real.sqrt (y + 1 + (φ - 1 / 2) ^ 2) := rfl
    rw [e₁, e₂]
    have h := Real.sqrt_le_sqrt
      (by linarith : x + 1 + (φ - 1 / 2) ^ 2 ≤ y + 1 + (φ - 1 / 2) ^ 2)
    linarith
  | succ k hk ih =>
    intro x y φ hφ hx hxy
    rw [fStar_succ k hk, fStar_succ k hk]
    have hf₂ : 2 ≤ fStar k x (φ + 1) := fStar_ge_two k hk x (φ + 1) hx (by linarith)
    have hmono := ih x y (φ + 1) (by linarith) hx hxy
    have h1 : (0:ℝ) ≤ x * (fStar k y (φ + 1) - fStar k x (φ + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : (0:ℝ) ≤ (y - x) * fStar k y (φ + 1) :=
      mul_nonneg (by linarith) (by linarith)
    have harg : x * fStar k x (φ + 1) ≤ y * fStar k y (φ + 1) := by nlinarith [h1, h2]
    have h := Real.sqrt_le_sqrt
      (by linarith : x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2
        ≤ y * fStar k y (φ + 1) + (φ - 1 / 2) ^ 2)
    linarith

/-- Root algebra, base form: f*₃(x, φ) ≤ r ⟹ (r−1)(r−2φ) ≥ x+1.
    (Forward implication only — the unconditional iff has a lower-root
    ambiguity; Codex gate NIT 5.) -/
lemma fStar_root_base (x φ r : ℝ) (hx : 0 ≤ x) (_hφ : 0 ≤ φ)
    (h : fStar 3 x φ ≤ r) :
    x + 1 ≤ (r - 1) * (r - 2 * φ) := by
  have e : fStar 3 x φ = φ + 1 / 2 + Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2) := rfl
  rw [e] at h
  have harg : (0:ℝ) ≤ x + 1 + (φ - 1 / 2) ^ 2 := by positivity
  have hs0 : 0 ≤ Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2) := Real.sqrt_nonneg _
  have hs : Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2) ^ 2 = x + 1 + (φ - 1 / 2) ^ 2 :=
    Real.sq_sqrt harg
  have h1 : Real.sqrt (x + 1 + (φ - 1 / 2) ^ 2) ≤ r - φ - 1 / 2 := by linarith
  nlinarith [hs, hs0, h1]

/-- Root algebra, step form: f*₍ₖ₊₁₎(x, φ) ≤ r ⟹ (r−1)(r−2φ) ≥ x·f*ₖ(x, φ+1). -/
lemma fStar_root_step (k : ℕ) (hk : 3 ≤ k) (x φ r : ℝ) (hx : 2 ≤ x) (hφ : 0 ≤ φ)
    (h : fStar (k + 1) x φ ≤ r) :
    x * fStar k x (φ + 1) ≤ (r - 1) * (r - 2 * φ) := by
  rw [fStar_succ k hk] at h
  have hf : 2 ≤ fStar k x (φ + 1) := fStar_ge_two k hk x (φ + 1) hx (by linarith)
  have harg : (0:ℝ) ≤ x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2 := by
    nlinarith [sq_nonneg (φ - 1 / 2)]
  have hs0 : 0 ≤ Real.sqrt (x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2) := Real.sqrt_nonneg _
  have hs : Real.sqrt (x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2) ^ 2
      = x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2 := Real.sq_sqrt harg
  have h1 : Real.sqrt (x * fStar k x (φ + 1) + (φ - 1 / 2) ^ 2) ≤ r - φ - 1 / 2 := by
    linarith
  nlinarith [hs, hs0, h1]

/-- Two distinct even integers ≥ each other differ by ≥ 2 (own copy of
    upstream's `private even_range_ge_two`). -/
lemma even_range_ge_two' (S : Finset ℤ) (hne : S.Nonempty)
    (heven : ∀ a ∈ S, (2 : ℤ) ∣ a) (hcard : 2 ≤ S.card) :
    2 ≤ S.max' hne - S.min' hne := by
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ S, a ≠ S.min' hne := Finset.exists_mem_ne hcard _
  have h1 := heven a ha₁
  have h2 := heven _ (S.min'_mem hne)
  have h3 := S.min'_le a ha₁
  have h4 := S.le_max' a ha₁
  omega

/-! ## B1 — the φ-weighted difference pigeonhole -/

/-- Total pair count: Σ over even d ∈ [2, range] of |A₀ ∩ (A₀ − d)| counts each
    increasing pair once (upstream `ceslemgeneral_pigeonhole_strong` inner
    fact, extracted standalone). -/
private lemma total_pairs_eq (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a) :
    (∑ d ∈ Finset.Icc 2 (A₀.max' hne - A₀.min' hne),
      if 2 ∣ d then (Finset.filter (fun a => a + d ∈ A₀) A₀).card else 0)
      = (A₀.card * (A₀.card - 1)) / 2 := by
  have h1 : (∑ d ∈ Finset.Icc 2 (A₀.max' hne - A₀.min' hne), if 2 ∣ d then (Finset.filter (fun a => a + d ∈ A₀) A₀).card else 0) = Finset.card (Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀)) := by
    have h_total_pairs : Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀) = Finset.biUnion (Finset.filter (fun d => 2 ∣ d) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne))) (fun d => Finset.image (fun a => (a, a + d)) (Finset.filter (fun a => a + d ∈ A₀) A₀)) := by
      ext ⟨a, b⟩; simp [Finset.mem_biUnion, Finset.mem_image];
      constructor;
      · intro h;
        use b - a;
        exact ⟨ ⟨ ⟨ by obtain ⟨ ha, hb ⟩ := h.1; obtain ⟨ ⟨ ha, hb ⟩, hab ⟩ := h; exact by obtain ⟨ k, hk ⟩ := heven a ha; obtain ⟨ l, hl ⟩ := heven b hb; omega, by obtain ⟨ ha, hb ⟩ := h.1; exact by linarith [ Finset.le_max' _ _ ha, Finset.le_max' _ _ hb, Finset.min'_le _ _ ha, Finset.min'_le _ _ hb ] ⟩, by obtain ⟨ ha, hb ⟩ := h.1; exact by obtain ⟨ k, hk ⟩ := heven a ha; obtain ⟨ l, hl ⟩ := heven b hb; omega ⟩, ⟨ h.1.1, by simpa using h.1.2 ⟩, by ring ⟩;
      · grind;
    rw [ h_total_pairs, Finset.card_biUnion ];
    · rw [ Finset.sum_filter ] ; exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_image_of_injective ] ; aesop_cat;
    · intros d hd d' hd' hdd'; simp_all +decide [ Finset.disjoint_left ] ;
      intros; subst_vars; omega;
  have h2 : Finset.card (Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀)) = Finset.card (Finset.powersetCard 2 A₀) := by
    refine' Finset.card_bij ( fun p hp => { p.1, p.2 } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
    · exact fun a b ha hb hab => Finset.card_pair hab.ne;
    · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      intros; omega;
    · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; cases lt_trichotomy a b <;> aesop;
  rw [h1, h2, Finset.card_powersetCard, Nat.choose_two_right]

/-- The number of even integers in [2, X] is at most X/2. -/
private lemma even_divisor_count_le (X : ℤ) (hX : 2 ≤ X) :
    (((Finset.Icc (2:ℤ) X).filter (fun d => 2 ∣ d)).card : ℤ) ≤ X / 2 := by
  have himg : (Finset.Icc (2:ℤ) X).filter (fun d => 2 ∣ d)
      = Finset.image (fun j : ℤ => 2 * j) (Finset.Icc 1 (X / 2)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h2d, hdX⟩, hdvd⟩
      exact ⟨d / 2, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨j, ⟨h1j, hjX⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨j, by ring⟩⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by omega)]
  rw [Int.card_Icc]
  omega

/-- **B1 pigeonhole.** If x·M ≤ (r−1)(r−2φ) with M > 0, some *allowed* (∉ F)
    even difference m ∈ [2, x] has |U_m| ≥ M, where U_m = A₀ ∩ (A₀ − m).
    Strictly simpler than upstream `ceslemgeneral_pigeonhole_strong`: no
    disjointness halving; the forbidden F-mass (≤ φ·(r−1)) is subtracted
    instead. -/
lemma lemmaA_pigeonhole (A₀ : Finset ℤ) (hne : A₀.Nonempty) (F : Finset ℤ)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (M : ℝ) (hM : 0 < M)
    (hroot : (↑(A₀.max' hne - A₀.min' hne) : ℝ) * M ≤
      ((A₀.card : ℝ) - 1) * ((A₀.card : ℝ) - 2 * (F.card : ℝ))) :
    ∃ m : ℤ, 2 ≤ m ∧ m ≤ A₀.max' hne - A₀.min' hne ∧ (2 : ℤ) ∣ m ∧ m ∉ F ∧
      M ≤ ((A₀.filter (fun a => a + m ∈ A₀)).card : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have h_total := total_pairs_eq A₀ hne heven
  have hXdvd : (2:ℤ) ∣ (A₀.max' hne - A₀.min' hne) :=
    dvd_sub (heven _ (A₀.max'_mem hne)) (heven _ (A₀.min'_mem hne))
  have h_even_count := even_divisor_count_le (A₀.max' hne - A₀.min' hne) hrange
  -- |U_m| ≤ r − 1 for every m ≥ 2 (the max element never lies in U_m)
  have h_Um_le : ∀ m : ℤ, 2 ≤ m →
      (Finset.filter (fun a => a + m ∈ A₀) A₀).card ≤ A₀.card - 1 := by
    intro m hm
    have hsub : Finset.filter (fun a => a + m ∈ A₀) A₀ ⊆ A₀.erase (A₀.max' hne) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_erase]
      refine ⟨fun heq => ?_, ha.1⟩
      have h1 := Finset.le_max' A₀ (a + m) ha.2
      omega
    calc (Finset.filter (fun a => a + m ∈ A₀) A₀).card
        ≤ (A₀.erase (A₀.max' hne)).card := Finset.card_le_card hsub
      _ = A₀.card - 1 := Finset.card_erase_of_mem (A₀.max'_mem hne)
  set X : ℤ := A₀.max' hne - A₀.min' hne with hX_def
  set r : ℕ := A₀.card with hr_def
  set D : Finset ℤ := (Finset.Icc 2 X).filter (fun d => 2 ∣ d) with hD_def
  set Df : Finset ℤ := D.filter (fun d => d ∈ F) with hDf_def
  set Da : Finset ℤ := D.filter (fun d => d ∉ F) with hDa_def
  have hr1 : 1 ≤ r := Finset.card_pos.mpr hne
  have h2dvd : 2 ∣ r * (r - 1) := by
    rcases Nat.even_or_odd r with h | h
    · exact h.two_dvd.mul_right _
    · obtain ⟨j, hj⟩ := h
      exact Dvd.dvd.mul_left ⟨j, by omega⟩ r
  -- Σ over D form of the total
  have h_totalD : (∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card)
      = r * (r - 1) / 2 := by
    rw [hD_def, Finset.sum_filter]
    exact h_total
  -- split into forbidden / allowed parts
  have hsplit : (∑ d ∈ Df, (Finset.filter (fun a => a + d ∈ A₀) A₀).card)
      + (∑ d ∈ Da, (Finset.filter (fun a => a + d ∈ A₀) A₀).card)
      = ∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card := by
    rw [hDf_def, hDa_def]
    exact Finset.sum_filter_add_sum_filter_not D _ _
  -- forbidden part: ≤ φ·(r−1)
  have hFpart : (∑ d ∈ Df, (Finset.filter (fun a => a + d ∈ A₀) A₀).card)
      ≤ F.card * (r - 1) := by
    calc (∑ d ∈ Df, (Finset.filter (fun a => a + d ∈ A₀) A₀).card)
        ≤ ∑ _d ∈ Df, (r - 1) := by
          refine Finset.sum_le_sum fun d hd => h_Um_le d ?_
          have hd1 := (Finset.mem_filter.mp hd).1
          exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hd1).1).1
      _ = Df.card * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ F.card * (r - 1) := by
          refine Nat.mul_le_mul_right _ (Finset.card_le_card fun d hd => ?_)
          exact (Finset.mem_filter.mp hd).2
  -- real-cast facts
  have h_total_real : 2 * ((∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
      = (r : ℝ) * ((r : ℝ) - 1) := by
    have h1 : 2 * (∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card) = r * (r - 1) := by
      rw [h_totalD]; exact Nat.mul_div_cancel' h2dvd
    calc 2 * ((∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
        = ((2 * ∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ) := by
          push_cast; ring
      _ = ((r * (r - 1) : ℕ) : ℝ) := by rw [h1]
      _ = (r : ℝ) * ((r : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hr1]; norm_num
  have hsplit_real : ((∑ d ∈ Df, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
      + ((∑ d ∈ Da, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
      = ((∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hsplit
  have hF_real : ((∑ d ∈ Df, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
      ≤ (F.card : ℝ) * ((r : ℝ) - 1) := by
    calc ((∑ d ∈ Df, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
        ≤ ((F.card * (r - 1) : ℕ) : ℝ) := by exact_mod_cast hFpart
      _ = (F.card : ℝ) * ((r : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub hr1]; norm_num
  have hXpos : (0:ℝ) < (X : ℝ) := by
    have : (2:ℝ) ≤ (X : ℝ) := by exact_mod_cast hrange
    linarith
  rcases Finset.eq_empty_or_nonempty Da with hDa_empty | hDa_ne
  · -- no allowed difference at all: Σ_D ≤ φ(r−1) forces (r−1)(r−2φ) ≤ 0 < X·M
    have hDa0 : (∑ d ∈ Da, (Finset.filter (fun a => a + d ∈ A₀) A₀).card) = 0 := by
      rw [hDa_empty]; simp
    have h1 : (∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card)
        ≤ F.card * (r - 1) := by omega
    have h2 : ((∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
        ≤ (F.card : ℝ) * ((r : ℝ) - 1) := by
      calc ((∑ d ∈ D, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
          ≤ ((F.card * (r - 1) : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (F.card : ℝ) * ((r : ℝ) - 1) := by
            rw [Nat.cast_mul, Nat.cast_sub hr1]; norm_num
    nlinarith [hroot, mul_pos hXpos hM, h_total_real, h2]
  · -- allowed part is strictly below |Da|·M ≤ (X/2)·M
    have hDa_lt : ∀ d ∈ Da, ((Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℝ) < M := by
      intro d hd
      have h1 := Finset.mem_filter.mp hd
      have h2 := Finset.mem_filter.mp h1.1
      have h3 := Finset.mem_Icc.mp h2.1
      exact hcon d h3.1 h3.2 h2.2 h1.2
    have hDa_cast : ((∑ d ∈ Da, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
        = ∑ d ∈ Da, ((Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℝ) := by
      push_cast; rfl
    have hDa_sum_lt : ((∑ d ∈ Da, (Finset.filter (fun a => a + d ∈ A₀) A₀).card : ℕ) : ℝ)
        < (Da.card : ℝ) * M := by
      rw [hDa_cast]
      have h := Finset.sum_lt_sum_of_nonempty hDa_ne hDa_lt
      simpa [Finset.sum_const, nsmul_eq_mul] using h
    have hDa_card : (Da.card : ℝ) ≤ (X : ℝ) / 2 := by
      have h1 : Da.card ≤ D.card := Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : (D.card : ℤ) ≤ X / 2 := h_even_count
      have h3 : 2 * (X / 2) = X := by omega
      have h4 : ((X / 2 : ℤ) : ℝ) = (X : ℝ) / 2 := by
        have h5 := congrArg (fun z : ℤ => (z : ℝ)) h3
        push_cast at h5
        linarith
      have h6 : ((D.card : ℤ) : ℝ) ≤ ((X / 2 : ℤ) : ℝ) := by exact_mod_cast h2
      rw [h4] at h6
      have h7 : (Da.card : ℝ) ≤ (D.card : ℝ) := by exact_mod_cast h1
      push_cast at h6 ⊢
      linarith
    have hcm : (Da.card : ℝ) * M ≤ (X : ℝ) / 2 * M :=
      mul_le_mul_of_nonneg_right hDa_card (le_of_lt hM)
    -- r(r−1) < 2φ(r−1) + X·M  ⟹  (r−1)(r−2φ) < X·M, contradicting hroot
    nlinarith [hroot, h_total_real, hsplit_real, hF_real, hDa_sum_lt, hcm]

/-! ## B3 — Lemma A base case k = 3 -/

lemma lemmaA_base3 (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (F : Finset ℤ) (hF : ∀ f ∈ F, 0 < f)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : fStar 3 (↑(A₀.max' hne - A₀.min' hne)) (F.card : ℝ) ≤ (A₀.card : ℝ)) :
    HasSubsetSumsAvoiding A₀ F 3 := by
  have hX2 : (2:ℝ) ≤ (↑(A₀.max' hne - A₀.min' hne) : ℝ) := by exact_mod_cast hrange
  have hXpos : (0:ℝ) < (↑(A₀.max' hne - A₀.min' hne) : ℝ) := by linarith
  have hXne : (↑(A₀.max' hne - A₀.min' hne) : ℝ) ≠ 0 := ne_of_gt hXpos
  have hroot := fStar_root_base (↑(A₀.max' hne - A₀.min' hne)) (F.card : ℝ) (A₀.card : ℝ)
    (by linarith) (by positivity) hcard
  obtain ⟨m, hm2, hmX, hmdvd, hmF, hUM⟩ := lemmaA_pigeonhole A₀ hne F heven hrange
    ((↑(A₀.max' hne - A₀.min' hne) + 1) / ↑(A₀.max' hne - A₀.min' hne))
    (div_pos (by linarith) hXpos)
    (by
      have h : (↑(A₀.max' hne - A₀.min' hne) : ℝ)
          * ((↑(A₀.max' hne - A₀.min' hne) + 1) / ↑(A₀.max' hne - A₀.min' hne))
          = ↑(A₀.max' hne - A₀.min' hne) + 1 := by
        field_simp
      rw [h]; exact hroot)
  have hU2 : 1 < (Finset.filter (fun a => a + m ∈ A₀) A₀).card := by
    have h1 : (1:ℝ) < ((Finset.filter (fun a => a + m ∈ A₀) A₀).card : ℝ) :=
      lt_of_lt_of_le ((one_lt_div hXpos).mpr (by linarith)) hUM
    exact_mod_cast h1
  obtain ⟨u, hu, u', hu', huu'⟩ := Finset.one_lt_card.mp hU2
  -- given v < w both in U_m, the triple (w, v − w, m) works
  suffices H : ∀ v w : ℤ, v ∈ A₀ → w ∈ A₀ → v + m ∈ A₀ → w + m ∈ A₀ → v < w →
      HasSubsetSumsAvoiding A₀ F 3 by
    have h1 := Finset.mem_filter.mp hu
    have h2 := Finset.mem_filter.mp hu'
    rcases lt_or_gt_of_ne huu' with hlt | hlt
    · exact H u u' h1.1 h2.1 h1.2 h2.2 hlt
    · exact H u' u h2.1 h1.1 h2.2 h1.2 hlt
  intro v w hv hw hvm hwm hvw
  refine ⟨![w, v - w, m], ?_, ?_, ?_, ?_⟩
  · -- nonzero
    intro i hi
    fin_cases i
    · simp at hi
    · show v - w ≠ 0
      omega
    · show m ≠ 0
      omega
  · -- pairwise distinct (i, j ≥ 1)
    intro i j hi hj hij
    fin_cases i <;> fin_cases j <;> simp_all
    · show v - w ≠ m
      omega
    · show m ≠ v - w
      omega
  · -- avoid F
    intro i hi
    fin_cases i
    · simp at hi
    · show v - w ∉ F
      intro hmem
      have := hF _ hmem
      omega
    · show m ∉ F
      exact hmF
  · -- subset sums containing index 0: w, v, w + m, v + m (up to ring normal form)
    intro S hS
    fin_cases S <;> simp_all
    all_goals first
      | exact hw
      | exact hv
      | exact hwm
      | exact hvm
      | (rw [show w + (v - w + m) = v + m from by ring]; exact hvm)

/-! ## B4 — extension step (no disjointness needed: the whole point of Lemma A) -/

/-- Extension: a structure on U ⊆ A₀ avoiding `insert m F`, with U + m ⊆ A₀,
    extends by cₖ := m to a structure on A₀ avoiding F.  Mirror of upstream
    `ceslemprelim_extend` minus `disjoint_half_subset` — distinctness of the
    new element comes from m ∈ insert m F. -/
lemma lemmaA_extend (k : ℕ) (hk : 1 ≤ k)
    (A₀ U F : Finset ℤ) (m : ℤ)
    (hU_sub : U ⊆ A₀) (hm_pos : 2 ≤ m) (hmF : m ∉ F)
    (hU_shift : ∀ a ∈ U, a + m ∈ A₀)
    (hSSA : HasSubsetSumsAvoiding U (insert m F) k) :
    HasSubsetSumsAvoiding A₀ F (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨b, hb1, hb2, hb3, hb4⟩ := hSSA
  refine ⟨Fin.snoc b m, ?_, ?_, ?_, ?_⟩
  · -- nonzero
    intro i hi
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      omega
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact hb1 i (by simpa using hi)
  · -- pairwise distinct
    intro i j hi hj hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        intro he
        apply hb3 j (by simpa using hj)
        rw [← he]
        exact Finset.mem_insert_self m F
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        intro he
        apply hb3 i (by simpa using hi)
        rw [he]
        exact Finset.mem_insert_self m F
      | cast j =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hb2 i j (by simpa using hi) (by simpa using hj)
          (fun h => hij (by rw [h]))
  · -- avoid F
    intro i hi
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      exact hmF
    | cast i =>
      rw [Fin.snoc_castSucc]
      exact fun h => hb3 i (by simpa using hi) (Finset.mem_insert_of_mem h)
  · -- subset sums containing index 0
    intro S hS
    classical
    have h0ne : (0 : Fin (j + 2)) ≠ Fin.last (j + 1) := by
      simp [Fin.ext_iff]
    have h0S' : (0 : Fin (j + 1)) ∈ Finset.univ.filter (fun i : Fin (j + 1) => Fin.castSucc i ∈ S) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa using hS
    have hsum' := hb4 (Finset.univ.filter (fun i : Fin (j + 1) => Fin.castSucc i ∈ S)) h0S'
    have himg : S.erase (Fin.last (j + 1))
        = (Finset.univ.filter (fun i : Fin (j + 1) => Fin.castSucc i ∈ S)).image Fin.castSucc := by
      ext i
      simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne_last, hiS⟩
        have hval : i.val < j + 1 := by
          have h1 := i.isLt
          have h2 : i.val ≠ j + 1 := fun h => hne_last (Fin.ext h)
          omega
        have he : Fin.castSucc (⟨i.val, hval⟩ : Fin (j + 1)) = i := Fin.ext rfl
        exact ⟨⟨i.val, hval⟩, by rw [he]; exact hiS, he⟩
      · rintro ⟨i', hi', rfl⟩
        exact ⟨(Fin.castSucc_lt_last i').ne, hi'⟩
    have hinj : Set.InjOn (Fin.castSucc (n := j + 1))
        ↑(Finset.univ.filter (fun i : Fin (j + 1) => Fin.castSucc i ∈ S)) :=
      fun a _ b _ h => Fin.castSucc_injective _ h
    by_cases hlast : Fin.last (j + 1) ∈ S
    · have hsum_eq : (∑ i ∈ S, Fin.snoc b m i)
          = (∑ i ∈ Finset.univ.filter (fun i : Fin (j + 1) => Fin.castSucc i ∈ S), b i) + m := by
        rw [← Finset.add_sum_erase S (Fin.snoc b m) hlast, himg,
          Finset.sum_image hinj, Fin.snoc_last]
        rw [Finset.sum_congr rfl (fun i _ => by rw [Fin.snoc_castSucc])]
        ring
      rw [hsum_eq]
      exact hU_shift _ hsum'
    · have hS_eq : S = (Finset.univ.filter (fun i : Fin (j + 1) => Fin.castSucc i ∈ S)).image Fin.castSucc := by
        rw [← himg, Finset.erase_eq_of_notMem hlast]
      rw [hS_eq, Finset.sum_image hinj,
        Finset.sum_congr rfl (fun i _ => by rw [Fin.snoc_castSucc])]
      exact hU_sub hsum'

/-! ## Lemma A — the induction (C2-P3 sorry discharged) -/

/-- **Lemma A** (lens new-recursion.md §2, repaired statement with `hrange`;
    replaces upstream `ceslemprelim`, removing the disjoint-representation
    factor 2 at every recursion level).

    A₀ a set of even integers ≥ 2 with range x := max − min ≥ 2, F a finite
    set of POSITIVE integers, |A₀| ≥ f*ₖ(x, |F|): then A₀ has the subset-sums
    structure avoiding F. -/
theorem lemmaA (k : ℕ) (hk : 3 ≤ k) (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (F : Finset ℤ) (hF : ∀ f ∈ F, 0 < f)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : fStar k (↑(A₀.max' hne - A₀.min' hne)) (F.card : ℝ) ≤ (A₀.card : ℝ)) :
    HasSubsetSumsAvoiding A₀ F k := by
  induction k, hk using Nat.le_induction generalizing A₀ F with
  | base => exact lemmaA_base3 A₀ hne F hF heven hrange hcard
  | succ k hk ih =>
    have hX2 : (2:ℝ) ≤ (↑(A₀.max' hne - A₀.min' hne) : ℝ) := by exact_mod_cast hrange
    have hφ0 : (0:ℝ) ≤ (F.card : ℝ) := by positivity
    have hM2 : (2:ℝ) ≤ fStar k (↑(A₀.max' hne - A₀.min' hne)) ((F.card : ℝ) + 1) :=
      fStar_ge_two k hk _ _ hX2 (by linarith)
    have hroot := fStar_root_step k hk (↑(A₀.max' hne - A₀.min' hne)) (F.card : ℝ)
      (A₀.card : ℝ) hX2 hφ0 hcard
    obtain ⟨m, hm2, hmX, hmdvd, hmF, hUM⟩ := lemmaA_pigeonhole A₀ hne F heven hrange
      (fStar k (↑(A₀.max' hne - A₀.min' hne)) ((F.card : ℝ) + 1)) (by linarith) hroot
    have hU_sub : A₀.filter (fun a => a + m ∈ A₀) ⊆ A₀ := Finset.filter_subset _ _
    have hU_shift : ∀ a ∈ A₀.filter (fun a => a + m ∈ A₀), a + m ∈ A₀ :=
      fun a ha => (Finset.mem_filter.mp ha).2
    have hU_even : ∀ a ∈ A₀.filter (fun a => a + m ∈ A₀), (2:ℤ) ∣ a :=
      fun a ha => heven a (hU_sub ha)
    have hU_pos : ∀ a ∈ A₀.filter (fun a => a + m ∈ A₀), (2:ℤ) ≤ a :=
      fun a ha => hpos a (hU_sub ha)
    have hU_card2 : 2 ≤ (A₀.filter (fun a => a + m ∈ A₀)).card := by
      have h : (2:ℝ) ≤ ((A₀.filter (fun a => a + m ∈ A₀)).card : ℝ) := le_trans hM2 hUM
      exact_mod_cast h
    have hU_ne : (A₀.filter (fun a => a + m ∈ A₀)).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hU_range : 2 ≤ (A₀.filter (fun a => a + m ∈ A₀)).max' hU_ne
        - (A₀.filter (fun a => a + m ∈ A₀)).min' hU_ne :=
      even_range_ge_two' _ hU_ne hU_even hU_card2
    have hU_range_le : (A₀.filter (fun a => a + m ∈ A₀)).max' hU_ne
        - (A₀.filter (fun a => a + m ∈ A₀)).min' hU_ne
        ≤ A₀.max' hne - A₀.min' hne := by
      have h1 := Finset.max'_subset hU_ne hU_sub
      have h2 := Finset.min'_subset hU_ne hU_sub
      omega
    have hF' : ∀ f ∈ insert m F, 0 < f := by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · omega
      · exact hF f hf
    have hcard' : fStar k (↑((A₀.filter (fun a => a + m ∈ A₀)).max' hU_ne
        - (A₀.filter (fun a => a + m ∈ A₀)).min' hU_ne)) (((insert m F).card : ℕ) : ℝ)
        ≤ ((A₀.filter (fun a => a + m ∈ A₀)).card : ℝ) := by
      have hcardF' : (((insert m F).card : ℕ) : ℝ) = (F.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hmF]
        push_cast
        ring
      rw [hcardF']
      calc fStar k (↑((A₀.filter (fun a => a + m ∈ A₀)).max' hU_ne
            - (A₀.filter (fun a => a + m ∈ A₀)).min' hU_ne)) ((F.card : ℝ) + 1)
          ≤ fStar k (↑(A₀.max' hne - A₀.min' hne)) ((F.card : ℝ) + 1) := by
            apply fStar_mono_x k hk
            · linarith
            · exact_mod_cast hU_range
            · exact_mod_cast hU_range_le
        _ ≤ ((A₀.filter (fun a => a + m ∈ A₀)).card : ℝ) := hUM
    have hIH := ih (A₀.filter (fun a => a + m ∈ A₀)) hU_ne (insert m F) hF'
      hU_even hU_pos hU_range hcard'
    exact lemmaA_extend k (by omega) A₀ (A₀.filter (fun a => a + m ∈ A₀)) F m
      hU_sub hm2 hmF hU_shift hIH

/-- **Corollary of Lemma A** (φ = 0 chain) — the drop-in replacement for
    upstream `ceslemgeneral` in the g₅ proof: |A₀| ≥ f*ₖ(range, 0) forces
    k distinct integers with all pairwise sums in A₀.  (Now sorry-free; the
    b-extraction is upstream `subsetsums_to_pairwise`, reused verbatim.) -/
theorem ceslemgeneral_star (k : ℕ) (hk : 3 ≤ k) (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : fStar k (↑(A₀.max' hne - A₀.min' hne)) 0 ≤ (A₀.card : ℝ)) :
    HasPairwiseSums A₀ k := by
  have h0 : ((∅ : Finset ℤ).card : ℝ) = 0 := by simp
  have hA := lemmaA k hk A₀ hne ∅ (by simp) heven hpos hrange (by rw [h0]; exact hcard)
  exact subsetsums_to_pairwise A₀ k hk heven hA.toContaining

/-! ## Phase C — Theorem-8 assembly, parameterized over the constant

The upstream `g5upper_*` case tree, written once over a constant `c` and a
key-inequality hypothesis `hkey` (the f*-analogue of upstream `key_ineq`),
then instantiated at c = 3520599 via `key_ineq_star_tuned`.  Constant-free
upstream lemmas (`g5special`, `exists_good_p`, `g5_from_evens_low/high`,
`nat_div2_cast_ge`) are reused verbatim. -/

/-- f*-version of upstream `g5upper_case_even`. -/
lemma g5upper_case_even_star (A A₀ : Finset ℤ)
    (hA₀_sub : A₀ ⊆ A)
    (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : fStar 5 (↑(A₀.max' hne - A₀.min' hne)) 0 ≤ (A₀.card : ℝ)) :
    HasPairwiseSums A 5 := by
  obtain ⟨b, hb_inj, hb_sums⟩ := ceslemgeneral_star 5 (by omega) A₀ hne heven hpos hrange hcard
  exact ⟨b, hb_inj, fun i j hij => hA₀_sub (hb_sums i j hij)⟩

/-- Even-element count is ≥ c when |A| ≥ n + c (upstream `even_count_ge_c`,
    constant made generic). -/
lemma even_count_ge_c_star (c : ℕ) (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + c ≤ A.card) :
    c ≤ (A.filter (fun x => Even x)).card := by
  have h_odd_subset : (A.filter (fun x => ¬Even x)) ⊆ Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n) := by
    intro x hx; simp_all +decide [ Finset.subset_iff ];
    obtain ⟨ k, rfl ⟩ := hx.2; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith [ hA hx.1 ] : ( 0 : ℤ ) ≤ k ), hA hx.1 ], by linarith [ Int.toNat_of_nonneg ( by linarith [ hA hx.1 ] : ( 0 : ℤ ) ≤ k ) ] ⟩
  have h_odd_le_n : (A.filter (fun x => ¬Even x)).card ≤ n :=
    le_trans (Finset.card_le_card h_odd_subset) (Finset.card_image_le.trans (by simp))
  have h2 : (A.filter (fun x => Even x)).card + (A.filter (fun x => ¬Even x)).card = A.card :=
    Finset.card_filter_add_card_filter_not (fun x => Even x)
  omega

/-- At most |A₀| − c odd elements of [1, 2n] are missing from A (upstream
    `missing_odds_le`, constant made generic). -/
lemma missing_odds_le_star (c : ℕ) (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + c ≤ A.card)
    (heven_gt : c < (A.filter (fun x => Even x)).card) :
    ((Icc (1:ℤ) (2*↑n)).filter (fun x => ¬Even x) \ A).card
      ≤ (A.filter (fun x => Even x)).card - c := by
  rw [ Finset.card_sdiff ];
  rw [ Finset.inter_comm ];
  rw [ show { x ∈ Icc 1 ( 2 * ( n : ℤ ) ) | ¬Even x } ∩ A = A.filter ( fun x => ¬Even x ) from ?_ ];
  · have h_odd_count : (Finset.filter (fun x => ¬Even x) (Finset.Icc (1:ℤ) (2 * n))).card = n := by
      rw [ show ( Finset.filter ( fun x : ℤ => ¬Even x ) ( Finset.Icc 1 ( 2 * n ) ) ) = Finset.image ( fun k : ℕ => 2 * k + 1 : ℕ → ℤ ) ( Finset.range n ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      apply Finset.ext
      intro x
      simp [Finset.mem_image, Finset.mem_filter];
      exact ⟨ fun hx => by obtain ⟨ k, rfl ⟩ := hx.2; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : ( 0 : ℤ ) ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : ( 0 : ℤ ) ≤ k ) ] ⟩, by rintro ⟨ k, hk, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩ ⟩;
    have h_card_filter : (A.filter (fun x => Even x)).card + (A.filter (fun x => ¬Even x)).card = A.card := by
      rw [ Finset.card_filter_add_card_filter_not ];
    omega;
  · grind

/-- The all-odds case t = 0 (upstream `g5upper_all_odds`, constant generic):
    every odd of [1, 2n] is present, use upstream `g5special`. -/
lemma g5upper_all_odds_star (c : ℕ) (hc : 7 ≤ c) (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + c ≤ A.card)
    (_hn : c ≤ n)
    (ht0 : (A.filter (fun x => Even x)).card = c) :
    HasPairwiseSums A 5 := by
  have hA_odd_card : (A.filter (fun x => ¬Even x)).card = n := by
    have hA_odd_card : (A.filter (fun x => ¬Even x)).card + (A.filter (fun x => Even x)).card = A.card := by
      rw [ add_comm, Finset.card_filter_add_card_filter_not ];
    have hA_odd_card : (A.filter (fun x => ¬Even x)).card ≤ n := by
      have hA_odd_card : (A.filter (fun x => ¬Even x)).card ≤ Finset.card (Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n)) := by
        refine Finset.card_le_card ?_;
        intro x hx; have := hA ( Finset.mem_filter.mp hx |>.1 ) ; simp_all +decide [ parity_simps ] ;
        exact hx.2.elim fun k hk => ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩;
      exact hA_odd_card.trans ( Finset.card_image_le.trans ( by simp ) );
    grind;
  convert g5special n A hA _ _;
  · have hA_odd_subset : A.filter (fun x => ¬Even x) = Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n) := by
      refine' Finset.eq_of_subset_of_card_le _ _;
      · intro x hx; have := hA ( Finset.mem_filter.mp hx |>.1 ) ; simp_all +decide [ parity_simps ] ;
        rcases hx.2 with ⟨ k, rfl ⟩ ; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩ ;
      · grind;
    simp_all +decide [ Finset.ext_iff ];
    exact fun x hx₁ hx₂ hx₃ => by obtain ⟨ k, hk₁, rfl ⟩ := Int.odd_iff.mpr hx₃; exact hA_odd_subset _ |>.2 ⟨ k.natAbs, by linarith [ abs_of_nonneg ( by linarith : 0 ≤ k ) ], by simp +decide [ abs_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩ |>.1;
  · omega

/-- Concentrated edge subcase (upstream `g5upper_conc_edge`, f*-version):
    ≥ t/2 + c/2 − 2 evens within a window of length 6t force the structure. -/
lemma g5upper_conc_edge_star (c : ℕ) (hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + (c : ℝ) / 2 - 2)
    (A : Finset ℤ)
    (t : ℕ) (ht : 1 ≤ t)
    (E : Finset ℤ) (hE_sub : E ⊆ A)
    (hE_even : ∀ x ∈ E, 2 ∣ x) (hE_pos : ∀ x ∈ E, (2 : ℤ) ≤ x)
    (hE_ne : E.Nonempty)
    (hE_spread : 2 ≤ E.max' hE_ne - E.min' hE_ne)
    (hE_spread_bound : E.max' hE_ne - E.min' hE_ne ≤ 6 * (↑t : ℤ))
    (hE_card : (t : ℝ) / 2 + (c : ℝ) / 2 - 2 ≤ ↑E.card) :
    HasPairwiseSums A 5 := by
  apply g5upper_case_even_star A E hE_sub hE_ne hE_even hE_pos hE_spread
  have ht1 : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h1 : fStar 5 (↑(E.max' hE_ne - E.min' hE_ne)) 0 ≤ fStar 5 (6 * (t:ℝ)) 0 := by
    apply fStar_mono_x 5 (by omega)
    · exact le_rfl
    · exact_mod_cast hE_spread
    · exact_mod_cast hE_spread_bound
  have h2 : fStar 5 (6 * (t:ℝ)) 0 < 6 * (t:ℝ) / 12 + (c : ℝ) / 2 - 2 :=
    hkey _ (by linarith)
  linarith

/-- Concentrated subcase of the hard case (upstream `g5upper_hard_concentrated`,
    constant generic; pigeonhole arithmetic shifted by c = B − 1). -/
lemma g5upper_hard_concentrated_star (c : ℕ) (hc : 7 ≤ c)
    (hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + (c : ℝ) / 2 - 2)
    (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (t : ℕ) (ht : 1 ≤ t)
    (A₀ : Finset ℤ) (hA₀_def : A₀ = A.filter (fun x => Even x))
    (ht_card : t + c ≤ A₀.card)
    (A_mid : Finset ℤ)
    (hA_mid_def : A_mid = A₀.filter (fun x => 6 * (↑t : ℤ) + 2 ≤ x ∧ x ≤ 2 * ↑n - 6 * ↑t - 2))
    (hmid : A_mid.card < 5) :
    HasPairwiseSums A 5 := by
  set E_low := A₀.filter (fun x => x < 6 * (↑t : ℤ) + 2) with hE_low_def
  set E_high := A₀.filter (fun x => 2 * (↑n : ℤ) - 6 * ↑t - 2 < x) with hE_high_def
  have h_count : A₀.card ≤ E_low.card + A_mid.card + E_high.card := by
    have h_union : A₀ = E_low ∪ A_mid ∪ E_high := by
      grind;
    grind
  have h_sum : t + c - 4 ≤ E_low.card + E_high.card := by omega
  by_cases hlow : (t + c - 3) / 2 ≤ E_low.card
  · have hE_sub : E_low ⊆ A := (Finset.filter_subset _ _).trans (hA₀_def ▸ Finset.filter_subset _ _)
    have hE_even : ∀ x ∈ E_low, 2 ∣ x := by
      intro x hx
      have hx' := hA₀_def ▸ Finset.filter_subset _ _ hx
      exact (Finset.mem_filter.mp hx').2.two_dvd
    have hE_pos : ∀ x ∈ E_low, (2 : ℤ) ≤ x := by
      intro x hx
      have h1 := (Finset.mem_Icc.mp (hA (hE_sub hx))).1
      obtain ⟨k, rfl⟩ := hE_even x hx
      omega
    have hE_ne : E_low.Nonempty := Finset.card_pos.mp (by omega)
    have hE_spread : 2 ≤ E_low.max' hE_ne - E_low.min' hE_ne := by
      by_contra h
      push_neg at h
      have hall : ∀ x ∈ E_low, x = E_low.min' hE_ne := by
        intro x hx
        have h1 := Finset.min'_le E_low x hx
        have h2 := Finset.le_max' E_low x hx
        obtain ⟨k, hk⟩ := hE_even x hx
        obtain ⟨m, hm⟩ := hE_even _ (Finset.min'_mem _ _)
        omega
      have : E_low.card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy => by rw [hall x hx, hall y hy])
      omega
    have hE_spread_bound : E_low.max' hE_ne - E_low.min' hE_ne ≤ 6 * (↑t : ℤ) := by
      have hmax : E_low.max' hE_ne ≤ 6 * (↑t : ℤ) := by
        have hm := (Finset.mem_filter.mp (Finset.max'_mem E_low hE_ne)).2
        obtain ⟨k, hk⟩ := hE_even _ (Finset.max'_mem _ _)
        omega
      linarith [hE_pos (E_low.min' hE_ne) (Finset.min'_mem E_low hE_ne)]
    have hE_card : (t : ℝ) / 2 + (c : ℝ) / 2 - 2 ≤ ↑E_low.card := by
      have h1 : (((t + c - 3) / 2 : ℕ) : ℝ) ≤ (E_low.card : ℝ) := by exact_mod_cast hlow
      have h2 := nat_div2_cast_ge (t + c - 3)
      have h3 : ((t + c - 3 : ℕ) : ℝ) = (t : ℝ) + (c : ℝ) - 3 := by
        have h4 : (3:ℕ) ≤ t + c := by omega
        rw [Nat.cast_sub h4]
        push_cast
        ring
      rw [h3] at h2
      linarith
    exact g5upper_conc_edge_star c hkey A t ht E_low hE_sub hE_even hE_pos hE_ne hE_spread hE_spread_bound hE_card
  · push_neg at hlow
    have hhigh : (t + c - 3) / 2 ≤ E_high.card := by omega
    have hE_sub : E_high ⊆ A := (Finset.filter_subset _ _).trans (hA₀_def ▸ Finset.filter_subset _ _)
    have hE_even : ∀ x ∈ E_high, 2 ∣ x := by
      intro x hx
      have hx' := hA₀_def ▸ Finset.filter_subset _ _ hx
      exact (Finset.mem_filter.mp hx').2.two_dvd
    have hE_pos : ∀ x ∈ E_high, (2 : ℤ) ≤ x := by
      intro x hx
      have h1 := (Finset.mem_Icc.mp (hA (hE_sub hx))).1
      obtain ⟨k, rfl⟩ := hE_even x hx
      omega
    have hE_ne : E_high.Nonempty := Finset.card_pos.mp (by omega)
    have hE_spread : 2 ≤ E_high.max' hE_ne - E_high.min' hE_ne := by
      by_contra h
      push_neg at h
      have hall : ∀ x ∈ E_high, x = E_high.min' hE_ne := by
        intro x hx
        have h1 := Finset.min'_le E_high x hx
        have h2 := Finset.le_max' E_high x hx
        obtain ⟨k, hk⟩ := hE_even x hx
        obtain ⟨m, hm⟩ := hE_even _ (Finset.min'_mem _ _)
        omega
      have : E_high.card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy => by rw [hall x hx, hall y hy])
      omega
    have hE_spread_bound : E_high.max' hE_ne - E_high.min' hE_ne ≤ 6 * (↑t : ℤ) := by
      have hmax : E_high.max' hE_ne ≤ 2 * (↑n : ℤ) :=
        (Finset.mem_Icc.mp (hA (hE_sub (Finset.max'_mem _ _)))).2
      have hmin : 2 * (↑n : ℤ) - 6 * ↑t ≤ E_high.min' hE_ne := by
        have hm := (Finset.mem_filter.mp (Finset.min'_mem E_high hE_ne)).2
        obtain ⟨k, hk⟩ := hE_even _ (Finset.min'_mem _ _)
        omega
      linarith
    have hE_card : (t : ℝ) / 2 + (c : ℝ) / 2 - 2 ≤ ↑E_high.card := by
      have h1 : (((t + c - 3) / 2 : ℕ) : ℝ) ≤ (E_high.card : ℝ) := by exact_mod_cast hhigh
      have h2 := nat_div2_cast_ge (t + c - 3)
      have h3 : ((t + c - 3 : ℕ) : ℝ) = (t : ℝ) + (c : ℝ) - 3 := by
        have h4 : (3:ℕ) ≤ t + c := by omega
        rw [Nat.cast_sub h4]
        push_cast
        ring
      rw [h3] at h2
      linarith
    exact g5upper_conc_edge_star c hkey A t ht E_high hE_sub hE_even hE_pos hE_ne hE_spread hE_spread_bound hE_card

/-- The hard case: t ≥ 1 extra evens beyond c (upstream `g5upper_hard_case`,
    constant generic; reuses the constant-free pair constructions
    `g5_from_evens_low/high` verbatim). -/
lemma g5upper_hard_case_star (c : ℕ) (hc : 7 ≤ c)
    (hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + (c : ℝ) / 2 - 2)
    (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + c ≤ A.card)
    (heven_lt : (A.filter (fun x => Even x)).card < n / 6 + c)
    (heven_gt : c < (A.filter (fun x => Even x)).card) :
    HasPairwiseSums A 5 := by
  set t := (A.filter (fun x => Even x)).card - c
  have ht : 1 ≤ t := Nat.sub_pos_of_lt heven_gt
  have h6tn : (6 : ℤ) * ↑t + 6 ≤ ↑n := by omega
  have hmissing : ((Icc (1:ℤ) (2*↑n)).filter (fun x => ¬Even x) \ A).card ≤ t :=
    missing_odds_le_star c n A hA hcard heven_gt
  set A₀ := A.filter (fun x => Even x)
  set A_mid := A₀.filter (fun x => 6 * (↑t : ℤ) + 2 ≤ x ∧ x ≤ 2 * ↑n - 6 * ↑t - 2)
  by_cases hmid : A_mid.card ≥ 5
  · obtain ⟨b, hbm, hbs⟩ : ∃ b : Fin 5 → ℤ, (∀ i, b i ∈ A_mid) ∧ StrictMono b :=
      ⟨fun i => A_mid.orderEmbOfFin rfl ⟨i, by omega⟩,
       fun i => by simp +decide, by simp +decide [StrictMono]⟩
    by_cases hle : b 2 ≤ ↑n
    · exact g5_from_evens_low n A hA (b 0) (b 1) (b 2)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 0) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 1) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 2) |>.1) |>.1)
        (Finset.mem_filter.mp (hbm 0 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 1 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 2 |> Finset.mem_filter.mp |>.1) |>.2)
        (hbs (by decide)) (hbs (by decide)) t ht
        (Finset.mem_filter.mp (hbm 0) |>.2.1) hle h6tn hmissing
    · push_neg at hle
      exact g5_from_evens_high n A hA (b 2) (b 3) (b 4)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 2) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 3) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 4) |>.1) |>.1)
        (Finset.mem_filter.mp (hbm 2 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 3 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 4 |> Finset.mem_filter.mp |>.1) |>.2)
        (hbs (by decide)) (hbs (by decide)) t ht
        (by linarith) (Finset.mem_filter.mp (hbm 4) |>.2.2) h6tn hmissing
  · push_neg at hmid
    have htcard : t + c ≤ A₀.card := le_of_eq (Nat.sub_add_cancel (le_of_lt heven_gt))
    exact g5upper_hard_concentrated_star c hc hkey n A hA t ht A₀ rfl htcard A_mid rfl hmid

/-- Many-evens case (upstream `g5upper_aux_ces`, f*-version).  Per the Codex
    gate (finding 4), no sublinearity lemma is needed: `hkey` at x = 2n plus
    monotonicity already gives a stronger bound than upstream's
    `fFun5_bound_2n` route. -/
lemma g5upper_aux_ces_star (c : ℕ) (hc : 7 ≤ c)
    (hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + (c : ℝ) / 2 - 2)
    (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hn : c ≤ n)
    (heven_count : n / 6 + c ≤ (A.filter (fun x => Even x)).card) :
    HasPairwiseSums A 5 := by
  have hA₀_sub : A.filter (fun x => Even x) ⊆ A := Finset.filter_subset _ _
  have hA₀_even : ∀ a ∈ A.filter (fun x => Even x), (2:ℤ) ∣ a :=
    fun x hx => even_iff_two_dvd.mp (Finset.mem_filter.mp hx).2
  have hA₀_pos : ∀ a ∈ A.filter (fun x => Even x), (2:ℤ) ≤ a := by
    intro x hx
    have h1 := (Finset.mem_Icc.mp (hA (hA₀_sub hx))).1
    obtain ⟨k, rfl⟩ := hA₀_even x hx
    omega
  have hA₀_card2 : 2 ≤ (A.filter (fun x => Even x)).card := by omega
  have hA₀_ne : (A.filter (fun x => Even x)).Nonempty := Finset.card_pos.mp (by omega)
  have hA₀_range : 2 ≤ (A.filter (fun x => Even x)).max' hA₀_ne
      - (A.filter (fun x => Even x)).min' hA₀_ne :=
    even_range_ge_two' _ hA₀_ne hA₀_even hA₀_card2
  have hrange_ub : (A.filter (fun x => Even x)).max' hA₀_ne
      - (A.filter (fun x => Even x)).min' hA₀_ne ≤ 2 * (n : ℤ) := by
    have h1 : (A.filter (fun x => Even x)).max' hA₀_ne ≤ 2 * (n : ℤ) :=
      (Finset.mem_Icc.mp (hA (hA₀_sub (Finset.max'_mem _ hA₀_ne)))).2
    have h2 : (2:ℤ) ≤ (A.filter (fun x => Even x)).min' hA₀_ne :=
      hA₀_pos _ (Finset.min'_mem _ hA₀_ne)
    omega
  have hcard : fStar 5 (↑((A.filter (fun x => Even x)).max' hA₀_ne
      - (A.filter (fun x => Even x)).min' hA₀_ne)) 0
      ≤ ((A.filter (fun x => Even x)).card : ℝ) := by
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by
      have : (7:ℕ) ≤ n := le_trans hc hn
      exact_mod_cast le_trans (by norm_num : (1:ℕ) ≤ 7) this
    have hmono : fStar 5 (↑((A.filter (fun x => Even x)).max' hA₀_ne
        - (A.filter (fun x => Even x)).min' hA₀_ne)) 0 ≤ fStar 5 (2 * (n:ℝ)) 0 := by
      apply fStar_mono_x 5 (by omega)
      · exact le_rfl
      · exact_mod_cast hA₀_range
      · exact_mod_cast hrange_ub
    have hk := hkey (2 * (n:ℝ)) (by linarith)
    have h6 : (n:ℝ) < 6 * ((n / 6 : ℕ) : ℝ) + 6 := by
      have h7 : n < 6 * (n / 6) + 6 := by omega
      exact_mod_cast h7
    have hec : ((n / 6 : ℕ) : ℝ) + (c:ℝ) ≤ ((A.filter (fun x => Even x)).card : ℝ) := by
      exact_mod_cast heven_count
    have hc4 : (7:ℝ) ≤ (c:ℝ) := by exact_mod_cast hc
    -- fStar 5 (2n) < n/6 + c/2 − 2 ≤ ⌊n/6⌋ + c ≤ |A₀|
    linarith
  exact g5upper_case_even_star A (A.filter (fun x => Even x)) hA₀_sub hA₀_ne
    hA₀_even hA₀_pos hA₀_range hcard

/-- Few-evens case dispatcher (upstream `g5upper_aux_few_evens`). -/
lemma g5upper_aux_few_evens_star (c : ℕ) (hc : 7 ≤ c)
    (hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + (c : ℝ) / 2 - 2)
    (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + c ≤ A.card)
    (hn : c ≤ n)
    (hec : (A.filter (fun x => Even x)).card < n / 6 + c) :
    HasPairwiseSums A 5 := by
  have hge := even_count_ge_c_star c n A hA hcard
  by_cases ht0 : (A.filter (fun x => Even x)).card = c
  · exact g5upper_all_odds_star c hc n A hA hcard hn ht0
  · exact g5upper_hard_case_star c hc hkey n A hA hcard hec
      (Nat.lt_of_le_of_ne hge (Ne.symm ht0))

/-- The parameterized core (upstream `g5upper_aux`): any A ⊆ [1, 2n] with
    |A| ≥ n + c has 5 distinct integers with all pairwise sums in A,
    provided c ≥ 7 satisfies the key inequality. -/
lemma g5upper_aux_star (c : ℕ) (hc : 7 ≤ c)
    (hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + (c : ℝ) / 2 - 2)
    (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + c ≤ A.card) :
    HasPairwiseSums A 5 := by
  by_cases hn : n < c
  · exfalso
    have h1 := Finset.card_le_card hA
    have h2 : (Icc (1:ℤ) (2*↑n)).card = 2*n := by rw [Int.card_Icc]; omega
    omega
  · push_neg at hn
    by_cases hec : n / 6 + c ≤ (A.filter (fun x => Even x)).card
    · exact g5upper_aux_ces_star c hc hkey n A hA hn hec
    · push_neg at hec
      exact g5upper_aux_few_evens_star c hc hkey n A hA hcard hn hec

/-! ## The T1 closure at the tuned fallback constant B = 3,520,600 -/

/-- **g₅(n) < 3,520,600 for all n** — the C3-P1 exit theorem: 34.1× below the
    standing Lean bound `g5upper` (120,000,000), via Lemma A (no
    disjoint-representation factor 2) and the kernel-grade tuned certificate
    `key_ineq_star_tuned`. -/
theorem g5upper_star (n : ℕ) : gFun 5 n < 3520600 := by
  unfold gFun
  have hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + ((3520599 : ℕ) : ℝ) / 2 - 2 := by
    intro x hx
    have h := key_ineq_star_tuned x hx
    have he : ((3520599 : ℕ) : ℝ) = (3520600 : ℝ) - 1 := by norm_num
    rw [he]
    exact h
  have hmem : (3520599 : ℕ) ∈ {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
      n + m ≤ A.card → HasPairwiseSums A 5} := by
    intro A hA hcard
    exact g5upper_aux_star 3520599 (by norm_num) hkey n A hA hcard
  exact lt_of_le_of_lt (Nat.sInf_le hmem) (by norm_num)

/-- The formal T1 Prop from Statements.lean, closed at B' = 3,520,600. -/
theorem T1TargetG5_closed_3520600 : T1TargetG5 3520600 :=
  ⟨by norm_num, g5upper_star⟩

/-! ## Phase D — the charter constant B = 3,519,220 (two-regime certificate)

The wrapper above is constant-generic, so Phase D is purely numeric: prove
(xineq*) at c = 3,519,219.  Design (exact-arithmetic transcript
`lenses/C3P1-g5-port/phaseD_design2.py`):

* split point u_c = 52/5 (x_c = (52/5)⁸ ≈ 1.369·10⁸, below the maximizer
  x* ≈ 1.478·10⁸);
* low regime 1 ≤ u ≤ 52/5: the OLD chain `fStar5_le_poly` + tangent lines at
  u_c itself; the slope excess (8.05·10⁻⁴) is absorbed by u⁸ ≤ (52/5)⁸; the
  bound collapses to g_old(52/5) exactly — margin 3758.02;
* sharp regime u ≥ 52/5: two-regime base bound f*₃(u⁸,2) ≤ u⁴ + 5/2 + δ with
  δ = 13/(8·(52/5)⁴) = 625/4499456, giving the u³ coefficient
  A₅ = 11249265/17997824 ≈ 0.6250347 (vs 9/8 in the fallback chain); new u⁷
  tangent at u₀ = 10500232243/10⁹ ≈ the true maximizer, reusing
  `young_u3_tuned`/`young_u1_tuned`; slope gap 3.521·10⁻¹², constant margin
  0.0162403 — razor-thin but exact. -/

private lemma sqrt_le_of_sq_ge' {z y : ℝ} (hy : 0 ≤ y) (h : z ≤ y ^ 2) :
    Real.sqrt z ≤ y := by
  calc Real.sqrt z ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = y := Real.sqrt_sq hy

/-- Sharp base bound (two-regime): f*₃(u⁸, 2) ≤ u⁴ + 5/2 + 625/4499456 for
    u ≥ 52/5.  (5/2 + 625/4499456 = 11249265/4499456.) -/
lemma fStar3_le_poly_sharp (u : ℝ) (hu : 52/5 ≤ u) :
    fStar 3 (u ^ 8) 2 ≤ u ^ 4 + 11249265/4499456 := by
  have hu0 : (0:ℝ) ≤ u := by linarith
  have e : fStar 3 (u ^ 8) 2
      = 2 + 1 / 2 + Real.sqrt (u ^ 8 + 1 + ((2 : ℝ) - 1 / 2) ^ 2) := rfl
  have h4 : (52/5 : ℝ) ^ 4 ≤ u ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have h : Real.sqrt (u ^ 8 + 1 + ((2 : ℝ) - 1 / 2) ^ 2) ≤ u ^ 4 + 625/4499456 := by
    apply sqrt_le_of_sq_ge' (by positivity)
    nlinarith [h4]
  rw [e]; linarith

/-- Sharp level 4: f*₄(u⁸, 1) ≤ u⁶ + (11249265/8998912)u² + 3/2 for u ≥ 52/5. -/
lemma fStar4_le_poly_sharp (u : ℝ) (hu : 52/5 ≤ u) :
    fStar 4 (u ^ 8) 1 ≤ u ^ 6 + 11249265/8998912 * u ^ 2 + 3 / 2 := by
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu0 : (0:ℝ) ≤ u := by linarith
  have e : fStar 4 (u ^ 8) 1
      = 1 + 1 / 2 + Real.sqrt (u ^ 8 * fStar 3 (u ^ 8) (1 + 1) + ((1 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((1 : ℝ) + 1) = 2 by norm_num] at e
  have h3 := fStar3_le_poly_sharp u hu
  have hu4 : (1 : ℝ) ≤ u ^ 4 :=
    by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu1 4
  have hmul : u ^ 8 * fStar 3 (u ^ 8) 2 ≤ u ^ 8 * (u ^ 4 + 11249265/4499456) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h : Real.sqrt (u ^ 8 * fStar 3 (u ^ 8) 2 + ((1 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 6 + 11249265/8998912 * u ^ 2 := by
    apply sqrt_le_of_sq_ge' (by positivity)
    nlinarith [hmul, hu4]
  rw [e]; linarith

/-- Sharp level 5: f*₅(u⁸, 0) ≤ u⁷ + (11249265/17997824)u³ + (3/4)u + 1/2 for
    u ≥ 52/5 — the charter-grade chain bound (u³ coefficient ≈ 0.62503 vs the
    fallback 9/8). -/
lemma fStar5_le_poly_sharp (u : ℝ) (hu : 52/5 ≤ u) :
    fStar 5 (u ^ 8) 0 ≤ u ^ 7 + 11249265/17997824 * u ^ 3 + 3 / 4 * u + 1 / 2 := by
  have hu1 : (1:ℝ) ≤ u := by linarith
  have hu0 : (0:ℝ) ≤ u := by linarith
  have e : fStar 5 (u ^ 8) 0
      = 0 + 1 / 2 + Real.sqrt (u ^ 8 * fStar 4 (u ^ 8) (0 + 1) + ((0 : ℝ) - 1 / 2) ^ 2) := rfl
  rw [show ((0 : ℝ) + 1) = 1 by norm_num] at e
  have h4 := fStar4_le_poly_sharp u hu
  have hu2 : (1 : ℝ) ≤ u ^ 2 :=
    by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu1 2
  have hu4 : (1 : ℝ) ≤ u ^ 4 :=
    by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu1 4
  have hu6 : (1 : ℝ) ≤ u ^ 6 :=
    by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hu1 6
  have hmul : u ^ 8 * fStar 4 (u ^ 8) 1 ≤ u ^ 8 * (u ^ 6 + 11249265/8998912 * u ^ 2 + 3 / 2) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h : Real.sqrt (u ^ 8 * fStar 4 (u ^ 8) 1 + ((0 : ℝ) - 1 / 2) ^ 2)
      ≤ u ^ 7 + 11249265/17997824 * u ^ 3 + 3 / 4 * u := by
    apply sqrt_le_of_sq_ge' (by positivity)
    nlinarith [hmul, hu2, hu4, hu6]
  rw [e]; linarith

/-- Charter u⁷ tangent at u₀ = 10500232243/10⁹ (≈ the true maximizer
    u* = x*^{1/8}; sensitivity quadratic, so 10 digits suffice).
    Slope 875000000/10500232243, constant u₀⁷/8. -/
lemma young_u7_charter (u : ℝ) (hu : 0 ≤ u) :
    u ^ 7 ≤ 875000000/10500232243 * u ^ 8
      + 14073182965951859623990984925864909030403618285298785781253508980975707/8000000000000000000000000000000000000000000000000000000000000000 := by
  have h := poly_nonneg (1000000000 * u / 10500232243) (by positivity)
  have key : 875000000/10500232243 * u ^ 8
      + (14073182965951859623990984925864909030403618285298785781253508980975707/8000000000000000000000000000000000000000000000000000000000000000 : ℝ) - u ^ 7
      = 14073182965951859623990984925864909030403618285298785781253508980975707/8000000000000000000000000000000000000000000000000000000000000000 *
        (7 * (1000000000 * u / 10500232243) ^ 8 - 8 * (1000000000 * u / 10500232243) ^ 7 + 1) := by
    ring
  have h2 : (0 : ℝ) ≤ 875000000/10500232243 * u ^ 8
      + (14073182965951859623990984925864909030403618285298785781253508980975707/8000000000000000000000000000000000000000000000000000000000000000 : ℝ) - u ^ 7 := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Sharp-regime polynomial core: margin 0.0162403, slope gap 3.521·10⁻¹²
    (exact arithmetic, phaseD_design2.py). -/
lemma key_ineq_charter_poly_high (u : ℝ) (hu : 52/5 ≤ u) :
    u ^ 7 + 11249265/17997824 * u ^ 3 + 3 / 4 * u + 1 / 2
      < u ^ 8 / 12 + ((3519220 : ℝ) - 1) / 2 - 2 := by
  have hu0 : (0:ℝ) ≤ u := by linarith
  have h7 := young_u7_charter u hu0
  have h3 := young_u3_tuned u hu0
  have h1 := young_u1_tuned u hu0
  have h8 : (0 : ℝ) ≤ u ^ 8 := by positivity
  linarith

/-- Low-regime u⁷ tangent at u_c = 52/5: slope 35/416, constant
    (52/5)⁷/8 = 128508962816/78125. -/
lemma young_u7_low (u : ℝ) (hu : 0 ≤ u) :
    u ^ 7 ≤ 35/416 * u ^ 8 + 128508962816/78125 := by
  have h := poly_nonneg (5 * u / 52) (by positivity)
  have key : 35/416 * u ^ 8 + (128508962816/78125 : ℝ) - u ^ 7
      = 128508962816/78125 * (7 * (5 * u / 52) ^ 8 - 8 * (5 * u / 52) ^ 7 + 1) := by
    ring
  have h2 : (0 : ℝ) ≤ 35/416 * u ^ 8 + (128508962816/78125 : ℝ) - u ^ 7 := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Low-regime u³ tangent at u_c = 52/5: slope 9375/3041632256, constant
    (5/8)(52/5)³ = 17576/25. -/
lemma young_u3_low (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ 9375/3041632256 * u ^ 8 + 17576/25 := by
  have h := poly_nonneg38 (5 * u / 52) (by positivity)
  have key : 9375/3041632256 * u ^ 8 + (17576/25 : ℝ) - u ^ 3
      = 17576/125 * (3 * (5 * u / 52) ^ 8 - 8 * (5 * u / 52) ^ 3 + 5) := by
    ring
  have h2 : (0 : ℝ) ≤ 9375/3041632256 * u ^ 8 + (17576/25 : ℝ) - u ^ 3 := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Low-regime u tangent at u_c = 52/5: slope 78125/8224573620224, constant
    (7/8)(52/5) = 91/10. -/
lemma young_u1_low (u : ℝ) (hu : 0 ≤ u) :
    u ≤ 78125/8224573620224 * u ^ 8 + 91/10 := by
  have h := poly_nonneg18 (5 * u / 52) (by positivity)
  have key : 78125/8224573620224 * u ^ 8 + (91/10 : ℝ) - u
      = 13/10 * ((5 * u / 52) ^ 8 - 8 * (5 * u / 52) + 7) := by
    ring
  have h2 : (0 : ℝ) ≤ 78125/8224573620224 * u ^ 8 + (91/10 : ℝ) - u := by
    rw [key]; exact mul_nonneg (by norm_num) h
  linarith

/-- Low-regime polynomial core (1 ≤ u ≤ 52/5): the slope excess over 1/12 is
    absorbed by u⁸ ≤ (52/5)⁸; bound = g_old(52/5), margin 3758.02. -/
lemma key_ineq_charter_poly_low (u : ℝ) (hu1 : 1 ≤ u) (hu : u ≤ 52/5) :
    u ^ 7 + 9 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2
      < u ^ 8 / 12 + ((3519220 : ℝ) - 1) / 2 - 2 := by
  have hu0 : (0:ℝ) ≤ u := by linarith
  have h7 := young_u7_low u hu0
  have h3 := young_u3_low u hu0
  have h1 := young_u1_low u hu0
  have h8 : u ^ 8 ≤ (53459728531456/390625 : ℝ) := by
    calc u ^ 8 ≤ (52/5 : ℝ) ^ 8 := pow_le_pow_left₀ hu0 hu 8
      _ = 53459728531456/390625 := by norm_num
  linarith

/-- **(xineq*) at the charter constant B = 3,519,220** — Phase D complete.
    Two-regime split at u = 52/5 (x ≈ 1.369·10⁸). -/
theorem key_ineq_star_charter (x : ℝ) (hx : 1 ≤ x) :
    fStar 5 x 0 < x / 12 + ((3519220 : ℝ) - 1) / 2 - 2 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set u : ℝ := x ^ ((1 : ℝ) / 8) with hu_def
  have hu : 1 ≤ u := Real.one_le_rpow hx (by norm_num)
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hux : u ^ (8 : ℕ) = x := by
    rw [hu_def, ← Real.rpow_natCast (x ^ ((1 : ℝ) / 8)) 8, ← Real.rpow_mul hx0]
    norm_num
  rcases le_total u (52/5) with hcase | hcase
  · calc fStar 5 x 0 = fStar 5 (u ^ 8) 0 := by rw [hux]
      _ ≤ u ^ 7 + 9 / 8 * u ^ 3 + 3 / 4 * u + 1 / 2 := fStar5_le_poly u hu
      _ < u ^ 8 / 12 + ((3519220 : ℝ) - 1) / 2 - 2 :=
          key_ineq_charter_poly_low u hu hcase
      _ = x / 12 + ((3519220 : ℝ) - 1) / 2 - 2 := by rw [hux]
  · calc fStar 5 x 0 = fStar 5 (u ^ 8) 0 := by rw [hux]
      _ ≤ u ^ 7 + 11249265/17997824 * u ^ 3 + 3 / 4 * u + 1 / 2 :=
          fStar5_le_poly_sharp u hcase
      _ < u ^ 8 / 12 + ((3519220 : ℝ) - 1) / 2 - 2 :=
          key_ineq_charter_poly_high u hcase
      _ = x / 12 + ((3519220 : ℝ) - 1) / 2 - 2 := by rw [hux]

/-- **g₅(n) < 3,519,220 for all n** — the FULL charter constant (ATTACK.md P3
    exit statement; the lens-certified route minimum is 3,519,219 = B − 1).
    34.1× below the standing `g5upper`. -/
theorem g5upper_star_charter (n : ℕ) : gFun 5 n < 3519220 := by
  unfold gFun
  have hkey : ∀ x : ℝ, 1 ≤ x → fStar 5 x 0 < x / 12 + ((3519219 : ℕ) : ℝ) / 2 - 2 := by
    intro x hx
    have h := key_ineq_star_charter x hx
    have he : ((3519219 : ℕ) : ℝ) = (3519220 : ℝ) - 1 := by norm_num
    rw [he]
    exact h
  have hmem : (3519219 : ℕ) ∈ {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
      n + m ≤ A.card → HasPairwiseSums A 5} := by
    intro A hA hcard
    exact g5upper_aux_star 3519219 (by norm_num) hkey n A hA hcard
  exact lt_of_le_of_lt (Nat.sInf_le hmem) (by norm_num)

/-- The formal T1 Prop, closed at the charter constant B' = 3,519,220. -/
theorem T1TargetG5_closed_charter : T1TargetG5 3519220 :=
  ⟨by norm_num, g5upper_star_charter⟩

/-! ## Axiom audit -/

-- Expected: NO sorryAx anywhere; base axioms [propext, Classical.choice,
-- Quot.sound] only.
#print axioms lemmaA
#print axioms ceslemgeneral_star
#print axioms g5upper_star
#print axioms T1TargetG5_closed_3520600
#print axioms key_ineq_star_charter
#print axioms g5upper_star_charter
#print axioms T1TargetG5_closed_charter

end Erdos866
