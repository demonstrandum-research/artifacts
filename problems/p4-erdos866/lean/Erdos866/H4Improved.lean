/-
Erdős #866, Campaign 2, P1 — h₄(n) ≤ 1000 (NEW module; upstream untouched).

Lean port of the central-interval lens result (lenses/central-interval/PROOF.md):

  **Theorem** `h4_le_1000` : for every n ≥ 1, hFun 4 n ≤ 1000.

Standing formalized bound before this: hFun 4 n ≤ 2270 (upstream `h4upper`).

Proof skeleton = van Doorn's §7 skeleton with two changes (PROOF.md §0):
1. *Asymmetric central window*: case 1 fires for an even 2m ∈ A with
   8t+6 ≤ 2m ≤ 2n−4t−4 (upper edge only needs the largest constructed sum
   2m+4t+3 ≤ 2n−1). `exists_valid_b3_asym` / `has_pps_central_even_asym` below
   are the upstream lemmas with the hypothesis `m + 4t + 3 ≤ n` relaxed to
   `2m + 4t + 4 ≤ 2n`; the proofs are the upstream proofs verbatim (the final
   linear-arithmetic facts absorb the change).
2. *Energy-form weak-Sidon base*: case 2 splits the evens into
   low ⊆ [2, 8t+4] (diameter ≤ 8t+2) and high ⊆ [2n−4t−2, 2n] (diameter
   ≤ 4t+2) and runs the CES Lemma-A chain against the quantitative energy
   inequality `weak_sidon_key_ineq` (upstream, line 889) with explicit (Φ, ν)
   certificates (`Erdos866.H4Cert` table for t ≤ 400000, `Erdos866.H4Tail`
   tail tuple for t > 400000), instead of Ruzsa's closed-form bound.

Upstream ingredients reused as-is: `weak_sidon_key_ineq`,
`pigeonhole_differences_strong`, `exists_shift_independent_subset`,
`has_pps_from_shifted_non_sidon`, and the `hFun`/`HasPosPairwiseSums` API.
-/
import Erdos866.Upstream
import Erdos866.H4Cert
import Erdos866.H4Tail

open Finset
open scoped Pointwise Classical

set_option maxHeartbeats 800000
set_option maxRecDepth 16000

namespace ErdosH4

/-! ### Weak-Sidon helper lemmas (new) -/

/-- A subset of a weak Sidon set is weak Sidon. -/
lemma weak_sidon_subset {S T : Finset ℤ} (h : IsWeakSidonSet T) (hsub : S ⊆ T) :
    IsWeakSidonSet S :=
  fun a ha b hb c hc d hd hab hac had hbc hbd hcd =>
    h a (hsub ha) b (hsub hb) c (hsub hc) d (hsub hd) hab hac had hbc hbd hcd

/-- **Energy-violation criterion.** A set of ≥ Φ even integers inside a window
of diameter ≤ R (R even) is not weak Sidon, provided the pair (Φ, ν) violates
the energy inequality for N₀ = R/2 + 1, i.e. (R/2 + ν)(3Φ + ν − 1) < Φ²ν.
This replaces the upstream `not_weak_sidon_of_card_large` route: it feeds the
*quantitative* `weak_sidon_key_ineq` with an explicit certificate ν instead of
the Nat.sqrt-shaped specialization. -/
lemma not_weak_sidon_of_phinu (S : Finset ℤ)
    (heven : ∀ a ∈ S, Even a)
    (R Φ ν : ℕ) (hν : 0 < ν) (hΦ : 0 < Φ) (hReven : Even R)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (R : ℤ))
    (hΦle : Φ ≤ S.card)
    (hV : (R / 2 + ν) * (3 * Φ + ν - 1) < Φ * Φ * ν) :
    ¬ IsWeakSidonSet S := by
  intro hws
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hΦle
  have hne' : S'.Nonempty := Finset.card_pos.mp (by omega)
  set m := S'.min' hne' with hm_def
  have hmS : m ∈ S' := S'.min'_mem hne'
  have hm2 : m % 2 = 0 := Int.even_iff.mp (heven m (hS'sub hmS))
  obtain ⟨r, hr⟩ := hReven
  -- the halved translate T ⊆ [1, R/2 + 1]
  set f : ℤ → ℤ := fun x => (x - m) / 2 + 1 with hf_def
  have hinj : Set.InjOn f S' := by
    intro x hx y hy hxy
    have hx2 : x % 2 = 0 := Int.even_iff.mp (heven x (hS'sub hx))
    have hy2 : y % 2 = 0 := Int.even_iff.mp (heven y (hS'sub hy))
    simp only [hf_def] at hxy
    omega
  set T := S'.image f with hT_def
  have hTcard : T.card = Φ := by
    rw [hT_def, Finset.card_image_of_injOn hinj, hS'card]
  have hTbound : ∀ x ∈ T, 1 ≤ x ∧ x ≤ ((R / 2 + 1 : ℕ) : ℤ) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have h1 : m ≤ x := S'.min'_le x hx
    have h2 : x - m ≤ (R : ℤ) := (abs_le.mp (hdiam x (hS'sub hx) m (hS'sub hmS))).2
    have hx2 : x % 2 = 0 := Int.even_iff.mp (heven x (hS'sub hx))
    have hRr : R = r + r := hr
    simp only [hf_def]
    omega
  have hwsT : IsWeakSidonSet T := by
    intro a ha b hb c hc d hd hab hac had hbc hbd hcd
    obtain ⟨xa, hxa, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨xb, hxb, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨xc, hxc, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨xd, hxd, rfl⟩ := Finset.mem_image.mp hd
    intro heq
    have hxa2 : xa % 2 = 0 := Int.even_iff.mp (heven xa (hS'sub hxa))
    have hxb2 : xb % 2 = 0 := Int.even_iff.mp (heven xb (hS'sub hxb))
    have hxc2 : xc % 2 = 0 := Int.even_iff.mp (heven xc (hS'sub hxc))
    have hxd2 : xd % 2 = 0 := Int.even_iff.mp (heven xd (hS'sub hxd))
    simp only [hf_def] at heq
    have hsum : xa + xb = xc + xd := by omega
    exact hws xa (hS'sub hxa) xb (hS'sub hxb) xc (hS'sub hxc) xd (hS'sub hxd)
      (fun h => hab (congrArg f h)) (fun h => hac (congrArg f h))
      (fun h => had (congrArg f h)) (fun h => hbc (congrArg f h))
      (fun h => hbd (congrArg f h)) (fun h => hcd (congrArg f h)) hsum
  have hkey := weak_sidon_key_ineq T (R / 2 + 1) ν hwsT hTbound hν
  rw [hTcard] at hkey
  have he1 : R / 2 + 1 + ν - 1 = R / 2 + ν := by omega
  rw [he1, pow_two] at hkey
  exact absurd hkey (Nat.not_le.mpr hV)

/-- **CES Lemma-A chain for k = 4, (Φ, ν)-certified version** (Lemma 5 of the
lens PROOF.md). A₁ ⊆ A a set of positive even integers within a window of
diameter ≤ R (R even), with |A₁|(|A₁|−1) > 2R(Φ−1) (the popularity threshold)
and (R/2 + ν)(3Φ + ν − 1) < Φ²ν (the energy violation), yields four distinct
positive integers with all six pairwise sums in A. -/
lemma chain_phinu (A A₁ : Finset ℤ)
    (hA₁_sub : A₁ ⊆ A)
    (heven : ∀ a ∈ A₁, Even a)
    (hpos : ∀ a ∈ A₁, 0 < a)
    (R Φ ν : ℕ)
    (hR_pos : 0 < R) (hReven : Even R) (hν : 0 < ν) (hΦ : 0 < Φ)
    (hdiam : ∀ a ∈ A₁, ∀ b ∈ A₁, |a - b| ≤ (R : ℤ))
    (hW : 2 * R * (Φ - 1) < A₁.card * (A₁.card - 1))
    (hV : (R / 2 + ν) * (3 * Φ + ν - 1) < Φ * Φ * ν) :
    HasPosPairwiseSums A 4 := by
  have h2 : 2 ≤ A₁.card := by
    rcases Nat.lt_or_ge A₁.card 2 with h | h
    · exfalso
      have h0 : A₁.card * (A₁.card - 1) = 0 := by
        have : A₁.card = 0 ∨ A₁.card = 1 := by omega
        rcases this with h' | h' <;> simp [h']
      rw [h0] at hW
      exact Nat.not_lt_zero _ hW
    · exact h
  obtain ⟨d, hd_pos, hd_even, hd_le_R, hd_card⟩ :=
    pigeonhole_differences_strong A₁ h2 heven R hdiam hR_pos
  obtain ⟨S, hS_sub, hS_card2, hS_shift⟩ :=
    exists_shift_independent_subset (A₁.filter (fun x => x + d ∈ A₁)) d hd_pos
  -- popularity: |P_d| > 2(Φ−1), hence |S| ≥ Φ
  have hP : 2 * (Φ - 1) < (A₁.filter (fun x => x + d ∈ A₁)).card := by
    by_contra hcon
    push_neg at hcon
    have hmul : R * (A₁.filter (fun x => x + d ∈ A₁)).card ≤ R * (2 * (Φ - 1)) :=
      Nat.mul_le_mul_left R hcon
    have h2R : R * (2 * (Φ - 1)) = 2 * R * (Φ - 1) := by ring
    linarith [hd_card, hW, hmul, h2R.le, h2R.ge]
  have hSΦ : Φ ≤ S.card := by omega
  have hSsubA₁ : S ⊆ A₁ := fun x hx => (Finset.mem_filter.mp (hS_sub hx)).1
  apply has_pps_from_shifted_non_sidon A A₁ hA₁_sub S hSsubA₁ d hd_pos
    (fun x hx => (Finset.mem_filter.mp (hS_sub hx)).2)
    hS_shift
    (fun a ha => heven a (hSsubA₁ ha))
    (fun a ha => hpos a (hSsubA₁ ha))
  exact not_weak_sidon_of_phinu S (fun a ha => heven a (hSsubA₁ ha)) R Φ ν hν hΦ hReven
    (fun a ha b hb => hdiam a (hSsubA₁ ha) b (hSsubA₁ hb)) hSΦ hV

/-! ### Case 1 with the asymmetric window (upstream proofs, relaxed upper edge)

`exists_valid_b3` and `has_pps_central_even` from the upstream development,
verbatim except that the window hypothesis `m + 4t + 3 ≤ n` is relaxed to
`2m + 4t + 4 ≤ 2n` (the largest constructed sum is 2m + 4t + 3 ≤ 2n − 1, so
the same linear arithmetic closes). -/

/-- Pigeonhole: find a valid b₃ with correct parity whose 4 cross-sums are in A
(asymmetric-window version of upstream `exists_valid_b3`). -/
lemma exists_valid_b3_asym (A : Finset ℤ) (n t : ℕ) (m : ℤ)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hm_lb : 4 * (↑t : ℤ) + 3 ≤ m)
    (hm_ub : 2 * m + 4 * (↑t : ℤ) + 4 ≤ 2 * ↑n)
    (h_miss : ((Finset.Icc (1 : ℤ) (2 * ↑n)).filter (fun x => ¬ Even x) \ A).card ≤ t) :
    ∃ b₃ : ℤ, m - 4 * ↑t - 2 ≤ b₃ ∧ b₃ ≤ m - 2 ∧
      (m - 1 + b₃ ∈ A) ∧ (m + 1 + b₃ ∈ A) ∧
      (3 * m - 1 - b₃ ∈ A) ∧ (3 * m + 1 - b₃ ∈ A) := by
        revert A m hm_lb hm_ub h_miss;
        intro A m hA hm₁ hm₂ hB;
        -- Let's count the number of bad $b_3$ values.
        have h_bad_count : Finset.card (Finset.filter (fun b₃ => ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; ¬Even s_i ∧ 1 ≤ s_i ∧ s_i ≤ 2 * n ∧ s_i ∉ A)) (Finset.Icc (m - 4 * t - 2) (m - 2))) ≤ 2 * t := by
          -- Each missing odd can make at most 2 candidate $b_3$ values bad.
          have h_missing_odd_bound : ∀ (s : ℤ), ¬Even s ∧ 1 ≤ s ∧ s ≤ 2 * n ∧ s ∉ A → Finset.card (Finset.filter (fun b₃ => ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; s_i = s)) (Finset.Icc (m - 4 * t - 2) (m - 2))) ≤ 2 := by
            intro s hs
            simp;
            rw [ show { b₃ ∈ Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) | m - 1 + b₃ = s ∨ m + 1 + b₃ = s ∨ 3 * m - 1 - b₃ = s ∨ 3 * m + 1 - b₃ = s } = { s - ( m - 1 ), s - ( m + 1 ), 3 * m - 1 - s, 3 * m + 1 - s } ∩ Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) from ?_ ];
            · grind +locals;
            · grind;
          have h_bad_count : Finset.card (Finset.filter (fun b₃ => ∃ s ∈ ({x ∈ Icc 1 (2 * n : ℤ) | ¬Even x} \ A), ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; s_i = s)) (Finset.Icc (m - 4 * t - 2) (m - 2))) ≤ 2 * t := by
            have h_bad_count : Finset.card (Finset.biUnion ({x ∈ Icc 1 (2 * n : ℤ) | ¬Even x} \ A) (fun s => Finset.filter (fun b₃ => ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; s_i = s)) (Finset.Icc (m - 4 * t - 2) (m - 2)))) ≤ 2 * t := by
              refine' le_trans ( Finset.card_biUnion_le ) _;
              refine' le_trans ( Finset.sum_le_sum fun x hx => h_missing_odd_bound x _ ) _;
              · grind +qlia;
              · simpa [ mul_comm ] using Nat.mul_le_mul_left 2 hB;
            convert h_bad_count using 2 ; ext ; simp +decide [ Finset.mem_biUnion ];
            exact ⟨ fun ⟨ h₁, s, hs₁, hs₂ ⟩ => ⟨ s, hs₁, h₁, hs₂ ⟩, fun ⟨ s, hs₁, h₁, hs₂ ⟩ => ⟨ h₁, s, hs₁, hs₂ ⟩ ⟩;
          convert h_bad_count using 2;
          grind;
        contrapose! h_bad_count;
        refine' lt_of_lt_of_le _ ( Finset.card_mono _ );
        rotate_left;
        exact Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) |> Finset.filter ( fun x => x % 2 = m % 2 );
        · intro x hx; simp_all +decide [ Int.even_iff ] ;
          grind +ring;
        · rw [ show ( Finset.filter ( fun x => x % 2 = m % 2 ) ( Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) ) ) = Finset.image ( fun x : ℕ => m - 2 - 2 * x ) ( Finset.range ( 2 * t + 1 ) ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
          ext;
          constructor;
          · simp +zetaDelta at *;
            exact fun h₁ h₂ h₃ => ⟨ Int.toNat ( ( m - 2 - ‹ℤ› ) / 2 ), by omega, by omega ⟩;
          · grind

/-- Case 1 helper, asymmetric window: a central even element 2m ∈ A with
4t+3 ≤ m and 2m + 4t + 4 ≤ 2n, plus ≤ t missing odds, gives a positive
4-configuration (asymmetric-window version of upstream `has_pps_central_even`). -/
lemma has_pps_central_even_asym (A : Finset ℤ) (n t : ℕ) (m : ℤ)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hm : (2 * m) ∈ A)
    (hm_lb : 4 * (↑t : ℤ) + 3 ≤ m)
    (hm_ub : 2 * m + 4 * (↑t : ℤ) + 4 ≤ 2 * ↑n)
    (h_miss : ((Finset.Icc (1 : ℤ) (2 * ↑n)).filter (fun x => ¬ Even x) \ A).card ≤ t) :
    HasPosPairwiseSums A 4 := by
      -- Use exists_valid_b3_asym to get b₃ with the 4 sums in A.
      obtain ⟨b₃, hb₃_range, hb₃_sums⟩ : ∃ b₃ : ℤ, m - 4 * ↑t - 2 ≤ b₃ ∧ b₃ ≤ m - 2 ∧ (m - 1 + b₃ ∈ A) ∧ (m + 1 + b₃ ∈ A) ∧ (3 * m - 1 - b₃ ∈ A) ∧ (3 * m + 1 - b₃ ∈ A) := by
        exact exists_valid_b3_asym A n t m hA hm_lb hm_ub h_miss
      use ![b₃, m - 1, m + 1, 2 * m - b₃];
      simp +decide [ Fin.forall_fin_succ, Function.Injective, * ];
      refine' ⟨ _, _, _, _ ⟩;
      · omega;
      · exact ⟨ by linarith, by linarith, by linarith, by linarith ⟩;
      · exact ⟨ by convert hb₃_sums.2.1 using 1; ring, by convert hb₃_sums.2.2.1 using 1; ring ⟩;
      · exact ⟨ ⟨ by convert hm using 1; ring, by convert hb₃_sums.2.2.2.1 using 1; ring ⟩, by convert hb₃_sums.2.2.2.2 using 1; ring ⟩

/-! ### Assembly -/

/-- Main engine: any A ⊆ [1, 2n] with |A| ≥ n + 1000 has a positive
4-configuration. Uniform in n (no n-threshold needed). -/
lemma has_pps_of_large_1000 (A : Finset ℤ) (n : ℕ)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hcard : n + 1000 ≤ A.card) :
    HasPosPairwiseSums A 4 := by
  -- odd elements of A number at most n (upstream argument)
  have h_odd_le : (A.filter (fun x => ¬Even x)).card ≤ n := by
    have h_odd_subset : (A.filter (fun x => ¬Even x)) ⊆ Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n) := by
      exact fun x hx => by rcases Int.odd_iff.mpr ( show x % 2 = 1 from Int.emod_two_ne_zero.mp fun con => by simp_all +decide [ Int.even_iff ] ) with ⟨ k, rfl ⟩ ; exact Finset.mem_image.mpr ⟨ Int.toNat k, Finset.mem_range.mpr <| by linarith [ Int.toNat_of_nonneg <| show 0 ≤ k from by linarith [ Finset.mem_Icc.mp <| hA <| Finset.mem_filter.mp hx |>.1 ], Finset.mem_Icc.mp <| hA <| Finset.mem_filter.mp hx |>.1 ], by linarith [ Int.toNat_of_nonneg <| show 0 ≤ k from by linarith [ Finset.mem_Icc.mp <| hA <| Finset.mem_filter.mp hx |>.1 ] ] ⟩ ;
    exact le_trans ( Finset.card_le_card h_odd_subset ) ( Finset.card_image_le.trans ( by simp ) )
  have h_split : (A.filter (fun x => ¬Even x)).card + (A.filter Even).card = A.card := by
    rw [ add_comm, Finset.card_filter_add_card_filter_not ]
  have hA₀card : 1000 ≤ (A.filter Even).card := by omega
  set t := (A.filter Even).card - 1000 with ht_def
  -- missing odds in [1,2n] number exactly n − (odd elements of A) ≤ t
  have h_missing_eq : ((Finset.Icc (1 : ℤ) (2 * ↑n)).filter (fun x => ¬ Even x) \ A).card = n - (A.filter (fun x => ¬ Even x)).card := by
    rw [ Finset.card_sdiff ];
    rw [ show { x ∈ Icc 1 ( 2 * n : ℤ ) | ¬Even x } = Finset.image ( fun k : ℕ => 2 * k + 1 : ℕ → ℤ ) ( Finset.range n ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    · congr with x ; simp +decide [ parity_simps ];
      exact fun hx => ⟨ fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ⟨ a, by ring ⟩, fun hx => by obtain ⟨ k, rfl ⟩ := hx; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith [ Finset.mem_Icc.mp ( hA hx ) ] : ( 0 : ℤ ) ≤ k ), Finset.mem_Icc.mp ( hA hx ) ], by linarith [ Int.toNat_of_nonneg ( by linarith [ Finset.mem_Icc.mp ( hA hx ) ] : ( 0 : ℤ ) ≤ k ) ] ⟩ ⟩;
    · -- To prove equality of finite sets, we show each set is a subset of the other.
      apply Finset.ext
      intro x
      simp [Finset.mem_image, Finset.mem_filter];
      exact ⟨ fun hx => by obtain ⟨ k, rfl ⟩ := hx.2; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩, by rintro ⟨ k, hk₁, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩ ⟩
  have h_miss : ((Finset.Icc (1 : ℤ) (2 * ↑n)).filter (fun x => ¬ Even x) \ A).card ≤ t := by
    omega
  -- the asymmetric central window
  by_cases h_central : ∃ m : ℤ, (2 * m) ∈ A ∧ 4 * (t : ℤ) + 3 ≤ m ∧ 2 * m + 4 * (t : ℤ) + 4 ≤ 2 * ↑n
  · obtain ⟨m, hm, hm_lb, hm_ub⟩ := h_central
    exact has_pps_central_even_asym A n t m hA hm hm_lb hm_ub h_miss
  · push_neg at h_central
    -- Case 2: split the evens into low ⊆ [2, 8t+4] and high ⊆ [2n−4t−2, 2n]
    set low := (A.filter Even).filter (fun x => x ≤ 8 * (t : ℤ) + 4) with hlow_def
    set high := (A.filter Even).filter (fun x => 2 * (n : ℤ) - 4 * (t : ℤ) - 2 ≤ x) with hhigh_def
    have hlowsubA : low ⊆ A := fun x hx =>
      Finset.filter_subset _ _ (Finset.filter_subset _ _ hx)
    have hhighsubA : high ⊆ A := fun x hx =>
      Finset.filter_subset _ _ (Finset.filter_subset _ _ hx)
    have hcover : (A.filter Even).card ≤ low.card + high.card := by
      have hsub : A.filter Even ⊆ low ∪ high := by
        intro e he
        have heven : Even e := (Finset.mem_filter.mp he).2
        have heA : e ∈ A := (Finset.mem_filter.mp he).1
        obtain ⟨me, hme⟩ := heven
        have h2me : (2 * me) ∈ A := by rw [show (2:ℤ) * me = me + me by ring]; rwa [← hme]
        have hcm := h_central me h2me
        rw [hlow_def, hhigh_def]
        by_cases hge : 4 * (t : ℤ) + 3 ≤ me
        · have hub := hcm hge
          have he2 : e % 2 = 0 := by omega
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, by omega⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, by omega⟩)
      calc (A.filter Even).card ≤ (low ∪ high).card := Finset.card_le_card hsub
        _ ≤ low.card + high.card := Finset.card_union_le _ _
    -- the certified tuple (block table for t ≤ 400000, tail tuple beyond)
    obtain ⟨t2, ΦL, νL, ψL, ΦH, νH, ψH, htle, hΦLpos, hνLpos, hΦHpos, hνHpos,
        hVL, hVH, hWL, hWH, hV5⟩ :
        ∃ t2 ΦL νL ψL ΦH νH ψH : ℕ,
          t ≤ t2 ∧ 0 < ΦL ∧ 0 < νL ∧ 0 < ΦH ∧ 0 < νH ∧
          (4*t2 + 1 + νL) * (3*ΦL + νL - 1) < ΦL*ΦL*νL ∧
          (2*t2 + 1 + νH) * (3*ΦH + νH - 1) < ΦH*ΦH*νH ∧
          2*(8*t2+2)*(ΦL-1) < ψL*(ψL-1) ∧
          2*(4*t2+2)*(ΦH-1) < ψH*(ψH-1) ∧
          ψL + ψH ≤ 1001 + t := by
      rcases Nat.lt_or_ge 400000 t with hbig | hsmall
      · exact ErdosH4Tail.tail_cert t hbig
      · exact cert_lookup t hsmall
    have hA₀eq : (A.filter Even).card = t + 1000 := by omega
    -- unequal-threshold pigeonhole: one of the two windows is populated enough
    have hpig : ψL ≤ low.card ∨ ψH ≤ high.card := by
      by_contra hcon
      push_neg at hcon
      omega
    rcases hpig with hbigside | hbigside
    · -- low side: window diameter ≤ 8t+2 ≤ 8t2+2
      refine chain_phinu A low hlowsubA
        (fun a ha => (Finset.mem_filter.mp (Finset.filter_subset _ _ ha)).2)
        (fun a ha => by
          have := Finset.mem_Icc.mp (hA (hlowsubA ha))
          omega)
        (8*t2+2) ΦL νL (by omega) ⟨4*t2+1, by omega⟩ hνLpos hΦLpos ?_ ?_ ?_
      · -- diameter
        intro a ha b hb
        have haA := Finset.mem_Icc.mp (hA (hlowsubA ha))
        have hbA := Finset.mem_Icc.mp (hA (hlowsubA hb))
        have ha2 : a % 2 = 0 := Int.even_iff.mp (Finset.mem_filter.mp (Finset.filter_subset _ _ ha)).2
        have hb2 : b % 2 = 0 := Int.even_iff.mp (Finset.mem_filter.mp (Finset.filter_subset _ _ hb)).2
        have haub : a ≤ 8 * (t : ℤ) + 4 := (Finset.mem_filter.mp ha).2
        have hbub : b ≤ 8 * (t : ℤ) + 4 := (Finset.mem_filter.mp hb).2
        rw [abs_le]
        constructor <;> omega
      · -- popularity threshold (V4) transported to |low|
        refine lt_of_lt_of_le hWL ?_
        exact Nat.mul_le_mul hbigside (by omega)
      · -- energy violation (V2), with (8t2+2)/2 = 4t2+1
        have he : (8*t2+2)/2 = 4*t2+1 := by omega
        rw [he]
        exact hVL
    · -- high side: window diameter ≤ 4t+2 ≤ 4t2+2
      refine chain_phinu A high hhighsubA
        (fun a ha => (Finset.mem_filter.mp (Finset.filter_subset _ _ ha)).2)
        (fun a ha => by
          have := Finset.mem_Icc.mp (hA (hhighsubA ha))
          omega)
        (4*t2+2) ΦH νH (by omega) ⟨2*t2+1, by omega⟩ hνHpos hΦHpos ?_ ?_ ?_
      · -- diameter
        intro a ha b hb
        have haA := Finset.mem_Icc.mp (hA (hhighsubA ha))
        have hbA := Finset.mem_Icc.mp (hA (hhighsubA hb))
        have halb : 2 * (n : ℤ) - 4 * (t : ℤ) - 2 ≤ a := (Finset.mem_filter.mp ha).2
        have hblb : 2 * (n : ℤ) - 4 * (t : ℤ) - 2 ≤ b := (Finset.mem_filter.mp hb).2
        rw [abs_le]
        constructor <;> omega
      · refine lt_of_lt_of_le hWH ?_
        exact Nat.mul_le_mul hbigside (by omega)
      · have he : (4*t2+2)/2 = 2*t2+1 := by omega
        rw [he]
        exact hVH

end ErdosH4

/-- **Main theorem (T1, Erdős #866 program): h₄(n) ≤ 1000 for all n ≥ 1.**
Improves the upstream Lean-verified `h4upper` (hFun 4 n ≤ 2270). -/
theorem h4_le_1000 (n : ℕ) (hn : 0 < n) : hFun 4 n ≤ 1000 := by
  unfold hFun
  apply Nat.sInf_le
  intro A hA hcard
  exact ErdosH4.has_pps_of_large_1000 A n hA hcard

#print axioms h4_le_1000
