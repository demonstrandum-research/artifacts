/-
SMaj/Six/Euler.lean — the Euler 2-split, fully CLOSED (campaign C4,
lens C4L3-lean-close, 2026-06-13; the augmentation reduction is from
campaign C3, lens C3L4-lean-six, 2026-06-12).

CLOSED (sorry-free):

* `even_sum_mdeg` — the handshake lemma for multiplicity matrices
  (edge-peeling induction over `decr`).
* `even_card_odd_mdeg` — evenly many odd-degree vertices.
* `exists_pairing` — for any evenly-sized vertex set, a perfect-matching
  matrix `p` (degree 1 exactly on the set, 0 elsewhere).
* `two_split_restrict` — a degree-≤ 2 split of an augmented matrix
  `m + p` restricts to one of `m` (subtract the `p`-edges from the part
  containing them; pointwise `min` arithmetic — machine-pretested,
  `pretest2_shannon.py` P7, 2,000/2,000).
* `two_split_of_even_split_hypothesis` — **the reduction**: if every
  EVEN loopless multigraph with Δ ≤ 4 2-splits, then every loopless
  multigraph with Δ ≤ 4 2-splits (pair the odd vertices — evenly many —
  by `exists_pairing`; degrees stay ≤ 4 because an odd degree is ≤ 3;
  split the even augmented matrix; restrict).
* `orient_core` / `exists_balanced_orientation` — **walk-free Eulerian
  orientation**: every even symmetric loopless matrix orients with
  in-degree = out-degree (mutual edge-count induction tracking an open
  trail; no Euler circuits formalized).  Pretested:
  `lenses/C4L3-lean-close/pretest3_orient.py` P8 (543 instances).
* `exists_two_split_even` — **the even-degree core, CLOSED**: balanced
  orientation + balanced orientation of the odd-paired bipartite double
  + `two_split_restrict`.  Pretested end-to-end: `pretest3_orient.py`
  P9 (756 instances, exact verification).
* `exists_two_split` — **the full Euler 2-split** (Δ ≤ 4 splits into two
  Δ ≤ 2 halves), no open inputs.  Shannon's bound at Δ = 4 follows
  (`shannon_six_of_maxDegree_four`, `SMaj/Six/Targets.lean`).
-/
import Mathlib
import SMaj.Six.Shannon

namespace SMaj

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Exact degree bookkeeping for `decr` -/

lemma mdeg_decr_eq_left {m : V → V → ℕ} {a b : V} (hne : a ≠ b)
    (hab : 0 < m a b) : mdeg (decr m a b) a = mdeg m a - 1 := by
  have hsplit₁ : decr m a b a b + ∑ u ∈ Finset.univ.erase b, decr m a b a u =
      mdeg (decr m a b) a := Finset.add_sum_erase _ _ (Finset.mem_univ b)
  have hsplit₂ : m a b + ∑ u ∈ Finset.univ.erase b, m a u = mdeg m a :=
    Finset.add_sum_erase _ _ (Finset.mem_univ b)
  have hcongr : ∑ u ∈ Finset.univ.erase b, decr m a b a u =
      ∑ u ∈ Finset.univ.erase b, m a u := by
    refine Finset.sum_congr rfl fun u hu => decr_of_ne m ?_
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact (Finset.mem_erase.mp hu).1 h
    · exact hne h
  rw [decr_ab] at hsplit₁
  omega

lemma mdeg_decr_eq_right {m : V → V → ℕ} {a b : V} (hne : a ≠ b)
    (hba : 0 < m b a) : mdeg (decr m a b) b = mdeg m b - 1 := by
  have hsplit₁ : decr m a b b a + ∑ u ∈ Finset.univ.erase a, decr m a b b u =
      mdeg (decr m a b) b := Finset.add_sum_erase _ _ (Finset.mem_univ a)
  have hsplit₂ : m b a + ∑ u ∈ Finset.univ.erase a, m b u = mdeg m b :=
    Finset.add_sum_erase _ _ (Finset.mem_univ a)
  have hcongr : ∑ u ∈ Finset.univ.erase a, decr m a b b u =
      ∑ u ∈ Finset.univ.erase a, m b u := by
    refine Finset.sum_congr rfl fun u hu => decr_of_ne m ?_
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hne h.symm
    · exact (Finset.mem_erase.mp hu).1 h
  rw [decr_ba] at hsplit₁
  omega

lemma mdeg_decr_eq_other {m : V → V → ℕ} {a b v : V} (hva : v ≠ a)
    (hvb : v ≠ b) : mdeg (decr m a b) v = mdeg m v := by
  refine Finset.sum_congr rfl fun u _ => decr_of_ne m ?_
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact hva h
  · exact hvb h

/-- Removing one (a,b) edge lowers the total degree by exactly 2. -/
lemma sum_mdeg_decr {m : V → V → ℕ} {a b : V} (hne : a ≠ b)
    (hab : 0 < m a b) (hba : 0 < m b a) :
    ∑ v, mdeg (decr m a b) v + 2 = ∑ v, mdeg m v := by
  have hsplit : ∀ g : V → ℕ, ∑ v, g v =
      g a + (g b + ∑ v ∈ (Finset.univ.erase a).erase b, g v) := by
    intro g
    rw [Finset.add_sum_erase _ _
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ b⟩),
      Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have h₁ := hsplit fun v => mdeg (decr m a b) v
  have h₂ := hsplit fun v => mdeg m v
  have hcongr : ∑ v ∈ (Finset.univ.erase a).erase b, mdeg (decr m a b) v =
      ∑ v ∈ (Finset.univ.erase a).erase b, mdeg m v := by
    refine Finset.sum_congr rfl fun v hv => ?_
    have hv' := Finset.mem_erase.mp hv
    have hv'' := Finset.mem_erase.mp hv'.2
    exact mdeg_decr_eq_other hv''.1 hv'.1
  have hda : 0 < mdeg m a :=
    lt_of_lt_of_le hab (Finset.single_le_sum (f := fun u => m a u)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ b))
  have hdb : 0 < mdeg m b :=
    lt_of_lt_of_le hba (Finset.single_le_sum (f := fun u => m b u)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ a))
  have hea := mdeg_decr_eq_left hne hab
  have heb := mdeg_decr_eq_right hne hba
  omega

/-! ### The handshake lemma and the odd-vertex count -/

/-- **Handshake**: a symmetric loopless multiplicity matrix has even
total degree (edge-peeling induction). -/
theorem even_sum_mdeg (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u)
    (hloop : ∀ v, m v v = 0) : Even (∑ v, mdeg m v) := by
  suffices h : ∀ N (m : V → V → ℕ), ∑ v, mdeg m v ≤ N →
      (∀ u v, m u v = m v u) → (∀ v, m v v = 0) →
      Even (∑ v, mdeg m v) from h _ m le_rfl hsym hloop
  intro N
  induction N with
  | zero =>
    intro m htot _ _
    rw [Nat.le_zero.mp htot]
    exact ⟨0, rfl⟩
  | succ N ih =>
    intro m htot hsym hloop
    by_cases hex : ∃ a b, 0 < m a b
    · obtain ⟨a, b, hab⟩ := hex
      have hne : a ≠ b := by
        rintro rfl; have := hloop a; omega
      have hba : 0 < m b a := by rw [← hsym a b]; exact hab
      have hdrop := sum_mdeg_decr hne hab hba
      obtain ⟨c, hc⟩ := ih (decr m a b) (by omega) (decr_symm hsym a b)
        (decr_loopless hloop a b)
      exact ⟨c + 1, by omega⟩
    · simp only [not_exists, not_lt, Nat.le_zero] at hex
      have hz : ∑ v, mdeg m v = 0 :=
        Finset.sum_eq_zero fun v _ =>
          Finset.sum_eq_zero fun u _ => hex v u
      rw [hz]; exact ⟨0, rfl⟩

/-- **Evenly many odd-degree vertices.** -/
theorem even_card_odd_mdeg (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u)
    (hloop : ∀ v, m v v = 0) :
    Even #(Finset.univ.filter fun v => Odd (mdeg m v)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v => Odd (mdeg m v)) fun v => mdeg m v
  -- the even-degree rows sum to an even number
  have heven_part : Even (∑ v ∈ Finset.univ.filter
      (fun v => ¬ Odd (mdeg m v)), mdeg m v) :=
    Finset.sum_induction _ Even (fun _ _ => Even.add) ⟨0, rfl⟩
      fun v hv => Nat.not_odd_iff_even.mp (Finset.mem_filter.mp hv).2
  have htot := even_sum_mdeg m hsym hloop
  -- so the odd-degree rows sum to an even number
  have hodd_sum : Even (∑ v ∈ Finset.univ.filter
      (fun v => Odd (mdeg m v)), mdeg m v) := by
    obtain ⟨c, hc⟩ := heven_part
    obtain ⟨d, hd⟩ := htot
    exact ⟨d - c, by omega⟩
  -- each odd row is (even) + 1, so the sum is (even) + the card
  have hshift : ∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), mdeg m v =
      (∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), (mdeg m v - 1)) +
        #(Finset.univ.filter fun v => Odd (mdeg m v)) := by
    have h1 : ∀ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)),
        mdeg m v = (mdeg m v - 1) + 1 := by
      intro v hv
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hv).2
      omega
    calc ∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), mdeg m v
        = ∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)),
            ((mdeg m v - 1) + 1) := Finset.sum_congr rfl h1
      _ = (∑ v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)),
            (mdeg m v - 1)) +
          ∑ _v ∈ Finset.univ.filter (fun v => Odd (mdeg m v)), 1 :=
            Finset.sum_add_distrib
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have heven_shift : Even (∑ v ∈ Finset.univ.filter
      (fun v => Odd (mdeg m v)), (mdeg m v - 1)) :=
    Finset.sum_induction _ Even (fun _ _ => Even.add) ⟨0, rfl⟩ fun v hv => by
      obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hv).2
      exact ⟨k, by omega⟩
  obtain ⟨c, hc⟩ := hodd_sum
  obtain ⟨d, hd⟩ := heven_shift
  exact ⟨c - d, by omega⟩

/-! ### Pairing an even vertex set -/

/-- The single-edge matrix on the pair `{x, y}`. -/
def pairUnit (x y : V) : V → V → ℕ := fun u v =>
  if (u = x ∧ v = y) ∨ (u = y ∧ v = x) then 1 else 0

lemma pairUnit_symm (x y : V) : ∀ u v, pairUnit x y u v = pairUnit x y v u := by
  intro u v; unfold pairUnit
  by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
  · rw [if_pos h, if_pos (by tauto)]
  · rw [if_neg h, if_neg (by tauto)]

lemma pairUnit_loopless {x y : V} (hxy : x ≠ y) :
    ∀ v, pairUnit x y v v = 0 := by
  intro v; unfold pairUnit
  rw [if_neg]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hxy (h1.symm.trans h2)
  · exact hxy (h2.symm.trans h1)

lemma mdeg_pairUnit {x y : V} (hxy : x ≠ y) (v : V) :
    mdeg (pairUnit x y) v = if v = x ∨ v = y then 1 else 0 := by
  by_cases hvx : v = x
  · subst hvx
    rw [if_pos (Or.inl rfl)]
    have hsplit : pairUnit v y v y +
        ∑ u ∈ Finset.univ.erase y, pairUnit v y v u = mdeg (pairUnit v y) v :=
      Finset.add_sum_erase _ _ (Finset.mem_univ y)
    have h1 : pairUnit v y v y = 1 := by
      unfold pairUnit; rw [if_pos (Or.inl ⟨rfl, rfl⟩)]
    have h0 : ∑ u ∈ Finset.univ.erase y, pairUnit v y v u = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      unfold pairUnit
      rw [if_neg]
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact (Finset.mem_erase.mp hu).1 h
      · exact hxy h
    omega
  · by_cases hvy : v = y
    · subst hvy
      rw [if_pos (Or.inr rfl)]
      have hsplit : pairUnit x v v x +
          ∑ u ∈ Finset.univ.erase x, pairUnit x v v u =
          mdeg (pairUnit x v) v :=
        Finset.add_sum_erase _ _ (Finset.mem_univ x)
      have h1 : pairUnit x v v x = 1 := by
        unfold pairUnit; rw [if_pos (Or.inr ⟨rfl, rfl⟩)]
      have h0 : ∑ u ∈ Finset.univ.erase x, pairUnit x v v u = 0 := by
        refine Finset.sum_eq_zero fun u hu => ?_
        unfold pairUnit
        rw [if_neg]
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hxy h.symm
        · exact (Finset.mem_erase.mp hu).1 h
      omega
    · rw [if_neg (by tauto)]
      refine Finset.sum_eq_zero fun u _ => ?_
      unfold pairUnit
      rw [if_neg]
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hvx h
      · exact hvy h

/-- **Pairing**: every evenly-sized vertex set carries a perfect-matching
matrix (symmetric, loopless, degree 1 exactly on the set). -/
theorem exists_pairing :
    ∀ (s : Finset V), Even #s →
      ∃ p : V → V → ℕ, (∀ u v, p u v = p v u) ∧ (∀ v, p v v = 0) ∧
        (∀ v, mdeg p v = if v ∈ s then 1 else 0) := by
  suffices h : ∀ (k : ℕ) (s : Finset V), #s ≤ k → Even #s →
      ∃ p : V → V → ℕ, (∀ u v, p u v = p v u) ∧ (∀ v, p v v = 0) ∧
        (∀ v, mdeg p v = if v ∈ s then 1 else 0) from
    fun s hs => h #s s le_rfl hs
  intro k
  induction k with
  | zero =>
    intro s hcard _
    have hempty : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hempty
    exact ⟨fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun v => by
      simp [mdeg]⟩
  | succ k ih =>
    intro s hcard heven
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact ⟨fun _ _ => 0, fun _ _ => rfl, fun _ => rfl, fun v => by
        simp [mdeg]⟩
    · -- two distinct elements of s
      have hpos : 0 < #s := Finset.card_pos.mpr ⟨x, hx⟩
      have h2 : 2 ≤ #s := by
        obtain ⟨c, hc⟩ := heven; omega
      have herase : #(s.erase x) = #s - 1 := Finset.card_erase_of_mem hx
      have hpos2 : 0 < #(s.erase x) := by omega
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos2
      obtain ⟨hyx, hys⟩ := Finset.mem_erase.mp hy
      have hxy : x ≠ y := hyx.symm
      -- recurse on s minus the pair
      have hcard' : #((s.erase x).erase y) = #s - 2 := by
        rw [Finset.card_erase_of_mem hy, herase]
        omega
      obtain ⟨p', hsym', hloop', hdeg'⟩ := ih ((s.erase x).erase y)
        (by omega) (by obtain ⟨c, hc⟩ := heven; exact ⟨c - 1, by omega⟩)
      refine ⟨fun u v => p' u v + pairUnit x y u v, ?_, ?_, ?_⟩
      · intro u v; dsimp only; rw [hsym' u v, pairUnit_symm x y u v]
      · intro v; dsimp only; rw [hloop' v, pairUnit_loopless hxy v]
      · intro v
        have hadd : mdeg (fun u v => p' u v + pairUnit x y u v) v =
            mdeg p' v + mdeg (pairUnit x y) v := by
          unfold mdeg; exact Finset.sum_add_distrib
        rw [hadd, hdeg' v, mdeg_pairUnit hxy v]
        by_cases hvx : v = x
        · subst hvx
          rw [if_neg (show v ∉ (s.erase v).erase y from fun h =>
              (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl),
            if_pos (show v = v ∨ v = y from Or.inl rfl), if_pos hx]
        · by_cases hvy : v = y
          · subst hvy
            rw [if_neg (show v ∉ (s.erase x).erase v from fun h =>
                (Finset.mem_erase.mp h).1 rfl),
              if_pos (show v = x ∨ v = v from Or.inr rfl), if_pos hys]
          · rw [if_neg (show ¬(v = x ∨ v = y) from by tauto)]
            by_cases hvs : v ∈ s
            · rw [if_pos (show v ∈ (s.erase x).erase y from
                Finset.mem_erase.mpr ⟨hvy, Finset.mem_erase.mpr ⟨hvx, hvs⟩⟩),
                if_pos hvs]
            · rw [if_neg (show v ∉ (s.erase x).erase y from fun h =>
                hvs (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))),
                if_neg hvs]

/-! ### Restricting a split of an augmented matrix -/

/-- **Restriction** (pretested: `pretest2_shannon.py` P7): a degree-≤ 2
split `s₁ + s₂` of an augmented matrix `m + p` restricts to a degree-≤ 2
split of `m`: take `m₁ = s₁ − min s₁ p` and the rest.  All conditions are
pointwise `min` arithmetic. -/
theorem two_split_restrict {m p s₁ s₂ : V → V → ℕ}
    (hadd : ∀ u v, m u v + p u v = s₁ u v + s₂ u v)
    (hsymm : ∀ u v, m u v = m v u) (hsymp : ∀ u v, p u v = p v u)
    (hsym₁ : ∀ u v, s₁ u v = s₁ v u)
    (hdeg₁ : ∀ v, mdeg s₁ v ≤ 2) (hdeg₂ : ∀ v, mdeg s₂ v ≤ 2) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) := by
  refine ⟨fun u v => s₁ u v - min (s₁ u v) (p u v),
    fun u v => m u v - (s₁ u v - min (s₁ u v) (p u v)), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v; have := hadd u v; dsimp only; omega
  · intro u v; dsimp only; rw [hsym₁ u v, hsymp u v]
  · intro u v; dsimp only; rw [hsymm u v, hsym₁ u v, hsymp u v]
  · intro v
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) (hdeg₁ v)
    dsimp only; omega
  · intro v
    refine le_trans (Finset.sum_le_sum fun u _ => ?_) (hdeg₂ v)
    have := hadd v u; dsimp only; omega

/-! ### Directed matrices: in-degree, unit edges, and small algebra

The even-degree core is closed below WITHOUT Euler circuits: a balanced
("Eulerian") orientation is built by a walk-free mutual induction
(`orient_core`), applied twice — once on `V`, once on the bipartite
double `V ⊕ V` — and the two directions of the second orientation are the
two halves.  Machine-pretested end-to-end:
`lenses/C4L3-lean-close/pretest3_orient.py` P8/P9 (campaign C4). -/

/-- In-degree (column sum) of a directed multiplicity matrix; the
out-degree is the row sum `mdeg`. -/
def indeg (d : V → V → ℕ) (v : V) : ℕ := ∑ u, d u v

/-- An orientation `d` of `m` (`d u v + d v u = m u v`) splits each vertex
degree as out + in. -/
lemma mdeg_add_indeg {m d : V → V → ℕ}
    (hsum : ∀ u v, d u v + d v u = m u v) (v : V) :
    mdeg d v + indeg d v = mdeg m v := by
  show (∑ u, d v u) + ∑ u, d u v = ∑ u, m v u
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => hsum v u

/-- The single directed edge `a → b`. -/
def dirUnit (a b : V) : V → V → ℕ := fun u v => if u = a ∧ v = b then 1 else 0

lemma sum_dirUnit_row (a b v : V) :
    (∑ u, dirUnit a b v u) = if v = a then 1 else 0 := by
  by_cases hva : v = a
  · simp [dirUnit, hva]
  · simp [dirUnit, hva]

lemma sum_dirUnit_col (a b v : V) :
    (∑ u, dirUnit a b u v) = if v = b then 1 else 0 := by
  by_cases hvb : v = b
  · simp [dirUnit, hvb]
  · simp [dirUnit, hvb]

lemma mdeg_add_dirUnit (d : V → V → ℕ) (a b v : V) :
    mdeg (fun u w => d u w + dirUnit a b u w) v =
      mdeg d v + if v = a then 1 else 0 := by
  show (∑ u, (d v u + dirUnit a b v u)) = _
  rw [Finset.sum_add_distrib, sum_dirUnit_row]
  rfl

lemma indeg_add_dirUnit (d : V → V → ℕ) (a b v : V) :
    indeg (fun u w => d u w + dirUnit a b u w) v =
      indeg d v + if v = b then 1 else 0 := by
  show (∑ u, (d u v + dirUnit a b u v)) = _
  rw [Finset.sum_add_distrib, sum_dirUnit_col]
  rfl

lemma pairUnit_comm (a b : V) : ∀ u v, pairUnit a b u v = pairUnit b a u v := by
  intro u v; unfold pairUnit
  by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  · rw [if_pos h, if_pos (by tauto)]
  · rw [if_neg h, if_neg (by tauto)]

/-- The two directions of one undirected unit edge. -/
lemma dirUnit_add_swap {a b : V} (hab : a ≠ b) (u v : V) :
    dirUnit a b u v + dirUnit a b v u = pairUnit a b u v := by
  unfold dirUnit pairUnit
  by_cases h1 : u = a ∧ v = b
  · have h2 : ¬(v = a ∧ u = b) := fun h => hab (h1.1.symm.trans h.2)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1)]
  · by_cases h2 : v = a ∧ u = b
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr ⟨h2.2, h2.1⟩)]
    · rw [if_neg h1, if_neg h2, if_neg ?_]
      rintro (h | ⟨hb, ha⟩)
      · exact h1 h
      · exact h2 ⟨ha, hb⟩

/-- Putting one removed edge back. -/
lemma decr_add_pairUnit {m : V → V → ℕ} {a b : V}
    (hab : 0 < m a b) (hba : 0 < m b a) :
    ∀ u v, decr m a b u v + pairUnit a b u v = m u v := by
  intro u v
  unfold decr pairUnit
  by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  · rw [if_pos h, if_pos h]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · rw [if_neg h, if_neg h]
    omega

/-! ### Balanced orientations (the walk-free Euler engine) -/

/-- **Balanced-orientation engine** (mutual induction on the edge count;
pretested: `pretest3_orient.py` P8).  (A) Every symmetric loopless matrix
with all degrees even has an orientation with in-degree = out-degree at
every vertex.  (B) With odd degrees at exactly two vertices `x ≠ y`, an
orientation with one extra out at `x` and one extra in at `y` — the
formal "open trail from x to y", built edge by edge: case (A) peels any
edge `(a, b)` and closes the trail (B) of the rest; case (B) peels an
edge `(x, c)` at the source and either finishes (`c = y`, rest even) or
continues the trail from `c`. -/
theorem orient_core : ∀ (N : ℕ) (m : V → V → ℕ), ∑ v, mdeg m v ≤ N →
    (∀ u v, m u v = m v u) → (∀ v, m v v = 0) →
    ((∀ v, Even (mdeg m v)) →
      ∃ d : V → V → ℕ, (∀ u v, d u v + d v u = m u v) ∧
        ∀ v, indeg d v = mdeg d v) ∧
    (∀ x y : V, x ≠ y → Odd (mdeg m x) → Odd (mdeg m y) →
      (∀ v, v ≠ x → v ≠ y → Even (mdeg m v)) →
      ∃ d : V → V → ℕ, (∀ u v, d u v + d v u = m u v) ∧
        ∀ v, indeg d v + (if v = x then 1 else 0) =
          mdeg d v + (if v = y then 1 else 0)) := by
  intro N
  induction N with
  | zero =>
    intro m htot _ _
    have hz : ∀ u v, m u v = 0 := by
      intro u v
      have h1 : mdeg m u ≤ ∑ v, mdeg m v :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ u)
      have h2 : m u v ≤ mdeg m u :=
        Finset.single_le_sum (f := fun w => m u w) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ v)
      omega
    constructor
    · intro _
      exact ⟨fun _ _ => 0, fun u v => by have := hz u v; dsimp only; omega,
        fun v => rfl⟩
    · intro x y _ hox _ _
      exfalso
      have h1 : mdeg m x ≤ ∑ v, mdeg m v :=
        Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ x)
      obtain ⟨k, hk⟩ := hox
      omega
  | succ N ih =>
    intro m htot hsym hloop
    constructor
    · -- (A): all degrees even
      intro heven
      by_cases hex : ∃ a b, 0 < m a b
      · obtain ⟨a, b, hab⟩ := hex
        have hne : a ≠ b := by rintro rfl; have := hloop a; omega
        have hba : 0 < m b a := by rw [← hsym a b]; exact hab
        have hdrop := sum_mdeg_decr hne hab hba
        have hda : 0 < mdeg m a :=
          lt_of_lt_of_le hab (Finset.single_le_sum (f := fun u => m a u)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ b))
        have hdb : 0 < mdeg m b :=
          lt_of_lt_of_le hba (Finset.single_le_sum (f := fun u => m b u)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ a))
        have hoa : Odd (mdeg (decr m a b) a) := by
          rw [mdeg_decr_eq_left hne hab]
          obtain ⟨k, hk⟩ := heven a
          exact ⟨k - 1, by omega⟩
        have hob : Odd (mdeg (decr m a b) b) := by
          rw [mdeg_decr_eq_right hne hba]
          obtain ⟨k, hk⟩ := heven b
          exact ⟨k - 1, by omega⟩
        have hev' : ∀ v, v ≠ a → v ≠ b → Even (mdeg (decr m a b) v) := by
          intro v hva hvb
          rw [mdeg_decr_eq_other hva hvb]
          exact heven v
        obtain ⟨d', hsum', hbal'⟩ := (ih (decr m a b) (by omega)
          (decr_symm hsym a b) (decr_loopless hloop a b)).2 a b hne hoa hob hev'
        refine ⟨fun u v => d' u v + dirUnit b a u v, ?_, ?_⟩
        · intro u v
          have hs := hsum' u v
          have hswap := dirUnit_add_swap hne.symm u v
          have hpc := pairUnit_comm a b u v
          have hp := decr_add_pairUnit hab hba u v
          dsimp only
          omega
        · intro v
          rw [indeg_add_dirUnit, mdeg_add_dirUnit]
          exact hbal' v
      · simp only [not_exists, not_lt, Nat.le_zero] at hex
        exact ⟨fun _ _ => 0, fun u v => by have := hex u v; dsimp only; omega,
          fun v => rfl⟩
    · -- (B): the open trail from x to y
      intro x y hxy hox hoy hev
      have hpos : 0 < mdeg m x := by obtain ⟨k, hk⟩ := hox; omega
      have hexc : ∃ c, 0 < m x c := by
        by_contra h
        push_neg at h
        have hz : mdeg m x = 0 :=
          Finset.sum_eq_zero fun u _ => Nat.le_zero.mp (h u)
        omega
      obtain ⟨c, hxc⟩ := hexc
      have hnxc : x ≠ c := by rintro rfl; have := hloop x; omega
      have hcx : 0 < m c x := by rw [← hsym x c]; exact hxc
      have hdrop := sum_mdeg_decr hnxc hxc hcx
      have hdc : 0 < mdeg m c :=
        lt_of_lt_of_le hcx (Finset.single_le_sum (f := fun u => m c u)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ x))
      by_cases hcy : c = y
      · -- the trail closes: the rest is all even
        subst hcy
        have heven' : ∀ v, Even (mdeg (decr m x c) v) := by
          intro v
          by_cases hvx : v = x
          · subst hvx
            rw [mdeg_decr_eq_left hnxc hxc]
            obtain ⟨k, hk⟩ := hox
            exact ⟨k, by omega⟩
          · by_cases hvc : v = c
            · subst hvc
              rw [mdeg_decr_eq_right hnxc hcx]
              obtain ⟨k, hk⟩ := hoy
              exact ⟨k, by omega⟩
            · rw [mdeg_decr_eq_other hvx hvc]
              exact hev v hvx hvc
        obtain ⟨d', hsum', hbal'⟩ := (ih (decr m x c) (by omega)
          (decr_symm hsym x c) (decr_loopless hloop x c)).1 heven'
        refine ⟨fun u v => d' u v + dirUnit x c u v, ?_, ?_⟩
        · intro u v
          have hs := hsum' u v
          have hswap := dirUnit_add_swap hnxc u v
          have hp := decr_add_pairUnit hxc hcx u v
          dsimp only
          omega
        · intro v
          rw [indeg_add_dirUnit, mdeg_add_dirUnit]
          have hb := hbal' v
          omega
      · -- the trail continues from c
        have hoc : Odd (mdeg (decr m x c) c) := by
          rw [mdeg_decr_eq_right hnxc hcx]
          obtain ⟨k, hk⟩ := hev c (Ne.symm hnxc) hcy
          exact ⟨k - 1, by omega⟩
        have hoy' : Odd (mdeg (decr m x c) y) := by
          rw [mdeg_decr_eq_other (Ne.symm hxy) (Ne.symm hcy)]
          exact hoy
        have hev' : ∀ v, v ≠ c → v ≠ y → Even (mdeg (decr m x c) v) := by
          intro v hvc hvy
          by_cases hvx : v = x
          · subst hvx
            rw [mdeg_decr_eq_left hnxc hxc]
            obtain ⟨k, hk⟩ := hox
            exact ⟨k, by omega⟩
          · rw [mdeg_decr_eq_other hvx hvc]
            exact hev v hvx hvy
        obtain ⟨d', hsum', hbal'⟩ := (ih (decr m x c) (by omega)
          (decr_symm hsym x c) (decr_loopless hloop x c)).2 c y hcy hoc hoy' hev'
        refine ⟨fun u v => d' u v + dirUnit x c u v, ?_, ?_⟩
        · intro u v
          have hs := hsum' u v
          have hswap := dirUnit_add_swap hnxc u v
          have hp := decr_add_pairUnit hxc hcx u v
          dsimp only
          omega
        · intro v
          rw [indeg_add_dirUnit, mdeg_add_dirUnit]
          have hb := hbal' v
          omega

/-- **Eulerian (balanced) orientation** of an even loopless multigraph. -/
theorem exists_balanced_orientation (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (heven : ∀ v, Even (mdeg m v)) :
    ∃ d : V → V → ℕ, (∀ u v, d u v + d v u = m u v) ∧
      ∀ v, indeg d v = mdeg d v :=
  (orient_core (∑ v, mdeg m v) m le_rfl hsym hloop).1 heven

/-! ### The bipartite double of an orientation -/

/-- Bipartite double: vertex set `V ⊕ V`, one edge `inl u — inr v` per
directed edge `u → v` of `d`. -/
def biMat (d : V → V → ℕ) : (V ⊕ V) → (V ⊕ V) → ℕ
  | Sum.inl u, Sum.inr v => d u v
  | Sum.inr v, Sum.inl u => d u v
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

lemma biMat_symm (d : V → V → ℕ) : ∀ a b, biMat d a b = biMat d b a := by
  rintro (u | u) (v | v) <;> rfl

lemma biMat_loopless (d : V → V → ℕ) : ∀ a, biMat d a a = 0 := by
  rintro (u | u) <;> rfl

lemma mdeg_biMat_inl (d : V → V → ℕ) (v : V) :
    mdeg (biMat d) (Sum.inl v) = mdeg d v := by
  show (∑ a : V ⊕ V, biMat d (Sum.inl v) a) = ∑ u, d v u
  rw [Fintype.sum_sum_type]
  have h1 : (∑ u : V, biMat d (Sum.inl v) (Sum.inl u)) = 0 :=
    Finset.sum_eq_zero fun u _ => rfl
  have h2 : (∑ u : V, biMat d (Sum.inl v) (Sum.inr u)) = ∑ u, d v u :=
    Finset.sum_congr rfl fun u _ => rfl
  omega

lemma mdeg_biMat_inr (d : V → V → ℕ) (v : V) :
    mdeg (biMat d) (Sum.inr v) = indeg d v := by
  show (∑ a : V ⊕ V, biMat d (Sum.inr v) a) = ∑ u, d u v
  rw [Fintype.sum_sum_type]
  have h1 : (∑ u : V, biMat d (Sum.inr v) (Sum.inl u)) = ∑ u, d u v :=
    Finset.sum_congr rfl fun u _ => rfl
  have h2 : (∑ u : V, biMat d (Sum.inr v) (Sum.inr u)) = 0 :=
    Finset.sum_eq_zero fun u _ => rfl
  omega

/-! ### The even-degree core, CLOSED -/

/-- **The even-degree core** (formerly the open Euler step — now CLOSED,
without Euler circuits): every loopless multigraph with all degrees EVEN
and ≤ 4 splits into two halves of degree ≤ 2.  Proof: balanced-orient `m`
(`orient_core`, degrees become out = in = mdeg/2 ≤ 2); pair the odd
vertices of the bipartite double `biMat d` (`exists_pairing`) and
balanced-orient the augmented double (degrees ≤ 3, so out = in ≤ 1); the
two directions of that orientation classify the edges of `m` into two
halves meeting every vertex ≤ 1 + 1 = 2 times; `two_split_restrict`
removes the pairing shadow.  Machine-pretested end-to-end:
`lenses/C4L3-lean-close/pretest3_orient.py` P9. -/
theorem exists_two_split_even (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) (heven : ∀ v, Even (mdeg m v)) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) := by
  obtain ⟨d, hdsum, hdbal⟩ := exists_balanced_orientation m hsym hloop heven
  have hdhalf : ∀ v, mdeg d v ≤ 2 := by
    intro v
    have h1 := mdeg_add_indeg hdsum v
    have h2 := hdbal v
    have h3 := hdeg v
    omega
  have hihalf : ∀ v, indeg d v ≤ 2 := by
    intro v
    have h1 := hdbal v
    have h2 := hdhalf v
    omega
  -- pair the odd vertices of the bipartite double
  obtain ⟨p, hpsym, hploop, hpdeg⟩ := exists_pairing
    (Finset.univ.filter fun w : V ⊕ V => Odd (mdeg (biMat d) w))
    (even_card_odd_mdeg (biMat d) (biMat_symm d) (biMat_loopless d))
  have hpdeg' : ∀ w, mdeg p w =
      if Odd (mdeg (biMat d) w) then 1 else 0 := by
    intro w
    rw [hpdeg w]
    by_cases h : Odd (mdeg (biMat d) w)
    · have hmem : w ∈ Finset.univ.filter
          fun w : V ⊕ V => Odd (mdeg (biMat d) w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ w, h⟩
      rw [if_pos hmem, if_pos h]
    · have hmem : w ∉ Finset.univ.filter
          fun w : V ⊕ V => Odd (mdeg (biMat d) w) :=
        fun hmem => h (Finset.mem_filter.mp hmem).2
      rw [if_neg hmem, if_neg h]
  have hBpadd : ∀ w, mdeg (fun a b => biMat d a b + p a b) w =
      mdeg (biMat d) w + mdeg p w := by
    intro w
    show (∑ a, (biMat d w a + p w a)) = _
    rw [Finset.sum_add_distrib]
    rfl
  -- balanced orientation of the augmented (all-even) double
  obtain ⟨D, hDsum, hDbal⟩ := exists_balanced_orientation
    (fun a b => biMat d a b + p a b)
    (fun a b => by dsimp only; rw [biMat_symm d a b, hpsym a b])
    (fun a => by dsimp only; rw [biMat_loopless d a, hploop a])
    (fun w => by
      rw [hBpadd w, hpdeg' w]
      rcases Nat.even_or_odd (mdeg (biMat d) w) with h | h
      · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h)]
        obtain ⟨k, hk⟩ := h
        exact ⟨k, by omega⟩
      · rw [if_pos h]
        obtain ⟨k, hk⟩ := h
        exact ⟨k + 1, by omega⟩)
  -- per-vertex bound on the double orientation: out = in ≤ 1
  have hDtot : ∀ w, mdeg D w + indeg D w = mdeg (biMat d) w + mdeg p w := by
    intro w
    have h1 : ∀ a, D w a + D a w = biMat d w a + p w a := fun a => hDsum w a
    show (∑ a, D w a) + ∑ a, D a w = (∑ a, biMat d w a) + ∑ a, p w a
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => h1 a
  have hD1 : ∀ w, mdeg D w ≤ 1 := by
    intro w
    have h1 := hDtot w
    have h2 := hDbal w
    have h4 := hpdeg' w
    have h5 : mdeg (biMat d) w ≤ 2 := by
      rcases w with v | v
      · rw [mdeg_biMat_inl]; exact hdhalf v
      · rw [mdeg_biMat_inr]; exact hihalf v
    by_cases ho : Odd (mdeg (biMat d) w)
    · rw [if_pos ho] at h4; omega
    · rw [if_neg ho] at h4; omega
  have hD1' : ∀ w, indeg D w ≤ 1 := by
    intro w
    have h1 := hDbal w
    have h2 := hD1 w
    omega
  -- the two halves and the pairing shadow
  have hadd : ∀ u v,
      m u v + (p (Sum.inl u) (Sum.inr v) + p (Sum.inl v) (Sum.inr u)) =
      (D (Sum.inl u) (Sum.inr v) + D (Sum.inl v) (Sum.inr u)) +
      (D (Sum.inr v) (Sum.inl u) + D (Sum.inr u) (Sum.inl v)) := by
    intro u v
    have h1 := hDsum (Sum.inl u) (Sum.inr v)
    have h2 := hDsum (Sum.inl v) (Sum.inr u)
    have hb1 : biMat d (Sum.inl u) (Sum.inr v) = d u v := rfl
    have hb2 : biMat d (Sum.inl v) (Sum.inr u) = d v u := rfl
    have h3 := hdsum u v
    omega
  refine two_split_restrict
    (m := m)
    (p := fun u v => p (Sum.inl u) (Sum.inr v) + p (Sum.inl v) (Sum.inr u))
    (s₁ := fun u v => D (Sum.inl u) (Sum.inr v) + D (Sum.inl v) (Sum.inr u))
    (s₂ := fun u v => D (Sum.inr v) (Sum.inl u) + D (Sum.inr u) (Sum.inl v))
    hadd hsym ?_ ?_ ?_ ?_
  · intro u v; dsimp only; omega
  · intro u v; dsimp only; omega
  · -- degree bound on the first half
    intro v
    have hsplit : mdeg (fun u w => D (Sum.inl u) (Sum.inr w) +
        D (Sum.inl w) (Sum.inr u)) v =
        (∑ u, D (Sum.inl v) (Sum.inr u)) + ∑ u, D (Sum.inl u) (Sum.inr v) := by
      show (∑ u, (D (Sum.inl v) (Sum.inr u) + D (Sum.inl u) (Sum.inr v))) = _
      rw [Finset.sum_add_distrib]
    have hle1 : (∑ u, D (Sum.inl v) (Sum.inr u)) ≤ mdeg D (Sum.inl v) := by
      show _ ≤ ∑ a : V ⊕ V, D (Sum.inl v) a
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_left _ _
    have hle2 : (∑ u, D (Sum.inl u) (Sum.inr v)) ≤ indeg D (Sum.inr v) := by
      show _ ≤ ∑ a : V ⊕ V, D a (Sum.inr v)
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_right _ _
    have h1 := hD1 (Sum.inl v)
    have h2 := hD1' (Sum.inr v)
    omega
  · -- degree bound on the second half
    intro v
    have hsplit : mdeg (fun u w => D (Sum.inr w) (Sum.inl u) +
        D (Sum.inr u) (Sum.inl w)) v =
        (∑ u, D (Sum.inr u) (Sum.inl v)) + ∑ u, D (Sum.inr v) (Sum.inl u) := by
      show (∑ u, (D (Sum.inr u) (Sum.inl v) + D (Sum.inr v) (Sum.inl u))) = _
      rw [Finset.sum_add_distrib]
    have hle1 : (∑ u, D (Sum.inr u) (Sum.inl v)) ≤ indeg D (Sum.inl v) := by
      show _ ≤ ∑ a : V ⊕ V, D a (Sum.inl v)
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_left _ _
    have hle2 : (∑ u, D (Sum.inr v) (Sum.inl u)) ≤ mdeg D (Sum.inr v) := by
      show _ ≤ ∑ a : V ⊕ V, D (Sum.inr v) a
      rw [Fintype.sum_sum_type]
      exact Nat.le_add_right _ _
    have h1 := hD1' (Sum.inl v)
    have h2 := hD1 (Sum.inr v)
    omega

/-- **The augmentation reduction**: if every even loopless multigraph with
Δ ≤ 4 2-splits (`exists_two_split_even`), then every loopless multigraph
with Δ ≤ 4 2-splits (`exists_two_split`) — pair the odd-degree vertices
(evenly many, `even_card_odd_mdeg`/`exists_pairing`), split the augmented
even matrix, and restrict (`two_split_restrict`). -/
theorem two_split_of_even_split_hypothesis
    (heven_split : ∀ M : V → V → ℕ, (∀ u v, M u v = M v u) →
      (∀ v, M v v = 0) → (∀ v, mdeg M v ≤ 4) → (∀ v, Even (mdeg M v)) →
      ∃ s₁ s₂ : V → V → ℕ, (∀ u v, M u v = s₁ u v + s₂ u v) ∧
        (∀ u v, s₁ u v = s₁ v u) ∧ (∀ u v, s₂ u v = s₂ v u) ∧
        (∀ v, mdeg s₁ v ≤ 2) ∧ (∀ v, mdeg s₂ v ≤ 2))
    (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) := by
  -- pair the odd-degree vertices
  obtain ⟨p, hsymp, hloopp, hdegp⟩ := exists_pairing
    (Finset.univ.filter fun v => Odd (mdeg m v))
    (even_card_odd_mdeg m hsym hloop)
  have hdegp' : ∀ v, mdeg p v = if Odd (mdeg m v) then 1 else 0 := by
    intro v
    rw [hdegp v]
    by_cases h : Odd (mdeg m v)
    · rw [if_pos (show v ∈ Finset.univ.filter (fun w => Odd (mdeg m w)) from
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩), if_pos h]
    · rw [if_neg (show v ∉ Finset.univ.filter (fun w => Odd (mdeg m w)) from
        fun hmem => h (Finset.mem_filter.mp hmem).2), if_neg h]
  -- the augmented matrix is even with degrees ≤ 4
  have hmdeg_add : ∀ v, mdeg (fun u w => m u w + p u w) v =
      mdeg m v + mdeg p v := by
    intro v; unfold mdeg; exact Finset.sum_add_distrib
  obtain ⟨s₁, s₂, hadd, hsym₁, hsym₂, hdeg₁, hdeg₂⟩ :=
    heven_split (fun u w => m u w + p u w)
      (fun u w => by dsimp only; rw [hsym u w, hsymp u w])
      (fun v => by dsimp only; rw [hloop v, hloopp v])
      (fun v => by
        rw [hmdeg_add v, hdegp' v]
        rcases Nat.even_or_odd (mdeg m v) with h | h
        · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h)]
          have := hdeg v; omega
        · rw [if_pos h]
          obtain ⟨k, hk⟩ := h
          have := hdeg v; omega)
      (fun v => by
        rw [hmdeg_add v, hdegp' v]
        rcases Nat.even_or_odd (mdeg m v) with h | h
        · rw [if_neg (by simpa [Nat.not_odd_iff_even] using h)]
          obtain ⟨c, hc⟩ := h
          exact ⟨c, by omega⟩
        · rw [if_pos h]
          obtain ⟨k, hk⟩ := h
          exact ⟨k + 1, by omega⟩)
  exact two_split_restrict (fun u v => hadd u v) hsym hsymp hsym₁
    hdeg₁ hdeg₂

/-- **The Euler 2-split, CLOSED** (campaign C4; was
`proof_wanted exists_two_split` in `SMaj/Six/Shannon.lean`): every
loopless multigraph with Δ ≤ 4 splits into two spanning sub-multigraphs
of degree ≤ 2.  With `shannon_six_of_split_hypothesis` this closes
Shannon's bound at Δ = 4 (`shannon_six_of_maxDegree_four`,
`SMaj/Six/Targets.lean`) — the ≤ 6 proof's last open mathematical
input. -/
theorem exists_two_split (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u)
    (hloop : ∀ v, m v v = 0) (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
      (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
      (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2) :=
  two_split_of_even_split_hypothesis
    (fun M hs hl hd he => exists_two_split_even M hs hl hd he)
    m hsym hloop hdeg

end SMaj
