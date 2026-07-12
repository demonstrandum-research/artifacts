/-
SMaj/Six/Shannon.lean — the multigraph edge-coloring engine of the (G3)
step, restructuring the ≤ 6 proof's sole external input.

Multigraphs are loopless symmetric multiplicity matrices `m : V → V → ℕ`
with vertex degree `mdeg m v = ∑ u, m v u`; a proper coloring (matching
`shannon_six_of_maxDegree_four` in `SMaj/Six/Targets.lean`) assigns each
parallel class a set of `m u v` distinct colors, classes at a common
vertex disjoint (`IsMulticoloring`).

CLOSED here (sorry-free, kernel-audited):

* `exists_multicoloring_of_le` — **the greedy bound χ′ ≤ 2D − 1** for
  every loopless multigraph with all degrees ≤ D, by induction on the
  edge count (machine-pretested shape: `pretest2_shannon.py` P4).
* `exists_seven_coloring_of_mdeg_le_four` — Δ ≤ 4 ⇒ 7 colors,
  UNCONDITIONALLY: the (G3) step of the L2 construction needs no
  external input at palette 7 (and rows/fill of this library already
  work at any palette ≥ 5), so the future glue gives a fully formal
  `Maj′ ≤ 7` with no open mathematical inputs.
* `exists_three_coloring_of_mdeg_le_two` — Δ ≤ 2 ⇒ 3 colors (the same
  greedy lemma at D = 2; for Δ ≤ 2 the greedy bound IS Shannon's bound).
* `IsMulticoloring.combine` — palette sum: 3-colorings of two halves
  combine to a 6-coloring of their sum (disjoint palette embedding).
* `shannon_six_of_split` / `shannon_six_of_split_hypothesis` — **Shannon
  at Δ = 4 reduced to the Euler 2-split**: if `m = m₁ + m₂` with
  `mdeg mᵢ ≤ 2` then χ′(m) ≤ 6; hence the full
  `shannon_six_of_maxDegree_four` statement follows from
  `exists_two_split` alone (closed implication, no other inputs).

UPDATE (campaign C4, lens C4L3-lean-close, 2026-06-13): the formerly
open `exists_two_split` is now a THEOREM (`SMaj/Six/Euler.lean`, via
walk-free balanced orientations).  Shannon at Δ = 4 is therefore fully
closed: see `shannon_six_of_maxDegree_four` in `SMaj/Six/Targets.lean`.

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12.
-/
import Mathlib

namespace SMaj

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Multigraphs as multiplicity matrices -/

/-- Degree of `v` in the multiplicity matrix `m`. -/
def mdeg (m : V → V → ℕ) (v : V) : ℕ := ∑ u, m v u

/-- `φ` is a proper edge multicoloring of `m`: symmetric, the parallel
class `{u,v}` carries `m u v` distinct colors, and classes at a common
vertex are pairwise disjoint.  This is exactly the conclusion shape of
`shannon_six_of_maxDegree_four` (`SMaj/Six/Targets.lean`). -/
def IsMulticoloring {C : Type*} (m : V → V → ℕ) (φ : V → V → Finset C) : Prop :=
  (∀ u v, φ u v = φ v u) ∧ (∀ u v, #(φ u v) = m u v) ∧
    (∀ u v w, v ≠ w → Disjoint (φ u v) (φ u w))

/-- The all-empty coloring is proper for the zero matrix. -/
lemma isMulticoloring_of_zero {C : Type*} {m : V → V → ℕ}
    (hz : ∀ u v, m u v = 0) :
    IsMulticoloring m (fun _ _ => (∅ : Finset C)) :=
  ⟨fun _ _ => rfl, fun u v => by simp [hz], fun _ _ _ _ => by simp⟩

/-- The colors present at a vertex `a` form exactly `mdeg m a` colors. -/
lemma card_biUnion_eq_mdeg {C : Type*} [DecidableEq C] {m : V → V → ℕ}
    {φ : V → V → Finset C} (h : IsMulticoloring m φ) (a : V) :
    #(Finset.univ.biUnion fun w => φ a w) = mdeg m a := by
  rw [Finset.card_biUnion fun x _ y _ hxy => h.2.2 a x y hxy]
  exact Finset.sum_congr rfl fun w _ => h.2.1 a w

/-! ### Decrementing one parallel class -/

/-- `m` with the parallel class `{a,b}` decremented by one. -/
def decr (m : V → V → ℕ) (a b : V) : V → V → ℕ := fun u v =>
  if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then m u v - 1 else m u v

lemma decr_le (m : V → V → ℕ) (a b u v : V) : decr m a b u v ≤ m u v := by
  unfold decr; split <;> omega

lemma decr_ab (m : V → V → ℕ) (a b : V) : decr m a b a b = m a b - 1 := by
  unfold decr; rw [if_pos (Or.inl ⟨rfl, rfl⟩)]

lemma decr_ba (m : V → V → ℕ) (a b : V) : decr m a b b a = m b a - 1 := by
  unfold decr; rw [if_pos (Or.inr ⟨rfl, rfl⟩)]

lemma decr_of_ne (m : V → V → ℕ) {a b u v : V}
    (h : ¬((u = a ∧ v = b) ∨ (u = b ∧ v = a))) : decr m a b u v = m u v := by
  unfold decr; rw [if_neg h]

lemma decr_symm {m : V → V → ℕ} (hsym : ∀ u v, m u v = m v u) (a b : V) :
    ∀ u v, decr m a b u v = decr m a b v u := by
  intro u v; unfold decr
  by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
  · rw [if_pos h, if_pos (by tauto), hsym]
  · rw [if_neg h, if_neg (by tauto), hsym]

lemma decr_loopless {m : V → V → ℕ} (hloop : ∀ v, m v v = 0) (a b : V) :
    ∀ v, decr m a b v v = 0 := by
  intro v; have := hloop v; unfold decr; split <;> omega

lemma mdeg_decr_le (m : V → V → ℕ) (a b v : V) :
    mdeg (decr m a b) v ≤ mdeg m v :=
  Finset.sum_le_sum fun u _ => decr_le m a b v u

lemma mdeg_decr_lt_left {m : V → V → ℕ} {a b : V} (hab : 0 < m a b) :
    mdeg (decr m a b) a < mdeg m a :=
  Finset.sum_lt_sum (fun u _ => decr_le m a b a u)
    ⟨b, Finset.mem_univ b, by rw [decr_ab]; omega⟩

lemma mdeg_decr_lt_right {m : V → V → ℕ} {a b : V} (hba : 0 < m b a) :
    mdeg (decr m a b) b < mdeg m b :=
  Finset.sum_lt_sum (fun u _ => decr_le m a b b u)
    ⟨a, Finset.mem_univ a, by rw [decr_ba]; omega⟩

/-! ### The greedy bound χ′ ≤ 2D − 1 -/

/-- **Greedy multigraph edge coloring** (induction core): every loopless
symmetric multiplicity matrix with all degrees ≤ D has a proper
edge coloring with k colors whenever 2D ≤ k + 1 (i.e. k ≥ 2D − 1): an
uncolored parallel edge at `{a,b}` sees at most (D−1) colors at `a` and
(D−1) at `b`, and 2D − 2 < k.  Pretested shape: `pretest2_shannon.py`
P4 (invariant asserted at every extension step, 2,880 colorings). -/
theorem exists_multicoloring_of_le {k D : ℕ} (hkD : 2 * D ≤ k + 1) :
    ∀ N (m : V → V → ℕ), ∑ v, mdeg m v ≤ N →
      (∀ u v, m u v = m v u) → (∀ v, m v v = 0) → (∀ v, mdeg m v ≤ D) →
      ∃ φ : V → V → Finset (Fin k), IsMulticoloring m φ := by
  intro N
  induction N with
  | zero =>
    intro m htot _ _ _
    refine ⟨fun _ _ => ∅, isMulticoloring_of_zero ?_⟩
    intro u v
    have h1 : mdeg m u ≤ ∑ v, mdeg m v :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ u)
    have h2 : m u v ≤ mdeg m u :=
      Finset.single_le_sum (f := fun w => m u w) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ v)
    omega
  | succ N ih =>
    intro m htot hsym hloop hdeg
    by_cases hex : ∃ a b, 0 < m a b
    · obtain ⟨a, b, hab⟩ := hex
      have hba : 0 < m b a := by rw [← hsym a b]; exact hab
      -- the decremented matrix
      have htot' : ∑ v, mdeg (decr m a b) v ≤ N := by
        have hlt : ∑ v, mdeg (decr m a b) v < ∑ v, mdeg m v :=
          Finset.sum_lt_sum (fun v _ => mdeg_decr_le m a b v)
            ⟨a, Finset.mem_univ a, mdeg_decr_lt_left hab⟩
        omega
      obtain ⟨φ', hφ'⟩ := ih (decr m a b) htot' (decr_symm hsym a b)
        (decr_loopless hloop a b)
        (fun v => le_trans (mdeg_decr_le m a b v) (hdeg v))
      obtain ⟨hsymφ, hcardφ, hdisjφ⟩ := hφ'
      -- a fresh color outside both endpoint palettes
      have hSa : #(Finset.univ.biUnion fun w => φ' a w) + 1 ≤ D := by
        have := card_biUnion_eq_mdeg ⟨hsymφ, hcardφ, hdisjφ⟩ a
        have := mdeg_decr_lt_left (m := m) hab
        have := hdeg a
        omega
      have hSb : #(Finset.univ.biUnion fun w => φ' b w) + 1 ≤ D := by
        have := card_biUnion_eq_mdeg ⟨hsymφ, hcardφ, hdisjφ⟩ b
        have := mdeg_decr_lt_right (m := m) hba
        have := hdeg b
        omega
      have hfree : ∃ x : Fin k,
          x ∉ (Finset.univ.biUnion fun w => φ' a w) ∪
              (Finset.univ.biUnion fun w => φ' b w) := by
        have hcard := Finset.card_union_le
          (Finset.univ.biUnion fun w => φ' a w)
          (Finset.univ.biUnion fun w => φ' b w)
        have hne : (((Finset.univ.biUnion fun w => φ' a w) ∪
            (Finset.univ.biUnion fun w => φ' b w))ᶜ).Nonempty := by
          rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
          omega
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, Finset.mem_compl.mp hx⟩
      obtain ⟨x, hx⟩ := hfree
      have hxa : ∀ w, x ∉ φ' a w := fun w hmem =>
        hx (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, hmem⟩))
      have hxb : ∀ w, x ∉ φ' b w := fun w hmem =>
        hx (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, hmem⟩))
      -- extend φ' by x on the class {a,b}
      refine ⟨fun u v => φ' u v ∪
        (if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then {x} else ∅), ?_, ?_, ?_⟩
      · -- symmetry
        intro u v; dsimp only
        rw [hsymφ u v]
        congr 1
        by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
        · rw [if_pos h, if_pos (by tauto)]
        · rw [if_neg h, if_neg (by tauto)]
      · -- cardinality
        intro u v; dsimp only
        by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
        · have hxuv : x ∉ φ' u v := by
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa v
            · exact hxb v
          rw [if_pos h, Finset.union_comm, Finset.singleton_union,
            Finset.card_insert_of_notMem hxuv, hcardφ]
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [decr_ab]; omega
          · rw [decr_ba]; omega
        · rw [if_neg h, Finset.union_empty, hcardφ, decr_of_ne m h]
      · -- disjointness at every vertex
        intro u v w hvw; dsimp only
        rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
          Finset.disjoint_union_right]
        refine ⟨⟨hdisjφ u v w hvw, ?_⟩, ?_, ?_⟩
        · -- old class (u,v) vs new singleton at (u,w)
          split_ifs with h
          · rw [Finset.disjoint_singleton_right]
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa v
            · exact hxb v
          · exact Finset.disjoint_empty_right _
        · -- new singleton at (u,v) vs old class (u,w)
          split_ifs with h
          · rw [Finset.disjoint_singleton_left]
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa w
            · exact hxb w
          · exact Finset.disjoint_empty_left _
        · -- the two singletons cannot both be present (v ≠ w)
          split_ifs with h1 h2
          · exfalso
            apply hvw
            rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
              rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
            · exact h1b.trans h2b.symm
            · exact h1b.trans (((h1a.symm.trans h2a).symm).trans h2b.symm)
            · exact h1b.trans (((h1a.symm.trans h2a).symm).trans h2b.symm)
            · exact h1b.trans h2b.symm
          · exact Finset.disjoint_empty_right _
          · exact Finset.disjoint_empty_left _
          · exact Finset.disjoint_empty_left _
    · -- no edge left: the zero matrix
      simp only [not_exists, not_lt, Nat.le_zero] at hex
      exact ⟨fun _ _ => ∅, isMulticoloring_of_zero hex⟩

/-- **Δ ≤ 4 ⇒ χ′ ≤ 7, unconditional** (greedy at D = 4): the (G3)
multigraph-coloring step of the ≤ 6 construction needs NO external input
at palette 7.  Since the row analysis (`SMaj/Six/Rows.lean`) and the fill
(`SMaj/Six/Fill.lean`, any palette ≥ 5) are palette-generic, this pins a
fully-formal-reachable `Maj′ ≤ 7` — already better than the published 8. -/
theorem exists_seven_coloring_of_mdeg_le_four (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ φ : V → V → Finset (Fin 7), IsMulticoloring m φ :=
  exists_multicoloring_of_le (by omega) (∑ v, mdeg m v) m le_rfl hsym hloop hdeg

/-- **Δ ≤ 2 ⇒ χ′ ≤ 3** (greedy at D = 2; for Δ ≤ 2 the greedy bound is
exactly Shannon's ⌊3Δ/2⌋).  One half of the 2-split route to 6. -/
theorem exists_three_coloring_of_mdeg_le_two (m : V → V → ℕ)
    (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 2) :
    ∃ φ : V → V → Finset (Fin 3), IsMulticoloring m φ :=
  exists_multicoloring_of_le (by omega) (∑ v, mdeg m v) m le_rfl hsym hloop hdeg

/-! ### Combining palettes: 3 + 3 → 6 -/

/-- `Fin 3 ↪ Fin 6` onto colors {0,1,2}. -/
def loEmb : Fin 3 ↪ Fin 6 :=
  ⟨fun i => ⟨i.1, by omega⟩, fun i j h => by
    have h' : (i : ℕ) = (j : ℕ) := by simpa using h
    exact Fin.ext h'⟩

/-- `Fin 3 ↪ Fin 6` onto colors {3,4,5}. -/
def hiEmb : Fin 3 ↪ Fin 6 :=
  ⟨fun i => ⟨i.1 + 3, by omega⟩, fun i j h => by
    have h' : (i : ℕ) = (j : ℕ) := by simpa using h
    exact Fin.ext h'⟩

/-- The two palette copies are disjoint. -/
lemma disjoint_loEmb_hiEmb (s t : Finset (Fin 3)) :
    Disjoint (s.map loEmb) (t.map hiEmb) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, -, hj⟩ := Finset.mem_map.mp hy
  have h1 : (loEmb i).val = i.val := rfl
  have h2 : (hiEmb j).val = j.val + 3 := rfl
  have := congrArg Fin.val hj
  have hi3 := i.2
  omega

/-- Mapping by an embedding preserves disjointness. -/
lemma disjoint_map_emb {α β : Type*} (f : α ↪ β) {s t : Finset α}
    (h : Disjoint s t) : Disjoint (s.map f) (t.map f) := by
  rw [Finset.disjoint_left] at h ⊢
  rintro x hx hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨j, hj, hje⟩ := Finset.mem_map.mp hy
  exact h hi (f.injective hje ▸ hj)

/-- **Palette sum**: proper 3-colorings of two halves combine — on the
disjoint palettes {0,1,2} and {3,4,5} — to a proper 6-coloring of the
pointwise sum.  Pretested: `pretest2_shannon.py` P6 (989 instances). -/
theorem IsMulticoloring.combine {m₁ m₂ : V → V → ℕ}
    {φ₁ φ₂ : V → V → Finset (Fin 3)}
    (h₁ : IsMulticoloring m₁ φ₁) (h₂ : IsMulticoloring m₂ φ₂) :
    IsMulticoloring (fun u v => m₁ u v + m₂ u v)
      (fun u v => (φ₁ u v).map loEmb ∪ (φ₂ u v).map hiEmb) := by
  obtain ⟨hs₁, hc₁, hd₁⟩ := h₁
  obtain ⟨hs₂, hc₂, hd₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · intro u v; dsimp only
    rw [hs₁ u v, hs₂ u v]
  · intro u v; dsimp only
    rw [Finset.card_union_of_disjoint (disjoint_loEmb_hiEmb _ _),
      Finset.card_map, Finset.card_map, hc₁, hc₂]
  · intro u v w hvw; dsimp only
    rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
      Finset.disjoint_union_right]
    exact ⟨⟨disjoint_map_emb _ (hd₁ u v w hvw), disjoint_loEmb_hiEmb _ _⟩,
      (disjoint_loEmb_hiEmb _ _).symm, disjoint_map_emb _ (hd₂ u v w hvw)⟩

/-! ### Shannon at Δ = 4, reduced to the Euler 2-split -/

/-- **Shannon's bound at Δ ≤ 4 from a 2-split**: if `m = m₁ + m₂` with
both halves of degree ≤ 2, then `m` has a proper 6-edge-coloring
(3 greedy colors per half on disjoint palettes).  Closed implication. -/
theorem shannon_six_of_split (m m₁ m₂ : V → V → ℕ)
    (hadd : ∀ u v, m u v = m₁ u v + m₂ u v)
    (hsym₁ : ∀ u v, m₁ u v = m₁ v u) (hsym₂ : ∀ u v, m₂ u v = m₂ v u)
    (hloop₁ : ∀ v, m₁ v v = 0) (hloop₂ : ∀ v, m₂ v v = 0)
    (hdeg₁ : ∀ v, mdeg m₁ v ≤ 2) (hdeg₂ : ∀ v, mdeg m₂ v ≤ 2) :
    ∃ φ : V → V → Finset (Fin 6), IsMulticoloring m φ := by
  obtain ⟨φ₁, h₁⟩ := exists_three_coloring_of_mdeg_le_two m₁ hsym₁ hloop₁ hdeg₁
  obtain ⟨φ₂, h₂⟩ := exists_three_coloring_of_mdeg_le_two m₂ hsym₂ hloop₂ hdeg₂
  obtain ⟨hs, hc, hd⟩ := h₁.combine h₂
  exact ⟨fun u v => (φ₁ u v).map loEmb ∪ (φ₂ u v).map hiEmb,
    hs, fun u v => by rw [hc u v, hadd], hd⟩

/- **The Euler 2-split** (the formerly open obligation; replaced
Shannon's theorem as the ≤ 6 proof's sole external input): every loopless
multigraph with Δ ≤ 4 splits into two spanning sub-multigraphs of degree
≤ 2.  Classical proof: pair the (evenly many) odd-degree vertices by new
edges so all degrees lie in {2,4}; per component take an Euler circuit and
2-color its edges alternately, starting an odd-length circuit at a
degree-2 vertex (one exists: degrees in {2,4} with odd edge count force
one); each visit then contributes one edge to each half.  Machine-tested:
`pretest2_shannon.py` P5 (1,189/1,189: exhaustive n ≤ 4 + Euler
construction on random n ≤ 12).
UPDATE (campaign C4, lens C4L3-lean-close, 2026-06-13): this is now a
THEOREM — `exists_two_split` in `SMaj/Six/Euler.lean`, proved via
walk-free balanced orientations, no open inputs. -/

/-- **Shannon at Δ ≤ 4, conditional form**: the exact statement of
`shannon_six_of_maxDegree_four` (`SMaj/Six/Targets.lean`) follows from
the 2-split hypothesis alone.  The hypothesis is discharged by
`exists_two_split` (`SMaj/Six/Euler.lean`), closing Shannon at Δ = 4. -/
theorem shannon_six_of_split_hypothesis
    (hsplit : ∀ m : V → V → ℕ, (∀ u v, m u v = m v u) → (∀ v, m v v = 0) →
      (∀ v, mdeg m v ≤ 4) →
      ∃ m₁ m₂ : V → V → ℕ, (∀ u v, m u v = m₁ u v + m₂ u v) ∧
        (∀ u v, m₁ u v = m₁ v u) ∧ (∀ u v, m₂ u v = m₂ v u) ∧
        (∀ v, mdeg m₁ v ≤ 2) ∧ (∀ v, mdeg m₂ v ≤ 2))
    (m : V → V → ℕ) (hsym : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, mdeg m v ≤ 4) :
    ∃ φ : V → V → Finset (Fin 6),
      (∀ u v, φ u v = φ v u) ∧ (∀ u v, #(φ u v) = m u v) ∧
      (∀ u v w, v ≠ w → Disjoint (φ u v) (φ u w)) := by
  obtain ⟨m₁, m₂, hadd, hsym₁, hsym₂, hdeg₁, hdeg₂⟩ :=
    hsplit m hsym hloop hdeg
  have hloop₁ : ∀ v, m₁ v v = 0 := fun v => by
    have h1 := hadd v v; have h2 := hloop v; omega
  have hloop₂ : ∀ v, m₂ v v = 0 := fun v => by
    have h1 := hadd v v; have h2 := hloop v; omega
  exact shannon_six_of_split m m₁ m₂ hadd hsym₁ hsym₂ hloop₁ hloop₂
    hdeg₁ hdeg₂

end SMaj
