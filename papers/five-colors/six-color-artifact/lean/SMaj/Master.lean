/-
SMaj/Master.lean — the Master Theorem (THEOREMS.md §3) in Lean.

Fully proved here:
* `master_coloring` — the coloring form: a coloring rainbow on a grouping with
  g(v) ≤ h_s(d(v)) is strong majority whenever every edge satisfies CRIT_s.
* `admissible_of_crit` — CRIT_s (s ≥ 2) implies admissibility.
* `corA_coloring` — the Corollary-A instantiation (no degrees 2 or 4, s = 3).
* `master_of_inputs` — the full Master Theorem conditional on the two
  existence inputs, each isolated as a named statement below.

Also proved here (campaign C5, lens C5L3-lean-six, 2026-06-13):
* `exists_even_grouping` — partition the edges at each vertex into
  h_s(d(v)) groups of size ≤ s (the even-split construction `evenIx`:
  index the incident edges by `Finset.equivFin` and group by index
  division — CLOSED, was a `proof_wanted`).

Open obligation (stated as `proof_wanted`, keeping the library sorry-free):
* `rainbow_of_groupSizes` — a rainbow (s+1)-coloring exists when all groups
  have size ≤ s.  This is Vizing's theorem for the split graph G* (Δ(G*) ≤ s,
  G* simple — THEOREMS.md Lemmas 2–3).  Vizing's theorem is NOT in mathlib
  v4.30.0 (checked 2026-06-12) and still absent from master (GitHub code
  search grep-clean for `Vizing`, re-checked 2026-06-13); this is the
  bridgehead's single external gap.
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Arith

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

/-- **Master Theorem, coloring form** (THEOREMS.md §3, fully proved): if `c`
is rainbow on a grouping `ix` whose group counts obey g(v) ≤ h_s(d(v)), and
every edge of `G` satisfies CRIT_s, then `c` is a strong majority coloring. -/
theorem master_coloring (s : ℕ) (ix : V → Sym2 V → ℕ) (c : Sym2 V → C)
    (hrb : IsRainbow G ix c)
    (hg : ∀ v : V, groups G ix v ≤ hfun s (G.degree v))
    (hcrit : ∀ u v : V, G.Adj u v → Crit s (G.degree u) (G.degree v)) :
    IsStrongMajority G c := by
  intro u v huv α
  calc nColor G c u v α
      ≤ groups G ix u + groups G ix v := counting_lemma hrb huv α
    _ ≤ hfun s (G.degree u) + hfun s (G.degree v) :=
        Nat.add_le_add (hg u) (hg v)
    _ ≤ (G.degree u + G.degree v - 2) / 2 := hcrit u v huv

/-- CRIT_s (any s ≥ 2) excludes the inadmissible pair (1,2): graphs satisfying
the Master Theorem's hypothesis are automatically admissible. -/
theorem admissible_of_crit (s : ℕ) (hs : 2 ≤ s)
    (hcrit : ∀ u v : V, G.Adj u v → Crit s (G.degree u) (G.degree v)) :
    Admissible G := fun u v huv =>
  crit_admissible hs ((G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩)
    ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩) (hcrit u v huv)

/-- Corollary A, coloring form: if no vertex has degree 2 or 4 and `c` is
rainbow on a grouping with g(v) ≤ h_3(d(v)) — e.g. an even grouping into
triples-and-pairs — then `c` is strong majority.  (With the two existence
inputs below this gives Maj′(G) ≤ 4 on that class.) -/
theorem corA_coloring (ix : V → Sym2 V → ℕ) (c : Sym2 V → C)
    (hrb : IsRainbow G ix c)
    (hg : ∀ v : V, groups G ix v ≤ hfun 3 (G.degree v))
    (hdeg : ∀ v : V, G.degree v ≠ 2 ∧ G.degree v ≠ 4) :
    IsStrongMajority G c :=
  master_coloring 3 ix c hrb hg fun u v huv =>
    crit3_of_no24 ((G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩)
      ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩)
      (hdeg u).1 (hdeg u).2 (hdeg v).1 (hdeg v).2

variable (G) in
/-- Every group of the grouping `ix` has at most `s` members. -/
def GroupSizesLE (ix : V → Sym2 V → ℕ) (s : ℕ) : Prop :=
  ∀ (v : V) (k : ℕ), #{f ∈ G.incidenceFinset v | ix v f = k} ≤ s

/-- **The full Master Theorem, conditional form** (proved): given the two
existence inputs — an even grouping, and a rainbow (s+1)-coloring on any
grouping with group sizes ≤ s (= Vizing for the split graph) — every graph
all of whose edges satisfy CRIT_s is admissible and has a strong majority
(s+1)-coloring (i.e. Maj′(G) ≤ s + 1). -/
theorem master_of_inputs (s : ℕ) (hs : 2 ≤ s)
    (hgrp : ∃ ix : V → Sym2 V → ℕ,
      GroupSizesLE G ix s ∧ ∀ v : V, groups G ix v ≤ hfun s (G.degree v))
    (hviz : ∀ ix : V → Sym2 V → ℕ, GroupSizesLE G ix s →
      ∃ c : Sym2 V → Fin (s + 1), IsRainbow G ix c)
    (hcrit : ∀ u v : V, G.Adj u v → Crit s (G.degree u) (G.degree v)) :
    Admissible G ∧ ∃ c : Sym2 V → Fin (s + 1), IsStrongMajority G c := by
  obtain ⟨ix, hsz, hg⟩ := hgrp
  obtain ⟨c, hrb⟩ := hviz ix hsz
  exact ⟨admissible_of_crit s hs hcrit, c, master_coloring s ix c hrb hg hcrit⟩

/-! ### The even grouping (input 1 of `master_of_inputs`): CLOSED
(campaign C5, lens C5L3-lean-six; machine pretest
`lenses/C5L3-lean-six/pretest_glue.py` P0 re-pinned the index-division
shape — fiber sizes and group counts — for s = 1..8, d = 0..200 before
these proofs were written). -/

/-- Fibers of division by `s` on `range d` have at most `s` members
(the arithmetic core of the even grouping). -/
lemma card_div_fiber_le (d : ℕ) {s : ℕ} (hs : 1 ≤ s) (k : ℕ) :
    #{i ∈ Finset.range d | i / s = k} ≤ s := by
  calc #{i ∈ Finset.range d | i / s = k}
      ≤ #(Finset.Ico (k * s) (k * s + s)) := by
        apply card_le_card
        intro i hi
        rw [mem_filter, mem_range] at hi
        rw [mem_Ico]
        constructor
        · calc k * s = i / s * s := by rw [hi.2]
            _ ≤ i := Nat.div_mul_le_self i s
        · have h1 : i / s < k + 1 := by omega
          calc i < (k + 1) * s := (Nat.div_lt_iff_lt_mul (by omega)).mp h1
            _ = k * s + s := by ring
    _ = s := by rw [Nat.card_Ico]; omega

variable (G) in
/-- The canonical even grouping: index the incident edges at each vertex by
`Finset.equivFin` and group by index division (groups of `s` consecutive
indices).  Off the incidence set the value is irrelevant (0). -/
noncomputable def evenIx (s : ℕ) (v : V) (f : Sym2 V) : ℕ :=
  if h : f ∈ G.incidenceFinset v
  then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) / s else 0

/-- **Even grouping existence** (input 1 of `master_of_inputs`, CLOSED):
split the d(v) edges at each vertex into h_s(d(v)) groups of size ≤ s by
index division. -/
theorem exists_even_grouping (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ ix : V → Sym2 V → ℕ,
      GroupSizesLE G ix s ∧ ∀ v : V, groups G ix v ≤ hfun s (G.degree v) := by
  refine ⟨evenIx G s, ?_, ?_⟩
  · -- group sizes ≤ s: inject each fiber into the matching division fiber
    -- of the index range
    intro v k
    calc #{f ∈ G.incidenceFinset v | evenIx G s v f = k}
        ≤ #{i ∈ Finset.range #(G.incidenceFinset v) | i / s = k} := by
          apply card_le_card_of_injOn
            (fun f => if h : f ∈ G.incidenceFinset v
              then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0)
          · intro f hf
            rw [mem_coe, mem_filter] at hf
            obtain ⟨hmem, hval⟩ := hf
            rw [evenIx, dif_pos hmem] at hval
            show (if h : f ∈ G.incidenceFinset v
              then ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) else 0) ∈ _
            rw [dif_pos hmem, mem_coe, mem_filter, mem_range]
            exact ⟨((G.incidenceFinset v).equivFin ⟨f, hmem⟩).isLt, hval⟩
          · intro f₁ h₁ f₂ h₂ heq
            rw [mem_coe, mem_filter] at h₁ h₂
            simp only [dif_pos h₁.1, dif_pos h₂.1] at heq
            have hfin : ((G.incidenceFinset v).equivFin ⟨f₁, h₁.1⟩) =
                ((G.incidenceFinset v).equivFin ⟨f₂, h₂.1⟩) :=
              Fin.val_injective heq
            exact Subtype.ext_iff.mp ((G.incidenceFinset v).equivFin.injective hfin)
      _ ≤ s := card_div_fiber_le _ hs k
  · -- group counts ≤ h_s(d): the image of index division lies in
    -- range ((d−1)/s + 1) = range ⌈d/s⌉
    intro v
    rw [groups]
    split_ifs with hd
    · exact Nat.zero_le _
    · rw [hfun, if_neg (by omega)]
      calc #((G.incidenceFinset v).image (evenIx G s v))
          ≤ #(Finset.range ((G.degree v - 1) / s + 1)) := by
            apply card_le_card
            intro k hk
            rw [mem_image] at hk
            obtain ⟨f, hf, hfk⟩ := hk
            rw [evenIx, dif_pos hf] at hfk
            rw [mem_range]
            have hlt : ((G.incidenceFinset v).equivFin ⟨f, hf⟩ : ℕ) <
                G.degree v := by
              have h := ((G.incidenceFinset v).equivFin ⟨f, hf⟩).isLt
              have hc : #(G.incidenceFinset v) = G.degree v := by
                rw [card_incidenceFinset_eq_degree]
              omega
            subst hfk
            exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
        _ = (G.degree v + s - 1) / s := by
            rw [card_range, ← Nat.add_div_right _ (by omega : 0 < s)]
            congr 1
            omega

/-! ### Open obligation (the precise remaining gap to the unconditional
Master Theorem, hence to Corollaries A/A1/A2/B/C of THEOREMS.md §4). -/

/-- Rainbow colorability with s+1 colors when all groups have size ≤ s:
equivalently, a proper edge (s+1)-coloring of the split graph G* with
Δ(G*) ≤ s (THEOREMS.md Lemmas 2–3).  This is **Vizing's theorem**, absent
from mathlib v4.30.0 and from master (re-checked 2026-06-13) — the single
external gap of the bridgehead. -/
proof_wanted rainbow_of_groupSizes (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (ix : V → Sym2 V → ℕ) (hsz : GroupSizesLE G ix s) :
    ∃ c : Sym2 V → Fin (s + 1), IsRainbow G ix c

end SMaj
