/-
Pins2.lean — sound pin ladder for the degree-{3,4} constructive route.

This file is self-contained over the frozen `Maj5Base.lean` interface.  It does
NOT import the returned C8 file.  The externally kernel-proved edge split is
restated as `exists_edge_split_pin` so this file can compile in isolation.

Status vocabulary:

* PROVED             — sorry-free in this file.
* EXTERNAL-BANKED    — kernel-proved in another return; locally a `sorry` pin.
* ROUTINE-EXPECTED   — mathematically proved/standard, formal bridge still open.
* OPEN-CRUX          — genuine unproved global placement theorem.

The old parity classification P2″ is false.  Two induced K₅-e blocks joined
through their missing-edge ports give a connected 4-regular graph of even order
with no zero-odd split.  No statement of that false classification remains here.
-/

import Maj5Base

set_option autoImplicit false

open Finset SimpleGraph

namespace Rung4Moonshot

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Per-vertex counts and the E1 counting core -/

/-- Number of `α`-colored `G`-edges incident to `v`. -/
def cnt (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*} [DecidableEq C]
    (c : Sym2 V → C) (v : V) (α : C) : ℕ :=
  #{f ∈ G.incidenceFinset v | c f = α}

/-- PROVED.  Exact row-count/per-vertex-count identity. -/
lemma nColor_add_two_mul
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*} [DecidableEq C]
    (c : Sym2 V → C) {u v : V} (huv : G.Adj u v) (α : C) :
    SMaj.nColor G c u v α + 2 * (if c s(u, v) = α then 1 else 0)
      = cnt G c u α + cnt G c v α := by
  unfold SMaj.nColor cnt;
  unfold SMaj.row; simp +decide [ Finset.filter_union, Finset.filter_erase, huv ] ; ring;
  rw [ Finset.card_union_of_disjoint ];
  · rw [ show G.incidenceFinset u = insert s(u, v) (SMaj.side G u v) from ?_, show G.incidenceFinset v = insert s(v, u) (SMaj.side G v u) from ?_ ];
    · split_ifs <;> simp_all +decide [ Finset.filter_insert, Sym2.eq_swap ] ; ring;
      grind +suggestions;
    · simp +decide [ SMaj.side, huv.symm ];
    · simp +decide [ SMaj.side, huv ];
  · exact SMaj.disjoint_sides huv |> fun h => h.mono ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ )

/-- PROVED.  Reduction of SM to endpoint color-count inequalities. -/
lemma isStrongMajority_of_cnt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {C : Type*} [DecidableEq C]
    (c : Sym2 V → C)
    (h : ∀ u v, G.Adj u v → ∀ α : C,
      cnt G c u α + cnt G c v α
        ≤ (G.degree u + G.degree v - 2) / 2
          + 2 * (if c s(u, v) = α then 1 else 0)) :
    SMaj.IsStrongMajority G c := by
  intro u v huv α
  have hc := h u v huv α
  have hn := nColor_add_two_mul G c huv α
  split_ifs at * <;> omega

/-- PROVED (E1 counting core).  Per-vertex properness implies SM. -/
lemma E1_of_cnt_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Sym2 V → Fin 4)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (h1 : ∀ (v : V) (α : Fin 4), cnt G c v α ≤ 1) :
    SMaj.IsStrongMajority G c := by
  apply isStrongMajority_of_cnt
  intro u v huv α
  have hu := h1 u α
  have hv := h1 v α
  rcases hdeg u with h | h <;> rcases hdeg v with h' | h' <;>
    rw [h, h'] <;> split_ifs <;> omega

/-- BANKED (parallel counting core; transplanted sorry-free from the
`r4w3_p3_conditional` Aristotle return, statements re-attached to THIS file's local
`cnt`/`isStrongMajority_of_cnt`).  Defect-tolerant variant of `E1_of_cnt_le_one`:
colors may be doubled (`cnt ≤ 2`) provided the two Probe-G placement conditions hold —
`C1` (no two adjacent vertices both doubled in an off-edge color) and `C2` (no doubled
vertex with a tight off-color neighbour already carrying that color).  This is a raw
`cnt`-count lemma.  BRIDGE NEEDED to wire it into the class-II thread: derive `C1`/`C2`
for `combine H₀ b₀ b₁` from `DefectProfile` + `DefectSafe` (that derivation is exactly
the content deferred inside `strongMajority_of_crossSafe_split`). -/
lemma E1_defect_core (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 4)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (h2 : ∀ (v : V) (α : Fin 4), cnt G c v α ≤ 2)
    (C1 : ∀ (u v : V) (α : Fin 4),
      ¬ (G.Adj u v ∧ cnt G c u α = 2 ∧ cnt G c v α = 2 ∧ c s(u, v) ≠ α))
    (C2 : ∀ (x v : V) (α : Fin 4),
      ¬ (G.Adj x v ∧ cnt G c x α = 2 ∧ c s(x, v) ≠ α
          ∧ (G.degree x = 3 ∨ G.degree v = 3) ∧ 1 ≤ cnt G c v α)) :
    SMaj.IsStrongMajority G c := by
  apply isStrongMajority_of_cnt
  intro u v huv α
  have hu := h2 u α
  have hv := h2 v α
  have du := hdeg u
  have dv := hdeg v
  by_cases hcol : c s(u, v) = α
  · rw [if_pos hcol]
    omega
  · have hsvu : c s(v, u) ≠ α := by rw [Sym2.eq_swap]; exact hcol
    have k1 : ¬ (cnt G c u α = 2 ∧ cnt G c v α = 2) :=
      fun h => C1 u v α ⟨huv, h.1, h.2, hcol⟩
    have k2u : cnt G c u α = 2 →
        (G.degree u = 3 ∨ G.degree v = 3) → cnt G c v α = 0 := by
      intro p tight
      by_contra hc
      exact C2 u v α ⟨huv, p, hcol, tight, Nat.one_le_iff_ne_zero.mpr hc⟩
    have k2v : cnt G c v α = 2 →
        (G.degree v = 3 ∨ G.degree u = 3) → cnt G c u α = 0 := by
      intro p tight
      by_contra hc
      exact C2 v u α ⟨huv.symm, p, hsvu, tight, Nat.one_le_iff_ne_zero.mpr hc⟩
    rw [if_neg hcol]
    omega

/-! ## Split vocabulary -/

/-- The full contract returned by the banked degree-two edge split. -/
def IsEdgeSplit
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj] : Prop :=
  (∀ u v, G.Adj u v ↔ (H₀.Adj u v ∨ H₁.Adj u v)) ∧
  (∀ u v, H₀.Adj u v → ¬ H₁.Adj u v) ∧
  H₀ ≤ G ∧ H₁ ≤ G ∧
  (∀ v, H₀.degree v ≤ 2) ∧
  (∀ v, H₁.degree v ≤ 2) ∧
  (∀ v, H₀.degree v + H₁.degree v = G.degree v)

/-- PROVED.  Swapping the two halves preserves the split contract. -/
lemma IsEdgeSplit.swap
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (h : IsEdgeSplit G H₀ H₁) :
    IsEdgeSplit G H₁ H₀ := by
  rcases h with ⟨hpart, hdisj, hsub₀, hsub₁, hdeg₀, hdeg₁, hsum⟩
  refine ⟨?_, ?_, hsub₁, hsub₀, hdeg₁, hdeg₀, ?_⟩
  · intro u v
    rw [hpart u v, or_comm]
  · intro u v h₁ h₀
    exact hdisj u v h₀ h₁
  · intro v
    rw [add_comm, hsum v]

/-- A graph has no odd cycle. -/
def NoOddCycle (H : SimpleGraph V) : Prop :=
  ∀ x (w : H.Walk x x), w.IsCycle → ¬ Odd w.length

/-- Existence of a degree-two split in which both halves have no odd cycle. -/
def HasZeroOddSplit (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ (H₀ H₁ : SimpleGraph V)
      (_ : DecidableRel H₀.Adj) (_ : DecidableRel H₁.Adj),
    IsEdgeSplit G H₀ H₁ ∧ NoOddCycle H₀ ∧ NoOddCycle H₁

/-- Adjacency multiplicity matrix of `G` (values in `{0,1}`).  Transplanted with
the split proof below from the `rung4_c8_1_a` return (round 4). -/
def adjMat (G : SimpleGraph V) [DecidableRel G.Adj] : V → V → ℕ :=
  fun u v => if G.Adj u v then 1 else 0

lemma mdeg_adjMat (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    SMaj.mdeg (adjMat G) v = G.degree v := by
  unfold SMaj.mdeg adjMat;
  simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ]

/-- PROVED (round 4; formerly EXTERNAL-BANKED).  The Euler edge-split, attached
from its kernel proof `Rung4Kernel.exists_edge_split` in the `rung4_c8_1_a`
return: `SMaj.exists_two_split` on the adjacency matrix, with the two halves
realized as `SimpleGraph.fromRel` of the split multiplicities.  Statement
unchanged; the proof opens with `simp only [IsEdgeSplit]` to unfold this file's
packaging of the identical seven-clause contract. -/
lemma exists_edge_split_pin
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 4) :
    ∃ (H₀ H₁ : SimpleGraph V)
      (_ : DecidableRel H₀.Adj) (_ : DecidableRel H₁.Adj),
      IsEdgeSplit G H₀ H₁ := by
  simp only [IsEdgeSplit]
  obtain ⟨ m₁, m₂, hm₁m₂, hm₁, hm₂ ⟩ := SMaj.exists_two_split ( adjMat G ) ( by simp +decide [ adjMat, SimpleGraph.adj_comm ] ) ( by simp +decide [ adjMat ] ) ( fun v => by linarith [ mdeg_adjMat G v, hdeg v ] );
  refine' ⟨ SimpleGraph.fromRel ( fun u v => m₁ u v ≠ 0 ), SimpleGraph.fromRel ( fun u v => m₂ u v ≠ 0 ), _, _, _, _, _ ⟩ <;> simp +decide [ SimpleGraph.fromRel_adj ];
  all_goals try infer_instance;
  · intro u v; specialize hm₁m₂ u v; unfold adjMat at hm₁m₂;
    by_cases hu : u = v <;> by_cases hv : G.Adj u v <;> simp +decide [ hu, hv, hm₁ u v, hm₂.1 u v ] at hm₁m₂ ⊢;
    · omega;
    · grind;
  · intro u v huv huv' huv''; specialize hm₁m₂ u v; simp_all +decide [ adjMat ] ;
    grind;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · intro u v; simp +decide [ SimpleGraph.fromRel_adj ] ;
      intro huv h; specialize hm₁m₂ u v; unfold adjMat at hm₁m₂; simp_all +decide [ SimpleGraph.adj_comm ] ;
      grind;
    · intro u v huv; specialize hm₁m₂ u v; simp_all +decide [ adjMat ] ;
      grind;
    · intro v; specialize hm₂; have := hm₂.2.1 v; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ] ;
      refine' le_trans _ ( hm₂.2.1 v );
      refine' le_trans _ ( Finset.sum_le_sum_of_subset ( show Finset.filter ( fun x => ¬v = x ∧ ¬m₁ v x = 0 ) Finset.univ ⊆ Finset.univ from Finset.filter_subset _ _ ) );
      refine' le_trans _ ( Finset.sum_le_sum fun x hx => Nat.one_le_iff_ne_zero.mpr <| by aesop ) ; simp +decide [ Finset.sum_ite ];
    · intro v;
      refine' le_trans _ ( hm₂.2.2 v );
      refine' le_trans _ ( Finset.sum_le_sum fun u hu => show m₂ v u ≥ if m₂ v u ≠ 0 then 1 else 0 from _ );
      · simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
        rw [ Finset.card_filter ];
        gcongr ; aesop;
      · grind;
    · intro v; simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def, SimpleGraph.fromRel_adj ] ;
      rw [ ← Finset.card_union_of_disjoint ];
      · congr with x ; simp +decide [ hm₁m₂, hm₁, hm₂.1 ];
        by_cases h : v = x <;> simp +decide [ h, adjMat ] at hm₁m₂ ⊢;
        grind;
      · simp +contextual [ Finset.disjoint_left, hm₁, hm₂.1 ];
        intro u huv hmu; specialize hm₁m₂ u v; simp_all +decide [ adjMat ] ;
        grind

/-! ## E1 split assembly (fully closed) -/

/-- Embed two Boolean palettes as `{0,1}` and `{2,3}`. -/
noncomputable def combine
    (H₀ : SimpleGraph V) [DecidableRel H₀.Adj]
    (col₀ col₁ : Sym2 V → Bool) : Sym2 V → Fin 4 :=
  fun e => if e ∈ H₀.edgeFinset then (if col₀ e then 1 else 0)
           else (if col₁ e then 3 else 2)

/-- PROVED (full E1 split form).  Proper Boolean colorings of the two
halves assemble to an SM four-coloring.  The statement deliberately keeps
only the hypotheses used by the proof. -/
lemma E1_split
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hpart : ∀ u v, G.Adj u v ↔ (H₀.Adj u v ∨ H₁.Adj u v))
    (col₀ col₁ : Sym2 V → Bool)
    (hp0 : ∀ (v : V) (b : Bool),
      #{f ∈ H₀.incidenceFinset v | col₀ f = b} ≤ 1)
    (hp1 : ∀ (v : V) (b : Bool),
      #{f ∈ H₁.incidenceFinset v | col₁ f = b} ≤ 1) :
    SMaj.IsStrongMajority G (combine H₀ col₀ col₁) := by
  apply E1_of_cnt_le_one G (combine H₀ col₀ col₁) hdeg
  intro v α
  fin_cases α
  · refine (Finset.card_le_card ?_).trans (hp0 v false)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfH0 : f ∈ H₀.edgeFinset := by
      by_contra hnot
      cases h : col₁ f <;> simp [combine, hnot, h] at hcolor
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨SimpleGraph.mem_edgeFinset.mp hfH0, hfg.2⟩
    · simpa [combine, hfH0] using hcolor
  · refine (Finset.card_le_card ?_).trans (hp0 v true)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfH0 : f ∈ H₀.edgeFinset := by
      by_contra hnot
      cases h : col₁ f <;> simp [combine, hnot, h] at hcolor
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨SimpleGraph.mem_edgeFinset.mp hfH0, hfg.2⟩
    · simpa [combine, hfH0] using hcolor
  · refine (Finset.card_le_card ?_).trans (hp1 v false)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfnot : f ∉ H₀.edgeFinset := by
      intro hfH0
      cases h : col₀ f <;> simp [combine, hfH0, h] at hcolor
    have hfH1edge : f ∈ H₁.edgeSet := by
      rw [SimpleGraph.mem_incidenceFinset] at hfg
      rcases hfg with ⟨hfGedge, _⟩
      induction f using Sym2.inductionOn with
      | _ u w =>
          rw [G.mem_edgeSet] at hfGedge
          rw [H₁.mem_edgeSet]
          have hs := (hpart u w).mp hfGedge
          rcases hs with hs | hs
          · exact False.elim (hfnot (SimpleGraph.mem_edgeFinset.mpr hs))
          · exact hs
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨hfH1edge, hfg.2⟩
    · simpa [combine, hfnot] using hcolor
  · refine (Finset.card_le_card ?_).trans (hp1 v true)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfnot : f ∉ H₀.edgeFinset := by
      intro hfH0
      cases h : col₀ f <;> simp [combine, hfH0, h] at hcolor
    have hfH1edge : f ∈ H₁.edgeSet := by
      rw [SimpleGraph.mem_incidenceFinset] at hfg
      rcases hfg with ⟨hfGedge, _⟩
      induction f using Sym2.inductionOn with
      | _ u w =>
          rw [G.mem_edgeSet] at hfGedge
          rw [H₁.mem_edgeSet]
          have hs := (hpart u w).mp hfGedge
          rcases hs with hs | hs
          · exact False.elim (hfnot (SimpleGraph.mem_edgeFinset.mpr hs))
          · exact hs
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨hfH1edge, hfg.2⟩
    · simpa [combine, hfnot] using hcolor

/-- PROVED (round 3).  The count bound inside `E1_split`, exposed as a lemma:
two per-half proper Boolean colorings give every assembled color count `≤ 1`.
The four blocks are extracted verbatim from the kernel-proved `E1_split` body. -/
lemma cnt_combine_le_one
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hpart : ∀ u v, G.Adj u v ↔ (H₀.Adj u v ∨ H₁.Adj u v))
    (col₀ col₁ : Sym2 V → Bool)
    (hp0 : ∀ (v : V) (b : Bool),
      #{f ∈ H₀.incidenceFinset v | col₀ f = b} ≤ 1)
    (hp1 : ∀ (v : V) (b : Bool),
      #{f ∈ H₁.incidenceFinset v | col₁ f = b} ≤ 1)
    (v : V) (α : Fin 4) :
    cnt G (combine H₀ col₀ col₁) v α ≤ 1 := by
  fin_cases α
  · refine (Finset.card_le_card ?_).trans (hp0 v false)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfH0 : f ∈ H₀.edgeFinset := by
      by_contra hnot
      cases h : col₁ f <;> simp [combine, hnot, h] at hcolor
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨SimpleGraph.mem_edgeFinset.mp hfH0, hfg.2⟩
    · simpa [combine, hfH0] using hcolor
  · refine (Finset.card_le_card ?_).trans (hp0 v true)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfH0 : f ∈ H₀.edgeFinset := by
      by_contra hnot
      cases h : col₁ f <;> simp [combine, hnot, h] at hcolor
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨SimpleGraph.mem_edgeFinset.mp hfH0, hfg.2⟩
    · simpa [combine, hfH0] using hcolor
  · refine (Finset.card_le_card ?_).trans (hp1 v false)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfnot : f ∉ H₀.edgeFinset := by
      intro hfH0
      cases h : col₀ f <;> simp [combine, hfH0, h] at hcolor
    have hfH1edge : f ∈ H₁.edgeSet := by
      rw [SimpleGraph.mem_incidenceFinset] at hfg
      rcases hfg with ⟨hfGedge, _⟩
      induction f using Sym2.inductionOn with
      | _ u w =>
          rw [G.mem_edgeSet] at hfGedge
          rw [H₁.mem_edgeSet]
          have hs := (hpart u w).mp hfGedge
          rcases hs with hs | hs
          · exact False.elim (hfnot (SimpleGraph.mem_edgeFinset.mpr hs))
          · exact hs
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨hfH1edge, hfg.2⟩
    · simpa [combine, hfnot] using hcolor
  · refine (Finset.card_le_card ?_).trans (hp1 v true)
    intro f hf
    simp only [Finset.mem_filter] at hf ⊢
    rcases hf with ⟨hfg, hcolor⟩
    have hfnot : f ∉ H₀.edgeFinset := by
      intro hfH0
      cases h : col₀ f <;> simp [combine, hfH0, h] at hcolor
    have hfH1edge : f ∈ H₁.edgeSet := by
      rw [SimpleGraph.mem_incidenceFinset] at hfg
      rcases hfg with ⟨hfGedge, _⟩
      induction f using Sym2.inductionOn with
      | _ u w =>
          rw [G.mem_edgeSet] at hfGedge
          rw [H₁.mem_edgeSet]
          have hs := (hpart u w).mp hfGedge
          rcases hs with hs | hs
          · exact False.elim (hfnot (SimpleGraph.mem_edgeFinset.mpr hs))
          · exact hs
    constructor
    · rw [SimpleGraph.mem_incidenceFinset] at hfg ⊢
      exact ⟨hfH1edge, hfg.2⟩
    · simpa [combine, hfnot] using hcolor

/-! ## Banked counting bricks (transplanted sorry-free from the `r4w3_p3_oddarm`
Aristotle return; both re-attached to this file's local `cnt`/`combine`).  Together
they are the count core `strongMajority_of_crossSafe_split` reduces to: `cnt_combine_le_two`
supplies the `≤2` bound and `sm_of_offcolor` closes SM from an off-color cap bound. -/

/-- BANKED.  Every color is seen at most twice per vertex by a `combine` coloring:
colors `0,1` land only on `H₁`-edges and colors `2,3` on the complementary (`H₂`) edges. -/
lemma cnt_combine_le_two (G H₁ H₂ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₁.Adj] [DecidableRel H₂.Adj]
    (hpart : ∀ u v, G.Adj u v ↔ (H₁.Adj u v ∨ H₂.Adj u v))
    (hsub1 : H₁ ≤ G) (hsub2 : H₂ ≤ G)
    (hd1 : ∀ v, H₁.degree v ≤ 2) (hd2 : ∀ v, H₂.degree v ≤ 2)
    (col₁ col₂ : Sym2 V → Bool) (v : V) (α : Fin 4) :
    cnt G (combine H₁ col₁ col₂) v α ≤ 2 := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact if α = 0 ∨ α = 1 then H₁.incidenceFinset v else H₂.incidenceFinset v;
  · intro f hf; split_ifs at * <;> simp_all +decide [ combine ] ;
    · simp_all +decide [ SimpleGraph.incidenceSet ];
      grind +revert;
    · cases f ; simp_all +decide [ SimpleGraph.incidenceSet ];
      grind +revert;
  · split_ifs <;> simp_all +decide [ SimpleGraph.card_incidenceFinset_eq_degree ]

/-- BANKED.  Off-color counting wrapper: `cnt ≤ 2` everywhere plus an off-color
endpoint-sum cap bound gives strong majority.  When `α` is the edge's own color the
`+2` cap slack plus `cnt ≤ 2` already suffices. -/
lemma sm_of_offcolor (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 4)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hA : ∀ v α, cnt G c v α ≤ 2)
    (hB : ∀ u v, G.Adj u v → ∀ α, c s(u, v) ≠ α →
      cnt G c u α + cnt G c v α ≤ (G.degree u + G.degree v - 2) / 2) :
    SMaj.IsStrongMajority G c := by
  apply isStrongMajority_of_cnt
  intro u v huv α
  by_cases h : c s(u, v) = α
  · have h1 := hA u α; have h2 := hA v α
    rcases hdeg u with hu | hu <;> rcases hdeg v with hv | hv <;>
      rw [hu, hv] <;> simp only [h, if_true] <;> omega
  · have := hB u v huv α h
    simp only [h, if_false, Nat.mul_zero, Nat.add_zero]
    omega

/-! ## The true P2 replacement: class I iff zero-odd split -/

/-- A proper four-edge-coloring in the per-vertex count form. -/
def IsProper4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Sym2 V → Fin 4) : Prop :=
  ∀ v α, cnt G c v α ≤ 1

/-! ## Proper 2-edge-coloring of odd-cycle-free max-degree-2 graphs
(transplanted sorry-free from the `r4w3_proper2_direct` Aristotle return, where it
closed the stale `Rung4Kernel.exists_proper_two_edge_coloring`; self-contained over
mathlib, re-homed into this namespace verbatim.  The orphan `hitsOdd_deleteEdges`
helper, which served only the stale steerable-defects pin, was not transplanted). -/

/-! ## Alternating 2-edge-coloring of a max-degree-≤2 graph. -/

lemma incidenceFinset_deleteEdges_single (M : SimpleGraph V) [DecidableRel M.Adj]
    (e : Sym2 V) (v : V) :
    (M.deleteEdges {e}).incidenceFinset v = (M.incidenceFinset v).erase e := by
  ext f; simp [SimpleGraph.incidenceFinset, SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet, SimpleGraph.edgeSet_deleteEdges, Finset.mem_erase] ; aesop;

lemma degree_deleteEdges_single (M : SimpleGraph V) [DecidableRel M.Adj]
    (a b : V) (hab : M.Adj a b) (v : V) :
    (M.deleteEdges {s(a, b)}).degree v
      = M.degree v - (if v = a ∨ v = b then 1 else 0) := by
  have := @incidenceFinset_deleteEdges_single V;
  rw [ ← SimpleGraph.card_incidenceFinset_eq_degree, ← SimpleGraph.card_incidenceFinset_eq_degree, this ];
  split_ifs <;> simp_all +decide [ SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff ]

/-! ### Helper lemmas for the proper 2-edge-coloring (proof by induction on edges). -/

/-
Deleting a present edge drops the edge count by exactly one.
-/
lemma card_edgeFinset_deleteEdges_adj (M : SimpleGraph V) [DecidableRel M.Adj]
    {a b : V} (h : M.Adj a b) :
    (M.deleteEdges {s(a, b)}).edgeFinset.card + 1 = M.edgeFinset.card := by
  convert Set.ncard_diff_singleton_add_one ( show s(a, b) ∈ M.edgeSet from ?_ ) using 1;
  · rw [ ← Set.ncard_coe_finset ] ; congr ; aesop;
  · rw [ ← Set.ncard_coe_finset ] ; congr ; aesop;
  · exact (mem_edgeSet M).mpr h

/-
Deleting an edge cannot create odd cycles: the no-odd-cycle property
transfers from `M` to `M.deleteEdges {e}`.
-/
lemma noOdd_deleteEdges (M : SimpleGraph V) [DecidableRel M.Adj] (e : Sym2 V)
    (hno : ∀ (x : V) (w : M.Walk x x), w.IsCycle → ¬ Odd w.length) :
    ∀ (x : V) (w : (M.deleteEdges {e}).Walk x x), w.IsCycle → ¬ Odd w.length := by
  intro x w hw;
  contrapose! hno;
  refine' ⟨ x, w.map ( SimpleGraph.Hom.ofLE ( SimpleGraph.deleteEdges_le _ ) ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.map ]

/-
**Alternation along a path.** For a proper `Bool`-edge-coloring, the color of
the `i`-th edge of a path is the color of the first edge if `i` is even, and its
negation if `i` is odd.
-/
lemma path_edge_color {N : SimpleGraph V} [DecidableRel N.Adj]
    {col : Sym2 V → Bool}
    (hcol : ∀ (v : V) (bb : Bool), #{f ∈ N.incidenceFinset v | col f = bb} ≤ 1)
    {a b : V} (p : N.Walk a b) (hp : p.IsPath) :
    ∀ i, i + 1 ≤ p.length →
      col s(p.getVert i, p.getVert (i + 1)) =
        (if Even i then col s(p.getVert 0, p.getVert 1)
         else !(col s(p.getVert 0, p.getVert 1))) := by
  intro i hi;
  induction' i with i ih;
  · simp +decide;
  · have h_distinct : s(p.getVert i, p.getVert (i + 1)) ≠ s(p.getVert (i + 1), p.getVert (i + 2)) := by
      intro h; have := hp.getVert_injOn; simp_all +decide [ Set.InjOn ] ;
      grind +qlia;
    have h_adj : N.Adj (p.getVert i) (p.getVert (i + 1)) ∧ N.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
      exact ⟨ p.adj_getVert_succ ( by linarith ), p.adj_getVert_succ ( by linarith ) ⟩;
    have h_diff : col s(p.getVert i, p.getVert (i + 1)) ≠ col s(p.getVert (i + 1), p.getVert (i + 2)) := by
      intro h_eq
      have h_card : 2 ≤ Finset.card (Finset.filter (fun f => col f = col s(p.getVert i, p.getVert (i + 1))) (N.incidenceFinset (p.getVert (i + 1)))) := by
        refine' Finset.one_lt_card.mpr ⟨ s(p.getVert i, p.getVert (i + 1)), _, s(p.getVert (i + 1), p.getVert (i + 2)), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.incidenceSet ];
      exact not_lt_of_ge h_card ( lt_of_le_of_lt ( hcol _ _ ) ( by decide ) );
    rw [ ih ( by linarith ) ] at h_diff; split_ifs at * <;> simp_all +decide [ Nat.even_add_one ] ;
    cases h : col s(a, p.getVert 1) <;> cases h' : col s(p.getVert (i + 1), p.getVert (i + 2)) <;> simp_all +decide only

/-
**Reachability of the two odd-degree vertices.** In a finite graph whose only
odd-degree vertices are `a` and `b`, the vertices `a` and `b` lie in the same
connected component (per-component handshaking lemma).
-/
lemma reachable_two_odd (N : SimpleGraph V) [DecidableRel N.Adj]
    {a b : V} (hab : a ≠ b) (hna : Odd (N.degree a)) (hnb : Odd (N.degree b))
    (hother : ∀ v, v ≠ a → v ≠ b → Even (N.degree v)) :
    N.Reachable a b := by
  contrapose! hnb; have := N.even_card_odd_degree_vertices; simp_all +decide [ Finset.filter_or, parity_simps ] ;
  -- Consider the set of vertices reachable from $a$.
  set s := {v : V | N.Reachable a v} with hs_def
  have hs : a ∈ s ∧ b ∉ s := by
    exact ⟨ SimpleGraph.Reachable.refl _, hnb ⟩;
  -- Consider the induced subgraph $G'$ on $s$.
  set G' := N.induce s with hG'_def
  have hG'_deg : ∀ v : s, G'.degree v = N.degree v := by
    intro v; exact (by
    apply SimpleGraph.degree_induce_of_neighborSet_subset; intro w hw; exact (by
    exact v.2.trans ( SimpleGraph.Adj.reachable hw )););
  have hG'_odd : Finset.card (Finset.filter (fun v : s => Odd (G'.degree v)) Finset.univ) = 1 := by
    rw [ Finset.card_eq_one ] ; use ⟨ a, hs.1 ⟩ ; ext v ; by_cases hv : v = ⟨ a, hs.1 ⟩ <;> simp_all +decide [ Nat.even_iff ] ;
    grind +splitImp
  have hG'_even : Even (Finset.card (Finset.filter (fun v : s => Odd (G'.degree v)) Finset.univ)) := by
    convert G'.even_card_odd_degree_vertices using 1
  simp_all +decide [ parity_simps ] ;

/-
**Leaf peeling step.** If `a` is a degree-one vertex with unique incident edge
`s(a,b)`, a proper coloring of `M` minus that edge extends to a proper coloring of
`M` (choose the new edge's color to avoid `b`'s single remaining edge).
-/
lemma epc_leaf_step (M : SimpleGraph V) [DecidableRel M.Adj]
    (hdeg : ∀ v, M.degree v ≤ 2)
    {a b : V} (hab : M.Adj a b) (hdega : M.degree a = 1)
    (col' : Sym2 V → Bool)
    (hcol' : ∀ (v : V) (bb : Bool),
      #{f ∈ (M.deleteEdges {s(a, b)}).incidenceFinset v | col' f = bb} ≤ 1) :
    ∃ col : Sym2 V → Bool,
      ∀ (v : V) (bb : Bool), #{f ∈ M.incidenceFinset v | col f = bb} ≤ 1 := by
  -- Let `cb : Bool` be a color not used by `col'` on the remaining incident edges at `b`.
  obtain ⟨cb, hcb⟩ : ∃ cb : Bool, ∀ f ∈ (M.deleteEdges {s(a, b)}).incidenceFinset b, col' f ≠ cb := by
    by_contra h_contra
    push_neg at h_contra
    have h_card : (Finset.filter (fun f => col' f = true) ((M.deleteEdges {s(a, b)}).incidenceFinset b)).card + (Finset.filter (fun f => col' f = false) ((M.deleteEdges {s(a, b)}).incidenceFinset b)).card = (M.deleteEdges {s(a, b)}).degree b := by
      rw [ Finset.card_filter, Finset.card_filter ];
      rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x hx => by aesop, Finset.sum_const, Finset.card_eq_sum_ones ] ; simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
    have h_card_le : (M.deleteEdges {s(a, b)}).degree b ≤ 1 := by
      grind +suggestions;
    linarith [ show Finset.card ( Finset.filter ( fun f => col' f = true ) ( ( M.deleteEdges { s(a, b) } ).incidenceFinset b ) ) ≥ 1 from Finset.card_pos.mpr ( by obtain ⟨ f, hf₁, hf₂ ⟩ := h_contra true; exact ⟨ f, Finset.mem_filter.mpr ⟨ hf₁, hf₂ ⟩ ⟩ ), show Finset.card ( Finset.filter ( fun f => col' f = false ) ( ( M.deleteEdges { s(a, b) } ).incidenceFinset b ) ) ≥ 1 from Finset.card_pos.mpr ( by obtain ⟨ f, hf₁, hf₂ ⟩ := h_contra false; exact ⟨ f, Finset.mem_filter.mpr ⟨ hf₁, hf₂ ⟩ ⟩ ) ];
  refine' ⟨ fun f => if f = s(a, b) then cb else col' f, fun v bb => _ ⟩;
  by_cases hv : v = a ∨ v = b;
  · rcases hv with ( rfl | rfl );
    · rw [ Finset.card_le_one_iff ];
      have := Finset.card_eq_one.mp ( show Finset.card ( M.incidenceFinset v ) = 1 from by rw [ SimpleGraph.card_incidenceFinset_eq_degree ] ; exact hdega ) ; obtain ⟨ f, hf ⟩ := this; simp_all +decide [ Finset.ext_iff ] ;
    · by_cases h : bb = cb <;> simp_all +decide [ Finset.filter_insert, Finset.filter_singleton ];
      · refine' le_trans ( Finset.card_le_one.mpr _ ) _ <;> simp_all +decide [ SimpleGraph.incidenceSet ];
      · rw [ show { f ∈ M.incidenceFinset v | ( if f = s(a, v) then cb else col' f ) = bb } = { f ∈ ( M.deleteEdges { s(a, v) } ).incidenceFinset v | col' f = bb } from ?_ ];
        · cases bb <;> cases cb <;> simp_all +decide;
        · ext f; simp [SimpleGraph.incidenceFinset];
          by_cases hf : f = s(a, v) <;> simp_all +decide [ SimpleGraph.incidenceSet ];
          exact Ne.symm h;
  · convert hcol' v bb using 2;
    ext f; simp [hv];
    by_cases hf : f = s(a, b) <;> simp_all +decide [ SimpleGraph.incidenceSet ]

/-
**Key equality for the cycle step.** With every degree even and `s(a,b)` an
edge, in `M' := M.deleteEdges {s(a,b)}` the vertices `a` and `b` each have exactly
one incident edge, and those two edges get the same color under any proper coloring
`col'` of `M'`.
-/
set_option maxHeartbeats 1000000 in
lemma epc_cycle_key (M : SimpleGraph V) [DecidableRel M.Adj]
    (hdeg : ∀ v, M.degree v ≤ 2)
    (hno : ∀ (x : V) (w : M.Walk x x), w.IsCycle → ¬ Odd w.length)
    (heven : ∀ v, Even (M.degree v))
    {a b : V} (hab : M.Adj a b)
    (col' : Sym2 V → Bool)
    (hcol' : ∀ (v : V) (bb : Bool),
      #{f ∈ (M.deleteEdges {s(a, b)}).incidenceFinset v | col' f = bb} ≤ 1) :
    ∃ fa fb : Sym2 V,
      (M.deleteEdges {s(a, b)}).incidenceFinset a = {fa} ∧
      (M.deleteEdges {s(a, b)}).incidenceFinset b = {fb} ∧
      col' fa = col' fb := by
  obtain ⟨fa, hfa⟩ : ∃ fa : Sym2 V, (M.deleteEdges {s(a, b)}).incidenceFinset a = {fa} := by
    have h_deg_a : (M.deleteEdges {s(a, b)}).degree a = 1 := by
      rw [ degree_deleteEdges_single ];
      · have := hdeg a; have := heven a; interval_cases _ : M.degree a <;> simp_all +decide ;
        simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
      · exact hab;
    exact Finset.card_eq_one.mp ( by simpa [ SimpleGraph.card_incidenceFinset_eq_degree ] using h_deg_a );
  obtain ⟨fb, hfb⟩ : ∃ fb : Sym2 V, (M.deleteEdges {s(a, b)}).incidenceFinset b = {fb} := by
    have h_deg_b : (M.deleteEdges {s(a, b)}).degree b = 1 := by
      convert degree_deleteEdges_single M a b hab b using 1;
      have := hdeg b; have := heven b; interval_cases _ : M.degree b <;> simp_all +decide ;
      simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
      exact ‹∀ x, ¬M.Adj b x› a hab.symm;
    exact Finset.card_eq_one.mp ( by simpa [ SimpleGraph.card_incidenceFinset_eq_degree ] using h_deg_b );
  obtain ⟨p, hp⟩ : ∃ p : (M.deleteEdges {s(a, b)}).Walk a b, p.IsPath := by
    have h_reachable : (M.deleteEdges {s(a, b)}).Reachable a b := by
      apply reachable_two_odd;
      · exact hab.ne;
      · replace hfa := congr_arg Finset.card hfa; simp_all +decide ;
      · replace hfb := congr_arg Finset.card hfb; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ;
      · intro v hv hv'; specialize heven v; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ;
    obtain ⟨ p, hp ⟩ := h_reachable.exists_isPath; exact ⟨ p, hp ⟩ ;
  -- Since `p` is a path in `M'`, its length `L` must be odd (as shown in `path_odd`).
  have hL_odd : Odd p.length := by
    contrapose! hno;
    refine' ⟨ a, SimpleGraph.Walk.cons hab ( p.map ( SimpleGraph.Hom.ofLE ( SimpleGraph.deleteEdges_le _ ) ) |> SimpleGraph.Walk.reverse ), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ];
    intro h; have := p.edges_subset_edgeSet h; simp_all +decide [ SimpleGraph.deleteEdges ] ;
  -- By `path_edge_color`, the colors at the endpoints are equal.
  have h_color_eq : col' fa = col' fb := by
    have h_color_eq : col' s(p.getVert 0, p.getVert 1) = col' s(p.getVert (p.length - 1), p.getVert p.length) := by
      have := path_edge_color hcol' p hp;
      grind +splitImp;
    convert h_color_eq using 2;
    · replace hfa := Finset.ext_iff.mp hfa ( s(p.getVert 0, p.getVert 1) ) ; simp_all +decide [ SimpleGraph.mem_incidenceFinset ] ;
      rcases p with ( _ | ⟨ _, _, p ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.cons_isPath_iff ]; all_goals simp_all +decide [ SimpleGraph.deleteEdges ];
    · have h_edge : (M.deleteEdges {s(a, b)}).Adj (p.getVert (p.length - 1)) (p.getVert p.length) := by
        convert p.adj_getVert_succ ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) zero_lt_one ) using 1;
        grind;
      replace hfb := Finset.ext_iff.mp hfb ( s(p.getVert (p.length - 1), b) ) ; simp_all +decide [ SimpleGraph.incidenceSet ] ;
  exact ⟨ fa, fb, hfa, hfb, h_color_eq ⟩

/-
**Cycle-breaking step.** If every degree of `M` is even (so `M` is a disjoint
union of cycles) and `s(a,b)` is an edge, then a proper coloring of `M` minus that
edge extends to a proper coloring of `M`.  The two remaining edges at `a` and `b`
get the same color (they are the ends of the odd-length path completing the even
cycle through `s(a,b)`), so the removed edge can be given the opposite color.
-/
set_option maxHeartbeats 1000000 in
lemma epc_cycle_step (M : SimpleGraph V) [DecidableRel M.Adj]
    (hdeg : ∀ v, M.degree v ≤ 2)
    (hno : ∀ (x : V) (w : M.Walk x x), w.IsCycle → ¬ Odd w.length)
    (heven : ∀ v, Even (M.degree v))
    {a b : V} (hab : M.Adj a b)
    (col' : Sym2 V → Bool)
    (hcol' : ∀ (v : V) (bb : Bool),
      #{f ∈ (M.deleteEdges {s(a, b)}).incidenceFinset v | col' f = bb} ≤ 1) :
    ∃ col : Sym2 V → Bool,
      ∀ (v : V) (bb : Bool), #{f ∈ M.incidenceFinset v | col f = bb} ≤ 1 := by
  obtain ⟨fa, fb, hfa, hfb, h_eq⟩ := epc_cycle_key M hdeg hno heven hab col' hcol';
  refine' ⟨ fun f => if f = s(a, b) then !col' fa else col' f, fun v bb => _ ⟩;
  by_cases hv : v = a ∨ v = b;
  · rcases hv with ( rfl | rfl );
    · rw [ show M.incidenceFinset v = insert s(v, b) ( ( M.deleteEdges { s(v, b) } ).incidenceFinset v ) from ?_ ];
      · rw [ Finset.filter_insert, hfa ] ; simp +decide [ Finset.filter_singleton ];
        grind;
      · simp +decide [ SimpleGraph.incidenceFinset, SimpleGraph.incidenceSet ];
        ext x; by_cases hx : x = s(v, b) <;> simp +decide [ hx, hab ] ;
    · have h_incidence : M.incidenceFinset v = insert s(a, v) {fb} := by
        simp_all +decide [ Finset.ext_iff, SimpleGraph.incidenceFinset ];
        intro f; specialize hfb f; by_cases hf : f = s(a, v) <;> simp_all +decide [ SimpleGraph.incidenceSet ] ;
      simp_all +decide [ Finset.filter_insert, Finset.filter_singleton ];
      split_ifs <;> simp_all +decide [ Finset.card_insert_of_notMem ];
  · convert hcol' v bb using 2;
    ext f; simp [hv];
    split_ifs <;> simp_all +decide [ SimpleGraph.incidenceSet ]

/-
Strong induction on the number of edges: every max-degree-≤2 graph with no odd
cycle has a proper `Bool`-edge-coloring.
-/
lemma epc_aux :
    ∀ (n : ℕ) (M : SimpleGraph V) [DecidableRel M.Adj], M.edgeFinset.card = n →
    (∀ v, M.degree v ≤ 2) →
    (∀ (x : V) (w : M.Walk x x), w.IsCycle → ¬ Odd w.length) →
    ∃ col : Sym2 V → Bool,
      ∀ (v : V) (bb : Bool), #{f ∈ M.incidenceFinset v | col f = bb} ≤ 1 := by
  intros n M _ hcard hdeg hno
  induction' n using Nat.strong_induction_on with n ih generalizing M;
  by_cases h : ∃ v : V, M.degree v = 1;
  · obtain ⟨a, ha⟩ : ∃ a : V, M.degree a = 1 := h
    obtain ⟨b, hab⟩ : ∃ b : V, M.Adj a b := by
      exact Exists.elim ( M.degree_pos_iff_exists_adj a |>.1 ( by linarith ) ) fun b hb => ⟨ b, hb ⟩
    set M' := M.deleteEdges {s(a, b)} with hM';
    have hM'_card : M'.edgeFinset.card < n := by
      grind +suggestions;
    obtain ⟨col', hcol'⟩ : ∃ col' : Sym2 V → Bool, ∀ v : V, ∀ bb : Bool, #{f ∈ M'.incidenceFinset v | col' f = bb} ≤ 1 := by
      apply ih (M'.edgeFinset.card) hM'_card M' rfl;
      · intro v;
        exact le_trans ( SimpleGraph.degree_le_of_le ( SimpleGraph.deleteEdges_le _ ) ) ( hdeg v );
      · exact fun x w hw => noOdd_deleteEdges M s(a, b) hno x w hw
    exact epc_leaf_step M hdeg hab ha col' hcol';
  · by_cases h : ∃ a b : V, M.Adj a b;
    · obtain ⟨ a, b, hab ⟩ := h;
      obtain ⟨col', hcol'⟩ : ∃ col' : Sym2 V → Bool, ∀ v : V, ∀ bb : Bool, #{f ∈ (M.deleteEdges {s(a, b)}).incidenceFinset v | col' f = bb} ≤ 1 := by
        apply ih (M.deleteEdges {s(a, b)}).edgeFinset.card;
        · grind +suggestions;
        · rfl;
        · exact fun v => le_trans ( SimpleGraph.degree_le_of_le ( SimpleGraph.deleteEdges_le _ ) ) ( hdeg v );
        · exact fun x w hw => noOdd_deleteEdges M s(a, b) hno x w hw
      apply epc_cycle_step M hdeg hno (fun v => by
        grind +qlia) hab col' hcol';
    · use fun _ => false; simp +decide [ SimpleGraph.incidenceFinset ] ;
      simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ]

/-- **Bipartite case.** A max-degree-≤2 graph with no odd cycle has a proper
`Bool`-edge-coloring (every vertex sees each color at most once). -/
lemma exists_proper_two_edge_coloring (M : SimpleGraph V) [DecidableRel M.Adj]
    (hdeg : ∀ v, M.degree v ≤ 2)
    (hno : ∀ (x : V) (w : M.Walk x x), w.IsCycle → ¬ Odd w.length) :
    ∃ col : Sym2 V → Bool,
      ∀ v, ∀ b : Bool, #{f ∈ M.incidenceFinset v | col f = b} ≤ 1 :=
  epc_aux M.edgeFinset.card M rfl hdeg hno


/-- PROVED (round 3).  Alternating each path/even-cycle component of a
zero-odd split yields a proper four-edge-coloring: `exists_proper_two_edge_coloring`
on each half, assembled by `combine` and bounded by `cnt_combine_le_one`. -/
lemma P2_equiv_fwd
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : HasZeroOddSplit G) :
    ∃ c : Sym2 V → Fin 4, IsProper4 G c := by
  obtain ⟨H₀, H₁, i₀, i₁, hsplit, hno₀, hno₁⟩ := h
  letI : DecidableRel H₀.Adj := i₀
  letI : DecidableRel H₁.Adj := i₁
  obtain ⟨hpart, hdisj, hsub₀, hsub₁, hd₀, hd₁, hsum⟩ := hsplit
  obtain ⟨b₀, hb₀⟩ := exists_proper_two_edge_coloring H₀ hd₀ hno₀
  obtain ⟨b₁, hb₁⟩ := exists_proper_two_edge_coloring H₁ hd₁ hno₁
  exact ⟨combine H₀ b₀ b₁,
    fun v α => cnt_combine_le_one G H₀ H₁ hpart b₀ b₁ hb₀ hb₁ v α⟩

/-! ## Color-pair halves of a proper 4-coloring (transplanted sorry-free from the
`r4w4_p2equiv` Aristotle return, wave-4 payload, statements identical; the return's
`Conf`/walk-surgery route to the FORWARD direction was NOT transplanted — our
`P2_equiv_fwd` is already closed — and is recorded as an independent second proof). -/

/-- The subgraph of `G` retaining exactly the edges whose color satisfies `P`. -/
def colSub (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 4)
    (P : Fin 4 → Prop) [DecidablePred P] : SimpleGraph V where
  Adj u v := G.Adj u v ∧ P (c s(u, v))
  symm := by rintro u v ⟨h1, h2⟩; exact ⟨h1.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun v h => (G.ne_of_adj h.1) rfl⟩

instance instDecColSub (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 4)
    (P : Fin 4 → Prop) [DecidablePred P] : DecidableRel (colSub G c P).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj u v ∧ P (c s(u, v))))

/-
ROUTINE.  The incidence set of a `colSub` is the color-filtered incidence set.
-/
lemma incidenceFinset_colSub (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 4)
    (P : Fin 4 → Prop) [DecidablePred P] (v : V) :
    (colSub G c P).incidenceFinset v = {e ∈ G.incidenceFinset v | P (c e)} := by
  ext e; simp [colSub];
  induction e using Sym2.inductionOn ; simp +decide [ *, SimpleGraph.incidenceSet ];
  tauto


/-
CRUX (backward parity).  A proper edge 2-coloring forbids odd cycles: along a
cycle the incident edges alternate the two colors, so the length is even.
-/
lemma even_length_of_proper (H : SimpleGraph V) [DecidableRel H.Adj]
    (col : Sym2 V → Bool)
    (hproper : ∀ (v : V) (b : Bool), #{e ∈ H.incidenceFinset v | col e = b} ≤ 1)
    {x : V} (w : H.Walk x x) (hc : w.IsCycle) : Even w.length := by
  -- By the properties of the coloring and the cycle, we can show that the colors of the edges must alternate.
  have h_alternating : ∀ i < w.length - 1, col (s(w.getVert i, w.getVert (i + 1))) ≠ col (s(w.getVert (i + 1), w.getVert (i + 2))) := by
    intro i hi
    have h_distinct : s(w.getVert i, w.getVert (i + 1)) ≠ s(w.getVert (i + 1), w.getVert (i + 2)) := by
      intro h_eq
      have h_distinct : w.getVert i = w.getVert (i + 2) := by
        grind +suggestions;
      have h_inj : Set.InjOn w.getVert {i | 1 ≤ i ∧ i ≤ w.length} := by
        exact Walk.IsCycle.getVert_injOn hc;
      have := h_inj ( show 1 ≤ i + 2 ∧ i + 2 ≤ w.length from ⟨ by linarith, by omega ⟩ ) ( show 1 ≤ i ∧ i ≤ w.length from ⟨ Nat.pos_of_ne_zero ( by
                                                                                            rintro rfl; simp_all +decide [ SimpleGraph.Walk.getVert ] ;
                                                                                            have := h_inj ( show 1 ≤ 2 ∧ 2 ≤ w.length from ⟨ by linarith, by linarith ⟩ ) ( show 1 ≤ w.length ∧ w.length ≤ w.length from ⟨ by linarith, by linarith ⟩ ) ; simp_all +decide [ SimpleGraph.Walk.getVert ] ;
                                                                                            exact absurd ( hc.three_le_length ) ( by linarith ) ), by omega ⟩ ) ; simp_all +decide ;
    have h_inc : s(w.getVert i, w.getVert (i + 1)) ∈ H.incidenceSet (w.getVert (i + 1)) ∧ s(w.getVert (i + 1), w.getVert (i + 2)) ∈ H.incidenceSet (w.getVert (i + 1)) := by
      simp +decide [ SimpleGraph.incidenceSet ];
      exact ⟨ w.adj_getVert_succ ( by omega ), w.adj_getVert_succ ( by omega ) ⟩
    have h_contra : col (s(w.getVert i, w.getVert (i + 1))) ≠ col (s(w.getVert (i + 1), w.getVert (i + 2))) := by
      intro h_eq
      have h_contra : #({e ∈ H.incidenceFinset (w.getVert (i + 1)) | col e = col (s(w.getVert i, w.getVert (i + 1)))}) ≥ 2 := by
        refine' Finset.one_lt_card.mpr ⟨ s(w.getVert i, w.getVert (i + 1)), _, s(w.getVert (i + 1), w.getVert (i + 2)), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.incidenceSet ];
      exact not_lt_of_ge h_contra ( lt_of_le_of_lt ( hproper _ _ ) ( by decide ) )
    exact h_contra;
  -- By the properties of the coloring and the cycle, we can show that the colors of the edges must alternate, leading to a contradiction if the length is odd.
  have h_contradiction : col (s(w.getVert (w.length - 1), w.getVert 0)) ≠ col (s(w.getVert 0, w.getVert 1)) := by
    have h_distinct : w.getVert (w.length - 1) ≠ w.getVert 1 := by
      have := hc.getVert_injOn';
      have := hc.three_le_length; rcases n : w.length with ( _ | _ | _ | n ) <;> simp_all +decide ;
      exact this.ne ( by simp +decide ) ( by simp +decide ) ( by simp +decide );
    contrapose! hproper;
    refine' ⟨ w.getVert 0, col s(w.getVert 0, w.getVert 1), _ ⟩;
    refine' Finset.one_lt_card.mpr ⟨ s(w.getVert 0, w.getVert 1), _, s(w.getVert (w.length - 1), w.getVert 0), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.incidenceSet ];
    · cases w <;> simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ];
    · convert w.adj_getVert_succ ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) zero_lt_one ) using 1;
      rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr ( by aesop_cat ) ), w.getVert_length ];
    · exact ⟨ fun h => Ne.symm h_distinct, Ne.symm h_distinct ⟩;
  have h_alternating : ∀ i < w.length, col (s(w.getVert i, w.getVert (i + 1))) = if i % 2 = 0 then col (s(w.getVert 0, w.getVert 1)) else !col (s(w.getVert 0, w.getVert 1)) := by
    intro i hi
    induction' i with i ih;
    · rfl;
    · specialize ih ( Nat.lt_of_succ_lt hi ) ; specialize h_alternating i ( Nat.lt_pred_iff.mpr hi ) ; split_ifs at * <;> simp_all +decide [ Nat.add_mod ] ;
      cases h : col s(x, w.getVert 1) <;> cases h' : col s(w.getVert (i + 1), w.getVert (i + 2)) <;> simp_all +decide only;
  specialize h_alternating ( w.length - 1 ) ; rcases n : w.length with ( _ | _ | k ) <;> simp_all +decide [ Nat.even_add_one ] ;
  · exact absurd n ( by linarith [ hc.three_le_length ] );
  · have := w.getVert_length; simp_all +decide [ Nat.even_iff ] ;
    omega


/-
CRUX (backward halves).  Each color-pair half of a proper 4-coloring has no
odd cycle, being a proper edge 2-colored (max-degree-2) graph.
-/
lemma noOddCycle_colSub (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 4)
    (a b : Fin 4) (hab : a ≠ b) (hc : IsProper4 G c) :
    NoOddCycle (colSub G c (fun x => x = a ∨ x = b)) := by
  intro x w hw;
  have := even_length_of_proper (colSub G c fun x => x = a ∨ x = b) (fun e => decide (c e = b)) (by
  intro v b_1
  simp [incidenceFinset_colSub];
  convert hc v ( if b_1 then b else a ) using 1;
  congr 1 with e ; aesop) w hw;
  exact this.elim fun k hk => by simp +decide [ hk ] ;

/-
ROUTINE (backward split).  The color-pair halves `{0,1}` and `{2,3}` of a
proper 4-coloring form an edge split of `G`.
-/
lemma isEdgeSplit_colSub (G : SimpleGraph V) [DecidableRel G.Adj] (c : Sym2 V → Fin 4)
    (hc : IsProper4 G c) :
    IsEdgeSplit G (colSub G c (fun a => a = 0 ∨ a = 1))
      (colSub G c (fun a => a = 2 ∨ a = 3)) := by
  constructor;
  · intro u v; simp +decide [ colSub ] ;
    grind;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · unfold colSub; aesop;
    · exact fun u v h => h.1;
    · exact fun u v h => h.1;
    · intro v
      have h_card : (colSub G c (fun a => a = 0 ∨ a = 1)).degree v = Finset.card (Finset.filter (fun e => c e = 0 ∨ c e = 1) (G.incidenceFinset v)) := by
        convert congr_arg Finset.card ( incidenceFinset_colSub G c ( fun a => a = 0 ∨ a = 1 ) v ) using 1;
        exact Eq.symm (card_incidenceFinset_eq_degree (colSub G c fun a ↦ a = 0 ∨ a = 1) v);
      rw [ h_card, Finset.filter_or ];
      exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( hc v 0 ) ( hc v 1 ) );
    · constructor;
      · intro v;
        convert Nat.le_trans ( Finset.card_le_card ( show ( colSub G c fun a => a = 2 ∨ a = 3 ).incidenceFinset v ⊆ Finset.filter ( fun e => c e = 2 ∨ c e = 3 ) ( G.incidenceFinset v ) from ?_ ) ) ?_ using 1;
        · exact Eq.symm (card_incidenceFinset_eq_degree (colSub G c fun a ↦ a = 2 ∨ a = 3) v);
        · simp +decide [ Finset.subset_iff, incidenceFinset_colSub ];
        · have := hc v 2; have := hc v 3; simp_all +decide [ Finset.filter_or ] ;
          exact le_trans ( Finset.card_union_le _ _ ) ( add_le_add ‹cnt G c v 2 ≤ 1› ‹cnt G c v 3 ≤ 1› );
      · intro v;
        rw [ SimpleGraph.degree, SimpleGraph.degree, SimpleGraph.degree ];
        rw [ ← Finset.card_union_of_disjoint ];
        · congr with w ; simp +decide [ colSub ];
          grind +revert;
        · simp +decide [ Finset.disjoint_left, colSub ];
          grind


/-- PROVED (transplant, round 5).  Pairing the color classes of a proper
four-edge-coloring yields two maximum-degree-two halves (the `{0,1}` and `{2,3}`
color-pair subgraphs), and every cycle in either half alternates two colors and
is therefore even. -/
lemma P2_equiv_bwd
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Sym2 V → Fin 4) (hc : IsProper4 G c) :
    HasZeroOddSplit G :=
  ⟨colSub G c (fun a => a = 0 ∨ a = 1), colSub G c (fun a => a = 2 ∨ a = 3),
    inferInstance, inferInstance, isEdgeSplit_colSub G c hc,
    noOddCycle_colSub G c 0 1 (by decide) hc, noOddCycle_colSub G c 2 3 (by decide) hc⟩

/-- PROVED modulo the two explicitly tagged routine directions above. -/
theorem P2_equiv
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    HasZeroOddSplit G ↔ ∃ c : Sym2 V → Fin 4, IsProper4 G c := by
  constructor
  · exact P2_equiv_fwd G
  · rintro ⟨c, hc⟩
    exact P2_equiv_bwd G c hc

/-- PROVED.  The shortest class-I arm: proper directly implies SM by E1. -/
lemma classI_strongMajority
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Sym2 V → Fin 4)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hc : IsProper4 G c) :
    SMaj.IsStrongMajority G c :=
  E1_of_cnt_le_one G c hdeg hc

/-- PROVED.  Existential class-I arm. -/
lemma classI_arm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hI : ∃ c : Sym2 V → Fin 4, IsProper4 G c) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c := by
  obtain ⟨c, hc⟩ := hI
  exact ⟨c, classI_strongMajority G c hdeg hc⟩

/-- Number of degree-three vertices. -/
def numDeg3 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v : V => G.degree v = 3)).card

/-! ### Odd-cycle/parity toolbox (transplanted sorry-free from the
`r4w3_parity_pair` Aristotle return; `private` dropped for per-decl audit).
The first four lemmas are the odd-closed-walk => odd-cycle => bipartite chain —
exactly the machinery the open `P2_equiv_fwd`/`P2_equiv_bwd` pins need
(odd-cycle-free implies 2-colorable).  The last two feed `P2_onlyif`. -/

/-- A closed walk that is not a cycle but has odd length `≥ 3` contains a
strictly shorter closed walk of odd length. -/
lemma exists_shorter_odd_closed_walk {W : Type*} (H : SimpleGraph W)
    (u : W) (w : H.Walk u u) (hnc : ¬ w.IsCycle) (h3 : 3 ≤ w.length)
    (hodd : Odd w.length) :
    ∃ x, ∃ c : H.Walk x x, c.length < w.length ∧ Odd c.length := by
  classical
  have hnd : ¬ w.support.tail.Nodup := by
    intro hnd
    apply hnc
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, h3⟩
    have hnn : ¬ w.Nil := by rw [SimpleGraph.Walk.nil_iff_length_eq]; omega
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_tail_of_not_nil _ hnn]
    exact hnd
  obtain ⟨x, hxdup⟩ := List.exists_duplicate_iff_not_nodup.mpr hnd
  rw [List.duplicate_iff_two_le_count] at hxdup
  have hxtail : x ∈ w.support.tail := List.count_pos_iff.mp (by omega)
  have hx : x ∈ w.support := List.mem_of_mem_tail hxtail
  set w' := w.rotate hx with hw'
  have hlen : w'.length = w.length := by
    have := (w.rotate_darts hx).perm.length_eq
    simpa [SimpleGraph.Walk.length_darts] using this
  have hcount' : 2 ≤ w'.support.tail.count x := by
    have hp := (w.support_rotate hx).perm
    rw [hp.count_eq]; exact hxdup
  have hnn' : ¬ w'.Nil := by rw [SimpleGraph.Walk.nil_iff_length_eq]; omega
  obtain ⟨y, h₀, p, hpeq⟩ := SimpleGraph.Walk.not_nil_iff.mp hnn'
  have hps : p.support = w'.support.tail := by rw [hpeq]; simp
  have hpcount : 2 ≤ p.support.count x := by rw [hps]; exact hcount'
  have hxp : x ∈ p.support := List.count_pos_iff.mp (by omega)
  set r := p.takeUntil x hxp with hr
  set q := p.dropUntil x hxp with hq
  have hsum : r.length + q.length = p.length := by
    have h1 := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec p hxp)
    rwa [SimpleGraph.Walk.length_append] at h1
  have hpsupp : p.support = r.support ++ q.support.tail := by
    rw [hr, hq, ← SimpleGraph.Walk.support_append, SimpleGraph.Walk.take_spec]
  have hrcount : r.support.count x = 1 := SimpleGraph.Walk.count_support_takeUntil_eq_one p hxp
  have hqpos : 0 < q.length := by
    by_contra hcon
    push_neg at hcon
    have hq0 : q.length = 0 := by omega
    have htail : q.support.tail = [] := by
      have hl : q.support.length = 1 := by rw [SimpleGraph.Walk.length_support, hq0]
      have h0 : q.support.tail.length = 0 := by simp [List.length_tail, hl]
      exact List.length_eq_zero_iff.mp h0
    have : p.support.count x = 1 := by
      rw [hpsupp, List.count_append, htail, hrcount]; simp
    omega
  have hwlen : w.length = r.length + 1 + q.length := by
    rw [← hlen, hpeq, SimpleGraph.Walk.length_cons, ← hsum]; ring
  rcases Nat.even_or_odd r.length with hre | hro
  · refine ⟨x, SimpleGraph.Walk.cons h₀ r, ?_, ?_⟩
    · rw [SimpleGraph.Walk.length_cons]; omega
    · rw [SimpleGraph.Walk.length_cons]; exact hre.add_one
  · have hqodd : Odd q.length := by
      rcases hodd with ⟨m, hm⟩
      rcases hro with ⟨t, ht⟩
      exact ⟨m - t - 1, by omega⟩
    exact ⟨x, q, by omega, hqodd⟩

/-- An odd closed walk contains an odd cycle (strong induction on length). -/
lemma exists_odd_cycle_of_odd_closed_walk {W : Type*} (H : SimpleGraph W)
    (u : W) (w : H.Walk u u) (hodd : Odd w.length) :
    ∃ x, ∃ c : H.Walk x x, c.IsCycle ∧ Odd c.length := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, w.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing u w with
  | _ n ih =>
    subst hn
    have hne1 : w.length ≠ 1 := by
      cases w with
      | nil => simp
      | cons h p =>
        intro hl
        simp only [SimpleGraph.Walk.length_cons, Nat.add_eq_right] at hl
        obtain rfl := SimpleGraph.Walk.eq_of_length_eq_zero hl
        exact H.irrefl h
    have hpos : 0 < w.length := hodd.pos
    have h3 : 3 ≤ w.length := by
      rcases hodd with ⟨k, hk⟩; omega
    by_cases hc : w.IsCycle
    · exact ⟨u, w, hc, hodd⟩
    · obtain ⟨x, c, hlt, hcodd⟩ := exists_shorter_odd_closed_walk H u w hc h3 hodd
      exact ih c.length hlt x c hcodd rfl

/-- If a graph has no odd cycle, every closed walk has even length. -/
lemma closedWalk_even_of_no_odd_cycle {W : Type*} (H : SimpleGraph W)
    (hno : ∀ x (w : H.Walk x x), w.IsCycle → ¬ Odd w.length) :
    ∀ u (w : H.Walk u u), Even w.length := by
  intro u w
  by_contra h
  rw [Nat.not_even_iff_odd] at h
  obtain ⟨x, c, hcyc, hcodd⟩ := exists_odd_cycle_of_odd_closed_walk (H := H) u w h
  exact hno x c hcyc hcodd

/-- A graph with no odd cycle is `2`-colorable (bipartite). -/
lemma colorable_two_of_no_odd_cycle {W : Type*} (H : SimpleGraph W)
    (hno : ∀ x (w : H.Walk x x), w.IsCycle → ¬ Odd w.length) :
    H.Colorable 2 :=
  SimpleGraph.two_colorable_iff_forall_loop_even.mpr
    (closedWalk_even_of_no_odd_cycle H hno)

/-- A finite `2`-regular bipartite graph has an even number of vertices. -/
lemma even_card_of_two_regular_colorable (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = 2) (hc : H.Colorable 2) :
    Even (Fintype.card V) := by
  classical
  obtain ⟨c⟩ := hc
  set A : Finset V := Finset.univ.filter (fun v => c v = 0) with hA
  set B : Finset V := Finset.univ.filter (fun v => c v = 1) with hB
  have hbip : H.IsBipartiteWith (↑A : Set V) (↑B : Set V) := by
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro v hvA hvB
      simp only [hA, hB, coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hvA hvB
      rw [hvA] at hvB; exact absurd hvB (by decide)
    · intro v w hvw
      have hne := c.valid hvw
      simp only [hA, hB, coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
      have hv2 : c v = 0 ∨ c v = 1 := by omega
      have hw2 : c w = 0 ∨ c w = 1 := by omega
      rcases hv2 with h | h <;> rcases hw2 with h' | h' <;> simp_all
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq hbip
  simp only [hreg] at hsum
  rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul] at hsum
  have hcardeq : A.card = B.card := by omega
  have hBeq : B = Finset.univ.filter (fun v => ¬ c v = 0) := by
    rw [hB]; apply Finset.filter_congr; intro v _
    constructor <;> intro h
    · rw [h]; decide
    · omega
  have hunion : A.card + B.card = Fintype.card V := by
    rw [hBeq, hA, Finset.card_filter_add_card_filter_not]
    rfl
  rw [← hunion, hcardeq]
  exact ⟨B.card, by ring⟩

/-- A finite `2`-regular graph with no odd cycle has an even number of vertices. -/
lemma even_card_of_two_regular_no_odd_cycle (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ v, H.degree v = 2)
    (hno : ∀ x (w : H.Walk x x), w.IsCycle → ¬ Odd w.length) :
    Even (Fintype.card V) :=
  even_card_of_two_regular_colorable H hreg (colorable_two_of_no_odd_cycle H hno)

/-- PROVED (true parity obstruction; unused by the final case split; proof
transplanted from the `r4w3_parity_pair` return and re-attached to THIS file's
`HasZeroOddSplit`/`IsEdgeSplit` packaging — the stale return stated the split
contract inline; only fields present in `IsEdgeSplit` are consumed).
If `|V|` is odd and at most two vertices have degree three, every balanced
degree-two split contains an odd cycle. -/
lemma P2_onlyif
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hn : Odd (Fintype.card V)) (ht : numDeg3 G ≤ 2) :
    ¬ HasZeroOddSplit G := by
  rintro ⟨H₁, H₂, i1, i2, hsplit, hno1, hno2⟩
  obtain ⟨hpart, hdisj, hsub1, hsub2, hd1, hd2, hdegsum⟩ := hsplit
  -- Per-vertex bounds: each part has degree in `{1,2}` at every vertex.
  have hb1 : ∀ v, 1 ≤ H₁.degree v ∧ H₁.degree v ≤ 2 := by
    intro v
    have hs := hdegsum v; have h2 := hd2 v; have h1 := hd1 v
    rcases hdeg v with h | h <;> omega
  have hb2 : ∀ v, 1 ≤ H₂.degree v ∧ H₂.degree v ≤ 2 := by
    intro v
    have hs := hdegsum v; have h2 := hd2 v; have h1 := hd1 v
    rcases hdeg v with h | h <;> omega
  -- At least one of the two parts is `2`-regular.
  have key : (∀ v, H₁.degree v = 2) ∨ (∀ v, H₂.degree v = 2) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hcon
    have hp1 : H₁.degree p = 1 := by have := hb1 p; omega
    have hpd3 : G.degree p = 3 ∧ H₂.degree p = 2 := by
      have hs := hdegsum p; have := hd2 p; rcases hdeg p with h | h <;> omega
    have hq1 : H₂.degree q = 1 := by have := hb2 q; omega
    have hqd3 : G.degree q = 3 ∧ H₁.degree q = 2 := by
      have hs := hdegsum q; have := hd1 q; rcases hdeg q with h | h <;> omega
    have hpq : p ≠ q := by
      rintro rfl; have := hpd3.2; have := hq1; omega
    -- The degree-3 set is exactly `{p, q}`.
    have hsub : ({p, q} : Finset V) ⊆ Finset.univ.filter (fun v => G.degree v = 3) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl
      · exact hpd3.1
      · exact hqd3.1
    have hcardle : (Finset.univ.filter (fun v => G.degree v = 3)).card ≤ 2 := ht
    have hDeq : ({p, q} : Finset V) = Finset.univ.filter (fun v => G.degree v = 3) :=
      Finset.eq_of_subset_of_card_le hsub
        (by rw [Finset.card_pair hpq]; exact hcardle)
    -- Then `H₁` has exactly one odd-degree vertex, namely `p` — impossible (handshake).
    have hseteq : Finset.univ.filter (fun v => Odd (H₁.degree v)) = {p} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hodd
        have hbv := hb1 v
        have hv1 : H₁.degree v = 1 := by
          rcases Nat.lt_or_ge (H₁.degree v) 2 with hlt | hge
          · omega
          · exact absurd (by rw [show H₁.degree v = 2 by omega] at hodd; exact hodd)
              (by decide)
        have hvd3 : G.degree v = 3 := by
          have hs := hdegsum v; have := hd2 v; rcases hdeg v with h | h <;> omega
        have hvD : v ∈ Finset.univ.filter (fun w => G.degree w = 3) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hvd3
        rw [← hDeq] at hvD
        simp only [Finset.mem_insert, Finset.mem_singleton] at hvD
        rcases hvD with rfl | rfl
        · rfl
        · rw [hqd3.2] at hv1; exact absurd hv1 (by decide)
      · rintro rfl; rw [hp1]; decide
    have hodd1 := SimpleGraph.even_card_odd_degree_vertices H₁
    rw [hseteq, Finset.card_singleton] at hodd1
    exact (Nat.not_even_one) hodd1
  -- One `2`-regular, odd-cycle-free part forces an even vertex count — contra `hn`.
  rcases key with hreg | hreg
  · exact (Nat.not_even_iff_odd.mpr hn)
      (@even_card_of_two_regular_no_odd_cycle V _ _ H₁ i1 hreg hno1)
  · exact (Nat.not_even_iff_odd.mpr hn)
      (@even_card_of_two_regular_no_odd_cycle V _ _ H₂ i2 hreg hno2)

/-! ## Exact defect calculus, with no bound on the number of defects -/

/-- Boolean load contributed by one half. -/
def halfCount
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (v : V) (a : Bool) : ℕ :=
  #{e ∈ H.incidenceFinset v | b e = a}

/-- The SM cap belonging to an edge with endpoints `u,v`. -/
def cap (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  (G.degree u + G.degree v - 2) / 2

/-- Cross-safety of the Boolean coloring of `H` on every foreign `K` edge. -/
def CrossSafe
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (b : Sym2 V → Bool) : Prop :=
  ∀ u v, K.Adj u v → ∀ a : Bool,
    halfCount H b u a + halfCount H b v a ≤ cap G u v

/-- `D` contains exactly one vertex on every odd-cycle support, and no
vertices outside odd cycles.  In a maximum-degree-two graph this is exactly
one rotatable defect per odd-cycle component. -/
def IsOddCycleDefectSet (H : SimpleGraph V) (D : Finset V) : Prop :=
  (∀ v, v ∈ D → ∃ (x : V) (w : H.Walk x x),
      w.IsCycle ∧ Odd w.length ∧ v ∈ w.support) ∧
  (∀ x (w : H.Walk x x), w.IsCycle → Odd w.length →
      ∃! v : V, v ∈ w.support ∧ v ∈ D)

/-- Load profile of an alternating coloring with signed defects.  This
definition permits arbitrarily many defects. -/
def DefectProfile
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (D : Finset V) (σ : V → Bool) : Prop :=
  (∀ v, v ∈ D →
      H.degree v = 2 ∧
      halfCount H b v (σ v) = 2 ∧
      halfCount H b v (Bool.not (σ v)) = 0) ∧
  (∀ v, v ∉ D → ∀ a : Bool, halfCount H b v a ≤ 1)

/-- Minimum-defect alternation: exactly one signed defect per odd-cycle
component and no other repeated color. -/
def IsMinAlternating
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (D : Finset V) (σ : V → Bool) : Prop :=
  IsOddCycleDefectSet H D ∧ DefectProfile H b D σ

/-- Exact local safety rules from the defect calculus.

On a cap-two foreign edge, an `α`-defect is safe exactly when the other
endpoint is an opposite-sign defect, or is degree one in `H` and has zero
`α`-load.  On a cap-three edge, two defects must have opposite signs. -/
def DefectSafe
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (b : Sym2 V → Bool) (D : Finset V) (σ : V → Bool) : Prop :=
  ∀ u v, K.Adj u v →
    (cap G u v = 2 →
      (u ∈ D →
        ((v ∈ D ∧ σ v ≠ σ u) ∨
          (H.degree v = 1 ∧ halfCount H b v (σ u) = 0))) ∧
      (v ∈ D →
        ((u ∈ D ∧ σ u ≠ σ v) ∨
          (H.degree u = 1 ∧ halfCount H b u (σ v) = 0)))) ∧
    (cap G u v = 3 →
      u ∈ D → v ∈ D → σ u ≠ σ v)

/-! ## Cross/defect calculus helpers (transplanted sorry-free from the
`r4w4_defect_iff` Aristotle return; `cap_eq_three_iff` from `r4w5_crux_bricked`).
These close the two remaining ROUTINE-EXPECTED local-calculus pins below. -/

/-! ### Helper lemmas for the cross/defect calculus -/

/-- PROVED.  Every incident edge is colored `true` or `false`, so the two
half-loads at `v` add up to the `H`-degree of `v`. -/
lemma halfCount_true_add_false
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (v : V) :
    halfCount H b v true + halfCount H b v false = H.degree v := by
  unfold halfCount
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  rw [← Finset.card_filter_add_card_filter_not (s := H.incidenceFinset v)
        (p := fun e => b e = true)]
  congr 2
  ext e
  simp only [Bool.not_eq_true]

/-- PROVED.  Signed variant of `halfCount_true_add_false`. -/
lemma halfCount_add_not
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (v : V) (a : Bool) :
    halfCount H b v a + halfCount H b v (!a) = H.degree v := by
  cases a with
  | false => rw [add_comm]; simpa using halfCount_true_add_false H b v
  | true => simpa using halfCount_true_add_false H b v

/-- PROVED.  A half-load never exceeds the degree. -/
lemma halfCount_le_degree
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (v : V) (a : Bool) :
    halfCount H b v a ≤ H.degree v := by
  unfold halfCount
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  exact Finset.card_filter_le _ _

/-- PROVED.  In any degree-two split of a `{3,4}`-graph each half has
degree `1` or `2` at every vertex. -/
lemma half_degree_bounds
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K) (v : V) :
    1 ≤ H.degree v ∧ H.degree v ≤ 2 := by
  obtain ⟨_, _, _, _, hH, hK, hsum⟩ := hsplit
  have := hH v; have := hK v; have := hsum v; have := hdeg v
  omega

/-- PROVED.  The SM cap of any edge in a `{3,4}`-graph is `2` or `3`. -/
lemma cap_two_or_three
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4) (u v : V) :
    cap G u v = 2 ∨ cap G u v = 3 := by
  unfold cap
  rcases hdeg u with h | h <;> rcases hdeg v with h' | h' <;> rw [h, h'] <;> omega

/-
BRIDGE.  Color `0` of `combine` counts the `false`-edges of `H₀`.
-/
lemma cnt_combine_H0_false
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hle : H₀ ≤ G) (b₀ b₁ : Sym2 V → Bool) (v : V) :
    cnt G (combine H₀ b₀ b₁) v 0 = halfCount H₀ b₀ v false := by
  refine' congr_arg Finset.card ( Finset.ext fun e => _ );
  by_cases he : e ∈ H₀.edgeFinset <;> simp +decide [ he, combine ];
  · by_cases hev : v ∈ e <;> simp +decide [ hev, SimpleGraph.incidenceSet ];
    cases e ; aesop;
  · split_ifs <;> simp_all +decide [ SimpleGraph.incidenceSet ]

/-
BRIDGE.  Color `1` of `combine` counts the `true`-edges of `H₀`.
-/
lemma cnt_combine_H0_true
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hle : H₀ ≤ G) (b₀ b₁ : Sym2 V → Bool) (v : V) :
    cnt G (combine H₀ b₀ b₁) v 1 = halfCount H₀ b₀ v true := by
  refine' congr_arg Finset.card ( Finset.ext fun x => _ );
  simp +decide [ combine, SimpleGraph.incidenceSet ];
  cases x ; aesop

/-
BRIDGE.  Color `2` of `combine` counts the `false`-edges of `H₁`.
-/
lemma cnt_combine_H1_false
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hsplit : IsEdgeSplit G H₀ H₁) (b₀ b₁ : Sym2 V → Bool) (v : V) :
    cnt G (combine H₀ b₀ b₁) v 2 = halfCount H₁ b₁ v false := by
  refine' congr_arg Finset.card ( Finset.ext fun x => _ );
  cases hsplit;
  unfold combine; simp +decide [ *, SimpleGraph.mem_incidenceFinset ] ;
  rcases x with ⟨ u, v ⟩ ; simp +decide [ *, SimpleGraph.incidenceSet ] ;
  grind

/-
BRIDGE.  Color `3` of `combine` counts the `true`-edges of `H₁`.
-/
lemma cnt_combine_H1_true
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hsplit : IsEdgeSplit G H₀ H₁) (b₀ b₁ : Sym2 V → Bool) (v : V) :
    cnt G (combine H₀ b₀ b₁) v 3 = halfCount H₁ b₁ v true := by
  refine' congr_arg Finset.card ( Finset.ext fun x => _ );
  simp +decide [ SimpleGraph.incidenceSet, combine ];
  split_ifs <;> simp_all +decide [ IsEdgeSplit ]; all_goals cases x ; aesop

/-
SAME-HALF BOUND.  On an edge of `H` itself, the two half-loads of a
color `a` are compensated by the `+2·[b s(u,v)=a]` own-edge term.
-/
lemma same_half_bound
    (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHle : ∀ w, H.degree w ≤ 2)
    (b : Sym2 V → Bool) {u v : V} (huv : H.Adj u v) (a : Bool)
    (hcap : 2 ≤ cap G u v) :
    halfCount H b u a + halfCount H b v a
      ≤ cap G u v + 2 * (if b s(u, v) = a then 1 else 0) := by
  split_ifs <;> simp_all +decide;
  · linarith [ hHle u, hHle v, show halfCount H b u a ≤ H.degree u from halfCount_le_degree H b u a, show halfCount H b v a ≤ H.degree v from halfCount_le_degree H b v a ];
  · -- Since $b s(u, v) \neq a$, we have $1 \leq halfCount H b u (not a)$ and $1 \leq halfCount H b v (not a)$.
    have h_halfCount_not_a_u : 1 ≤ halfCount H b u (not a) := by
      refine' Finset.card_pos.mpr ⟨ s(u, v), _ ⟩ ; simp_all +decide [ halfCount ];
      cases a <;> aesop
    have h_halfCount_not_a_v : 1 ≤ halfCount H b v (not a) := by
      refine' Finset.card_pos.mpr ⟨ Sym2.mk ( v, u ), _ ⟩ ; simp_all +decide [ SimpleGraph.adj_comm ];
      cases a <;> simp_all +decide [ Sym2.eq_swap ];
    grind +suggestions


omit [DecidableEq V] in
/-- PROVED helper.  The cap is `3` exactly when both endpoints have degree `4`. -/
lemma cap_eq_three_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4) (u v : V) :
    cap G u v = 3 ↔ (G.degree u = 4 ∧ G.degree v = 4) := by
  unfold cap
  rcases hdeg u with hu | hu <;> rcases hdeg v with hv | hv <;>
    rw [hu, hv] <;> simp


set_option maxHeartbeats 1000000 in
/-- ROUTINE-EXPECTED.  Exact equivalence between the signed local rules and
the foreign endpoint-count inequalities.  It applies to any number of defects. -/
lemma defectSafe_iff_crossSafe
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (b : Sym2 V → Bool) (D : Finset V) (σ : V → Bool)
    (hprofile : DefectProfile H b D σ) :
    DefectSafe G H K b D σ ↔ CrossSafe G H K b := by
  constructor;
  · intro hdefect;
    intro u v huv a
    specialize hdefect u v huv
    cases' cap_two_or_three G hdeg u v with hcap hcap;
    · by_cases hu : u ∈ D <;> by_cases hv : v ∈ D <;> simp_all +decide only [DefectProfile];
      · cases h : σ u <;> cases h' : σ v <;> simp_all +decide only [not_true];
        · grind;
        · cases a <;> simp_all +decide [ halfCount ];
          · have := hprofile.1 u hu; have := hprofile.1 v hv; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ;
          · have := hprofile.1 u hu; have := hprofile.1 v hv; simp_all +decide [ Finset.filter_eq', Finset.filter_ne' ] ;
        · cases a <;> simp_all +decide [ halfCount_add_not ];
          · grind;
          · have := hprofile.1 u hu; have := hprofile.1 v hv; simp_all +decide ;
        · grind;
      · cases' em ( a = σ u ) with ha ha <;> simp_all +decide [ halfCount_add_not ];
        cases' em ( a = true ) with ha ha <;> simp_all +decide [ halfCount_add_not ];
        · grind +suggestions;
        · grind +splitIndPred;
      · by_cases ha : a = σ v <;> simp_all +decide;
        cases a <;> cases σ v <;> simp_all +decide;
        · grind +suggestions;
        · grind +suggestions;
        · grind +splitIndPred;
        · grind +splitIndPred;
      · linarith [ hprofile.2 u hu a, hprofile.2 v hv a ];
    · by_cases huD : u ∈ D <;> by_cases hvD : v ∈ D <;> simp_all +decide only [DefectProfile];
      · cases a <;> simp_all +decide only [cap];
        · cases h : σ u <;> cases h' : σ v <;> simp_all +decide only [halfCount];
          · tauto;
          · have := hprofile.1 u huD; have := hprofile.1 v hvD; simp_all +decide ;
            rw [ Finset.card_eq_zero.mpr ] <;> simp_all +decide [ Finset.ext_iff ];
          · have := hprofile.1 u huD; have := hprofile.1 v hvD; simp_all +decide ;
            rw [ Finset.card_eq_zero.mpr ] <;> aesop;
          · tauto;
        · cases h : σ u <;> cases h' : σ v <;> simp_all +decide only;
          · tauto;
          · grind +splitIndPred;
          · grind;
          · tauto;
      · grind +suggestions;
      · grind +suggestions;
      · linarith [ hprofile.2 u huD a, hprofile.2 v hvD a ];
  · intro hcs u v huv;
    constructor;
    · intro hcap
      constructor;
      · intro huD
        have h_halfCount_u : halfCount H b u (σ u) = 2 := by
          exact hprofile.1 u huD |>.2.1
        have h_halfCount_v : halfCount H b v (σ u) ≤ 0 := by
          have := hcs u v huv ( σ u ) ; simp_all +decide ;
        have h_halfCount_v_zero : halfCount H b v (σ u) = 0 := by
          exact le_antisymm h_halfCount_v ( Nat.zero_le _ )
        by_cases hvD : v ∈ D;
        · have := hprofile.1 v hvD; simp_all +decide ;
          grind;
        · have := hprofile.2 v hvD ( σ u ) ; have := hprofile.2 v hvD ( ! ( σ u ) ) ; simp_all +decide [ halfCount_add_not ] ;
          have := halfCount_add_not H b v ( σ u ) ; simp_all +decide ;
          exact le_antisymm ‹_› ( by linarith [ half_degree_bounds G H K hdeg hsplit v ] );
      · intro hvD
        have h_halfCount_v : halfCount H b v (σ v) = 2 := by
          exact hprofile.1 v hvD |>.2.1
        have h_halfCount_u : halfCount H b u (σ v) = 0 := by
          have := hcs u v huv ( σ v ) ; simp_all +decide [ cap ] ;
        have h_deg_u : H.degree u = 1 ∨ u ∈ D := by
          have := halfCount_add_not H b u (σ v);
          by_cases huD : u ∈ D <;> simp_all +decide;
          have := hprofile.2 u huD ( !σ v ) ; simp_all +decide ;
          exact le_antisymm this ( by linarith [ half_degree_bounds G H K hdeg hsplit u ] )
        cases' h_deg_u with huD huD
        · exact Or.inr ⟨huD, h_halfCount_u⟩
        · exact Or.inl ⟨huD, by
            have := hprofile.1 u huD; have := hprofile.1 v hvD; simp_all +decide [ halfCount ] ;
            contrapose! h_halfCount_u;
            exact Exists.elim ( Finset.card_pos.mp ( by linarith ) ) fun x hx => ⟨ x, by aesop ⟩⟩;
    · intro hcap hu hv;
      have := hcs u v huv ( σ u );
      cases hprofile.1 u hu ; cases hprofile.1 v hv ; aesop


set_option maxHeartbeats 1000000 in
/-- ROUTINE-EXPECTED.  Same-half colors are automatically safe by the
`-2[c(uv)=α]` term; the two `CrossSafe` hypotheses handle the foreign pairs. -/
lemma strongMajority_of_crossSafe_split
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H₀ H₁)
    (b₀ b₁ : Sym2 V → Bool)
    (hsafe₀ : CrossSafe G H₀ H₁ b₀)
    (hsafe₁ : CrossSafe G H₁ H₀ b₁) :
    SMaj.IsStrongMajority G (combine H₀ b₀ b₁) := by
  have hcap2 : ∀ u v, G.Adj u v → 2 ≤ cap G u v := by
    intro u v huv; rcases hdeg u with ha | ha <;> rcases hdeg v with hb | hb <;> simp +decide [ ha, hb, cap ] ;
  apply isStrongMajority_of_cnt;
  intro u v huv α; fin_cases α <;> simp +decide [ * ] ;
  · obtain hH0adj | hH1adj := ( hsplit.1 u v ).mp huv;
    · convert same_half_bound G H₀ ( fun w => hsplit.2.2.2.2.1 w ) b₀ hH0adj false ( hcap2 u v huv ) using 1;
      · rw [ cnt_combine_H0_false G H₀ H₁ hsplit.2.2.1 b₀ b₁ u, cnt_combine_H0_false G H₀ H₁ hsplit.2.2.1 b₀ b₁ v ];
      · unfold combine; simp +decide [ hH0adj, hsplit.2.2.1 ] ;
        rfl;
    · rw [ cnt_combine_H0_false G H₀ H₁ hsplit.2.2.1 b₀ b₁ u, cnt_combine_H0_false G H₀ H₁ hsplit.2.2.1 b₀ b₁ v ];
      have := hsafe₀ u v hH1adj false; simp_all +decide [ combine ] ;
      exact le_add_right this;
  · by_cases hH0adj : H₀.Adj u v <;> by_cases hH1adj : H₁.Adj u v <;> simp_all +decide [ IsEdgeSplit ];
    · convert same_half_bound G H₀ hsplit.2.2.2.2.1 b₀ hH0adj true ( hcap2 u v ( Or.inl hH0adj ) ) using 1;
      · rw [ cnt_combine_H0_true G H₀ H₁ hsplit.2.2.1 b₀ b₁ u, cnt_combine_H0_true G H₀ H₁ hsplit.2.2.1 b₀ b₁ v ];
      · unfold combine; simp +decide [ hH0adj ] ;
        rfl;
    · rw [ cnt_combine_H0_true G H₀ H₁ hsplit.2.2.1 b₀ b₁ u, cnt_combine_H0_true G H₀ H₁ hsplit.2.2.1 b₀ b₁ v ];
      refine' le_add_of_le_of_nonneg ( hsafe₀ u v hH1adj true ) ( Nat.zero_le _ );
  · obtain hH0adj | hH1adj := hsplit.1 u v |>.1 huv;
    · rw [ cnt_combine_H1_false G H₀ H₁ hsplit b₀ b₁ u, cnt_combine_H1_false G H₀ H₁ hsplit b₀ b₁ v ];
      split_ifs <;> simp_all +decide [ combine ];
      · grind +revert;
      · exact hsafe₁ u v ( by have := hsplit.2.1 u v; aesop ) false;
    · rw [ cnt_combine_H1_false G H₀ H₁ hsplit b₀ b₁ u, cnt_combine_H1_false G H₀ H₁ hsplit b₀ b₁ v ];
      convert same_half_bound G H₁ ( fun w => hsplit.2.2.2.2.2.1 w ) b₁ hH1adj false ( hcap2 u v huv ) using 1;
      unfold combine; simp +decide [ hH1adj ] ;
      have := hsplit.2.1 u v; aesop;
  · obtain hH0 | hH1 := hsplit.1 u v |>.1 huv;
    · rw [ cnt_combine_H1_true G H₀ H₁ hsplit b₀ b₁ u, cnt_combine_H1_true G H₀ H₁ hsplit b₀ b₁ v ];
      split_ifs <;> simp_all +decide [ combine ];
      · grind;
      · exact hsafe₁ u v ( by have := hsplit.2.1 u v; aesop ) true;
    · convert same_half_bound G H₁ ( fun w => hsplit.2.2.2.2.2.1 w ) b₁ hH1 true ( hcap2 u v huv ) using 1;
      · rw [ cnt_combine_H1_true G H₀ H₁ hsplit b₀ b₁ u, cnt_combine_H1_true G H₀ H₁ hsplit b₀ b₁ v ];
      · unfold combine; simp +decide [ hH1 ] ;
        grind +locals



/-- PROVED modulo the two ROUTINE-EXPECTED local-calculus lemmas above.
This is the general conditional defect-placement lemma requested by the
coordinator; `D₀,D₁` may be arbitrarily large. -/
lemma strongMajority_of_safe_defects
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H₀ H₁)
    (b₀ b₁ : Sym2 V → Bool)
    (D₀ D₁ : Finset V) (σ₀ σ₁ : V → Bool)
    (hprofile₀ : DefectProfile H₀ b₀ D₀ σ₀)
    (hprofile₁ : DefectProfile H₁ b₁ D₁ σ₁)
    (hsafe₀ : DefectSafe G H₀ H₁ b₀ D₀ σ₀)
    (hsafe₁ : DefectSafe G H₁ H₀ b₁ D₁ σ₁) :
    SMaj.IsStrongMajority G (combine H₀ b₀ b₁) := by
  apply strongMajority_of_crossSafe_split G H₀ H₁ hdeg hsplit b₀ b₁
  · exact (defectSafe_iff_crossSafe G H₀ H₁ hdeg hsplit b₀ D₀ σ₀ hprofile₀).mp hsafe₀
  · exact (defectSafe_iff_crossSafe G H₁ H₀ hdeg
      (IsEdgeSplit.swap G H₀ H₁ hsplit) b₁ D₁ σ₁ hprofile₁).mp hsafe₁

/-! ## Odd-cycle-minimal splits and the sole global open crux -/

/-- Finite set of supports of odd cycles.  For a maximum-degree-two graph,
its cardinality is the number of odd-cycle components. -/
noncomputable def oddCycleSupports (H : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (fun S : Finset V =>
    ∃ (x : V) (w : H.Walk x x),
      w.IsCycle ∧ Odd w.length ∧ w.support.toFinset = S)

noncomputable def oddCycleCount (H : SimpleGraph V) : ℕ :=
  (oddCycleSupports H).card

/-- A split minimizing the total number of odd-cycle components across both
halves.  Total, rather than per-half, minimality is the empirical invariant. -/
def IsOddCycleMinimalSplit
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj] : Prop :=
  IsEdgeSplit G H₀ H₁ ∧
  ∀ (K₀ K₁ : SimpleGraph V)
      (_ : DecidableRel K₀.Adj) (_ : DecidableRel K₁.Adj),
    IsEdgeSplit G K₀ K₁ →
      oddCycleCount H₀ + oddCycleCount H₁
        ≤ oddCycleCount K₀ + oddCycleCount K₁

/-- PROVED (transplanted sorry-free from the `r4w4_oddmin` Aristotle return,
wave-4 payload, statement identical).  Fintype argmin over the finite split
space, seeded by the banked split; the only remaining debt is the
`exists_edge_split_pin` it consumes. -/
lemma exists_oddCycleMinimal_split
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4) :
    ∃ (H₀ H₁ : SimpleGraph V)
      (_ : DecidableRel H₀.Adj) (_ : DecidableRel H₁.Adj),
      IsOddCycleMinimalSplit G H₀ H₁ := by
  classical
  set f : SimpleGraph V × SimpleGraph V → ℕ :=
    fun p => oddCycleCount p.1 + oddCycleCount p.2 with hf
  set Q : SimpleGraph V × SimpleGraph V → Prop :=
    fun p => ∃ (_ : DecidableRel p.1.Adj) (_ : DecidableRel p.2.Adj),
      IsEdgeSplit G p.1 p.2 with hQ
  set s : Finset (SimpleGraph V × SimpleGraph V) :=
    Finset.univ.filter Q with hs
  have hle : ∀ v, G.degree v ≤ 4 := fun v => by rcases hdeg v with h | h <;> omega
  obtain ⟨A₀, A₁, iA₀, iA₁, hA⟩ := exists_edge_split_pin G hle
  have hAmem : (A₀, A₁) ∈ s := by
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, iA₀, iA₁, hA⟩
  obtain ⟨M, hMmem, hMmin⟩ := Finset.exists_min_image s f ⟨_, hAmem⟩
  rw [hs, Finset.mem_filter] at hMmem
  obtain ⟨_, iM₀, iM₁, hM⟩ := hMmem
  refine ⟨M.1, M.2, iM₀, iM₁, hM, ?_⟩
  intro K₀ K₁ iK₀ iK₁ hK
  have hKmem : (K₀, K₁) ∈ s := by
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, iK₀, iK₁, hK⟩
  have hmin := hMmin (K₀, K₁) hKmem
  simpa [hf] using hmin


/-! ## FABLE CRUX LANE TOOLBOX (2026-07-12) — STATUS
The OPEN-CRUX `placement_on_oddCycleMinimal_split` below remains `sorry`.
This session banked:
(1) the complete informal reduction + exchange calculus + the refutation of the
    naive strictly-decreasing-swap scheme (see rung4-moonshot/FABLE-CRUX.md);
(2) the min-alternating coloring toolbox A0-A3 below (kernel-proved here):
    ANY defect set (one vertex per odd cycle) with ANY signs is realizable
    (`exists_defectProfile` / `exists_isMinAlternating`), with per-component
    phase control (`DefectProfile.flipOn`) and the zero-odd discharge lemmas.
REMAINING GAP (exact): choose (D, sigma) per half satisfying `DefectSafe` on a
total-odd-minimal split — the exact-cover + XOR feasibility of FABLE-CRUX.md §1,
for which minimality must be exploited via an exchange argument (schemes A/B in
FABLE-CRUX.md §3). First tractable rung: the PROPOSED sub-pin
`placement_on_oddCycleMinimal_split_omega1` stated after the crux. -/

/-! ## A0: cycle supports in max-degree-2 graphs -/

/-- In a max-degree-2 graph, every edge incident to a cycle vertex is an edge
of that cycle. -/
lemma cycle_edge_mem_of_adj
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {x : V} {c : H.Walk x x} (hc : c.IsCycle)
    {u y : V} (hu : u ∈ c.support) (hy : H.Adj u y) :
    s(u, y) ∈ c.edges := by
  have h2 : (c.toSubgraph.neighborSet u).ncard = 2 :=
    hc.ncard_neighborSet_toSubgraph_eq_two hu
  have hsub : c.toSubgraph.neighborSet u ⊆ H.neighborSet u := by
    intro z hz
    exact c.toSubgraph.adj_sub ((c.toSubgraph.mem_neighborSet u z).mp hz)
  have hcardH : (H.neighborSet u).ncard ≤ 2 := by
    have hval : (H.neighborSet u).ncard = H.degree u := by
      rw [Set.ncard_eq_toFinset_card']
      simp [SimpleGraph.neighborFinset_def, SimpleGraph.degree]
    rw [hval]; exact hdeg u
  have heq : c.toSubgraph.neighborSet u = H.neighborSet u :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  have hadj : c.toSubgraph.Adj u y := by
    rw [← c.toSubgraph.mem_neighborSet, heq]
    exact (H.mem_neighborSet u y).mpr hy
  exact Walk.adj_toSubgraph_iff_mem_edges.mp hadj

/-- Cycle supports are closed under adjacency (max degree 2). -/
lemma cycle_support_closed_adj
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {x : V} {c : H.Walk x x} (hc : c.IsCycle)
    {u y : V} (hu : u ∈ c.support) (hy : H.Adj u y) :
    y ∈ c.support :=
  c.snd_mem_support_of_mem_edges (cycle_edge_mem_of_adj H hdeg hc hu hy)

/-- Cycle supports are closed under reachability (max degree 2). -/
lemma cycle_support_closed_reachable
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {x : V} {c : H.Walk x x} (hc : c.IsCycle)
    {u y : V} (hu : u ∈ c.support) (h : H.Reachable u y) :
    y ∈ c.support := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj p ih => exact ih (cycle_support_closed_adj H hdeg hc hu hadj)

/-- Every vertex of a cycle has degree exactly 2 in a max-degree-2 graph. -/
lemma degree_eq_two_of_mem_cycle_support
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {x : V} {c : H.Walk x x} (hc : c.IsCycle)
    {u : V} (hu : u ∈ c.support) :
    H.degree u = 2 := by
  have h2 : (c.toSubgraph.neighborSet u).ncard = 2 :=
    hc.ncard_neighborSet_toSubgraph_eq_two hu
  have hsub : c.toSubgraph.neighborSet u ⊆ H.neighborSet u := by
    intro z hz
    exact c.toSubgraph.adj_sub ((c.toSubgraph.mem_neighborSet u z).mp hz)
  have hval : (H.neighborSet u).ncard = H.degree u := by
    rw [Set.ncard_eq_toFinset_card']
    simp [SimpleGraph.neighborFinset_def, SimpleGraph.degree]
  have hge : 2 ≤ (H.neighborSet u).ncard := by
    rw [← h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have := hdeg u
  omega

/-- Two cycles through a common vertex have the same support (max degree 2). -/
lemma cycle_support_subset_of_mem
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {x x' u : V} {c : H.Walk x x} {c' : H.Walk x' x'}
    (hc : c.IsCycle) (hc' : c'.IsCycle)
    (hu : u ∈ c.support) (hu' : u ∈ c'.support)
    {z : V} (hz : z ∈ c.support) :
    z ∈ c'.support := by
  have hreach : H.Reachable u z := by
    have hz' : z ∈ (c.rotate hu).support := by
      rw [Walk.mem_support_rotate_iff]
      exact hz
    exact ⟨(c.rotate hu).takeUntil z hz'⟩
  exact cycle_support_closed_reachable H hdeg hc' hu' hreach

/-! ## A3: per-component phase flip -/

open scoped Classical in
/-- Flip a Boolean edge coloring on all edges touching a vertex set `A`. -/
noncomputable def flipOn (b : Sym2 V → Bool) (A : Set V) : Sym2 V → Bool :=
  fun e => if ∃ z ∈ e, z ∈ A then !b e else b e

/-- At a vertex inside the flipped set, the flip swaps the per-color loads. -/
lemma halfCount_flipOn_mem
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (A : Set V)
    {v : V} (hvA : v ∈ A) (a : Bool) :
    halfCount H (flipOn b A) v a = halfCount H b v (!a) := by
  classical
  unfold halfCount flipOn
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro e he
  rw [SimpleGraph.mem_incidenceFinset] at he
  have hex : ∃ z ∈ e, z ∈ A := ⟨v, he.2, hvA⟩
  rw [if_pos hex]
  cases a <;> cases h : b e <;> simp [h]

/-- At a vertex outside an adjacency-closed flipped set, loads are unchanged. -/
lemma halfCount_flipOn_notMem
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (A : Set V)
    (hA : ∀ ⦃p q : V⦄, H.Adj p q → p ∈ A → q ∈ A)
    {v : V} (hvA : v ∉ A) (a : Bool) :
    halfCount H (flipOn b A) v a = halfCount H b v a := by
  classical
  unfold halfCount flipOn
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro e he
  rw [SimpleGraph.mem_incidenceFinset] at he
  have heE : e ∈ H.edgeSet := he.1
  have hev : v ∈ e := he.2
  have hnex : ¬ ∃ z ∈ e, z ∈ A := by
    rintro ⟨z, hz, hzA⟩
    apply hvA
    induction e using Sym2.inductionOn with
    | _ p₁ q₁ =>
      rw [SimpleGraph.mem_edgeSet] at heE
      rw [Sym2.mem_iff] at hz hev
      rcases hz with rfl | rfl <;> rcases hev with rfl | rfl
      · exact hzA
      · exact hA heE hzA
      · exact hA heE.symm hzA
      · exact hzA
  rw [if_neg hnex]

/-- Flipping an adjacency-closed set preserves `DefectProfile`, with the signs
flipped on that set (given in hypothesis form to avoid a `Decidable (v ∈ A)`
requirement in the statement). -/
lemma DefectProfile.flipOn
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (D : Finset V) (σ : V → Bool) (A : Set V)
    (hA : ∀ ⦃p q : V⦄, H.Adj p q → p ∈ A → q ∈ A)
    {σ' : V → Bool}
    (hσ'A : ∀ v ∈ D, v ∈ A → σ' v = !(σ v))
    (hσ'n : ∀ v ∈ D, v ∉ A → σ' v = σ v)
    (hprof : DefectProfile H b D σ) :
    DefectProfile H (Rung4Moonshot.flipOn b A) D σ' := by
  classical
  constructor
  · intro v hv
    obtain ⟨hd, h2, h0⟩ := hprof.1 v hv
    by_cases hvA : v ∈ A
    · refine ⟨hd, ?_, ?_⟩
      · rw [halfCount_flipOn_mem H b A hvA, hσ'A v hv hvA]
        simpa using h2
      · rw [halfCount_flipOn_mem H b A hvA, hσ'A v hv hvA]
        simpa using h0
    · refine ⟨hd, ?_, ?_⟩
      · rw [halfCount_flipOn_notMem H b A hA hvA, hσ'n v hv hvA]
        exact h2
      · rw [halfCount_flipOn_notMem H b A hA hvA, hσ'n v hv hvA]
        exact h0
  · intro v hv a
    by_cases hvA : v ∈ A
    · rw [halfCount_flipOn_mem H b A hvA]
      exact hprof.2 v hv _
    · rw [halfCount_flipOn_notMem H b A hA hvA]
      exact hprof.2 v hv _

/-- `DefectProfile` only reads the signs on `D`. -/
lemma DefectProfile.congr_sigma
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (b : Sym2 V → Bool) (D : Finset V) {σ σ' : V → Bool}
    (h : ∀ v ∈ D, σ v = σ' v)
    (hprof : DefectProfile H b D σ) :
    DefectProfile H b D σ' := by
  constructor
  · intro v hv
    obtain ⟨hd, h2, h0⟩ := hprof.1 v hv
    rw [h v hv] at h2 h0
    exact ⟨hd, h2, h0⟩
  · exact hprof.2

/-! ## A1: defect sets exist -/

/-- Every odd-cycle support is nonempty. -/
lemma nonempty_of_mem_oddCycleSupports
    (H : SimpleGraph V) {S : Finset V}
    (hS : S ∈ oddCycleSupports H) : S.Nonempty := by
  classical
  unfold oddCycleSupports at hS
  simp only [Finset.mem_filter] at hS
  obtain ⟨-, x, w, hw, hodd, hsupp⟩ := hS
  exact ⟨x, by rw [← hsupp]; simp⟩

/-- A defect set — one vertex on each odd cycle, nothing else — exists for
every max-degree-2 graph. -/
lemma exists_isOddCycleDefectSet
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2) :
    ∃ D : Finset V, IsOddCycleDefectSet H D := by
  classical
  refine ⟨(oddCycleSupports H).attach.image
    (fun S => (nonempty_of_mem_oddCycleSupports H S.2).choose), ?_, ?_⟩
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨⟨S, hS⟩, -, hpick⟩ := hv
    have hpick' : (nonempty_of_mem_oddCycleSupports H hS).choose = v := hpick
    have hmem : v ∈ S := hpick' ▸ (nonempty_of_mem_oddCycleSupports H hS).choose_spec
    have hS' := hS
    unfold oddCycleSupports at hS'
    simp only [Finset.mem_filter] at hS'
    obtain ⟨-, x, w, hw, hodd, hsupp⟩ := hS'
    refine ⟨x, w, hw, hodd, ?_⟩
    rw [← hsupp] at hmem
    simpa using hmem
  · intro x w hw hodd
    have hS₀ : w.support.toFinset ∈ oddCycleSupports H := by
      unfold oddCycleSupports
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, x, w, hw, hodd, rfl⟩
    have hv₀S : (nonempty_of_mem_oddCycleSupports H hS₀).choose ∈ w.support.toFinset :=
      (nonempty_of_mem_oddCycleSupports H hS₀).choose_spec
    refine ⟨(nonempty_of_mem_oddCycleSupports H hS₀).choose,
      ⟨by simpa using hv₀S, ?_⟩, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨⟨_, hS₀⟩, Finset.mem_attach _ _, rfl⟩
    · rintro v' ⟨hv'w, hv'D⟩
      rw [Finset.mem_image] at hv'D
      obtain ⟨⟨S', hS'⟩, -, hpick⟩ := hv'D
      have hpick' : (nonempty_of_mem_oddCycleSupports H hS').choose = v' := hpick
      have hv'S' : v' ∈ S' := hpick' ▸ (nonempty_of_mem_oddCycleSupports H hS').choose_spec
      have hS'w : S' = w.support.toFinset := by
        have hS'c := hS'
        unfold oddCycleSupports at hS'c
        simp only [Finset.mem_filter] at hS'c
        obtain ⟨-, x', w', hw', hodd', hsupp'⟩ := hS'c
        have hv'w' : v' ∈ w'.support := by
          rw [← hsupp'] at hv'S'
          simpa using hv'S'
        ext t
        simp only [← hsupp', List.mem_toFinset]
        constructor
        · intro ht
          exact cycle_support_subset_of_mem H hdeg hw' hw hv'w' hv'w ht
        · intro ht
          exact cycle_support_subset_of_mem H hdeg hw hw' hv'w hv'w' ht
      subst hS'w
      rw [← hpick']

/-! ## Interior-properness path alternation
(variant of `path_edge_color` whose properness hypothesis is required only at
the interior vertices of the path — the endpoints may be defective). -/

lemma path_edge_color_interior {N : SimpleGraph V} [DecidableRel N.Adj]
    {col : Sym2 V → Bool}
    {a b : V} (p : N.Walk a b) (hp : p.IsPath)
    (hcol : ∀ j, 0 < j → j < p.length → ∀ bb : Bool,
      #{f ∈ N.incidenceFinset (p.getVert j) | col f = bb} ≤ 1) :
    ∀ i, i + 1 ≤ p.length →
      col s(p.getVert i, p.getVert (i + 1)) =
        (if Even i then col s(p.getVert 0, p.getVert 1)
         else !(col s(p.getVert 0, p.getVert 1))) := by
  intro i hi
  induction' i with i ih
  · simp +decide
  · have h_distinct : s(p.getVert i, p.getVert (i + 1)) ≠ s(p.getVert (i + 1), p.getVert (i + 2)) := by
      intro h; have := hp.getVert_injOn; simp_all +decide [ Set.InjOn ] ;
      grind +qlia
    have h_adj : N.Adj (p.getVert i) (p.getVert (i + 1)) ∧ N.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
      exact ⟨ p.adj_getVert_succ ( by linarith ), p.adj_getVert_succ ( by linarith ) ⟩
    have h_diff : col s(p.getVert i, p.getVert (i + 1)) ≠ col s(p.getVert (i + 1), p.getVert (i + 2)) := by
      intro h_eq
      have h_card : 2 ≤ Finset.card (Finset.filter (fun f => col f = col s(p.getVert i, p.getVert (i + 1))) (N.incidenceFinset (p.getVert (i + 1)))) := by
        refine' Finset.one_lt_card.mpr ⟨ s(p.getVert i, p.getVert (i + 1)), _, s(p.getVert (i + 1), p.getVert (i + 2)), _, _ ⟩ <;> simp_all +decide [ SimpleGraph.incidenceSet ]
      exact not_lt_of_ge h_card
        (lt_of_le_of_lt (hcol (i + 1) (by omega) (by omega) _) (by decide))
    rw [ ih ( by linarith ) ] at h_diff; split_ifs at * <;> simp_all +decide [ Nat.even_add_one ] ;
    cases h : col s(a, p.getVert 1) <;> cases h' : col s(p.getVert (i + 1), p.getVert (i + 2)) <;> simp_all +decide only

/-- End-edge colors of an interior-proper path of even length ≥ 2 are opposite. -/
lemma path_end_colors_of_even
    {N : SimpleGraph V} [DecidableRel N.Adj]
    {col : Sym2 V → Bool}
    {a b : V} (p : N.Walk a b) (hp : p.IsPath)
    (hlen : 2 ≤ p.length) (heven : Even p.length)
    (hcol : ∀ j, 0 < j → j < p.length → ∀ bb : Bool,
      #{f ∈ N.incidenceFinset (p.getVert j) | col f = bb} ≤ 1) :
    col s(p.penultimate, b) = !(col s(a, p.snd)) := by
  have hkey := path_edge_color_interior p hp hcol (p.length - 1) (by omega)
  have hodd : ¬ Even (p.length - 1) := by
    rcases heven with ⟨k, hk⟩
    intro hcon
    rcases hcon with ⟨m, hm⟩
    omega
  rw [if_neg hodd] at hkey
  have h1 : p.length - 1 + 1 = p.length := by omega
  rw [h1] at hkey
  have h2 : p.getVert p.length = b := p.getVert_length
  have h0 : p.getVert 0 = a := p.getVert_zero
  rw [h2, h0] at hkey
  exact hkey

/-! ## A2: any defect set with any signs is realizable -/

set_option maxHeartbeats 1600000 in
/-- Workhorse: every defect set (one vertex per odd cycle) with arbitrary signs
is realized by a Boolean coloring of the half.  Strong induction on `|D|`;
the odd length of each cycle is exactly what makes the re-inserted defect edge
consistent at its far endpoint. -/
lemma exists_defectProfile_aux :
    ∀ (n : ℕ) (M : SimpleGraph V) [DecidableRel M.Adj] (D : Finset V) (σ : V → Bool),
      D.card = n → (∀ v, M.degree v ≤ 2) → IsOddCycleDefectSet M D →
      ∃ b : Sym2 V → Bool, DefectProfile M b D σ := by
  intros n M _ D σ hcard hdeg hD
  induction' n using Nat.strong_induction_on with n ih generalizing M D σ
  classical
  by_cases hD0 : D = ∅
  · -- no defects: the graph has no odd cycle; alternate properly
    subst hD0
    have hno : ∀ x (w : M.Walk x x), w.IsCycle → ¬ Odd w.length := by
      intro x w hw hodd
      obtain ⟨z, ⟨-, hz⟩, -⟩ := hD.2 x w hw hodd
      simp at hz
    obtain ⟨col, hcol⟩ := exists_proper_two_edge_coloring M hdeg hno
    refine ⟨col, ?_, ?_⟩
    · intro v hv; simp at hv
    · intro v _ a; exact hcol v a
  · -- pick a defect v and its odd cycle, rotated to start at v
    obtain ⟨v, hv⟩ := Finset.nonempty_of_ne_empty hD0
    obtain ⟨x₀, c₀, hc₀, hodd₀, hvc₀⟩ := hD.1 v hv
    set c : M.Walk v v := c₀.rotate hvc₀ with hcdef
    have hc : c.IsCycle := hc₀.rotate hvc₀
    have hclen : c.length = c₀.length := by
      rw [hcdef]
      have := (c₀.rotate_darts hvc₀).perm.length_eq
      simpa [SimpleGraph.Walk.length_darts] using this
    have hcodd : Odd c.length := by rw [hclen]; exact hodd₀
    have hc3 : 3 ≤ c.length := hc.three_le_length
    have hcnil : ¬ c.Nil := by rw [Walk.nil_iff_length_eq]; omega
    obtain ⟨y, hadj, q, hq_eq⟩ := Walk.not_nil_iff.mp hcnil
    have hq_cyc : q.IsPath ∧ s(v, y) ∉ q.edges := by
      have h := hc
      rw [hq_eq, Walk.cons_isCycle_iff] at h
      exact h
    obtain ⟨hq_path, he₁q⟩ := hq_cyc
    have hqlen : q.length + 1 = c.length := by rw [hq_eq]; simp
    have hqlen2 : 2 ≤ q.length := by omega
    have hqeven : Even q.length := by
      rcases hcodd with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    have hqnil : ¬ q.Nil := by rw [Walk.nil_iff_length_eq]; omega
    -- the two edges of M at v
    set e₁ : Sym2 V := s(v, y) with he₁def
    set z : V := q.penultimate with hzdef
    set e₂ : Sym2 V := s(z, v) with he₂def
    have he₂q : e₂ ∈ q.edges := by
      rw [he₂def, hzdef]
      exact q.mk_penultimate_end_mem_edges hqnil
    have hzadj : M.Adj z v := by
      have h := q.edges_subset_edgeSet he₂q
      rwa [SimpleGraph.mem_edgeSet] at h
    have he₁e₂ : e₁ ≠ e₂ := by
      intro h; rw [h] at he₁q; exact he₁q he₂q
    have hyz : y ≠ z := by
      intro h
      apply he₁e₂
      rw [he₁def, he₂def, ← h, Sym2.eq_swap]
    have hdegv : M.degree v = 2 := by
      have hsub : ({y, z} : Finset V) ⊆ M.neighborFinset v := by
        intro t ht
        rw [Finset.mem_insert, Finset.mem_singleton] at ht
        rw [SimpleGraph.mem_neighborFinset]
        rcases ht with rfl | rfl
        · exact hadj
        · exact hzadj.symm
      have h2 : 2 ≤ M.degree v := by
        have hle := Finset.card_le_card hsub
        rw [Finset.card_pair hyz] at hle
        exact hle
      have := hdeg v
      omega
    have hvsupp : v ∈ c.support := c.start_mem_support
    have hysupp : y ∈ c.support := by
      rw [hq_eq, Walk.support_cons]
      exact List.mem_cons_of_mem _ q.start_mem_support
    -- y is not a defect
    have hyD : y ∉ D := by
      intro hyD
      obtain ⟨w', -, huniq⟩ := hD.2 v c hc hcodd
      have h1 := huniq v ⟨hvsupp, hv⟩
      have h2 := huniq y ⟨hysupp, hyD⟩
      exact hadj.ne' (h2.trans h1.symm)
    -- incidence structure at v
    have hincv : M.incidenceFinset v = {e₁, e₂} := by
      have hsub : ({e₁, e₂} : Finset (Sym2 V)) ⊆ M.incidenceFinset v := by
        intro t ht
        rw [Finset.mem_insert, Finset.mem_singleton] at ht
        rw [SimpleGraph.mem_incidenceFinset]
        rcases ht with rfl | rfl
        · exact ⟨(SimpleGraph.mem_edgeSet M).mpr hadj, Sym2.mem_mk_left _ _⟩
        · exact ⟨(SimpleGraph.mem_edgeSet M).mpr hzadj, Sym2.mem_mk_right _ _⟩
      have hcard2 : ({e₁, e₂} : Finset (Sym2 V)).card = 2 := Finset.card_pair he₁e₂
      have hcardinc : (M.incidenceFinset v).card = 2 := by
        rw [SimpleGraph.card_incidenceFinset_eq_degree]; exact hdegv
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    -- delete e₁; the smaller instance
    set M' : SimpleGraph V := M.deleteEdges {e₁} with hM'def
    have hM'le : M' ≤ M := SimpleGraph.deleteEdges_le _
    have hdeg' : ∀ w, M'.degree w ≤ 2 :=
      fun w => le_trans (SimpleGraph.degree_le_of_le hM'le) (hdeg w)
    have he₁M : e₁ ∉ M'.edgeSet := by
      rw [hM'def, SimpleGraph.edgeSet_deleteEdges]
      simp
    set D' : Finset V := D.erase v with hD'def
    have hD'card : D'.card < n := by
      rw [hD'def, ← hcard]
      exact Finset.card_erase_lt_of_mem hv
    have hD' : IsOddCycleDefectSet M' D' := by
      constructor
      · intro v' hv'
        have hv'D : v' ∈ D := Finset.mem_of_mem_erase hv'
        have hv'v : v' ≠ v := Finset.ne_of_mem_erase hv'
        obtain ⟨x₁, w₁, hw₁, hodd₁, hv'w₁⟩ := hD.1 v' hv'D
        have he₁w₁ : ∀ e ∈ w₁.edges, e ∈ M'.edgeSet := by
          intro e he
          have heM : e ∈ M.edgeSet := w₁.edges_subset_edgeSet he
          have hne : e ≠ e₁ := by
            rintro rfl
            have hvw₁ : v ∈ w₁.support := by
              rw [he₁def] at he
              exact w₁.fst_mem_support_of_mem_edges he
            obtain ⟨w', -, huniq⟩ := hD.2 x₁ w₁ hw₁ hodd₁
            have h1 := huniq v ⟨hvw₁, hv⟩
            have h2 := huniq v' ⟨hv'w₁, hv'D⟩
            exact hv'v (h2.trans h1.symm)
          rw [hM'def, SimpleGraph.edgeSet_deleteEdges]
          exact ⟨heM, by simpa using hne⟩
        refine ⟨x₁, w₁.transfer M' he₁w₁, hw₁.transfer he₁w₁, ?_, ?_⟩
        · rw [Walk.length_transfer]; exact hodd₁
        · rw [Walk.support_transfer]; exact hv'w₁
      · intro x₁ w₁ hw₁ hodd₁
        have hsub : ∀ e ∈ w₁.edges, e ∈ M.edgeSet := by
          intro e he
          exact SimpleGraph.edgeSet_mono hM'le (w₁.edges_subset_edgeSet he)
        have hw₁Mc : (w₁.transfer M hsub).IsCycle := hw₁.transfer hsub
        have hw₁Modd : Odd (w₁.transfer M hsub).length := by
          rw [Walk.length_transfer]; exact hodd₁
        obtain ⟨z₀, ⟨hz₀s, hz₀D⟩, huniq⟩ := hD.2 x₁ (w₁.transfer M hsub) hw₁Mc hw₁Modd
        have hz₀v : z₀ ≠ v := by
          intro heq
          have hz₀s' : v ∈ (w₁.transfer M hsub).support := heq ▸ hz₀s
          have hedge : s(v, y) ∈ (w₁.transfer M hsub).edges :=
            cycle_edge_mem_of_adj M hdeg hw₁Mc hz₀s' hadj
          rw [Walk.edges_transfer] at hedge
          have hmem : e₁ ∈ M'.edgeSet := by
            rw [he₁def]
            exact w₁.edges_subset_edgeSet hedge
          exact he₁M hmem
        refine ⟨z₀, ⟨?_, ?_⟩, ?_⟩
        · have h := hz₀s
          rwa [Walk.support_transfer] at h
        · rw [hD'def]; exact Finset.mem_erase.mpr ⟨hz₀v, hz₀D⟩
        · rintro t ⟨hts, htD⟩
          refine huniq t ⟨?_, Finset.mem_of_mem_erase htD⟩
          rwa [Walk.support_transfer]
    -- induction
    obtain ⟨b', hb'⟩ := ih D'.card hD'card M' D' σ rfl hdeg' hD'
    -- M'-incidence at v is the single edge e₂
    have hdegv' : M'.degree v = 1 := by
      have h : M'.degree v = M.degree v - (if v = v ∨ v = y then 1 else 0) :=
        degree_deleteEdges_single M v y hadj v
      rw [h, hdegv]
      simp
    have hincv' : M'.incidenceFinset v = {e₂} := by
      have h1 : M'.incidenceFinset v = (M.incidenceFinset v).erase e₁ :=
        incidenceFinset_deleteEdges_single M (s(v, y)) v
      rw [h1, hincv, Finset.erase_insert (by simpa using he₁e₂)]
    -- fix the phase at v: ensure b'' e₂ = σ v
    have hkey : ∃ b'' : Sym2 V → Bool,
        DefectProfile M' b'' D' σ ∧ b'' e₂ = σ v := by
      by_cases hphase : b' e₂ = σ v
      · exact ⟨b', hb', hphase⟩
      · set A : Set V := {u | M'.Reachable v u} with hAdef
        have hA : ∀ ⦃p₁ q₁ : V⦄, M'.Adj p₁ q₁ → p₁ ∈ A → q₁ ∈ A := by
          intro p₁ q₁ hpq hp₁
          exact Reachable.trans hp₁ hpq.reachable
        have hDA : ∀ t ∈ D', t ∉ A := by
          intro t ht htA
          have htv : t ≠ v := Finset.ne_of_mem_erase ht
          have htD : t ∈ D := Finset.mem_of_mem_erase ht
          have hreachM : M.Reachable v t := Reachable.mono hM'le htA
          have htc : t ∈ c.support :=
            cycle_support_closed_reachable M hdeg hc hvsupp hreachM
          obtain ⟨w', -, huniq⟩ := hD.2 v c hc hcodd
          have h1 := huniq v ⟨hvsupp, hv⟩
          have h2 := huniq t ⟨htc, htD⟩
          exact htv (h2.trans h1.symm)
        have hprof' : DefectProfile M' (Rung4Moonshot.flipOn b' A) D' σ :=
          DefectProfile.flipOn M' b' D' σ A hA
            (fun t ht htA => absurd htA (hDA t ht))
            (fun _ _ _ => rfl) hb'
        refine ⟨Rung4Moonshot.flipOn b' A, hprof', ?_⟩
        have hvA : v ∈ A := Reachable.refl v
        have hex : ∃ t ∈ e₂, t ∈ A := by
          refine ⟨v, ?_, hvA⟩
          rw [he₂def]
          exact Sym2.mem_mk_right _ _
        simp only [Rung4Moonshot.flipOn]
        rw [if_pos hex]
        cases h : b' e₂ <;> cases h' : σ v <;> simp_all
    obtain ⟨b'', hb'', hb''e₂⟩ := hkey
    -- final coloring
    set b : Sym2 V → Bool := fun e => if e = e₁ then σ v else b'' e with hbdef
    have hbe₁ : b e₁ = σ v := by rw [hbdef]; simp
    have hbe₂ : b e₂ = σ v := by
      rw [hbdef]
      simp only [if_neg (Ne.symm he₁e₂)]
      exact hb''e₂
    -- transfer of halfCounts away from v, y
    have htransfer : ∀ u, u ≠ v → u ≠ y → ∀ a : Bool,
        halfCount M b u a = halfCount M' b'' u a := by
      intro u huv huy a
      unfold halfCount
      have hinc : M'.incidenceFinset u = M.incidenceFinset u := by
        have h1 : M'.incidenceFinset u = (M.incidenceFinset u).erase e₁ :=
          incidenceFinset_deleteEdges_single M (s(v, y)) u
        rw [h1]
        apply Finset.erase_eq_of_notMem
        intro hmem
        rw [SimpleGraph.mem_incidenceFinset] at hmem
        have hue : u ∈ e₁ := hmem.2
        rw [he₁def, Sym2.mem_iff] at hue
        rcases hue with rfl | rfl
        · exact huv rfl
        · exact huy rfl
      rw [← hinc]
      refine congrArg Finset.card (Finset.filter_congr ?_)
      intro e he
      have hee₁ : e ≠ e₁ := by
        rintro rfl
        rw [SimpleGraph.mem_incidenceFinset] at he
        exact he₁M he.1
      rw [hbdef]
      simp [hee₁]
    -- halfCount at v
    have hhv : ∀ a : Bool, halfCount M b v a = if σ v = a then 2 else 0 := by
      intro a
      unfold halfCount
      rw [hincv]
      simp only [Finset.filter_insert, Finset.filter_singleton, hbe₁, hbe₂]
      by_cases h : σ v = a
      · simp [h, Finset.card_pair he₁e₂]
      · simp [h]
    -- q transfers to M'
    have hqM' : ∀ e ∈ q.edges, e ∈ M'.edgeSet := by
      intro e he
      have heM : e ∈ M.edgeSet := q.edges_subset_edgeSet he
      have hne : e ≠ e₁ := by
        rintro rfl
        rw [he₁def] at he
        exact he₁q he
      rw [hM'def, SimpleGraph.edgeSet_deleteEdges]
      exact ⟨heM, by simpa using hne⟩
    set q' := q.transfer M' hqM' with hq'def
    have hq'path : q'.IsPath := hq_path.transfer hqM'
    have hq'len : q'.length = q.length := Walk.length_transfer _ _
    have hq'nil : ¬ q'.Nil := by
      rw [Walk.nil_iff_length_eq, hq'len]
      omega
    -- interior properness of b'' along q'
    have hinterior : ∀ j, 0 < j → j < q'.length → ∀ bb : Bool,
        #{f ∈ M'.incidenceFinset (q'.getVert j) | b'' f = bb} ≤ 1 := by
      intro j hj0 hjlen bb
      have htD' : q'.getVert j ∉ D' := by
        intro htD'
        have htD : q'.getVert j ∈ D := Finset.mem_of_mem_erase htD'
        have htv : q'.getVert j ≠ v := Finset.ne_of_mem_erase htD'
        have htq : q'.getVert j ∈ q'.support := Walk.getVert_mem_support _ _
        have htq2 : q'.getVert j ∈ q.support := by
          rw [hq'def, Walk.support_transfer] at htq
          exact htq
        have htc : q'.getVert j ∈ c.support := by
          rw [hq_eq, Walk.support_cons]
          exact List.mem_cons_of_mem _ htq2
        obtain ⟨w', -, huniq⟩ := hD.2 v c hc hcodd
        have h1 := huniq v ⟨hvsupp, hv⟩
        have h2 := huniq (q'.getVert j) ⟨htc, htD⟩
        exact htv (h2.trans h1.symm)
      have h := hb''.2 (q'.getVert j) htD' bb
      unfold halfCount at h
      exact h
    -- last edge of q' is e₂
    have hlastmem : s(q'.penultimate, v) ∈ q'.edges := q'.mk_penultimate_end_mem_edges hq'nil
    have hlast_eq : s(q'.penultimate, v) = e₂ := by
      have hmem : s(q'.penultimate, v) ∈ M'.incidenceFinset v := by
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨q'.edges_subset_edgeSet hlastmem, Sym2.mem_mk_right _ _⟩
      rw [hincv'] at hmem
      simpa using hmem
    -- alternation along q'
    have halt := path_end_colors_of_even q' hq'path
      (by omega) (by rw [hq'len]; exact hqeven) hinterior
    -- first edge of q' is the second M-edge at y
    have hfirstmem : s(y, q'.snd) ∈ q'.edges := q'.mk_start_snd_mem_edges hq'nil
    set f : Sym2 V := s(y, q'.snd) with hfdef
    have hf_alt : b'' f = !(b'' e₂) := by
      have h1 := halt
      rw [hlast_eq] at h1
      cases h : b'' f <;> simp_all
    have hf_color : b'' f = !(σ v) := by
      rw [hf_alt, hb''e₂]
    -- M-incidence at y
    have hdegy : M.degree y = 2 :=
      degree_eq_two_of_mem_cycle_support M hdeg hc hysupp
    have hdegy' : M'.degree y = 1 := by
      have h : M'.degree y = M.degree y - (if y = v ∨ y = y then 1 else 0) :=
        degree_deleteEdges_single M v y hadj y
      rw [h, hdegy]
      simp
    have hincy' : M'.incidenceFinset y = {f} := by
      have hcard1 : (M'.incidenceFinset y).card = 1 := by
        rw [SimpleGraph.card_incidenceFinset_eq_degree]
        exact hdegy'
      have hfmem : f ∈ M'.incidenceFinset y := by
        rw [SimpleGraph.mem_incidenceFinset]
        refine ⟨q'.edges_subset_edgeSet hfirstmem, ?_⟩
        rw [hfdef]
        exact Sym2.mem_mk_left _ _
      obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hcard1
      have hfg : f = g := by
        rw [hg] at hfmem
        simpa using hfmem
      rw [hg, hfg]
    have hfe₁ : f ≠ e₁ := by
      intro h
      have hmem : f ∈ M'.incidenceFinset y := by rw [hincy']; simp
      rw [SimpleGraph.mem_incidenceFinset] at hmem
      rw [h] at hmem
      exact he₁M hmem.1
    have hincy : M.incidenceFinset y = {e₁, f} := by
      have h1 : M'.incidenceFinset y = (M.incidenceFinset y).erase e₁ :=
        incidenceFinset_deleteEdges_single M (s(v, y)) y
      have h2 : (M.incidenceFinset y).erase e₁ = {f} := by
        rw [← h1]
        exact hincy'
      have he₁inc : e₁ ∈ M.incidenceFinset y := by
        rw [SimpleGraph.mem_incidenceFinset]
        refine ⟨(SimpleGraph.mem_edgeSet M).mpr hadj, ?_⟩
        rw [he₁def]
        exact Sym2.mem_mk_right _ _
      rw [← Finset.insert_erase he₁inc, h2]
    have hbf : b f = !(σ v) := by
      rw [hbdef]
      simp only [if_neg hfe₁]
      exact hf_color
    have hhy : ∀ a : Bool, halfCount M b y a ≤ 1 := by
      intro a
      unfold halfCount
      rw [hincy]
      simp only [Finset.filter_insert, Finset.filter_singleton, hbe₁, hbf]
      by_cases h : σ v = a
      · have h' : ¬((!(σ v)) = a) := by rw [← h]; simp
        simp [h, h']
      · by_cases h' : (!(σ v)) = a <;> simp [h, h']
    -- assemble the profile
    refine ⟨b, ?_, ?_⟩
    · intro u hu
      by_cases huv : u = v
      · subst huv
        refine ⟨hdegv, ?_, ?_⟩
        · rw [hhv]; simp
        · rw [hhv]; cases hσ : σ u <;> simp
      · have huy : u ≠ y := by
          rintro rfl
          exact hyD hu
        have huD' : u ∈ D' := by
          rw [hD'def]
          exact Finset.mem_erase.mpr ⟨huv, hu⟩
        obtain ⟨hd', h2', h0'⟩ := hb''.1 u huD'
        have hdegu : M.degree u = M'.degree u := by
          have h : M'.degree u = M.degree u - (if u = v ∨ u = y then 1 else 0) :=
            degree_deleteEdges_single M v y hadj u
          have hcond : ¬(u = v ∨ u = y) := by
            rintro (rfl | rfl)
            · exact huv rfl
            · exact huy rfl
          rw [h]
          simp [hcond]
        refine ⟨by rw [hdegu]; exact hd', ?_, ?_⟩
        · rw [htransfer u huv huy]; exact h2'
        · rw [htransfer u huv huy]; exact h0'
    · intro u huD a
      by_cases huv : u = v
      · subst huv; exact absurd hv huD
      · by_cases huy : u = y
        · subst huy; exact hhy a
        · rw [htransfer u huv huy]
          have huD' : u ∉ D' := by
            intro h
            exact huD (Finset.mem_of_mem_erase h)
          exact hb''.2 u huD' a

/-! ## Zero-odd interface (discharges the trivial half of ω-stratified cases) -/

/-- A half with `oddCycleCount = 0` has no odd cycle. -/
lemma noOddCycle_of_oddCycleCount_eq_zero
    (H : SimpleGraph V) (h : oddCycleCount H = 0) :
    NoOddCycle H := by
  classical
  intro x w hw hodd
  have hmem : w.support.toFinset ∈ oddCycleSupports H := by
    unfold oddCycleSupports
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, x, w, hw, hodd, rfl⟩
  unfold oddCycleCount at h
  rw [Finset.card_eq_zero] at h
  rw [h] at hmem
  simp at hmem

/-- An odd-cycle-free half accepts the empty defect set. -/
lemma isOddCycleDefectSet_empty
    (H : SimpleGraph V) (hno : NoOddCycle H) :
    IsOddCycleDefectSet H (∅ : Finset V) := by
  constructor
  · intro v hv; simp at hv
  · intro x w hw hodd
    exact absurd hodd (hno x w hw)

/-- `DefectSafe` is vacuous for the empty defect set. -/
lemma defectSafe_empty
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (b : Sym2 V → Bool) (σ : V → Bool) :
    DefectSafe G H K b (∅ : Finset V) σ := by
  intro u v huv
  constructor
  · intro _
    constructor
    · intro hu; simp at hu
    · intro hv; simp at hv
  · intro _ hu; simp at hu

/-- ANY defect set with ANY signs is realizable (packaged form). -/
lemma exists_defectProfile
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    (D : Finset V) (σ : V → Bool) (hD : IsOddCycleDefectSet H D) :
    ∃ b : Sym2 V → Bool, DefectProfile H b D σ :=
  exists_defectProfile_aux D.card H D σ rfl hdeg hD

/-- ANY defect set with ANY signs extends to a min-alternating coloring. -/
lemma exists_isMinAlternating
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    (D : Finset V) (σ : V → Bool) (hD : IsOddCycleDefectSet H D) :
    ∃ b : Sym2 V → Bool, IsMinAlternating H b D σ := by
  obtain ⟨b, hb⟩ := exists_defectProfile H hdeg D σ hD
  exact ⟨b, hD, hb⟩

/-- Min-alternating colorings exist for every max-degree-2 graph. -/
lemma exists_minAlternating_data
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2) :
    ∃ (D : Finset V) (σ : V → Bool) (b : Sym2 V → Bool),
      IsMinAlternating H b D σ := by
  obtain ⟨D, hD⟩ := exists_isOddCycleDefectSet H hdeg
  obtain ⟨b, hb⟩ := exists_isMinAlternating H hdeg D (fun _ => true) hD
  exact ⟨D, fun _ => true, b, hb⟩

/-! ## Omega-stratification + singleton-safety interface (transplanted sorry-free
from the `r4w8_crux_parity` Aristotle return, built on the toolboxed candidate;
all references are to mainline declarations — token-checked). -/

/-- PROVED helper rung.  Any odd-cycle-free half discharges its per-half
obligation with the *empty* defect set, against *any* cross half `K`.  This is
the fully-general engine behind every zero-odd discharge: `D = ∅` is trivially a
min-alternating defect set (no odd cycle to host), and `DefectSafe` is vacuous on
an empty defect set.  Reusable for either half of any split. -/
lemma placement_half_of_noOddCycle
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg2 : ∀ v, H.degree v ≤ 2)
    (hno : NoOddCycle H) :
    ∃ (D : Finset V) (σ : V → Bool) (b : Sym2 V → Bool),
      IsMinAlternating H b D σ ∧ DefectSafe G H K b D σ := by
  obtain ⟨b, hb⟩ :=
    exists_isMinAlternating H hdeg2 (∅ : Finset V) (fun _ => true)
      (isOddCycleDefectSet_empty H hno)
  exact ⟨∅, (fun _ => true), b, hb, defectSafe_empty G H K b (fun _ => true)⟩

/-- PROVED helper rung.  When BOTH halves of the split are odd-cycle-free
(`oddCycleCount = 0` on each), the crux conclusion holds outright: each half is
discharged by `placement_half_of_noOddCycle` with the empty defect set.  This is
the class-I-like base case of the ω-stratification (no `hII`/minimality needed). -/
lemma placement_on_oddCycleMinimal_split_both_zero
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hsplit : IsEdgeSplit G H₀ H₁)
    (hz0 : oddCycleCount H₀ = 0) (hz1 : oddCycleCount H₁ = 0) :
    ∃ (D₀ D₁ : Finset V) (σ₀ σ₁ : V → Bool)
      (b₀ b₁ : Sym2 V → Bool),
      IsMinAlternating H₀ b₀ D₀ σ₀ ∧
      DefectSafe G H₀ H₁ b₀ D₀ σ₀ ∧
      IsMinAlternating H₁ b₁ D₁ σ₁ ∧
      DefectSafe G H₁ H₀ b₁ D₁ σ₁ := by
  obtain ⟨-, -, -, -, hdeg0, hdeg1, -⟩ := hsplit
  obtain ⟨D₀, σ₀, b₀, halt₀, hsafe₀⟩ :=
    placement_half_of_noOddCycle G H₀ H₁ hdeg0
      (noOddCycle_of_oddCycleCount_eq_zero H₀ hz0)
  obtain ⟨D₁, σ₁, b₁, halt₁, hsafe₁⟩ :=
    placement_half_of_noOddCycle G H₁ H₀ hdeg1
      (noOddCycle_of_oddCycleCount_eq_zero H₁ hz1)
  exact ⟨D₀, D₁, σ₀, σ₁, b₀, b₁, halt₀, hsafe₀, halt₁, hsafe₁⟩

/-- PROVED helper rung.  Whenever *one* half of the split is odd-cycle-free, its
obligation is dischargeable with the empty defect set, so the crux reduces to
supplying `(D, σ, b)` for the *other* half alone.  This is the ω-stratification
reduction used at every level: it strips the trivial half.  (Stated for the case
the second half `H₁` is odd-cycle-free; apply after `IsEdgeSplit.swap` for the
symmetric case.) -/
lemma placement_reduce_to_single_half
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hsplit : IsEdgeSplit G H₀ H₁)
    (hz1 : oddCycleCount H₁ = 0)
    (hhalf0 : ∃ (D₀ : Finset V) (σ₀ : V → Bool) (b₀ : Sym2 V → Bool),
      IsMinAlternating H₀ b₀ D₀ σ₀ ∧ DefectSafe G H₀ H₁ b₀ D₀ σ₀) :
    ∃ (D₀ D₁ : Finset V) (σ₀ σ₁ : V → Bool)
      (b₀ b₁ : Sym2 V → Bool),
      IsMinAlternating H₀ b₀ D₀ σ₀ ∧
      DefectSafe G H₀ H₁ b₀ D₀ σ₀ ∧
      IsMinAlternating H₁ b₁ D₁ σ₁ ∧
      DefectSafe G H₁ H₀ b₁ D₁ σ₁ := by
  obtain ⟨-, -, -, -, -, hdeg1, -⟩ := hsplit
  obtain ⟨D₀, σ₀, b₀, halt₀, hsafe₀⟩ := hhalf0
  obtain ⟨D₁, σ₁, b₁, halt₁, hsafe₁⟩ :=
    placement_half_of_noOddCycle G H₁ H₀ hdeg1
      (noOddCycle_of_oddCycleCount_eq_zero H₁ hz1)
  exact ⟨D₀, D₁, σ₀, σ₁, b₀, b₁, halt₀, hsafe₀, halt₁, hsafe₁⟩

/-- PROVED helper rung.  `cap` is symmetric in its two endpoints. -/
lemma cap_comm (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    cap G u v = cap G v u := by
  unfold cap; rw [add_comm]

/-- PROVED helper rung.  For a *single-defect* placement `D = {d}` (sign taken
from `σ d`), `DefectSafe` collapses to a purely local condition at the cross
neighbours of `d`: every cap-two `K`-neighbour `v` of `d` must be an `H`-leaf
(`H.degree v = 1`) carrying zero `σ d`-load.  All other `DefectSafe` clauses are
vacuous because a singleton defect set cannot contain both endpoints of an edge.
This is the exact interface reducing the single-odd-cycle crux to placing one
defect so that this local condition holds. -/
lemma defectSafe_singleton
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (b : Sym2 V → Bool) (d : V) (σ : V → Bool)
    (hcond : ∀ v, K.Adj d v → cap G d v = 2 →
        H.degree v = 1 ∧ halfCount H b v (σ d) = 0) :
    DefectSafe G H K b {d} σ := by
  intro u v huv
  refine ⟨?_, ?_⟩
  · intro hcap2
    refine ⟨?_, ?_⟩
    · intro hu
      rw [Finset.mem_singleton] at hu
      subst hu
      exact Or.inr (hcond v huv hcap2)
    · intro hv
      rw [Finset.mem_singleton] at hv
      subst hv
      have hcap2' : cap G v u = 2 := by rw [cap_comm]; exact hcap2
      exact Or.inr (hcond u huv.symm hcap2')
  · intro _ hu hv
    rw [Finset.mem_singleton] at hu hv
    exact absurd (hu.trans hv.symm) huv.ne


/-! ## Max-degree-2 structure theory (transplanted sorry-free from the
`r4w7_crux_smallfirst` Aristotle return; round 10).  Cycle-component structure +
one-edge-deletion bookkeeping — descent-pin (exchange argument) infrastructure. -/

/-! ## Structural infrastructure toward the placement crux
(kernel-proved in this file).  These lemmas establish the "max-degree-≤2 graph is
a disjoint union of paths and cycles" structure theory that underlies the defect
placement: cycle vertices have degree exactly two, a cycle occupies its whole
2-regular component, and deleting one edge of a cycle turns that component
acyclic.  `min_alt_no_odd` packages the odd-cycle-free case as a defect-free
`IsMinAlternating`.  They are the coloring-side foundation on which any proof of
`placement_on_oddCycleMinimal_split` builds. -/

/-- Packaging: a max-degree-≤2 graph with no odd cycle is min-alternating with an
empty defect set. -/
lemma min_alt_no_odd (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v ≤ 2)
    (hno : ∀ x (w : H.Walk x x), w.IsCycle → ¬ Odd w.length) :
    ∃ b : Sym2 V → Bool, IsMinAlternating H b ∅ (fun _ => true) := by
  obtain ⟨ b, hb ⟩ := exists_proper_two_edge_coloring H hdeg hno;
  refine' ⟨ b, _, _ ⟩ <;> simp_all +decide [ IsOddCycleDefectSet, DefectProfile ];
  exact hb

/-
Every vertex on a cycle has degree at least two.
-/
lemma cycle_support_deg_ge_two (H : SimpleGraph V) [DecidableRel H.Adj]
    {x : V} (w : H.Walk x x) (hw : w.IsCycle) :
    ∀ v ∈ w.support, 2 ≤ H.degree v := by
  intro v hv
  have h_cycle : ∃ u₁ u₂ : V, u₁ ≠ u₂ ∧ H.Adj v u₁ ∧ H.Adj v u₂ := by
    obtain ⟨w', hw'⟩ : ∃ w' : H.Walk v v, w'.IsCycle ∧ w'.support.toFinset = w.support.toFinset := by
      refine' ⟨ w.rotate hv, hw.rotate _, _ ⟩;
      simp +decide [ Finset.ext_iff, List.mem_append ];
    -- Since $w'$ is a cycle, it must have at least three vertices, and thus $v$ must be adjacent to at least two other vertices in the cycle.
    have h_cycle_length : 3 ≤ w'.length := by
      exact hw'.1.three_le_length;
    obtain ⟨u₁, u₂, hu₁, hu₂, hu₁u₂⟩ : ∃ u₁ u₂ : V, u₁ ≠ u₂ ∧ w'.getVert 1 = u₁ ∧ w'.getVert (w'.length - 1) = u₂ := by
      have := hw'.1.getVert_injOn;
      exact ⟨ _, _, this.ne ( by constructor <;> omega ) ( by constructor <;> omega ) ( by omega ), rfl, rfl ⟩;
    use u₁, u₂;
    simp_all +decide [ SimpleGraph.Walk.getVert ];
    have h_adj : H.Adj v (w'.getVert 1) ∧ H.Adj (w'.getVert (w'.length - 1)) v := by
      constructor;
      · cases w' <;> aesop;
      · convert w'.adj_getVert_succ ( Nat.sub_lt ( by linarith ) zero_lt_one ) using 1;
        rw [ Nat.sub_add_cancel ( by linarith ), SimpleGraph.Walk.getVert_length ];
    exact ⟨ hu₂ ▸ h_adj.1, hu₁u₂ ▸ h_adj.2.symm ⟩;
  obtain ⟨ u₁, u₂, hne, h₁, h₂ ⟩ := h_cycle; exact Finset.one_lt_card.2 ⟨ u₁, by aesop, u₂, by aesop ⟩ ;

/-
In a max-degree-≤2 graph, every neighbour of a cycle-support vertex is again
on the cycle support (the cycle is a whole 2-regular component).
-/
lemma cycle_support_closed
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {x : V} (w : H.Walk x x) (hw : w.IsCycle) :
    ∀ v ∈ w.support, ∀ z, H.Adj v z → z ∈ w.support := by
  intro v hv z hz
  by_contra hz_not_in_w_support;
  obtain ⟨w', hw'⟩ : ∃ w' : H.Walk v v, w'.IsCycle ∧ w'.support.toFinset = w.support.toFinset := by
    exact ⟨ w.rotate hv, hw.rotate _, by simp +decide [ Finset.ext_iff ] ⟩;
  -- Since $w'$ is a cycle, it has exactly two neighbors at $v$: $u_1 = w'.getVert 1$ and $u_2 = w'.getVert (w'.length - 1)$.
  have h_neighbors : ∀ u ∈ H.neighborFinset v, u = w'.getVert 1 ∨ u = w'.getVert (w'.length - 1) := by
    have h_neighbors : H.neighborFinset v ⊇ {w'.getVert 1, w'.getVert (w'.length - 1)} := by
      have h_adj_u1 : H.Adj v (w'.getVert 1) := by
        cases w' <;> aesop
      have h_adj_u2 : H.Adj (w'.getVert (w'.length - 1)) v := by
        convert w'.adj_getVert_succ _;
        · rw [ Nat.sub_add_cancel ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ] ; simp +decide [ SimpleGraph.Walk.getVert ];
        · exact Nat.pred_lt ( ne_bot_of_gt ( SimpleGraph.Walk.IsCycle.three_le_length hw'.1 ) );
      simp_all +decide [ Finset.insert_subset_iff, SimpleGraph.adj_comm ];
    have h_neighbors_card : Finset.card ({w'.getVert 1, w'.getVert (w'.length - 1)} : Finset V) = 2 := by
      rw [ Finset.card_pair ];
      have := hw'.1.getVert_injOn;
      have := hw'.1.three_le_length; norm_num at *;
      exact fun h => absurd ( ‹Set.InjOn w'.getVert { i | 1 ≤ i ∧ i ≤ w'.length } › ( show 1 ∈ { i | 1 ≤ i ∧ i ≤ w'.length } from ⟨ by norm_num, by linarith ⟩ ) ( show w'.length - 1 ∈ { i | 1 ≤ i ∧ i ≤ w'.length } from ⟨ Nat.sub_pos_of_lt ( by linarith ), Nat.sub_le _ _ ⟩ ) h ) ( by omega );
    have h_neighbors_card : H.neighborFinset v = {w'.getVert 1, w'.getVert (w'.length - 1)} := by
      rw [ Finset.eq_of_subset_of_card_le h_neighbors ( by aesop ) ];
    simp [h_neighbors_card];
  cases h_neighbors z ( by simpa [ SimpleGraph.adj_comm ] using hz ) <;> simp_all +decide [ Finset.ext_iff ];
  · exact hz_not_in_w_support ( hw'.2 _ |>.1 ( by simp +decide [ SimpleGraph.Walk.getVert ] ) );
  · exact hz_not_in_w_support ( hw'.2 _ |>.1 ( by simp ) )

/-
In a max-degree-≤2 graph, if `x` lies on a cycle `w` then every vertex
reachable from `x` lies on `w` (the cycle occupies its whole component).
-/
lemma maxdeg2_component_of_cycle_is_2regular
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {x : V} (w : H.Walk x x) (hw : w.IsCycle)
    {u : V} (hu : H.Reachable x u) :
    u ∈ w.support := by
  obtain ⟨ p ⟩ := hu;
  have h_ind : ∀ {a : V} (q : H.Walk a u), a ∈ w.support → u ∈ w.support := by
    intro a q ha
    induction' q with a b q ih;
    · exact ha;
    · rename_i h₁ h₂ h₃;
      exact h₃ ( p ) ( cycle_support_closed H hdeg w hw b ha q h₁ );
  exact h_ind p ( w.start_mem_support )

/-- A degree-1 vertex lies on no cycle. -/
lemma not_mem_cycle_of_degree_one
    (H : SimpleGraph V) [DecidableRel H.Adj] {a : V} (hda : H.degree a = 1)
    {y : V} (c : H.Walk y y) (hc : c.IsCycle) : a ∉ c.support := by
  intro ha
  have := cycle_support_deg_ge_two H c hc a ha
  omega

/-
After deleting one edge `s(a,b)` of a cycle `w` (in a max-degree-≤2 graph,
with `a,b` of degree 2), no cycle of the smaller graph meets the component of the
deleted cycle.
-/
lemma deleted_cycle_component_acyclic
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg : ∀ v, H.degree v ≤ 2)
    {a b : V} (hab : H.Adj a b) (hda : H.degree a = 2)
    {x : V} (w : H.Walk x x) (hw : w.IsCycle) (haw : a ∈ w.support)
    {y : V} (c : (H.deleteEdges {s(a, b)}).Walk y y) (hc : c.IsCycle) :
    ∀ u ∈ c.support, u ∉ w.support := by
  intro u hu hwu
  have h_reachable : H.Reachable y a := by
    have h_reachable : H.Reachable y u := by
      exact ⟨ c.takeUntil u hu |> SimpleGraph.Walk.map ( SimpleGraph.Hom.ofLE ( SimpleGraph.deleteEdges_le _ ) ) ⟩
    have h_reachable' : H.Reachable u a := by
      have h_reachable' : H.Reachable x u := by
        exact ⟨ w.takeUntil u hwu ⟩
      have h_reachable'' : H.Reachable u a := by
        exact h_reachable'.symm.trans ( SimpleGraph.Reachable.trans ( SimpleGraph.Walk.reachable ( SimpleGraph.Walk.takeUntil w a haw ) ) ( SimpleGraph.Walk.reachable ( SimpleGraph.Walk.nil ) ) ) |> SimpleGraph.Reachable.trans <| SimpleGraph.Reachable.refl _;
      exact h_reachable'';
    exact h_reachable.trans h_reachable'
  have h_contradiction : a ∈ c.support := by
    have h_contradiction : a ∈ (c.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))).support := by
      have h_cycle : (c.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))).IsCycle := by
        exact hc.map ( by aesop_cat )
      apply maxdeg2_component_of_cycle_is_2regular H hdeg (c.map (SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _))) h_cycle h_reachable
    generalize_proofs at *; (
    aesop)
  have h_contradiction' : ¬∃ c' : (H.deleteEdges {s(a, b)}).Walk y y, c'.IsCycle ∧ a ∈ c'.support := by
    have h_contradiction' : (H.deleteEdges {s(a, b)}).degree a = 1 := by
      convert degree_deleteEdges_single H a b hab a using 1 ; simp +decide [ hda ];
    exact fun ⟨ c', hc', h ⟩ => not_mem_cycle_of_degree_one _ h_contradiction' c' hc' h
  exact h_contradiction' ⟨c, hc, h_contradiction⟩


/-! ## Odd-cycle-count monotonicity under edge deletion (descent building blocks)

These are the numeric engine of the descent/exchange argument: deleting an edge
from a graph can only destroy odd-cycle supports, never create them, and
deleting an edge that lies on an odd cycle of a max-degree-2 graph strictly
drops the odd-cycle count.  Neither statement needs `DecidableRel` because
`oddCycleSupports` is defined classically. -/

/-
Deleting edges only removes odd-cycle supports: every odd-cycle support of
`H.deleteEdges {e}` is already an odd-cycle support of `H`.  (An odd cycle in
the smaller graph maps, via the injective inclusion homomorphism, to an odd
cycle of `H` with the same vertex support.)
-/
lemma oddCycleSupports_deleteEdges_subset
    (H : SimpleGraph V) (e : Sym2 V) :
    oddCycleSupports (H.deleteEdges {e}) ⊆ oddCycleSupports H := by
  intro S hS;
  simp_all +decide [ Finset.mem_filter, oddCycleSupports ];
  obtain ⟨ x, w, hw₁, hw₂, hw₃ ⟩ := hS;
  refine' ⟨ x, w.map ( SimpleGraph.Hom.ofLE ( SimpleGraph.deleteEdges_le _ ) ), _, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.Walk.map ]

/-- Deleting an edge never increases the odd-cycle count. -/
lemma oddCycleCount_deleteEdges_le
    (H : SimpleGraph V) (e : Sym2 V) :
    oddCycleCount (H.deleteEdges {e}) ≤ oddCycleCount H :=
  Finset.card_le_card (oddCycleSupports_deleteEdges_subset H e)

/-- Deleting an edge that lies on an odd cycle of a max-degree-2 graph strictly
decreases the odd-cycle count.  Key point: an endpoint `a` of the deleted edge
lies on the odd cycle, so has `H`-degree `2`; after deletion its degree is `1`,
so it can no longer lie on any cycle, hence the deleted cycle's support leaves
`oddCycleSupports`. -/
lemma oddCycleCount_deleteEdges_lt
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v ≤ 2)
    {x : V} {c : H.Walk x x} (hc : c.IsCycle) (hodd : Odd c.length)
    {a b : V} (hab : H.Adj a b) (he : s(a, b) ∈ c.edges) :
    oddCycleCount (H.deleteEdges {s(a, b)}) < oddCycleCount H := by
  classical
  have hKdeg : ∀ v, (H.deleteEdges {s(a, b)}).degree v ≤ 2 := by
    intro v
    have h := degree_deleteEdges_single H a b hab v
    have hv := hdeg v
    split_ifs at h <;> omega
  have ha_supp : a ∈ c.support := c.fst_mem_support_of_mem_edges he
  have ha_deg : H.degree a = 2 := degree_eq_two_of_mem_cycle_support H hdeg hc ha_supp
  have hKa : (H.deleteEdges {s(a, b)}).degree a = 1 := by
    have h := degree_deleteEdges_single H a b hab a
    rw [ha_deg] at h
    simpa using h
  set S := c.support.toFinset with hS
  have hSmemH : S ∈ oddCycleSupports H := by
    unfold oddCycleSupports
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, x, c, hc, hodd, rfl⟩
  have haS : a ∈ S := by rw [hS]; exact List.mem_toFinset.mpr ha_supp
  have hSnotK : S ∉ oddCycleSupports (H.deleteEdges {s(a, b)}) := by
    intro hSK
    unfold oddCycleSupports at hSK
    rw [Finset.mem_filter] at hSK
    obtain ⟨-, y, c', hc', hodd', hsupp'⟩ := hSK
    have haC' : a ∈ c'.support := by
      have hmem : a ∈ c'.support.toFinset := by rw [hsupp']; exact haS
      exact List.mem_toFinset.mp hmem
    have h2 : (H.deleteEdges {s(a, b)}).degree a = 2 :=
      degree_eq_two_of_mem_cycle_support _ hKdeg hc' haC'
    omega
  have hsub := oddCycleSupports_deleteEdges_subset H (s(a, b))
  unfold oddCycleCount
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset hsub).mpr ⟨S, hSmemH, hSnotK⟩)


/-! ## Combinatorial avoidance core (transplanted sorry-free from the
`r4w11_descent_4reg` Aristotle return's companion `Avoidance.lean`; integrated
inline to preserve the one-file discipline — `Maj5Base` imports full Mathlib,
so `Finset.all_card_le_biUnion_card_iff_existsInjective'` is available).
Capacitated Hall: pairwise-disjoint families with members of size ≥ 3 admit a
transversal whose image contains no `T`-set in full. -/

namespace Avoid

set_option maxHeartbeats 1000000

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- The dangerous subtype: sets `t ∈ T` that could conceivably be covered by a
transversal of `S` (all vertices in some `S`-class, each class met ≤ once). -/
abbrev DangIx (S T : Finset (Finset V)) :=
  {t : Finset V // t ∈ T ∧ t ⊆ S.biUnion id ∧ ∀ s ∈ S, (t ∩ s).card ≤ 1}

/-- Hall counting bound (sum form): for any subfamily `I` of dangerous sets, its
size is at most the total "slack" `∑ (#s - 1)` over classes meeting `I`. -/
lemma hall_slot_sum
    (S T : Finset (Finset V))
    (hTdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (hScard : ∀ s ∈ S, 3 ≤ s.card)
    (hTcard : ∀ t ∈ T, 3 ≤ t.card)
    (I : Finset (DangIx S T)) :
    I.card ≤ ∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty), (s.card - 1) := by
  have h_card_I : I.card ≤ (∑ t ∈ I.image Subtype.val, t.card) / 3 := by
    rw [ Finset.sum_image ];
    · exact Nat.le_div_iff_mul_le three_pos |>.2 ( by simpa [ mul_comm ] using Finset.sum_le_sum fun x ( hx : x ∈ I ) => hTcard _ x.2.1 );
    · exact fun x hx y hy hxy => Subtype.ext hxy;
  have h_card_I : (∑ t ∈ I.image Subtype.val, t.card) ≤ (∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty), s.card) := by
    have h_card_I : (∑ t ∈ I.image Subtype.val, t.card) ≤ (∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty), (∑ t ∈ I.image Subtype.val, (t ∩ s).card)) := by
      rw [ Finset.sum_comm ];
      refine' Finset.sum_le_sum fun t ht => _;
      have h_card_I : t ⊆ Finset.biUnion (S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty)) (fun s => t ∩ s) := by
        grind;
      exact le_trans ( Finset.card_le_card h_card_I ) ( Finset.card_biUnion_le );
    refine' le_trans h_card_I ( Finset.sum_le_sum fun s hs => _ );
    rw [ ← Finset.card_biUnion ];
    · exact Finset.card_le_card ( Finset.biUnion_subset.mpr fun t ht => Finset.inter_subset_right );
    · intro t ht t' ht' h; simp_all +decide [ Finset.disjoint_left ] ;
      exact fun x hx₁ hx₂ hx₃ => hTdisj _ ( ht.1.1 ) _ ( ht'.1.1 ) h hx₁ hx₃;
  have h_card_I : (∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty), s.card) ≤ (∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty), (s.card - 1)) + (S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty)).card := by
    rw [ Finset.card_eq_sum_ones ];
    rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_le_sum fun x hx => by rw [ tsub_add_cancel_of_le ] ; exact Nat.succ_le_of_lt ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty ( by specialize hScard x ( Finset.mem_filter.mp hx |>.1 ) ; aesop_cat ) ) ) ;
  have h_card_I : (S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty)).card ≤ (∑ s ∈ S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty), (s.card - 1)) / 2 := by
    rw [ Nat.le_div_iff_mul_le zero_lt_two ];
    exact le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum fun x hx => show #x - 1 ≥ 2 from Nat.le_sub_one_of_lt ( hScard x ( Finset.mem_filter.mp hx |>.1 ) ) );
  omega

/-- Vertex-slot target of a set `t`: for each class meeting `t`, all its vertices
except the designated hole. -/
def slotTarget (S : Finset (Finset V)) (h : Finset V → V) (t : Finset V) : Finset V :=
  (S.filter (fun s => (t ∩ s).Nonempty)).biUnion (fun s => s.erase (h s))

/-- The `slotTarget`-biUnion over a subfamily `I` collapses to the biUnion over the
classes meeting `I`. -/
lemma biUnion_slotTarget_eq
    (S T : Finset (Finset V)) (h : Finset V → V)
    (I : Finset (DangIx S T)) :
    I.biUnion (fun t => slotTarget S h t.val)
      = (S.filter (fun s => ∃ t ∈ I, (t.val ∩ s).Nonempty)).biUnion (fun s => s.erase (h s)) := by
  ext v
  simp only [slotTarget, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨t, htI, s, ⟨hsS, hts⟩, hv⟩
    exact ⟨s, ⟨hsS, t, htI, hts⟩, hv⟩
  · rintro ⟨s, ⟨hsS, t, htI, hts⟩, hv⟩
    exact ⟨t, htI, s, ⟨hsS, hts⟩, hv⟩

/-
Hall matching: assign to each dangerous set an injective slot vertex.
-/
lemma exists_slot_matching
    (S T : Finset (Finset V)) (h : Finset V → V)
    (hSdisj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → Disjoint s₁ s₂)
    (hScard : ∀ s ∈ S, 3 ≤ s.card)
    (hTdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (hTcard : ∀ t ∈ T, 3 ≤ t.card)
    (hh : ∀ s ∈ S, h s ∈ s) :
    ∃ f : DangIx S T → V, Function.Injective f ∧
      ∀ t, f t ∈ slotTarget S h t.val := by
  have := @Finset.all_card_le_biUnion_card_iff_existsInjective' (DangIx S T) V;
  specialize this ( fun t => slotTarget S h t.val );
  refine' this.mp _;
  intro I
  rw [biUnion_slotTarget_eq S T h I];
  rw [ Finset.card_biUnion ];
  · convert hall_slot_sum S T hTdisj hScard hTcard I using 1;
    exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_erase_of_mem ( hh x ( Finset.mem_filter.mp hx |>.1 ) ) ] ;
  · exact fun s hs t ht hst => Disjoint.mono ( Finset.erase_subset _ _ ) ( Finset.erase_subset _ _ ) ( hSdisj s ( Finset.mem_filter.mp hs |>.1 ) t ( Finset.mem_filter.mp ht |>.1 ) hst )

/-
Combinatorial avoidance core.
-/
lemma avoidance_core
    (S T : Finset (Finset V))
    (hSdisj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → Disjoint s₁ s₂)
    (hTdisj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (hScard : ∀ s ∈ S, 3 ≤ s.card)
    (hTcard : ∀ t ∈ T, 3 ≤ t.card) :
    ∃ d : Finset V → V,
      (∀ s ∈ S, d s ∈ s) ∧ (∀ t ∈ T, ¬ t ⊆ S.image d) := by
  by_contra! h_contra;
  -- Set the hole function `h : Finset V → V := fun s => if hs : s.Nonempty then s.min' hs else Classical.arbitrary V`.
  obtain ⟨h, hh⟩ : ∃ h : Finset V → V, ∀ s ∈ S, h s ∈ s := by
    exact ⟨ fun s => if hs : s.Nonempty then Classical.choose hs else Classical.arbitrary V, fun s hs => by have := hScard s hs; exact Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) |> fun h => by aesop ⟩;
  obtain ⟨f, hf_inj, hf⟩ := exists_slot_matching S T h hSdisj hScard hTdisj hTcard hh;
  -- For each `t : DangIx S T`, unfold membership: there is a class `sc t ∈ S` with `(t.val ∩ sc t).Nonempty` and `f t ∈ (sc t).erase (h (sc t))`.
  obtain ⟨sc, hscS, hscMeet, hscf⟩ : ∃ sc : DangIx S T → Finset V, (∀ t, sc t ∈ S) ∧ (∀ t, (t.val ∩ sc t).Nonempty) ∧ (∀ t, f t ∈ (sc t).erase (h (sc t))) := by
    choose sc hscS hscMeet hscf using fun t => by have := hf t; simpa [ slotTarget, Finset.mem_biUnion, Finset.mem_filter ] using this;
    exact ⟨ sc, fun t => hscS t |>.1, fun t => hscS t |>.2, fun t => Finset.mem_erase_of_ne_of_mem ( hscMeet t ) ( hscf t ) ⟩;
  -- Choose a protected vertex for each dangerous set.
  obtain ⟨a, ha⟩ : ∃ a : DangIx S T → V, (∀ t, a t ∈ t.val) ∧ (∀ t, a t ∈ sc t) := by
    exact ⟨ fun t => Classical.choose ( hscMeet t ), fun t => Finset.mem_of_mem_inter_left ( Classical.choose_spec ( hscMeet t ) ), fun t => Finset.mem_of_mem_inter_right ( Classical.choose_spec ( hscMeet t ) ) ⟩;
  -- Define `As (s : Finset V) : Finset V := (Finset.univ.filter (fun t : DangIx S T => sc t = s)).image a`.
  set As : Finset V → Finset V := fun s => (Finset.univ.filter (fun t : DangIx S T => sc t = s)).image a;
  -- KEY CARD BOUND: for `s ∈ S`, `(As s).card ≤ s.card - 1`.
  have h_card_bound : ∀ s ∈ S, (As s).card ≤ s.card - 1 := by
    intro s hs
    have h_card_filter : (Finset.univ.filter (fun t : DangIx S T => sc t = s)).card ≤ (s.erase (h s)).card := by
      have h_card_filter : Finset.card (Finset.image f (Finset.univ.filter (fun t : DangIx S T => sc t = s))) ≤ Finset.card (s.erase (h s)) := by
        exact Finset.card_le_card ( Finset.image_subset_iff.mpr fun t ht => by aesop );
      rwa [ Finset.card_image_of_injective _ hf_inj ] at h_card_filter;
    exact le_trans ( Finset.card_image_le ) ( h_card_filter.trans ( by rw [ Finset.card_erase_of_mem ( hh s hs ) ] ) );
  -- Define `d : Finset V → V := fun s => if hs : s ∈ S then (s \ As s).min' (by ...) else Classical.arbitrary V`.
  obtain ⟨d, hd⟩ : ∃ d : Finset V → V, (∀ s ∈ S, d s ∈ s) ∧ (∀ s ∈ S, d s ∉ As s) := by
    have h_nonempty : ∀ s ∈ S, (s \ As s).Nonempty := by
      intro s hs
      have h_card : (s \ As s).card ≥ 1 := by
        grind;
      exact Finset.card_pos.mp h_card;
    choose! d hd using fun s hs => Finset.nonempty_iff_ne_empty.2 ( show s \ As s ≠ ∅ from Finset.Nonempty.ne_empty ( h_nonempty s hs ) );
    exact ⟨ d, fun s hs => Finset.mem_sdiff.mp ( hd s hs ) |>.1, fun s hs => Finset.mem_sdiff.mp ( hd s hs ) |>.2 ⟩;
  obtain ⟨ t, htT, ht ⟩ := h_contra d hd.1;
  -- Show that `t` is dangerous.
  have ht_dangerous : t ⊆ S.biUnion id ∧ ∀ s ∈ S, (t ∩ s).card ≤ 1 := by
    refine' ⟨ _, _ ⟩;
    · exact fun x hx => by have := ht hx; obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp this; exact Finset.mem_biUnion.mpr ⟨ s, hs, hd.1 s hs ⟩ ;
    · intro s hs
      have h_inter : t ∩ s ⊆ {d s} := by
        intro x hx; have := ht ( Finset.mem_of_mem_inter_left hx ) ; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ a, haS, rfl ⟩ := ht hx.1; specialize hSdisj a haS s hs; by_cases ha : a = s <;> simp_all +decide [ Finset.disjoint_left ] ;
      exact Finset.card_le_card h_inter;
  -- Consider `a T0 ∈ t` (haT). Show `a T0 ∉ S.image d`, contradicting `hsub (haT ...)`.
  have h_not_in_image : a ⟨t, htT, ht_dangerous⟩ ∉ S.image d := by
    simp +zetaDelta at *;
    intro s hs; specialize hd; have := hd.2 s hs t htT ht_dangerous.1 ht_dangerous.2; simp_all +decide [ Finset.disjoint_left ] ;
    grind +splitImp;
  exact h_not_in_image ( ht ( ha.1 ⟨ t, htT, ht_dangerous ⟩ ) )

end Avoid

/-! ### Odd-cycle supports satisfy the avoidance-core hypotheses
(transplanted sorry-free from the same return). -/

/-
Distinct odd-cycle supports of a max-degree-≤2 graph are disjoint (each is a
whole 2-regular component).
-/
lemma oddCycleSupports_pairwise_disjoint
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg2 : ∀ v, H.degree v ≤ 2) :
    ∀ S₁ ∈ oddCycleSupports H, ∀ S₂ ∈ oddCycleSupports H, S₁ ≠ S₂ → Disjoint S₁ S₂ := by
  intros S₁ hS₁ S₂ hS₂ hneq
  simp [oddCycleSupports] at hS₁ hS₂;
  obtain ⟨ x₁, w₁, hw₁, hw₁', rfl ⟩ := hS₁; obtain ⟨ x₂, w₂, hw₂, hw₂', rfl ⟩ := hS₂; simp_all +decide [ Finset.disjoint_left ] ;
  intro u hu₁ hu₂; contrapose! hneq; simp_all +decide [ Finset.ext_iff ] ;
  exact fun v => ⟨ fun hv => cycle_support_subset_of_mem H hdeg2 hw₁ hw₂ hu₁ hu₂ hv, fun hv => cycle_support_subset_of_mem H hdeg2 hw₂ hw₁ hu₂ hu₁ hv ⟩

/-
Every odd-cycle support has at least three vertices.
-/
lemma oddCycleSupports_three_le_card
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ S ∈ oddCycleSupports H, 3 ≤ S.card := by
  intro S;
  simp +decide [ oddCycleSupports ];
  rintro x w hw hw' rfl;
  refine' Finset.two_lt_card_iff.mpr _;
  rcases w with ( _ | ⟨ _, _, w ⟩ ) <;> simp_all +decide;
  · exact SimpleGraph.irrefl _ ‹_›;
  · rename_i k hk;
    rcases hk with ( _ | ⟨ _, _, hk ⟩ ) <;> simp_all +decide [ SimpleGraph.Walk.cons_isCycle_iff ]


/-! ## Clean transversals (round 9; probe-validated kernel target, PROBE-I.md)

`CleanVertex` formalizes probeI.py's domain predicate verbatim: a vertex all of
whose cross (`K`-) edges have cap `3`.  The probe's second failure mode
(NON-BIPARTITE-FORCED) is a transversal-level condition, so it lives in the
PIN's conclusion, not in the vertex predicate. -/

/-- A vertex is CLEAN for the cross half `K` when every `K`-edge at it has cap
`3` (equivalently: it and all its `K`-neighbours have `G`-degree 4). -/
def CleanVertex (G K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel K.Adj] (u : V) : Prop :=
  ∀ v, K.Adj u v → cap G u v = 3

/-- The clean subset of a support `S` (probeI.py's domain `D(Z) = C_H(Z)`). -/
def cleanSet (G K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel K.Adj] (S : Finset V) : Finset V :=
  S.filter (fun u => ∀ v, K.Adj u v → cap G u v = 3)

lemma mem_cleanSet (G K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel K.Adj] {S : Finset V} {u : V} :
    u ∈ cleanSet G K S ↔ u ∈ S ∧ CleanVertex G K u := by
  unfold cleanSet CleanVertex
  exact Finset.mem_filter

/-- PROVED.  Total-odd-cycle minimality is symmetric in the two halves. -/
lemma IsOddCycleMinimalSplit.swap
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (h : IsOddCycleMinimalSplit G H₀ H₁) :
    IsOddCycleMinimalSplit G H₁ H₀ := by
  refine ⟨IsEdgeSplit.swap G H₀ H₁ h.1, ?_⟩
  intro K₀ K₁ i₀ i₁ hK
  letI : DecidableRel K₀.Adj := i₀
  letI : DecidableRel K₁.Adj := i₁
  have := h.2 K₁ K₀ i₁ i₀ (IsEdgeSplit.swap G K₀ K₁ hK)
  omega

/-- OPEN-CRUX-DESCENT-CORE (round 12; the SINGLE remaining pin, transplanted
from the gated Codex descent candidate — see CODEX-DESCENT.md).  If a valid
split of a connected class-II degree-`{3,4}` graph admits NO clean transversal,
then a strictly-lower-total-odd-cycle split exists.  Its EMPTY-DOMAIN branch is
the poisoned-support strict descent; its NON-BIPARTITE branch is the
capacitated-Hall forced-transversal descent.  Both reduce to a global
augmenting-trail / common-transition theorem (parity-sensitive
Kempe/Tashkinov-style) — the named missing idea.  Evidence: a strict seeded
transition trail exists for ALL 15,525 poisoned-support instances over
connected degree-`{3,4}` graphs through `n = 9`.  Note `hsplit` only — the
descent statement needs no minimality. -/
lemma strict_descent_of_no_clean_transversal
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c)
    (hsplit : IsEdgeSplit G H₀ H₁)
    (hbad :
      ¬ ∃ d : Finset V → V,
        (∀ S ∈ oddCycleSupports H₀, d S ∈ S ∧ CleanVertex G H₁ (d S)) ∧
        (∀ S' ∈ oddCycleSupports H₁,
          ¬ (S' ⊆ (oddCycleSupports H₀).image d))) :
    ∃ (K₀ K₁ : SimpleGraph V)
      (_ : DecidableRel K₀.Adj) (_ : DecidableRel K₁.Adj),
      IsEdgeSplit G K₀ K₁ ∧
      oddCycleCount K₀ + oddCycleCount K₁ <
        oddCycleCount H₀ + oddCycleCount H₁ := by
  sorry

/-- CASE B of the clean-transversal crux (round 13): the degree-3 (poisoning)
regime.  PROVED modulo the descent core above — the by_contra/minimality
reduction of round 12, now needed only when a degree-3 vertex is present
(`hnreg`); the 4-regular case is closed unconditionally below via
`Avoid.avoidance_core`. -/
lemma clean_transversal_case_deg3
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c)
    (hmin : IsOddCycleMinimalSplit G H₀ H₁)
    (hnreg : ¬ ∀ v, G.degree v = 4) :
    ∃ d : Finset V → V,
      (∀ S ∈ oddCycleSupports H₀, d S ∈ S ∧ CleanVertex G H₁ (d S)) ∧
      (∀ S' ∈ oddCycleSupports H₁,
        ¬ (S' ⊆ (oddCycleSupports H₀).image d)) := by
  classical
  by_contra hbad
  obtain ⟨K₀, K₁, i₀, i₁, hK, hlt⟩ :=
    strict_descent_of_no_clean_transversal
      G H₀ H₁ hconn hdeg hII hmin.1 hbad
  have hge := hmin.2 K₀ K₁ i₀ i₁ hK
  omega

/-- PROVED (round 13) modulo the descent core, WITH THE 4-REGULAR CASE CLOSED
UNCONDITIONALLY: the round-9 kernel-target pin (CODEX-PARITY-KERNEL.md §6.1,
validated by PROBE-I.md: 1380 exhaustive minimal split-halves, zero failures).
Case split from the `r4w11_descent_4reg` return: if `G` is 4-regular, every
vertex is clean (`cap_eq_three_iff`) and `Avoid.avoidance_core` on the two
odd-cycle-support families produces the transversal outright — no `sorry`
anywhere on that branch; otherwise delegate to `clean_transversal_case_deg3`. -/
lemma clean_transversal_of_minimal
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c)
    (hmin : IsOddCycleMinimalSplit G H₀ H₁) :
    ∃ d : Finset V → V,
      (∀ S ∈ oddCycleSupports H₀, d S ∈ S ∧ CleanVertex G H₁ (d S)) ∧
      (∀ S' ∈ oddCycleSupports H₁,
        ¬ (S' ⊆ (oddCycleSupports H₀).image d)) := by
  haveI : Nonempty V := hconn.nonempty
  have hdeg2H0 : ∀ v, H₀.degree v ≤ 2 := hmin.1.2.2.2.2.1
  have hdeg2H1 : ∀ v, H₁.degree v ≤ 2 := hmin.1.2.2.2.2.2.1
  by_cases hreg : ∀ v, G.degree v = 4
  · -- CASE A: `G` is 4-regular, so every edge has cap 3 and every vertex is CLEAN.
    have hclean : ∀ u, CleanVertex G H₁ u := by
      intro u v huv
      exact (cap_eq_three_iff G hdeg u v).2 ⟨hreg u, hreg v⟩
    obtain ⟨d, hd_mem, hd_avoid⟩ :=
      Avoid.avoidance_core (oddCycleSupports H₀) (oddCycleSupports H₁)
        (oddCycleSupports_pairwise_disjoint H₀ hdeg2H0)
        (oddCycleSupports_pairwise_disjoint H₁ hdeg2H1)
        (oddCycleSupports_three_le_card H₀)
        (oddCycleSupports_three_le_card H₁)
    exact ⟨d, fun S hS => ⟨hd_mem S hS, hclean (d S)⟩, hd_avoid⟩
  · -- CASE B: a degree-3 vertex is present (degree-3 poisoning regime).
    exact clean_transversal_case_deg3 G H₀ H₁ hconn hdeg hII hmin hreg

/-- PROVED modulo the descent pin (its projection; the round-9 order's named
lemma).  At a minimal split every odd `H₀`-cycle support has a nonempty clean
set — the sharp PROBE-I finding (EMPTY-DOMAIN only ever at `ω ≥ min + 1`). -/
lemma clean_set_nonempty_of_minimal
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c)
    (hmin : IsOddCycleMinimalSplit G H₀ H₁) :
    ∀ S ∈ oddCycleSupports H₀, (cleanSet G H₁ S).Nonempty := by
  obtain ⟨d, hd, -⟩ := clean_transversal_of_minimal G H₀ H₁ hconn hdeg hII hmin
  intro S hS
  obtain ⟨hmem, hclean⟩ := hd S hS
  exact ⟨d S, (mem_cleanSet G H₁).mpr ⟨hmem, hclean⟩⟩

/-! ### Bridge helpers for `placement_of_clean_transversal` -/

/-- The cross half `K` restricted to a vertex set `D`: keep exactly the `K`-edges
whose *both* endpoints lie in `D`.  This is the graph `K[D]` whose odd cycles the
avoidance clause forbids, hence which the 2-colorer signs. -/
def crossOnSet (K : SimpleGraph V) (D : Finset V) : SimpleGraph V where
  Adj u v := K.Adj u v ∧ u ∈ D ∧ v ∈ D
  symm := fun _ _ ⟨h, hu, hv⟩ => ⟨h.symm, hv, hu⟩
  loopless := ⟨fun v h => (K.ne_of_adj h.1) rfl⟩

lemma crossOnSet_le (K : SimpleGraph V) (D : Finset V) : crossOnSet K D ≤ K :=
  fun _ _ h => h.1

/-- Every vertex on a positive-length `crossOnSet K D`-walk lies in `D`. -/
lemma crossOnSet_support_subset (K : SimpleGraph V) (D : Finset V) {x y : V}
    (w : (crossOnSet K D).Walk x y) (hpos : 0 < w.length) :
    ∀ z ∈ w.support, z ∈ D := by
  induction w with
  | nil => simp at hpos
  | @cons a b c hadj p ih =>
    intro z hz
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hadj.2.1
    · rcases Nat.eq_zero_or_pos p.length with hz0 | hzp
      · have hbc := Walk.eq_of_length_eq_zero hz0
        subst hbc
        cases p with
        | nil =>
          simp only [Walk.support_nil, List.mem_singleton] at hz
          subst hz; exact hadj.2.2
        | cons _ _ => simp at hz0
      · exact ih hzp z hz

/-- The avoidance clause makes `K[D]` odd-cycle-free: any odd cycle of
`crossOnSet K D` maps down to an odd `K`-cycle whose support lies in `D`,
contradicting `havoid`. -/
lemma crossOnSet_noOddCycle (K : SimpleGraph V) [DecidableRel K.Adj] (D : Finset V)
    (havoid : ∀ S' ∈ oddCycleSupports K, ¬ (S' ⊆ D)) :
    ∀ x (w : (crossOnSet K D).Walk x x), w.IsCycle → ¬ Odd w.length := by
  intro x w hc hodd
  have hcK : (w.mapLe (crossOnSet_le K D)).IsCycle :=
    Walk.IsCycle.mapLe (crossOnSet_le K D) hc
  have hlen : (w.mapLe (crossOnSet_le K D)).length = w.length := by simp [Walk.mapLe]
  have hsupp : (w.mapLe (crossOnSet_le K D)).support = w.support := by simp [Walk.mapLe]
  have hoddK : Odd (w.mapLe (crossOnSet_le K D)).length := by rw [hlen]; exact hodd
  have hmem : (w.mapLe (crossOnSet_le K D)).support.toFinset ∈ oddCycleSupports K := by
    unfold oddCycleSupports
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, x, _, hcK, hoddK, rfl⟩
  have hpos : 0 < w.length := by have := hc.three_le_length; omega
  have hsub : (w.mapLe (crossOnSet_le K D)).support.toFinset ⊆ D := by
    rw [hsupp]
    intro z hz
    rw [List.mem_toFinset] at hz
    exact crossOnSet_support_subset K D w hpos z hz
  exact havoid _ hmem hsub

/-- A transversal picking one vertex from each odd-`H`-cycle support is an
`IsOddCycleDefectSet` (adaptation of `exists_isOddCycleDefectSet` with an
arbitrary selector `d` in place of the arbitrary choice). -/
lemma isOddCycleDefectSet_image_transversal
    (H : SimpleGraph V) [DecidableRel H.Adj] (hdeg2 : ∀ v, H.degree v ≤ 2)
    (d : Finset V → V)
    (hd : ∀ S ∈ oddCycleSupports H, d S ∈ S) :
    IsOddCycleDefectSet H ((oddCycleSupports H).image d) := by
  classical
  refine ⟨?_, ?_⟩
  · intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨S, hS, hpick⟩ := hv
    have hmem : v ∈ S := hpick ▸ hd S hS
    have hS' := hS
    unfold oddCycleSupports at hS'
    simp only [Finset.mem_filter] at hS'
    obtain ⟨-, x, w, hw, hodd, hsupp⟩ := hS'
    refine ⟨x, w, hw, hodd, ?_⟩
    rw [← hsupp] at hmem
    simpa using hmem
  · intro x w hw hodd
    have hS₀ : w.support.toFinset ∈ oddCycleSupports H := by
      unfold oddCycleSupports
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, x, w, hw, hodd, rfl⟩
    have hv₀S : d (w.support.toFinset) ∈ w.support.toFinset := hd _ hS₀
    refine ⟨d (w.support.toFinset), ⟨by simpa using hv₀S, ?_⟩, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨_, hS₀, rfl⟩
    · rintro v' ⟨hv'w, hv'D⟩
      rw [Finset.mem_image] at hv'D
      obtain ⟨S', hS', hpick⟩ := hv'D
      have hv'S' : v' ∈ S' := hpick ▸ hd S' hS'
      have hS'w : S' = w.support.toFinset := by
        have hS'c := hS'
        unfold oddCycleSupports at hS'c
        simp only [Finset.mem_filter] at hS'c
        obtain ⟨-, x', w', hw', hodd', hsupp'⟩ := hS'c
        have hv'w' : v' ∈ w'.support := by
          rw [← hsupp'] at hv'S'
          simpa using hv'S'
        ext t
        simp only [← hsupp', List.mem_toFinset]
        constructor
        · intro ht
          exact cycle_support_subset_of_mem H hdeg2 hw' hw hv'w' hv'w ht
        · intro ht
          exact cycle_support_subset_of_mem H hdeg2 hw hw' hv'w hv'w' ht
      rw [← hpick, hS'w]


/-- PROVED (transplant, round 10; formerly BRIDGE-EXPECTED).  A clean transversal yields the per-half
placement data.  Proof shape, fully covered by banked machinery: all cap-2
`DefectSafe` clauses are vacuous at clean defects (`CleanVertex` kills the
antecedent); the cap-3 clause needs a proper 2-signing of the selected set
inside `H₁`... i.e. of `K[D]`, which the avoidance clause makes odd-cycle-free
(max-degree-2), so `colorable_two_of_no_odd_cycle` supplies `σ`; support
disjointness (A0 suite) gives `IsOddCycleDefectSet`, and
`exists_isMinAlternating` realizes `b`. -/
lemma placement_of_clean_transversal
    (G H K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hsplit : IsEdgeSplit G H K)
    (d : Finset V → V)
    (hd : ∀ S ∈ oddCycleSupports H, d S ∈ S ∧ CleanVertex G K (d S))
    (havoid : ∀ S' ∈ oddCycleSupports K,
      ¬ (S' ⊆ (oddCycleSupports H).image d)) :
    ∃ (D : Finset V) (σ : V → Bool) (b : Sym2 V → Bool),
      IsMinAlternating H b D σ ∧ DefectSafe G H K b D σ := by
  classical
  have hdeg2 : ∀ v, H.degree v ≤ 2 := hsplit.2.2.2.2.1
  set D : Finset V := (oddCycleSupports H).image d with hDdef
  have hclean : ∀ x ∈ D, CleanVertex G K x := by
    intro x hx
    rw [hDdef, Finset.mem_image] at hx
    obtain ⟨S, hS, hpick⟩ := hx
    rw [← hpick]
    exact (hd S hS).2
  have hoddset : IsOddCycleDefectSet H D :=
    isOddCycleDefectSet_image_transversal H hdeg2 d (fun S hS => (hd S hS).1)
  have hnoodd : ∀ x (w : (crossOnSet K D).Walk x x), w.IsCycle → ¬ Odd w.length :=
    crossOnSet_noOddCycle K D havoid
  obtain ⟨c⟩ := colorable_two_of_no_odd_cycle (crossOnSet K D) hnoodd
  set σ : V → Bool := fun v => decide (c v = 1) with hσdef
  obtain ⟨b, hb⟩ := exists_isMinAlternating H hdeg2 D σ hoddset
  refine ⟨D, σ, b, hb, ?_⟩
  intro u v huv
  refine ⟨?_, ?_⟩
  · intro hcap2
    refine ⟨?_, ?_⟩
    · intro hu
      exfalso
      have hc3 := hclean u hu v huv
      omega
    · intro hv
      exfalso
      have hc3 := hclean v hv u huv.symm
      rw [cap_comm G v u] at hc3
      omega
  · intro _ hu hv
    have hadj : (crossOnSet K D).Adj u v := ⟨huv, hu, hv⟩
    have hne := c.valid hadj
    have h1 : c u = 0 ∨ c u = 1 := by omega
    have h2 : c v = 0 ∨ c v = 1 := by omega
    rw [hσdef]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all

/-- PROVED (round 9) modulo the descent pin and the bridge: the universal
placement conjecture, re-threaded through clean transversals on both ordered
halves (`IsOddCycleMinimalSplit.swap` supplies the second half).

Empirically, EVERY total-odd-cycle-minimal split tested admits these data.
Arbitrary splits do not (`K₃,₃+e` supplies a fixed-split obstruction).  The
statement permits unboundedly many odd cycles/defects, as required by cyclic
chains of `K₅-e` blocks. -/
lemma placement_on_oddCycleMinimal_split
    (G H₀ H₁ : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H₀.Adj] [DecidableRel H₁.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c)
    (hmin : IsOddCycleMinimalSplit G H₀ H₁) :
    ∃ (D₀ D₁ : Finset V) (σ₀ σ₁ : V → Bool)
      (b₀ b₁ : Sym2 V → Bool),
      IsMinAlternating H₀ b₀ D₀ σ₀ ∧
      DefectSafe G H₀ H₁ b₀ D₀ σ₀ ∧
      IsMinAlternating H₁ b₁ D₁ σ₁ ∧
      DefectSafe G H₁ H₀ b₁ D₁ σ₁ := by
  obtain ⟨d₀, hd₀, havoid₀⟩ :=
    clean_transversal_of_minimal G H₀ H₁ hconn hdeg hII hmin
  obtain ⟨d₁, hd₁, havoid₁⟩ :=
    clean_transversal_of_minimal G H₁ H₀ hconn hdeg hII
      (IsOddCycleMinimalSplit.swap G H₀ H₁ hmin)
  obtain ⟨D₀, σ₀, b₀, halt₀, hsafe₀⟩ :=
    placement_of_clean_transversal G H₀ H₁ hdeg hmin.1 d₀ hd₀ havoid₀
  obtain ⟨D₁, σ₁, b₁, halt₁, hsafe₁⟩ :=
    placement_of_clean_transversal G H₁ H₀ hdeg
      (IsEdgeSplit.swap G H₀ H₁ hmin.1) d₁ hd₁ havoid₁
  exact ⟨D₀, D₁, σ₀, σ₁, b₀, b₁, halt₀, hsafe₀, halt₁, hsafe₁⟩

/-- OPEN-CRUX-EX (round 7; authored per the Scheme-C quantifier analysis in
CODEX-PARITY-KERNEL.md §5).  Existential form of the placement crux: SOME split
of a connected class-II degree-`{3,4}` graph admits defect-safe placement data
in both halves.  This is exactly — and no more than — what
`strongMajority_of_safe_defects` consumes downstream: the split contract, a
`DefectProfile` per half (NOT full `IsMinAlternating`: the odd-cycle-transversal
component is never used by the assembly), and `DefectSafe` both ways.  It is
strictly weaker than `placement_on_oddCycleMinimal_split` (which fixes an
ARBITRARY total-odd-minimal split): a lexicographic `(ω, Φ)` descent — Scheme C
— proves this form without the split-transport theorem the universal form
needs.  Since round 9 it is PROVED from the universal lemma (itself re-threaded
through the clean-transversal descent pin) + `exists_oddCycleMinimal_split`. -/
lemma exists_safe_split_placement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c) :
    ∃ (H₀ H₁ : SimpleGraph V)
      (_ : DecidableRel H₀.Adj) (_ : DecidableRel H₁.Adj),
      IsEdgeSplit G H₀ H₁ ∧
      ∃ (D₀ D₁ : Finset V) (σ₀ σ₁ : V → Bool) (b₀ b₁ : Sym2 V → Bool),
        DefectProfile H₀ b₀ D₀ σ₀ ∧
        DefectSafe G H₀ H₁ b₀ D₀ σ₀ ∧
        DefectProfile H₁ b₁ D₁ σ₁ ∧
        DefectSafe G H₁ H₀ b₁ D₁ σ₁ := by
  obtain ⟨H₀, H₁, i₀, i₁, hmin⟩ := exists_oddCycleMinimal_split G hdeg
  letI : DecidableRel H₀.Adj := i₀
  letI : DecidableRel H₁.Adj := i₁
  obtain ⟨D₀, D₁, σ₀, σ₁, b₀, b₁, halt₀, hsafe₀, halt₁, hsafe₁⟩ :=
    placement_on_oddCycleMinimal_split G H₀ H₁ hconn hdeg hII hmin
  exact ⟨H₀, H₁, inferInstance, inferInstance, hmin.1, D₀, D₁, σ₀, σ₁, b₀, b₁,
    halt₀.2, hsafe₀, halt₁.2, hsafe₁⟩

/-! ## Final assembly: class I versus class II -/

/-- PROVED as a thread; since round 7 the critical path runs through the
EXISTENTIAL pin `exists_safe_split_placement` (Scheme-C form) rather than the
universal `placement_on_oddCycleMinimal_split`, which remains in the file as a
parallel route.  No parity stratification is used. -/
lemma classII_arm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (hII : ¬ ∃ c : Sym2 V → Fin 4, IsProper4 G c) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c := by
  obtain ⟨H₀, H₁, i₀, i₁, hsplit, D₀, D₁, σ₀, σ₁, b₀, b₁,
    hprof₀, hsafe₀, hprof₁, hsafe₁⟩ :=
    exists_safe_split_placement G hconn hdeg hII
  letI : DecidableRel H₀.Adj := i₀
  letI : DecidableRel H₁.Adj := i₁
  exact ⟨combine H₀ b₀ b₁,
    strongMajority_of_safe_defects G H₀ H₁ hdeg hsplit b₀ b₁ D₀ D₁ σ₀ σ₁
      hprof₀ hprof₁ hsafe₀ hsafe₁⟩

/-- PROVED as a classical class-I/class-II case split, conditional only on
the explicitly tagged pins above. -/
theorem R4_three_four_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c := by
  by_cases hI : ∃ c : Sym2 V → Fin 4, IsProper4 G c
  · exact classI_arm G hdeg hI
  · exact classII_arm G hconn hdeg hI

/-! ## Component-lift infrastructure (transplanted sorry-free from the
`r4w3_component_lift` Aristotle return; `Rung4Kernel.cnt`/`nColor_add_two_mul`
re-attached to this file's local `cnt`/`nColor_add_two_mul`).  This closes the
former `R4_three_four` pin: colour each connected component with the connected
theorem and glue. -/

open scoped Classical

/-- On a connected component `K`, the induced subgraph has the same degree at each
vertex as `G`, because every `G`-neighbour of a component vertex lies in the same
component. -/
lemma induce_supp_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : G.ConnectedComponent) (v : K.supp) :
    (G.induce K.supp).degree v = G.degree v.1 := by
  rw [SimpleGraph.degree, SimpleGraph.degree]
  apply Finset.card_bij (fun (w : K.supp) _ => (w : V))
  · intro w hw
    simp only [mem_neighborFinset, induce_adj] at hw ⊢
    exact hw
  · intro a ha b hb hab
    simp only [mem_neighborFinset] at ha hb
    exact Subtype.ext hab
  · intro w hw
    simp only [mem_neighborFinset] at hw
    have hmem : w ∈ K.supp := K.mem_supp_of_adj_mem_supp v.2 hw
    exact ⟨⟨w, hmem⟩, by simp [mem_neighborFinset, hw], rfl⟩

/-- Send a vertex into a component's support, using an arbitrary base point of the
(nonempty) support for vertices outside it.  Only the in-support branch is ever used. -/
noncomputable def projTo (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : G.ConnectedComponent) (w : V) : K.supp :=
  if h : w ∈ K.supp then ⟨w, h⟩ else ⟨K.nonempty_supp.choose, K.nonempty_supp.choose_spec⟩

/-- Ordered-pair form of the glued coloring: an ordered pair inside a single
component is colored by that component's coloring; otherwise `0`. -/
noncomputable def glueAux (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : ∀ K : G.ConnectedComponent, Sym2 K.supp → Fin 4) (u v : V) : Fin 4 :=
  if h : G.connectedComponentMk u = G.connectedComponentMk v
  then col (G.connectedComponentMk u) (Sym2.map (projTo G (G.connectedComponentMk u)) s(u, v))
  else 0

lemma glueAux_symm (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : ∀ K : G.ConnectedComponent, Sym2 K.supp → Fin 4) (u v : V) :
    glueAux G col u v = glueAux G col v u := by
  unfold glueAux
  by_cases h : G.connectedComponentMk u = G.connectedComponentMk v
  · rw [dif_pos h, dif_pos h.symm, ← h, Sym2.map_pair_eq, Sym2.map_pair_eq, Sym2.eq_swap]
  · rw [dif_neg h, dif_neg (fun e => h e.symm)]

/-- The glued `Sym2 V → Fin 4` coloring assembled from a per-component family. -/
noncomputable def glue (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : ∀ K : G.ConnectedComponent, Sym2 K.supp → Fin 4) : Sym2 V → Fin 4 :=
  Sym2.lift ⟨glueAux G col, glueAux_symm G col⟩

lemma glue_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : ∀ K : G.ConnectedComponent, Sym2 K.supp → Fin 4) (u v : V) :
    glue G col s(u, v) = glueAux G col u v := rfl

/-- On a genuine edge `s(u,w)`, the glued coloring is exactly the component
coloring evaluated at the corresponding induced-subgraph edge. -/
lemma glue_edge (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : ∀ K : G.ConnectedComponent, Sym2 K.supp → Fin 4) {u w : V} (huw : G.Adj u w)
    (hu : u ∈ (G.connectedComponentMk u).supp) (hw : w ∈ (G.connectedComponentMk u).supp) :
    glue G col s(u, w) = col (G.connectedComponentMk u) s(⟨u, hu⟩, ⟨w, hw⟩) := by
  have hcomp : G.connectedComponentMk u = G.connectedComponentMk w :=
    ConnectedComponent.connectedComponentMk_eq_of_adj huw
  rw [glue_mk]; unfold glueAux
  rw [dif_pos hcomp, Sym2.map_pair_eq]
  congr 1; rw [Sym2.eq_iff]; left
  exact ⟨by simp [projTo, hu], by simp [projTo, hw]⟩

/-- Per-vertex count transfer: the number of `α`-colored `glue`-edges incident to a
component vertex `u` in `G` equals the count in the induced subgraph. -/
lemma cnt_glue_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : ∀ K : G.ConnectedComponent, Sym2 K.supp → Fin 4)
    (K : G.ConnectedComponent) (u : V) (hu : u ∈ K.supp) (α : Fin 4) :
    cnt G (glue G col) u α
      = cnt (G.induce K.supp) (col K) ⟨u, hu⟩ α := by
  refine' Finset.card_bij ( fun f hf => Sym2.map ( fun v : K.supp => v ) ( Sym2.map ( fun x : V => if hx : x ∈ K.supp then ⟨ x, hx ⟩ else ⟨ K.nonempty_supp.choose, K.nonempty_supp.choose_spec ⟩ ) f ) ) _ _ _ <;> simp +decide [ Finset.mem_filter, SimpleGraph.mem_incidenceFinset ] at *;
  · intro e he hglue
    have h_adj : ∀ v ∈ e, G.connectedComponentMk v = K := by
      cases e ; simp_all +decide [ SimpleGraph.mk'_mem_incidenceSet_iff ];
      cases he.2 <;> simp_all +decide [ SimpleGraph.connectedComponentMk ];
      · exact hu ▸ Quot.sound ( SimpleGraph.Adj.reachable he ) ▸ rfl;
      · exact hu ▸ Quot.sound ( SimpleGraph.Adj.reachable he );
    rcases e with ⟨ x, y ⟩ ; simp_all +decide [ SimpleGraph.incidenceSet ] ;
    grind +suggestions;
  · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; rcases a₁ with ⟨ x, y ⟩ ; rcases a₂ with ⟨ u, v ⟩ ; simp_all +decide [ SimpleGraph.incidenceSet ] ;
    grind +suggestions;
  · rintro ⟨ x, y ⟩ hxy hα; use s(x.val, y.val); simp_all +decide [ SimpleGraph.mk'_mem_incidenceSet_iff ] ;
    grind +suggestions

/-- Row-count transfer: the `nColor` of a `glue`-edge in `G` equals the `nColor` of
the corresponding edge in the induced subgraph. -/
lemma nColor_glue_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (col : ∀ K : G.ConnectedComponent, Sym2 K.supp → Fin 4) {u v : V} (huv : G.Adj u v)
    (hu : u ∈ (G.connectedComponentMk u).supp) (hv : v ∈ (G.connectedComponentMk u).supp)
    (α : Fin 4) :
    SMaj.nColor G (glue G col) u v α
      = SMaj.nColor (G.induce (G.connectedComponentMk u).supp)
          (col (G.connectedComponentMk u)) ⟨u, hu⟩ ⟨v, hv⟩ α := by
  have hadj : (G.induce (G.connectedComponentMk u).supp).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
    rw [induce_adj]; exact huv
  have e1 := nColor_add_two_mul G (glue G col) huv α
  have e2 := nColor_add_two_mul (G.induce (G.connectedComponentMk u).supp)
    (col (G.connectedComponentMk u)) hadj α
  have hc1 := cnt_glue_eq G col (G.connectedComponentMk u) u hu α
  have hc2 := cnt_glue_eq G col (G.connectedComponentMk u) v hv α
  have hedge := glue_edge G col huv hu hv
  rw [hedge] at e1
  rw [hc1, hc2] at e1
  omega

/-- PROVED (component lift).  Every finite simple graph with all degrees in `{3,4}`
has a strong majority 4-coloring: colour each connected component with
`R4_three_four_connected` and glue.  Transplanted sorry-free from the
`r4w3_component_lift` return. -/
theorem R4_three_four
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c := by
  have hcol : ∀ K : G.ConnectedComponent, ∃ c : Sym2 K.supp → Fin 4,
      SMaj.IsStrongMajority (G.induce K.supp) c := by
    intro K
    apply R4_three_four_connected _ (K.maximal_connected_induce_supp).1
    intro v
    rw [induce_supp_degree G K v]
    exact hdeg v.1
  choose col hcolp using hcol
  refine ⟨glue G col, ?_⟩
  intro u v huv α
  have hu : u ∈ (G.connectedComponentMk u).supp := ConnectedComponent.connectedComponentMk_mem
  have hv : v ∈ (G.connectedComponentMk u).supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
  have hadj : (G.induce (G.connectedComponentMk u).supp).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
    rw [induce_adj]; exact huv
  have hb := hcolp (G.connectedComponentMk u) ⟨u, hu⟩ ⟨v, hv⟩ hadj α
  rw [nColor_glue_eq G col huv hu hv α]
  rw [induce_supp_degree G _ ⟨u, hu⟩, induce_supp_degree G _ ⟨v, hv⟩] at hb
  exact hb

/-! ## The unconditional 4-regular theorem (round 16)

`R4_four_regular` runs a PARALLEL sorry-free chain — it must NOT route through
`clean_transversal_of_minimal` (whose compiled term contains the degree-3
branch and hence `sorryAx`, regardless of input).  For 4-regular graphs the
placement needs neither minimality, connectivity, nor the class split: ANY
split works (every vertex is clean; `Avoid.avoidance_core` supplies both
transversals), so the chain is `exists_edge_split_pin` → `avoidance_core` ×2 →
`placement_of_clean_transversal` ×2 → `strongMajority_of_safe_defects`. -/

/-- THEOREM (unconditional, kernel-clean).  Every finite simple 4-regular graph
admits a strong majority edge-coloring with four colors: `Maj′(G) ≤ 4`. -/
theorem R4_four_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c := by
  classical
  obtain hV | hV := isEmpty_or_nonempty V
  · refine ⟨fun _ => 0, ?_⟩
    intro u
    exact (hV.elim u)
  · have hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4 := fun v => Or.inr (hreg v)
    have hle : ∀ v, G.degree v ≤ 4 := fun v => by rw [hreg v]
    obtain ⟨H₀, H₁, i₀, i₁, hsplit⟩ := exists_edge_split_pin G hle
    letI : DecidableRel H₀.Adj := i₀
    letI : DecidableRel H₁.Adj := i₁
    have hclean₀ : ∀ u, CleanVertex G H₁ u :=
      fun u v _ => (cap_eq_three_iff G hdeg u v).2 ⟨hreg u, hreg v⟩
    have hclean₁ : ∀ u, CleanVertex G H₀ u :=
      fun u v _ => (cap_eq_three_iff G hdeg u v).2 ⟨hreg u, hreg v⟩
    have hdeg2H0 : ∀ v, H₀.degree v ≤ 2 := hsplit.2.2.2.2.1
    have hdeg2H1 : ∀ v, H₁.degree v ≤ 2 := hsplit.2.2.2.2.2.1
    obtain ⟨d₀, hd₀mem, hd₀avoid⟩ :=
      Avoid.avoidance_core (oddCycleSupports H₀) (oddCycleSupports H₁)
        (oddCycleSupports_pairwise_disjoint H₀ hdeg2H0)
        (oddCycleSupports_pairwise_disjoint H₁ hdeg2H1)
        (oddCycleSupports_three_le_card H₀)
        (oddCycleSupports_three_le_card H₁)
    obtain ⟨d₁, hd₁mem, hd₁avoid⟩ :=
      Avoid.avoidance_core (oddCycleSupports H₁) (oddCycleSupports H₀)
        (oddCycleSupports_pairwise_disjoint H₁ hdeg2H1)
        (oddCycleSupports_pairwise_disjoint H₀ hdeg2H0)
        (oddCycleSupports_three_le_card H₁)
        (oddCycleSupports_three_le_card H₀)
    obtain ⟨D₀, σ₀, b₀, halt₀, hsafe₀⟩ :=
      placement_of_clean_transversal G H₀ H₁ hdeg hsplit d₀
        (fun S hS => ⟨hd₀mem S hS, hclean₀ (d₀ S)⟩) hd₀avoid
    obtain ⟨D₁, σ₁, b₁, halt₁, hsafe₁⟩ :=
      placement_of_clean_transversal G H₁ H₀ hdeg
        (IsEdgeSplit.swap G H₀ H₁ hsplit) d₁
        (fun S hS => ⟨hd₁mem S hS, hclean₁ (d₁ S)⟩) hd₁avoid
    exact ⟨combine H₀ b₀ b₁,
      strongMajority_of_safe_defects G H₀ H₁ hdeg hsplit b₀ b₁ D₀ D₁ σ₀ σ₁
        halt₀.2 halt₁.2 hsafe₀ hsafe₁⟩

end Rung4Moonshot
