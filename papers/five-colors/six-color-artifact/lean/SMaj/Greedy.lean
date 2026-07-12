/-
SMaj/Greedy.lean — the greedy rainbow route (campaign C10, lens
C10L3-lean-rainbow, 2026-07-08).

DECISION AT LENS OPEN (per the §38.3 L3⁸ charter): full Vizing (fan/Kempe)
is absent from mathlib v4.30.0 — as is even greedy vertex coloring — and is
a multi-week formalization; this lens banks the days-cheap greedy route
instead.  Machine pretest: `lenses/C10L3-lean-rainbow/pretest_greedy.py`
(exit 0; P-A greedy invariant on 11,400 runs / 155,902 colored edges with
the conflict bound 2s−2 attained, P-B fiber arithmetic, P-C the s ≤ 2
corner, P-D the strong-majority composition end-to-end on 85 no-{2,4}
graphs) was run BEFORE these proofs were written.

Proved here:
* `exists_rainbowOn` — the greedy induction: coloring edges one at a time,
  each new edge conflicts with ≤ 2s−2 already-colored edges (the two
  endpoint fibers minus the edge itself), so 2s−1 colors always admit a
  free one.
* `rainbow_of_groupSizes_greedy` — a rainbow (2s−1)-coloring exists when
  all groups have size ≤ s (the greedy substitute for the `proof_wanted`
  `rainbow_of_groupSizes`, which is Vizing and stays open).
* `rainbow_of_groupSizes_le_two` — the `proof_wanted`'s EXACT (s+1)-shape
  for s ≤ 2, where 2s−1 ≤ s+1 (a genuine partial close; at s = 1, 2 no
  Vizing is needed).
* `strongMajority_greedy_of_crit` — **unconditional** Master-Theorem
  corollary: every graph all of whose edges satisfy CRIT_s is admissible
  and has a strong majority (2s−1)-coloring, i.e. Maj′(G) ≤ 2s−1 on
  CRIT_s — no existence input left open.
* `strongMajority_five_of_no24` — the s = 3 instantiation: Maj′(G) ≤ 5
  unconditionally on the no-degree-{2,4} class (Corollary-A class).
  NOT claimed novel (ATTACK.md §35.42): the value banked is the
  machine-checked unconditional pipeline, not the constant.
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Arith
import SMaj.Master

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

variable (G) in
/-- `c` is rainbow on the grouping `ix` restricted to the edge subset `E`:
two incident edges of `E` at a common vertex, in the same group, with the
same color, are equal.  `IsRainbow` is recovered at `E = G.edgeFinset`. -/
def IsRainbowOn (ix : V → Sym2 V → ℕ) (c : Sym2 V → C)
    (E : Finset (Sym2 V)) : Prop :=
  ∀ v : V, ∀ f₁ ∈ G.incidenceFinset v, ∀ f₂ ∈ G.incidenceFinset v,
    f₁ ∈ E → f₂ ∈ E → ix v f₁ = ix v f₂ → c f₁ = c f₂ → f₁ = f₂

omit [DecidableEq C] in
/-- Rainbow on all of `G.edgeFinset` is rainbow (incident edges are edges). -/
lemma isRainbow_of_isRainbowOn_edgeFinset {ix : V → Sym2 V → ℕ}
    {c : Sym2 V → C} (h : IsRainbowOn G ix c G.edgeFinset) :
    IsRainbow G ix c := by
  intro v f₁ h₁ f₂ h₂
  have m₁ : f₁ ∈ G.edgeFinset :=
    mem_edgeFinset.mpr (G.incidenceSet_subset v (mem_incFinset.mp h₁))
  have m₂ : f₂ ∈ G.edgeFinset :=
    mem_edgeFinset.mpr (G.incidenceSet_subset v (mem_incFinset.mp h₂))
  exact h v f₁ h₁ f₂ h₂ m₁ m₂

/-- **The greedy induction** (machine-pretested P-A): for any edge subset
`E`, a coloring with 2s−1 colors exists that is rainbow on `E`, provided
every group of `ix` has ≤ s members.  Remove an edge `e = s(u,v)`, color
the rest, and give `e` a color avoiding its ≤ (s−1) + (s−1) conflicting
colored edges (the two endpoint fibers of `e`, `e` itself erased). -/
theorem exists_rainbowOn (s : ℕ) (hs : 1 ≤ s) (ix : V → Sym2 V → ℕ)
    (hsz : GroupSizesLE G ix s) (E : Finset (Sym2 V)) :
    ∃ c : Sym2 V → Fin (2 * s - 1), IsRainbowOn G ix c E := by
  induction E using Finset.strongInduction with
  | _ E IH =>
    rcases E.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => ⟨0, by omega⟩,
        fun v f₁ _ f₂ _ h₁E _ _ _ => absurd h₁E (Finset.notMem_empty _)⟩
    obtain ⟨e, he⟩ := hne
    -- destructure the chosen edge before anything depends on it
    revert he
    induction e using Sym2.ind with
    | _ u v =>
    intro he
    obtain ⟨c', hc'⟩ := IH (E.erase s(u, v)) (Finset.erase_ssubset he)
    by_cases hadj : G.Adj u v
    · -- the two endpoint fibers of s(u,v), each of size ≤ s, contain s(u,v)
      have hmemu : s(u, v) ∈ {f ∈ G.incidenceFinset u | ix u f = ix u s(u, v)} :=
        mem_filter.mpr
          ⟨mem_incFinset.mpr (G.mk'_mem_incidenceSet_left_iff.mpr hadj), rfl⟩
      have hmemv : s(u, v) ∈ {f ∈ G.incidenceFinset v | ix v f = ix v s(u, v)} :=
        mem_filter.mpr
          ⟨mem_incFinset.mpr (G.mk'_mem_incidenceSet_right_iff.mpr hadj), rfl⟩
      -- the conflict set: already-colored edges sharing a fiber with s(u,v)
      set B : Finset (Sym2 V) :=
        {f ∈ E.erase s(u, v) |
          (f ∈ G.incidenceFinset u ∧ ix u f = ix u s(u, v)) ∨
          (f ∈ G.incidenceFinset v ∧ ix v f = ix v s(u, v))} with hBdef
      have hBcard : #B ≤ (s - 1) + (s - 1) := by
        have hsub : B ⊆
            ({f ∈ G.incidenceFinset u | ix u f = ix u s(u, v)}.erase s(u, v)) ∪
            ({f ∈ G.incidenceFinset v | ix v f = ix v s(u, v)}.erase s(u, v)) := by
          intro f hf
          rw [hBdef, mem_filter, Finset.mem_erase] at hf
          rcases hf.2 with ⟨hi, hx⟩ | ⟨hi, hx⟩
          · exact mem_union_left _
              (Finset.mem_erase.mpr ⟨hf.1.1, mem_filter.mpr ⟨hi, hx⟩⟩)
          · exact mem_union_right _
              (Finset.mem_erase.mpr ⟨hf.1.1, mem_filter.mpr ⟨hi, hx⟩⟩)
        calc #B ≤ _ := card_le_card hsub
          _ ≤ _ := card_union_le _ _
          _ ≤ (s - 1) + (s - 1) := by
              rw [card_erase_of_mem hmemu, card_erase_of_mem hmemv]
              have h1 := hsz u (ix u s(u, v))
              have h2 := hsz v (ix v s(u, v))
              omega
      -- a free color exists: ≤ 2s−2 forbidden colors among 2s−1
      have hfree : (Finset.univ \ B.image c').Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        have h1 := card_le_card hsub
        have h2 : #(B.image c') ≤ #B := card_image_le
        rw [card_univ, Fintype.card_fin] at h1
        omega
      obtain ⟨β, hβ⟩ := hfree
      rw [mem_sdiff] at hβ
      refine ⟨fun f => if f = s(u, v) then β else c' f, ?_⟩
      intro w f₁ hf₁ f₂ hf₂ h₁E h₂E hix hcol
      by_cases h₁e : f₁ = s(u, v) <;> by_cases h₂e : f₂ = s(u, v)
      · rw [h₁e, h₂e]
      · -- f₁ is the new edge: f₂ would be a conflict painted β — impossible
        exfalso
        subst h₁e
        have hw : w = u ∨ w = v :=
          (G.mk'_mem_incidenceSet_iff.mp (mem_incFinset.mp hf₁)).2
        have hf₂B : f₂ ∈ B := by
          rw [hBdef, mem_filter]
          refine ⟨Finset.mem_erase.mpr ⟨h₂e, h₂E⟩, ?_⟩
          rcases hw with rfl | rfl
          · exact Or.inl ⟨hf₂, hix.symm⟩
          · exact Or.inr ⟨hf₂, hix.symm⟩
        apply hβ.2
        have hcβ : β = c' f₂ := by simpa [h₂e] using hcol
        exact hcβ ▸ mem_image_of_mem c' hf₂B
      · -- symmetric: f₂ is the new edge
        exfalso
        subst h₂e
        have hw : w = u ∨ w = v :=
          (G.mk'_mem_incidenceSet_iff.mp (mem_incFinset.mp hf₂)).2
        have hf₁B : f₁ ∈ B := by
          rw [hBdef, mem_filter]
          refine ⟨Finset.mem_erase.mpr ⟨h₁e, h₁E⟩, ?_⟩
          rcases hw with rfl | rfl
          · exact Or.inl ⟨hf₁, hix⟩
          · exact Or.inr ⟨hf₁, hix⟩
        apply hβ.2
        have hcβ : β = c' f₁ := by simpa [h₁e] using hcol.symm
        exact hcβ ▸ mem_image_of_mem c' hf₁B
      · -- both old: defer to the inductive coloring
        have e₁ : (if f₁ = s(u, v) then β else c' f₁) = c' f₁ := if_neg h₁e
        have e₂ : (if f₂ = s(u, v) then β else c' f₂) = c' f₂ := if_neg h₂e
        exact hc' w f₁ hf₁ f₂ hf₂
          (Finset.mem_erase.mpr ⟨h₁e, h₁E⟩) (Finset.mem_erase.mpr ⟨h₂e, h₂E⟩)
          hix (by rw [← e₁, ← e₂]; exact hcol)
    · -- s(u,v) is not an edge: it meets no incidence set, reuse c'
      refine ⟨c', ?_⟩
      intro w f₁ hf₁ f₂ hf₂ h₁E h₂E hix hcol
      have hkey : ∀ f ∈ G.incidenceFinset w, f ≠ s(u, v) := by
        rintro f hf rfl
        exact hadj
          (G.mem_edgeSet.mp (G.incidenceSet_subset w (mem_incFinset.mp hf)))
      exact hc' w f₁ hf₁ f₂ hf₂
        (Finset.mem_erase.mpr ⟨hkey f₁ hf₁, h₁E⟩)
        (Finset.mem_erase.mpr ⟨hkey f₂ hf₂, h₂E⟩) hix hcol

/-- **Greedy rainbow coloring**: 2s−1 colors always admit a rainbow coloring
when every group has ≤ s members — the greedy substitute for the Vizing
`proof_wanted rainbow_of_groupSizes` (whose s+1 stays open). -/
theorem rainbow_of_groupSizes_greedy (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (ix : V → Sym2 V → ℕ) (hsz : GroupSizesLE G ix s) :
    ∃ c : Sym2 V → Fin (2 * s - 1), IsRainbow G ix c := by
  obtain ⟨c, hc⟩ := exists_rainbowOn s hs ix hsz G.edgeFinset
  exact ⟨c, isRainbow_of_isRainbowOn_edgeFinset hc⟩

omit [DecidableEq C] in
/-- Rainbowness pushes forward along injective recolorings. -/
lemma IsRainbow.comp {C' : Type*} {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) (g : C → C') (hg : Function.Injective g) :
    IsRainbow G ix (g ∘ c) :=
  fun v f₁ h₁ f₂ h₂ hix hcol => hrb v f₁ h₁ f₂ h₂ hix (hg hcol)

/-- The `proof_wanted rainbow_of_groupSizes` EXACT (s+1)-shape holds for
s ≤ 2 with no Vizing: there 2s−1 ≤ s+1, so the greedy coloring embeds. -/
theorem rainbow_of_groupSizes_le_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : ℕ) (hs : 1 ≤ s) (hs2 : s ≤ 2) (ix : V → Sym2 V → ℕ)
    (hsz : GroupSizesLE G ix s) :
    ∃ c : Sym2 V → Fin (s + 1), IsRainbow G ix c := by
  obtain ⟨c, hc⟩ := rainbow_of_groupSizes_greedy G s hs ix hsz
  exact ⟨Fin.castLE (by omega) ∘ c, hc.comp _ (Fin.castLE_injective _)⟩

/-- **Unconditional Master-Theorem corollary (greedy form)**: every graph
all of whose edges satisfy CRIT_s is admissible and strong-majority
(2s−1)-colorable — Maj′(G) ≤ 2s−1 on CRIT_s.  Both existence inputs on
THIS (2s−1)-color route are discharged (`exists_even_grouping` +
`rainbow_of_groupSizes_greedy` through `master_coloring`); the
`master_of_inputs` Vizing input proper is `Fin (s+1)` and stays open. -/
theorem strongMajority_greedy_of_crit (s : ℕ) (hs : 2 ≤ s)
    (hcrit : ∀ u v : V, G.Adj u v → Crit s (G.degree u) (G.degree v)) :
    Admissible G ∧ ∃ c : Sym2 V → Fin (2 * s - 1), IsStrongMajority G c := by
  obtain ⟨ix, hsz, hg⟩ := exists_even_grouping G s (by omega)
  obtain ⟨c, hrb⟩ := rainbow_of_groupSizes_greedy G s (by omega) ix hsz
  exact ⟨admissible_of_crit s hs hcrit, c, master_coloring s ix c hrb hg hcrit⟩

/-- The s = 3 instantiation, unconditional: a graph with no vertex of
degree 2 or 4 has a strong majority 5-coloring (Maj′(G) ≤ 5 on the
Corollary-A class; per ATTACK.md §35.42 the constant is NOT claimed novel —
the banked value is the machine-checked unconditional pipeline). -/
theorem strongMajority_five_of_no24
    (hdeg : ∀ v : V, G.degree v ≠ 2 ∧ G.degree v ≠ 4) :
    ∃ c : Sym2 V → Fin 5, IsStrongMajority G c :=
  (strongMajority_greedy_of_crit 3 (by omega) fun u v huv =>
    crit3_of_no24 ((G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩)
      ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩)
      (hdeg u).1 (hdeg u).2 (hdeg v).1 (hdeg v).2).2

end SMaj
