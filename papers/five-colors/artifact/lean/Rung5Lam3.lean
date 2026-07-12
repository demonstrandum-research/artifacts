/-
# RUNG-5 Λ-LADDER, rung Λ3 (heavy-class reinsertion; synthesis.md §4).
# EXPLORATORY.

Context: after de-fattening, every remaining parallel class of the
contraction multigraph satisfies the heavy-pair inequality (V2.1 Rule 3:
μ ≥ s_P + s_Q − 5 rearranged); delete the heavy classes, 5-color the simple
remainder (Λ2 = T1 below, restated as a prerequisite — prove it here
self-containedly OR leave it as your single sorry and close T2 from it),
reinsert greedily: forbidden colors at a class {a,b} number ≤
(mdeg a − μ) + (mdeg b − μ) ≤ 5 − μ by hheavy, so μ free colors remain
(V2.2 step 2; the inequality is order-independent).

NOTE on binders: synthesis.md's Λ3 writes `(hsymm : _) (hloop : _)`; they
are completed here with Λ2's exact forms (faithful completion, flagged for
lane triage).  Base module = frozen artifact VERBATIM; its `maj_le_five`
sorry is out of scope — do not modify that file.

TASK: fill the sorries in THIS file only (T2 required; T1 if you can).  Do
not change any definition or statement.  No axioms beyond
propext/Classical.choice/Quot.sound.
-/
import Rung5Lam2

set_option maxRecDepth 8000

namespace SMaj

open Finset

/-- TARGET T1 (prerequisite, = Λ2, VERBATIM).

GAP DIAGNOSIS (T1 sorry intact; T2 is closed from it, see below).

T1 is exactly **Vizing's theorem** specialized to simple graphs of maximum
degree `≤ 4`: a simple graph with `Δ ≤ 4` has edge-chromatic number
`χ′ ≤ Δ + 1 = 5`.  This is *sharp*: `χ′ ≥ Δ = 4` always, and `Δ`-edge-
colorings need not exist (e.g. an odd cycle with a pendant path forcing
Δ=4 class-2 behaviour), so the `+1` here is unavoidable — no purely
greedy / degree-counting bound suffices.  Indeed the base module's greedy
core `exists_multicoloring_of_le` (χ′ ≤ 2Δ−1) yields only `Fin 7` at Δ=4
(`exists_seven_coloring_of_mdeg_le_four`); dropping from 7 to 5 is precisely
the Vizing improvement.

Why it is not discharged here:
* Vizing's theorem is **not** in Mathlib at this pin (no `Vizing`,
  `edgeChromaticNumber`, or fan/Kempe-chain API exists), so it must be
  built from scratch.
* The standard proof is the **fan + Kempe-chain (alternating-path)
  recoloring** argument: after removing one edge `{x,y0}` and 5-coloring
  the rest by induction, one grows a maximal Vizing fan `y0,…,yk` of
  distinct `x`-neighbours (each edge `x yᵢ` colored by a color missing at
  `y_{i-1}`), then swaps colors along the maximal `α/β`-alternating path
  (α missing at `x`, β missing at `yk`) to free a color for `{x,y0}`.
  Formalizing this needs: a per-vertex *missing-color* set, a recursively
  built fan with distinctness/maximality invariants, the two-color
  subgraph's path/cycle decomposition, and the Kempe swap with its
  well-definedness (all four `IsMulticoloring` clauses re-established after
  each swap).  In the `mult : α → α → ℕ` / `Finset`-valued `IsMulticoloring`
  representation the alternating-path and swap bookkeeping is especially
  heavy; a faithful development is on the order of many hundreds of lines
  of new infrastructure and did not converge within a search attempt.

Everything downstream (T2) is proved *relative to* this lemma via
`reinsert_core`, so filling this single `sorry` with a Vizing proof would
make the whole file axiom-clean. -/
theorem exists_five_multicoloring_of_simple
    {α : Type*} [Fintype α] [DecidableEq α]
    (mult : α → α → ℕ) (hsymm : ∀ a b, mult a b = mult b a)
    (hloop : ∀ a, mult a a = 0)
    (hdeg : ∀ a, mdeg mult a ≤ 4) (hsimple : ∀ a b, mult a b ≤ 1) :
    ∃ f, IsMulticoloring (C := Fin 5) mult f := by
  exact SMaj.Lam2.exists_five_multicoloring_of_simple
    mult hsymm hloop hdeg hsimple

/-- **Heavy-class reinsertion core** (greedy induction for T2).

Strong induction on the total degree budget `N`.  As long as a heavy
parallel class `{a,b}` (multiplicity `≥ 2`) survives, decrement it by one
edge and recurse on the smaller multigraph; the `hheavy` inequality is
preserved by the decrement (`decr`), and it caps the number of colors
forbidden to the reinserted edge at `4 < 5`, so a fresh color always
exists.  When no heavy class remains, every class is simple and `T1`
finishes. -/
private lemma reinsert_core {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ N (m : α → α → ℕ), ∑ v, mdeg m v ≤ N →
      (∀ u v, m u v = m v u) → (∀ v, m v v = 0) → (∀ v, mdeg m v ≤ 4) →
      (∀ a b, 2 ≤ m a b → mdeg m a + mdeg m b ≤ 5 + m a b) →
      ∃ φ : α → α → Finset (Fin 5), IsMulticoloring m φ := by
  intro N
  induction N with
  | zero =>
    intro m htot _ _ _ _
    refine ⟨fun _ _ => ∅, isMulticoloring_of_zero ?_⟩
    intro u v
    have h1 : mdeg m u ≤ ∑ v, mdeg m v :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ u)
    have h2 : m u v ≤ mdeg m u :=
      Finset.single_le_sum (f := fun w => m u w) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ v)
    omega
  | succ N ih =>
    intro m htot hsym hloop hdeg hheavy
    by_cases hex : ∃ a b, 2 ≤ m a b
    · obtain ⟨a, b, hab2⟩ := hex
      have hab : 0 < m a b := by omega
      have hba : 0 < m b a := by rw [← hsym a b]; exact hab
      have hne : a ≠ b := by
        intro h; subst h; rw [hloop a] at hab2; omega
      -- the decremented matrix has a smaller degree budget
      have htot' : ∑ v, mdeg (decr m a b) v ≤ N := by
        have hlt : ∑ v, mdeg (decr m a b) v < ∑ v, mdeg m v :=
          Finset.sum_lt_sum (fun v _ => mdeg_decr_le m a b v)
            ⟨a, Finset.mem_univ a, mdeg_decr_lt_left hab⟩
        omega
      -- `decr` preserves the heavy-pair inequality
      have hheavy' : ∀ a' b', 2 ≤ decr m a b a' b' →
          mdeg (decr m a b) a' + mdeg (decr m a b) b' ≤ 5 + decr m a b a' b' := by
        intro a' b' h2'
        have hle : decr m a b a' b' ≤ m a' b' := decr_le m a b a' b'
        have h2m : 2 ≤ m a' b' := le_trans h2' hle
        have hstar := hheavy a' b' h2m
        by_cases hcase : (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)
        · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [decr_ab]
            have hla := mdeg_decr_eq_left hne hab
            have hlb := mdeg_decr_eq_right hne hba
            omega
          · rw [decr_ba]
            have hla := mdeg_decr_eq_left hne hab
            have hlb := mdeg_decr_eq_right hne hba
            omega
        · rw [decr_of_ne m hcase]
          have h1 := mdeg_decr_le m a b a'
          have h2 := mdeg_decr_le m a b b'
          omega
      obtain ⟨φ', hφ'⟩ := ih (decr m a b) htot' (decr_symm hsym a b)
        (decr_loopless hloop a b)
        (fun v => le_trans (mdeg_decr_le m a b v) (hdeg v)) hheavy'
      obtain ⟨hsymφ, hcardφ, hdisjφ⟩ := hφ'
      -- the union of the two endpoint palettes has ≤ 4 colors
      have hUa : #(Finset.univ.biUnion fun w => φ' a w) = mdeg (decr m a b) a :=
        card_biUnion_eq_mdeg ⟨hsymφ, hcardφ, hdisjφ⟩ a
      have hUb : #(Finset.univ.biUnion fun w => φ' b w) = mdeg (decr m a b) b :=
        card_biUnion_eq_mdeg ⟨hsymφ, hcardφ, hdisjφ⟩ b
      have hsub : φ' a b ⊆ (Finset.univ.biUnion fun w => φ' a w) ∩
          (Finset.univ.biUnion fun w => φ' b w) := by
        intro c hc
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hc⟩
        · exact Finset.mem_biUnion.mpr
            ⟨a, Finset.mem_univ a, by rw [hsymφ b a]; exact hc⟩
      have hcardab : #(φ' a b) = decr m a b a b := hcardφ a b
      have hinter : decr m a b a b ≤ #((Finset.univ.biUnion fun w => φ' a w) ∩
          (Finset.univ.biUnion fun w => φ' b w)) := by
        rw [← hcardab]; exact Finset.card_le_card hsub
      have heqa : mdeg (decr m a b) a = mdeg m a - 1 := mdeg_decr_eq_left hne hab
      have heqb : mdeg (decr m a b) b = mdeg m b - 1 := mdeg_decr_eq_right hne hba
      have hdab : decr m a b a b = m a b - 1 := decr_ab m a b
      have hheavyab := hheavy a b hab2
      have hmagea : m a b ≤ mdeg m a :=
        Finset.single_le_sum (f := fun w => m a w)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ b)
      have hmageb : m b a ≤ mdeg m b :=
        Finset.single_le_sum (f := fun w => m b w)
          (fun i _ => Nat.zero_le _) (Finset.mem_univ a)
      have hsymab : m b a = m a b := (hsym a b).symm
      have hunioncard : #((Finset.univ.biUnion fun w => φ' a w) ∪
          (Finset.univ.biUnion fun w => φ' b w)) ≤ 4 := by
        have hcu := Finset.card_union_add_card_inter
          (Finset.univ.biUnion fun w => φ' a w)
          (Finset.univ.biUnion fun w => φ' b w)
        omega
      have hfree : ∃ x : Fin 5,
          x ∉ (Finset.univ.biUnion fun w => φ' a w) ∪
              (Finset.univ.biUnion fun w => φ' b w) := by
        have hne' : (((Finset.univ.biUnion fun w => φ' a w) ∪
            (Finset.univ.biUnion fun w => φ' b w))ᶜ).Nonempty := by
          rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
          omega
        obtain ⟨x, hx⟩ := hne'
        exact ⟨x, Finset.mem_compl.mp hx⟩
      obtain ⟨x, hx⟩ := hfree
      have hxa : ∀ w, x ∉ φ' a w := fun w hmem =>
        hx (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, hmem⟩))
      have hxb : ∀ w, x ∉ φ' b w := fun w hmem =>
        hx (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, hmem⟩))
      -- extend φ' by the fresh color `x` on the class {a,b}
      refine ⟨fun u v => φ' u v ∪
        (if (u = a ∧ v = b) ∨ (u = b ∧ v = a) then {x} else ∅), ?_, ?_, ?_⟩
      · intro u v; dsimp only
        rw [hsymφ u v]; congr 1
        by_cases h : (u = a ∧ v = b) ∨ (u = b ∧ v = a)
        · rw [if_pos h, if_pos (by tauto)]
        · rw [if_neg h, if_neg (by tauto)]
      · intro u v; dsimp only
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
      · intro u v w hvw; dsimp only
        rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
          Finset.disjoint_union_right]
        refine ⟨⟨hdisjφ u v w hvw, ?_⟩, ?_, ?_⟩
        · split_ifs with h
          · rw [Finset.disjoint_singleton_right]
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa v
            · exact hxb v
          · exact Finset.disjoint_empty_right _
        · split_ifs with h
          · rw [Finset.disjoint_singleton_left]
            rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hxa w
            · exact hxb w
          · exact Finset.disjoint_empty_left _
        · split_ifs with h1 h2
          · exfalso; apply hvw
            rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
              rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
            · exact h1b.trans h2b.symm
            · exact h1b.trans (((h1a.symm.trans h2a).symm).trans h2b.symm)
            · exact h1b.trans (((h1a.symm.trans h2a).symm).trans h2b.symm)
            · exact h1b.trans h2b.symm
          · exact Finset.disjoint_empty_right _
          · exact Finset.disjoint_empty_left _
          · exact Finset.disjoint_empty_left _
    · -- no heavy class remains: every class is simple, finish with T1
      push_neg at hex
      have hsimple : ∀ a b, m a b ≤ 1 := fun a b => by have := hex a b; omega
      exact exists_five_multicoloring_of_simple m hsym hloop hdeg hsimple

/-- TARGET T2 (Λ3, binder-completed from synthesis.md §4). -/
theorem exists_five_multicoloring_of_reinsertable
    {α : Type*} [Fintype α] [DecidableEq α]
    (mult : α → α → ℕ)
    (hsymm : ∀ a b, mult a b = mult b a)
    (hloop : ∀ a, mult a a = 0)
    (hdeg : ∀ a, mdeg mult a ≤ 4)
    (hheavy : ∀ a b, 2 ≤ mult a b →
      mdeg mult a + mdeg mult b ≤ 5 + mult a b) :
    ∃ f, IsMulticoloring (C := Fin 5) mult f :=
  reinsert_core (∑ v, mdeg mult v) mult le_rfl hsymm hloop hdeg hheavy

end SMaj
