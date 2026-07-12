/-
SMaj/Six/Construct.lean — construction-half bricks for the (G1)–(G5) glue
(campaign C6, lens C6L3-lean-construction, 2026-06-13).

`maj_le_six_of_glue` (SMaj/Six/Glue.lean, campaign C5) reduced the
headline `maj_le_six` to the CONSTRUCTION half only: exhibit, for every
admissible G, a 6-color `IsGlueColoring` (chain decomposition →
contraction multigraph M → `shannon_six_of_maxDegree_four` → port
transport → `isFill_exists`).  This file banks the two construction-layer
steps that are independent of the chain decomposition itself:

* `shannon_six_indexed` — step (G3) in the form the glue assembly
  consumes: Shannon at Δ ≤ 4 repackaged from the multiplicity-matrix
  interface into an INDEXED-FAMILY interface.  The M-edges of the
  contraction multigraph arise as a family `t : ι → Sym2 N` (ι = the
  chains of length ≤ 2 plus the two halves of each chain of length ≥ 3;
  `t i` = the unordered pair of M-nodes joined: junction groups, kept
  degree-≤1 vertices, fresh middle nodes), and the transport wants ONE
  color per family member, distinct whenever two members share an
  M-node — exactly what properness of the M-coloring delivers:
  rainbowness within junction groups, l = 2 chains monochromatic, l = 3
  port distinctness via the shared middle node.  Internally: the
  multiplicity matrix of the family (`famMatrix`) satisfies Shannon's
  hypotheses (the degree transfer is `mdeg_famMatrix`, a fiberwise
  partition by the other endpoint), and Shannon's set-valued output is
  converted to a per-member color by a per-parallel-class bijection
  (`transportAt`: fiber ≃ color set via `Finset.equivFinOfCardEq`).

* `exists_cycle_distance2` — the pure-cycle part of step (G5): for every
  cycle length L ≥ 3 an explicit 3-color pattern with no two colors at
  cyclic index distance 2 equal (consumed as c(e_i) := f i along a pure
  cycle, discharging the `interior` field of `IsGlueColoring` there;
  3 ≤ 6 colors).  Formula: L = 3 ↦ (0,1,2); L ≥ 4 ↦ ⌊i/2⌋ mod 2 with the
  last two positions overridden to color 2.

Machine pretest BEFORE proving (standing rule):
`lenses/C6L3-lean-construction/pretest_construct.py`, exit 0 — P-A pins
the cycle formula verbatim (L = 3..4000, every constraint, exact); P-B
pins the indexed-Shannon proof shape (counting identity + per-fiber
bijection transport) on a corpus including the Shannon-tight fat
triangle, a 4-fold parallel class, middle-node chain shapes, and 600
random loopless Δ ≤ 4 multigraph families (524 with a degree-4-tight
node), the conclusion checked exhaustively over all index pairs.
-/
import Mathlib
import SMaj.Six.Targets

namespace SMaj

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The multiplicity matrix of an indexed family of M-edges -/

/-- The multiplicity matrix of a family `t` of unordered node pairs:
`famMatrix t a b` counts the family members equal to `s(a,b)`.  This is
the contraction multigraph M of the ≤ 6 construction when `t` enumerates
its edges (one entry per l ≤ 2 chain, two per l ≥ 3 chain). -/
def famMatrix (t : ι → Sym2 V) (a b : V) : ℕ :=
  #{i ∈ Finset.univ | t i = s(a, b)}

lemma famMatrix_symm (t : ι → Sym2 V) (a b : V) :
    famMatrix t a b = famMatrix t b a := by
  unfold famMatrix
  rw [show s(a, b) = s(b, a) from Sym2.eq_swap]

/-- A loopless family has zero diagonal multiplicities. -/
lemma famMatrix_diag (t : ι → Sym2 V) (hloop : ∀ i, ¬(t i).IsDiag) (a : V) :
    famMatrix t a a = 0 := by
  unfold famMatrix
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ h
  exact hloop i (by rw [h]; exact Sym2.mk_isDiag_iff.mpr rfl)

/-- **Degree transfer**: the matrix degree of a node equals the number of
family members containing it (fiberwise partition of those members by
their other endpoint; looplessness makes the other endpoint unique). -/
lemma mdeg_famMatrix (t : ι → Sym2 V) (hloop : ∀ i, ¬(t i).IsDiag) (a : V) :
    mdeg (famMatrix t) a = #{i ∈ Finset.univ | a ∈ t i} := by
  classical
  rw [mdeg, Finset.card_eq_sum_card_fiberwise
    (f := fun i => if h : a ∈ t i then Sym2.Mem.other' h else a)
    (t := Finset.univ) (fun x _ => mem_univ _)]
  apply Finset.sum_congr rfl
  intro u _
  unfold famMatrix
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hti
    have ha : a ∈ t i := by rw [hti]; exact Sym2.mem_mk_left a u
    refine ⟨ha, ?_⟩
    simp only [dif_pos ha]
    exact Sym2.congr_right.mp ((Sym2.other_spec' ha).trans hti)
  · rintro ⟨ha, hfu⟩
    simp only [dif_pos ha] at hfu
    rw [← hfu]
    exact (Sym2.other_spec' ha).symm

/-! ### Transport: from set-valued Shannon output to one color per edge -/

/-- Pick the color of family member `i` inside the parallel class `e`:
the fiber `{k | t k = e}` is bijected onto the color set `Φ e` (their
cardinalities agree), and `i`'s image is taken.  Stated at an explicit
`e` (with `h : t i = e`) so that injectivity lives at a FIXED parallel
class — no dependent rewriting in the consumers. -/
private noncomputable def transportAt (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 V) (i : ι) (h : t i = e) : Fin 6 :=
  ((Φ e).equivFin.symm (Finset.equivFinOfCardEq (hc e)
    ⟨i, mem_filter.mpr ⟨mem_univ i, h⟩⟩)).1

private lemma transportAt_mem (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 V) (i : ι) (h : t i = e) :
    transportAt t Φ hc e i h ∈ Φ e :=
  ((Φ e).equivFin.symm _).2

/-- Within one parallel class the transport is injective. -/
private lemma transportAt_inj (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 V) {i j : ι} (hi : t i = e) (hj : t j = e)
    (heq : transportAt t Φ hc e i hi = transportAt t Φ hc e j hj) :
    i = j := by
  unfold transportAt at heq
  have h1 := (Φ e).equivFin.symm.injective (Subtype.ext heq)
  have h2 := (Finset.equivFinOfCardEq (hc e)).injective h1
  exact Subtype.mk_eq_mk.mp h2

/-- The transport only depends on the parallel class as a value (proof
irrelevance across the membership certificate). -/
private lemma transportAt_congr (t : ι → Sym2 V)
    (Φ : Sym2 V → Finset (Fin 6))
    (hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (i : ι) {e e' : Sym2 V} (h : t i = e) (h' : t i = e')
    (hee : e = e') :
    transportAt t Φ hc e i h = transportAt t Φ hc e' i h' := by
  subst hee
  rfl

/-! ### Shannon at Δ ≤ 4, indexed-family form -/

/-- **Indexed Shannon transport** (the (G3) step in the form the glue
assembly consumes): every finite family `t : ι → Sym2 V` of loopless
M-edges with at most 4 members at each node admits a 6-coloring
`col : ι → Fin 6` of its MEMBERS such that any two distinct members
sharing a node receive distinct colors.  Specializing `ι` to the chains
(l ≤ 2) plus chain halves (l ≥ 3) of the ≤ 6 construction, `col` is the
per-chain/per-port color: distinctness at a junction-group node is the
`rainbow` field, and distinctness at a middle node is the l = 3 port
distinctness required by `isFill_exists`. -/
theorem shannon_six_indexed (t : ι → Sym2 V)
    (hloop : ∀ i, ¬(t i).IsDiag)
    (hdeg : ∀ a : V, #{i ∈ Finset.univ | a ∈ t i} ≤ 4) :
    ∃ col : ι → Fin 6, ∀ i j : ι, i ≠ j →
      ∀ a : V, a ∈ t i → a ∈ t j → col i ≠ col j := by
  classical
  obtain ⟨φ, hφs, hφc, hφd⟩ := shannon_six_of_maxDegree_four (famMatrix t)
    (famMatrix_symm t) (famMatrix_diag t hloop)
    (fun a => by
      show mdeg (famMatrix t) a ≤ 4
      rw [mdeg_famMatrix t hloop a]
      exact hdeg a)
  set Φ : Sym2 V → Finset (Fin 6) := Sym2.lift ⟨φ, hφs⟩ with hΦdef
  have hc : ∀ e : Sym2 V, #{k ∈ Finset.univ | t k = e} = #(Φ e) := by
    intro e
    induction e using Sym2.ind with
    | _ a b => rw [hΦdef, Sym2.lift_mk, hφc]; rfl
  refine ⟨fun i => transportAt t Φ hc (t i) i rfl, ?_⟩
  intro i j hij a hai haj hcol
  replace hcol : transportAt t Φ hc (t i) i rfl =
      transportAt t Φ hc (t j) j rfl := hcol
  by_cases he : t i = t j
  · -- same parallel class: the per-fiber bijection is injective
    rw [transportAt_congr t Φ hc j rfl he.symm he.symm] at hcol
    exact hij (transportAt_inj t Φ hc (t i) rfl he.symm hcol)
  · -- different parallel classes at a shared node: color sets disjoint
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hai
    obtain ⟨b', hb'⟩ := Sym2.mem_iff_exists.mp haj
    have hbb : b ≠ b' := fun hcontra => he (by rw [hb, hb', hcontra])
    have hdisj : Disjoint (Φ (t i)) (Φ (t j)) := by
      rw [hb, hb', hΦdef, Sym2.lift_mk, Sym2.lift_mk]
      exact hφd a b b' hbb
    have h1 := transportAt_mem t Φ hc (t i) i rfl
    have h2 := transportAt_mem t Φ hc (t j) j rfl
    rw [hcol] at h1
    exact (Finset.disjoint_left.mp hdisj h1) h2

/-! ### Pure-cycle distance-2 coloring (the (G5) pure-cycle step) -/

/-- **Pure-cycle distance-2 coloring**: for every cycle length L ≥ 3
there is a 3-color pattern `f` with `f i ≠ f ((i+2) % L)` for every
`i < L` — consumed as `c(e_i) := f i` along a pure cycle of the chain
decomposition, which discharges the `interior` field of
`IsGlueColoring` there (each side of an interior row is the edge two
steps away around the cycle).  Explicit formula, machine-pretested
verbatim (P-A): `L = 3 ↦ i % 3`, else `⌊i/2⌋ mod 2` overridden to `2`
at the last two positions. -/
theorem exists_cycle_distance2 (L : ℕ) (hL : 3 ≤ L) :
    ∃ f : ℕ → ℕ, (∀ i, f i < 3) ∧ ∀ i < L, f i ≠ f ((i + 2) % L) := by
  rcases Nat.lt_or_ge L 4 with hL3 | hL4
  · -- L = 3: the pure triangle; all three colors pairwise distinct
    have h3 : L = 3 := by omega
    subst h3
    exact ⟨fun i => i % 3, fun i => by show i % 3 < 3; omega, by decide⟩
  · -- L ≥ 4: ⌊i/2⌋ mod 2, last two positions overridden to 2
    refine ⟨fun i => if i = L - 2 ∨ i = L - 1 then 2 else (i / 2) % 2,
      fun i => ?_, fun i hi => ?_⟩
    · show (if i = L - 2 ∨ i = L - 1 then 2 else (i / 2) % 2) < 3
      split_ifs <;> omega
    · show (if i = L - 2 ∨ i = L - 1 then 2 else (i / 2) % 2) ≠
        (if (i + 2) % L = L - 2 ∨ (i + 2) % L = L - 1 then 2
         else ((i + 2) % L / 2) % 2)
      by_cases h2 : i = L - 2
      · -- wrap: (L−2) + 2 ≡ 0, and f 0 = 0 ≠ 2
        have hj : (i + 2) % L = 0 := by
          rw [show i + 2 = L by omega, Nat.mod_self]
        rw [if_pos (Or.inl h2), hj, if_neg (by omega)]
        omega
      · by_cases h1 : i = L - 1
        · -- wrap: (L−1) + 2 ≡ 1, and f 1 = 0 ≠ 2
          have hj : (i + 2) % L = 1 := by
            rw [show i + 2 = L + 1 by omega, Nat.add_mod_left,
              Nat.mod_eq_of_lt (by omega)]
          rw [if_pos (Or.inr h1), hj, if_neg (by omega)]
          omega
        · -- interior: no wrap, both positions ≤ L − 1
          have hj : (i + 2) % L = i + 2 := Nat.mod_eq_of_lt (by omega)
          rw [hj, if_neg (by omega)]
          by_cases hend : i + 2 = L - 2 ∨ i + 2 = L - 1
          · rw [if_pos hend]; omega
          · rw [if_neg hend]; omega

end SMaj
