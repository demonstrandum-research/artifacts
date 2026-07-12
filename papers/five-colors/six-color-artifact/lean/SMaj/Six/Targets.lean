/-
SMaj/Six/Targets.lean — case (b) rows (closed), Shannon at Δ = 4
(CLOSED, campaign C4), and the single named open obligation separating
the formalized core from the full unconditional T1 theorem
`Maj′(G) ≤ 6`:

1. `shannon_six_of_maxDegree_four` — Shannon's theorem at Δ = 4 for
   loopless multigraphs (χ′ ≤ ⌊3·4/2⌋ = 6), stated over a symmetric
   multiplicity matrix (mathlib has no multigraph edge-coloring theory:
   v4.30.0 and master both grep clean of Vizing/Shannon, checked
   2026-06-12; the `Graph α β` multigraph type has no degree API yet).
   **CLOSED (campaign C4, lens C4L3-lean-close, 2026-06-13)**: a THEOREM
   below, = `shannon_six_of_split_hypothesis` (`SMaj/Six/Shannon.lean`)
   applied to the closed Euler 2-split `exists_two_split`
   (`SMaj/Six/Euler.lean`, balanced orientations).  No open inputs.
2. `maj_le_six` — the headline: every admissible graph has a strong
   majority 6-edge-coloring (T1, strong form; proved on paper + machine,
   `lenses/L2-chain-grouping/WRITEUP.md`).  The remaining formal distance
   was the chain-decomposition glue (G1)–(G5); **its row-dispatch half is
   now CLOSED** (campaign C5, lens C5L3-lean-six, `SMaj/Six/Glue.lean`):
   `strongMajority_of_glue` dispatches every row of an admissible graph
   through `l1_row_le` / `twoChain_row_le` / `chainEnd_row_le` /
   `interior_row_le`, and `maj_le_six_of_glue` reduces this target to
   the construction half ONLY — exhibit, for every admissible G, a glue
   coloring (`IsGlueColoring`, 6 colors): build the contraction
   multigraph M from the chain decomposition, color it by
   `shannon_six_of_maxDegree_four`, transport to ports, fill interiors
   by `isFill_exists` (+ the pure-cycle construction).  No open external
   theorem input remains (and a fortiori at palette 7); what remains is
   construction formalization.

Lens C3L4-lean-six (campaign C3, T4), 2026-06-12; Shannon closure
lens C4L3-lean-close (campaign C4), 2026-06-13.
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Six.Arith
import SMaj.Six.Rows
import SMaj.Six.Fill
import SMaj.Six.Shannon
import SMaj.Six.Euler

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {C : Type*} [DecidableEq C]

/-- Case (b) of the ≤ 6 row analysis (l = 1 chains: junction–junction and
pendant rows): if neither endpoint has degree 2 and the coloring is rainbow
on a grouping with g ≤ ⌈d/4⌉ at both ends, the row is strong-majority
(Counting Lemma + R1/R2 via CRIT₄). -/
theorem l1_row_le {ix : V → Sym2 V → ℕ} {c : Sym2 V → C}
    (hrb : IsRainbow G ix c) {u v : V} (huv : G.Adj u v)
    (hdu : G.degree u ≠ 2) (hdv : G.degree v ≠ 2)
    (hgu : groups G ix u ≤ hfun 4 (G.degree u))
    (hgv : groups G ix v ≤ hfun 4 (G.degree v)) (α : C) :
    nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2 := by
  have hcrit : Crit 4 (G.degree u) (G.degree v) :=
    crit4_of_ne_two ((G.degree_pos_iff_exists_adj u).mpr ⟨v, huv⟩)
      ((G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩) hdu hdv
  calc nColor G c u v α
      ≤ groups G ix u + groups G ix v := counting_lemma hrb huv α
    _ ≤ hfun 4 (G.degree u) + hfun 4 (G.degree v) := Nat.add_le_add hgu hgv
    _ ≤ (G.degree u + G.degree v - 2) / 2 := hcrit

/-! ### The two named open obligations -/

/-- **Shannon's theorem at Δ = 4, CLOSED** (the (G3) step; formerly the
sole external mathematical input of the ≤ 6 proof — now a theorem with
no open inputs, campaign C4, lens C4L3-lean-close).  A loopless
multigraph is presented by its symmetric multiplicity matrix `m`
(m v v = 0); a proper 6-edge-coloring assigns each parallel class `{u,v}`
a set of `m u v` distinct colors (`φ u v`), classes at a common vertex
receiving disjoint sets.  Shannon 1949: χ′ ≤ ⌊3Δ/2⌋; at Δ ≤ 4 a 6-color
palette suffices.  Absent from mathlib v4.30.0 AND master (checked
2026-06-12).  Proof: `shannon_six_of_split_hypothesis`
(`SMaj/Six/Shannon.lean`) applied to the closed Euler 2-split
`exists_two_split` (`SMaj/Six/Euler.lean` — balanced orientations). -/
theorem shannon_six_of_maxDegree_four
    {V : Type*} [Fintype V] [DecidableEq V] (m : V → V → ℕ)
    (hsymm : ∀ u v, m u v = m v u) (hloop : ∀ v, m v v = 0)
    (hdeg : ∀ v, ∑ u, m v u ≤ 4) :
    ∃ φ : V → V → Finset (Fin 6),
      (∀ u v, φ u v = φ v u) ∧
      (∀ u v, #(φ u v) = m u v) ∧
      (∀ u v w, v ≠ w → Disjoint (φ u v) (φ u w)) :=
  shannon_six_of_split_hypothesis
    (fun M hs hl hd => exists_two_split M hs hl hd) m hsymm hloop hdeg

/- **T1, strong form (the program headline)**: every admissible graph has
a strong majority 6-edge-coloring — `Maj′(G) ≤ 6` for every admissible G.
Formerly the `proof_wanted maj_le_six` of this file (campaigns C3–C8);
**CLOSED (campaign C9, lens C9L3-lean-assembly, 2026-07-08)**: now the
THEOREM `SMaj.maj_le_six` in `SMaj/Six/Final.lean`, via the completed
(G1)–(G5) construction `exists_isGlueColoring` composed with
`maj_le_six_of_glue` (`SMaj/Six/Glue.lean`).  No obligation remains
here. -/

end SMaj
