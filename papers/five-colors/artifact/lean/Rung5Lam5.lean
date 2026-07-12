import Rung5Lam4

set_option maxRecDepth 8000

namespace SMaj.Synthesis

open SMaj

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- TARGET T1 (prerequisite, = Λ4, VERBATIM from synthesis.md §4). -/
theorem exists_isGlueColoring_five (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G) :
    ∃ (ix : V → Sym2 V → ℕ) (c : Sym2 V → Fin 5), IsGlueColoring G ix c := by
  exact SMaj.exists_isGlueColoring_five G hadm

/-- TARGET T2 (Λ5 — the frozen `maj_le_five` statement, verbatim body). -/
theorem maj_le_five (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G) :
    ∃ c : Sym2 V → Fin 5, IsStrongMajority G c := by
  exact maj_le_five_of_glue G hadm (exists_isGlueColoring_five G hadm)

#print axioms SMaj.Synthesis.maj_le_five

end SMaj.Synthesis
