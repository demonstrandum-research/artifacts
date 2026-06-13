/- Axiom audit for the HullSeven work package.
Run: lake env lean scripts/CheckAxiomsHullSeven.lean
Expect: only propext, Classical.choice, Quot.sound — no sorryAx. -/
import Borsuk.HullSeven

#print axioms Borsuk.hullSA_subset_halfspaces
#print axioms Borsuk.hullSeven_subset_hullSA
#print axioms Borsuk.halfspace_lattice_enum
#print axioms Borsuk.mem_hullSA_iff
#print axioms Borsuk.latticeCount_hullSA
