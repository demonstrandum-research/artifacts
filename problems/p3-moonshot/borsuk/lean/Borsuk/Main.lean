/-
# Borsuk/Main.lean — the disproof of Conjecture 3 of arXiv:2508.20009

Top-level assembly.  This file only combines the theorems of the work-package
files; the whole development is sorry-free (see scripts/CheckAxioms.lean).

**Conjecture 3** (Brose, De Loera, Lopez-Campos, Torres, arXiv:2508.20009,
§4.2, verbatim): "Let `S ⊂ ℤ^d` be a bounded set. Then `β_ℤ(S) = 2^d` if and
only if `conv(S)` is unimodularly equivalent to a `d`-cube `[0,m]^d` for any
`m ∈ ℕ`."

**Refutation** (d = 2): for `S_A = {(0,0), (1,0), (0,1), (3,5)}`,

* `β_ℤ(S_A) = 4 = 2²`  — all six pairwise differences are primitive, so
  `diam_ℤ(S_A) = 1` and every Borsuk partition needs singleton parts
  (`Borsuk/WitnessA.lean`, via the gcd bridge of `Borsuk/SegmentGcd.lean`);
* `conv(S_A)` contains exactly `7` lattice points (`Borsuk/HullSeven.lean`);
* unimodular equivalence preserves the lattice-point count, and
  `|[0,m]² ∩ ℤ²| = (m+1)²` is a perfect square, never `7`
  (`Borsuk/Unimodular.lean`).

Hence `β_ℤ(S_A) = 2²` while `conv(S_A)` is unimodularly equivalent to no cube
`[0,m]²` — the "only if" direction of Conjecture 3 fails, so the conjecture is
false as stated.
-/
import Borsuk.WitnessA
import Borsuk.HullSeven
import Borsuk.Unimodular

namespace Borsuk

/-- **MAIN THEOREM (the witness-A kill).**  The bounded set
`S_A = {(0,0), (1,0), (0,1), (3,5)} ⊆ ℤ²` has lattice Borsuk number
`β_ℤ(S_A) = 4 = 2²`, yet its convex hull is unimodularly equivalent to no cube
`[0,m]²`, `m ∈ ℕ`.  This is the negation of (the `d = 2` instance of, hence of)
Conjecture 3 of arXiv:2508.20009. -/
theorem witnessA_kills_conjecture3 :
    betaZ SA = 4 ∧
      ∀ m : ℕ, ¬ UnimodEquiv (convexHull ℝ (toR '' (SA : Set Z2))) (cube m) :=
  ⟨betaZ_SA, fun m =>
    not_unimodEquiv_cube_of_latticeCount_seven latticeCount_hullSA m⟩

/-- The negation of Conjecture 3 in existential form: there is a bounded set
`S ⊆ ℤ²` with `β_ℤ(S) = 2²` whose hull is not unimodularly equivalent to any
square `[0,m]²`. -/
theorem conjecture3_counterexample :
    ∃ S : Finset Z2, betaZ S = 2 ^ 2 ∧
      ∀ m : ℕ, ¬ UnimodEquiv (convexHull ℝ (toR '' (S : Set Z2))) (cube m) :=
  ⟨SA, by rw [betaZ_SA]; norm_num, witnessA_kills_conjecture3.2⟩

/-- **Conjecture 3 of arXiv:2508.20009 is false** (its `d = 2` instance fails,
hence the conjecture, which asserts all dimensions, fails as stated). -/
theorem conjecture3_false : ¬ Conjecture3For2D := by
  intro hconj
  have h4 : betaZ SA = 2 ^ 2 := by rw [betaZ_SA]; norm_num
  obtain ⟨m, hm⟩ := (hconj SA).mp h4
  exact witnessA_kills_conjecture3.2 m hm

end Borsuk
