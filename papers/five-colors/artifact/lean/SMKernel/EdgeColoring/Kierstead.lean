/-
SMKernel/EdgeColoring/Kierstead.lean — the Kierstead 4-path configuration
and the campaign's statements of record.

SM kernel campaign (`problems/p5-strongmajority/KERNEL-CAMPAIGN.md` §1).
The theorem of record is Theorem A = Kostochka–Stiebitz (2006), TR
DMF-2006-10-003 Theorem 7.2(d) = SSTF *Graph Edge Coloring* Theorem 3.3(b),
UNCONDITIONAL (no degree guard; the guards in the literature attach only to
the elementarity clause, which this development never states or uses).
Proof route: `lenses/T2FRESHLOOK/ks_proof_reconstruction.md`
(RECONSTRUCTED-SOUND; repairs F-R1..F-R3 included in the formalization
targets).  The corollary of record is the four-broom exclusion.

Design notes:
* The 4-vertex configuration is pinned concretely (fields, no lists).  The
  general list-indexed Kierstead path needed for the Theorem 7.1 induction
  is deliberately NOT defined yet — it lands with tranche smk2, after the
  smk1 swap machinery is kernel-returned (charter §4, riskiest item).
* Statements are palette-generalized: colorings take values in `Fin n` with
  `Δ(G) ≤ n` and `¬G.EdgeColorable n`.  At `n = Δ` this is the literature
  statement; for `n > Δ` it is (by the same proof) true and, post-Vizing,
  vacuous.  No Vizing anywhere.
-/
import SMKernel.EdgeColoring.Kempe

namespace SimpleGraph

variable {V : Type*}

/-- The short-Kierstead configuration: a path `v₀v₁v₂v₃` of distinct
vertices, a proper `n`-edge-coloring `c` of `G − v₀v₁`, and the two
Kierstead color conditions (handle + tail).  Missing sets are those of the
deletion graph `G − v₀v₁`. -/
structure IsShortKiersteadConfig [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) (c : Sym2 V → Fin n)
    (v0 v1 v2 v3 : V) : Prop where
  ne01 : v0 ≠ v1
  ne02 : v0 ≠ v2
  ne03 : v0 ≠ v3
  ne12 : v1 ≠ v2
  ne13 : v1 ≠ v3
  ne23 : v2 ≠ v3
  adj01 : G.Adj v0 v1
  adj12 : G.Adj v1 v2
  adj23 : G.Adj v2 v3
  proper : (G.deleteEdges {s(v0, v1)}).IsProperEdgeColoring c
  handle : c s(v1, v2) ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v0
  tail : c s(v2, v3) ∈ (G.deleteEdges {s(v0, v1)}).missingColors c v0 ∪
    (G.deleteEdges {s(v0, v1)}).missingColors c v1

/-- **Theorem A, statement of record** (Kostochka–Stiebitz 2006; TR Thm
7.2(d) = SSTF Thm 3.3(b), unconditional): in any short-Kierstead
configuration on a non-`n`-edge-colorable graph with `Δ(G) ≤ n`,
`|φ̄(v₃) ∩ (φ̄(v₀) ∪ φ̄(v₁))| ≤ 1`.

This `Prop` is the pinned formalization target; the theorem proving it
arrives via the smk1–smk3 payload tranches (charter §4). -/
def ShortKiersteadStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (c : Sym2 V → Fin n) (v0 v1 v2 v3 : V),
    G.maxDegree ≤ n →
    ¬G.EdgeColorable n →
    IsShortKiersteadConfig G n c v0 v1 v2 v3 →
    ((G.deleteEdges {s(v0, v1)}).missingColors c v3 ∩
      ((G.deleteEdges {s(v0, v1)}).missingColors c v0 ∪
        (G.deleteEdges {s(v0, v1)}).missingColors c v1)).card ≤ 1

/-- **Corollary B, statement of record** (four-broom exclusion, the sharp
`Δ = 4` case): no simple 4-edge-critical graph contains a path `z–x–y–t` of
distinct vertices with degrees `(2, 4, 4, 2)`.  "4-edge-critical" is pinned
as: `Δ(G) = 4`, `G` not 4-edge-colorable, every edge deletion
4-edge-colorable. -/
def FourBroomExclusionStatement : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (z x y t : V),
    G.maxDegree = 4 →
    ¬G.EdgeColorable 4 →
    (∀ e ∈ G.edgeSet, (G.deleteEdges {e}).EdgeColorable 4) →
    G.Adj z x → G.Adj x y → G.Adj y t →
    z ≠ x → z ≠ y → z ≠ t → x ≠ y → x ≠ t → y ≠ t →
    ¬(G.degree z = 2 ∧ G.degree x = 4 ∧ G.degree y = 4 ∧ G.degree t = 2)

/-! ### Reading-kit validation demos: the configuration is REAL

`C₅` (class two, every edge critical) carries a genuine short-Kierstead
configuration, and the theorem's conclusion holds on it — all pinned by
`decide`.  This certifies the hypothesis bundle is satisfiable exactly as
formalized (no vacuous statement of record). -/

section Demos

set_option maxRecDepth 8000

/-- The 5-cycle `0–1–2–3–4–0`. -/
private def C5 : SimpleGraph (Fin 5) where
  Adj x y := y = x + 1 ∨ x = y + 1
  symm := fun _ _ h => h.symm
  loopless := ⟨by decide⟩

private instance : DecidableRel C5.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- A proper 2-edge-coloring of `C₅ − s(0,1)` (the path `1‑2‑3‑4‑0`). -/
private def c5col : Sym2 (Fin 5) → Fin 2 := fun e =>
  if e = s(1, 2) ∨ e = s(3, 4) then 0 else 1

-- C₅ is class two with Δ = 2: an odd cycle is not 2-edge-colorable (the
-- alternation argument, walked around the cycle; `Fin 2` forces each
-- next edge color, and the cycle closes on a clash).
private lemma c5_not_edgeColorable_two : ¬C5.EdgeColorable 2 := by
  rintro ⟨c, hc⟩
  have swap : ∀ a b : Fin 5, c s(a, b) = c s(b, a) := fun a b => by
    rw [Sym2.eq_swap]
  have key : ∀ a b d : Fin 2, a ≠ b → b ≠ d → a = d := by decide
  have h1 : c s(1, 0) ≠ c s(1, 2) := hc (by decide) (by decide) (by decide)
  have h2 : c s(2, 1) ≠ c s(2, 3) := hc (by decide) (by decide) (by decide)
  have h3 : c s(3, 2) ≠ c s(3, 4) := hc (by decide) (by decide) (by decide)
  have h4 : c s(4, 3) ≠ c s(4, 0) := hc (by decide) (by decide) (by decide)
  have h0 : c s(0, 4) ≠ c s(0, 1) := hc (by decide) (by decide) (by decide)
  rw [swap 1 0] at h1                     -- c s(0,1) ≠ c s(1,2)
  rw [swap 2 1] at h2                     -- c s(1,2) ≠ c s(2,3)
  rw [swap 3 2] at h3                     -- c s(2,3) ≠ c s(3,4)
  rw [swap 4 3] at h4                     -- c s(3,4) ≠ c s(4,0)
  rw [swap 0 4] at h0                     -- c s(4,0) ≠ c s(0,1)
  -- alternation: c s(0,1) = c s(2,3) = c s(4,0), clashing with h0
  have e1 : c s(0, 1) = c s(2, 3) := key _ _ _ h1 h2
  have e2 : c s(2, 3) = c s(4, 0) := key _ _ _ h3 h4
  exact h0 (e1.trans e2).symm

example : C5.maxDegree = 2 := by decide

-- … and s(0,1) is a critical edge, witnessed through the pinned definition.
example : C5.IsCriticalEdge 2 s(0, 1) :=
  ⟨by decide, c5_not_edgeColorable_two, ⟨c5col, by decide⟩⟩

-- (0, 1, 2, 3) is a short-Kierstead configuration for c5col:
example : IsShortKiersteadConfig C5 2 c5col 0 1 2 3 where
  ne01 := by decide
  ne02 := by decide
  ne03 := by decide
  ne12 := by decide
  ne13 := by decide
  ne23 := by decide
  adj01 := by decide
  adj12 := by decide
  adj23 := by decide
  proper := by decide
  handle := by decide
  tail := by decide

-- … and Theorem A's conclusion holds on it (here φ̄(v₃) = ∅, so the
-- intersection is empty):
example : ((C5.deleteEdges {s(0, 1)}).missingColors c5col 3 ∩
    ((C5.deleteEdges {s(0, 1)}).missingColors c5col 0 ∪
      (C5.deleteEdges {s(0, 1)}).missingColors c5col 1)).card ≤ 1 := by
  decide

-- Semantics pin for the handle condition: φ̄(0) = {0} and c(s(1,2)) = 0.
example : (C5.deleteEdges {s(0, 1)}).missingColors c5col 0 = {0} := by decide
example : c5col s(1, 2) = 0 := by decide

end Demos

end SimpleGraph
