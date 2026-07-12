/-
SMKernel/EdgeColoring/KiersteadPath.lean — the general list-indexed
Kierstead path, elementarity, and reachability sets.

SM kernel campaign, tranche smk2 (charter §4, the pre-registered riskiest
item).  Definition shapes AUDITED before pinning (gpt-5.6-sol shape-audit
2026-07-11, thread 019f4fc0-b777-74b3-846c-031f485c8f74, against
`lenses/T2FRESHLOOK/ks_proof_reconstruction.md`): the `k2` field uses the
TR's DIRECT edge index (`i` means the TR's `e_i`, `2 ≤ i`), per the audit's
ACCEPT-WITH-EDIT repair; properness of the deletion coloring is
deliberately NOT a field (recoloring arguments re-establish path shape and
properness separately).

TR conventions rendered (TR DMF-2006-10-003, Section 7): a Kierstead path
K = (y0, e1, y1, ..., en, yn) has (K1) distinct vertices, e1 = the
uncolored edge, e_i ∈ E(y_{i-1}, y_i) — in a simple graph e_i = s(y_{i-1},
y_i) is forced, so (K1) reduces to nodup + chain — and (K2) for i ≥ 2,
φ(e_i) ∈ φ̄(y_j) for some j < i, missing sets in G − e1.

Audit trap list (binding for every smk2+ payload): missing sets ALWAYS in
`G.deleteEdges {s(v0,v1)}`; degree hypotheses ALWAYS in `G`; never evaluate
K2 on e₁ (the total coloring's value there is meaningless); prefix lemmas
must preserve the original deletion edge; never replace `∃ j < i` by a
fixed handle vertex or by `j ≤ i`.
-/
import SMKernel.EdgeColoring.KempeSwap
import SMKernel.EdgeColoring.Kierstead

namespace SimpleGraph

variable {V : Type*} {C : Type*}

/-- A *Kierstead path* for `G`, the uncolored edge `s(v0,v1)`, and the
deletion coloring `c`: the path `v0 :: v1 :: rest` has distinct vertices,
consecutive vertices adjacent in `G`, and every colored path edge `e_i`
(`2 ≤ i`) has its color missing at some earlier path vertex (missing sets
w.r.t. `G − v0v1`).  The index `i` is the TR's edge index: `e_i =
s(p[i-1], p[i])` on `p = v0 :: v1 :: rest`. -/
structure IsKiersteadPath [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [Fintype C] [DecidableEq C]
    (c : Sym2 V → C) (v0 v1 : V) (rest : List V) : Prop where
  nodup : (v0 :: v1 :: rest).Nodup
  chain : (v0 :: v1 :: rest).IsChain G.Adj
  k2 : ∀ i, 2 ≤ i → ∀ hi : i < (v0 :: v1 :: rest).length,
    ∃ j, ∃ _ : j < i,
      c s((v0 :: v1 :: rest)[i - 1]'(by omega),
          (v0 :: v1 :: rest)[i]'hi) ∈
        (G.deleteEdges {s(v0, v1)}).missingColors c
          ((v0 :: v1 :: rest)[j]'(by omega))

/-- A vertex list is *elementary* for `H, c`: missing sets pairwise
disjoint (TR "V(K) is elementary w.r.t. φ", with `H` the deletion
graph). -/
def IsElementaryList [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] [Fintype C] [DecidableEq C]
    (c : Sym2 V → C) (l : List V) : Prop :=
  l.Pairwise fun u v => Disjoint (H.missingColors c u) (H.missingColors c v)

/-- The reachability set of `v` in `H` as a Finset (the support of `v`'s
connected component); the canonical Kempe-closed set. -/
def reachFinset (H : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel H.Adj] (v : V) : Finset V :=
  Finset.univ.filter fun w => H.Reachable v w

lemma mem_reachFinset {H : SimpleGraph V} [Fintype V] [DecidableEq V]
    [DecidableRel H.Adj] {v w : V} :
    w ∈ H.reachFinset v ↔ H.Reachable v w := by
  simp [reachFinset]

lemma self_mem_reachFinset (H : SimpleGraph V) [Fintype V] [DecidableEq V]
    [DecidableRel H.Adj] (v : V) : v ∈ H.reachFinset v :=
  mem_reachFinset.mpr (Reachable.refl v)

/-! ### Kernel-returned lemmas (tranche smk2_kpath_v2, Aristotle 69461880,
audited 2026-07-11; KERNEL-ACCEPTED 3/4, the Theorem-7.1 stretch target
remains open) -/

/-- The statement-of-record configuration is exactly a proper deletion
coloring plus a length-4 Kierstead path (K2's `∃ j < i` collapses to the
handle/tail conditions because a color present at an incident vertex
cannot be missing there). -/
theorem isShortKiersteadConfig_iff_isKiersteadPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (c : Sym2 V → Fin n) (v0 v1 v2 v3 : V) :
    IsShortKiersteadConfig G n c v0 v1 v2 v3 ↔
      (G.deleteEdges {s(v0, v1)}).IsProperEdgeColoring c ∧
        IsKiersteadPath G c v0 v1 [v2, v3] := by
  constructor;
  · rintro ⟨ h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12 ⟩;
    refine' ⟨ h10, _, _, _ ⟩ <;> simp_all +decide;
    intro i hi hi'; interval_cases i <;> simp_all +decide ;
    · exact ⟨ 0, by decide, h11 ⟩;
    · cases' h12 with h12 h12 <;> [ exact ⟨ 0, by decide, h12 ⟩ ; exact ⟨ 1, by decide, h12 ⟩ ];
  · intro h;
    constructor;
    all_goals have := h.2.nodup; simp_all +decide [ List.nodup_cons ];
    · exact h.2.chain.rel_head;
    · have := h.2.chain; simp_all +decide ;
    · have := h.2.chain; simp_all +decide ;
    · have := h.2.k2 2 ( by decide ) ( by simp +decide );
      obtain ⟨ j, hj₁, hj₂ ⟩ := this; interval_cases j <;> simp_all +decide ;
      have := h.2.chain; simp_all +decide ;
      unfold SimpleGraph.missingColors at hj₂; simp_all +decide [ SimpleGraph.mem_presentColors_iff_exists_adj ] ;
      grind;
    · have := h.2.k2 3 ( by decide ) ( by simp +decide ) ; simp_all +decide ;
      rcases this with ⟨ j, hj, hj' ⟩ ; interval_cases j <;> simp_all +decide ;
      contrapose! hj';
      unfold SimpleGraph.missingColors; simp +decide [ SimpleGraph.mem_presentColors_iff_exists_adj ] ;
      exact ⟨ v3, h.2.chain |> fun h => by simp_all +decide [ List.isChain_cons_cons ], by tauto, by tauto, rfl ⟩

/-- Kierstead paths restrict to prefixes (the SAME deletion edge
`s(v0,v1)` — load-bearing). -/
theorem IsKiersteadPath.take
    {V C : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype C] [DecidableEq C]
    {c : Sym2 V → C} {v0 v1 : V} {rest : List V}
    (hp : IsKiersteadPath G c v0 v1 rest) (m : ℕ) :
    IsKiersteadPath G c v0 v1 (rest.take m) := by
  constructor;
  · have := hp.nodup;
    exact this.sublist ( by simp +decide [ List.take_sublist ] );
  · convert hp.chain.take ( m + 2 ) using 1;
  · intro i hi hi';
    obtain ⟨ j, hj ⟩ := hp.k2 i hi ( by
      grind );
    grind

/-! ### Reading-kit validation demos (small-n, kernel-checked)

The C₅ configuration of `Kierstead.lean` is a genuine general Kierstead
path; the definitions are pinned on it. -/

section Demos

set_option maxRecDepth 8000

/-- The 5-cycle `0–1–2–3–4–0` (local copy; the `Kierstead.lean` one is
file-private). -/
private def C5 : SimpleGraph (Fin 5) where
  Adj x y := y = x + 1 ∨ x = y + 1
  symm := fun _ _ h => h.symm
  loopless := ⟨by decide⟩

private instance : DecidableRel C5.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- A proper 2-edge-coloring of `C₅ − s(0,1)` (the path `1‑2‑3‑4‑0`). -/
private def c5col : Sym2 (Fin 5) → Fin 2 := fun e =>
  if e = s(1, 2) ∨ e = s(3, 4) then 0 else 1

-- (0, 1, [2, 3]) is a Kierstead path: e₂ = s(1,2) has color 0 ∈ φ̄(y₀),
-- e₃ = s(2,3) has color 1 ∈ φ̄(y₁).
example : IsKiersteadPath C5 c5col 0 1 [2, 3] where
  nodup := by decide
  chain := by decide
  k2 := by
    intro i h2 hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact ⟨0, by omega, by decide +revert⟩
    · exact ⟨1, by omega, by decide +revert⟩

-- Elementarity holds on it (φ̄ = {0}, {1}, ∅, ∅ at 0, 1, 2, 3).
example : IsElementaryList (C5.deleteEdges {s(0, 1)}) c5col [0, 1, 2, 3] := by
  unfold IsElementaryList
  decide

-- The (0,1)-Kempe subgraph of the deletion coloring: the whole colored
-- path is one component, so vertex 1 reaches vertex 0 …
example : ((C5.deleteEdges {s(0, 1)}).kempeGraph c5col 0 1).reachFinset 1 =
    Finset.univ := by
  unfold reachFinset; decide
-- … consistent with Lemma B (0 and 1 are linked in the (α,β)-subgraph for
-- α ∈ φ̄(0), β ∈ φ̄(1)); and the reach-set is Kempe-closed, as the smk2
-- closure target asserts in general.
example : (C5.deleteEdges {s(0, 1)}).IsKempeClosed c5col 0 1
    (((C5.deleteEdges {s(0, 1)}).kempeGraph c5col 0 1).reachFinset 1) := by
  unfold IsKempeClosed reachFinset; decide

end Demos

end SimpleGraph
