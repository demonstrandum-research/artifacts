/-
SMaj/Six/Final.lean — steps 3–5 of the `maj_le_six` assembly: the port
coloring, the fills, the global coloring, the `IsGlueColoring` bundle,
and the headline theorem `maj_le_six` (campaign C9, lens
C9L3-lean-assembly, 2026-07-08).

`SMaj/Six/Assembly.lean` (C8) banked the M-family and the Shannon member
coloring `exists_member_coloring`; `SMaj/Six/Partition.lean` (C8) the
slot calculus; `SMaj/Six/Fill.lean` (C3) the fill lemma;
`SMaj/Six/Construct.lean` (C6) the pure-cycle pattern;
`SMaj/Six/Glue.lean` (C5) the row dispatch `maj_le_six_of_glue`.  This
file composes them:

* `portColor` — the PORT-STAGE coloring: a junction-incident edge gets
  the Shannon color of its (unique) port member; defined per linkage
  class by slot so that the two ends of an l = 1 chain and the two
  ports of an l = 2 chain agree BY CONSTRUCTION (the whole-chain member
  is one term — the C8L3 risk note (ii) discharged as designed);
* `FxOf`/`FyOf` — the fill's saturated sets, computed from `portColor`
  at junction chain ends (`card_satSet_le_two` gives ≤ 2) and EMPTY at
  pendant ends (degree < 3; the `chain_end` field never looks there);
* `fillFun` — `isFill_exists` instantiated per chain class of length
  ≥ 3, ports pinned to the two half colors (distinct at every length
  ≥ 3 — the halves share the class's middle node, `col_inl_ne_inr`);
* `cycleFun` — `exists_cycle_distance2` per pure cycle;
* `glueColor` — the global coloring, per class by slot index
  (`List.idxOf` in the canonical piece's edge list, pinned by
  `edges_nodup`);
* the satSet agreement (`satSet_glueColor_eq`): the final and
  port-stage saturated sets agree at junctions, because every side
  edge there is a port (`eq_first_or_last`) and fills pin port slots
  to the port colors — the fill ↔ satSet circularity broken exactly as
  the C8L3 risk note (i) prescribed;
* the four `IsGlueColoring` fields (`glueColor_rainbow`,
  `groups_glueIx_le`, `glueColor_chain_end`, `glueColor_interior`) and
  `exists_isGlueColoring` — NO admissibility needed for the
  construction itself;
* **`maj_le_six`** — the T1 headline, now a THEOREM through
  `maj_le_six_of_glue` (the former `proof_wanted` in
  `SMaj/Six/Targets.lean` is deleted).

Machine pretest BEFORE proving (standing rule):
`lenses/C9L3-lean-assembly/pretest_final.py`, exit 0 — S-A..S-E pin
this file's definitions verbatim on 34,165 graphs (EXHAUSTIVE all
labeled graphs n ≤ 6, classics incl. a 9-arm star of chains and
subdivided K₄, 300 randoms n ≤ 14): fill sat-set cards ≤ 2 with the
pendant-∅ choice, p ≠ q at long chains, IsFill existence, satSet
agreement, all four bundle fields, strong majority on all 28,070
admissible corpus graphs, and the cycle wraparound arithmetic.
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting
import SMaj.Six.Fill
import SMaj.Six.Rows
import SMaj.Six.Glue
import SMaj.Six.ChainDecomp
import SMaj.Six.Partition
import SMaj.Six.Construct
import SMaj.Six.Assembly

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### List slot bookkeeping -/

/-- On a nodup list, the index of the value at a position is that
position — `idxOf` inverts `getElem`. -/
lemma idxOf_eq_of_getElem {α : Type*} [DecidableEq α] {l : List α}
    (hnd : l.Nodup) {i : ℕ} (hi : i < l.length) {a : α}
    (ha : l[i] = a) : l.idxOf a = i := by
  have hmem : a ∈ l := ha ▸ List.getElem_mem hi
  have hlt : l.idxOf a < l.length := List.idxOf_lt_length_of_mem hmem
  have h2 : l[l.idxOf a]'hlt = l[i]'hi := by
    rw [List.getElem_idxOf hlt, ha]
  exact hnd.getElem_inj_iff.mp h2

/-! ### Piece-level cycle transports (the `IsPiece` cycle lemmas need a
closed walk `G.Walk x x`; a `Piece` carries `G.Walk P.a P.b` with
`P.a = P.b` only propositionally) -/

namespace Piece

omit [DecidableEq V] in
/-- Pure-cycle pieces have at least 3 edges. -/
lemma three_le_length_of_cycle (P : Piece G) (h : P.IsCycle) :
    3 ≤ P.walk.length := by
  obtain ⟨hab, -⟩ := P.cycle_spec h
  obtain ⟨a, b, w, hp⟩ := P
  have hab' : a = b := hab
  subst hab'
  exact three_le_length_of_closed hp.trail hp.ne

/-- `IsPiece.other_edge_slot_of_cycle`, transported to a `Piece`. -/
lemma cycle_slot (P : Piece G) (hcyc : P.IsCycle) {i : ℕ}
    (hi : i < P.walk.edges.length) {v : V} (hv : v ∈ P.walk.edges[i])
    {f : Sym2 V} (hf : f ∈ P.walk.edges) (hvf : v ∈ f)
    (hne : f ≠ P.walk.edges[i]) :
    (v = P.walk.getVert i ∧
      ∃ h : (i + P.walk.edges.length - 1) % P.walk.edges.length <
          P.walk.edges.length,
        f = P.walk.edges[(i + P.walk.edges.length - 1) %
          P.walk.edges.length]) ∨
    (v = P.walk.getVert (i + 1) ∧
      ∃ h : (i + 1) % P.walk.edges.length < P.walk.edges.length,
        f = P.walk.edges[(i + 1) % P.walk.edges.length]) := by
  obtain ⟨hab, hall⟩ := P.cycle_spec hcyc
  obtain ⟨a, b, w, hp⟩ := P
  have hab' : a = b := hab
  subst hab'
  exact IsPiece.other_edge_slot_of_cycle hp hall hi hv hf hvf hne

end Piece

/-! ### The class of an edge -/

variable (G) in
/-- The linkage class of an edge, as an `EdgeClass` (the index type of
the canonical pieces). -/
noncomputable def edgeClassOf {e : Sym2 V} (he : e ∈ G.edgeSet) :
    EdgeClass G :=
  ⟨Quotient.mk (linkSetoid G) e, out_mem_edgeSet he⟩

variable (G) in
/-- An edge on a class's piece has that class (`pieceOf G e he` is
definitionally `classPiece G (edgeClassOf G he)`). -/
lemma edgeClassOf_eq {q : EdgeClass G} {e : Sym2 V} (he : e ∈ G.edgeSet)
    (hm : e ∈ (classPiece G q).walk.edges) : edgeClassOf G he = q :=
  Subtype.ext (classPiece_class_eq G hm)

/-! ### The Shannon member-coloring property, and the two half colors -/

variable (G) in
/-- The property `exists_member_coloring` delivers: distinct members
sharing an M-node get distinct colors. -/
def IsMemberColoring (col : Member G → Fin 6) : Prop :=
  ∀ m m' : Member G, m ≠ m' → ∀ a : MNode G,
    a ∈ mfam G m → a ∈ mfam G m' → col m ≠ col m'

/-- The two halves of a long chain get DISTINCT colors: they share the
class's middle node (this is the l = 3 port-distinctness input of the
fill, valid at every length ≥ 3). -/
lemma col_inl_ne_inr {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    col ⟨Sum.inl q, hc⟩ ≠ col ⟨Sum.inr q, hc, h3⟩ := by
  apply hcol _ _ (by simp) (Sum.inr q.1)
  · simp only [mfam, if_pos h3]
    exact Sym2.mem_mk_right _ _
  · simp only [mfam]
    exact Sym2.mem_mk_left _ _

/-! ### The port-stage coloring -/

/-- `IsCycle` is a decidable degree test. -/
instance (P : Piece G) : Decidable P.IsCycle :=
  inferInstanceAs (Decidable (G.degree P.a = 2))

/-- Port-stage class coloring: slot 0 (the first edge) gets the
whole/L-member color, later slots the R-member color on long chains;
short chains are monochromatic in their whole-member color.  Values on
cycle classes and on interior slots are garbage — no junction ever
reads them. -/
noncomputable def portClassColor (col : Member G → Fin 6)
    (q : EdgeClass G) (i : ℕ) : Fin 6 :=
  if hc : (classPiece G q).IsCycle then 0
  else if h3 : 3 ≤ (classPiece G q).walk.length then
    if i = 0 then col ⟨Sum.inl q, hc⟩ else col ⟨Sum.inr q, hc, h3⟩
  else col ⟨Sum.inl q, hc⟩

/-- **The port-stage coloring**: every edge is colored through its
linkage class by its slot in the canonical piece.  On junction-incident
edges (= ports, `eq_first_or_last`) this is the Shannon color of the
port member; the fill's saturated sets are computed from it, breaking
the fill ↔ satSet circularity. -/
noncomputable def portColor (col : Member G → Fin 6) (e : Sym2 V) :
    Fin 6 :=
  if he : e ∈ G.edgeSet then
    portClassColor col (edgeClassOf G he)
      ((classPiece G (edgeClassOf G he)).walk.edges.idxOf e)
  else 0

/-! ### The fill's saturated sets -/

/-- The start-end saturated set of a chain class: the port-stage satSet
at the start junction, EMPTY at a pendant/low-degree start (the
`chain_end` field requires degree ≥ 3, so the empty choice is never
consulted there). -/
noncomputable def FxOf (col : Member G → Fin 6) (q : EdgeClass G) :
    Finset (Fin 6) :=
  if 3 ≤ G.degree (classPiece G q).a then
    satSet G (portColor col) (classPiece G q).a (classPiece G q).walk.snd
  else ∅

/-- Mirror of `FxOf` at the far end. -/
noncomputable def FyOf (col : Member G → Fin 6) (q : EdgeClass G) :
    Finset (Fin 6) :=
  if 3 ≤ G.degree (classPiece G q).b then
    satSet G (portColor col) (classPiece G q).b
      (classPiece G q).walk.penultimate
  else ∅

lemma FxOf_card_le (col : Member G → Fin 6) (q : EdgeClass G) :
    #(FxOf col q) ≤ 2 := by
  unfold FxOf
  split_ifs with h
  · have hadj : G.Adj (classPiece G q).a (classPiece G q).walk.snd :=
      G.mem_edgeSet.mp ((classPiece G q).walk.edges_subset_edgeSet
        (classPiece G q).firstEdge_mem)
    exact card_satSet_le_two hadj (by omega)
  · simp

lemma FyOf_card_le (col : Member G → Fin 6) (q : EdgeClass G) :
    #(FyOf col q) ≤ 2 := by
  unfold FyOf
  split_ifs with h
  · have hadj : G.Adj (classPiece G q).walk.penultimate
        (classPiece G q).b :=
      G.mem_edgeSet.mp ((classPiece G q).walk.edges_subset_edgeSet
        (classPiece G q).lastEdge_mem)
    exact card_satSet_le_two hadj.symm (by omega)
  · simp

/-! ### The per-class colorings: fill, cycle pattern, and the composite -/

/-- **The fill of a long chain class** (`isFill_exists` instantiated):
ports pinned to the two half colors, saturated sets `FxOf`/`FyOf`. -/
noncomputable def fillFun {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (q : EdgeClass G)
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) : ℕ → Fin 6 :=
  (isFill_exists (by rw [Fintype.card_fin]; omega) h3
    (col ⟨Sum.inl q, hc⟩) (col ⟨Sum.inr q, hc, h3⟩)
    (fun _ => col_inl_ne_inr hcol hc h3)
    (FxOf_card_le col q) (FyOf_card_le col q)).choose

lemma fillFun_isFill {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (q : EdgeClass G)
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    IsFill (classPiece G q).walk.length (col ⟨Sum.inl q, hc⟩)
      (col ⟨Sum.inr q, hc, h3⟩) (FxOf col q) (FyOf col q)
      (fillFun hcol q hc h3) :=
  (isFill_exists (by rw [Fintype.card_fin]; omega) h3
    (col ⟨Sum.inl q, hc⟩) (col ⟨Sum.inr q, hc, h3⟩)
    (fun _ => col_inl_ne_inr hcol hc h3)
    (FxOf_card_le col q) (FyOf_card_le col q)).choose_spec

/-- **The pure-cycle pattern** (`exists_cycle_distance2`), indexed by
edge-list slots. -/
noncomputable def cycleFun (q : EdgeClass G)
    (hc : (classPiece G q).IsCycle) : ℕ → ℕ :=
  (exists_cycle_distance2 (classPiece G q).walk.edges.length
    (by rw [(classPiece G q).walk.length_edges]
        exact (classPiece G q).three_le_length_of_cycle hc)).choose

lemma cycleFun_spec (q : EdgeClass G) (hc : (classPiece G q).IsCycle) :
    (∀ i, cycleFun q hc i < 3) ∧
      ∀ i < (classPiece G q).walk.edges.length,
        cycleFun q hc i ≠
          cycleFun q hc ((i + 2) % (classPiece G q).walk.edges.length) :=
  (exists_cycle_distance2 (classPiece G q).walk.edges.length
    (by rw [(classPiece G q).walk.length_edges]
        exact (classPiece G q).three_le_length_of_cycle hc)).choose_spec

/-- The 3-color cycle pattern embedded in the 6-color palette. -/
def embed6 (n : ℕ) : Fin 6 := ⟨n % 6, Nat.mod_lt _ (by omega)⟩

lemma embed6_ne {a b : ℕ} (ha : a < 3) (hb : b < 3) (h : a ≠ b) :
    embed6 a ≠ embed6 b := by
  intro hab
  apply h
  have h' : a % 6 = b % 6 := congrArg Fin.val hab
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'

/-- The per-class slot coloring of the FINAL coloring: cycle pattern on
pure cycles, fill on long chains, monochromatic whole-member color on
short chains. -/
noncomputable def classColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (q : EdgeClass G) (i : ℕ) : Fin 6 :=
  if hc : (classPiece G q).IsCycle then embed6 (cycleFun q hc i)
  else if h3 : 3 ≤ (classPiece G q).walk.length then fillFun hcol q hc h3 i
  else col ⟨Sum.inl q, hc⟩

/-- **The global coloring** of the ≤ 6 construction. -/
noncomputable def glueColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) (e : Sym2 V) : Fin 6 :=
  if he : e ∈ G.edgeSet then
    classColor hcol (edgeClassOf G he)
      ((classPiece G (edgeClassOf G he)).walk.edges.idxOf e)
  else 0

/-! ### Access lemmas: colors through class and slot -/

lemma glueColor_eq_classColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G} {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hm : e ∈ (classPiece G q).walk.edges) :
    glueColor hcol e =
      classColor hcol q ((classPiece G q).walk.edges.idxOf e) := by
  unfold glueColor
  rw [dif_pos he, edgeClassOf_eq G he hm]

lemma portColor_eq_portClassColor (col : Member G → Fin 6)
    {q : EdgeClass G} {e : Sym2 V} (he : e ∈ G.edgeSet)
    (hm : e ∈ (classPiece G q).walk.edges) :
    portColor col e =
      portClassColor col q ((classPiece G q).walk.edges.idxOf e) := by
  unfold portColor
  rw [dif_pos he, edgeClassOf_eq G he hm]

lemma idxOf_firstEdge (P : Piece G) :
    P.walk.edges.idxOf P.firstEdge = 0 := by
  obtain ⟨h0, he⟩ := P.firstEdge_eq
  exact idxOf_eq_of_getElem P.piece.trail.edges_nodup h0 he

lemma idxOf_lastEdge (P : Piece G) :
    P.walk.edges.idxOf P.lastEdge = P.walk.edges.length - 1 := by
  obtain ⟨hl, he⟩ := P.lastEdge_eq
  exact idxOf_eq_of_getElem P.piece.trail.edges_nodup hl he

lemma classColor_of_short {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) (i : ℕ) :
    classColor hcol q i = col ⟨Sum.inl q, hc⟩ := by
  unfold classColor
  rw [dif_neg hc, dif_neg h3]

lemma classColor_of_fill {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) (i : ℕ) :
    classColor hcol q i = fillFun hcol q hc h3 i := by
  unfold classColor
  rw [dif_neg hc, dif_pos h3]

lemma classColor_of_cycle {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : (classPiece G q).IsCycle) (i : ℕ) :
    classColor hcol q i = embed6 (cycleFun q hc i) := by
  unfold classColor
  rw [dif_pos hc]

/-! ### Port values of the two colorings -/

lemma glueColor_firstEdge {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle) :
    glueColor hcol (classPiece G q).firstEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).firstEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [glueColor_eq_classColor hcol he hm, idxOf_firstEdge]
  by_cases h3 : 3 ≤ (classPiece G q).walk.length
  · rw [classColor_of_fill hcol hc h3]
    exact (fillFun_isFill hcol q hc h3).1
  · exact classColor_of_short hcol hc h3 0

lemma glueColor_lastEdge_long {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    glueColor hcol (classPiece G q).lastEdge =
      col ⟨Sum.inr q, hc, h3⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [glueColor_eq_classColor hcol he hm, idxOf_lastEdge,
    (classPiece G q).walk.length_edges, classColor_of_fill hcol hc h3]
  exact (fillFun_isFill hcol q hc h3).2.1

lemma glueColor_lastEdge_short {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) :
    glueColor hcol (classPiece G q).lastEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [glueColor_eq_classColor hcol he hm]
  exact classColor_of_short hcol hc h3 _

lemma portColor_firstEdge (col : Member G → Fin 6) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle) :
    portColor col (classPiece G q).firstEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).firstEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [portColor_eq_portClassColor col he hm, idxOf_firstEdge]
  unfold portClassColor
  rw [dif_neg hc]
  by_cases h3 : 3 ≤ (classPiece G q).walk.length
  · rw [dif_pos h3, if_pos rfl]
  · rw [dif_neg h3]

lemma portColor_lastEdge_long (col : Member G → Fin 6) {q : EdgeClass G}
    (hc : ¬(classPiece G q).IsCycle)
    (h3 : 3 ≤ (classPiece G q).walk.length) :
    portColor col (classPiece G q).lastEdge =
      col ⟨Sum.inr q, hc, h3⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [portColor_eq_portClassColor col he hm, idxOf_lastEdge]
  unfold portClassColor
  rw [dif_neg hc, dif_pos h3, if_neg]
  have := (classPiece G q).walk.length_edges
  omega

lemma portColor_lastEdge_short (col : Member G → Fin 6)
    {q : EdgeClass G} (hc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) :
    portColor col (classPiece G q).lastEdge = col ⟨Sum.inl q, hc⟩ := by
  have hm := (classPiece G q).lastEdge_mem
  have he := (classPiece G q).walk.edges_subset_edgeSet hm
  rw [portColor_eq_portClassColor col he hm]
  unfold portClassColor
  rw [dif_neg hc, dif_neg h3]

/-! ### Both colorings give a port its member's Shannon color -/

/-- The final color of a member's port edge is the member's Shannon
color (any member, through any group site it contains). -/
lemma glueColor_portEdge {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {v : V}
    {k : Fin (Fintype.card V + 1)} {m : Member G}
    (hm : (Sum.inl (v, k) : MNode G) ∈ mfam G m) :
    glueColor hcol (portEdge G (Sum.inl (v, k)) m) = col m := by
  obtain ⟨mv, hs⟩ := m
  rcases mv with q | q
  · by_cases hstart : (classPiece G q).startNode = Sum.inl (v, k)
    · simp only [portEdge, if_pos hstart]
      exact glueColor_firstEdge hcol hs
    · have h3 : ¬3 ≤ (classPiece G q).walk.length := by
        intro h3
        simp only [mfam, if_pos h3] at hm
        rcases Sym2.mem_iff.mp hm with h | h
        · exact hstart h.symm
        · exact absurd h (by simp)
      simp only [portEdge, if_neg hstart]
      exact glueColor_lastEdge_short hcol hs h3
  · simp only [portEdge]
    exact glueColor_lastEdge_long hcol hs.1 hs.2

/-- Port-stage mirror of `glueColor_portEdge`. -/
lemma portColor_portEdge (col : Member G → Fin 6) {v : V}
    {k : Fin (Fintype.card V + 1)} {m : Member G}
    (hm : (Sum.inl (v, k) : MNode G) ∈ mfam G m) :
    portColor col (portEdge G (Sum.inl (v, k)) m) = col m := by
  obtain ⟨mv, hs⟩ := m
  rcases mv with q | q
  · by_cases hstart : (classPiece G q).startNode = Sum.inl (v, k)
    · simp only [portEdge, if_pos hstart]
      exact portColor_firstEdge col hs
    · have h3 : ¬3 ≤ (classPiece G q).walk.length := by
        intro h3
        simp only [mfam, if_pos h3] at hm
        rcases Sym2.mem_iff.mp hm with h | h
        · exact hstart h.symm
        · exact absurd h (by simp)
      simp only [portEdge, if_neg hstart]
      exact portColor_lastEdge_short col hs h3
  · simp only [portEdge]
    exact portColor_lastEdge_long col hs.1 hs.2

/-! ### Junction agreement and the satSet agreement -/

/-- On junction-incident edges the final and port-stage colorings
agree (both give the port member's Shannon color). -/
lemma glueColor_eq_portColor {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {e : Sym2 V} (he : e ∈ G.edgeSet)
    {v : V} (hv : v ∈ e) (hdv : G.degree v ≠ 2) :
    glueColor hcol e = portColor col e := by
  obtain ⟨m, hm, hp⟩ := exists_port_member G hdv he hv
  have hm' : (Sum.inl (v, ⟨glueIx G v e, glueIx_lt v e⟩) : MNode G) ∈
      mfam G m := hm
  have hp' : portEdge G
      (Sum.inl (v, ⟨glueIx G v e, glueIx_lt v e⟩) : MNode G) m = e := hp
  calc glueColor hcol e
      = col m := by rw [← hp']; exact glueColor_portEdge hcol hm'
    _ = portColor col e := by rw [← hp']
                              exact (portColor_portEdge col hm').symm

/-- **The satSet agreement** (C8L3 risk note (i) discharged): the
saturated sets of the final and port-stage colorings agree at every
junction — every side edge there is junction-incident, where the two
colorings agree. -/
lemma satSet_glueColor_eq {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {x w : V} (hdx : G.degree x ≠ 2) :
    satSet G (glueColor hcol) x w = satSet G (portColor col) x w := by
  have hside : ∀ α : Fin 6,
      {f ∈ side G x w | glueColor hcol f = α} =
        {f ∈ side G x w | portColor col f = α} := by
    intro α
    apply filter_congr
    intro f hf
    have hf2 : f ∈ G.incidenceSet x := (mem_side.mp hf).2
    rw [glueColor_eq_portColor hcol hf2.1 hf2.2 hdx]
  unfold satSet
  apply filter_congr
  intro α _
  rw [hside α]

/-! ### The four bundle fields -/

/-- **Rainbow** (field 1): at junctions via port members + Shannon
distinctness at the shared group site; at degree ≤ 2 via singleton
groups. -/
lemma glueColor_rainbow {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) :
    IsRainbow G (glueIx G) (glueColor hcol) := by
  intro v f₁ h₁ f₂ h₂ hix hc
  by_cases hdeg : 3 ≤ G.degree v
  · have hdv : G.degree v ≠ 2 := by omega
    have hf₁ := mem_incFinset.mp h₁
    have hf₂ := mem_incFinset.mp h₂
    obtain ⟨m₁, hm₁, hp₁⟩ := exists_port_member G hdv hf₁.1 hf₁.2
    obtain ⟨m₂, hm₂, hp₂⟩ := exists_port_member G hdv hf₂.1 hf₂.2
    have hnd : nodeAt G v f₁ = nodeAt G v f₂ := by
      unfold nodeAt
      exact congrArg Sum.inl (congrArg (Prod.mk v) (Fin.ext hix))
    have hc₁ : glueColor hcol f₁ = col m₁ := by
      rw [← hp₁]; exact glueColor_portEdge hcol hm₁
    have hc₂ : glueColor hcol f₂ = col m₂ := by
      rw [← hp₂]; exact glueColor_portEdge hcol hm₂
    have hm12 : m₁ = m₂ := by
      by_contra hne
      exact hcol m₁ m₂ hne (nodeAt G v f₁) hm₁ (by rw [hnd]; exact hm₂)
        (by rw [← hc₁, ← hc₂]; exact hc)
    rw [← hp₁, ← hp₂, hnd, hm12]
  · exact glueIx_inj_low hdeg h₁ h₂ hix

/-- **Chain end** (field 3): short chains are monochromatic (left
disjunct); on long chains the inward edge sits at slot 1 (resp.
length − 2), where the fill avoids the port-stage satSet — equal to the
final satSet by the agreement lemma. -/
lemma glueColor_chain_end {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {x w y : V} (hxw : G.Adj x w)
    (hwy : G.Adj w y) (hxy : x ≠ y) (hdw : G.degree w = 2)
    (hdx3 : 3 ≤ G.degree x) :
    glueColor hcol s(x, w) = glueColor hcol s(w, y) ∨
      glueColor hcol s(w, y) ∉ satSet G (glueColor hcol) x w := by
  have he : s(x, w) ∈ G.edgeSet := G.mem_edgeSet.mpr hxw
  have hey : s(w, y) ∈ G.edgeSet := G.mem_edgeSet.mpr hwy
  set q : EdgeClass G := edgeClassOf G he with hq
  have hmem : s(x, w) ∈ (classPiece G q).walk.edges := mem_pieceOf G he
  have hdx2 : G.degree x ≠ 2 := by omega
  have hwsup : w ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.snd_mem_support_of_mem_edges hmem
  have hnc : ¬(classPiece G q).IsCycle := by
    intro hcyc
    have hxsup : x ∈ (classPiece G q).walk.support :=
      (classPiece G q).walk.fst_mem_support_of_mem_edges hmem
    exact hdx2 (((classPiece G q).cycle_spec hcyc).2 x hxsup)
  have hwy_mem : s(w, y) ∈ (classPiece G q).walk.edges :=
    (classPiece G q).piece.saturated_of_degree_two hwsup hdw _
      (mem_incFinset.mpr ⟨hwy, Sym2.mem_mk_left _ _⟩)
  by_cases h3 : 3 ≤ (classPiece G q).walk.length
  · right
    rcases (classPiece G q).piece.eq_first_or_last hmem
        (Sym2.mem_mk_left x w) hdx2 with ⟨hxa, hef⟩ | ⟨hxb, hel⟩
    · -- x is the start: the inward edge is slot 1, avoiding Fx
      have hw : w = (classPiece G q).walk.snd := by
        rcases Sym2.eq_iff.mp hef with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact h2
        · exact absurd (hxa.trans h2.symm) (G.ne_of_adj hxw)
      obtain ⟨h1len, he1⟩ := (classPiece G q).piece.edges_one_eq
        (by rw [← hxa]; exact hdx2) (by rw [← hw]; exact hdw)
        (by rw [← hw]; exact hwy) (by rw [← hxa]; exact Ne.symm hxy)
      have hidx : (classPiece G q).walk.edges.idxOf s(w, y) = 1 :=
        idxOf_eq_of_getElem (classPiece G q).piece.trail.edges_nodup
          h1len (by rw [he1, ← hw])
      have hcy : glueColor hcol s(w, y) = fillFun hcol q hnc h3 1 := by
        rw [glueColor_eq_classColor hcol hey hwy_mem, hidx,
          classColor_of_fill hcol hnc h3]
      rw [hcy, satSet_glueColor_eq hcol hdx2, hxa, hw]
      have hnotin := (fillFun_isFill hcol q hnc h3).2.2.2.1
      unfold FxOf at hnotin
      rwa [if_pos (hxa ▸ hdx3)] at hnotin
    · -- x is the end: the inward edge is slot length − 2, avoiding Fy
      have hw : w = (classPiece G q).walk.penultimate := by
        rcases Sym2.eq_iff.mp hel with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact absurd (hxb.trans h2.symm) (G.ne_of_adj hxw)
        · exact h2
      obtain ⟨hslen, hes⟩ :=
        (classPiece G q).piece.edges_length_sub_two_eq
          (by rw [← hxb]; exact hdx2) (by rw [← hw]; exact hdw)
          (by rw [← hw]; exact hwy) (by rw [← hxb]; exact Ne.symm hxy)
      have hidx : (classPiece G q).walk.edges.idxOf s(w, y) =
          (classPiece G q).walk.edges.length - 2 :=
        idxOf_eq_of_getElem (classPiece G q).piece.trail.edges_nodup
          hslen (by rw [hes, ← hw])
      have hcy : glueColor hcol s(w, y) =
          fillFun hcol q hnc h3 ((classPiece G q).walk.length - 2) := by
        rw [glueColor_eq_classColor hcol hey hwy_mem, hidx,
          (classPiece G q).walk.length_edges,
          classColor_of_fill hcol hnc h3]
      rw [hcy, satSet_glueColor_eq hcol hdx2, hxb, hw]
      have hnotin := (fillFun_isFill hcol q hnc h3).2.2.2.2
      unfold FyOf at hnotin
      rwa [if_pos (hxb ▸ hdx3)] at hnotin
  · -- short chain: monochromatic
    left
    rw [glueColor_eq_classColor hcol he hmem,
      glueColor_eq_classColor hcol hey hwy_mem,
      classColor_of_short hcol hnc h3 _, classColor_of_short hcol hnc h3 _]

/-- **Interior** (field 4): both sides of an all-degree-2 row are the
edges two slots apart on the same piece — distinct under the fill's
(F-a) on chains and under the distance-2 pattern on pure cycles. -/
lemma glueColor_interior {col : Member G → Fin 6}
    (hcol : IsMemberColoring G col) {u v : V} (huv : G.Adj u v)
    (hdu : G.degree u = 2) (hdv : G.degree v = 2) {f : Sym2 V}
    (hf : f ∈ side G u v) {g : Sym2 V} (hg : g ∈ side G v u) :
    glueColor hcol f ≠ glueColor hcol g := by
  have he : s(u, v) ∈ G.edgeSet := G.mem_edgeSet.mpr huv
  set q : EdgeClass G := edgeClassOf G he with hq
  have hmem : s(u, v) ∈ (classPiece G q).walk.edges := mem_pieceOf G he
  have hfside := mem_side.mp hf
  have hgside := mem_side.mp hg
  have husup : u ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.fst_mem_support_of_mem_edges hmem
  have hvsup : v ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.snd_mem_support_of_mem_edges hmem
  have hfP : f ∈ (classPiece G q).walk.edges :=
    (classPiece G q).piece.saturated_of_degree_two husup hdu f
      (mem_incFinset.mpr hfside.2)
  have hgP : g ∈ (classPiece G q).walk.edges :=
    (classPiece G q).piece.saturated_of_degree_two hvsup hdv g
      (mem_incFinset.mpr hgside.2)
  have hfe : f ∈ G.edgeSet := hfside.2.1
  have hge : g ∈ G.edgeSet := hgside.2.1
  have hnd := (classPiece G q).piece.trail.edges_nodup
  have hi : (classPiece G q).walk.edges.idxOf s(u, v) <
      (classPiece G q).walk.edges.length :=
    List.idxOf_lt_length_of_mem hmem
  set i := (classPiece G q).walk.edges.idxOf s(u, v) with hidef
  have hei : (classPiece G q).walk.edges[i] = s(u, v) :=
    List.getElem_idxOf hi
  have heq : s(u, v) = s((classPiece G q).walk.getVert i,
      (classPiece G q).walk.getVert (i + 1)) := by
    rw [← hei]
    exact edges_getElem _ hi
  have hor := Sym2.eq_iff.mp heq
  have hgv_ne : (classPiece G q).walk.getVert i ≠
      (classPiece G q).walk.getVert (i + 1) := by
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact G.ne_of_adj huv
    · rw [← h1, ← h2]; exact (G.ne_of_adj huv).symm
  by_cases hcyc : (classPiece G q).IsCycle
  · -- pure cycle: the two sides are the previous and next modular slots
    have h3L : 3 ≤ (classPiece G q).walk.edges.length := by
      rw [(classPiece G q).walk.length_edges]
      exact (classPiece G q).three_le_length_of_cycle hcyc
    have hfslot := (classPiece G q).cycle_slot hcyc hi
      (by rw [hei]; exact Sym2.mem_mk_left u v) hfP hfside.2.2
      (by rw [hei]; exact hfside.1)
    have hgslot := (classPiece G q).cycle_slot hcyc hi
      (by rw [hei]; exact Sym2.mem_mk_right u v) hgP hgside.2.2
      (by rw [hei, Sym2.eq_swap]; exact hgside.1)
    have hspec := cycleFun_spec q hcyc
    have harith : ∀ j : ℕ,
        ((j + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length + 2) %
          (classPiece G q).walk.edges.length =
        (j + 1) % (classPiece G q).walk.edges.length := by
      intro j
      rw [Nat.mod_add_mod,
        show j + (classPiece G q).walk.edges.length - 1 + 2 =
          j + 1 + (classPiece G q).walk.edges.length by omega,
        Nat.add_mod_right]
    have hcolor : ∀ {h : Sym2 V} (hhP : h ∈ (classPiece G q).walk.edges)
        (hhe : h ∈ G.edgeSet) {j : ℕ}
        (hj : j < (classPiece G q).walk.edges.length)
        (hh : h = (classPiece G q).walk.edges[j]),
        glueColor hcol h = embed6 (cycleFun q hcyc j) := by
      intro h hhP hhe j hj hh
      rw [glueColor_eq_classColor hcol hhe hhP,
        idxOf_eq_of_getElem hnd hj hh.symm, classColor_of_cycle hcol hcyc]
    rcases hor with ⟨hu, hv'⟩ | ⟨hu, hv'⟩
    · -- u near, v far: f = previous slot, g = next slot
      obtain ⟨hj1, hf1⟩ : ∃ h : _, f = (classPiece G q).walk.edges[
          (i + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length] := by
        rcases hfslot with ⟨-, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hu.symm.trans hcontra) hgv_ne
      obtain ⟨hj2, hg1⟩ : ∃ h : _, g = (classPiece G q).walk.edges[
          (i + 1) % (classPiece G q).walk.edges.length] := by
        rcases hgslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hv'.symm.trans hcontra) hgv_ne.symm
        · exact hh
      rw [hcolor hfP hfe hj1 hf1, hcolor hgP hge hj2 hg1]
      apply embed6_ne (hspec.1 _) (hspec.1 _)
      have := hspec.2 ((i + (classPiece G q).walk.edges.length - 1) %
        (classPiece G q).walk.edges.length)
        (Nat.mod_lt _ (by omega))
      rwa [harith i] at this
    · -- u far, v near: f = next slot, g = previous slot
      obtain ⟨hj1, hf1⟩ : ∃ h : _, f = (classPiece G q).walk.edges[
          (i + 1) % (classPiece G q).walk.edges.length] := by
        rcases hfslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hu.symm.trans hcontra) hgv_ne.symm
        · exact hh
      obtain ⟨hj2, hg1⟩ : ∃ h : _, g = (classPiece G q).walk.edges[
          (i + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length] := by
        rcases hgslot with ⟨-, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hv'.symm.trans hcontra) hgv_ne
      rw [hcolor hfP hfe hj1 hf1, hcolor hgP hge hj2 hg1]
      apply embed6_ne (hspec.1 _) (hspec.1 _)
      have := hspec.2 ((i + (classPiece G q).walk.edges.length - 1) %
        (classPiece G q).walk.edges.length)
        (Nat.mod_lt _ (by omega))
      rw [harith i] at this
      exact (Ne.symm this)
  · -- chain: the two sides are slots i − 1 and i + 1, distinct by (F-a)
    have hends := (classPiece G q).chain_ends hcyc
    have hLe := (classPiece G q).walk.length_edges
    have hfslot := (classPiece G q).piece.other_edge_slot_of_chain
      hends.1 hends.2 hi (by rw [hei]; exact Sym2.mem_mk_left u v) hdu
      hfP hfside.2.2 (by rw [hei]; exact hfside.1)
    have hgslot := (classPiece G q).piece.other_edge_slot_of_chain
      hends.1 hends.2 hi (by rw [hei]; exact Sym2.mem_mk_right u v) hdv
      hgP hgside.2.2 (by rw [hei, Sym2.eq_swap]; exact hgside.1)
    have hcolor : ∀ {h : Sym2 V} (hhP : h ∈ (classPiece G q).walk.edges)
        (hhe : h ∈ G.edgeSet) {j : ℕ}
        (hj : j < (classPiece G q).walk.edges.length)
        (hh : h = (classPiece G q).walk.edges[j])
        (h3 : 3 ≤ (classPiece G q).walk.length),
        glueColor hcol h = fillFun hcol q hcyc h3 j := by
      intro h hhP hhe j hj hh h3
      rw [glueColor_eq_classColor hcol hhe hhP,
        idxOf_eq_of_getElem hnd hj hh.symm,
        classColor_of_fill hcol hcyc h3]
    rcases hor with ⟨hu, hv'⟩ | ⟨hu, hv'⟩
    · -- u near, v far
      have h0 : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        have hua : u = (classPiece G q).a := by
          rw [hu, hi0, Walk.getVert_zero]
        exact hends.1 (hua ▸ hdu)
      have hilen : i + 1 < (classPiece G q).walk.edges.length := by
        by_contra h
        have hieq : i + 1 = (classPiece G q).walk.length := by omega
        have hvb : v = (classPiece G q).b := by
          rw [hv', hieq, Walk.getVert_length]
        exact hends.2 (hvb ▸ hdv)
      have h3 : 3 ≤ (classPiece G q).walk.length := by omega
      obtain ⟨hj1, hf1⟩ : ∃ h : i - 1 <
          (classPiece G q).walk.edges.length,
          f = (classPiece G q).walk.edges[i - 1] := by
        rcases hfslot with ⟨-, -, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hu.symm.trans hcontra) hgv_ne
      obtain ⟨hj2, hg1⟩ : ∃ h : i + 1 <
          (classPiece G q).walk.edges.length,
          g = (classPiece G q).walk.edges[i + 1] := by
        rcases hgslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hv'.symm.trans hcontra) hgv_ne.symm
        · exact hh
      rw [hcolor hfP hfe hj1 hf1 h3, hcolor hgP hge hj2 hg1 h3]
      have hfa := (fillFun_isFill hcol q hcyc h3).2.2.1 (i - 1)
        (by omega)
      rwa [show i - 1 + 2 = i + 1 by omega] at hfa
    · -- u far, v near
      have h0 : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        have hva : v = (classPiece G q).a := by
          rw [hv', hi0, Walk.getVert_zero]
        exact hends.1 (hva ▸ hdv)
      have hilen : i + 1 < (classPiece G q).walk.edges.length := by
        by_contra h
        have hieq : i + 1 = (classPiece G q).walk.length := by omega
        have hub : u = (classPiece G q).b := by
          rw [hu, hieq, Walk.getVert_length]
        exact hends.2 (hub ▸ hdu)
      have h3 : 3 ≤ (classPiece G q).walk.length := by omega
      obtain ⟨hj1, hf1⟩ : ∃ h : i + 1 <
          (classPiece G q).walk.edges.length,
          f = (classPiece G q).walk.edges[i + 1] := by
        rcases hfslot with ⟨hcontra, -⟩ | ⟨-, hh⟩
        · exact absurd (hu.symm.trans hcontra) hgv_ne.symm
        · exact hh
      obtain ⟨hj2, hg1⟩ : ∃ h : i - 1 <
          (classPiece G q).walk.edges.length,
          g = (classPiece G q).walk.edges[i - 1] := by
        rcases hgslot with ⟨-, -, hh⟩ | ⟨hcontra, -⟩
        · exact hh
        · exact absurd (hv'.symm.trans hcontra) hgv_ne
      rw [hcolor hfP hfe hj1 hf1 h3, hcolor hgP hge hj2 hg1 h3]
      have hfa := (fillFun_isFill hcol q hcyc h3).2.2.1 (i - 1)
        (by omega)
      rw [show i - 1 + 2 = i + 1 by omega] at hfa
      exact (Ne.symm hfa)

/-! ### The construction theorem and the headline -/

/-- **The glue construction, complete** (steps 3–5 of the C6L3 step
map): EVERY graph — no admissibility needed — admits a 6-color glue
coloring on the glue grouping. -/
theorem exists_isGlueColoring (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (ix : V → Sym2 V → ℕ) (c : Sym2 V → Fin 6),
      IsGlueColoring G ix c := by
  obtain ⟨col, hcol⟩ := exists_member_coloring G
  have hcol' : IsMemberColoring G col := hcol
  refine ⟨glueIx G, glueColor hcol', ?_, ?_, ?_, ?_⟩
  · exact glueColor_rainbow hcol'
  · intro v hv
    exact groups_glueIx_le hv
  · intro x w y hxw hwy hxy hdw hdx3
    exact glueColor_chain_end hcol' hxw hwy hxy hdw hdx3
  · intro u v huv hdu hdv f hf g hg
    exact glueColor_interior hcol' huv hdu hdv hf hg

/-- **T1, strong form (the program headline) — THEOREM**: every
admissible graph has a strong majority 6-edge-coloring, `Maj′(G) ≤ 6`,
improving the published 8 (arXiv:2605.23828 Thm 12; ≤ 5 is
arXiv:2607.00212 — this formalization is the independent chain-glue
architecture).  Proof: the (G1)–(G5) construction
(`exists_isGlueColoring`) through the closed row dispatch
(`maj_le_six_of_glue`).  Zero open inputs; the former `proof_wanted`
(SMaj/Six/Targets.lean, campaigns C3–C8) is hereby discharged. -/
theorem maj_le_six (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G) :
    ∃ c : Sym2 V → Fin 6, IsStrongMajority G c :=
  maj_le_six_of_glue G hadm (exists_isGlueColoring G)

/-! ### Honest scope note

Banked here: the port/fill/cycle colorings, the satSet agreement, the
four `IsGlueColoring` fields, `exists_isGlueColoring`, and the headline
`maj_le_six` — steps 3–5 of the C6L3/C7L3/C8L3 handoff, completing the
T4 lift of the ≤ 6 theorem.  Still open elsewhere:
`rainbow_of_groupSizes` (SMaj/Master.lean, Vizing Δ ≤ 4 fan — the last
`proof_wanted` of the library, NOT on the `maj_le_six` path). -/

end SMaj
