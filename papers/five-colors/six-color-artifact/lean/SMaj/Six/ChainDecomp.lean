/-
SMaj/Six/ChainDecomp.lean — chain-decomposition existence: the one
remaining mathematical stone of the `maj_le_six` lift (campaign C7,
lens C7L3-lean-chaindecomp, 2026-06-13; step 1 of the C6L3 WRITEUP
handoff).

`maj_le_six_of_glue` (campaign C5) reduced the headline to the
construction half; `shannon_six_indexed` + `exists_cycle_distance2`
(campaign C6) banked its coloring layer.  What the assembly still
consumes from the graph itself is the CHAIN DECOMPOSITION: every edge
lies on a piece — a trail threaded through degree-2 internal vertices,
which is either
* a CHAIN: both end degrees ≠ 2 (junction/pendant ends; x = y gives a
  loop chain, necessarily of length ≥ 3 in a simple graph), or
* a PURE CYCLE: closed with EVERY support vertex of degree 2 (length
  ≥ 3 likewise).

This file proves that existence statement for EVERY graph (no
admissibility needed), kernel-grade:
* `IsPiece` — the certificate bundle (nonempty + trail + internal
  degrees 2 + the end dichotomy);
* `exists_piece` — through every edge there is a piece (the maximal
  threaded-trail walker: extend at any degree-2 end with an unused
  edge; the parity dichotomy `end_eq_start_of_saturated` shows a
  saturated degree-2 end can only be the start, so maximal pieces
  classify);
* `IsPiece.three_le_length` — closed pieces (loop chains AND pure
  cycles) have ≥ 3 edges.

Machine pretest BEFORE proving (standing rule):
`lenses/C7L3-lean-chaindecomp/pretest_chaindecomp.py`, exit 0, re-run
fresh this session — P-A pins the slot-counting identity on 27,214
arbitrary walks; P-B the parity dichotomy at a saturated degree-2 end
(the exact E(z) = 2k_z − 1 odd-vs-≥2 contradiction shape); P-C the
walker's chain/cycle classification through every edge of the
EXHAUSTIVE 33,866 labeled graphs n ≤ 6 (251,085 edge classifications)
plus classics (C₉, theta, subdivided K₄, loop chain, disjoint union,
P₆) and 400 randoms n ≤ 14; P-D/P-E the linkage-closure and greedy
partition facts (NOT yet formalized here — see the honest-scope note
at the end of the file).
-/
import Mathlib
import SMaj.Defs
import SMaj.Counting

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Support bookkeeping for reversal and tails -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The internal vertices (support minus the two end positions) of the
reverse walk are those of the walk, reversed. -/
private lemma internal_reverse {x z : V} (p : G.Walk x z) :
    p.reverse.support.tail.dropLast = p.support.tail.dropLast.reverse := by
  rw [Walk.support_reverse, List.tail_reverse, List.dropLast_reverse,
    List.tail_dropLast]

omit [DecidableEq V] in
/-- If a walk's internal vertices and its END vertex all have degree 2,
then every support vertex except possibly the start has degree 2. -/
private lemma deg_two_of_mem_tail :
    ∀ {x z : V} (p : G.Walk x z), G.degree z = 2 →
      (∀ v ∈ p.support.tail.dropLast, G.degree v = 2) →
      ∀ v ∈ p.support.tail, G.degree v = 2 := by
  intro x z p
  induction p with
  | nil =>
    intro _ _ v hv
    simp at hv
  | cons h q ih =>
    intro hdz hint v hv
    rw [Walk.support_cons, List.tail_cons] at hv
    rw [Walk.support_cons, List.tail_cons] at hint
    cases q with
    | nil =>
      rw [Walk.support_nil, List.mem_singleton] at hv
      exact hv ▸ hdz
    | cons h' q' =>
      rw [Walk.support_cons] at hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · apply hint
        rw [Walk.support_cons,
          List.dropLast_cons_of_ne_nil q'.support_ne_nil]
        exact List.mem_cons_self ..
      · refine ih hdz ?_ v ?_
        · intro u hu
          rw [Walk.support_cons, List.tail_cons] at hu
          apply hint
          rw [Walk.support_cons,
            List.dropLast_cons_of_ne_nil q'.support_ne_nil]
          exact List.mem_cons_of_mem _ hu
        · rw [Walk.support_cons, List.tail_cons]
          exact hv'

/-! ### The parity dichotomy at a saturated end (pretest P-B) -/

/-- **Parity dichotomy**: if a trail ends at a degree-2 vertex `z` both
of whose incident edges already lie on the trail, the trail is closed
(`z` is its start).  Pretest P-B pins the numeric shape: the number of
trail edges at `z` is odd (2k_z − 1) for an open end but saturation
forces it to be exactly deg z = 2. -/
theorem end_eq_start_of_saturated {x z : V} {p : G.Walk x z}
    (ht : p.IsTrail) (hdz : G.degree z = 2)
    (hsat : ∀ f ∈ G.incidenceFinset z, f ∈ p.edges) : z = x := by
  have hcount : (p.edges.countP fun e => z ∈ e) = 2 := by
    rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (ht.edges_nodup.filter _),
      List.toFinset_filter, ← hdz, ← card_incidenceFinset_eq_degree]
    congr 1
    ext f
    simp only [Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq,
      mem_incidenceFinset]
    constructor
    · rintro ⟨hf, hzf⟩
      exact ⟨p.edges_subset_edgeSet hf, hzf⟩
    · intro hf
      exact ⟨hsat f (mem_incFinset.mpr hf), hf.2⟩
  by_contra hne
  have heven : Even (p.edges.countP fun e => z ∈ e) := by
    rw [hcount]
    exact ⟨1, rfl⟩
  obtain ⟨-, hzz⟩ :=
    (ht.even_countP_edges_iff z).mp heven fun h => hne h.symm
  exact hzz rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- The trail-edge count at a vertex as a finset cardinality. -/
private lemma countP_edges_eq_card {x z : V} {p : G.Walk x z}
    (ht : p.IsTrail) (v : V) :
    (p.edges.countP fun e => v ∈ e) = #{f ∈ p.edges.toFinset | v ∈ f} := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (ht.edges_nodup.filter _),
    List.toFinset_filter]
  congr 1
  ext f
  simp [decide_eq_true_eq]

/-- The edges of a walk at a vertex `v` lie in `v`'s incidence finset. -/
private lemma filter_subset_incidence {x z : V} (p : G.Walk x z) (v : V) :
    {f ∈ p.edges.toFinset | v ∈ f} ⊆ G.incidenceFinset v := by
  intro f hf
  rw [Finset.mem_filter, List.mem_toFinset] at hf
  exact mem_incFinset.mpr ⟨p.edges_subset_edgeSet hf.1, hf.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every support vertex of a nonempty walk lies on one of its edges. -/
private lemma exists_edge_of_mem_support :
    ∀ {x z : V} (p : G.Walk x z), p.length ≠ 0 → ∀ v ∈ p.support,
      ∃ f ∈ p.edges, v ∈ f := by
  intro x z p
  induction p with
  | nil =>
    intro h
    simp at h
  | @cons a c d hadj q ih =>
    intro _ v hv
    rw [Walk.support_cons] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨s(v, c),
        by rw [Walk.edges_cons]; exact List.mem_cons_self ..,
        Sym2.mem_mk_left _ _⟩
    · cases q with
      | nil =>
        rw [Walk.support_nil, List.mem_singleton] at hv'
        subst hv'
        exact ⟨s(a, v),
          by rw [Walk.edges_cons]; exact List.mem_cons_self ..,
          Sym2.mem_mk_right _ _⟩
      | cons hadj' q' =>
        obtain ⟨f, hf, hvf⟩ := ih (by rw [Walk.length_cons]; omega) v hv'
        refine ⟨f, ?_, hvf⟩
        rw [Walk.edges_cons]
        exact List.mem_cons_of_mem _ hf

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every support vertex of a walk is the start, the end, or internal. -/
private lemma mem_support_cases :
    ∀ {x z : V} (p : G.Walk x z), ∀ v ∈ p.support,
      v = x ∨ v = z ∨ v ∈ p.support.tail.dropLast := by
  intro x z p
  induction p with
  | nil =>
    intro v hv
    rw [Walk.support_nil, List.mem_singleton] at hv
    exact Or.inl hv
  | cons h q ih =>
    intro v hv
    rw [Walk.support_cons] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Or.inl rfl
    · rcases ih v hv' with rfl | h' | h'
      · -- v is the head of the tail walk: internal unless the tail walk
        -- is trivial (then it is the end)
        cases q with
        | nil => exact Or.inr (Or.inl rfl)
        | cons hadj' q' =>
          right; right
          rw [Walk.support_cons, List.tail_cons, Walk.support_cons,
            List.dropLast_cons_of_ne_nil q'.support_ne_nil]
          exact List.mem_cons_self ..
      · exact Or.inr (Or.inl h')
      · right; right
        rw [Walk.support_cons, List.tail_cons]
        have hne : q.support.tail ≠ [] := by
          intro hnil
          rw [hnil] at h'
          simp at h'
        rw [← q.cons_tail_support,
          List.dropLast_cons_of_ne_nil hne]
        exact List.mem_cons_of_mem _ h'

/-! ### Closed trails have length ≥ 3 (loop chains and pure cycles) -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A nonempty closed trail in a simple graph has at least 3 edges
(length 1 would be a loop, length 2 a repeated edge). -/
theorem three_le_length_of_closed {x : V} {p : G.Walk x x}
    (ht : p.IsTrail) (hne : p.length ≠ 0) : 3 ≤ p.length := by
  cases p with
  | nil => simp at hne
  | cons h q =>
    cases q with
    | nil => exact absurd rfl h.ne
    | cons h' q' =>
      cases q' with
      | nil =>
        exfalso
        rw [Walk.isTrail_def] at ht
        simp only [Walk.edges_cons, Walk.edges_nil, List.nodup_cons,
          List.mem_cons, List.not_mem_nil, or_false] at ht
        exact ht.1 Sym2.eq_swap
      | cons h'' q'' =>
        simp only [Walk.length_cons]
        omega

/-! ### The maximal threaded-trail walker (pretest P-C) -/

/-- One-sided maximal extension: any trail whose internal vertices have
degree 2 extends (through degree-2 ends, along unused edges — the
extension is FORCED, hence stays a trail with degree-2 internals) to
one that cannot be extended at its far end: either the far end is a
junction/pendant (degree ≠ 2) or all its incident edges are used.
Fuel-indexed recursion; a trail has at most #E(G) edges, so fuel
`#G.edgeFinset` always suffices. -/
private lemma exists_max_extension :
    ∀ (n : ℕ) (x z : V) (p : G.Walk x z), p.IsTrail →
      (∀ v ∈ p.support.tail.dropLast, G.degree v = 2) →
      #G.edgeFinset ≤ p.length + n →
      ∃ (y : V) (q : G.Walk x y), q.IsTrail ∧
        (∀ v ∈ q.support.tail.dropLast, G.degree v = 2) ∧
        (∀ f ∈ p.edges, f ∈ q.edges) ∧
        (G.degree y ≠ 2 ∨ ∀ f ∈ G.incidenceFinset y, f ∈ q.edges) := by
  intro n
  induction n with
  | zero =>
    -- out of fuel: the trail already carries every edge of G, so its
    -- end is saturated outright
    intro x z p ht hint hlen
    have hsub : p.edges.toFinset ⊆ G.edgeFinset := fun e he =>
      mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he))
    have hcard : #G.edgeFinset ≤ #p.edges.toFinset := by
      rw [List.toFinset_card_of_nodup ht.edges_nodup, p.length_edges]
      omega
    have heq : p.edges.toFinset = G.edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub hcard
    refine ⟨z, p, ht, hint, fun f hf => hf, Or.inr fun f hf => ?_⟩
    have hfe : f ∈ G.edgeFinset :=
      mem_edgeFinset.mpr (mem_incFinset.mp hf).1
    rw [← heq] at hfe
    exact List.mem_toFinset.mp hfe
  | succ n ih =>
    intro x z p ht hint hlen
    by_cases hdz : G.degree z = 2
    · by_cases hsat : ∀ f ∈ G.incidenceFinset z, f ∈ p.edges
      · exact ⟨z, p, ht, hint, fun f hf => hf, Or.inr hsat⟩
      · -- forced extension along an unused edge at the degree-2 end
        push Not at hsat
        obtain ⟨f, hfz, hfp⟩ := hsat
        have hzf : z ∈ f := (mem_incFinset.mp hfz).2
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hzf
        have hzw : G.Adj z w :=
          G.mem_edgeSet.mp (mem_incFinset.mp hfz).1
        have ht' : (p.concat hzw).IsTrail := by
          rw [Walk.isTrail_def, Walk.edges_concat, List.concat_eq_append,
            List.nodup_append]
          refine ⟨ht.edges_nodup, List.nodup_singleton _, ?_⟩
          intro a ha c hc
          rw [List.mem_singleton] at hc
          subst hc
          exact fun heq => hfp (heq ▸ ha)
        have hint' : ∀ v ∈ (p.concat hzw).support.tail.dropLast,
            G.degree v = 2 := by
          intro v hv
          rw [Walk.support_concat, ← p.cons_tail_support,
            List.cons_append, List.tail_cons, List.dropLast_concat] at hv
          exact deg_two_of_mem_tail p hdz hint v hv
        obtain ⟨y, q, h1, h2, h3, h4⟩ := ih x w (p.concat hzw) ht' hint'
          (by rw [Walk.length_concat]; omega)
        refine ⟨y, q, h1, h2, fun f hf => h3 f ?_, h4⟩
        rw [Walk.edges_concat, List.concat_eq_append, List.mem_append]
        exact Or.inl hf
    · exact ⟨z, p, ht, hint, fun f hf => hf, Or.inl hdz⟩

/-! ### Pieces -/

variable (G) in
/-- **A piece of the chain decomposition**: a nonempty trail all of
whose internal vertices (the support with both end positions removed)
have degree 2, which is either a CHAIN (both end degrees ≠ 2 — the
case x = y is a loop chain) or a PURE CYCLE (closed, with every support
vertex of degree 2).  This is the LOCAL per-piece certificate used
toward the glue assembly (pure cycles = the `exists_cycle_distance2`
clients); the global partition/canonicality facts and the first/last
port-POSITION fact are separate obligations, still owed (see the
honest-scope note at the end of the file). -/
structure IsPiece {x y : V} (p : G.Walk x y) : Prop where
  ne : p.length ≠ 0
  trail : p.IsTrail
  internal : ∀ v ∈ p.support.tail.dropLast, G.degree v = 2
  ends : (G.degree x ≠ 2 ∧ G.degree y ≠ 2) ∨
    (x = y ∧ ∀ v ∈ p.support, G.degree v = 2)

omit [DecidableEq V] in
/-- Closed pieces — loop chains and pure cycles alike — have at least
3 edges. -/
theorem IsPiece.three_le_length {x : V} {p : G.Walk x x}
    (hp : IsPiece G p) : 3 ≤ p.length :=
  three_le_length_of_closed hp.trail hp.ne

/-- **Linkage closure** (pretest P-D): a piece is SATURATED at each of
its degree-2 support vertices — both incident edges of such a vertex lie
on the piece.  (The count of piece edges at `v` is even by the trail
parity lemma — `v` differs from both ends of a chain, and the cycle case
is closed — positive since `v` is on the walk, and at most deg v = 2.)
Consequently a piece's edge set is closed under "shares a degree-2
endpoint", the relation whose classes make the decomposition canonical:
this is the fill-independence input of the glue assembly. -/
theorem IsPiece.saturated_of_degree_two {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {v : V} (hv : v ∈ p.support)
    (hdv : G.degree v = 2) :
    ∀ f ∈ G.incidenceFinset v, f ∈ p.edges := by
  have hcc := countP_edges_eq_card hp.trail v
  have heven : Even (p.edges.countP fun e => v ∈ e) := by
    rw [hp.trail.even_countP_edges_iff v]
    intro hxy
    rcases hp.ends with ⟨hdx, hdy⟩ | ⟨heq, _⟩
    · exact ⟨fun h => hdx (h ▸ hdv), fun h => hdy (h ▸ hdv)⟩
    · exact absurd heq hxy
  have hpos : 0 < p.edges.countP fun e => v ∈ e := by
    obtain ⟨f, hf, hvf⟩ := exists_edge_of_mem_support p hp.ne v hv
    rw [List.countP_eq_length_filter]
    exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hf, by simpa⟩)
  have hle : #{f ∈ p.edges.toFinset | v ∈ f} ≤ 2 := by
    have h1 := Finset.card_le_card (filter_subset_incidence p v)
    rwa [card_incidenceFinset_eq_degree, hdv] at h1
  have hcard : #{f ∈ p.edges.toFinset | v ∈ f} = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have heqf : {f ∈ p.edges.toFinset | v ∈ f} = G.incidenceFinset v :=
    Finset.eq_of_subset_of_card_le (filter_subset_incidence p v)
      (by rw [hcard, card_incidenceFinset_eq_degree, hdv])
  intro f hf
  rw [← heqf, Finset.mem_filter, List.mem_toFinset] at hf
  exact hf.1

omit [DecidableEq V] in
/-- **Ports** (handoff fact): a piece edge incident to a vertex of
degree ≠ 2 has that vertex as an END of the piece — at junctions, pieces
only ever START or STOP.  (Internal vertices have degree 2 by the piece
certificate.) -/
theorem IsPiece.end_of_junction {x y : V} {p : G.Walk x y}
    (hp : IsPiece G p) {f : Sym2 V} (hf : f ∈ p.edges) {v : V}
    (hvf : v ∈ f) (hdv : G.degree v ≠ 2) : v = x ∨ v = y := by
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hvf
  have hvs : v ∈ p.support := Walk.fst_mem_support_of_mem_edges p hf
  rcases mem_support_cases p v hvs with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hp.internal v h) hdv

/-! ### The existence theorem (the chain-decomposition stone) -/

/-- **Chain-decomposition existence** (pretest P-C): through every edge
of EVERY graph there is a piece — a maximal threaded trail that is a
chain (end degrees ≠ 2) or a pure cycle (closed, all degrees 2).  No
admissibility hypothesis is needed.  Proof: grow the one-edge trail at
both ends through degree-2 vertices along unused edges
(`exists_max_extension`); at a maximal degree-2 end every incident
edge is used, so the parity dichotomy `end_eq_start_of_saturated`
closes the walk, and the internal-degree invariant turns the closed
case into a pure cycle. -/
theorem exists_piece {a b : V} (hab : G.Adj a b) :
    ∃ (x y : V) (p : G.Walk x y), IsPiece G p ∧ s(a, b) ∈ p.edges := by
  classical
  -- the seed: the one-edge trail a — b
  have ht0 : (Walk.cons hab Walk.nil : G.Walk a b).IsTrail := by
    rw [Walk.isTrail_def]
    simp
  have hint0 : ∀ v ∈ (Walk.cons hab Walk.nil :
      G.Walk a b).support.tail.dropLast, G.degree v = 2 := by
    simp
  -- extend maximally at the b end
  obtain ⟨z, q, htq, hintq, hsubq, hmaxq⟩ :=
    exists_max_extension #G.edgeFinset a b (Walk.cons hab Walk.nil)
      ht0 hint0 (by omega)
  -- extend maximally at the a end (extend the reverse at its far end)
  have hintqr : ∀ v ∈ q.reverse.support.tail.dropLast,
      G.degree v = 2 := by
    intro v hv
    rw [internal_reverse, List.mem_reverse] at hv
    exact hintq v hv
  obtain ⟨y, r, htr, hintr, hsubr, hmaxr⟩ :=
    exists_max_extension #G.edgeFinset z a q.reverse htq.reverse hintqr
      (by omega)
  -- the piece is r.reverse : G.Walk y z
  have hmem : s(a, b) ∈ r.reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse]
    apply hsubr
    rw [Walk.edges_reverse, List.mem_reverse]
    apply hsubq
    simp
  have hintrr : ∀ v ∈ r.reverse.support.tail.dropLast,
      G.degree v = 2 := by
    intro v hv
    rw [internal_reverse, List.mem_reverse] at hv
    exact hintr v hv
  have hne : r.reverse.length ≠ 0 := by
    have h1 := List.length_pos_of_mem hmem
    rw [r.reverse.length_edges] at h1
    omega
  -- the z-end maximality certificate transfers from q to r.reverse
  have hmaxz : G.degree z ≠ 2 ∨
      ∀ f ∈ G.incidenceFinset z, f ∈ r.reverse.edges := by
    rcases hmaxq with h | h
    · exact Or.inl h
    · refine Or.inr fun f hf => ?_
      rw [Walk.edges_reverse, List.mem_reverse]
      apply hsubr
      rw [Walk.edges_reverse, List.mem_reverse]
      exact h f hf
  by_cases hdz : G.degree z = 2
  · -- saturated degree-2 end z: the walk is closed (z = y), and with
    -- both ends of degree 2 every support vertex has degree 2
    have hsatz : ∀ f ∈ G.incidenceFinset z, f ∈ r.reverse.edges := by
      rcases hmaxz with h | h
      · exact absurd hdz h
      · exact h
    have hzy : z = y := end_eq_start_of_saturated htr.reverse hdz hsatz
    refine ⟨y, z, r.reverse,
      ⟨hne, htr.reverse, hintrr, Or.inr ⟨hzy.symm, ?_⟩⟩, hmem⟩
    intro v hv
    rw [← r.reverse.cons_tail_support] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact hzy ▸ hdz
    · exact deg_two_of_mem_tail r.reverse hdz hintrr v hv'
  · -- junction end z; the y end must be a junction too, else its
    -- saturation would close the walk onto z
    by_cases hdy : G.degree y = 2
    · exfalso
      rcases hmaxr with h | h
      · exact h hdy
      · exact hdz ((end_eq_start_of_saturated htr hdy h) ▸ hdy)
    · exact ⟨y, z, r.reverse,
        ⟨hne, htr.reverse, hintrr, Or.inl ⟨hdy, hdz⟩⟩, hmem⟩

/-! ### Honest scope note

Banked here: piece EXISTENCE through every edge (the maximal walker,
pretest P-C) with the end dichotomy and the closed-length bound — the
"one remaining mathematical stone" of the C6L3 handoff, step 1.  NOT
yet formalized (still owed to the assembly, pretests P-D/P-E):
linkage-closure (a piece's edge set is exactly the degree-2-linkage
class of any of its edges, making the decomposition canonical as a
partition) and the port-position fact (an edge of a piece at a
degree-≠ 2 vertex is the piece's first or last edge).  `maj_le_six`
remains `proof_wanted`. -/

end SMaj
