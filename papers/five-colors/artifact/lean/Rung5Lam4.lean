import Rung5Lam3

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

namespace SMaj

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The V2-steered glue grouping: triples at degrees 3 and 5, groups of
four at every other junction, and singleton groups below degree 3. -/
private noncomputable def steeredGlueIx (G : SimpleGraph V)
    [DecidableRel G.Adj] : V → Sym2 V → ℕ := fun v =>
  if 3 ≤ G.degree v then
    if G.degree v = 3 ∨ G.degree v = 5 then evenIx G 3 v else evenIx G 4 v
  else evenIx G 1 v

private lemma steeredGlueIx_eq_special {v : V} (hj : 3 ≤ G.degree v)
    (hs : G.degree v = 3 ∨ G.degree v = 5) :
    steeredGlueIx G v = evenIx G 3 v := by
  simp [steeredGlueIx, hj, hs]

private lemma steeredGlueIx_eq_regular {v : V} (hj : 3 ≤ G.degree v)
    (hs : ¬(G.degree v = 3 ∨ G.degree v = 5)) :
    steeredGlueIx G v = evenIx G 4 v := by
  simp [steeredGlueIx, hj, hs]

private lemma steeredGlueIx_eq_low {v : V} (hj : ¬3 ≤ G.degree v) :
    steeredGlueIx G v = evenIx G 1 v := by
  simp [steeredGlueIx, hj]

/-- V2.B2: every junction group has size at most four, and the exceptional
degrees 3 and 5 have the sharper size-three bound. -/
private lemma steeredGlueIx_fiber_le (v : V) (k : ℕ) :
    #{f ∈ G.incidenceFinset v | steeredGlueIx G v f = k} ≤ 4 ∧
      ((G.degree v = 3 ∨ G.degree v = 5) →
        #{f ∈ G.incidenceFinset v | steeredGlueIx G v f = k} ≤ 3) := by
  by_cases hj : 3 ≤ G.degree v
  · by_cases hs : G.degree v = 3 ∨ G.degree v = 5
    · rw [steeredGlueIx_eq_special hj hs]
      have h := evenIx_fiber_le G (s := 3) (by omega) v k
      exact ⟨by omega, fun _ => h⟩
    · rw [steeredGlueIx_eq_regular hj hs]
      exact ⟨evenIx_fiber_le G (s := 4) (by omega) v k,
        fun h => absurd h hs⟩
  · rw [steeredGlueIx_eq_low hj]
    have h := evenIx_fiber_le G (s := 1) (by omega) v k
    exact ⟨by omega, fun hs => by rcases hs with hs | hs <;> omega⟩

/-- V2.B1: the steered grouping still uses at most `hfun 4 d` groups at
every junction. -/
private lemma groups_steeredGlueIx_le {v : V} (hj : 3 ≤ G.degree v) :
    groups G (steeredGlueIx G) v ≤ hfun 4 (G.degree v) := by
  by_cases hs : G.degree v = 3 ∨ G.degree v = 5
  · unfold groups
    rw [steeredGlueIx_eq_special hj hs]
    rcases hs with hd | hd
    · have h := groups_evenIx_le G (s := 3) (by omega) v
      unfold groups at h
      simpa [hfun, hd] using h
    · have h := groups_evenIx_le G (s := 3) (by omega) v
      unfold groups at h
      simpa [hfun, hd] using h
  · unfold groups
    rw [steeredGlueIx_eq_regular hj hs]
    have h := groups_evenIx_le G (s := 4) (by omega) v
    unfold groups at h
    exact h

/-- Below degree three the steered grouping retains singleton fibers. -/
private lemma steeredGlueIx_inj_low {v : V} (hj : ¬3 ≤ G.degree v)
    {f₁ f₂ : Sym2 V} (h₁ : f₁ ∈ G.incidenceFinset v)
    (h₂ : f₂ ∈ G.incidenceFinset v)
    (heq : steeredGlueIx G v f₁ = steeredGlueIx G v f₂) : f₁ = f₂ := by
  rw [steeredGlueIx_eq_low hj] at heq
  exact evenIx_one_inj h₁ h₂ heq

private lemma steeredGlueIx_lt (v : V) (f : Sym2 V) :
    steeredGlueIx G v f < Fintype.card V + 1 := by
  have hgen : ∀ s : ℕ, evenIx G s v f < Fintype.card V + 1 := by
    intro s
    rw [evenIx]
    split_ifs with h
    · have h₁ : ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) <
          #(G.incidenceFinset v) := Fin.isLt _
      have h₂ : #(G.incidenceFinset v) ≤ Fintype.card V := by
        rw [card_incidenceFinset_eq_degree, ← card_neighborFinset_eq_degree]
        exact card_le_univ _
      have h₃ := Nat.div_le_self
        ((G.incidenceFinset v).equivFin ⟨f, h⟩ : ℕ) s
      omega
    · omega
  by_cases hj : 3 ≤ G.degree v
  · by_cases hs : G.degree v = 3 ∨ G.degree v = 5
    · rw [steeredGlueIx_eq_special hj hs]; exact hgen 3
    · rw [steeredGlueIx_eq_regular hj hs]; exact hgen 4
  · rw [steeredGlueIx_eq_low hj]; exact hgen 1

private abbrev ShortMNode (G : SimpleGraph V) :=
  V × Fin (Fintype.card V + 1)

private noncomputable def steeredNodeAt (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (f : Sym2 V) : ShortMNode G :=
  (v, ⟨steeredGlueIx G v f, steeredGlueIx_lt v f⟩)

private lemma steeredNodeAt_eq_iff {v w : V} {f g : Sym2 V} :
    steeredNodeAt G v f = steeredNodeAt G w g ↔
      v = w ∧ steeredGlueIx G v f = steeredGlueIx G w g := by
  simp [steeredNodeAt, Fin.ext_iff]

/-- The V2 M-population: exactly the non-cycle chain classes of length at
most two. Long chains and pure cycles have no member. -/
private abbrev ShortMember (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {q : EdgeClass G // ¬(classPiece G q).IsCycle ∧
    (classPiece G q).walk.length < 3}

private noncomputable instance shortMemberDecEq : DecidableEq (ShortMember G) :=
  Classical.decEq _

private noncomputable def shortStartNode (q : EdgeClass G) : ShortMNode G :=
  steeredNodeAt G (classPiece G q).a (classPiece G q).firstEdge

private noncomputable def shortEndNode (q : EdgeClass G) : ShortMNode G :=
  steeredNodeAt G (classPiece G q).b (classPiece G q).lastEdge

/-- Each short chain contributes exactly one M-edge, joining its two
steered end-group sites. -/
private noncomputable def shortMfam (m : ShortMember G) : Sym2 (ShortMNode G) :=
  s(shortStartNode (G := G) m.1, shortEndNode (G := G) m.1)

private lemma shortStartNode_ne_endNode (m : ShortMember G) :
    shortStartNode (G := G) m.1 ≠ shortEndNode (G := G) m.1 := by
  intro h
  have hab := (classPiece G m.1).a_ne_b_of_length_lt_three m.2.2
  exact hab ((steeredNodeAt_eq_iff.mp h).1)

/-- V2 looplessness is by construction: a short member has distinct end
vertices because a closed trail in a simple graph has length at least 3. -/
private lemma shortMfam_not_isDiag (m : ShortMember G) :
    ¬(shortMfam m).IsDiag := by
  simpa only [shortMfam, Sym2.mk_isDiag_iff] using shortStartNode_ne_endNode m

/-- Population completeness in the reverse direction: every chain class
of length at most two supplies its unique short member. -/
private def shortMember_of_chain {q : EdgeClass G}
    (hnc : ¬(classPiece G q).IsCycle)
    (hl : (classPiece G q).walk.length < 3) : ShortMember G :=
  ⟨q, hnc, hl⟩

private noncomputable def shortPortEdge (nd : ShortMNode G)
    (m : ShortMember G) : Sym2 V :=
  if shortStartNode (G := G) m.1 = nd then
    (classPiece G m.1).firstEdge else (classPiece G m.1).lastEdge

private lemma shortPortEdge_mem (nd : ShortMNode G) (m : ShortMember G) :
    shortPortEdge nd m ∈ (classPiece G m.1).walk.edges := by
  unfold shortPortEdge
  split_ifs
  · exact (classPiece G m.1).firstEdge_mem
  · exact (classPiece G m.1).lastEdge_mem

private lemma shortPortEdge_spec {v : V} {k : Fin (Fintype.card V + 1)}
    {m : ShortMember G} (hnd : (v, k) ∈ shortMfam m) :
    shortPortEdge (G := G) (v, k) m ∈ G.incidenceFinset v ∧
      steeredGlueIx G v (shortPortEdge (G := G) (v, k) m) = k.1 := by
  have hstart : ∀ (q : EdgeClass G), shortStartNode (G := G) q = (v, k) →
      (classPiece G q).firstEdge ∈ G.incidenceFinset v ∧
        steeredGlueIx G v (classPiece G q).firstEdge = k.1 := by
    intro q h
    have hv : (classPiece G q).a = v := by
      simpa [shortStartNode, steeredNodeAt] using
        congrArg (fun z : ShortMNode G => z.1) h
    have hix := congrArg (fun z : ShortMNode G => z.2.1) h
    simp only [shortStartNode, steeredNodeAt] at hix
    subst hv
    exact ⟨mem_incFinset.mpr ⟨
      (classPiece G q).walk.edges_subset_edgeSet (classPiece G q).firstEdge_mem,
      Sym2.mem_mk_left _ _⟩, hix⟩
  have hend : ∀ (q : EdgeClass G), shortEndNode (G := G) q = (v, k) →
      (classPiece G q).lastEdge ∈ G.incidenceFinset v ∧
        steeredGlueIx G v (classPiece G q).lastEdge = k.1 := by
    intro q h
    have hv : (classPiece G q).b = v := by
      simpa [shortEndNode, steeredNodeAt] using
        congrArg (fun z : ShortMNode G => z.1) h
    have hix := congrArg (fun z : ShortMNode G => z.2.1) h
    simp only [shortEndNode, steeredNodeAt] at hix
    subst hv
    exact ⟨mem_incFinset.mpr ⟨
      (classPiece G q).walk.edges_subset_edgeSet (classPiece G q).lastEdge_mem,
      Sym2.mem_mk_right _ _⟩, hix⟩
  rcases Sym2.mem_iff.mp hnd with hs | he
  · have hs' : shortStartNode (G := G) m.1 = (v, k) := hs.symm
    simp only [shortPortEdge, if_pos hs']
    exact hstart m.1 hs'
  · have he' : shortEndNode (G := G) m.1 = (v, k) := he.symm
    have hne : shortStartNode (G := G) m.1 ≠ (v, k) := by
      intro hs'
      exact shortStartNode_ne_endNode m (hs'.trans he'.symm)
    simp only [shortPortEdge, if_neg hne]
    exact hend m.1 he'

private lemma shortPort_member_unique {nd : ShortMNode G}
    {m m' : ShortMember G} (heq : shortPortEdge nd m = shortPortEdge nd m') :
    m = m' := by
  have hc : m.1 = m'.1 := by
    apply Subtype.ext
    rw [← classPiece_class_eq G (shortPortEdge_mem nd m),
      ← classPiece_class_eq G (shortPortEdge_mem nd m'), heq]
  exact Subtype.ext hc

/-- V2 degree transfer: members at a site inject into that site's steered
group, hence every M-node has degree at most four. -/
private lemma shortMfam_count_le_four [Fintype (ShortMember G)]
    (nd : ShortMNode G) :
    #{m ∈ (Finset.univ : Finset (ShortMember G)) | nd ∈ shortMfam m} ≤ 4 := by
  classical
  rcases nd with ⟨v, k⟩
  calc
    #{m ∈ (Finset.univ : Finset (ShortMember G)) | (v, k) ∈ shortMfam m}
        ≤ #{f ∈ G.incidenceFinset v | steeredGlueIx G v f = k.1} := by
          apply card_le_card_of_injOn (shortPortEdge (G := G) (v, k))
          · intro m hm
            rw [mem_coe, mem_filter] at hm
            rw [mem_coe, mem_filter]
            exact shortPortEdge_spec hm.2
          · intro m hm m' hm' heq
            exact shortPort_member_unique heq
    _ ≤ 4 := (steeredGlueIx_fiber_le v k.1).1

private lemma Piece.firstEdge_eq_mk_ends_of_length_one (P : Piece G)
    (h₁ : P.walk.length = 1) : P.firstEdge = s(P.a, P.b) := by
  obtain ⟨hpos, hedge⟩ := P.firstEdge_eq
  calc
    P.firstEdge = P.walk.edges[0] := hedge.symm
    _ = s(P.walk.getVert 0, P.walk.getVert (0 + 1)) := edges_getElem P.walk hpos
    _ = s(P.a, P.b) := by
      rw [Walk.getVert_zero, show 0 + 1 = P.walk.length by omega,
        P.walk.getVert_length]

private lemma shortMember_eq_of_parallel_direct {m m' : ShortMember G}
    (hm₁ : (classPiece G m.1).walk.length = 1)
    (hm₁' : (classPiece G m'.1).walk.length = 1)
    (hpar : shortMfam m = shortMfam m') : m = m' := by
  have hp := Sym2.eq_iff.mp hpar
  have hedge : (classPiece G m.1).firstEdge =
      (classPiece G m'.1).firstEdge := by
    rw [(classPiece G m.1).firstEdge_eq_mk_ends_of_length_one hm₁,
      (classPiece G m'.1).firstEdge_eq_mk_ends_of_length_one hm₁']
    rcases hp with ⟨hs, he⟩ | ⟨hs, he⟩
    · have ha := congrArg (fun z : ShortMNode G => z.1) hs
      have hb := congrArg (fun z : ShortMNode G => z.1) he
      simp only [shortStartNode, shortEndNode, steeredNodeAt] at ha hb
      rw [ha, hb]
    · have ha := congrArg (fun z : ShortMNode G => z.1) hs
      have hb := congrArg (fun z : ShortMNode G => z.1) he
      simp only [shortStartNode, shortEndNode, steeredNodeAt] at ha hb
      rw [ha, hb]
      exact Sym2.eq_swap
  have hc : m.1 = m'.1 := by
    apply Subtype.ext
    rw [← classPiece_class_eq G (classPiece G m.1).firstEdge_mem,
      ← classPiece_class_eq G (classPiece G m'.1).firstEdge_mem, hedge]
  exact Subtype.ext hc

/-- V2 cherry extraction: two distinct short members in one parallel
class cannot both be direct edges, by simplicity of `G`; hence at least
one is a length-two chain and supplies the cherry. -/
private lemma exists_two_chain_of_parallel {m m' : ShortMember G}
    (hne : m ≠ m') (hpar : shortMfam m = shortMfam m') :
    (classPiece G m.1).walk.length = 2 ∨
      (classPiece G m'.1).walk.length = 2 := by
  by_contra h
  push_neg at h
  have hmpos := Nat.pos_of_ne_zero (classPiece G m.1).piece.ne
  have hmpos' := Nat.pos_of_ne_zero (classPiece G m'.1).piece.ne
  have hm₁ : (classPiece G m.1).walk.length = 1 := by omega
  have hm₁' : (classPiece G m'.1).walk.length = 1 := by omega
  exact hne (shortMember_eq_of_parallel_direct hm₁ hm₁' hpar)

private noncomputable def shortMult [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)]
    (a b : ShortMNode G) : ℕ := famMatrix (shortMfam (G := G)) a b

private lemma shortMult_symm [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (a b : ShortMNode G) :
    shortMult (G := G) a b = shortMult (G := G) b a :=
  famMatrix_symm (shortMfam (G := G)) a b

private lemma shortMult_diag [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (a : ShortMNode G) :
    shortMult (G := G) a a = 0 :=
  famMatrix_diag (shortMfam (G := G)) shortMfam_not_isDiag a

private lemma shortMult_mdeg_le_four [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)]
    (a : ShortMNode G) : mdeg (shortMult (G := G)) a ≤ 4 := by
  change mdeg (famMatrix (shortMfam (G := G))) a ≤ 4
  rw [mdeg_famMatrix (shortMfam (G := G)) shortMfam_not_isDiag]
  exact shortMfam_count_le_four a

private lemma shortMult_le_mdeg [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (a b : ShortMNode G) :
    shortMult (G := G) a b ≤ mdeg (shortMult (G := G)) a := by
  rw [mdeg]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

/-- The only heavy class that can violate Rule 3 is the `(4,4), μ=2`
class. This formulation uses actual M-degrees; degree transfer then pins
both endpoint groups to four occupied short-chain slots. -/
private lemma bad_parallel_table [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] {a b : ShortMNode G}
    (hμ : 2 ≤ shortMult (G := G) a b)
    (hbad : 5 + shortMult (G := G) a b <
      mdeg (shortMult (G := G)) a + mdeg (shortMult (G := G)) b) :
    mdeg (shortMult (G := G)) a = 4 ∧
      mdeg (shortMult (G := G)) b = 4 ∧
      shortMult (G := G) a b = 2 := by
  have ha := shortMult_mdeg_le_four (G := G) a
  have hb := shortMult_mdeg_le_four (G := G) b
  have hμa := shortMult_le_mdeg (G := G) a b
  have hμb : shortMult (G := G) a b ≤ mdeg (shortMult (G := G)) b := by
    rw [shortMult_symm (G := G) a b]
    exact shortMult_le_mdeg (G := G) b a
  omega

/-- Every Rule-3-violating class has a length-two member available for
the V2 cherry expansion. -/
private lemma exists_cherry_of_bad [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] {a b : ShortMNode G}
    (hμ : 2 ≤ shortMult (G := G) a b)
    (hbad : 5 + shortMult (G := G) a b <
      mdeg (shortMult (G := G)) a + mdeg (shortMult (G := G)) b) :
    ∃ m : ShortMember G, shortMfam m = s(a, b) ∧
      (classPiece G m.1).walk.length = 2 := by
  have hcard : #{m ∈ (Finset.univ : Finset (ShortMember G)) |
      shortMfam m = s(a, b)} = 2 := by
    change shortMult (G := G) a b = 2
    exact (bad_parallel_table hμ hbad).2.2
  obtain ⟨m, m', hne, hset⟩ := Finset.card_eq_two.mp hcard
  have hm : m ∈ {m ∈ (Finset.univ : Finset (ShortMember G)) |
      shortMfam m = s(a, b)} := by rw [hset]; simp
  have hm' : m' ∈ {m ∈ (Finset.univ : Finset (ShortMember G)) |
      shortMfam m = s(a, b)} := by rw [hset]; simp
  rw [Finset.mem_filter] at hm hm'
  rcases exists_two_chain_of_parallel hne (hm.2.trans hm'.2.symm) with h | h
  · exact ⟨m, hm.2, h⟩
  · exact ⟨m', hm'.2, h⟩

private def BadShortClass [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (e : Sym2 (ShortMNode G)) : Prop :=
  ∃ a b, e = s(a, b) ∧ 2 ≤ shortMult (G := G) a b ∧
    5 + shortMult (G := G) a b <
      mdeg (shortMult (G := G)) a + mdeg (shortMult (G := G)) b

private lemma short_rule3_of_not_bad [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] {a b : ShortMNode G}
    (hμ : 2 ≤ shortMult (G := G) a b)
    (hnot : ¬BadShortClass (G := G) s(a, b)) :
    mdeg (shortMult (G := G)) a + mdeg (shortMult (G := G)) b ≤
      5 + shortMult (G := G) a b := by
  by_contra h
  exact hnot ⟨a, b, rfl, hμ, by omega⟩

private noncomputable def cherryOf [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (e : Sym2 (ShortMNode G))
    (hbad : BadShortClass (G := G) e) : ShortMember G :=
  (show ∃ m : ShortMember G, shortMfam m = e ∧
      (classPiece G m.1).walk.length = 2 by
    rcases hbad with ⟨a, b, rfl, hμ, hbad⟩
    exact exists_cherry_of_bad hμ hbad).choose

private lemma cherryOf_spec [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (e : Sym2 (ShortMNode G))
    (hbad : BadShortClass (G := G) e) :
    shortMfam (cherryOf e hbad) = e ∧
      (classPiece G (cherryOf e hbad).1).walk.length = 2 :=
  (show ∃ m : ShortMember G, shortMfam m = e ∧
      (classPiece G m.1).walk.length = 2 by
    rcases hbad with ⟨a, b, rfl, hμ, hbad⟩
    exact exists_cherry_of_bad hμ hbad).choose_spec

private def IsChosenCherry [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (m : ShortMember G) : Prop :=
  ∃ hbad : BadShortClass (G := G) (shortMfam m),
    cherryOf (shortMfam m) hbad = m

private lemma chosenCherry_length_two [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] {m : ShortMember G}
    (hm : IsChosenCherry (G := G) m) :
    (classPiece G m.1).walk.length = 2 := by
  obtain ⟨hbad, h⟩ := hm
  rw [← h]
  exact (cherryOf_spec (shortMfam m) hbad).2

private noncomputable def shortFiber [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (e : Sym2 (ShortMNode G)) :
    Finset (ShortMember G) :=
  {m ∈ Finset.univ | shortMfam m = e}

private noncomputable def retainedFiber [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (e : Sym2 (ShortMNode G)) :
    Finset (ShortMember G) := by
  classical
  exact {m ∈ shortFiber (G := G) e | ¬IsChosenCherry (G := G) m}

private lemma chosen_iff_eq_cherry [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] {e : Sym2 (ShortMNode G)}
    (hbad : BadShortClass (G := G) e) {m : ShortMember G}
    (hm : m ∈ shortFiber (G := G) e) :
    IsChosenCherry (G := G) m ↔ m = cherryOf e hbad := by
  rw [shortFiber, Finset.mem_filter] at hm
  constructor
  · rintro ⟨hbad', hc⟩
    have he : shortMfam m = e := hm.2
    subst e
    have hp : hbad' = hbad := Subsingleton.elim _ _
    subst hp
    exact hc.symm
  · intro h
    subst m
    unfold IsChosenCherry
    rw [(cherryOf_spec e hbad).1]
    exact ⟨hbad, rfl⟩

private lemma retainedFiber_bad_eq_erase [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] {e : Sym2 (ShortMNode G)}
    (hbad : BadShortClass (G := G) e) :
    retainedFiber (G := G) e =
      (shortFiber (G := G) e).erase (cherryOf e hbad) := by
  classical
  ext m
  have hc : cherryOf e hbad ∈ shortFiber (G := G) e := by
    rw [shortFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (cherryOf_spec e hbad).1⟩
  by_cases hm : m ∈ shortFiber (G := G) e
  · rw [retainedFiber, Finset.mem_filter, Finset.mem_erase]
    simp only [hm, and_true]
    rw [chosen_iff_eq_cherry hbad hm]
    simp
  · simp [retainedFiber, hm]

private lemma retainedFiber_bad_card_one [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] {e : Sym2 (ShortMNode G)}
    (hbad : BadShortClass (G := G) e) :
    #(retainedFiber (G := G) e) = 1 := by
  classical
  rcases hbad with ⟨a, b, rfl, hμ, hfail⟩
  have hcard : #(shortFiber (G := G) s(a, b)) = 2 := by
    change shortMult (G := G) a b = 2
    exact (bad_parallel_table hμ hfail).2.2
  rw [retainedFiber_bad_eq_erase ⟨a, b, rfl, hμ, hfail⟩,
    Finset.card_erase_of_mem]
  · omega
  · rw [shortFiber, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (cherryOf_spec _ _).1⟩

private def ExpandedSpec [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] :
    ShortMember G ⊕ (ShortMember G × Bool) → Prop
  | Sum.inl m => ¬IsChosenCherry (G := G) m
  | Sum.inr (m, _) => IsChosenCherry (G := G) m

private abbrev ExpandedMember [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] :=
  {x : ShortMember G ⊕ (ShortMember G × Bool) // ExpandedSpec (G := G) x}

private noncomputable instance expandedMemberDecEq [Fintype (ShortMember G)] :
    DecidableEq (ExpandedMember (G := G)) := Classical.decEq _

private abbrev ExpandedNode (G : SimpleGraph V) [DecidableRel G.Adj] :=
  ShortMNode G ⊕ ShortMember G

private noncomputable def expandedMfam [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] :
    ExpandedMember (G := G) → Sym2 (ExpandedNode G)
  | ⟨Sum.inl m, _⟩ =>
      s(Sum.inl (shortStartNode (G := G) m.1),
        Sum.inl (shortEndNode (G := G) m.1))
  | ⟨Sum.inr (m, false), _⟩ =>
      s(Sum.inl (shortStartNode (G := G) m.1), Sum.inr m)
  | ⟨Sum.inr (m, true), _⟩ =>
      s(Sum.inr m, Sum.inl (shortEndNode (G := G) m.1))

/-- The cherry expansion remains loopless: retained members inherit short-M
looplessness and each half joins unlike sum constructors. -/
private lemma expandedMfam_not_isDiag [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] (x : ExpandedMember (G := G)) :
    ¬(expandedMfam x).IsDiag := by
  obtain ⟨x, hx⟩ := x
  rcases x with m | ⟨m, b⟩
  · simp only [expandedMfam, Sym2.mk_isDiag_iff, Sum.inl.injEq]
    exact shortStartNode_ne_endNode m
  · cases b <;> simp [expandedMfam]

private def expandedBase [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] : ExpandedMember (G := G) → ShortMember G
  | ⟨Sum.inl m, _⟩ => m
  | ⟨Sum.inr (m, _), _⟩ => m

private lemma expandedBase_mem_short {nd : ShortMNode G}
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    {x : ExpandedMember (G := G)}
    (hx : (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x) :
    nd ∈ shortMfam (expandedBase x) := by
  obtain ⟨x, hs⟩ := x
  rcases x with m | ⟨m, b⟩
  · simpa [expandedMfam, expandedBase, shortMfam] using hx
  · cases b
    · have h : nd = shortStartNode (G := G) m.1 := by
        simpa [expandedMfam] using hx
      change nd ∈ shortMfam m
      simp [shortMfam, h]
    · have h : nd = shortEndNode (G := G) m.1 := by
        simpa [expandedMfam] using hx
      change nd ∈ shortMfam m
      simp [shortMfam, h]

private lemma expandedBase_injective_at_old {nd : ShortMNode G}
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    {x y : ExpandedMember (G := G)}
    (hx : (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x)
    (hy : (Sum.inl nd : ExpandedNode G) ∈ expandedMfam y)
    (hbase : expandedBase x = expandedBase y) : x = y := by
  obtain ⟨x, hxs⟩ := x
  obtain ⟨y, hys⟩ := y
  apply Subtype.ext
  rcases x with m | ⟨m, b⟩ <;> rcases y with m' | ⟨m', b'⟩
  · simp only [expandedBase] at hbase
    subst m'
    rfl
  · simp only [expandedBase] at hbase
    subst m'
    exact absurd hys hxs
  · simp only [expandedBase] at hbase
    subst m'
    exact absurd hxs hys
  · simp only [expandedBase] at hbase
    subst m'
    cases b <;> cases b'
    · rfl
    · exfalso
      have h₁ : nd = shortStartNode (G := G) m.1 := by
        simpa [expandedMfam] using hx
      have h₂ : nd = shortEndNode (G := G) m.1 := by
        simpa [expandedMfam] using hy
      exact shortStartNode_ne_endNode m (h₁.symm.trans h₂)
    · exfalso
      have h₁ : nd = shortEndNode (G := G) m.1 := by
        simpa [expandedMfam] using hx
      have h₂ : nd = shortStartNode (G := G) m.1 := by
        simpa [expandedMfam] using hy
      exact shortStartNode_ne_endNode m (h₂.symm.trans h₁)
    · rfl

private lemma expandedMfam_count_old_le_four
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] (nd : ShortMNode G) :
    #{x ∈ (Finset.univ : Finset (ExpandedMember (G := G))) |
      (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x} ≤ 4 := by
  classical
  calc
    #{x ∈ (Finset.univ : Finset (ExpandedMember (G := G))) |
        (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x}
        ≤ #{m ∈ (Finset.univ : Finset (ShortMember G)) |
          nd ∈ shortMfam m} := by
            apply card_le_card_of_injOn (expandedBase (G := G))
            · intro x hx
              rw [mem_coe, mem_filter] at hx ⊢
              exact ⟨mem_univ _, expandedBase_mem_short hx.2⟩
            · intro x hx y hy heq
              rw [mem_coe, mem_filter] at hx hy
              exact expandedBase_injective_at_old hx.2 hy.2 heq
    _ ≤ 4 := shortMfam_count_le_four nd

private def expandedTag [Fintype (ShortMember G)]
    [DecidableEq (ShortMember G)] : ExpandedMember (G := G) → Bool
  | ⟨Sum.inl _, _⟩ => false
  | ⟨Sum.inr (_, b), _⟩ => b

private lemma expandedTag_injective_at_fresh {m₀ : ShortMember G}
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    {x y : ExpandedMember (G := G)}
    (hx : (Sum.inr m₀ : ExpandedNode G) ∈ expandedMfam x)
    (hy : (Sum.inr m₀ : ExpandedNode G) ∈ expandedMfam y)
    (htag : expandedTag x = expandedTag y) : x = y := by
  obtain ⟨x, hxs⟩ := x
  obtain ⟨y, hys⟩ := y
  apply Subtype.ext
  rcases x with m | ⟨m, b⟩ <;> rcases y with m' | ⟨m', b'⟩
  · simp [expandedMfam] at hx
  · simp [expandedMfam] at hx
  · simp [expandedMfam] at hy
  · cases b <;> cases b'
    · have hm : m₀ = m := by simpa [expandedMfam] using hx
      have hm' : m₀ = m' := by simpa [expandedMfam] using hy
      exact congrArg (fun z => Sum.inr (z, false)) (hm.symm.trans hm')
    · simp [expandedTag] at htag
    · simp [expandedTag] at htag
    · have hm : m₀ = m := by simpa [expandedMfam] using hx
      have hm' : m₀ = m' := by simpa [expandedMfam] using hy
      exact congrArg (fun z => Sum.inr (z, true)) (hm.symm.trans hm')

private lemma expandedMfam_count_fresh_le_four
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] (m₀ : ShortMember G) :
    #{x ∈ (Finset.univ : Finset (ExpandedMember (G := G))) |
      (Sum.inr m₀ : ExpandedNode G) ∈ expandedMfam x} ≤ 4 := by
  classical
  calc
    #{x ∈ (Finset.univ : Finset (ExpandedMember (G := G))) |
        (Sum.inr m₀ : ExpandedNode G) ∈ expandedMfam x}
        ≤ #(Finset.univ : Finset Bool) := by
          apply card_le_card_of_injOn (expandedTag (G := G))
          · intro x hx
            show expandedTag (G := G) x ∈ (Finset.univ : Finset Bool)
            exact Finset.mem_univ _
          · intro x hx y hy heq
            rw [mem_coe, mem_filter] at hx hy
            exact expandedTag_injective_at_fresh hx.2 hy.2 heq
    _ ≤ 4 := by decide

private lemma expandedMfam_count_le_four
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] (nd : ExpandedNode G) :
    #{x ∈ (Finset.univ : Finset (ExpandedMember (G := G))) |
      nd ∈ expandedMfam x} ≤ 4 := by
  rcases nd with nd | m₀
  · exact expandedMfam_count_old_le_four nd
  · exact expandedMfam_count_fresh_le_four m₀

private noncomputable def expandedOldFiber
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ShortMNode G) : Finset (ExpandedMember (G := G)) :=
  {x ∈ Finset.univ |
    expandedMfam x = s((Sum.inl a : ExpandedNode G), Sum.inl b)}

private lemma expandedOldFiber_card_eq_retained
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ShortMNode G) :
    #(expandedOldFiber (G := G) a b) = #(retainedFiber (G := G) s(a, b)) := by
  classical
  apply Finset.card_bij (fun x _ => expandedBase x)
  · intro x hx
    rw [expandedOldFiber, Finset.mem_filter] at hx
    rw [retainedFiber, Finset.mem_filter, shortFiber, Finset.mem_filter]
    obtain ⟨xv, hs⟩ := x
    rcases xv with m | ⟨m, tag⟩
    · simp only [expandedBase, expandedMfam] at hx ⊢
      have he : shortMfam m = s(a, b) := by
        unfold shortMfam
        rcases Sym2.eq_iff.mp hx.2 with h | h
        · apply Sym2.eq_iff.mpr
          exact Or.inl ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩
        · apply Sym2.eq_iff.mpr
          exact Or.inr ⟨Sum.inl.inj h.1, Sum.inl.inj h.2⟩
      exact ⟨⟨Finset.mem_univ _, he⟩, hs⟩
    · cases tag <;> simp [expandedMfam] at hx
  · intro x hx y hy heq
    rw [expandedOldFiber, Finset.mem_filter] at hx hy
    have hxi : (Sum.inl a : ExpandedNode G) ∈ expandedMfam x := by
      rw [hx.2]; exact Sym2.mem_mk_left _ _
    have hyi : (Sum.inl a : ExpandedNode G) ∈ expandedMfam y := by
      rw [hy.2]; exact Sym2.mem_mk_left _ _
    exact expandedBase_injective_at_old hxi hyi heq
  · intro m hm
    rw [retainedFiber, Finset.mem_filter, shortFiber, Finset.mem_filter] at hm
    let x : ExpandedMember (G := G) := ⟨Sum.inl m, hm.2⟩
    refine ⟨x, ?_, rfl⟩
    rw [expandedOldFiber, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [x, expandedMfam]
    simpa [shortMfam] using congrArg
      (Sym2.map (fun z : ShortMNode G => (Sum.inl z : ExpandedNode G))) hm.1.2

private lemma retainedFiber_eq_shortFiber_of_not_bad
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    {e : Sym2 (ShortMNode G)} (hnot : ¬BadShortClass (G := G) e) :
    retainedFiber (G := G) e = shortFiber (G := G) e := by
  classical
  ext m
  rw [retainedFiber, Finset.mem_filter]
  constructor
  · exact fun h => h.1
  · intro hm
    refine ⟨hm, ?_⟩
    rintro ⟨hbad, hc⟩
    have he : shortMfam m = e := by
      rw [shortFiber, Finset.mem_filter] at hm
      exact hm.2
    apply hnot
    rwa [he] at hbad

private lemma expandedMfam_injective_at_fresh {m₀ : ShortMember G}
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    {x y : ExpandedMember (G := G)}
    (hx : (Sum.inr m₀ : ExpandedNode G) ∈ expandedMfam x)
    (hy : (Sum.inr m₀ : ExpandedNode G) ∈ expandedMfam y)
    (he : expandedMfam x = expandedMfam y) : x = y := by
  obtain ⟨x, hxs⟩ := x
  obtain ⟨y, hys⟩ := y
  apply Subtype.ext
  rcases x with m | ⟨m, tx⟩ <;> rcases y with m' | ⟨m', ty⟩
  · simp [expandedMfam] at hx
  · simp [expandedMfam] at hx
  · simp [expandedMfam] at hy
  · cases tx <;> cases ty
    · have hm : m₀ = m := by simpa [expandedMfam] using hx
      have hm' : m₀ = m' := by simpa [expandedMfam] using hy
      exact congrArg (fun z => Sum.inr (z, false)) (hm.symm.trans hm')
    · exfalso
      have hm : m₀ = m := by simpa [expandedMfam] using hx
      have hm' : m₀ = m' := by simpa [expandedMfam] using hy
      subst m; subst m'
      have hp := Sym2.eq_iff.mp he
      rcases hp with h | h <;> simp at h
      exact shortStartNode_ne_endNode m₀ h
    · exfalso
      have hm : m₀ = m := by simpa [expandedMfam] using hx
      have hm' : m₀ = m' := by simpa [expandedMfam] using hy
      subst m; subst m'
      have hp := Sym2.eq_iff.mp he
      rcases hp with h | h <;> simp at h
      exact shortStartNode_ne_endNode m₀ h.symm
    · have hm : m₀ = m := by simpa [expandedMfam] using hx
      have hm' : m₀ = m' := by simpa [expandedMfam] using hy
      exact congrArg (fun z => Sum.inr (z, true)) (hm.symm.trans hm')

private noncomputable def expandedMult
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ExpandedNode G) : ℕ := famMatrix (expandedMfam (G := G)) a b

private lemma expandedMult_symm
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ExpandedNode G) :
    expandedMult (G := G) a b = expandedMult (G := G) b a :=
  famMatrix_symm (expandedMfam (G := G)) a b

private lemma expandedMult_diag
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a : ExpandedNode G) : expandedMult (G := G) a a = 0 :=
  famMatrix_diag (expandedMfam (G := G)) expandedMfam_not_isDiag a

private lemma expandedMult_mdeg_le_four
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a : ExpandedNode G) : mdeg (expandedMult (G := G)) a ≤ 4 := by
  change mdeg (famMatrix (expandedMfam (G := G))) a ≤ 4
  rw [mdeg_famMatrix (expandedMfam (G := G)) expandedMfam_not_isDiag]
  exact expandedMfam_count_le_four a

private lemma expandedMult_old_eq_retained
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ShortMNode G) :
    expandedMult (G := G) (Sum.inl a) (Sum.inl b) =
      #(retainedFiber (G := G) s(a, b)) := by
  change #(expandedOldFiber (G := G) a b) = _
  exact expandedOldFiber_card_eq_retained a b

private lemma expandedMult_le_one_of_fresh
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (m₀ : ShortMember G) (b : ExpandedNode G) :
    expandedMult (G := G) (Sum.inr m₀) b ≤ 1 := by
  unfold expandedMult famMatrix
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  apply expandedMfam_injective_at_fresh
  · rw [hx.2]; exact Sym2.mem_mk_left _ _
  · rw [hy.2]; exact Sym2.mem_mk_left _ _
  · exact hx.2.trans hy.2.symm

private lemma shortMult_eq_card_shortFiber
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    (a b : ShortMNode G) :
    shortMult (G := G) a b = #(shortFiber (G := G) s(a, b)) := by
  rfl

private lemma expanded_old_mdeg_le_short
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a : ShortMNode G) :
    mdeg (expandedMult (G := G)) (Sum.inl a) ≤
      mdeg (shortMult (G := G)) a := by
  change mdeg (famMatrix (expandedMfam (G := G))) (Sum.inl a) ≤
    mdeg (famMatrix (shortMfam (G := G))) a
  rw [mdeg_famMatrix (expandedMfam (G := G)) expandedMfam_not_isDiag,
    mdeg_famMatrix (shortMfam (G := G)) shortMfam_not_isDiag]
  apply card_le_card_of_injOn (expandedBase (G := G))
  · intro x hx
    rw [mem_coe, mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, expandedBase_mem_short hx.2⟩
  · intro x hx y hy heq
    rw [mem_coe, mem_filter] at hx hy
    exact expandedBase_injective_at_old hx.2 hy.2 heq

/-- The expanded matrix satisfies precisely the Rule-3 hypothesis needed
for greedy reinsertion. Bad classes have become simple; untouched classes
retain their multiplicity and only lose degree. -/
private lemma expandedMult_heavy
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ExpandedNode G) (hμ : 2 ≤ expandedMult (G := G) a b) :
    mdeg (expandedMult (G := G)) a + mdeg (expandedMult (G := G)) b ≤
      5 + expandedMult (G := G) a b := by
  rcases a with a | m
  · rcases b with b | m'
    · by_cases hbad : BadShortClass (G := G) s(a, b)
      · have hm : expandedMult (G := G) (Sum.inl a) (Sum.inl b) = 1 := by
          rw [expandedMult_old_eq_retained, retainedFiber_bad_card_one hbad]
        omega
      · have hmult : expandedMult (G := G) (Sum.inl a) (Sum.inl b) =
            shortMult (G := G) a b := by
          rw [expandedMult_old_eq_retained,
            retainedFiber_eq_shortFiber_of_not_bad hbad,
            ← shortMult_eq_card_shortFiber]
        have ha := expanded_old_mdeg_le_short (G := G) a
        have hb := expanded_old_mdeg_le_short (G := G) b
        have hr := short_rule3_of_not_bad (G := G) (by omega) hbad
        omega
    · have hm := expandedMult_symm (G := G) (Sum.inl a) (Sum.inr m')
      have hle := expandedMult_le_one_of_fresh (G := G) m' (Sum.inl a)
      omega
  · have hle := expandedMult_le_one_of_fresh (G := G) m b
    omega

/-- V2.2 passes 1–2 in one call: gated Λ3 colors the expanded matrix,
relative only to its T1 = Λ2 Vizing prerequisite. -/
private theorem exists_expandedMult_coloring
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))] :
    ∃ f, IsMulticoloring (C := Fin 5) (expandedMult (G := G)) f := by
  classical
  apply exists_five_multicoloring_of_reinsertable (expandedMult (G := G))
  · intro a b
    exact expandedMult_symm a b
  · intro a
    exact expandedMult_diag a
  · intro a
    exact expandedMult_mdeg_le_four a
  · intro a b hμ
    exact expandedMult_heavy a b hμ

private noncomputable def transportAt5 {I N : Type*} [Fintype I]
    [DecidableEq I] [DecidableEq N] (t : I → Sym2 N) (Φ : Sym2 N → Finset (Fin 5))
    (hc : ∀ e, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 N) (i : I) (h : t i = e) : Fin 5 :=
  ((Φ e).equivFin.symm (Finset.equivFinOfCardEq (hc e)
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩)).1

private lemma transportAt5_mem {I N : Type*} [Fintype I] [DecidableEq I] [DecidableEq N]
    (t : I → Sym2 N) (Φ : Sym2 N → Finset (Fin 5))
    (hc : ∀ e, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 N) (i : I) (h : t i = e) : transportAt5 t Φ hc e i h ∈ Φ e :=
  ((Φ e).equivFin.symm _).2

private lemma transportAt5_inj {I N : Type*} [Fintype I] [DecidableEq I] [DecidableEq N]
    (t : I → Sym2 N) (Φ : Sym2 N → Finset (Fin 5))
    (hc : ∀ e, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (e : Sym2 N) {i j : I} (hi : t i = e) (hj : t j = e)
    (heq : transportAt5 t Φ hc e i hi = transportAt5 t Φ hc e j hj) : i = j := by
  unfold transportAt5 at heq
  exact Subtype.mk_eq_mk.mp ((Finset.equivFinOfCardEq (hc e)).injective
    ((Φ e).equivFin.symm.injective (Subtype.ext heq)))

private lemma transportAt5_congr {I N : Type*} [Fintype I] [DecidableEq I] [DecidableEq N]
    (t : I → Sym2 N) (Φ : Sym2 N → Finset (Fin 5))
    (hc : ∀ e, #{k ∈ Finset.univ | t k = e} = #(Φ e))
    (i : I) {e e' : Sym2 N} (h : t i = e) (h' : t i = e') (hee : e = e') :
    transportAt5 t Φ hc e i h = transportAt5 t Φ hc e' i h' := by
  subst hee
  rfl

/-- Remaining pass A: transport the set-valued matrix coloring to one color
per expanded family member, injectively inside parallel classes. -/
private theorem exists_expandedMemberColoring
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (f : ExpandedNode G → ExpandedNode G → Finset (Fin 5))
    (hf : IsMulticoloring (expandedMult (G := G)) f) :
    ∃ col : ExpandedMember (G := G) → Fin 5,
      ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
        nd ∈ expandedMfam y → col x ≠ col y := by
  classical
  obtain ⟨hfs, hfc, hfd⟩ := hf
  set Φ : Sym2 (ExpandedNode G) → Finset (Fin 5) := Sym2.lift ⟨f, hfs⟩ with hΦ
  have hc : ∀ e, #{k ∈ Finset.univ | expandedMfam k = e} = #(Φ e) := by
    intro e
    induction e using Sym2.ind with
    | _ a b => rw [hΦ, Sym2.lift_mk, hfc]; rfl
  refine ⟨fun i => transportAt5 expandedMfam Φ hc (expandedMfam i) i rfl, ?_⟩
  intro i j hij a hai haj hcol
  change transportAt5 expandedMfam Φ hc (expandedMfam i) i rfl =
    transportAt5 expandedMfam Φ hc (expandedMfam j) j rfl at hcol
  by_cases he : expandedMfam i = expandedMfam j
  · rw [transportAt5_congr expandedMfam Φ hc j rfl he.symm he.symm] at hcol
    exact hij (transportAt5_inj expandedMfam Φ hc (expandedMfam i) rfl he.symm hcol)
  · obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hai
    obtain ⟨b', hb'⟩ := Sym2.mem_iff_exists.mp haj
    have hbb : b ≠ b' := fun h => he (by rw [hb, hb', h])
    have hd : Disjoint (Φ (expandedMfam i)) (Φ (expandedMfam j)) := by
      rw [hb, hb', hΦ, Sym2.lift_mk, Sym2.lift_mk]
      exact hfd a b b' hbb
    have h1 := transportAt5_mem expandedMfam Φ hc (expandedMfam i) i rfl
    have h2 := transportAt5_mem expandedMfam Φ hc (expandedMfam j) j rfl
    rw [hcol] at h1
    exact (Finset.disjoint_left.mp hd h1) h2

/-! ### Bare-coloring pass (a): mono short transport and pure cycles -/

private def retainedExpanded [Fintype (ShortMember G)]
    (m : ShortMember G) (hm : ¬IsChosenCherry (G := G) m) :
    ExpandedMember (G := G) := ⟨Sum.inl m, hm⟩

private def cherryExpanded [Fintype (ShortMember G)]
    (m : ShortMember G) (side : Bool) (hm : IsChosenCherry (G := G) m) :
    ExpandedMember (G := G) := ⟨Sum.inr (m, side), hm⟩

/-- Start/end port colors of a short-chain member. A chosen cherry uses its
two dispatched halves; every other short member uses its single retained
expanded edge at both ends. -/
private noncomputable def shortPortColor [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (m : ShortMember G)
    (atEnd : Bool) : Fin 5 := by
  classical
  exact if hm : IsChosenCherry (G := G) m
    then col (cherryExpanded m atEnd hm)
    else col (retainedExpanded m hm)

/-- V2 mono transport: every non-cherry short member, in particular every
unsplit length-two chain, receives the same color at both ports. -/
private lemma shortPortColor_mono [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (m : ShortMember G)
    (hm : ¬IsChosenCherry (G := G) m) :
    shortPortColor col m false = shortPortColor col m true := by
  classical
  simp [shortPortColor, hm]

/-- Chosen cherries really do expose the two half-member colors. -/
private lemma shortPortColor_cherry [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (m : ShortMember G)
    (hm : IsChosenCherry (G := G) m) (side : Bool) :
    shortPortColor col m side = col (cherryExpanded m side hm) := by
  classical
  simp [shortPortColor, hm]

/-- Pure-cycle transport directly in the five-color palette. -/
private lemma exists_cycle_distance2_five (L : ℕ) (hL : 3 ≤ L) :
    ∃ c : ℕ → Fin 5, ∀ i < L, c i ≠ c ((i + 2) % L) := by
  obtain ⟨f, hf, hdist⟩ := exists_cycle_distance2 L hL
  refine ⟨fun i => ⟨f i, by have := hf i; omega⟩, ?_⟩
  intro i hi heq
  exact hdist i hi (Fin.ext_iff.mp heq)

#print axioms shortPortColor_mono
#print axioms shortPortColor_cherry
#print axioms exists_cycle_distance2_five

/-! ### Bare-coloring pass (b): long-port first-fit availability -/

/-- The exact V2 port-step cap: at most three colors from the port's own
group plus at most its one l=3 partner leave a color in `Fin 5`. -/
private lemma exists_longPort_color (own : Finset (Fin 5)) (hown : #own ≤ 3)
    (partner : Option (Fin 5)) :
    ∃ c : Fin 5, c ∉ own ∧ ∀ p, partner = some p → c ≠ p := by
  classical
  let forbidden : Finset (Fin 5) := own ∪ partner.toFinset
  have hcard : #forbidden ≤ 4 := by
    have hop : #(partner.toFinset) ≤ 1 := by cases partner <;> simp
    calc
      #forbidden ≤ #own + #(partner.toFinset) := Finset.card_union_le _ _
      _ ≤ 4 := by omega
  have hne : forbiddenᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨c, hc⟩ := hne
  refine ⟨c, ?_, ?_⟩
  · intro h
    exact (Finset.mem_compl.mp hc) (Finset.mem_union_left _ h)
  · intro p hp heq
    subst c
    apply Finset.mem_compl.mp hc
    apply Finset.mem_union_right
    simpa [hp]

#print axioms exists_longPort_color

/-! ### Bare-coloring pass (c): global independent long-chain fills -/

private abbrev LongChain (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {q : EdgeClass G // ¬(classPiece G q).IsCycle ∧
    3 ≤ (classPiece G q).walk.length}

private abbrev LongPort (G : SimpleGraph V) [DecidableRel G.Adj] :=
  LongChain G × Bool

private noncomputable def longPortEdge (P : LongPort G) : Sym2 V :=
  if P.2 then (classPiece G P.1.1).lastEdge
  else (classPiece G P.1.1).firstEdge

private noncomputable def longPortNode (P : LongPort G) : ShortMNode G :=
  if P.2 then shortEndNode (G := G) P.1.1
  else shortStartNode (G := G) P.1.1

private def longPortPartner (P : LongPort G) : LongPort G :=
  (P.1, !P.2)

private lemma longPortPartner_involutive (P : LongPort G) :
    longPortPartner (longPortPartner P) = P := by
  rcases P with ⟨Q, side⟩
  cases side <;> rfl

private lemma longPortPartner_ne (P : LongPort G) : longPortPartner P ≠ P := by
  rcases P with ⟨Q, side⟩
  cases side <;> simp [longPortPartner]

private lemma longPortEdge_mem (P : LongPort G) :
    longPortEdge P ∈ (classPiece G P.1.1).walk.edges := by
  rcases P with ⟨Q, side⟩
  cases side
  · exact (classPiece G Q.1).firstEdge_mem
  · exact (classPiece G Q.1).lastEdge_mem

private lemma longPortEdge_partner_ne (P : LongPort G) :
    longPortEdge P ≠ longPortEdge (longPortPartner P) := by
  rcases P with ⟨Q, side⟩
  have hne := (classPiece G Q.1).firstEdge_ne_lastEdge (by omega :
    2 ≤ (classPiece G Q.1).walk.length)
  cases side
  · exact hne
  · exact hne.symm

private lemma longPortNode_edge (P : LongPort G) :
    longPortNode P = steeredNodeAt G
      (if P.2 then (classPiece G P.1.1).b else (classPiece G P.1.1).a)
      (longPortEdge P) := by
  rcases P with ⟨Q, side⟩
  cases side <;> rfl

private lemma longPortEdge_injective {P Q : LongPort G}
    (h : longPortEdge P = longPortEdge Q) : P = Q := by
  have hclass : P.1.1 = Q.1.1 := by
    apply Subtype.ext
    rw [← classPiece_class_eq G (longPortEdge_mem P),
      ← classPiece_class_eq G (longPortEdge_mem Q), h]
  rcases P with ⟨P, ps⟩
  rcases Q with ⟨Q, qs⟩
  simp only at hclass
  have hPQ : P = Q := Subtype.ext hclass
  subst Q
  cases ps <;> cases qs
  · rfl
  · exact False.elim (longPortEdge_partner_ne (G := G) (P, false) h)
  · exact False.elim (longPortEdge_partner_ne (G := G) (P, true) h)
  · rfl

#print axioms longPortPartner_involutive
#print axioms longPortEdge_partner_ne
#print axioms longPortNode_edge
#print axioms longPortEdge_injective

private abbrev PortSlot [Fintype (ShortMember G)] :=
  ExpandedMember (G := G) ⊕ LongPort G

private def slotAt [Fintype (ShortMember G)] (nd : ShortMNode G) :
    PortSlot (G := G) → Prop
  | Sum.inl x => (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x
  | Sum.inr P => longPortNode P = nd

private noncomputable def slotEdge [Fintype (ShortMember G)]
    (nd : ShortMNode G) : PortSlot (G := G) → Sym2 V
  | Sum.inl x => shortPortEdge nd (expandedBase x)
  | Sum.inr P => longPortEdge P

private def slotColor [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (portCol : LongPort G → Fin 5) :
    PortSlot (G := G) → Fin 5
  | Sum.inl x => col x
  | Sum.inr P => portCol P

private lemma slotEdge_spec [Fintype (ShortMember G)]
    {nd : ShortMNode G} {s : PortSlot (G := G)} (hs : slotAt nd s) :
    slotEdge nd s ∈ G.incidenceFinset nd.1 ∧
      steeredGlueIx G nd.1 (slotEdge nd s) = nd.2.1 := by
  rcases nd with ⟨v, k⟩
  rcases s with x | ⟨Q, side⟩
  · exact shortPortEdge_spec (expandedBase_mem_short hs)
  · cases side
    · have hn : steeredNodeAt G (classPiece G Q.1).a
          (classPiece G Q.1).firstEdge = (v, k) := by
        simpa [slotAt, longPortNode] using hs
      have hv : (classPiece G Q.1).a = v := by
        simpa [steeredNodeAt] using congrArg (fun z : ShortMNode G => z.1) hn
      have hi := congrArg (fun z : ShortMNode G => z.2.1) hn
      simp only [steeredNodeAt] at hi
      subst v
      exact ⟨mem_incFinset.mpr ⟨
        (classPiece G Q.1).walk.edges_subset_edgeSet
          (classPiece G Q.1).firstEdge_mem,
        Sym2.mem_mk_left _ _⟩, hi⟩
    · have hn : steeredNodeAt G (classPiece G Q.1).b
          (classPiece G Q.1).lastEdge = (v, k) := by
        simpa [slotAt, longPortNode] using hs
      have hv : (classPiece G Q.1).b = v := by
        simpa [steeredNodeAt] using congrArg (fun z : ShortMNode G => z.1) hn
      have hi := congrArg (fun z : ShortMNode G => z.2.1) hn
      simp only [steeredNodeAt] at hi
      subst v
      exact ⟨mem_incFinset.mpr ⟨
        (classPiece G Q.1).walk.edges_subset_edgeSet
          (classPiece G Q.1).lastEdge_mem,
        Sym2.mem_mk_right _ _⟩, hi⟩

private lemma slotEdge_injective_at [Fintype (ShortMember G)]
    {nd : ShortMNode G} {s t : PortSlot (G := G)}
    (hs : slotAt nd s) (ht : slotAt nd t)
    (he : slotEdge nd s = slotEdge nd t) : s = t := by
  rcases s with x | P <;> rcases t with y | Q
  · have hb : expandedBase x = expandedBase y :=
      shortPort_member_unique he
    exact congrArg Sum.inl (expandedBase_injective_at_old hs ht hb)
  · exfalso
    change shortPortEdge nd (expandedBase x) = longPortEdge Q at he
    have hc : (expandedBase x).1 = Q.1.1 := by
      apply Subtype.ext
      rw [← classPiece_class_eq G (shortPortEdge_mem nd (expandedBase x)),
        ← classPiece_class_eq G (longPortEdge_mem Q), he]
    have hslen := (expandedBase x).2.2
    have hqlen := Q.1.2.2
    rw [hc] at hslen
    omega
  · exfalso
    change longPortEdge P = shortPortEdge nd (expandedBase y) at he
    have hc : P.1.1 = (expandedBase y).1 := by
      apply Subtype.ext
      rw [← classPiece_class_eq G (longPortEdge_mem P),
        ← classPiece_class_eq G (shortPortEdge_mem nd (expandedBase y)), he]
    have hplen := P.1.2.2
    have hylen := (expandedBase y).2.2
    rw [hc] at hplen
    omega
  · exact congrArg Sum.inr (longPortEdge_injective he)

#print axioms slotEdge_spec
#print axioms slotEdge_injective_at

private noncomputable def slotsAt
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (nd : ShortMNode G) : Finset (PortSlot (G := G)) := by
  classical
  exact {s ∈ Finset.univ | slotAt nd s}

private lemma slotAt_card_le_four
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (nd : ShortMNode G) :
    #(slotsAt (G := G) nd) ≤ 4 := by
  classical
  calc
    #(slotsAt (G := G) nd)
        ≤ #{e ∈ G.incidenceFinset nd.1 |
          steeredGlueIx G nd.1 e = nd.2.1} := by
            apply card_le_card_of_injOn (slotEdge (G := G) nd)
            · intro s hs
              rw [slotsAt, mem_coe, mem_filter] at hs
              rw [mem_coe, mem_filter]
              exact ⟨(slotEdge_spec hs.2).1, (slotEdge_spec hs.2).2⟩
            · intro s hs t ht he
              rw [slotsAt, mem_coe, mem_filter] at hs ht
              exact slotEdge_injective_at hs.2 ht.2 he
    _ ≤ 4 := (steeredGlueIx_fiber_le nd.1 nd.2.1).1

#print axioms slotAt_card_le_four

/-- Once the two port colors and saturated sets are fixed, all long-chain
interiors can be filled simultaneously by independent choice per class. -/
private lemma exists_longChain_fills
    (p q : LongChain G → Fin 5)
    (hpq : ∀ Q : LongChain G,
      (classPiece G Q.1).walk.length = 3 → p Q ≠ q Q)
    (Fx Fy : LongChain G → Finset (Fin 5))
    (hFx : ∀ Q, #(Fx Q) ≤ 2) (hFy : ∀ Q, #(Fy Q) ≤ 2) :
    ∃ fill : LongChain G → ℕ → Fin 5,
      ∀ Q, IsFill (classPiece G Q.1).walk.length
        (p Q) (q Q) (Fx Q) (Fy Q) (fill Q) := by
  refine ⟨fun Q => (isFill_exists (C := Fin 5) (by decide) Q.2.2
    (p Q) (q Q) (hpq Q)
    (hFx Q) (hFy Q)).choose, ?_⟩
  intro Q
  exact (isFill_exists (C := Fin 5) (by decide) Q.2.2
    (p Q) (q Q) (hpq Q)
    (hFx Q) (hFy Q)).choose_spec

#print axioms exists_longChain_fills

/-! ### Bare-coloring pass (d): row-property discharge -/

/-- Junction-local properness is stronger than the rank-assembly
multiplicity requirement. This is the exact degree-4 handoff from the
Λ2-carried expanded-member coloring. -/
private lemma hmult_of_junction_injective (c : Sym2 V → Fin 5)
    (hinj : ∀ v : V, 3 ≤ G.degree v → ∀ f ∈ G.incidenceFinset v,
      ∀ g ∈ G.incidenceFinset v, c f = c g → f = g) :
    ∀ v : V, 3 ≤ G.degree v → ∀ α : Fin 5,
      #{f ∈ G.incidenceFinset v | c f = α} ≤ hfun 4 (G.degree v) := by
  intro v hv α
  have hone : #{f ∈ G.incidenceFinset v | c f = α} ≤ 1 := by
    rw [Finset.card_le_one]
    intro f hf g hg
    rw [Finset.mem_filter] at hf hg
    exact hinj v hv f hf.1 g hg.1 (hf.2.trans hg.2.symm)
  have hh : 1 ≤ hfun 4 (G.degree v) := by
    rw [hfun, if_neg (by omega)]
    omega
  exact le_trans hone hh

#print axioms hmult_of_junction_injective

/-! ### Generic finite first-fit traversal -/

/-- A finite port traversal in its exact reusable form.  A port may carry a
fixed forbidden palette, and it conflicts with the other ports selected by a
symmetric irreflexive relation.  If fixed colors plus all potential port
neighbours number at most four, five colors extend the partial coloring. -/
private lemma exists_firstFit_on_finset {A : Type*} [DecidableEq A]
    (S : Finset A) (fixed : A → Finset (Fin 5))
    (R : A → A → Prop) [DecidableRel R]
    (hsymm : ∀ a b, R a b → R b a) (hirr : ∀ a, ¬R a a)
    (hcap : ∀ a ∈ S, #(fixed a) + #{b ∈ S | R a b} ≤ 4) :
    ∃ color : A → Fin 5,
      (∀ a ∈ S, color a ∉ fixed a) ∧
      (∀ a ∈ S, ∀ b ∈ S, R a b → color a ≠ color b) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, by simp, by simp⟩
  | @insert a S ha ih =>
      have hcapS : ∀ x ∈ S, #(fixed x) + #{y ∈ S | R x y} ≤ 4 := by
        intro x hx
        have hbig := hcap x (Finset.mem_insert_of_mem hx)
        have hsub : {y ∈ S | R x y} ⊆ {y ∈ insert a S | R x y} := by
          intro y hy
          simp only [Finset.mem_filter] at hy ⊢
          exact ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩
        have hc := Finset.card_le_card hsub
        omega
      obtain ⟨color, hfixed, hproper⟩ := ih hcapS
      let used : Finset (Fin 5) :=
        fixed a ∪ ({b ∈ S | R a b}.image color)
      have hused : #used ≤ 4 := by
        change #(fixed a ∪ ({b ∈ S | R a b}.image color)) ≤ 4
        have hu := Finset.card_union_le (fixed a) ({b ∈ S | R a b}.image color)
        have hi : #({b ∈ S | R a b}.image color) ≤ #{b ∈ S | R a b} :=
          Finset.card_image_le
        have haCap := hcap a (Finset.mem_insert_self a S)
        have hnot : ¬R a a := hirr a
        simp only [Finset.filter_insert, hnot, ↓reduceIte] at haCap
        omega
      have hfree : usedᶜ.Nonempty := by
        rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
        omega
      obtain ⟨fresh, hfresh⟩ := hfree
      let color' := fun x => if x = a then fresh else color x
      refine ⟨color', ?_, ?_⟩
      · intro x hx
        by_cases hxa : x = a
        · subst x
          simp only [color', ↓reduceIte]
          exact fun hmem => (Finset.mem_compl.mp hfresh)
            (Finset.mem_union_left _ hmem)
        · have hxS : x ∈ S := (Finset.mem_insert.mp hx).resolve_left hxa
          simpa [color', hxa] using hfixed x hxS
      · intro x hx y hy hR
        by_cases hxa : x = a
        · subst x
          have hya : y ≠ a := fun h => by subst y; exact hirr a hR
          have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hya
          simp only [color', ↓reduceIte, hya]
          intro heq
          apply Finset.mem_compl.mp hfresh
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          exact ⟨y, Finset.mem_filter.mpr ⟨hyS, hR⟩, heq.symm⟩
        · have hxS : x ∈ S := (Finset.mem_insert.mp hx).resolve_left hxa
          by_cases hya : y = a
          · subst y
            simp only [color', hxa, ↓reduceIte]
            intro heq
            apply Finset.mem_compl.mp hfresh
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            exact ⟨x, Finset.mem_filter.mpr ⟨hxS, hsymm x a hR⟩, heq⟩
          · have hyS : y ∈ S := (Finset.mem_insert.mp hy).resolve_left hya
            simpa [color', hxa, hya] using hproper x hxS y hyS hR

#print axioms exists_firstFit_on_finset

private noncomputable def oldColorsAt
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5) (nd : ShortMNode G) :
    Finset (Fin 5) := by
  classical
  exact ({x ∈ (Finset.univ : Finset (ExpandedMember (G := G))) |
    (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x}).image col

private noncomputable def oldMembersAt
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (nd : ShortMNode G) : Finset (ExpandedMember (G := G)) := by
  classical
  exact {x ∈ Finset.univ |
    (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x}

private noncomputable def longPortsAt
    [Fintype (Quotient (linkSetoid G))] (nd : ShortMNode G) :
    Finset (LongPort G) := by
  classical
  exact {P ∈ Finset.univ | longPortNode P = nd}

private lemma slotsAt_card_eq
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (nd : ShortMNode G) :
    #(slotsAt (G := G) nd) = #(oldMembersAt (G := G) nd) +
      #(longPortsAt (G := G) nd) := by
  classical
  have heq : slotsAt (G := G) nd =
      (oldMembersAt (G := G) nd).disjSum (longPortsAt (G := G) nd) := by
    ext s
    rcases s with x | P
    · simp [slotsAt, slotAt, oldMembersAt, longPortsAt]
    · simp [slotsAt, slotAt, oldMembersAt, longPortsAt]
  rw [heq, Finset.card_disjSum]

private def longPortConflict (P Q : LongPort G) : Prop :=
  P ≠ Q ∧ (longPortNode P = longPortNode Q ∨
    ((classPiece G P.1.1).walk.length = 3 ∧ Q = longPortPartner P))

private lemma longPortConflict_symm {P Q : LongPort G}
    (h : longPortConflict P Q) : longPortConflict Q P := by
  rcases h with ⟨hne, hnode | ⟨hlen, hp⟩⟩
  · exact ⟨hne.symm, Or.inl hnode.symm⟩
  · subst Q
    refine ⟨longPortPartner_ne P, Or.inr ⟨?_, ?_⟩⟩
    · exact hlen
    · exact (longPortPartner_involutive P).symm

private lemma longPortConflict_irrefl (P : LongPort G) :
    ¬longPortConflict P P := fun h => h.1 rfl

private lemma slotColor_injective_at
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y)
    (portCol : LongPort G → Fin 5)
    (havoid : ∀ P, portCol P ∉ oldColorsAt col (longPortNode P))
    (hport : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q)
    {nd : ShortMNode G} {s t : PortSlot (G := G)}
    (hs : slotAt nd s) (ht : slotAt nd t)
    (hc : slotColor col portCol s = slotColor col portCol t) : s = t := by
  classical
  rcases s with x | P <;> rcases t with y | Q
  · apply congrArg Sum.inl
    by_contra hxy
    exact hcol x y hxy (Sum.inl nd) hs ht hc
  · exfalso
    apply havoid Q
    change (Sum.inl nd : ExpandedNode G) ∈ expandedMfam x at hs
    change longPortNode Q = nd at ht
    rw [ht]
    change col x = portCol Q at hc
    rw [← hc]
    apply Finset.mem_image.mpr
    exact ⟨x, by simp [oldMembersAt, hs], rfl⟩
  · exfalso
    apply havoid P
    change (Sum.inl nd : ExpandedNode G) ∈ expandedMfam y at ht
    change longPortNode P = nd at hs
    rw [hs]
    change portCol P = col y at hc
    rw [hc]
    apply Finset.mem_image.mpr
    exact ⟨y, by simp [oldMembersAt, ht], rfl⟩
  · apply congrArg Sum.inr
    by_contra hPQ
    exact hport P Q ⟨hPQ, Or.inl (hs.trans ht.symm)⟩ hc

private noncomputable def longPortConflicts
    [Fintype (Quotient (linkSetoid G))] (P : LongPort G) :
    Finset (LongPort G) := by
  classical
  exact {Q ∈ Finset.univ | longPortConflict P Q}

private lemma longPort_firstFit_cap
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5) (P : LongPort G) :
    #(oldColorsAt col (longPortNode P)) +
      #(longPortConflicts (G := G) P) ≤ 4 := by
  classical
  let nd := longPortNode P
  let old := oldMembersAt (G := G) nd
  let ports := longPortsAt (G := G) nd
  have hp : P ∈ ports := by
    simp [ports, longPortsAt, nd]
  have hportspos : 1 ≤ #ports := by
    have hpos : 0 < #ports := Finset.card_pos.mpr ⟨P, hp⟩
    omega
  have hslots := slotAt_card_le_four (G := G) nd
  have hsplit := slotsAt_card_eq (G := G) nd
  have htotal : #old + #ports ≤ 4 := by
    simpa [old, ports] using (show #(oldMembersAt (G := G) nd) +
      #(longPortsAt (G := G) nd) ≤ 4 by omega)
  have hfixed : #(oldColorsAt col nd) ≤ #old := by
    change #((oldMembersAt (G := G) nd).image col) ≤
      #(oldMembersAt (G := G) nd)
    exact Finset.card_image_le
  have herase : #(ports.erase P) = #ports - 1 := by
    rw [Finset.card_erase_of_mem hp]
  have hbase : #(oldColorsAt col nd) + #(ports.erase P) ≤ 3 := by
    dsimp only [old, ports] at htotal hfixed herase hportspos ⊢
    omega
  have hsub : longPortConflicts (G := G) P ⊆
      ports.erase P ∪ {longPortPartner P} := by
    intro Q hQ
    rw [longPortConflicts, Finset.mem_filter] at hQ
    rcases hQ.2 with ⟨hne, hnode | ⟨hlen, hpartner⟩⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_erase]
      exact ⟨hne.symm, by simp [ports, longPortsAt, nd, hnode]⟩
    · apply Finset.mem_union_right
      simp [hpartner]
  have hconf : #(longPortConflicts (G := G) P) ≤ #(ports.erase P) + 1 := by
    calc
      _ ≤ #(ports.erase P ∪ {longPortPartner P}) := Finset.card_le_card hsub
      _ ≤ #(ports.erase P) + #({longPortPartner P} : Finset (LongPort G)) :=
        Finset.card_union_le _ _
      _ = #(ports.erase P) + 1 := by simp
  change #(oldColorsAt col nd) +
    #(longPortConflicts (G := G) P) ≤ 4
  omega

private lemma exists_longPort_assignment
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5) :
    ∃ portColor : LongPort G → Fin 5,
      (∀ P, portColor P ∉ oldColorsAt col (longPortNode P)) ∧
      (∀ P Q, longPortConflict P Q → portColor P ≠ portColor Q) := by
  classical
  obtain ⟨c, hfixed, hproper⟩ := exists_firstFit_on_finset
    (Finset.univ : Finset (LongPort G)) (fun P => oldColorsAt col (longPortNode P))
    longPortConflict (fun _ _ => longPortConflict_symm) longPortConflict_irrefl
    (fun P _ => by simpa [longPortConflicts] using longPort_firstFit_cap col P)
  exact ⟨c, fun P => hfixed P (Finset.mem_univ P),
    fun P Q h => hproper P (Finset.mem_univ P) Q (Finset.mem_univ Q) h⟩

#print axioms longPortConflict_symm
#print axioms longPortConflict_irrefl
#print axioms longPort_firstFit_cap
#print axioms exists_longPort_assignment

private noncomputable def portStageClassColor
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (q : EdgeClass G) (i : ℕ) : Fin 5 :=
  if hcyc : (classPiece G q).IsCycle then 0
  else if hlong : 3 ≤ (classPiece G q).walk.length then
    if i = 0 then portCol (⟨q, hcyc, hlong⟩, false)
    else portCol (⟨q, hcyc, hlong⟩, true)
  else shortPortColor memberCol
    ⟨q, hcyc, Nat.lt_of_not_ge hlong⟩ (decide (i ≠ 0))

private noncomputable def portStageColor
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (e : Sym2 V) : Fin 5 :=
  if he : e ∈ G.edgeSet then
    portStageClassColor memberCol portCol (edgeClassOf G he)
      ((classPiece G (edgeClassOf G he)).walk.edges.idxOf e)
  else 0

private noncomputable def longFx
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (Q : LongChain G) : Finset (Fin 5) :=
  if 3 ≤ G.degree (classPiece G Q.1).a then
    satSet G (portStageColor memberCol portCol)
      (classPiece G Q.1).a (classPiece G Q.1).walk.snd
  else ∅

private noncomputable def longFy
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (Q : LongChain G) : Finset (Fin 5) :=
  if 3 ≤ G.degree (classPiece G Q.1).b then
    satSet G (portStageColor memberCol portCol)
      (classPiece G Q.1).b (classPiece G Q.1).walk.penultimate
  else ∅

private lemma longFx_card_le
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (Q : LongChain G) :
    #(longFx memberCol portCol Q) ≤ 2 := by
  unfold longFx
  split_ifs with h
  · have hadj : G.Adj (classPiece G Q.1).a (classPiece G Q.1).walk.snd :=
      G.mem_edgeSet.mp ((classPiece G Q.1).walk.edges_subset_edgeSet
        (classPiece G Q.1).firstEdge_mem)
    exact card_satSet_le_two hadj (by omega)
  · simp

private lemma longFy_card_le
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (Q : LongChain G) :
    #(longFy memberCol portCol Q) ≤ 2 := by
  unfold longFy
  split_ifs with h
  · have hadj : G.Adj (classPiece G Q.1).walk.penultimate
        (classPiece G Q.1).b :=
      G.mem_edgeSet.mp ((classPiece G Q.1).walk.edges_subset_edgeSet
        (classPiece G Q.1).lastEdge_mem)
    exact card_satSet_le_two hadj.symm (by omega)
  · simp

private lemma exists_fills_of_longPort_assignment
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5)
    (hproper : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q) :
    ∃ fill : LongChain G → ℕ → Fin 5,
      ∀ Q, IsFill (classPiece G Q.1).walk.length
        (portCol (Q, false)) (portCol (Q, true))
        (longFx memberCol portCol Q) (longFy memberCol portCol Q) (fill Q) := by
  apply exists_longChain_fills
    (p := fun Q => portCol (Q, false))
    (q := fun Q => portCol (Q, true))
    (Fx := fun Q => longFx memberCol portCol Q)
    (Fy := fun Q => longFy memberCol portCol Q)
  · intro Q hlen
    apply hproper (Q, false) (Q, true)
    refine ⟨by simp, Or.inr ⟨hlen, ?_⟩⟩
    rfl
  · exact longFx_card_le memberCol portCol
  · exact longFy_card_le memberCol portCol

#print axioms portStageColor
#print axioms longFx_card_le
#print axioms longFy_card_le
#print axioms exists_fills_of_longPort_assignment

/-! ### Total coloring dispatcher (definition before invariants) -/

private abbrev CycleClass (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {q : EdgeClass G // (classPiece G q).IsCycle}

private lemma exists_cycleClass_patterns :
    ∃ cyc : CycleClass G → ℕ → Fin 5,
      ∀ Q : CycleClass G, ∀ i < (classPiece G Q.1).walk.length,
        cyc Q i ≠ cyc Q ((i + 2) % (classPiece G Q.1).walk.length) := by
  classical
  refine ⟨fun Q => (exists_cycle_distance2_five
    (classPiece G Q.1).walk.length
    ((classPiece G Q.1).three_le_length_of_cycle Q.2)).choose, ?_⟩
  intro Q
  exact (exists_cycle_distance2_five (classPiece G Q.1).walk.length
    ((classPiece G Q.1).three_le_length_of_cycle Q.2)).choose_spec

/-- One total graph-edge coloring, dispatched through the canonical linkage
class and the edge's slot in its chosen piece. All later invariants refer to
this single definition. -/
private noncomputable def assembledClassColor
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (fill : LongChain G → ℕ → Fin 5)
    (cycle : CycleClass G → ℕ → Fin 5)
    (q : EdgeClass G) (i : ℕ) : Fin 5 :=
  if hcyc : (classPiece G q).IsCycle then cycle ⟨q, hcyc⟩ i
  else if hlong : 3 ≤ (classPiece G q).walk.length then
    fill ⟨q, hcyc, hlong⟩ i
  else shortPortColor memberCol
    ⟨q, hcyc, Nat.lt_of_not_ge hlong⟩ (decide (i ≠ 0))

private noncomputable def assembledColor
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (fill : LongChain G → ℕ → Fin 5)
    (cycle : CycleClass G → ℕ → Fin 5)
    (e : Sym2 V) : Fin 5 :=
  if he : e ∈ G.edgeSet then
    assembledClassColor memberCol fill cycle (edgeClassOf G he)
      ((classPiece G (edgeClassOf G he)).walk.edges.idxOf e)
  else 0

private lemma portStageColor_eq_class
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) {q : EdgeClass G} {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hm : e ∈ (classPiece G q).walk.edges) :
    portStageColor memberCol portCol e = portStageClassColor memberCol portCol q
      ((classPiece G q).walk.edges.idxOf e) := by
  unfold portStageColor
  rw [dif_pos he, edgeClassOf_eq G he hm]

private lemma assembledColor_eq_class
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (fill : LongChain G → ℕ → Fin 5) (cycle : CycleClass G → ℕ → Fin 5)
    {q : EdgeClass G} {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hm : e ∈ (classPiece G q).walk.edges) :
    assembledColor memberCol fill cycle e = assembledClassColor memberCol fill cycle q
      ((classPiece G q).walk.edges.idxOf e) := by
  unfold assembledColor
  rw [dif_pos he, edgeClassOf_eq G he hm]

private lemma portStageColor_first_long
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (Q : LongChain G) :
    portStageColor memberCol portCol (classPiece G Q.1).firstEdge =
      portCol (Q, false) := by
  have hm := (classPiece G Q.1).firstEdge_mem
  have he := (classPiece G Q.1).walk.edges_subset_edgeSet hm
  unfold portStageColor
  rw [dif_pos he, edgeClassOf_eq G he hm, idxOf_firstEdge]
  unfold portStageClassColor
  rw [dif_neg Q.2.1, dif_pos Q.2.2, if_pos]
  rfl

private lemma portStageColor_last_long
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (portCol : LongPort G → Fin 5) (Q : LongChain G) :
    portStageColor memberCol portCol (classPiece G Q.1).lastEdge =
      portCol (Q, true) := by
  have hm := (classPiece G Q.1).lastEdge_mem
  have he := (classPiece G Q.1).walk.edges_subset_edgeSet hm
  unfold portStageColor
  rw [dif_pos he, edgeClassOf_eq G he hm, idxOf_lastEdge]
  unfold portStageClassColor
  rw [dif_neg Q.2.1, dif_pos Q.2.2, if_neg]
  have := (classPiece G Q.1).walk.length_edges
  omega

private lemma portStageColor_first_short
    [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (portCol : LongPort G → Fin 5)
    (m : ShortMember G) :
    portStageColor col portCol (classPiece G m.1).firstEdge =
      shortPortColor col m false := by
  have hm := (classPiece G m.1).firstEdge_mem
  have he := (classPiece G m.1).walk.edges_subset_edgeSet hm
  rw [portStageColor_eq_class col portCol he hm, idxOf_firstEdge]
  unfold portStageClassColor
  rw [dif_neg m.2.1, dif_neg (by omega), show decide (0 ≠ 0) = false by decide]

private lemma portStageColor_last_short
    [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (portCol : LongPort G → Fin 5)
    (m : ShortMember G) (hm2 : (classPiece G m.1).walk.length = 2) :
    portStageColor col portCol (classPiece G m.1).lastEdge =
      shortPortColor col m true := by
  have hm := (classPiece G m.1).lastEdge_mem
  have he := (classPiece G m.1).walk.edges_subset_edgeSet hm
  rw [portStageColor_eq_class col portCol he hm, idxOf_lastEdge]
  unfold portStageClassColor
  rw [dif_neg m.2.1, dif_neg (by omega)]
  have hlen := (classPiece G m.1).walk.length_edges
  simp [hm2] at hlen ⊢

private lemma assembledColor_first_long
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (fill : LongChain G → ℕ → Fin 5) (cycle : CycleClass G → ℕ → Fin 5)
    (Q : LongChain G) :
    assembledColor memberCol fill cycle (classPiece G Q.1).firstEdge = fill Q 0 := by
  have hm := (classPiece G Q.1).firstEdge_mem
  have he := (classPiece G Q.1).walk.edges_subset_edgeSet hm
  unfold assembledColor
  rw [dif_pos he, edgeClassOf_eq G he hm, idxOf_firstEdge]
  unfold assembledClassColor
  rw [dif_neg Q.2.1, dif_pos Q.2.2]

private lemma assembledColor_last_long
    [Fintype (ShortMember G)]
    (memberCol : ExpandedMember (G := G) → Fin 5)
    (fill : LongChain G → ℕ → Fin 5) (cycle : CycleClass G → ℕ → Fin 5)
    (Q : LongChain G) :
    assembledColor memberCol fill cycle (classPiece G Q.1).lastEdge =
      fill Q ((classPiece G Q.1).walk.length - 1) := by
  have hm := (classPiece G Q.1).lastEdge_mem
  have he := (classPiece G Q.1).walk.edges_subset_edgeSet hm
  unfold assembledColor
  rw [dif_pos he, edgeClassOf_eq G he hm, idxOf_lastEdge]
  unfold assembledClassColor
  rw [dif_neg Q.2.1, dif_pos Q.2.2]
  congr 2
  rw [(classPiece G Q.1).walk.length_edges]

#print axioms exists_cycleClass_patterns
#print axioms assembledColor
#print axioms portStageColor_first_long
#print axioms portStageColor_last_long
#print axioms assembledColor_first_long
#print axioms assembledColor_last_long

private lemma assembledColor_eq_portStage_at_junction
    [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (portCol : LongPort G → Fin 5)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5) {e : Sym2 V} (he : e ∈ G.edgeSet)
    {v : V} (hv : v ∈ e) (hdv : G.degree v ≠ 2) :
    assembledColor col fill cycle e = portStageColor col portCol e := by
  let q : EdgeClass G := edgeClassOf G he
  have hm : e ∈ (classPiece G q).walk.edges := mem_pieceOf G he
  have hvsup : v ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.mem_support_of_mem_edges hm hv
  have hnc : ¬(classPiece G q).IsCycle := by
    intro hc
    exact hdv (((classPiece G q).cycle_spec hc).2 v hvsup)
  by_cases hl : 3 ≤ (classPiece G q).walk.length
  · let Q : LongChain G := ⟨q, hnc, hl⟩
    rcases (classPiece G q).piece.eq_first_or_last hm hv hdv with hs | he'
    · have hedge : e = (classPiece G q).firstEdge := by
        simpa [Piece.firstEdge] using hs.2
      rw [hedge]
      rw [assembledColor_first_long col fill cycle Q,
        portStageColor_first_long col portCol Q, (hfill Q).1]
    · have hedge : e = (classPiece G q).lastEdge := by
        simpa [Piece.lastEdge] using he'.2
      rw [hedge]
      rw [assembledColor_last_long col fill cycle Q,
        portStageColor_last_long col portCol Q, (hfill Q).2.1]
  · rw [assembledColor_eq_class col fill cycle he hm,
      portStageColor_eq_class col portCol he hm]
    unfold assembledClassColor portStageClassColor
    rw [dif_neg hnc, dif_neg hl, dif_neg hnc, dif_neg hl]

private lemma satSet_assembledColor_eq_portStage
    [Fintype (ShortMember G)]
    (col : ExpandedMember (G := G) → Fin 5) (portCol : LongPort G → Fin 5)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5) {x w : V} (hdx : G.degree x ≠ 2) :
    satSet G (assembledColor col fill cycle) x w =
      satSet G (portStageColor col portCol) x w := by
  have hside : ∀ α : Fin 5,
      {f ∈ side G x w | assembledColor col fill cycle f = α} =
        {f ∈ side G x w | portStageColor col portCol f = α} := by
    intro α
    apply filter_congr
    intro f hf
    have hf2 : f ∈ G.incidenceSet x := (mem_side.mp hf).2
    rw [assembledColor_eq_portStage_at_junction col portCol fill hfill cycle
      hf2.1 hf2.2 hdx]
  unfold satSet
  apply filter_congr
  intro α _
  rw [hside α]

private lemma exists_slot_of_junction_edge
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5) (portCol : LongPort G → Fin 5)
    {v : V} {e : Sym2 V} (he : e ∈ G.incidenceFinset v) (hdv : G.degree v ≠ 2) :
    ∃ s : PortSlot (G := G),
      slotAt (steeredNodeAt G v e) s ∧
      slotEdge (steeredNodeAt G v e) s = e ∧
      slotColor col portCol s = portStageColor col portCol e := by
  classical
  have heG := (mem_incFinset.mp he).1
  have hve := (mem_incFinset.mp he).2
  let q : EdgeClass G := edgeClassOf G heG
  have hm : e ∈ (classPiece G q).walk.edges := mem_pieceOf G heG
  have hvsup : v ∈ (classPiece G q).walk.support :=
    (classPiece G q).walk.mem_support_of_mem_edges hm hve
  have hnc : ¬(classPiece G q).IsCycle := by
    intro hc
    exact hdv (((classPiece G q).cycle_spec hc).2 v hvsup)
  rcases (classPiece G q).piece.eq_first_or_last hm hve hdv with hs | he'
  · have hedge : e = (classPiece G q).firstEdge := by
      simpa [Piece.firstEdge] using hs.2
    by_cases hl : 3 ≤ (classPiece G q).walk.length
    · let Q : LongChain G := ⟨q, hnc, hl⟩
      refine ⟨Sum.inr (Q, false), ?_, ?_, ?_⟩
      · dsimp [slotAt, longPortNode, Q, shortStartNode]
        rw [hs.1, hedge]
      · dsimp [slotEdge, longPortEdge, Q]
        exact hedge.symm
      · change portCol (Q, false) = _
        rw [hedge, portStageColor_first_long col portCol Q]
    · let m : ShortMember G := ⟨q, hnc, by omega⟩
      by_cases hc : IsChosenCherry (G := G) m
      · let z := cherryExpanded m false hc
        refine ⟨Sum.inl z, ?_, ?_, ?_⟩
        · dsimp [slotAt, z, cherryExpanded, expandedMfam, m, shortStartNode]
          have hnd : steeredNodeAt G v e = shortStartNode (G := G) q := by
            rw [hs.1, hedge]
            rfl
          rw [hnd]
          exact Sym2.mem_mk_left _ _
        · dsimp [slotEdge, z, cherryExpanded, expandedBase, shortPortEdge, m]
          have hnd : shortStartNode (G := G) q = steeredNodeAt G v e := by
            rw [hs.1, hedge]
            rfl
          rw [if_pos hnd]
          exact hedge.symm
        · change col z = _
          rw [hedge, portStageColor_first_short col portCol m,
            shortPortColor_cherry col m hc false]
      · let z := retainedExpanded m hc
        refine ⟨Sum.inl z, ?_, ?_, ?_⟩
        · dsimp [slotAt, z, retainedExpanded, expandedMfam, m, shortStartNode]
          have hnd : steeredNodeAt G v e = shortStartNode (G := G) q := by
            rw [hs.1, hedge]
            rfl
          rw [hnd]
          exact Sym2.mem_mk_left _ _
        · dsimp [slotEdge, z, retainedExpanded, expandedBase, shortPortEdge, m]
          have hnd : shortStartNode (G := G) q = steeredNodeAt G v e := by
            rw [hs.1, hedge]
            rfl
          rw [if_pos hnd]
          exact hedge.symm
        · change col z = _
          rw [hedge, portStageColor_first_short col portCol m]
          simp [shortPortColor, hc, z, retainedExpanded]
  · have hedge : e = (classPiece G q).lastEdge := by
      simpa [Piece.lastEdge] using he'.2
    by_cases hl : 3 ≤ (classPiece G q).walk.length
    · let Q : LongChain G := ⟨q, hnc, hl⟩
      refine ⟨Sum.inr (Q, true), ?_, ?_, ?_⟩
      · dsimp [slotAt, longPortNode, Q, shortEndNode]
        rw [he'.1, hedge]
      · dsimp [slotEdge, longPortEdge, Q]
        exact hedge.symm
      · change portCol (Q, true) = _
        rw [hedge, portStageColor_last_long col portCol Q]
    · let m : ShortMember G := ⟨q, hnc, by omega⟩
      by_cases hc : IsChosenCherry (G := G) m
      · have hm2 := chosenCherry_length_two hc
        let z := cherryExpanded m true hc
        refine ⟨Sum.inl z, ?_, ?_, ?_⟩
        · dsimp [slotAt, z, cherryExpanded, expandedMfam]
          change (Sum.inl (steeredNodeAt G v e) : ExpandedNode G) ∈
            s((Sum.inr m : ExpandedNode G), Sum.inl (shortEndNode (G := G) m.1))
          rw [he'.1, hedge]
          exact Sym2.mem_mk_right _ _
        · dsimp [slotEdge, z, cherryExpanded, expandedBase, shortPortEdge]
          have hne : shortStartNode (G := G) m.1 ≠ steeredNodeAt G v e := by
            rw [he'.1, hedge]
            exact shortStartNode_ne_endNode m
          rw [if_neg hne]
          dsimp [m]
          exact hedge.symm
        · change col z = _
          rw [hedge, portStageColor_last_short col portCol m hm2,
            shortPortColor_cherry col m hc true]
      · let z := retainedExpanded m hc
        refine ⟨Sum.inl z, ?_, ?_, ?_⟩
        · dsimp [slotAt, z, retainedExpanded, expandedMfam]
          change (Sum.inl (steeredNodeAt G v e) : ExpandedNode G) ∈
            s((Sum.inl (shortStartNode (G := G) m.1) : ExpandedNode G),
              Sum.inl (shortEndNode (G := G) m.1))
          rw [he'.1, hedge]
          exact Sym2.mem_mk_right _ _
        · dsimp [slotEdge, z, retainedExpanded, expandedBase, shortPortEdge]
          have hne : shortStartNode (G := G) m.1 ≠ steeredNodeAt G v e := by
            rw [he'.1, hedge]
            exact shortStartNode_ne_endNode m
          rw [if_neg hne]
          dsimp [m]
          exact hedge.symm
        · change col z = _
          rw [hedge]
          have hmemb := (classPiece G m.1).lastEdge_mem
          have hemb := (classPiece G m.1).walk.edges_subset_edgeSet hmemb
          rw [portStageColor_eq_class col portCol hemb hmemb]
          unfold portStageClassColor
          rw [dif_neg m.2.1, dif_neg (by omega)]
          simp [shortPortColor, hc, z, retainedExpanded]

private theorem assembledColor_hmult
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y)
    (portCol : LongPort G → Fin 5)
    (havoid : ∀ P, portCol P ∉ oldColorsAt col (longPortNode P))
    (hport : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5) :
    ∀ v : V, 3 ≤ G.degree v → ∀ α : Fin 5,
      #{f ∈ G.incidenceFinset v |
        assembledColor col fill cycle f = α} ≤ hfun 4 (G.degree v) := by
  intro v hv α
  calc
    #{f ∈ G.incidenceFinset v | assembledColor col fill cycle f = α}
        ≤ #((G.incidenceFinset v).image (steeredGlueIx G v)) := by
      apply card_le_card_of_injOn (steeredGlueIx G v)
      · intro f hf
        rw [mem_coe, mem_filter] at hf
        exact mem_coe.mpr (Finset.mem_image_of_mem _ hf.1)
      · intro f hf g hg hix
        rw [mem_coe, mem_filter] at hf hg
        obtain ⟨sf, hsf, hef, hcf⟩ := exists_slot_of_junction_edge col portCol
          hf.1 (by omega)
        obtain ⟨sg, hsg, heg, hcg⟩ := exists_slot_of_junction_edge col portCol
          hg.1 (by omega)
        have hnd : steeredNodeAt G v f = steeredNodeAt G v g := by
          rw [steeredNodeAt_eq_iff]
          exact ⟨rfl, hix⟩
        have hsg' : slotAt (steeredNodeAt G v f) sg := by rwa [hnd]
        have hacf := assembledColor_eq_portStage_at_junction col portCol fill hfill cycle
          (mem_incFinset.mp hf.1).1 (mem_incFinset.mp hf.1).2 (by omega)
        have hacg := assembledColor_eq_portStage_at_junction col portCol fill hfill cycle
          (mem_incFinset.mp hg.1).1 (mem_incFinset.mp hg.1).2 (by omega)
        have hcslot : slotColor col portCol sf = slotColor col portCol sg := by
          rw [hcf, hcg, ← hacf, ← hacg, hf.2, hg.2]
        have hst := slotColor_injective_at col hcol portCol havoid hport hsf hsg' hcslot
        rw [← hef, ← heg, hnd, hst]
    _ = groups G (steeredGlueIx G) v := by
      rw [groups, if_neg (by omega)]
    _ ≤ hfun 4 (G.degree v) := groups_steeredGlueIx_le hv

private theorem assembledColor_hint
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y)
    (portCol : LongPort G → Fin 5)
    (havoid : ∀ P, portCol P ∉ oldColorsAt col (longPortNode P))
    (hport : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5)
    (hcycle : ∀ Q : CycleClass G, ∀ i < (classPiece G Q.1).walk.length,
      cycle Q i ≠ cycle Q ((i + 2) % (classPiece G Q.1).walk.length)) :
    ∀ u v : V, G.Adj u v → G.degree u = 2 → G.degree v = 2 →
      ∀ f ∈ side G u v, ∀ g ∈ side G v u,
        assembledColor col fill cycle f ≠ assembledColor col fill cycle g := by
  intro u v huv hdu hdv f hf g hg
  have he : s(u, v) ∈ G.edgeSet := G.mem_edgeSet.mpr huv
  let q : EdgeClass G := edgeClassOf G he
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
      (classPiece G q).walk.edges.length := List.idxOf_lt_length_of_mem hmem
  let i := (classPiece G q).walk.edges.idxOf s(u, v)
  have hei : (classPiece G q).walk.edges[i] = s(u, v) := List.getElem_idxOf hi
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
  · have h3L : 3 ≤ (classPiece G q).walk.edges.length := by
      rw [(classPiece G q).walk.length_edges]
      exact (classPiece G q).three_le_length_of_cycle hcyc
    have hfslot := (classPiece G q).cycle_slot hcyc hi
      (by rw [hei]; exact Sym2.mem_mk_left u v) hfP hfside.2.2
      (by rw [hei]; exact hfside.1)
    have hgslot := (classPiece G q).cycle_slot hcyc hi
      (by rw [hei]; exact Sym2.mem_mk_right u v) hgP hgside.2.2
      (by rw [hei, Sym2.eq_swap]; exact hgside.1)
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
        assembledColor col fill cycle h = cycle ⟨q, hcyc⟩ j := by
      intro h hhP hhe j hj hh
      rw [assembledColor_eq_class col fill cycle hhe hhP,
        idxOf_eq_of_getElem hnd hj hh.symm]
      unfold assembledClassColor
      rw [dif_pos hcyc]
    rcases hor with ⟨hu, hv'⟩ | ⟨hu, hv'⟩
    · obtain ⟨hj1, hf1⟩ : ∃ h : _, f = (classPiece G q).walk.edges[
          (i + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length] := by
        rcases hfslot with ⟨-, hh⟩ | ⟨hc, -⟩
        · exact hh
        · exact absurd (hu.symm.trans hc) hgv_ne
      obtain ⟨hj2, hg1⟩ : ∃ h : _, g = (classPiece G q).walk.edges[
          (i + 1) % (classPiece G q).walk.edges.length] := by
        rcases hgslot with ⟨hc, -⟩ | ⟨-, hh⟩
        · exact absurd (hv'.symm.trans hc) hgv_ne.symm
        · exact hh
      rw [hcolor hfP hfe hj1 hf1, hcolor hgP hge hj2 hg1]
      have hs := hcycle ⟨q, hcyc⟩
        ((i + (classPiece G q).walk.edges.length - 1) %
          (classPiece G q).walk.edges.length)
        (by rw [← (classPiece G q).walk.length_edges]; exact Nat.mod_lt _ (by omega))
      rw [← (classPiece G q).walk.length_edges, harith i] at hs
      exact hs
    · obtain ⟨hj1, hf1⟩ : ∃ h : _, f = (classPiece G q).walk.edges[
          (i + 1) % (classPiece G q).walk.edges.length] := by
        rcases hfslot with ⟨hc, -⟩ | ⟨-, hh⟩
        · exact absurd (hu.symm.trans hc) hgv_ne.symm
        · exact hh
      obtain ⟨hj2, hg1⟩ : ∃ h : _, g = (classPiece G q).walk.edges[
          (i + (classPiece G q).walk.edges.length - 1) %
            (classPiece G q).walk.edges.length] := by
        rcases hgslot with ⟨-, hh⟩ | ⟨hc, -⟩
        · exact hh
        · exact absurd (hv'.symm.trans hc) hgv_ne
      rw [hcolor hfP hfe hj1 hf1, hcolor hgP hge hj2 hg1]
      have hs := hcycle ⟨q, hcyc⟩
        ((i + (classPiece G q).walk.edges.length - 1) %
          (classPiece G q).walk.edges.length)
        (by rw [← (classPiece G q).walk.length_edges]; exact Nat.mod_lt _ (by omega))
      rw [← (classPiece G q).walk.length_edges, harith i] at hs
      exact hs.symm
  · have hends := (classPiece G q).chain_ends hcyc
    have hLe := (classPiece G q).walk.length_edges
    have hfslot := (classPiece G q).piece.other_edge_slot_of_chain
      hends.1 hends.2 hi (by rw [hei]; exact Sym2.mem_mk_left u v) hdu
      hfP hfside.2.2 (by rw [hei]; exact hfside.1)
    have hgslot := (classPiece G q).piece.other_edge_slot_of_chain
      hends.1 hends.2 hi (by rw [hei]; exact Sym2.mem_mk_right u v) hdv
      hgP hgside.2.2 (by rw [hei, Sym2.eq_swap]; exact hgside.1)
    rcases hor with ⟨hu, hv'⟩ | ⟨hu, hv'⟩
    · have h0 : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        have hua : u = (classPiece G q).a := by rw [hu, hi0, Walk.getVert_zero]
        exact hends.1 (hua ▸ hdu)
      have hilen : i + 1 < (classPiece G q).walk.edges.length := by
        by_contra h
        have hieq : i + 1 = (classPiece G q).walk.length := by omega
        have hvb : v = (classPiece G q).b := by rw [hv', hieq, Walk.getVert_length]
        exact hends.2 (hvb ▸ hdv)
      have h3 : 3 ≤ (classPiece G q).walk.length := by omega
      let Q : LongChain G := ⟨q, hcyc, h3⟩
      obtain ⟨hj1, hf1⟩ : ∃ h : i - 1 <
          (classPiece G q).walk.edges.length,
          f = (classPiece G q).walk.edges[i - 1] := by
        rcases hfslot with ⟨-, -, hh⟩ | ⟨hc, -⟩
        · exact hh
        · exact absurd (hu.symm.trans hc) hgv_ne
      obtain ⟨hj2, hg1⟩ : ∃ h : i + 1 <
          (classPiece G q).walk.edges.length,
          g = (classPiece G q).walk.edges[i + 1] := by
        rcases hgslot with ⟨hc, -⟩ | ⟨-, hh⟩
        · exact absurd (hv'.symm.trans hc) hgv_ne.symm
        · exact hh
      rw [assembledColor_eq_class col fill cycle hfe hfP,
        idxOf_eq_of_getElem hnd hj1 hf1.symm,
        assembledColor_eq_class col fill cycle hge hgP,
        idxOf_eq_of_getElem hnd hj2 hg1.symm]
      unfold assembledClassColor
      rw [dif_neg hcyc, dif_pos h3, dif_neg hcyc, dif_pos h3]
      have hbound : i - 1 + 2 ≤ (classPiece G Q.1).walk.length - 1 := by
        change i - 1 + 2 ≤ (classPiece G q).walk.length - 1
        omega
      have hfa := (hfill Q).2.2.1 (i - 1) hbound
      rwa [show i - 1 + 2 = i + 1 by omega] at hfa
    · have h0 : 0 < i := by
        by_contra h
        have hi0 : i = 0 := by omega
        have hva : v = (classPiece G q).a := by rw [hv', hi0, Walk.getVert_zero]
        exact hends.1 (hva ▸ hdv)
      have hilen : i + 1 < (classPiece G q).walk.edges.length := by
        by_contra h
        have hieq : i + 1 = (classPiece G q).walk.length := by omega
        have hub : u = (classPiece G q).b := by rw [hu, hieq, Walk.getVert_length]
        exact hends.2 (hub ▸ hdu)
      have h3 : 3 ≤ (classPiece G q).walk.length := by omega
      let Q : LongChain G := ⟨q, hcyc, h3⟩
      obtain ⟨hj1, hf1⟩ : ∃ h : i + 1 <
          (classPiece G q).walk.edges.length,
          f = (classPiece G q).walk.edges[i + 1] := by
        rcases hfslot with ⟨hc, -⟩ | ⟨-, hh⟩
        · exact absurd (hu.symm.trans hc) hgv_ne.symm
        · exact hh
      obtain ⟨hj2, hg1⟩ : ∃ h : i - 1 <
          (classPiece G q).walk.edges.length,
          g = (classPiece G q).walk.edges[i - 1] := by
        rcases hgslot with ⟨-, -, hh⟩ | ⟨hc, -⟩
        · exact hh
        · exact absurd (hv'.symm.trans hc) hgv_ne
      rw [assembledColor_eq_class col fill cycle hfe hfP,
        idxOf_eq_of_getElem hnd hj1 hf1.symm,
        assembledColor_eq_class col fill cycle hge hgP,
        idxOf_eq_of_getElem hnd hj2 hg1.symm]
      unfold assembledClassColor
      rw [dif_neg hcyc, dif_pos h3, dif_neg hcyc, dif_pos h3]
      have hbound : i - 1 + 2 ≤ (classPiece G Q.1).walk.length - 1 := by
        change i - 1 + 2 ≤ (classPiece G q).walk.length - 1
        omega
      have hfa := (hfill Q).2.2.1 (i - 1) hbound
      rw [show i - 1 + 2 = i + 1 by omega] at hfa
      exact hfa.symm

private lemma chosenCherry_endpoint_not_special
    [Fintype (ShortMember G)] (m : ShortMember G)
    (hc : IsChosenCherry (G := G) m) {v : V} {k : Fin (Fintype.card V + 1)}
    (hnd : (v, k) ∈ shortMfam m) : G.degree v ≠ 3 ∧ G.degree v ≠ 5 := by
  classical
  obtain ⟨hbad, hm⟩ := hc
  rcases hbad with ⟨a, b, he, hμ, hfail⟩
  have htab := bad_parallel_table (G := G) hμ hfail
  have hdegM : mdeg (shortMult (G := G)) (v, k) = 4 := by
    rw [he] at hnd
    rcases Sym2.mem_iff.mp hnd with ha | hb
    · rw [ha]
      exact htab.1
    · rw [hb]
      exact htab.2.1
  have hcount : #{m ∈ (Finset.univ : Finset (ShortMember G)) |
      (v, k) ∈ shortMfam m} = 4 := by
    rw [← hdegM]
    change _ = mdeg (famMatrix (shortMfam (G := G))) (v, k)
    rw [mdeg_famMatrix (shortMfam (G := G)) shortMfam_not_isDiag]
  have htofiber : #{m ∈ (Finset.univ : Finset (ShortMember G)) |
      (v, k) ∈ shortMfam m} ≤
      #{f ∈ G.incidenceFinset v | steeredGlueIx G v f = k.1} := by
    apply card_le_card_of_injOn (shortPortEdge (G := G) (v, k))
    · intro m hm
      rw [mem_coe, mem_filter] at hm
      rw [mem_coe, mem_filter]
      exact shortPortEdge_spec hm.2
    · intro m hm m' hm' heq
      exact shortPort_member_unique heq
  constructor <;> intro hd
  · have hf := (steeredGlueIx_fiber_le v k.1).2 (Or.inl hd)
    omega
  · have hf := (steeredGlueIx_fiber_le v k.1).2 (Or.inr hd)
    omega

private lemma assembledColor_rainbow_steered
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y)
    (portCol : LongPort G → Fin 5)
    (havoid : ∀ P, portCol P ∉ oldColorsAt col (longPortNode P))
    (hport : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5) :
    IsRainbow G (steeredGlueIx G) (assembledColor col fill cycle) := by
  intro v f hf g hg hix hc
  by_contra hfg
  have hdv : G.degree v ≠ 2 := by
    intro hd
    exact hfg (steeredGlueIx_inj_low (G := G) (by omega) hf hg hix)
  obtain ⟨sf, hsf, hef, hcf⟩ := exists_slot_of_junction_edge col portCol hf
    hdv
  obtain ⟨sg, hsg, heg, hcg⟩ := exists_slot_of_junction_edge col portCol hg
    hdv
  have hnd : steeredNodeAt G v f = steeredNodeAt G v g := by
    rw [steeredNodeAt_eq_iff]
    exact ⟨rfl, hix⟩
  have hsg' : slotAt (steeredNodeAt G v f) sg := by rwa [hnd]
  have hacf := assembledColor_eq_portStage_at_junction col portCol fill hfill cycle
    (mem_incFinset.mp hf).1 (mem_incFinset.mp hf).2
    hdv
  have hacg := assembledColor_eq_portStage_at_junction col portCol fill hfill cycle
    (mem_incFinset.mp hg).1 (mem_incFinset.mp hg).2
    hdv
  have hcslot : slotColor col portCol sf = slotColor col portCol sg := by
    rw [hcf, hcg, ← hacf, ← hacg, hc]
  have hst := slotColor_injective_at col hcol portCol havoid hport hsf hsg' hcslot
  apply hfg
  rw [← hef, ← heg, hnd, hst]

private theorem assembledColor_short_hend
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y)
    (portCol : LongPort G → Fin 5)
    (havoid : ∀ P, portCol P ∉ oldColorsAt col (longPortNode P))
    (hport : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5)
    {x w y : V} (hxw : G.Adj x w) (hwy : G.Adj w y)
    (hxy : x ≠ y) (hdw : G.degree w = 2) (hdx3 : 3 ≤ G.degree x)
    {q : EdgeClass G} (hmem : s(x, w) ∈ (classPiece G q).walk.edges)
    (hwy_mem : s(w, y) ∈ (classPiece G q).walk.edges)
    (hnc : ¬(classPiece G q).IsCycle)
    (h3 : ¬3 ≤ (classPiece G q).walk.length) :
    assembledColor col fill cycle s(x, w) = assembledColor col fill cycle s(w, y) ∨
      assembledColor col fill cycle s(w, y) ∉
        satSet G (assembledColor col fill cycle) x w := by
  let m : ShortMember G := ⟨q, hnc, by omega⟩
  by_cases hc : IsChosenCherry (G := G) m
  · right
    have hdx2 : G.degree x ≠ 2 := by omega
    have hportmem := (classPiece G q).piece.eq_first_or_last hmem
      (Sym2.mem_mk_left x w) hdx2
    have hnd : steeredNodeAt G x s(x, w) ∈ shortMfam m := by
      rcases hportmem with hs | he'
      · have hedge : s(x, w) = (classPiece G q).firstEdge := by
          simpa [Piece.firstEdge] using hs.2
        have hedge' : s((classPiece G q).a, w) =
            (classPiece G q).firstEdge := by
          rw [← hs.1]
          exact hedge
        dsimp [m, shortMfam]
        rw [hs.1, hedge']
        exact Sym2.mem_mk_left _ _
      · have hedge : s(x, w) = (classPiece G q).lastEdge := by
          simpa [Piece.lastEdge] using he'.2
        have hedge' : s((classPiece G q).b, w) =
            (classPiece G q).lastEdge := by
          rw [← he'.1]
          exact hedge
        dsimp [m, shortMfam]
        rw [he'.1, hedge']
        exact Sym2.mem_mk_right _ _
    have hne := chosenCherry_endpoint_not_special m hc hnd
    have hrb := assembledColor_rainbow_steered col hcol portCol havoid hport
      fill hfill cycle
    rw [satSet_eq_empty_of_ne hrb hxw hdx3 hne.1 hne.2
      (groups_steeredGlueIx_le hdx3)]
    exact Finset.notMem_empty _
  · left
    have he := (classPiece G q).walk.edges_subset_edgeSet hmem
    have hey := (classPiece G q).walk.edges_subset_edgeSet hwy_mem
    rw [assembledColor_eq_class col fill cycle he hmem,
      assembledColor_eq_class col fill cycle hey hwy_mem]
    unfold assembledClassColor
    rw [dif_neg hnc, dif_neg (by omega), dif_neg hnc, dif_neg (by omega)]
    have hm := shortPortColor_mono col m hc
    generalize decide ((classPiece G q).walk.edges.idxOf s(x, w) ≠ 0) = b₁
    generalize decide ((classPiece G q).walk.edges.idxOf s(w, y) ≠ 0) = b₂
    cases b₁ <;> cases b₂
    · rfl
    · exact hm
    · exact hm.symm
    · rfl

private theorem assembledColor_hend
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y)
    (portCol : LongPort G → Fin 5)
    (havoid : ∀ P, portCol P ∉ oldColorsAt col (longPortNode P))
    (hport : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5) :
    ∀ x w y : V, G.Adj x w → G.Adj w y → x ≠ y →
      G.degree w = 2 → 3 ≤ G.degree x →
      assembledColor col fill cycle s(x, w) = assembledColor col fill cycle s(w, y) ∨
      assembledColor col fill cycle s(w, y) ∉
        satSet G (assembledColor col fill cycle) x w := by
  intro x w y hxw hwy hxy hdw hdx3
  have he : s(x, w) ∈ G.edgeSet := G.mem_edgeSet.mpr hxw
  have hey : s(w, y) ∈ G.edgeSet := G.mem_edgeSet.mpr hwy
  let q : EdgeClass G := edgeClassOf G he
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
    let Q : LongChain G := ⟨q, hnc, h3⟩
    rcases (classPiece G q).piece.eq_first_or_last hmem
        (Sym2.mem_mk_left x w) hdx2 with hs | he'
    · have hw : w = (classPiece G q).walk.snd := by
        rcases Sym2.eq_iff.mp hs.2 with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact h2
        · exact absurd (hs.1.trans h2.symm) (G.ne_of_adj hxw)
      obtain ⟨h1len, he1⟩ := (classPiece G q).piece.edges_one_eq
        (by rw [← hs.1]; exact hdx2) (by rw [← hw]; exact hdw)
        (by rw [← hw]; exact hwy) (by rw [← hs.1]; exact Ne.symm hxy)
      have hidx : (classPiece G q).walk.edges.idxOf s(w, y) = 1 :=
        idxOf_eq_of_getElem (classPiece G q).piece.trail.edges_nodup
          h1len (by rw [he1, ← hw])
      have hcy : assembledColor col fill cycle s(w, y) = fill Q 1 := by
        rw [assembledColor_eq_class col fill cycle hey hwy_mem, hidx]
        unfold assembledClassColor
        rw [dif_neg hnc, dif_pos h3]
      rw [hcy, satSet_assembledColor_eq_portStage col portCol fill hfill cycle hdx2,
        hs.1, hw]
      have hn := (hfill Q).2.2.2.1
      unfold longFx at hn
      rwa [if_pos (hs.1 ▸ hdx3)] at hn
    · have hw : w = (classPiece G q).walk.penultimate := by
        rcases Sym2.eq_iff.mp he'.2 with ⟨-, h2⟩ | ⟨-, h2⟩
        · exact absurd (he'.1.trans h2.symm) (G.ne_of_adj hxw)
        · exact h2
      obtain ⟨hslen, hes⟩ := (classPiece G q).piece.edges_length_sub_two_eq
        (by rw [← he'.1]; exact hdx2) (by rw [← hw]; exact hdw)
        (by rw [← hw]; exact hwy) (by rw [← he'.1]; exact Ne.symm hxy)
      have hidx : (classPiece G q).walk.edges.idxOf s(w, y) =
          (classPiece G q).walk.edges.length - 2 :=
        idxOf_eq_of_getElem (classPiece G q).piece.trail.edges_nodup
          hslen (by rw [hes, ← hw])
      have hcy : assembledColor col fill cycle s(w, y) =
          fill Q ((classPiece G q).walk.length - 2) := by
        rw [assembledColor_eq_class col fill cycle hey hwy_mem, hidx,
          (classPiece G q).walk.length_edges]
        unfold assembledClassColor
        rw [dif_neg hnc, dif_pos h3]
      rw [hcy, satSet_assembledColor_eq_portStage col portCol fill hfill cycle hdx2,
        he'.1, hw]
      have hn := (hfill Q).2.2.2.2
      unfold longFy at hn
      rwa [if_pos (he'.1 ▸ hdx3)] at hn
  · exact assembledColor_short_hend col hcol portCol havoid hport fill hfill
      cycle hxw hwy hxy hdw hdx3 hmem hwy_mem hnc h3

/-- Final verification residue after every coloring choice has been made.
This theorem contains no existence or traversal work: it is only the
canonical-piece case split proving the three direct-assembly hypotheses. -/
private theorem assembledColor_invariants
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (hadm : Admissible G) (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y)
    (portCol : LongPort G → Fin 5)
    (havoid : ∀ P, portCol P ∉ oldColorsAt col (longPortNode P))
    (hport : ∀ P Q, longPortConflict P Q → portCol P ≠ portCol Q)
    (fill : LongChain G → ℕ → Fin 5)
    (hfill : ∀ Q, IsFill (classPiece G Q.1).walk.length
      (portCol (Q, false)) (portCol (Q, true))
      (longFx col portCol Q) (longFy col portCol Q) (fill Q))
    (cycle : CycleClass G → ℕ → Fin 5)
    (hcycle : ∀ Q : CycleClass G, ∀ i < (classPiece G Q.1).walk.length,
      cycle Q i ≠ cycle Q ((i + 2) % (classPiece G Q.1).walk.length)) :
    let c := assembledColor col fill cycle
    (∀ v : V, 3 ≤ G.degree v → ∀ α : Fin 5,
      #{f ∈ G.incidenceFinset v | c f = α} ≤ hfun 4 (G.degree v)) ∧
    (∀ u v : V, G.Adj u v → G.degree u = 2 → G.degree v = 2 →
      ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g) ∧
    (∀ x w y : V, G.Adj x w → G.Adj w y → x ≠ y →
      G.degree w = 2 → 3 ≤ G.degree x →
      c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w) := by
  dsimp only
  exact ⟨assembledColor_hmult col hcol portCol havoid hport fill hfill cycle,
    assembledColor_hint col hcol portCol havoid hport fill hfill cycle hcycle,
    assembledColor_hend col hcol portCol havoid hport fill hfill cycle⟩

/-- Remaining pass B: construct only the bare graph coloring. The gated
rank grouping downstream supplies all `ix` bookkeeping. -/
private theorem exists_bareColoring_of_expandedMemberColoring
    [Fintype (Quotient (linkSetoid G))]
    [Fintype (ShortMember G)] [Fintype (ExpandedMember (G := G))]
    (hadm : Admissible G) (col : ExpandedMember (G := G) → Fin 5)
    (hcol : ∀ x y, x ≠ y → ∀ nd, nd ∈ expandedMfam x →
      nd ∈ expandedMfam y → col x ≠ col y) :
    ∃ c : Sym2 V → Fin 5,
      (∀ v : V, 3 ≤ G.degree v → ∀ α : Fin 5,
        #{f ∈ G.incidenceFinset v | c f = α} ≤ hfun 4 (G.degree v)) ∧
      (∀ u v : V, G.Adj u v → G.degree u = 2 → G.degree v = 2 →
        ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g) ∧
      (∀ x w y : V, G.Adj x w → G.Adj w y → x ≠ y →
        G.degree w = 2 → 3 ≤ G.degree x →
        c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w) := by
  obtain ⟨portCol, havoid, hport⟩ := exists_longPort_assignment col
  obtain ⟨fill, hfill⟩ := exists_fills_of_longPort_assignment col portCol hport
  obtain ⟨cycle, hcycle⟩ := exists_cycleClass_patterns (G := G)
  refine ⟨assembledColor col fill cycle, ?_⟩
  exact assembledColor_invariants hadm col hcol portCol havoid hport
    fill hfill cycle hcycle

/-- The simple support used as M₀: one representative of every nonempty
expanded parallel class. The remaining copies are precisely the greedy
reinsertion payload. -/
private noncomputable def simpleCore
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ExpandedNode G) : ℕ := min (expandedMult (G := G) a b) 1

private lemma simpleCore_symm
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ExpandedNode G) : simpleCore (G := G) a b = simpleCore (G := G) b a := by
  simp only [simpleCore, expandedMult_symm]

private lemma simpleCore_simple
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a b : ExpandedNode G) : simpleCore (G := G) a b ≤ 1 := by
  exact min_le_right _ _

private lemma simpleCore_diag
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a : ExpandedNode G) : simpleCore (G := G) a a = 0 := by
  simp [simpleCore, expandedMult_diag]

private lemma simpleCore_mdeg_le_four
    [Fintype (ShortMember G)] [DecidableEq (ShortMember G)]
    [Fintype (ExpandedMember (G := G))] [DecidableEq (ExpandedMember (G := G))]
    (a : ExpandedNode G) : mdeg (simpleCore (G := G)) a ≤ 4 := by
  calc
    mdeg (simpleCore (G := G)) a ≤ mdeg (expandedMult (G := G)) a := by
      unfold mdeg
      exact Finset.sum_le_sum fun b _ => min_le_left _ _
    _ ≤ 4 := expandedMult_mdeg_le_four a

/-! Gated Aristotle transport/fill layer, vendored verbatim modulo comments. -/

private lemma port_fill_five {l : ℕ} (hl : 3 ≤ l) (p q : Fin 5)
    (hpq : l = 3 → p ≠ q) {Fx Fy : Finset (Fin 5)}
    (hFx : #Fx ≤ 2) (hFy : #Fy ≤ 2) :
    ∃ c : ℕ → Fin 5, IsFill l p q Fx Fy c :=
  isFill_exists (by decide) hl p q hpq hFx hFy

private lemma satSet_card_le_two_five {c : Sym2 V → Fin 5} {x w : V}
    (hxw : G.Adj x w) (hd : 2 ≤ G.degree x) :
    #(satSet G c x w) ≤ 2 :=
  card_satSet_le_two hxw hd

private lemma cherry_satSet_empty_five {ix : V → Sym2 V → ℕ}
    {c : Sym2 V → Fin 5} (hrb : IsRainbow G ix c) {x w : V}
    (hxw : G.Adj x w) (hd4 : G.degree x = 4)
    (hg : groups G ix x ≤ hfun 4 (G.degree x)) :
    satSet G c x w = ∅ :=
  satSet_eq_empty_of_ne hrb hxw (by omega) (by omega) (by omega) hg

private lemma chainEnd_of_mono {c : Sym2 V → Fin 5} {x w y : V}
    (h : c s(x, w) = c s(w, y)) :
    c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w := Or.inl h

private lemma chainEnd_of_fill {c : Sym2 V → Fin 5} {x w y : V}
    (h : c s(w, y) ∉ satSet G c x w) :
    c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w := Or.inr h

private lemma chainEnd_of_safe {ix : V → Sym2 V → ℕ}
    {c : Sym2 V → Fin 5} (hrb : IsRainbow G ix c) {x w y : V}
    (hxw : G.Adj x w) (hd : 3 ≤ G.degree x) (h3 : G.degree x ≠ 3)
    (h5 : G.degree x ≠ 5)
    (hg : groups G ix x ≤ hfun 4 (G.degree x)) :
    c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w := by
  right
  rw [satSet_eq_empty_of_ne hrb hxw hd h3 h5 hg]
  exact Finset.notMem_empty _

private lemma interior_of_flank_distinct {c : Sym2 V → Fin 5} {u v : V}
    (h : ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g) :
    ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g := h

private lemma rainbow_of_sepIx (c : Sym2 V → Fin 5) :
    IsRainbow G (sepIx (V := V)) c := by
  intro v f₁ _ f₂ _ hix _
  exact sepIx_inj v hix

private lemma isGlueColoring_of_fields {ix : V → Sym2 V → ℕ}
    {c : Sym2 V → Fin 5} (hrb : IsRainbow G ix c)
    (hjg : ∀ v : V, 3 ≤ G.degree v → groups G ix v ≤ hfun 4 (G.degree v))
    (hce : ∀ x w y : V, G.Adj x w → G.Adj w y → x ≠ y →
      G.degree w = 2 → 3 ≤ G.degree x →
      c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w)
    (hint : ∀ u v : V, G.Adj u v → G.degree u = 2 → G.degree v = 2 →
      ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g) :
    IsGlueColoring G ix c :=
  ⟨hrb, hjg, hce, hint⟩

private lemma exists_isGlueColoring_five_of_maxDegree_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg2 : ∀ v, G.degree v ≤ 2) :
    ∃ (ix : V → Sym2 V → ℕ) (c : Sym2 V → Fin 5), IsGlueColoring G ix c := by
  obtain ⟨col, hcol⟩ := exists_proper_coloring (flankConflictSymm G) 5
    (flankConflictSymm_irrefl G) (flankConflictSymm_symm G)
    (flankConflictSymm_ncard_lt G hdeg2)
  refine ⟨sepIx, col, isGlueColoring_of_fields (rainbow_of_sepIx col) ?_ ?_ ?_⟩
  · exact fun v hv => absurd hv (by have := hdeg2 v; omega)
  · exact fun x w y _ _ _ _ hdx3 => absurd hdx3 (by have := hdeg2 x; omega)
  · exact fun u v huv hdu hdv f hf g hg =>
      hcol f g (Or.inl ⟨u, v, huv, hdu, hdv, hf, hg⟩)

/-! Gated lam4b-direct rank grouping and bare-coloring assembly. -/

private noncomputable def rankIx (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Sym2 V → Fin 5) (v : V) (f : Sym2 V) : ℕ :=
  #{g ∈ G.incidenceFinset v | c g = c f ∧
      (Fintype.equivFin (Sym2 V) g : ℕ) < (Fintype.equivFin (Sym2 V) f : ℕ)}

private lemma rankIx_isRainbow (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Sym2 V → Fin 5) : IsRainbow G (rankIx G c) c := by
  intro v f₁ hf₁ f₂ hf₂ h_rank h_color
  by_contra h_neq
  cases lt_or_gt_of_ne (show (Fintype.equivFin (Sym2 V) f₁ : ℕ) ≠
      (Fintype.equivFin (Sym2 V) f₂ : ℕ) from by
        simpa [Fin.ext_iff] using fun h => h_neq <|
          (Fintype.equivFin (Sym2 V)).injective <| Fin.ext h) <;>
      simp_all +decide [rankIx]
  · refine h_rank.not_lt (Finset.card_lt_card ?_)
    simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
    exact ⟨fun x hx₁ hx₂ hx₃ => lt_trans hx₃ ‹_›,
      f₁, hf₁, h_color, ‹_›, le_rfl⟩
  · refine h_rank.not_gt (Finset.card_lt_card ?_)
    simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
    exact ⟨fun x hx₁ hx₂ hx₃ => lt_trans hx₃ ‹_›,
      f₂, hf₂, rfl, ‹_›, le_rfl⟩

private lemma rankIx_groups_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : Sym2 V → Fin 5)
    (hmult : ∀ v : V, 3 ≤ G.degree v → ∀ α : Fin 5,
      #{f ∈ G.incidenceFinset v | c f = α} ≤ hfun 4 (G.degree v))
    (v : V) (hv : 3 ≤ G.degree v) :
    groups G (rankIx G c) v ≤ hfun 4 (G.degree v) := by
  have h_image : ∀ f ∈ G.incidenceFinset v,
      rankIx G c v f < hfun 4 (G.degree v) := by
    intro f hf
    specialize hmult v hv (c f)
    simp_all +decide [rankIx]
    refine lt_of_lt_of_le (Finset.card_lt_card ?_) hmult
    simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
    exact ⟨f, hf, rfl, le_rfl⟩
  unfold groups
  exact if_neg (by linarith) |> fun h => h.symm ▸
    le_trans (Finset.card_le_card (Finset.image_subset_iff.mpr fun f hf =>
      Finset.mem_range.mpr (h_image f hf))) (by simp +decide)

private lemma exists_glueColoring_of_coloring (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : Sym2 V → Fin 5)
    (hmult : ∀ v : V, 3 ≤ G.degree v → ∀ α : Fin 5,
      #{f ∈ G.incidenceFinset v | c f = α} ≤ hfun 4 (G.degree v))
    (hint : ∀ u v : V, G.Adj u v → G.degree u = 2 → G.degree v = 2 →
      ∀ f ∈ side G u v, ∀ g ∈ side G v u, c f ≠ c g)
    (hend : ∀ x w y : V, G.Adj x w → G.Adj w y → x ≠ y →
      G.degree w = 2 → 3 ≤ G.degree x →
      c s(x, w) = c s(w, y) ∨ c s(w, y) ∉ satSet G c x w) :
    ∃ (ix : V → Sym2 V → ℕ), IsGlueColoring G ix c :=
  ⟨rankIx G c, rankIx_isRainbow G c,
    fun v hv => rankIx_groups_le G c hmult v hv, hend, hint⟩

#print axioms steeredGlueIx_fiber_le
#print axioms groups_steeredGlueIx_le
#print axioms steeredGlueIx_inj_low
#print axioms shortMfam_not_isDiag
#print axioms shortMfam_count_le_four
#print axioms exists_two_chain_of_parallel
#print axioms shortMult_mdeg_le_four
#print axioms exists_cherry_of_bad
#print axioms short_rule3_of_not_bad
#print axioms expandedMfam_not_isDiag
#print axioms expandedMfam_count_old_le_four
#print axioms expandedMfam_count_le_four
#print axioms simpleCore_simple
#print axioms simpleCore_mdeg_le_four
#print axioms expandedMult_heavy
#print axioms exists_expandedMult_coloring
#print axioms exists_expandedMemberColoring
#print axioms port_fill_five
#print axioms cherry_satSet_empty_five
#print axioms isGlueColoring_of_fields
#print axioms exists_isGlueColoring_five_of_maxDegree_le_two
#print axioms rankIx_isRainbow
#print axioms rankIx_groups_le
#print axioms exists_glueColoring_of_coloring

/-- TARGET Λ4 (VERBATIM from synthesis.md §4). -/
theorem exists_isGlueColoring_five (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G) :
    ∃ (ix : V → Sym2 V → ℕ) (c : Sym2 V → Fin 5), IsGlueColoring G ix c := by
  classical
  letI : Fintype (Quotient (linkSetoid G)) := Fintype.ofFinite _
  letI : Fintype (ShortMember G) := Fintype.ofFinite _
  letI : Fintype (ExpandedMember (G := G)) := Fintype.ofFinite _
  obtain ⟨f, hf⟩ := exists_expandedMult_coloring (G := G)
  obtain ⟨col, hcol⟩ := exists_expandedMemberColoring f hf
  obtain ⟨c, hmult, hint, hend⟩ :=
    exists_bareColoring_of_expandedMemberColoring hadm col hcol
  obtain ⟨ix, hglue⟩ := exists_glueColoring_of_coloring G c hmult hint hend
  exact ⟨ix, c, hglue⟩

#print axioms SMaj.exists_isGlueColoring_five

end SMaj
