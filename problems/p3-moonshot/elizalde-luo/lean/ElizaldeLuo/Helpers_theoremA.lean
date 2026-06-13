/-
# Helpers for the "theoremA" sorry package (TheoremA.lean)

Position-level facts about nonnesting multiset permutations, culminating in:

* `fst_eq_oPos` / `snd_eq_qPos`: the first/second occurrences of the labels (in
  label order) are exactly the opener/closer positions of the shape — the
  position-level content of bijection.md Lemma 0 ("FIFO matching");
* `getD_oPos` / `getD_qPos`: the value carried at the `A`-th opener/closer is the
  `A`-th label;
* `arc_of_position`: every position of the word is the opener or closer of a
  (recoverable) arc, and carries that arc's label;
* the order calculus of `oPos`/`qPos` (strict monotonicity, Fact 0.1
  `oPos_lt_qPos_self`, position-to-arc recovery `oPos_count_take`/`qPos_count_take`).

Everything lives in the sub-namespace `ElizaldeLuo.TA` to avoid clashes with the
parallel helper namespaces: `ShapesH` (Helpers_shapes.lean) proves some of the same
`posOf` calculus, but it cannot be imported here because `Helpers_shapes` imports
`TheoremA` itself; the shared proofs are reproduced verbatim. This file is
sorry-free.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo
import ElizaldeLuo.SignWord

namespace ElizaldeLuo

open scoped List

namespace TA

/-! ## Generic list facts -/

theorem getD_range {n A : ℕ} (hA : A < n) : (List.range n).getD A 0 = A := by
  rw [List.getD_eq_getElem _ _ (by simpa using hA)]
  simp

/-- Two strictly sorted lists of naturals with `l₁ ⊆ l₂` and `|l₂| ≤ |l₁|` are
equal. -/
theorem sorted_eq_of_subset {l₁ l₂ : List ℕ} (h₁ : l₁.Pairwise (· < ·))
    (h₂ : l₂.Pairwise (· < ·)) (hsub : ∀ x ∈ l₁, x ∈ l₂)
    (hlen : l₂.length ≤ l₁.length) : l₁ = l₂ := by
  haveI : Std.Antisymm (α := ℕ) (· < ·) :=
    ⟨fun _ _ h h' => absurd h' (Nat.lt_asymm h)⟩
  have hnd : l₁.Nodup := h₁.imp (fun h => Nat.ne_of_lt h)
  have hsl : l₁ <+ l₂ :=
    List.sublist_of_subperm_of_pairwise (hnd.subperm hsub) h₁ h₂
  exact hsl.eq_of_length_le hlen

/-- Two positions with the same value force the count to be at least two. -/
theorem two_le_count_of_getD {u : List ℕ} {v : ℕ} {a b : ℕ} (hab : a < b)
    (hb : b < u.length) (ha : u.getD a 0 = v) (hbv : u.getD b 0 = v) :
    2 ≤ u.count v := by
  have haw : a < u.length := hab.trans hb
  have h1 : v ∈ u.take (a + 1) := by
    rw [← ha]
    exact SW.getD_mem_take (Nat.lt_succ_self a) haw
  have h2 : v ∈ u.drop (a + 1) := by
    have hd : b - (a + 1) < (u.drop (a + 1)).length := by
      rw [List.length_drop]
      omega
    have he : (u.drop (a + 1)).getD (b - (a + 1)) 0 = u.getD b 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        show a + 1 + (b - (a + 1)) = b from by omega]
    rw [← hbv, ← he]
    exact SW.getD_mem hd
  have hc1 : 0 < (u.take (a + 1)).count v := List.count_pos_iff.mpr h1
  have hc2 : 0 < (u.drop (a + 1)).count v := List.count_pos_iff.mpr h2
  have hsum : (u.take (a + 1)).count v + (u.drop (a + 1)).count v = u.count v := by
    rw [← List.count_append, List.take_append_drop]
  omega

/-- If `v` occurs exactly twice in `w` and positions `i < j` both carry `v`, then
`i` is the first occurrence and `j` the second. -/
theorem two_positions {w : List ℕ} {v : ℕ} (hcnt : w.count v = 2) {i j : ℕ}
    (hij : i < j) (hjw : j < w.length) (hiv : w.getD i 0 = v)
    (hjv : w.getD j 0 = v) :
    i = w.idxOf v ∧ j = SW.sndIdx w v := by
  have hiw : i < w.length := hij.trans hjw
  have hvmem : v ∈ w := by
    rw [← hiv]
    exact SW.getD_mem hiw
  have hfst : w.idxOf v ≤ i := by
    by_contra h
    have h' : i < w.idxOf v := by omega
    have hmem := SW.getD_mem_take h' hiw
    rw [hiv] at hmem
    exact SW.not_mem_take_idxOf w v hmem
  have hsplit : (w.take (w.idxOf v + 1)).count v + (w.drop (w.idxOf v + 1)).count v
      = 2 := by
    rw [← List.count_append, List.take_append_drop, hcnt]
  have h1 : (w.take (w.idxOf v + 1)).count v = 1 := SW.count_take_idxOf_succ hvmem
  have hdcnt : (w.drop (w.idxOf v + 1)).count v = 1 := by omega
  -- value transport into the drop
  have hdrop_val : ∀ {m : ℕ}, w.idxOf v < m → m < w.length → w.getD m 0 = v →
      (w.drop (w.idxOf v + 1)).getD (m - (w.idxOf v + 1)) 0 = v := by
    intro m hfm hmw hmv
    have he : (w.drop (w.idxOf v + 1)).getD (m - (w.idxOf v + 1)) 0
        = w.getD m 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
        show w.idxOf v + 1 + (m - (w.idxOf v + 1)) = m from by omega]
    rw [he, hmv]
  have hdlen : (w.drop (w.idxOf v + 1)).length = w.length - (w.idxOf v + 1) := by
    rw [List.length_drop]
  -- i is the first occurrence
  have hi_eq : i = w.idxOf v := by
    rcases Nat.lt_or_ge (w.idxOf v) i with hfi | hfi
    · -- two later positions would push the drop count to ≥ 2
      have h2le := two_le_count_of_getD (u := w.drop (w.idxOf v + 1))
        (a := i - (w.idxOf v + 1)) (b := j - (w.idxOf v + 1)) (by omega) (by omega)
        (hdrop_val hfi hiw hiv) (hdrop_val (hfi.trans hij) hjw hjv)
      omega
    · omega
  -- j is the second occurrence
  have hj_gt : w.idxOf v < j := by omega
  have hjdrop := hdrop_val hj_gt hjw hjv
  have hjd : j - (w.idxOf v + 1) < (w.drop (w.idxOf v + 1)).length := by omega
  have hd_le : (w.drop (w.idxOf v + 1)).idxOf v ≤ j - (w.idxOf v + 1) := by
    by_contra h
    have h' : j - (w.idxOf v + 1) < (w.drop (w.idxOf v + 1)).idxOf v := by omega
    have hmem := SW.getD_mem_take h' hjd
    rw [hjdrop] at hmem
    exact SW.not_mem_take_idxOf (w.drop (w.idxOf v + 1)) v hmem
  have hd_ge : ¬ (w.drop (w.idxOf v + 1)).idxOf v < j - (w.idxOf v + 1) := by
    intro h
    have hvd : v ∈ w.drop (w.idxOf v + 1) := List.count_pos_iff.mp (by omega)
    have := two_le_count_of_getD h hjd (SW.getD_idxOf hvd) hjdrop
    omega
  have hd_eq : (w.drop (w.idxOf v + 1)).idxOf v = j - (w.idxOf v + 1) := by omega
  have hs : SW.sndIdx w v = w.idxOf v + 1 + (w.drop (w.idxOf v + 1)).idxOf v := rfl
  exact ⟨hi_eq, by omega⟩

/-! ## Position lists: the generic `posOf` view of opener/closer positions

Reproduced from `ShapesH` (Helpers_shapes.lean), which cannot be imported here
(it imports `TheoremA`). -/

/-- The 0-based positions `k < s.length` with `s.getD k false = b`;
`openerPositions = posOf true`, `closerPositions = posOf false`. -/
def posOf (b : Bool) (s : List Bool) : List ℕ :=
  (List.range s.length).filter fun k => s.getD k false = b

theorem openerPositions_eq_posOf (s : List Bool) :
    openerPositions s = posOf true s := rfl

theorem closerPositions_eq_posOf (s : List Bool) :
    closerPositions s = posOf false s := rfl

theorem posOf_nil (b : Bool) : posOf b [] = [] := rfl

theorem posOf_concat (b c : Bool) (s : List Bool) :
    posOf b (s ++ [c]) = posOf b s ++ if c = b then [s.length] else [] := by
  unfold posOf
  have hlen : (s ++ [c]).length = s.length + 1 := by simp
  rw [hlen, List.range_succ, List.filter_append]
  have hgetD : (s ++ [c]).getD s.length false = c := by
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  congr 1
  · apply List.filter_congr
    intro k hk
    rw [List.mem_range] at hk
    rw [List.getD_append _ _ _ _ hk]
  · by_cases hcb : c = b
    · rw [if_pos hcb]
      simp [hcb]
    · rw [if_neg hcb]
      simp [hcb]

theorem posOf_append (b : Bool) (s t : List Bool) :
    posOf b (s ++ t) = posOf b s ++ (posOf b t).map (· + s.length) := by
  induction t using List.reverseRecOn with
  | nil => simp [posOf_nil]
  | append_singleton t c ih =>
    rw [← List.append_assoc, posOf_concat, posOf_concat, ih, List.append_assoc,
      List.map_append]
    congr 2
    by_cases hcb : c = b <;> simp [hcb, List.length_append, Nat.add_comm]

theorem length_posOf (b : Bool) (s : List Bool) :
    (posOf b s).length = s.count b := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s c ih =>
    rw [posOf_concat, List.length_append, ih, List.count_append]
    by_cases hcb : c = b <;> simp [hcb]

theorem mem_posOf {b : Bool} {s : List Bool} {k : ℕ} :
    k ∈ posOf b s ↔ k < s.length ∧ s.getD k false = b := by
  unfold posOf
  rw [List.mem_filter, List.mem_range]
  simp

theorem pairwise_posOf (b : Bool) (s : List Bool) :
    (posOf b s).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

/-! ## Sorted-list index lemmas (reproduced from `ShapesH`) -/

theorem getD_mem_of_lt {l : List ℕ} {j : ℕ} (hj : j < l.length) :
    l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

theorem pairwise_getD_lt {l : List ℕ} (hl : l.Pairwise (· < ·)) {i j : ℕ}
    (hij : i < j) (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (hij.trans hj), List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp hl i j (hij.trans hj) hj hij

/-- For a strictly sorted list, "the `K`-th entry is `< t`" is "`K` is below the
number of entries `< t`". -/
theorem getD_lt_iff_filter {l : List ℕ} (hl : l.Pairwise (· < ·)) {K t : ℕ}
    (hK : K < l.length) :
    l.getD K 0 < t ↔ K < (l.filter (· < t)).length := by
  induction l generalizing K with
  | nil => simp at hK
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ha, hl⟩ := hl
    by_cases hat : a < t
    · rw [List.filter_cons_of_pos (by simpa using hat)]
      match K with
      | 0 => simpa using hat
      | K + 1 =>
        rw [List.getD_cons_succ, List.length_cons]
        have hKl : K < l.length := by simpa using hK
        have := ih hl hKl
        omega
    · rw [List.filter_cons_of_neg (by simpa using hat)]
      have hfilter : l.filter (· < t) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have := ha x hx
        simp only [decide_eq_true_eq]
        omega
      rw [hfilter]
      simp only [List.length_nil]
      match K with
      | 0 =>
        rw [List.getD_cons_zero]
        omega
      | K + 1 =>
        rw [List.getD_cons_succ]
        have hKl : K < l.length := by simpa using hK
        have hmem : l.getD K 0 ∈ l := getD_mem_of_lt hKl
        have := ha _ hmem
        omega

/-- For a strictly sorted list, the index of an element `x` is the number of
entries `< x`. -/
theorem getD_length_filter {l : List ℕ} (hl : l.Pairwise (· < ·)) {x : ℕ}
    (hx : x ∈ l) :
    l.getD ((l.filter (· < x)).length) 0 = x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    obtain ⟨ha, hl⟩ := hl
    rcases List.mem_cons.mp hx with rfl | hx'
    · have hnil : (x :: l).filter (· < x) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp hy with rfl | hy'
        · omega
        · have := ha y hy'
          omega
      rw [hnil]
      rfl
    · have hax : a < x := ha x hx'
      rw [List.filter_cons_of_pos (by simpa using hax), List.length_cons,
        List.getD_cons_succ]
      exact ih hl hx'

theorem getD_map_of_lt {f : ℕ → ℕ} {l : List ℕ} {r : ℕ} (hr : r < l.length) :
    (l.map f).getD r 0 = f (l.getD r 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hr), List.getD_eq_getElem _ _ hr,
    List.getElem_map]

/-! ## Prefix counts vs. position lists (reproduced from `ShapesH`) -/

theorem filter_posOf_take (b : Bool) (s : List Bool) {t : ℕ} (ht : t ≤ s.length) :
    (posOf b s).filter (· < t) = posOf b (s.take t) := by
  have htake : (s.take t).length = t := by
    rw [List.length_take]
    omega
  conv_lhs => rw [← List.take_append_drop t s]
  rw [posOf_append, List.filter_append]
  have h1 : (posOf b (s.take t)).filter (· < t) = posOf b (s.take t) := by
    apply List.filter_eq_self.mpr
    intro x hx
    have hxlt := (mem_posOf.mp hx).1
    rw [htake] at hxlt
    simpa using hxlt
  have h2 : ((posOf b (s.drop t)).map (· + (s.take t).length)).filter (· < t)
      = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    rw [htake]
    simp only [decide_eq_true_eq]
    omega
  rw [h1, h2, List.append_nil]

theorem count_take_eq_length_filter (b : Bool) (s : List Bool) {t : ℕ}
    (ht : t ≤ s.length) :
    (s.take t).count b = ((posOf b s).filter (· < t)).length := by
  rw [filter_posOf_take b s ht, length_posOf]

theorem count_true_add_count_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases a <;> simp <;> omega

/-! ## Arc-index characterizations (reproduced/extended from `ShapesH`) -/

theorem oPos_eq_posOf_getD (s : List Bool) (j : ℕ) :
    oPos s j = (posOf true s).getD j 0 := rfl

theorem qPos_eq_posOf_getD (s : List Bool) (j : ℕ) :
    qPos s j = (posOf false s).getD j 0 := rfl

theorem oPos_lt_length {s : List Bool} {j : ℕ} (hj : j < s.count true) :
    oPos s j < s.length := by
  have hlen : (posOf true s).length = s.count true := length_posOf true s
  have hmem : oPos s j ∈ posOf true s := by
    rw [oPos_eq_posOf_getD]
    exact getD_mem_of_lt (by omega)
  exact (mem_posOf.mp hmem).1

theorem qPos_lt_length {s : List Bool} {j : ℕ} (hj : j < s.count false) :
    qPos s j < s.length := by
  have hlen : (posOf false s).length = s.count false := length_posOf false s
  have hmem : qPos s j ∈ posOf false s := by
    rw [qPos_eq_posOf_getD]
    exact getD_mem_of_lt (by omega)
  exact (mem_posOf.mp hmem).1

/-- Openers are increasingly ordered: `o_K < o_J ↔ K < J` (both in range). -/
theorem oPos_lt_oPos_iff {s : List Bool} {J K : ℕ} (hJ : J < s.count true)
    (hK : K < s.count true) :
    oPos s K < oPos s J ↔ K < J := by
  rw [oPos_eq_posOf_getD, oPos_eq_posOf_getD]
  have hlen : (posOf true s).length = s.count true := length_posOf true s
  constructor
  · intro h
    by_contra hKJ
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hKJ) with heq | hlt
    · rw [heq] at h
      omega
    · have := pairwise_getD_lt (pairwise_posOf true s) hlt (by omega)
      omega
  · intro h
    exact pairwise_getD_lt (pairwise_posOf true s) h (by omega)

/-- Closers are increasingly ordered: `q_K < q_J ↔ K < J` (both in range). -/
theorem qPos_lt_qPos_iff {s : List Bool} {J K : ℕ} (hJ : J < s.count false)
    (hK : K < s.count false) :
    qPos s K < qPos s J ↔ K < J := by
  rw [qPos_eq_posOf_getD, qPos_eq_posOf_getD]
  have hlen : (posOf false s).length = s.count false := length_posOf false s
  constructor
  · intro h
    by_contra hKJ
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hKJ) with heq | hlt
    · rw [heq] at h
      omega
    · have := pairwise_getD_lt (pairwise_posOf false s) hlt (by omega)
      omega
  · intro h
    exact pairwise_getD_lt (pairwise_posOf false s) h (by omega)

theorem qPos_le_qPos {s : List Bool} {j k : ℕ} (hjk : j ≤ k)
    (hk : k < s.count false) :
    qPos s j ≤ qPos s k := by
  rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
  · exact le_rfl
  · exact le_of_lt ((qPos_lt_qPos_iff hk (by omega)).mpr hlt)

/-- `q_K < o_J ↔ K < #closers before o_J`. -/
theorem qPos_lt_oPos_iff {s : List Bool} {J K : ℕ} (hJ : J < s.count true)
    (hK : K < s.count false) :
    qPos s K < oPos s J ↔ K < (s.take (oPos s J)).count false := by
  rw [qPos_eq_posOf_getD]
  have h1 := getD_lt_iff_filter (pairwise_posOf false s)
    (K := K) (t := oPos s J) (by rw [length_posOf]; omega)
  rw [h1, ← count_take_eq_length_filter false s (le_of_lt (oPos_lt_length hJ))]

/-- Openers and closers occupy distinct positions. -/
theorem qPos_ne_oPos {s : List Bool} {J K : ℕ} (hJ : J < s.count true)
    (hK : K < s.count false) : qPos s K ≠ oPos s J := by
  intro heq
  have h1 : s.getD (qPos s K) false = false := by
    rw [qPos_eq_posOf_getD]
    exact (mem_posOf.mp (getD_mem_of_lt (by rw [length_posOf]; omega))).2
  have h2 : s.getD (oPos s J) false = true := by
    rw [oPos_eq_posOf_getD]
    exact (mem_posOf.mp (getD_mem_of_lt (by rw [length_posOf]; omega))).2
  rw [heq, h2] at h1
  exact Bool.noConfusion h1

/-- The arc index of an opener: `#openers before o_j = j`. -/
theorem count_true_take_oPos {s : List Bool} {j : ℕ} (hj : j < s.count true) :
    (s.take (oPos s j)).count true = j := by
  have hlen : (posOf true s).length = s.count true := length_posOf true s
  have hjl : j < (posOf true s).length := by omega
  have hpw := pairwise_posOf true s
  have hlt : oPos s j < s.length := oPos_lt_length hj
  rw [count_take_eq_length_filter true s (le_of_lt hlt), oPos_eq_posOf_getD]
  have h1 : ¬ ((posOf true s).getD j 0 < (posOf true s).getD j 0) := lt_irrefl _
  rw [getD_lt_iff_filter hpw hjl] at h1
  by_contra hne
  have hcj : ((posOf true s).filter (· < (posOf true s).getD j 0)).length < j := by
    omega
  have h2 := pairwise_getD_lt hpw hcj hjl
  rw [getD_lt_iff_filter hpw (by omega)] at h2
  omega

/-- `o_J < q_K ↔ #closers before o_J ≤ K`. -/
theorem oPos_lt_qPos_iff {s : List Bool} {J K : ℕ} (hJ : J < s.count true)
    (hK : K < s.count false) :
    oPos s J < qPos s K ↔ (s.take (oPos s J)).count false ≤ K := by
  have h1 := qPos_lt_oPos_iff hJ hK
  have h2 := qPos_ne_oPos hJ hK
  omega

/-- An opener position `p` is the `(s.take p).count true`-th opener. -/
theorem oPos_count_take {s : List Bool} {p : ℕ} (hp : p < s.length)
    (hb : s.getD p false = true) :
    oPos s ((s.take p).count true) = p := by
  have hx : p ∈ posOf true s := mem_posOf.mpr ⟨hp, hb⟩
  rw [oPos_eq_posOf_getD, count_take_eq_length_filter true s (le_of_lt hp),
    getD_length_filter (pairwise_posOf true s) hx]

/-- A closer position `p` is the `(s.take p).count false`-th closer. -/
theorem qPos_count_take {s : List Bool} {p : ℕ} (hp : p < s.length)
    (hb : s.getD p false = false) :
    qPos s ((s.take p).count false) = p := by
  have hx : p ∈ posOf false s := mem_posOf.mpr ⟨hp, hb⟩
  rw [qPos_eq_posOf_getD, count_take_eq_length_filter false s (le_of_lt hp),
    getD_length_filter (pairwise_posOf false s) hx]

theorem count_take_lt {b : Bool} {s : List Bool} {p : ℕ} (hp : p < s.length)
    (hb : s.getD p false = b) :
    (s.take p).count b < s.count b := by
  have h1 : (s.take (p + 1)).count b = (s.take p).count b + 1 := by
    rw [List.take_add_one, List.getElem?_eq_getElem hp]
    rw [List.getD_eq_getElem _ _ hp] at hb
    simp [List.count_append, hb]
  have h2 : (s.take (p + 1)).count b ≤ s.count b :=
    ((List.take_prefix _ _).sublist).count_le b
  omega

/-- **Fact 0.1** (bijection.md §1): in a Dyck word, `o_A < q_A`. -/
theorem oPos_lt_qPos_self {n : ℕ} {s : List Bool} (hs : IsDyck n s) {A : ℕ}
    (hA : A < n) : oPos s A < qPos s A := by
  obtain ⟨hslen, hstrue, hspre⟩ := hs
  have hsfalse : s.count false = n := by
    have := count_true_add_count_false s
    omega
  rw [oPos_lt_qPos_iff (by omega) (by omega)]
  have h1 := count_true_take_oPos (s := s) (j := A) (by omega)
  have h2 := hspre (oPos s A) (le_of_lt (oPos_lt_length (by omega)))
  omega

/-! ## `openerShape` as a positional predicate -/

private theorem openerShape_go_cons (v : ℕ) (rest seen : List ℕ) :
    openerShape.go (v :: rest) seen
      = (if v ∈ seen then false else true) :: openerShape.go rest (v :: seen) := rfl

private theorem openerShape_go_length : ∀ (w seen : List ℕ),
    (openerShape.go w seen).length = w.length
  | [], _ => rfl
  | v :: rest, seen => by
    rw [openerShape_go_cons, List.length_cons, List.length_cons,
      openerShape_go_length rest (v :: seen)]

theorem openerShape_length (w : List ℕ) : (openerShape w).length = w.length :=
  openerShape_go_length w []

private theorem openerShape_go_getD : ∀ (w seen : List ℕ) (k : ℕ), k < w.length →
    ((openerShape.go w seen).getD k false = true
      ↔ (w.getD k 0 ∉ seen ∧ w.getD k 0 ∉ w.take k))
  | [], _, k, hk => by simp at hk
  | v :: rest, seen, 0, _ => by
    rw [openerShape_go_cons]
    by_cases hv : v ∈ seen <;> simp [hv]
  | v :: rest, seen, k + 1, hk => by
    rw [openerShape_go_cons, List.getD_cons_succ, List.getD_cons_succ,
      List.take_succ_cons,
      openerShape_go_getD rest (v :: seen) k (by simpa using hk)]
    simp only [List.mem_cons]
    tauto

/-- Position `k` is an opener iff its value has not occurred before. -/
theorem openerShape_getD_true_iff {w : List ℕ} {k : ℕ} (hk : k < w.length) :
    (openerShape w).getD k false = true ↔ w.getD k 0 ∉ w.take k := by
  have h := openerShape_go_getD w [] k hk
  simpa using h

/-- Position `k` is a closer iff its value has occurred before. -/
theorem openerShape_getD_false_iff {w : List ℕ} {k : ℕ} (hk : k < w.length) :
    (openerShape w).getD k false = false ↔ w.getD k 0 ∈ w.take k := by
  constructor
  · intro hb
    by_contra hmem
    have h := (openerShape_getD_true_iff hk).mpr hmem
    rw [hb] at h
    exact Bool.noConfusion h
  · intro hmem
    cases hb : (openerShape w).getD k false with
    | false => rfl
    | true => exact absurd ((openerShape_getD_true_iff hk).mp hb) (not_not_intro hmem)

/-! ## Labels of a multiset permutation -/

theorem labels_length {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w) :
    (openerLabels w).length = n := by
  simpa [idPerm] using (openerLabels_perm hw).length_eq

theorem labels_nodup {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w) :
    (openerLabels w).Nodup :=
  (List.Perm.nodup_iff (openerLabels_perm hw)).mpr (SW.nodup_idPerm n)

theorem label_mem {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w) {A : ℕ}
    (hA : A < n) : (openerLabels w).getD A 0 ∈ w := by
  have hplen : (openerLabels w).length = n := labels_length hw
  have h1 : (openerLabels w).getD A 0 ∈ openerLabels w := SW.getD_mem (by omega)
  have h2 := (List.Perm.mem_iff (openerLabels_perm hw)).mp h1
  have h3 : 1 ≤ (openerLabels w).getD A 0 ∧ (openerLabels w).getD A 0 < 1 + n := by
    simpa [idPerm, List.mem_range'_1] using h2
  exact (List.Perm.mem_iff hw).mpr (mem_baseWord.mpr ⟨h3.1, by omega⟩)

theorem label_count_two {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w) {A : ℕ}
    (hA : A < n) : w.count ((openerLabels w).getD A 0) = 2 :=
  FifoH.count_eq_two_of_perm_baseWord hw (label_mem hw hA)

/-! ## First/second occurrences of the labels = opener/closer positions -/

/-- The list of first occurrences of the labels (in label order) is exactly the
list of opener positions. -/
theorem fstList_eq {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w)
    (hnn : Nonnesting w) :
    (List.range n).map (fun A => w.idxOf ((openerLabels w).getD A 0))
      = posOf true (openerShape w) := by
  obtain ⟨hslen, hstrue, hspre⟩ := openerShape_isDyck hw hnn
  apply sorted_eq_of_subset
  · rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [List.getElem_map, List.getElem_range]
    have hb' : b < n := by simpa using hb
    exact SW.openerLabels_idxOf_lt hab (by rw [labels_length hw]; exact hb')
  · exact pairwise_posOf true (openerShape w)
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [List.mem_range] at hA
    have hvw := label_mem hw hA
    have hidx := List.idxOf_lt_length_of_mem hvw
    rw [mem_posOf]
    refine ⟨by rwa [openerShape_length], ?_⟩
    rw [openerShape_getD_true_iff hidx, SW.getD_idxOf hvw]
    exact SW.not_mem_take_idxOf w _
  · rw [length_posOf, hstrue, List.length_map, List.length_range]

/-- The list of second occurrences of the labels (in label order) is exactly the
list of closer positions (this is the FIFO matching of bijection.md Lemma 0,
and is where nonnesting enters). -/
theorem sndList_eq {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w)
    (hnn : Nonnesting w) :
    (List.range n).map (fun A => SW.sndIdx w ((openerLabels w).getD A 0))
      = posOf false (openerShape w) := by
  obtain ⟨hslen, hstrue, hspre⟩ := openerShape_isDyck hw hnn
  have hsfalse : (openerShape w).count false = n := by
    have := count_true_add_count_false (openerShape w)
    omega
  apply sorted_eq_of_subset
  · rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp only [List.getElem_map, List.getElem_range]
    have ha' : a < n := by simpa using ha
    have hb' : b < n := by simpa using hb
    refine SW.sndIdx_lt_sndIdx hnn ?_ ?_ ?_ ?_
    · exact le_of_eq (label_count_two hw ha').symm
    · exact le_of_eq (label_count_two hw hb').symm
    · exact SW.getD_ne_of_nodup (labels_nodup hw)
        (by rw [labels_length hw]; omega) (by rw [labels_length hw]; omega)
        (Nat.ne_of_lt hab)
    · exact SW.openerLabels_idxOf_lt hab (by rw [labels_length hw]; exact hb')
  · exact pairwise_posOf false (openerShape w)
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨A, hA, rfl⟩ := hx
    rw [List.mem_range] at hA
    have hvw := label_mem hw hA
    have hcnt : 2 ≤ w.count ((openerLabels w).getD A 0) :=
      le_of_eq (label_count_two hw hA).symm
    obtain ⟨hslt, hsv⟩ := SW.sndIdx_spec hcnt
    rw [mem_posOf]
    refine ⟨by rwa [openerShape_length], ?_⟩
    rw [openerShape_getD_false_iff hslt, hsv]
    have h1 := SW.getD_mem_take (SW.idxOf_lt_sndIdx w ((openerLabels w).getD A 0))
      (List.idxOf_lt_length_of_mem hvw)
    rwa [SW.getD_idxOf hvw] at h1
  · rw [length_posOf, hsfalse, List.length_map, List.length_range]

/-- The first occurrence of the `A`-th label is the `A`-th opener position. -/
theorem fst_eq_oPos {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w)
    (hnn : Nonnesting w) {A : ℕ} (hA : A < n) :
    w.idxOf ((openerLabels w).getD A 0) = oPos (openerShape w) A := by
  have h2 : ((List.range n).map
        (fun A => w.idxOf ((openerLabels w).getD A 0))).getD A 0
      = (posOf true (openerShape w)).getD A 0 := by
    rw [fstList_eq hw hnn]
  rw [oPos_eq_posOf_getD]
  rwa [getD_map_of_lt (by simpa using hA), getD_range hA] at h2

/-- The second occurrence of the `A`-th label is the `A`-th closer position. -/
theorem snd_eq_qPos {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w)
    (hnn : Nonnesting w) {A : ℕ} (hA : A < n) :
    SW.sndIdx w ((openerLabels w).getD A 0) = qPos (openerShape w) A := by
  have h2 : ((List.range n).map
        (fun A => SW.sndIdx w ((openerLabels w).getD A 0))).getD A 0
      = (posOf false (openerShape w)).getD A 0 := by
    rw [sndList_eq hw hnn]
  rw [qPos_eq_posOf_getD]
  rwa [getD_map_of_lt (by simpa using hA), getD_range hA] at h2

/-- The value at the `A`-th opener position is the `A`-th label. -/
theorem getD_oPos {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w)
    (hnn : Nonnesting w) {A : ℕ} (hA : A < n) :
    w.getD (oPos (openerShape w) A) 0 = (openerLabels w).getD A 0 := by
  rw [← fst_eq_oPos hw hnn hA]
  exact SW.getD_idxOf (label_mem hw hA)

/-- The value at the `A`-th closer position is the `A`-th label. -/
theorem getD_qPos {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w)
    (hnn : Nonnesting w) {A : ℕ} (hA : A < n) :
    w.getD (qPos (openerShape w) A) 0 = (openerLabels w).getD A 0 := by
  rw [← snd_eq_qPos hw hnn hA]
  exact (SW.sndIdx_spec (le_of_eq (label_count_two hw hA).symm)).2

/-- Every position of the word is the opener or the closer of an arc `A < n`,
and carries that arc's label. -/
theorem arc_of_position {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w)
    (hnn : Nonnesting w) {m : ℕ} (hm : m < w.length) :
    ∃ A, A < n ∧ (m = oPos (openerShape w) A ∨ m = qPos (openerShape w) A)
      ∧ w.getD m 0 = (openerLabels w).getD A 0 := by
  obtain ⟨hslen, hstrue, hspre⟩ := openerShape_isDyck hw hnn
  have hsfalse : (openerShape w).count false = n := by
    have := count_true_add_count_false (openerShape w)
    omega
  have hms : m < (openerShape w).length := by
    rw [openerShape_length]
    exact hm
  cases hb : (openerShape w).getD m false with
  | true =>
    have hA : ((openerShape w).take m).count true < n := by
      have := count_take_lt hms hb
      omega
    refine ⟨((openerShape w).take m).count true, hA,
      Or.inl (oPos_count_take hms hb).symm, ?_⟩
    have h := getD_oPos hw hnn hA
    rwa [oPos_count_take hms hb] at h
  | false =>
    have hA : ((openerShape w).take m).count false < n := by
      have := count_take_lt hms hb
      omega
    refine ⟨((openerShape w).take m).count false, hA,
      Or.inr (qPos_count_take hms hb).symm, ?_⟩
    have h := getD_qPos hw hnn hA
    rwa [qPos_count_take hms hb] at h

end TA
end ElizaldeLuo
