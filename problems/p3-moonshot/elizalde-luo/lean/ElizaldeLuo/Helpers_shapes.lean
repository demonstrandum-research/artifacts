/-
# Helpers for the "shapes" sorry package (Shapes.lean)

Infrastructure that does not mention the shape families themselves:

* `PrefixOK h s` — the Dyck prefix condition started at height `h`, with cons/
  replicate unfolding lemmas (`IsDyck`'s third clause is `PrefixOK 0 s`).
* `posOf b s` — the sorted list of positions carrying the letter `b`
  (`openerPositions = posOf true`, `closerPositions = posOf false`), with an
  append calculus and sorted-list index lemmas.
* The count characterizations of the `ValidSign` positional predicates
  (`o_K < o_J ↔ K < J`, `o_J < q_K ↔ c_J ≤ K` with `c_J = o_J - J` the number
  of closers before the `J`-th opener), culminating in `validSign_iff_count`,
  the master count form of validity (bijection.md Lemma 3).
* Position-to-arc recovery (`oPos_count_take`), monotonicity of `c_J`, and
  run-decomposition helpers (`takeWhile`/`dropWhile`) used by the Lemma 4+5
  classification.

Everything here lives in the `ElizaldeLuo.ShapesH` namespace; the helpers that
do mention `tailWord`/`shapeS`/`shapeI`/`shapeII` continue this namespace
inside Shapes.lean (the definitions live there).
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo
import ElizaldeLuo.TheoremA

namespace ElizaldeLuo

namespace ShapesH

/-! ## The prefix condition, started at an arbitrary height -/

/-- The prefix condition of `IsDyck`, started at height `h`: every prefix has
at most `h` more closers than openers. `IsDyck`'s third clause is `PrefixOK 0 s`. -/
def PrefixOK (h : ℕ) (s : List Bool) : Prop :=
  ∀ k ≤ s.length, (s.take k).count false ≤ h + (s.take k).count true

theorem prefixOK_nil (h : ℕ) : PrefixOK h [] := by
  intro k hk
  simp

theorem prefixOK_cons_true {h : ℕ} {s : List Bool} :
    PrefixOK h (true :: s) ↔ PrefixOK (h + 1) s := by
  constructor
  · intro H k hk
    have h2 := H (k + 1) (by simp; omega)
    simp at h2 ⊢
    omega
  · intro H k hk
    match k with
    | 0 => simp
    | k + 1 =>
      have h2 := H k (by simp at hk; omega)
      simp
      omega

theorem prefixOK_cons_false {h : ℕ} {s : List Bool} :
    PrefixOK h (false :: s) ↔ 1 ≤ h ∧ PrefixOK (h - 1) s := by
  constructor
  · intro H
    have h1 := H 1 (by simp)
    simp at h1
    refine ⟨h1, fun k hk => ?_⟩
    have h2 := H (k + 1) (by simp; omega)
    simp at h2 ⊢
    omega
  · rintro ⟨h1, H⟩ k hk
    match k with
    | 0 => simp
    | k + 1 =>
      have h2 := H k (by simp at hk; omega)
      simp
      omega

theorem prefixOK_replicate_true_append {m : ℕ} {s : List Bool} : ∀ {h : ℕ},
    PrefixOK h (List.replicate m true ++ s) ↔ PrefixOK (h + m) s := by
  induction m with
  | zero => intro h; simp
  | succ m ih =>
    intro h
    rw [List.replicate_succ, List.cons_append, prefixOK_cons_true, ih,
      Nat.add_right_comm h 1 m, Nat.add_assoc]

theorem prefixOK_replicate_false_append {m : ℕ} {s : List Bool} : ∀ {h : ℕ},
    PrefixOK h (List.replicate m false ++ s) ↔ m ≤ h ∧ PrefixOK (h - m) s := by
  induction m with
  | zero => intro h; simp
  | succ m ih =>
    intro h
    rw [List.replicate_succ, List.cons_append, prefixOK_cons_false, ih]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      have he : h - 1 - m = h - (m + 1) := by omega
      rwa [he] at h3
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, by omega, ?_⟩
      have he : h - 1 - m = h - (m + 1) := by omega
      rwa [he]

/-! ## Position lists: the generic `posOf` view of opener/closer positions -/

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

theorem posOf_singleton (b c : Bool) : posOf b [c] = if c = b then [0] else [] := by
  simpa using posOf_concat b c []

theorem posOf_cons (b c : Bool) (s : List Bool) :
    posOf b (c :: s) = (if c = b then [0] else []) ++ (posOf b s).map (· + 1) := by
  simpa [posOf_singleton] using posOf_append b [c] s

theorem posOf_replicate_self (b : Bool) (m : ℕ) :
    posOf b (List.replicate m b) = List.range m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ', posOf_concat, ih, List.length_replicate, if_pos rfl,
      List.range_succ]

theorem posOf_replicate_ne {b c : Bool} (h : c ≠ b) (m : ℕ) :
    posOf b (List.replicate m c) = [] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ', posOf_concat, ih, if_neg h]
    rfl

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

/-! ## Sorted-list index lemmas -/

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

/-! ## Prefix counts vs. position lists -/

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

/-! ## Arc-index characterizations of the positional predicates -/

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

/-- M2: openers are increasingly ordered: `o_K < o_J ↔ K < J` (both in range). -/
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

/-- M3 core: `q_K < o_J ↔ K < #closers before o_J`. -/
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

/-- `c_J`, the number of closers before the `J`-th opener, equals `o_J - J`. -/
theorem count_false_take_oPos {s : List Bool} {j : ℕ} (hj : j < s.count true) :
    (s.take (oPos s j)).count false = oPos s j - j := by
  have h1 := count_true_take_oPos hj
  have hlt : oPos s j < s.length := oPos_lt_length hj
  have h2 : (s.take (oPos s j)).count true + (s.take (oPos s j)).count false
      = (s.take (oPos s j)).length := count_true_add_count_false _
  rw [List.length_take] at h2
  omega

/-- The `j`-th opener has at least `j` earlier positions. -/
theorem le_oPos {s : List Bool} {j : ℕ} (hj : j < s.count true) :
    j ≤ oPos s j := by
  have h1 := count_true_take_oPos hj
  have hlt : oPos s j < s.length := oPos_lt_length hj
  have h2 : (s.take (oPos s j)).count true + (s.take (oPos s j)).count false
      = (s.take (oPos s j)).length := count_true_add_count_false _
  rw [List.length_take] at h2
  omega

/-- M3: `o_J < q_K ↔ c_J ≤ K`. -/
theorem oPos_lt_qPos_iff {s : List Bool} {J K : ℕ} (hJ : J < s.count true)
    (hK : K < s.count false) :
    oPos s J < qPos s K ↔ (s.take (oPos s J)).count false ≤ K := by
  have h1 := qPos_lt_oPos_iff hJ hK
  have h2 := qPos_ne_oPos hJ hK
  omega

/-- **Lemma 3, master form.** For a balanced word (`#U = #D = n`), validity of a
sign word becomes a pure count condition: writing `c_J := o_J - J` for the number
of closers before the `J`-th opener (so `J - c_J` is the start height of arc `J`),
`ε` is valid iff `ε_K ≠ ε_J` whenever `1 ≤ c_J ≤ K < J < n` (0-based arcs, the
sign of arc `j` being `ε.getD (j-1)`). -/
theorem validSign_iff_count {n : ℕ} {s : List Bool} (htrue : s.count true = n)
    (hfalse : s.count false = n) (ε : List Bool) :
    ValidSign n s ε ↔
      ∀ J < n, ∀ K < n, 1 ≤ oPos s J - J → oPos s J - J ≤ K → K < J →
        ε.getD (K - 1) false ≠ ε.getD (J - 1) false := by
  subst htrue
  constructor
  · intro H J hJ K hK h1 h2 h3
    have hcJ := count_false_take_oPos hJ
    exact H J hJ K hK
      ((qPos_lt_oPos_iff hJ (K := 0) (by omega)).mpr (by omega))
      ((oPos_lt_oPos_iff hJ hK).mpr h3)
      ((oPos_lt_qPos_iff hJ (by omega)).mpr (by omega))
  · intro H J hJ K hK hlate hopen1 hopen2
    have hcJ := count_false_take_oPos hJ
    have h1 := (qPos_lt_oPos_iff hJ (K := 0) (by omega)).mp hlate
    have h2 := (oPos_lt_qPos_iff hJ (by omega)).mp hopen2
    have h3 := (oPos_lt_oPos_iff hJ hK).mp hopen1
    exact H J hJ K hK (by omega) (by omega) h3

/-! ## Position-to-arc recovery and monotonicity -/

/-- An opener position `p` is the `(s.take p).count true`-th opener. -/
theorem oPos_count_take {s : List Bool} {p : ℕ} (hp : p < s.length)
    (hb : s.getD p false = true) :
    oPos s ((s.take p).count true) = p := by
  have hx : p ∈ posOf true s := mem_posOf.mpr ⟨hp, hb⟩
  rw [oPos_eq_posOf_getD, count_take_eq_length_filter true s (le_of_lt hp),
    getD_length_filter (pairwise_posOf true s) hx]

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

/-- `c_j = o_j - j` is nondecreasing in the arc index. -/
theorem closersBefore_mono {s : List Bool} {j k : ℕ} (hjk : j ≤ k)
    (hk : k < s.count true) :
    oPos s j - j ≤ oPos s k - k := by
  have hj : j < s.count true := by omega
  rw [← count_false_take_oPos hj, ← count_false_take_oPos hk]
  have hoo : oPos s j ≤ oPos s k := by
    rcases Nat.eq_or_lt_of_le hjk with heq | hlt
    · rw [heq]
    · exact le_of_lt ((oPos_lt_oPos_iff hk hj).mpr hlt)
  have heq : s.take (oPos s j) = (s.take (oPos s k)).take (oPos s j) := by
    rw [List.take_take, Nat.min_eq_left hoo]
  rw [heq]
  exact ((List.take_prefix _ _).sublist).count_le false

/-! ## Run decompositions -/

theorem head_dropWhile_false {p : Bool → Bool} :
    ∀ {l : List Bool} {b : Bool} {bs : List Bool},
      l.dropWhile p = b :: bs → p b = false := by
  intro l
  induction l with
  | nil => intro b bs h; simp [List.dropWhile] at h
  | cons a l ih =>
    intro b bs h
    rw [List.dropWhile_cons] at h
    by_cases hpa : p a = true
    · rw [if_pos hpa] at h
      exact ih h
    · rw [if_neg hpa] at h
      injection h with h1 _
      subst h1
      simpa using hpa

theorem eq_replicate_takeWhile_true_append (s : List Bool) :
    s = List.replicate (s.takeWhile (· = true)).length true
      ++ s.dropWhile (· = true) := by
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := (· = true)) (l := s)]
  congr 1
  apply List.eq_replicate_of_mem
  intro b hb
  have := List.mem_takeWhile_imp hb
  simpa using this

theorem eq_replicate_takeWhile_false_append (s : List Bool) :
    s = List.replicate (s.takeWhile (· = false)).length false
      ++ s.dropWhile (· = false) := by
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := (· = false)) (l := s)]
  congr 1
  apply List.eq_replicate_of_mem
  intro b hb
  have := List.mem_takeWhile_imp hb
  simpa using this

/-! ## Dyck glue, Bool glue, firstAscent computation -/

theorem isDyck_iff {n : ℕ} {s : List Bool} :
    IsDyck n s ↔ s.length = 2 * n ∧ s.count true = n ∧ PrefixOK 0 s := by
  unfold IsDyck PrefixOK
  simp

theorem eq_not_of_ne {x y : Bool} (h : x ≠ y) : y = !x := by
  cases x <;> cases y <;> simp_all

theorem eq_not_of_ne' {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

theorem ne_of_eq_not {x y : Bool} (h : y = !x) : x ≠ y := by
  cases x <;> cases y <;> simp_all

theorem ne_of_eq_not' {x y : Bool} (h : x = !y) : x ≠ y := by
  cases x <;> cases y <;> simp_all

theorem firstAscent_replicate_true_cons_false (a : ℕ) (x : List Bool) :
    firstAscent (List.replicate a true ++ false :: x) = a := by
  induction a with
  | zero =>
    show (List.takeWhile (· = true) (List.replicate 0 true ++ false :: x)).length = 0
    rw [List.replicate_zero, List.nil_append,
      List.takeWhile_cons_of_neg (by simp)]
    rfl
  | succ a ih =>
    show (List.takeWhile (· = true)
      (List.replicate (a + 1) true ++ false :: x)).length = a + 1
    rw [List.replicate_succ, List.cons_append,
      List.takeWhile_cons_of_pos (by simp), List.length_cons]
    have : (List.takeWhile (· = true) (List.replicate a true ++ false :: x)).length
        = a := ih
    omega

end ShapesH

end ElizaldeLuo
