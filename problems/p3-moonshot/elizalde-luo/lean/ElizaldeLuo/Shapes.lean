/-
# The shape classification (bijection.md §5) and valid sign words on admissible shapes (§6)

Lemma 4 (obstructions): a shape with ≥ 2 gap openers, or a tail opener of start
height ≥ 2, admits no valid sign word. Lemma 5: the remaining ("admissible") shapes
are exactly the staircase (S), the no-gap shapes (I) `U^a D^a · Tail(0; 0, δ)`, and
the one-gap shapes (II) `U^a D^i U D^(a-i) · Tail(1; δ)`. Lemma 6 computes validity
locally on each of these; Corollary 6.1 makes the valid sign words a free
`{L,H}^F(s)`.

Audit notes incorporated (final-results.json, bijection.md audits — presentational):
- Lemma 4 tail case: `K ≥ 2` (1-based) follows from Observation 4.1 / `K = J-2 ≥ c+1 ≥ a+1`.
- Cor 6.1's "where ε_{j-1} lives" list is case-dependent; the statements below are
  split by case (S)/(I)/(II) accordingly.
- Theorem B step 4 tacitly uses that the rebuilt shape classifies into the same
  case — that is exactly the converse half of Lemma 5 (`isDyck_shapeI` /
  `firstAscent_shapeI` / `shapeI_param_inj` etc. below).

0-based conventions: arcs `0..n-1` (draft arc `J` = `J-1` here); the sign of arc
`j ≥ 1` is `ε.getD (j-1) false`; in case (I) the parameter `a` ranges in `1..n-1`,
in case (II) `a` in `2..n-1` and `i` in `1..a-1` (both as in the draft, which is
already 1-based in `a` and `i` — these are counts, not positions); `δ : List Bool`
has length `n-a-1`, entry `r` being the start-height bit of 0-based tail arc
`a+1+r` (draft tail arc `a+2+r`).

SORRY PACKAGE "shapes": COMPLETE — all 11 statements proven (no `sorry` left).
Generic infrastructure lives in Helpers_shapes.lean (`ShapesH` namespace);
helpers that mention `tailWord`/the shape families continue that namespace
below (they cannot move out, the definitions live here).
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo
import ElizaldeLuo.TheoremA
import ElizaldeLuo.Helpers_shapes

namespace ElizaldeLuo

/-! ## The three admissible shape families -/

/-- `Tail(h₀; d₁,…,d_m)` (bijection.md Lemma 5): "start with `h := h₀`; for
`r = 1,…,m` emit `D^(h - d_r)` then `U` and set `h := d_r + 1`; finally emit `D^h`."
Here `d_r ∈ {0,1}` is encoded as `Bool` (`true` = 1). ℕ-subtraction makes this
junk-total (the side condition `d₁ ≤ h₀` for `m ≥ 1` is a hypothesis of the lemmas,
not of the definition). -/
def tailWord : ℕ → List Bool → List Bool
  | h, [] => List.replicate h false
  | h, d :: ds =>
      List.replicate (h - (if d then 1 else 0)) false ++
        true :: tailWord ((if d then 1 else 0) + 1) ds

/-- Case (S), the staircase: `s = U^n D^n` (first ascent `a = n`, no parameters). -/
def shapeS (n : ℕ) : List Bool :=
  List.replicate n true ++ List.replicate n false

/-- Case (I): no gap opener; parameters `(a, δ)` with `1 ≤ a ≤ n-1` and
`δ ∈ {0,1}^(n-a-1)`; `s = U^a D^a · Tail(0; δ_{a+1},…,δ_n)` with `δ_{a+1} := 0`
(the leading `false` below). -/
def shapeI (a : ℕ) (δ : List Bool) : List Bool :=
  List.replicate a true ++ List.replicate a false ++ tailWord 0 (false :: δ)

/-- Case (II): exactly one gap opener, belonging to arc `B = a+1` (draft 1-based),
with `i` closers before it; parameters `(a, i, δ)` with `2 ≤ a ≤ n-1`,
`1 ≤ i ≤ a-1`, `δ ∈ {0,1}^(n-a-1)`; `s = U^a D^i U D^(a-i) · Tail(1; δ_{a+2},…,δ_n)`. -/
def shapeII (a i : ℕ) (δ : List Bool) : List Bool :=
  List.replicate a true ++ List.replicate i false ++
    true :: (List.replicate (a - i) false ++ tailWord 1 δ)

/-! ## Helpers mentioning `tailWord` and the shape families
(continuing the `ShapesH` namespace of Helpers_shapes.lean; the definitions
live in this file, so these lemmas cannot move there) -/

namespace ShapesH

/-! ### tailWord: scan lemmas -/

theorem tailWord_nil (h : ℕ) : tailWord h [] = List.replicate h false := rfl

theorem tailWord_cons (h : ℕ) (d : Bool) (ds : List Bool) :
    tailWord h (d :: ds) =
      List.replicate (h - (if d then 1 else 0)) false ++
        true :: tailWord ((if d then 1 else 0) + 1) ds := rfl

theorem tailWord_zero_cons_false (δ : List Bool) :
    tailWord 0 (false :: δ) = true :: tailWord 1 δ := by
  simp [tailWord]

theorem count_true_tailWord (δ : List Bool) : ∀ h : ℕ, 1 ≤ h →
    (tailWord h δ).count true = δ.length := by
  induction δ with
  | nil => intro h _; simp [tailWord_nil, List.count_replicate]
  | cons d ds ih =>
    intro h hh
    have hd : (if d then 1 else 0) ≤ 1 := by cases d <;> simp
    have ht := ih ((if d then 1 else 0) + 1) (by omega)
    rw [tailWord_cons]
    simp [List.count_append, List.count_replicate, ht]

theorem count_false_tailWord (δ : List Bool) : ∀ h : ℕ, 1 ≤ h →
    (tailWord h δ).count false = h + δ.length := by
  induction δ with
  | nil => intro h _; simp [tailWord_nil]
  | cons d ds ih =>
    intro h hh
    have hd : (if d then 1 else 0) ≤ 1 := by cases d <;> simp
    have ht := ih ((if d then 1 else 0) + 1) (by omega)
    rw [tailWord_cons]
    simp [List.count_append, ht]
    omega

theorem length_tailWord (δ : List Bool) : ∀ h : ℕ, 1 ≤ h →
    (tailWord h δ).length = h + 2 * δ.length := by
  induction δ with
  | nil => intro h _; simp [tailWord_nil]
  | cons d ds ih =>
    intro h hh
    have hd : (if d then 1 else 0) ≤ 1 := by cases d <;> simp
    have ht := ih ((if d then 1 else 0) + 1) (by omega)
    rw [tailWord_cons]
    simp [ht]
    omega

theorem prefixOK_tailWord (δ : List Bool) : ∀ h : ℕ, 1 ≤ h →
    PrefixOK h (tailWord h δ) := by
  induction δ with
  | nil =>
    intro h _
    rw [tailWord_nil, ← List.append_nil (List.replicate h false),
      prefixOK_replicate_false_append]
    exact ⟨le_refl h, prefixOK_nil _⟩
  | cons d ds ih =>
    intro h hh
    have hd : (if d then 1 else 0) ≤ 1 := by cases d <;> simp
    rw [tailWord_cons, prefixOK_replicate_false_append]
    refine ⟨by omega, ?_⟩
    rw [prefixOK_cons_true]
    have he : h - (h - (if d then 1 else 0)) + 1 = (if d then 1 else 0) + 1 := by
      omega
    rw [he]
    exact ih _ (by omega)

/-! ### Explicit opener positions of `tailWord` and of the three shapes -/

/-- Opener positions of `tailWord h δ` (relative to its start). -/
def tailOpenerPos (h : ℕ) : List Bool → List ℕ
  | [] => []
  | d :: ds =>
      (h - (if d then 1 else 0)) ::
        (tailOpenerPos ((if d then 1 else 0) + 1) ds).map
          (· + (h - (if d then 1 else 0) + 1))

theorem length_tailOpenerPos (δ : List Bool) : ∀ h : ℕ,
    (tailOpenerPos h δ).length = δ.length := by
  induction δ with
  | nil => intro h; rfl
  | cons d ds ih =>
    intro h
    rw [tailOpenerPos, List.length_cons, List.length_map, ih, List.length_cons]

theorem posOf_true_tailWord (δ : List Bool) : ∀ h : ℕ,
    posOf true (tailWord h δ) = tailOpenerPos h δ := by
  induction δ with
  | nil =>
    intro h
    rw [tailWord_nil, posOf_replicate_ne (by simp)]
    rfl
  | cons d ds ih =>
    intro h
    rw [tailWord_cons, posOf_append, posOf_replicate_ne (by simp),
      List.nil_append, posOf_cons, if_pos rfl, ih, List.length_replicate,
      tailOpenerPos]
    simp only [List.singleton_append, List.map_cons, List.map_map]
    congr 1
    · omega
    · apply List.map_congr_left
      intro x _
      simp only [Function.comp_apply]
      omega

theorem getD_tailOpenerPos (δ : List Bool) : ∀ h r : ℕ, 1 ≤ h → r < δ.length →
    (tailOpenerPos h δ).getD r 0 =
      h + 2 * r - (if δ.getD r false then 1 else 0) := by
  induction δ with
  | nil => intro h r _ hr; simp at hr
  | cons d ds ih =>
    intro h r hh hr
    have hd : (if d then 1 else 0) ≤ 1 := by cases d <;> simp
    match r with
    | 0 =>
      rw [tailOpenerPos, List.getD_cons_zero, List.getD_cons_zero]
      omega
    | r + 1 =>
      rw [tailOpenerPos, List.getD_cons_succ, List.getD_cons_succ,
        getD_map_of_lt (by rw [length_tailOpenerPos]; simpa using hr),
        ih _ r (by omega) (by simpa using hr)]
      have he : (if ds.getD r false then 1 else 0) ≤ 1 := by
        cases ds.getD r false <;> simp
      omega

/-! ### shapeS computations -/

theorem count_true_shapeS (n : ℕ) : (shapeS n).count true = n := by
  unfold shapeS
  simp [List.count_append, List.count_replicate]

theorem count_false_shapeS (n : ℕ) : (shapeS n).count false = n := by
  unfold shapeS
  simp [List.count_append, List.count_replicate]

theorem posOf_true_shapeS (n : ℕ) : posOf true (shapeS n) = List.range n := by
  unfold shapeS
  rw [posOf_append, posOf_replicate_self, posOf_replicate_ne (by simp)]
  simp

theorem oPos_shapeS {n j : ℕ} (hj : j < n) : oPos (shapeS n) j = j := by
  rw [oPos_eq_posOf_getD, posOf_true_shapeS,
    List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_range]

/-! ### shapeI computations -/

theorem shapeI_eq (a : ℕ) (δ : List Bool) :
    shapeI a δ = List.replicate a true ++
      (List.replicate a false ++ (true :: tailWord 1 δ)) := by
  unfold shapeI
  rw [tailWord_zero_cons_false, List.append_assoc]

theorem count_true_shapeI (a : ℕ) (δ : List Bool) :
    (shapeI a δ).count true = a + 1 + δ.length := by
  rw [shapeI_eq]
  simp [List.count_append, List.count_replicate,
    count_true_tailWord δ 1 (le_refl 1)]
  omega

theorem count_false_shapeI (a : ℕ) (δ : List Bool) :
    (shapeI a δ).count false = a + 1 + δ.length := by
  rw [shapeI_eq]
  simp [List.count_append, List.count_replicate,
    count_false_tailWord δ 1 (le_refl 1)]
  omega

theorem posOf_true_shapeI (a : ℕ) (δ : List Bool) :
    posOf true (shapeI a δ) =
      List.range a ++ 2 * a :: (tailOpenerPos 1 δ).map (· + (2 * a + 1)) := by
  rw [shapeI_eq, posOf_append, posOf_append, posOf_replicate_self,
    posOf_replicate_ne (by simp), List.nil_append, posOf_cons, if_pos rfl,
    posOf_true_tailWord]
  simp only [List.length_replicate, List.singleton_append, List.map_cons,
    List.map_map]
  congr 2
  · omega
  · apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    omega

theorem oPos_shapeI_lt {a j : ℕ} {δ : List Bool} (hj : j < a) :
    oPos (shapeI a δ) j = j := by
  rw [oPos_eq_posOf_getD, posOf_true_shapeI,
    List.getD_append _ _ _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_range]

theorem oPos_shapeI_self {a : ℕ} {δ : List Bool} :
    oPos (shapeI a δ) a = 2 * a := by
  rw [oPos_eq_posOf_getD, posOf_true_shapeI,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem oPos_shapeI_tail {a r : ℕ} {δ : List Bool} (hr : r < δ.length) :
    oPos (shapeI a δ) (a + 1 + r) =
      2 * a + 2 + 2 * r - (if δ.getD r false then 1 else 0) := by
  rw [oPos_eq_posOf_getD, posOf_true_shapeI,
    List.getD_append_right _ _ _ _ (by rw [List.length_range]; omega)]
  have hidx : a + 1 + r - (List.range a).length = r + 1 := by
    rw [List.length_range]; omega
  rw [hidx, List.getD_cons_succ,
    getD_map_of_lt (by rw [length_tailOpenerPos]; exact hr),
    getD_tailOpenerPos δ 1 r (le_refl 1) hr]
  have he : (if δ.getD r false then 1 else 0) ≤ 1 := by
    cases δ.getD r false <;> simp
  omega

/-! ### shapeII computations -/

theorem shapeII_eq (a i : ℕ) (δ : List Bool) :
    shapeII a i δ = List.replicate a true ++
      (List.replicate i false ++
        (true :: (List.replicate (a - i) false ++ tailWord 1 δ))) := by
  unfold shapeII
  rw [List.append_assoc]

theorem count_true_shapeII (a i : ℕ) (δ : List Bool) :
    (shapeII a i δ).count true = a + 1 + δ.length := by
  rw [shapeII_eq]
  simp [List.count_append, List.count_replicate,
    count_true_tailWord δ 1 (le_refl 1)]
  omega

theorem count_false_shapeII {a i : ℕ} (hi : i ≤ a) (δ : List Bool) :
    (shapeII a i δ).count false = a + 1 + δ.length := by
  rw [shapeII_eq]
  simp [List.count_append, List.count_replicate,
    count_false_tailWord δ 1 (le_refl 1)]
  omega

theorem posOf_true_shapeII {a i : ℕ} (hi : i ≤ a) (δ : List Bool) :
    posOf true (shapeII a i δ) =
      List.range a ++ (a + i) :: (tailOpenerPos 1 δ).map (· + (2 * a + 1)) := by
  rw [shapeII_eq, posOf_append, posOf_append, posOf_replicate_self,
    posOf_replicate_ne (by simp), List.nil_append, posOf_cons, if_pos rfl,
    posOf_append, posOf_replicate_ne (by simp), List.nil_append,
    posOf_true_tailWord]
  simp only [List.length_replicate, List.singleton_append, List.map_cons,
    List.map_map]
  congr 2
  · omega
  · apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    omega

theorem oPos_shapeII_lt {a i j : ℕ} {δ : List Bool} (hi : i ≤ a) (hj : j < a) :
    oPos (shapeII a i δ) j = j := by
  rw [oPos_eq_posOf_getD, posOf_true_shapeII hi,
    List.getD_append _ _ _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_range]

theorem oPos_shapeII_self {a i : ℕ} {δ : List Bool} (hi : i ≤ a) :
    oPos (shapeII a i δ) a = a + i := by
  rw [oPos_eq_posOf_getD, posOf_true_shapeII hi,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem oPos_shapeII_tail {a i r : ℕ} {δ : List Bool} (hi : i ≤ a)
    (hr : r < δ.length) :
    oPos (shapeII a i δ) (a + 1 + r) =
      2 * a + 2 + 2 * r - (if δ.getD r false then 1 else 0) := by
  rw [oPos_eq_posOf_getD, posOf_true_shapeII hi,
    List.getD_append_right _ _ _ _ (by rw [List.length_range]; omega)]
  have hidx : a + 1 + r - (List.range a).length = r + 1 := by
    rw [List.length_range]; omega
  rw [hidx, List.getD_cons_succ,
    getD_map_of_lt (by rw [length_tailOpenerPos]; exact hr),
    getD_tailOpenerPos δ 1 r (le_refl 1) hr]
  have he : (if δ.getD r false then 1 else 0) ≤ 1 := by
    cases δ.getD r false <;> simp
  omega

/-! ### Lengths and prefix conditions of the shapes -/

theorem length_shapeS (n : ℕ) : (shapeS n).length = 2 * n := by
  simp [shapeS]
  omega

theorem length_shapeI (a : ℕ) (δ : List Bool) :
    (shapeI a δ).length = 2 * (a + 1 + δ.length) := by
  rw [shapeI_eq]
  simp [length_tailWord δ 1 (le_refl 1)]
  omega

theorem length_shapeII {a i : ℕ} (hi : i ≤ a) (δ : List Bool) :
    (shapeII a i δ).length = 2 * (a + 1 + δ.length) := by
  rw [shapeII_eq]
  simp [length_tailWord δ 1 (le_refl 1)]
  omega

theorem prefixOK_shapeS (n : ℕ) : PrefixOK 0 (shapeS n) := by
  unfold shapeS
  rw [prefixOK_replicate_true_append, ← List.append_nil (List.replicate n false),
    prefixOK_replicate_false_append]
  exact ⟨by omega, prefixOK_nil _⟩

theorem prefixOK_shapeI (a : ℕ) (δ : List Bool) : PrefixOK 0 (shapeI a δ) := by
  rw [shapeI_eq, prefixOK_replicate_true_append, prefixOK_replicate_false_append]
  refine ⟨by omega, ?_⟩
  rw [prefixOK_cons_true]
  have he : 0 + a - a + 1 = 1 := by omega
  rw [he]
  exact prefixOK_tailWord δ 1 (le_refl 1)

theorem prefixOK_shapeII {a i : ℕ} (hi : i ≤ a) (δ : List Bool) :
    PrefixOK 0 (shapeII a i δ) := by
  rw [shapeII_eq, prefixOK_replicate_true_append, prefixOK_replicate_false_append]
  refine ⟨by omega, ?_⟩
  rw [prefixOK_cons_true, prefixOK_replicate_false_append]
  refine ⟨by omega, ?_⟩
  have he : 0 + a - i + 1 - (a - i) = 1 := by omega
  rw [he]
  exact prefixOK_tailWord δ 1 (le_refl 1)

/-! ### tailWord injectivity, absorption, and reconstruction -/

theorem tailWord_inj (δ : List Bool) : ∀ (δ' : List Bool) (h : ℕ), 1 ≤ h →
    tailWord h δ = tailWord h δ' → δ = δ' := by
  induction δ with
  | nil =>
    intro δ' h hh heq
    cases δ' with
    | nil => rfl
    | cons d' ds' =>
      exfalso
      have hc := congrArg (List.count true) heq
      rw [count_true_tailWord [] h hh, count_true_tailWord (d' :: ds') h hh] at hc
      simp at hc
  | cons d ds ih =>
    intro δ' h hh heq
    cases δ' with
    | nil =>
      exfalso
      have hc := congrArg (List.count true) heq
      rw [count_true_tailWord (d :: ds) h hh, count_true_tailWord [] h hh] at hc
      simp at hc
    | cons d' ds' =>
      have hpos := congrArg (posOf true) heq
      rw [posOf_true_tailWord, posOf_true_tailWord, tailOpenerPos,
        tailOpenerPos] at hpos
      injection hpos with hhead _
      have hd : d = d' := by
        cases d <;> cases d' <;> simp at hhead ⊢ <;> omega
      subst hd
      rw [tailWord_cons, tailWord_cons] at heq
      have h2 := List.append_cancel_left heq
      injection h2 with _ h3
      rw [ih ds' _ (by omega) h3]

/-- Absorbing a `D`-run into a tail scan: `D^m · Tail(1; δ) = Tail(m+1; δ)`. -/
theorem replicate_append_tailWord (m : ℕ) (δ : List Bool) :
    List.replicate m false ++ tailWord 1 δ = tailWord (m + 1) δ := by
  cases δ with
  | nil =>
    rw [tailWord_nil, tailWord_nil, ← List.replicate_add]
  | cons d ds =>
    rw [tailWord_cons, tailWord_cons, ← List.append_assoc, ← List.replicate_add]
    have hd : (if d then 1 else 0) ≤ 1 := by cases d <;> simp
    have he : m + (1 - if d then 1 else 0) = m + 1 - (if d then 1 else 0) := by
      omega
    rw [he]

/-- **Tail reconstruction** (the forced-`D`-run argument of Lemma 5). A balanced
positive-start segment all of whose openers start at height `≤ 1` is a `tailWord`. -/
theorem tailWord_reconstruct : ∀ (N : ℕ) (T : List Bool) (h : ℕ), 1 ≤ h →
    T.count true = N →
    PrefixOK h T → T.count false = h + T.count true →
    (∀ k, k < T.length → T.getD k false = true →
      h + (T.take k).count true ≤ (T.take k).count false + 1) →
    ∃ δ : List Bool, δ.length = N ∧ T = tailWord h δ := by
  intro N
  induction N with
  | zero =>
    intro T h hh hct hpre hcf hop
    refine ⟨[], rfl, ?_⟩
    have hall : ∀ b ∈ T, b = false := by
      intro b hb
      cases b
      · rfl
      · exfalso
        have := List.count_pos_iff.mpr hb
        omega
    have hrep := List.eq_replicate_of_mem hall
    have hlen : T.length = h := by
      have h2 := count_true_add_count_false T
      omega
    rw [tailWord_nil, ← hlen]
    exact hrep
  | succ N ih =>
    intro T h hh hct hpre hcf hop
    have hdec := eq_replicate_takeWhile_false_append T
    set m := (T.takeWhile (· = false)).length with hm
    cases hdrop : T.dropWhile (· = false) with
    | nil =>
      exfalso
      rw [hdrop, List.append_nil] at hdec
      have : T.count true = 0 := by
        rw [hdec]
        simp [List.count_replicate]
      omega
    | cons b v =>
      have hb : b = true := by
        have := head_dropWhile_false hdrop
        simpa using this
      subst hb
      rw [hdrop] at hdec
      -- hdec : T = replicate m false ++ true :: v
      rw [hdec, prefixOK_replicate_false_append, prefixOK_cons_true] at hpre
      obtain ⟨hmh, hpre'⟩ := hpre
      have hctv : v.count true = N := by
        rw [hdec] at hct
        simp [List.count_append, List.count_replicate] at hct
        omega
      have hcfv : v.count false = (h - m + 1) + v.count true := by
        rw [hdec] at hcf hct
        simp [List.count_append, List.count_replicate] at hcf hct
        omega
      have hTlen : T.length = m + 1 + v.length := by
        rw [hdec]
        simp
        omega
      -- the first opener (at position `m`) has start height `h - m ≤ 1`
      have hgetDm : T.getD m false = true := by
        have hle : (List.replicate m false).length ≤ m := by simp
        rw [hdec, List.getD_append_right _ _ _ _ hle]
        simp
      have htakem_t : (T.take m).count true = 0 := by
        rw [hdec, List.take_append, List.take_of_length_le (by simp)]
        simp [List.count_replicate]
      have htakem_f : (T.take m).count false = m := by
        rw [hdec, List.take_append, List.take_of_length_le (by simp)]
        simp
      have hfirst : h ≤ m + 1 := by
        have := hop m (by omega) hgetDm
        omega
      -- transfer the opener-height condition to v
      have hop' : ∀ k, k < v.length → v.getD k false = true →
          (h - m + 1) + (v.take k).count true ≤ (v.take k).count false + 1 := by
        intro k hk hkb
        have hidx : m + 1 + k - (List.replicate m false).length = k + 1 := by
          rw [List.length_replicate]
          omega
        have hPgetD : T.getD (m + 1 + k) false = true := by
          rw [hdec, List.getD_append_right _ _ _ _ (by simp; omega), hidx,
            List.getD_cons_succ]
          exact hkb
        have htk_t : (T.take (m + 1 + k)).count true
            = 1 + (v.take k).count true := by
          rw [hdec, List.take_append, List.take_of_length_le (by simp; omega),
            hidx, List.take_succ_cons]
          simp [List.count_append, List.count_replicate]
          omega
        have htk_f : (T.take (m + 1 + k)).count false
            = m + (v.take k).count false := by
          rw [hdec, List.take_append, List.take_of_length_le (by simp; omega),
            hidx, List.take_succ_cons]
          simp [List.count_append]
        have := hop (m + 1 + k) (by omega) hPgetD
        omega
      obtain ⟨δ', hδ'l, hδ'e⟩ := ih v (h - m + 1) (by omega) hctv hpre' hcfv hop'
      refine ⟨decide (h - m = 1) :: δ', by simp [hδ'l], ?_⟩
      have hbit : (if (decide (h - m = 1) : Bool) then 1 else 0) = h - m := by
        by_cases hcase : h - m = 1
        · simp [hcase]
        · simp [hcase]
          omega
      rw [hdec, hδ'e, tailWord_cons, hbit]
      have h2 : h - (h - m) = m := by omega
      rw [h2]

end ShapesH

open ShapesH

/-! ## Lemma 5, converse half: the families are Dyck words with the stated data -/

/-- `shapeS n` is a Dyck word of semilength `n`. (Sorry package "shapes".) -/
theorem isDyck_shapeS (n : ℕ) : IsDyck n (shapeS n) := by
  rw [isDyck_iff]
  exact ⟨length_shapeS n, count_true_shapeS n, prefixOK_shapeS n⟩

/-- Lemma 5(I), converse: "for any such `(a, δ)` the displayed word is a Dyck word
of semilength `n` in case (I)". (Sorry package "shapes".) -/
theorem isDyck_shapeI {n a : ℕ} {δ : List Bool}
    (ha : 1 ≤ a) (han : a ≤ n - 1) (hδ : δ.length = n - a - 1) (hn : 1 ≤ n) :
    IsDyck n (shapeI a δ) := by
  rw [isDyck_iff]
  refine ⟨?_, ?_, prefixOK_shapeI a δ⟩
  · rw [length_shapeI]
    omega
  · rw [count_true_shapeI]
    omega

/-- Lemma 5(II), converse: "each `(a,i,δ)` yields a Dyck word of case (II)".
(Sorry package "shapes".) -/
theorem isDyck_shapeII {n a i : ℕ} {δ : List Bool}
    (ha : 2 ≤ a) (han : a ≤ n - 1) (hi : 1 ≤ i) (hia : i ≤ a - 1)
    (hδ : δ.length = n - a - 1) :
    IsDyck n (shapeII a i δ) := by
  have hia' : i ≤ a := by omega
  rw [isDyck_iff]
  refine ⟨?_, ?_, prefixOK_shapeII hia' δ⟩
  · rw [length_shapeII hia']
    omega
  · rw [count_true_shapeII]
    omega

/-- First ascents: `a(shapeS n) = n`, `a(shapeI a δ) = a`, `a(shapeII a i δ) = a`
(Lemma 5: "the first ascent is `a`"). Stated for `shapeI`; the `shapeS` case is
definitional and the `shapeII` case is analogous. (Sorry package "shapes".) -/
theorem firstAscent_shapeI {a : ℕ} {δ : List Bool} (ha : 1 ≤ a) :
    firstAscent (shapeI a δ) = a := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [shapeI_eq]
  exact firstAscent_replicate_true_cons_false (a' + 1)
    (List.replicate a' false ++ (true :: tailWord 1 δ))

/-- (Sorry package "shapes".) -/
theorem firstAscent_shapeII {a i : ℕ} {δ : List Bool} (hi : 1 ≤ i) :
    firstAscent (shapeII a i δ) = a := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [shapeII_eq]
  exact firstAscent_replicate_true_cons_false a
    (List.replicate i' false ++
      (true :: (List.replicate (a - (i' + 1)) false ++ tailWord 1 δ)))

/-- Lemma 5, uniqueness on case (I): `(a, δ) ↦ shapeI a δ` is injective (the draft:
"`s` is uniquely determined by the stated parameters"). (Sorry package "shapes".) -/
theorem shapeI_param_inj {a a' : ℕ} {δ δ' : List Bool}
    (ha : 1 ≤ a) (ha' : 1 ≤ a')
    (h : shapeI a δ = shapeI a' δ') : a = a' ∧ δ = δ' := by
  have haa : a = a' := by
    have hfa := congrArg firstAscent h
    rw [firstAscent_shapeI ha, firstAscent_shapeI ha'] at hfa
    exact hfa
  subst haa
  refine ⟨rfl, ?_⟩
  unfold shapeI at h
  have h2 := List.append_cancel_left h
  rw [tailWord_zero_cons_false, tailWord_zero_cons_false] at h2
  injection h2 with _ h3
  exact tailWord_inj δ δ' 1 (le_refl 1) h3

/-- Lemma 5, uniqueness on case (II). (Sorry package "shapes".) -/
theorem shapeII_param_inj {a a' i i' : ℕ} {δ δ' : List Bool}
    (ha : 2 ≤ a) (hi : 1 ≤ i) (hia : i ≤ a - 1)
    (ha' : 2 ≤ a') (hi' : 1 ≤ i') (hia' : i' ≤ a' - 1)
    (h : shapeII a i δ = shapeII a' i' δ') : a = a' ∧ i = i' ∧ δ = δ' := by
  have haa : a = a' := by
    have hfa := congrArg firstAscent h
    rw [firstAscent_shapeII hi, firstAscent_shapeII hi'] at hfa
    exact hfa
  subst haa
  have hii : i = i' := by
    have hoa := congrArg (fun s => oPos s a) h
    simp only at hoa
    rw [oPos_shapeII_self (by omega), oPos_shapeII_self (by omega)] at hoa
    omega
  subst hii
  refine ⟨rfl, rfl, ?_⟩
  unfold shapeII at h
  have h2 := List.append_cancel_left h
  injection h2 with _ h3
  exact tailWord_inj δ δ' 1 (le_refl 1) (List.append_cancel_left h3)

/-- **Lemmas 4 + 5 (classification).** Every Dyck word carrying at least one valid
sign word is of one of the three admissible forms. (Lemma 4 excludes ≥ 2 gap openers
and tail openers of start height ≥ 2; Lemma 5 identifies what remains. The two
hypotheses are logical complements, so cases S/I/II exhaust the shapes admitting a
valid `ε` — this exhaustiveness is cited by the Main theorem per audit fix (6) of
bijection.md §14.) (Sorry package "shapes" — headline.) -/
theorem admissible_classification {n : ℕ} {s : List Bool} (hs : IsDyck n s)
    (hex : ∃ ε ∈ strings Bool (n - 1), ValidSign n s ε) :
    s = shapeS n ∨
    (∃ a δ, 1 ≤ a ∧ a ≤ n - 1 ∧ δ.length = n - a - 1 ∧ s = shapeI a δ) ∨
    (∃ a i δ, 2 ≤ a ∧ a ≤ n - 1 ∧ 1 ≤ i ∧ i ≤ a - 1 ∧ δ.length = n - a - 1 ∧
      s = shapeII a i δ) := by
  obtain ⟨ε, hεmem, hvalid⟩ := hex
  rw [isDyck_iff] at hs
  obtain ⟨hlen, hct, hpre⟩ := hs
  have hcf : s.count false = n := by
    have := count_true_add_count_false s
    omega
  rw [validSign_iff_count hct hcf ε] at hvalid
  -- first-ascent decomposition: `s = U^a ++ (rest)`
  have hdec1 := eq_replicate_takeWhile_true_append s
  set a := (s.takeWhile (· = true)).length with ha_def
  -- closer-run decomposition of the rest
  have hdec2 := eq_replicate_takeWhile_false_append (s.dropWhile (· = true))
  set m := ((s.dropWhile (· = true)).takeWhile (· = false)).length with hm_def
  cases hdrop2 : (s.dropWhile (· = true)).dropWhile (· = false) with
  | nil =>
    -- no opener after the staircase: `s = U^a D^m` with `a = m = n`
    rw [hdrop2, List.append_nil] at hdec2
    rw [hdec2] at hdec1
    have hct2 := hct
    have hcf2 := hcf
    rw [hdec1] at hct2 hcf2
    simp [List.count_append, List.count_replicate] at hct2 hcf2
    left
    rw [hdec1, hct2, hcf2]
    rfl
  | cons b v =>
    have hb : b = true := by
      have := head_dropWhile_false hdrop2
      simpa using this
    subst hb
    rw [hdrop2] at hdec2
    rw [hdec2] at hdec1
    -- hdec1 : s = U^a ++ (D^m ++ U · v)
    have hct2 := hct
    have hcf2 := hcf
    have hlen2 := hlen
    rw [hdec1] at hct2 hcf2 hlen2
    simp [List.count_append, List.count_replicate] at hct2 hcf2
    simp at hlen2
    have hslen : s.length = a + m + 1 + v.length := by omega
    have hctv : v.count true = n - a - 1 := by omega
    have han1 : a + 1 ≤ n := by omega
    have hcfv : v.count false = n - m := by omega
    -- prefix conditions
    rw [hdec1, prefixOK_replicate_true_append, prefixOK_replicate_false_append,
      prefixOK_cons_true] at hpre
    obtain ⟨hma, hprev⟩ := hpre
    have hma' : m ≤ a := by omega
    -- the run after the first ascent is nonempty (it starts with the closer q_1)
    have hm1 : 1 ≤ m := by
      by_contra hm0
      have hm0' : m = 0 := by omega
      rw [hm0', List.replicate_zero, List.nil_append] at hdec2
      have := head_dropWhile_false hdec2
      simp at this
    have ha1 : 1 ≤ a := by omega
    -- the three-distinct-signs obstruction (Lemma 4 core)
    have hobs : ∀ X Y Z : ℕ, X < Y → Y < Z → Z < n →
        1 ≤ oPos s Y - Y → oPos s Y - Y ≤ X → oPos s Z - Z ≤ X → False := by
      intro X Y Z hXY hYZ hZn h1 h2 h3
      have hYn : Y < n := by omega
      have hXn : X < n := by omega
      have hmono : oPos s Y - Y ≤ oPos s Z - Z :=
        closersBefore_mono (le_of_lt hYZ) (by omega)
      have hA := hvalid Z hZn X hXn (by omega) (by omega) (by omega)
      have hB := hvalid Z hZn Y hYn (by omega) (by omega) hYZ
      have hC := hvalid Y hYn X hXn h1 h2 hXY
      have htriple : ∀ x y z : Bool, x ≠ z → y ≠ z → x ≠ y → False := by decide
      exact htriple _ _ _ hA hB hC
    -- the opener of arc `a` sits at position `a + m`
    have hoa : oPos s a = a + m := by
      have hP : s.getD (a + m) false = true := by
        rw [hdec1,
          List.getD_append_right _ _ _ _ (by rw [List.length_replicate]; omega)]
        have hidx : a + m - (List.replicate a true).length = m := by
          rw [List.length_replicate]; omega
        rw [hidx,
          List.getD_append_right _ _ _ _ (by simp)]
        have hidx2 : m - (List.replicate m false).length = 0 := by
          rw [List.length_replicate]; omega
        rw [hidx2, List.getD_cons_zero]
      have hQ : (s.take (a + m)).count true = a := by
        rw [hdec1, List.take_append,
          List.take_of_length_le (i := a + m) (by rw [List.length_replicate]; omega)]
        have hidx : a + m - (List.replicate a true).length = m := by
          rw [List.length_replicate]; omega
        rw [hidx, List.take_append,
          List.take_of_length_le (by simp)]
        have hidx2 : m - (List.replicate m false).length = 0 := by
          rw [List.length_replicate]; omega
        rw [hidx2, List.take_zero, List.append_nil]
        simp [List.count_append, List.count_replicate]
      have := oPos_count_take (s := s) (p := a + m) (by omega) hP
      rw [hQ] at this
      exact this
    -- arcs `≥ a` are late
    have hlate : ∀ j, a ≤ j → j < n → 1 ≤ oPos s j - j := by
      intro j haj hjn
      have := closersBefore_mono haj (by omega : j < s.count true)
      rw [hoa] at this
      omega
    -- every arc `≥ a + 1` starts at height ≤ 1 (kills two-gap and high tails)
    have hheight : ∀ Z, a + 1 ≤ Z → Z < n → Z ≤ (oPos s Z - Z) + 1 := by
      intro Z hZ1 hZn
      by_contra hcon
      refine hobs (Z - 2) (Z - 1) Z (by omega) (by omega) hZn ?_ ?_ ?_
      · exact hlate (Z - 1) (by omega) (by omega)
      · have := closersBefore_mono (s := s) (j := Z - 1) (k := Z)
          (by omega) (by omega)
        omega
      · omega
    -- transfer to the reconstruction hypothesis for v
    have hvopen : ∀ k, k < v.length → v.getD k false = true →
        (a - m + 1) + (v.take k).count true ≤ (v.take k).count false + 1 := by
      intro k hk hkb
      have hPlen : a + m + 1 + k < s.length := by omega
      have hidx : a + m + 1 + k - (List.replicate a true).length = m + 1 + k := by
        rw [List.length_replicate]; omega
      have hidx2 : m + 1 + k - (List.replicate m false).length = k + 1 := by
        rw [List.length_replicate]; omega
      have hPgetD : s.getD (a + m + 1 + k) false = true := by
        rw [hdec1,
          List.getD_append_right _ _ _ _ (by rw [List.length_replicate]; omega),
          hidx,
          List.getD_append_right _ _ _ _ (by rw [List.length_replicate]; omega),
          hidx2, List.getD_cons_succ]
        exact hkb
      have htkt : (s.take (a + m + 1 + k)).count true
          = a + 1 + (v.take k).count true := by
        rw [hdec1, List.take_append,
          List.take_of_length_le (by rw [List.length_replicate]; omega), hidx,
          List.take_append,
          List.take_of_length_le (by rw [List.length_replicate]; omega), hidx2,
          List.take_succ_cons]
        simp [List.count_append, List.count_replicate]
        omega
      have htkf : (s.take (a + m + 1 + k)).count false
          = m + (v.take k).count false := by
        rw [hdec1, List.take_append,
          List.take_of_length_le (by rw [List.length_replicate]; omega), hidx,
          List.take_append,
          List.take_of_length_le (by rw [List.length_replicate]; omega), hidx2,
          List.take_succ_cons]
        simp [List.count_append, List.count_replicate]
      have hZn : a + 1 + (v.take k).count true < n := by
        have := count_take_lt (s := v) (p := k) hk hkb
        omega
      have hoZ : oPos s (a + 1 + (v.take k).count true) = a + m + 1 + k := by
        have := oPos_count_take hPlen hPgetD
        rw [htkt] at this
        exact this
      have hh := hheight (a + 1 + (v.take k).count true) (by omega) hZn
      rw [hoZ] at hh
      have hcc := count_true_add_count_false (v.take k)
      rw [List.length_take] at hcc
      omega
    -- reconstruct the tail
    have hprev' : PrefixOK (a - m + 1) v := by
      have he : 0 + a - m + 1 = a - m + 1 := by omega
      rwa [he] at hprev
    have hcfv' : v.count false = (a - m + 1) + v.count true := by omega
    obtain ⟨δ, hδlen, hδeq⟩ := tailWord_reconstruct (v.count true) v (a - m + 1)
      (by omega) rfl hprev' hcfv' hvopen
    by_cases hcase : m = a
    · -- case (I)
      right; left
      refine ⟨a, δ, ha1, by omega, by omega, ?_⟩
      rw [hdec1, hδeq, hcase]
      have he : a - a + 1 = 1 := by omega
      rw [he, shapeI_eq]
    · -- case (II)
      right; right
      refine ⟨a, m, δ, by omega, by omega, hm1, by omega, by omega, ?_⟩
      rw [hdec1, hδeq, shapeII_eq, replicate_append_tailWord]

/-! ## Lemma 6: local form of validity on admissible shapes -/

/-- Lemma 6(S): on the staircase "every `ε` is valid. (There are no late arcs.)"
(Sorry package "shapes".) -/
theorem validSign_shapeS (n : ℕ) (ε : List Bool) :
    ValidSign n (shapeS n) ε := by
  rw [validSign_iff_count (count_true_shapeS n) (count_false_shapeS n)]
  intro J hJ K hK h1 h2 h3
  rw [oPos_shapeS hJ] at h1
  omega

/-- The tail constraint shared by cases (I) and (II): "for every tail arc `j` with
`δ_j = 1`: `ε_j = ¬ε_{j-1}`". 0-based: `δ.getD r false` is the height bit of arc
`a+1+r`, whose sign is `ε.getD (a+r) false`, the preceding arc's sign being
`ε.getD (a+r-1) false` (for `r = 0` that is arc `a`, i.e. the draft's arc `a+1` —
in case (II) that is the gap arc `B`). -/
def TailConstraint (a : ℕ) (δ ε : List Bool) : Prop :=
  ∀ r < δ.length, δ.getD r false = true →
    ε.getD (a + r) false = ! ε.getD (a + r - 1) false

instance (a : ℕ) (δ ε : List Bool) : Decidable (TailConstraint a δ ε) := by
  unfold TailConstraint; infer_instance

/-- Lemma 6(I): "`ε` is valid ⟺ for every tail arc `j ≥ a+2` with `δ_j = 1`:
`ε_j = ¬ε_{j-1}`. In particular `ε_2,…,ε_{a+1}` and `ε_j` for tail arcs with
`δ_j = 0` are unconstrained." (Sorry package "shapes".) -/
theorem validSign_shapeI_iff {n a : ℕ} {δ ε : List Bool}
    (ha : 1 ≤ a) (han : a ≤ n - 1) (hδ : δ.length = n - a - 1) (hn : 1 ≤ n)
    (hε : ε.length = n - 1) :
    ValidSign n (shapeI a δ) ε ↔ TailConstraint a δ ε := by
  have hct : (shapeI a δ).count true = n := by rw [count_true_shapeI]; omega
  have hcf : (shapeI a δ).count false = n := by rw [count_false_shapeI]; omega
  rw [validSign_iff_count hct hcf]
  constructor
  · intro H r hr hbit
    have hJ : a + 1 + r < n := by omega
    have hoJ := oPos_shapeI_tail (a := a) (δ := δ) hr
    rw [hbit] at hoJ
    simp at hoJ
    have hKn : a + r < n := by omega
    have hne := H (a + 1 + r) hJ (a + r) hKn (by rw [hoJ]; omega)
      (by rw [hoJ]; omega) (by omega)
    have hidx : a + 1 + r - 1 = a + r := by omega
    rw [hidx] at hne
    exact eq_not_of_ne hne
  · intro H J hJ K hK h1 h2 h3
    rcases Nat.lt_trichotomy J a with hJa | hJa | hJa
    · rw [oPos_shapeI_lt hJa] at h1
      omega
    · subst hJa
      rw [oPos_shapeI_self] at h1 h2
      omega
    · obtain ⟨r, rfl⟩ : ∃ r, J = a + 1 + r := ⟨J - a - 1, by omega⟩
      have hr : r < δ.length := by omega
      have hoJ := oPos_shapeI_tail (a := a) (δ := δ) hr
      cases hbit : δ.getD r false with
      | false =>
        rw [hbit] at hoJ
        simp at hoJ
        rw [hoJ] at h1 h2
        omega
      | true =>
        rw [hbit] at hoJ
        simp at hoJ
        rw [hoJ] at h1 h2
        have hKeq : K = a + r := by omega
        subst hKeq
        have heq := H r hr hbit
        have hidx : a + 1 + r - 1 = a + r := by omega
        rw [hidx]
        exact ne_of_eq_not heq

/-- Lemma 6(II): "`ε` is valid ⟺ `ε_{i+1} = ⋯ = ε_a = ¬ε_{a+1}` and for every tail
arc `j ≥ a+2` with `δ_j = 1`: `ε_j = ¬ε_{j-1}`. In particular `ε_2,…,ε_i`,
`ε_{a+1}`, and `ε_j` for tail arcs with `δ_j = 0` are unconstrained."
0-based: the block is `ε.getD (i-1+k) false` for `k < a-i`, and `ε_{a+1}` is
`ε.getD (a-1) false`. (Sorry package "shapes".) -/
theorem validSign_shapeII_iff {n a i : ℕ} {δ ε : List Bool}
    (ha : 2 ≤ a) (han : a ≤ n - 1) (hi : 1 ≤ i) (hia : i ≤ a - 1)
    (hδ : δ.length = n - a - 1) (hε : ε.length = n - 1) :
    ValidSign n (shapeII a i δ) ε ↔
      ((∀ k < a - i, ε.getD (i - 1 + k) false = ! ε.getD (a - 1) false) ∧
        TailConstraint a δ ε) := by
  have hia' : i ≤ a := by omega
  have hct : (shapeII a i δ).count true = n := by
    rw [count_true_shapeII]; omega
  have hcf : (shapeII a i δ).count false = n := by
    rw [count_false_shapeII hia']; omega
  rw [validSign_iff_count hct hcf]
  constructor
  · intro H
    constructor
    · intro k hk
      have hJ : a < n := by omega
      have hoJ := oPos_shapeII_self (δ := δ) hia'
      have hKn : i + k < n := by omega
      have hne := H a hJ (i + k) hKn (by rw [hoJ]; omega) (by rw [hoJ]; omega)
        (by omega)
      have hidx : i + k - 1 = i - 1 + k := by omega
      rw [hidx] at hne
      exact eq_not_of_ne' hne
    · intro r hr hbit
      have hJ : a + 1 + r < n := by omega
      have hoJ := oPos_shapeII_tail hia' hr
      rw [hbit] at hoJ
      simp at hoJ
      have hKn : a + r < n := by omega
      have hne := H (a + 1 + r) hJ (a + r) hKn (by rw [hoJ]; omega)
        (by rw [hoJ]; omega) (by omega)
      have hidx : a + 1 + r - 1 = a + r := by omega
      rw [hidx] at hne
      exact eq_not_of_ne hne
  · rintro ⟨Hblock, Htail⟩ J hJ K hK h1 h2 h3
    rcases Nat.lt_trichotomy J a with hJa | hJa | hJa
    · rw [oPos_shapeII_lt hia' hJa] at h1
      omega
    · subst hJa
      rw [oPos_shapeII_self hia'] at h1 h2
      have hk : K - i < J - i := by omega
      have heq := Hblock (K - i) hk
      have hidx : i - 1 + (K - i) = K - 1 := by omega
      rw [hidx] at heq
      exact ne_of_eq_not' heq
    · obtain ⟨r, rfl⟩ : ∃ r, J = a + 1 + r := ⟨J - a - 1, by omega⟩
      have hr : r < δ.length := by omega
      have hoJ := oPos_shapeII_tail hia' hr
      cases hbit : δ.getD r false with
      | false =>
        rw [hbit] at hoJ
        simp at hoJ
        rw [hoJ] at h1 h2
        omega
      | true =>
        rw [hbit] at hoJ
        simp at hoJ
        rw [hoJ] at h1 h2
        have hKeq : K = a + r := by omega
        subst hKeq
        have heq := Htail r hr hbit
        have hidx : a + 1 + r - 1 = a + r := by omega
        rw [hidx]
        exact ne_of_eq_not heq

end ElizaldeLuo
