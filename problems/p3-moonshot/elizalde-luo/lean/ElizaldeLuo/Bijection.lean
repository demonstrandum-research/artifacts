/-
# The bijection Φ/Ψ between valid pairs and the language W (bijection.md §8)

`Φ` encodes a valid pair `(s, ε)` as a ternary string of length `n` ("every free
coordinate of `ε` is written as its letter; every *forced* arc — block arcs, δ = 1
tail arcs — is written `C`; in case (I) the initial free block is shifted one slot
left so that position `a+1` can carry a `C` marking the end of the staircase; in
case (II) position 1 carries a `C` marking the presence of the gap opener; in case
(S) position 1 carries the padding letter `A`"). `Ψ` is the letter-by-letter parse.

Theorem B: `Φ` is a bijection from `{(s,ε) : s admissible, ε valid}` onto `W n`;
combined with Lemmas 4/5 (only admissible shapes carry valid sign words) this gives
`|validPairs n| = |W n|` — the second third of the proof chain.

Audit note (bijection.md §14 / final-results.json): Theorem B step 4 tacitly uses
that the rebuilt shape classifies into the same case; that is Lemma 5's converse
(`isDyck_shapeI`, `firstAscent_shapeI`, … in Shapes.lean) — cite it explicitly when
proving `phi_psi`.

SORRY PACKAGE "bijection": `phi_mem_W`, `psi_phi`, `psi_mem_validPairs`, `phi_psi`,
`card_validPairs_eq_card_W`.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo
import ElizaldeLuo.SignWord
import ElizaldeLuo.TheoremA
import ElizaldeLuo.Shapes
import ElizaldeLuo.WLang
import ElizaldeLuo.Helpers_bijection

namespace ElizaldeLuo

/-! ## Letter encoding of signs -/

/-- `ℓ(L) = A`, `ℓ(H) = B` (bijection.md §7). -/
def ltr (b : Bool) : ABC := if b then ABC.B else ABC.A

/-- `ℓ⁻¹`: `A ↦ L`, `B ↦ H` (junk on `C`: `false`). -/
def sgnOf (x : ABC) : Bool := x = ABC.B

/-- Does the shape have a gap opener? (an opener strictly between `q_1` and `q_a`;
detected as: some `U` among the `a` positions following the first ascent). -/
def hasGap (s : List Bool) (a : ℕ) : Bool :=
  ((s.drop a).take a).any (· = true)

/-- Number of closers before the gap opener (the draft's `i` in case (II)): the
length of the `D`-run starting right after the first ascent. -/
def gapIndex (s : List Bool) (a : ℕ) : ℕ :=
  ((s.drop a).takeWhile (· = false)).length

/-- The letters Φ writes for the tail arcs (draft positions `a+2 … n`, 0-based arcs
`a+1 … n-1`, shared by cases (I) and (II)): `C` if the arc's start height (`δ_j`)
is 1, else the sign letter of the arc. -/
def tailLetters (n : ℕ) (s ε : List Bool) (a : ℕ) : List ABC :=
  (List.range' (a + 1) (n - (a + 1))).map fun j =>
    if heightAt s (oPos s j) = 1 then ABC.C else ltr (ε.getD (j - 1) false)

/-- **Φ** (bijection.md §8, Definition of Φ), by cases on Lemma 5's classification:

- (S) (`s = U^n D^n`): `σ₁ = A`; `σ_j = ℓ(ε_j)` for `2 ≤ j ≤ n`.
- (I) (parameters `a, δ`): `σ_j = ℓ(ε_{j+1})` for `1 ≤ j ≤ a`; `σ_{a+1} = C`;
  for `a+2 ≤ j ≤ n`: `σ_j = ℓ(ε_j)` if `δ_j = 0`, `C` if `δ_j = 1`.
- (II) (parameters `a, i, δ`): `σ₁ = C`; `σ_j = ℓ(ε_j)` for `2 ≤ j ≤ i`;
  `σ_j = C` for `i+1 ≤ j ≤ a`; `σ_{a+1} = ℓ(ε_{a+1})`; tail as in (I).

(Junk-total on non-admissible shapes; the lemmas below only invoke it on
`validPairs`.) -/
def phi (n : ℕ) (s ε : List Bool) : List ABC :=
  let a := firstAscent s
  if a = n then
    ABC.A :: ε.map ltr
  else if hasGap s a then
    let i := gapIndex s a
    ABC.C :: ((ε.take (i - 1)).map ltr ++ List.replicate (a - i) ABC.C ++
      [ltr (ε.getD (a - 1) false)] ++ tailLetters n s ε a)
  else
    (ε.take a).map ltr ++ ABC.C :: tailLetters n s ε a

/-- The tail parse shared by Ψ's cases (I) and (II) (bijection.md §8, Definition of
Ψ): processing tail letters left to right with the previous sign at hand, a `C`
means `δ_j = 1` and `ε_j := ¬ε_{j-1}`; a sign letter means `δ_j = 0` and
`ε_j := ℓ⁻¹(σ_j)`. Returns `(ε-tail, δ)`. -/
def tailParse : Bool → List ABC → List Bool × List Bool
  | _, [] => ([], [])
  | prev, x :: rest =>
      let e := if x = ABC.C then ! prev else sgnOf x
      let d : Bool := x = ABC.C
      let p := tailParse e rest
      (e :: p.1, d :: p.2)

/-- **Ψ** (bijection.md §8, "The parse"), producing the pair `(s, ε)`:

- no `C` in `σ`: case (S); `ε_j := ℓ⁻¹(σ_j)`.
- `σ₁ ≠ C ∋ σ`: case (I) with `a+1` = position of the first `C`;
  `ε_{j+1} := ℓ⁻¹(σ_j)` for `j ≤ a`; tail parsed by `tailParse`.
- `σ₁ = C`: case (II) with `i-1` = length of the maximal `{A,B}`-run from position
  2 and `a` = end of the maximal `C`-run from position `i+1`;
  `ε_{a+1} := ℓ⁻¹(σ_{a+1})`, block `ε_{i+1} = ⋯ = ε_a := ¬ε_{a+1}`,
  `ε_2..ε_i := ℓ⁻¹(σ_2..σ_i)`; tail parsed by `tailParse`. -/
def psi (n : ℕ) (σ : List ABC) : List Bool × List Bool :=
  if ABC.C ∉ σ then
    (shapeS n, (σ.drop 1).map sgnOf)
  else if σ.head? ≠ some ABC.C then
    let a := (σ.takeWhile (· ≠ ABC.C)).length
    let head := (σ.take a).map sgnOf
    let t := tailParse (head.getLastD false) (σ.drop (a + 1))
    (shapeI a t.2, head ++ t.1)
  else
    let i := 1 + ((σ.drop 1).takeWhile (· ≠ ABC.C)).length
    let a := i + ((σ.drop i).takeWhile (· = ABC.C)).length
    let εab := ((σ.drop 1).take (i - 1)).map sgnOf
    let εa1 := sgnOf (σ.getD a ABC.A)
    let t := tailParse εa1 (σ.drop (a + 1))
    (shapeII a i t.2, εab ++ List.replicate (a - i) (! εa1) ++ εa1 :: t.1)

/-! ## Letter/sign basics -/

theorem ltr_ne_C (b : Bool) : ltr b ≠ ABC.C := by cases b <;> simp [ltr]

theorem sgnOf_ltr (b : Bool) : sgnOf (ltr b) = b := by cases b <;> simp [ltr, sgnOf]

theorem ltr_sgnOf {x : ABC} (hx : x ≠ ABC.C) : ltr (sgnOf x) = x := by
  cases x
  · simp [ltr, sgnOf]
  · simp [ltr, sgnOf]
  · exact absurd rfl hx

theorem C_not_mem_map_ltr (l : List Bool) : ABC.C ∉ l.map ltr := by
  intro h
  obtain ⟨b, -, hb⟩ := List.mem_map.mp h
  exact ltr_ne_C b hb

theorem map_sgnOf_map_ltr (l : List Bool) : (l.map ltr).map sgnOf = l := by
  rw [List.map_map]
  have h : ∀ x ∈ l, (sgnOf ∘ ltr) x = id x := fun x _ => sgnOf_ltr x
  rw [List.map_congr_left h, List.map_id]

theorem map_ltr_map_sgnOf {l : List ABC} (h : ∀ x ∈ l, x ≠ ABC.C) :
    (l.map sgnOf).map ltr = l := by
  rw [List.map_map]
  have h' : ∀ x ∈ l, (ltr ∘ sgnOf) x = id x := fun x hx => ltr_sgnOf (h x hx)
  rw [List.map_congr_left h', List.map_id]

theorem head?_ne_C_of_map_ltr {l : List Bool} (l' : List ABC) (hl : l ≠ []) :
    (l.map ltr ++ l').head? ≠ some ABC.C := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x t =>
      simp only [List.map_cons, List.cons_append, List.head?_cons]
      intro hc
      exact ltr_ne_C x (by injection hc)

/-! ## `tailParse`: equations and the four structural lemmas -/

theorem tailParse_nil (prev : Bool) : tailParse prev [] = ([], []) := rfl

theorem tailParse_cons (prev : Bool) (x : ABC) (rest : List ABC) :
    tailParse prev (x :: rest) =
      ((if x = ABC.C then ! prev else sgnOf x) ::
          (tailParse (if x = ABC.C then ! prev else sgnOf x) rest).1,
        (decide (x = ABC.C)) ::
          (tailParse (if x = ABC.C then ! prev else sgnOf x) rest).2) := rfl

theorem tailParse_cons_C (prev : Bool) (rest : List ABC) :
    tailParse prev (ABC.C :: rest) =
      ((! prev) :: (tailParse (! prev) rest).1,
        true :: (tailParse (! prev) rest).2) := by
  rw [tailParse_cons, if_pos rfl, decide_eq_true rfl]

theorem tailParse_cons_ltr (prev e : Bool) (rest : List ABC) :
    tailParse prev (ltr e :: rest) =
      (e :: (tailParse e rest).1, false :: (tailParse e rest).2) := by
  rw [tailParse_cons, if_neg (ltr_ne_C e), sgnOf_ltr, decide_eq_false (ltr_ne_C e)]

/-- Both outputs of the parse have the length of the input. -/
theorem tailParse_length (prev : Bool) (L : List ABC) :
    (tailParse prev L).1.length = L.length ∧ (tailParse prev L).2.length = L.length := by
  induction L generalizing prev with
  | nil => simp [tailParse_nil]
  | cons x rest ih =>
      obtain ⟨h1, h2⟩ := ih (if x = ABC.C then ! prev else sgnOf x)
      rw [tailParse_cons]
      simp [h1, h2]

/-- Forced-coordinate recovery (Theorem B step 3, the tail induction): the parse
inverts the canonical tail encoding `zipWith (δ, ε-tail)`, provided the `δ = 1`
coordinates satisfy the alternation forced by validity (Lemma 6). -/
theorem tailParse_zipWith (δ : List Bool) :
    ∀ (es : List Bool) (prev : Bool), δ.length = es.length →
      (∀ r < δ.length, δ.getD r false = true →
        es.getD r false = ! ((prev :: es).getD r false)) →
      tailParse prev (List.zipWith (fun d e => if d then ABC.C else ltr e) δ es) =
        (es, δ) := by
  induction δ with
  | nil =>
      intro es prev hlen _
      obtain rfl : es = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      simp [tailParse_nil]
  | cons d δ ih =>
      intro es prev hlen halt
      cases es with
      | nil => simp at hlen
      | cons e es =>
          have hlen' : δ.length = es.length := by simpa using hlen
          have halt' : ∀ r < δ.length, δ.getD r false = true →
              es.getD r false = ! ((e :: es).getD r false) := by
            intro r hr hd
            have h := halt (r + 1) (by simpa using Nat.succ_lt_succ hr)
              (by simpa [List.getD_cons_succ] using hd)
            simpa [List.getD_cons_succ] using h
          cases d with
          | false =>
              rw [List.zipWith_cons_cons]
              simp only [Bool.false_eq_true, if_false]
              rw [tailParse_cons_ltr, ih es e hlen' halt']
          | true =>
              have he : e = ! prev := by
                simpa [List.getD_cons_zero] using
                  halt 0 (by simp) (by simp [List.getD_cons_zero])
              rw [List.zipWith_cons_cons]
              simp only [if_true]
              rw [tailParse_cons_C, ih es (! prev) (by simpa using hlen')
                (by rw [← he]; exact halt'), ← he]

/-- Theorem B step 4, tail part: re-encoding the parse's output writes back exactly
the letters read. -/
theorem zipWith_tailParse (L : List ABC) :
    ∀ prev : Bool,
      List.zipWith (fun d e => if d then ABC.C else ltr e)
        (tailParse prev L).2 (tailParse prev L).1 = L := by
  induction L with
  | nil => intro prev; simp [tailParse_nil]
  | cons x rest ih =>
      intro prev
      by_cases hx : x = ABC.C
      · subst hx
        rw [tailParse_cons_C, List.zipWith_cons_cons, ih]
        simp
      · obtain ⟨e, rfl⟩ : ∃ e : Bool, x = ltr e := ⟨sgnOf x, (ltr_sgnOf hx).symm⟩
        rw [tailParse_cons_ltr, List.zipWith_cons_cons, ih]
        simp

/-- The parse output satisfies the alternation constraint by construction
(Lemma 6's condition for the rebuilt sign word; Theorem B step 2). -/
theorem tailParse_alternation (L : List ABC) :
    ∀ (prev : Bool) (r : ℕ), r < L.length → (tailParse prev L).2.getD r false = true →
      (tailParse prev L).1.getD r false =
        ! ((prev :: (tailParse prev L).1).getD r false) := by
  induction L with
  | nil => intro prev r hr; simp at hr
  | cons x rest ih =>
      intro prev r hr hd
      by_cases hx : x = ABC.C
      · subst hx
        rw [tailParse_cons_C] at hd ⊢
        cases r with
        | zero => simp [List.getD_cons_zero]
        | succ r =>
            simp only [List.getD_cons_succ] at hd ⊢
            exact ih (! prev) r (by simpa using hr) hd
      · obtain ⟨e, rfl⟩ : ∃ e : Bool, x = ltr e := ⟨sgnOf x, (ltr_sgnOf hx).symm⟩
        rw [tailParse_cons_ltr] at hd ⊢
        cases r with
        | zero => simp [List.getD_cons_zero] at hd
        | succ r =>
            simp only [List.getD_cons_succ] at hd ⊢
            exact ih e r (by simpa using hr) hd

/-! ## Branch equations for `psi` -/

theorem psi_caseS {n : ℕ} {σ : List ABC} (h : ABC.C ∉ σ) :
    psi n σ = (shapeS n, (σ.drop 1).map sgnOf) := by
  unfold psi
  rw [if_pos h]

theorem psi_caseI {n : ℕ} {σ : List ABC} (h1 : ABC.C ∈ σ) (h2 : σ.head? ≠ some ABC.C)
    {a : ℕ} (ha : (σ.takeWhile (· ≠ ABC.C)).length = a) :
    psi n σ =
      (shapeI a (tailParse (((σ.take a).map sgnOf).getLastD false) (σ.drop (a + 1))).2,
        (σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false) (σ.drop (a + 1))).1) := by
  unfold psi
  rw [if_neg (not_not_intro h1), if_pos h2]
  subst ha
  rfl

theorem psi_caseII {n : ℕ} {σ : List ABC} (h2 : σ.head? = some ABC.C) {i a : ℕ}
    (hi : 1 + ((σ.drop 1).takeWhile (· ≠ ABC.C)).length = i)
    (ha : i + ((σ.drop i).takeWhile (· = ABC.C)).length = a) :
    psi n σ =
      (shapeII a i (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).2,
        ((σ.drop 1).take (i - 1)).map sgnOf ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1) := by
  have h1 : ¬ ABC.C ∉ σ := by
    intro hns
    cases σ with
    | nil => simp at h2
    | cons y t =>
        rw [List.head?_cons, Option.some_inj] at h2
        exact hns (h2 ▸ List.mem_cons_self)
  unfold psi
  rw [if_neg h1, if_neg (not_not_intro h2)]
  subst hi
  subst ha
  rfl

/-! ## Branch equations for `phi` on the three admissible shapes -/

theorem phi_shapeS (n : ℕ) (ε : List Bool) :
    phi n (shapeS n) ε = ABC.A :: ε.map ltr := by
  simp only [phi]
  rw [firstAscent_shapeS, if_pos rfl]

theorem hasGap_shapeI (a : ℕ) (δ : List Bool) : hasGap (shapeI a δ) a = false := by
  unfold hasGap
  rw [drop_a_shapeI,
    List.take_append_of_le_length (by simp : a ≤ (List.replicate a false).length),
    List.take_replicate, Nat.min_self]
  simp

theorem hasGap_shapeII (a i : ℕ) (δ : List Bool) (hia : i < a) :
    hasGap (shapeII a i δ) a = true := by
  unfold hasGap
  rw [drop_a_shapeII, List.take_append, List.take_replicate,
    show a - (List.replicate i false).length = a - i by simp,
    show a - i = (a - i - 1) + 1 by omega, List.take_succ_cons]
  simp

theorem gapIndex_shapeII (a i : ℕ) (δ : List Bool) :
    gapIndex (shapeII a i δ) a = i := by
  unfold gapIndex
  rw [drop_a_shapeII,
    List.takeWhile_append_of_pos (by intro x hx; simp_all [List.mem_replicate]),
    List.takeWhile_cons_of_neg (by simp)]
  simp

theorem phi_shapeI {n a : ℕ} (δ ε : List Bool) (ha : 1 ≤ a) (han : a < n) :
    phi n (shapeI a δ) ε =
      (ε.take a).map ltr ++ ABC.C :: tailLetters n (shapeI a δ) ε a := by
  simp only [phi]
  rw [firstAscent_shapeI ha]
  simp only [hasGap_shapeI, Bool.false_eq_true, if_false]
  rw [if_neg (by omega : ¬ a = n)]

theorem phi_shapeII {n a i : ℕ} (δ ε : List Bool) (hi : 1 ≤ i) (hia : i < a)
    (han : a < n) :
    phi n (shapeII a i δ) ε =
      ABC.C :: ((ε.take (i - 1)).map ltr ++ List.replicate (a - i) ABC.C ++
        [ltr (ε.getD (a - 1) false)] ++ tailLetters n (shapeII a i δ) ε a) := by
  simp only [phi]
  rw [firstAscent_shapeII hi, gapIndex_shapeII]
  simp only [hasGap_shapeII a i δ hia, if_true]
  rw [if_neg (by omega : ¬ a = n)]

/-! ## `tailLetters` in canonical `zipWith` form -/

theorem length_tailLetters (n : ℕ) (s ε : List Bool) (a : ℕ) :
    (tailLetters n s ε a).length = n - (a + 1) := by
  unfold tailLetters
  simp

theorem tailLetters_eq_zipWith {n a : ℕ} {s ε δ : List Bool}
    (hh : ∀ r < δ.length,
      heightAt s (oPos s (a + 1 + r)) = if δ.getD r false then 1 else 0)
    (hlen : n - (a + 1) = δ.length)
    (hε : a + δ.length ≤ ε.length) :
    tailLetters n s ε a =
      List.zipWith (fun d e => if d then ABC.C else ltr e) δ (ε.drop a) := by
  unfold tailLetters
  rw [hlen]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', List.length_zipWith,
      List.length_drop]
    omega
  intro k h1 h2
  have hk : k < δ.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range', List.getElem_zipWith]
  rw [show a + 1 + 1 * k = a + 1 + k by ring]
  rw [hh k hk, List.getD_eq_getElem δ false hk,
    show a + 1 + k - 1 = a + k by omega, List.getElem_drop,
    ← List.getD_eq_getElem ε false (show a + k < ε.length by omega)]
  by_cases hb : δ[k] = true
  · simp [hb]
  · rw [Bool.not_eq_true] at hb
    simp [hb]

theorem tailLetters_shapeI {n a : ℕ} {δ ε : List Bool}
    (hδ : δ.length = n - a - 1) (ha1 : a + 1 ≤ n) (hε : ε.length = n - 1) :
    tailLetters n (shapeI a δ) ε a =
      List.zipWith (fun d e => if d then ABC.C else ltr e) δ (ε.drop a) := by
  apply tailLetters_eq_zipWith
  · intro r hr; exact heightAt_oPos_shapeI hr
  · omega
  · omega

theorem tailLetters_shapeII {n a i : ℕ} {δ ε : List Bool} (hia : i ≤ a)
    (hδ : δ.length = n - a - 1) (ha1 : a + 1 ≤ n) (hε : ε.length = n - 1) :
    tailLetters n (shapeII a i δ) ε a =
      List.zipWith (fun d e => if d then ABC.C else ltr e) δ (ε.drop a) := by
  apply tailLetters_eq_zipWith
  · intro r hr; exact heightAt_oPos_shapeII hia hr
  · omega
  · omega

/-! ## List recomposition helpers -/

theorem take_getD_drop {α : Type*} (l : List α) (d : α) {u : ℕ} (hu : u < l.length) :
    l.take u ++ l.getD u d :: l.drop (u + 1) = l := by
  rw [List.getD_eq_getElem _ _ hu, ← List.drop_eq_getElem_cons hu,
    List.take_append_drop]

theorem take_take_getD_drop {α : Type*} (l : List α) (d : α) {u v : ℕ}
    (huv : u + v < l.length) :
    l.take u ++ ((l.drop u).take v ++ l.getD (u + v) d :: l.drop (u + v + 1)) = l := by
  rw [← List.append_assoc, ← List.take_add, take_getD_drop l d huv]

/-- Reading the case-(II) string at position `i` (the first block `C`).
(`++` is left-associative: the body is `((m1 ++ rep) ++ [x]) ++ TL`.) -/
theorem getD_phiII_at_i {i a : ℕ} {m1 : List ABC} (x : ABC) (TL : List ABC)
    (hm1 : m1.length = i - 1) (hi : 1 ≤ i) (hia : i < a) :
    (ABC.C :: (m1 ++ List.replicate (a - i) ABC.C ++ [x] ++ TL)).getD i ABC.A
      = ABC.C := by
  rw [getD_cons_of_pos _ _ _ hi,
    List.getD_append _ _ _ _ (by
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, hm1]
      omega),
    List.getD_append _ _ _ _ (by
      simp only [List.length_append, List.length_replicate, hm1]
      omega),
    List.getD_append_right _ _ _ _ (le_of_eq hm1), hm1, Nat.sub_self,
    List.getD_replicate _ (by omega)]

/-- Reading the case-(II) string at position `a` (the sign letter after the block). -/
theorem getD_phiII_at_a {i a : ℕ} {m1 : List ABC} (x : ABC) (TL : List ABC)
    (hm1 : m1.length = i - 1) (hi : 1 ≤ i) (hia : i < a) :
    (ABC.C :: (m1 ++ List.replicate (a - i) ABC.C ++ [x] ++ TL)).getD a ABC.A
      = x := by
  have hm1r : (m1 ++ List.replicate (a - i) ABC.C).length = a - 1 := by
    rw [List.length_append, hm1, List.length_replicate]; omega
  rw [getD_cons_of_pos _ _ _ (by omega : 1 ≤ a),
    List.getD_append _ _ _ _ (by
      simp only [List.length_append, List.length_cons, List.length_nil, hm1r]
      omega),
    List.getD_append_right _ _ _ _ (le_of_eq hm1r), hm1r, Nat.sub_self,
    List.getD_cons_zero]

/-! ## The `TailConstraint` bridge between `tailParse` and `ValidSign` -/

/-- On a sign word `ε` whose positions `≥ a` are `tailParse`'s first output (with
`prev = ε.getD (a-1)`), the alternation property of the parse is exactly
`TailConstraint`. -/
theorem tailConstraint_of_tailParse {a : ℕ} {ε δ : List Bool} {L : List ABC}
    {prev : Bool}
    (h1 : (tailParse prev L).1 = ε.drop a)
    (h2 : (tailParse prev L).2 = δ)
    (hδL : δ.length = L.length)
    (hprev : ε.getD (a - 1) false = prev)
    (ha : 1 ≤ a) :
    TailConstraint a δ ε := by
  intro r hr hd
  have halt := tailParse_alternation L prev r (by omega)
    (by rw [h2]; exact hd)
  rw [h1] at halt
  have halt' := halt
  rw [getD_drop'] at halt'
  cases r with
  | zero =>
      rw [List.getD_cons_zero] at halt'
      rw [show a + 0 - 1 = a - 1 from by omega, hprev]
      exact halt'
  | succ r =>
      rw [List.getD_cons_succ, getD_drop'] at halt'
      rw [show a + (r + 1) - 1 = a + r by omega]
      exact halt'

/-! ## Theorem B (sorry package "bijection") -/

/-- Theorem B, step 1: "Φ lands in `W_n`" (and the three cases have disjoint
images — disjointness is implicit in `psi_phi` below).

(Statement note, reported as a definition issue: the hypothesis `1 ≤ n` was added
relative to the original skeleton — at `n = 0` the statement is false, since
`validPairs 0 = {([], [])}` is nonempty while `W 0 = ∅`; every consumer of this
lemma already carries `1 ≤ n`.) -/
theorem phi_mem_W {n : ℕ} {s ε : List Bool} (hn : 1 ≤ n) (h : (s, ε) ∈ validPairs n) :
    phi n s ε ∈ W n := by
  obtain ⟨hs, hε, hv⟩ := mem_validPairs_mk.mp h
  rcases admissible_classification hs ⟨ε, mem_strings.mpr hε, hv⟩ with
    hS | ⟨a, δ, ha, han, hδ, hI⟩ | ⟨a, i, δ, ha, han, hi, hia, hδ, hII⟩
  · -- case (S): the C-free string `A · ℓ(ε)`
    subst hS
    rw [phi_shapeS, mem_W]
    refine ⟨by simp [hε]; omega, fun _ => rfl, fun hc => absurd hc (by simp)⟩
  · -- case (I): `σ₁ ∈ {A, B}` and a C at position `a`
    subst hI
    have hn2 : 2 ≤ n := by omega
    rw [phi_shapeI δ ε ha (by omega), mem_W]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_map,
        List.length_take, length_tailLetters, hε]
      omega
    · intro hc
      exact absurd (List.mem_append_right _ List.mem_cons_self) hc
    · intro hc
      have hne : ε.take a ≠ [] := by
        have : (ε.take a).length = a := by rw [List.length_take]; omega
        intro h0; rw [h0] at this; simp at this; omega
      exact absurd hc (head?_ne_C_of_map_ltr _ hne)
  · -- case (II): leading C, the block C at position i, the sign letter at a
    subst hII
    have hn2 : 2 ≤ n := by omega
    have hialt : i < a := by omega
    rw [phi_shapeII δ ε hi hialt (by omega), mem_W]
    have hεt : (ε.take (i - 1)).length = i - 1 := by rw [List.length_take]; omega
    have hlenσ : (ABC.C :: ((ε.take (i - 1)).map ltr ++ List.replicate (a - i) ABC.C ++
        [ltr (ε.getD (a - 1) false)] ++ tailLetters n (shapeII a i δ) ε a)).length
        = n := by
      simp only [List.length_cons, List.length_append, List.length_map,
        List.length_replicate, List.length_nil, length_tailLetters, hεt]
      omega
    refine ⟨hlenσ, fun hc => absurd List.mem_cons_self hc, fun _ => ?_⟩
    -- the witness pair: position i (a C) and position a (a sign letter)
    have hm1l : ((ε.take (i - 1)).map ltr).length = i - 1 := by
      rw [List.length_map, hεt]
    have hgi := getD_phiII_at_i (ltr (ε.getD (a - 1) false))
      (tailLetters n (shapeII a i δ) ε a) hm1l hi hialt
    have hga := getD_phiII_at_a (ltr (ε.getD (a - 1) false))
      (tailLetters n (shapeII a i δ) ε a) hm1l hi hialt
    refine ⟨⟨i, by rw [hlenσ]; omega⟩, ⟨a, by rw [hlenσ]; omega⟩, by simpa using hi,
      by simpa using hialt, ?_, ?_⟩
    · rw [List.get_eq_getElem, ← List.getD_eq_getElem _ ABC.A]
      exact hgi
    · rw [List.get_eq_getElem, ← List.getD_eq_getElem _ ABC.A, hga]
      exact ltr_ne_C _

/-- Theorem B, step 3: `Ψ ∘ Φ = id` on valid pairs. (Sorry package "bijection".) -/
theorem psi_phi {n : ℕ} {s ε : List Bool} (h : (s, ε) ∈ validPairs n) :
    psi n (phi n s ε) = (s, ε) := by
  obtain ⟨hs, hε, hv⟩ := mem_validPairs_mk.mp h
  rcases admissible_classification hs ⟨ε, mem_strings.mpr hε, hv⟩ with
    hS | ⟨a, δ, ha, han, hδ, hI⟩ | ⟨a, i, δ, ha, han, hi, hia, hδ, hII⟩
  · -- case (S)
    subst hS
    rw [phi_shapeS]
    have hnc : ABC.C ∉ ABC.A :: ε.map ltr := by
      intro hc
      rcases List.mem_cons.mp hc with h' | h'
      · exact ABC.noConfusion h'
      · exact C_not_mem_map_ltr ε h'
    rw [psi_caseS hnc]
    rw [show (ABC.A :: ε.map ltr).drop 1 = ε.map ltr from rfl, map_sgnOf_map_ltr]
  · -- case (I)
    subst hI
    have hn2 : 2 ≤ n := by omega
    have haε : a ≤ ε.length := by omega
    rw [phi_shapeI δ ε ha (by omega)]
    have hm1len : ((ε.take a).map ltr).length = a := by
      rw [List.length_map, List.length_take]; omega
    have hm1ne : ε.take a ≠ [] := by
      intro h0
      rw [List.length_map, h0] at hm1len; simp at hm1len; omega
    -- branch selection
    have hCmem : ABC.C ∈ (ε.take a).map ltr ++ ABC.C :: tailLetters n (shapeI a δ) ε a :=
      List.mem_append_right _ List.mem_cons_self
    have hhead := head?_ne_C_of_map_ltr
      (ABC.C :: tailLetters n (shapeI a δ) ε a) hm1ne
    -- the parse recovers a
    have htw : (((ε.take a).map ltr ++ ABC.C :: tailLetters n (shapeI a δ) ε a).takeWhile
        (· ≠ ABC.C)).length = a := by
      rw [List.takeWhile_append_of_pos (by
          intro x hx
          obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
          simpa using ltr_ne_C b),
        List.takeWhile_cons_of_neg (by simp)]
      simpa using hm1len
    rw [psi_caseI hCmem hhead htw]
    -- components
    have htake : ((ε.take a).map ltr ++ ABC.C :: tailLetters n (shapeI a δ) ε a).take a
        = (ε.take a).map ltr := List.take_left' hm1len
    have hdrop : ((ε.take a).map ltr ++ ABC.C :: tailLetters n (shapeI a δ) ε a).drop
        (a + 1) = tailLetters n (shapeI a δ) ε a := by
      rw [show (ε.take a).map ltr ++ ABC.C :: tailLetters n (shapeI a δ) ε a
          = ((ε.take a).map ltr ++ [ABC.C]) ++ tailLetters n (shapeI a δ) ε a by simp,
        List.drop_left' (by rw [List.length_append, hm1len]; rfl)]
    rw [htake, hdrop, map_sgnOf_map_ltr]
    have hlast : (ε.take a).getLastD false = ε.getD (a - 1) false := by
      rw [getLastD_eq_getD, List.length_take,
        show min a ε.length - 1 = a - 1 by omega, getD_take' _ _ _ _ (by omega)]
    rw [hlast, tailLetters_shapeI hδ (by omega) hε]
    have htc : TailConstraint a δ ε :=
      (validSign_shapeI_iff ha han hδ (by omega) hε).mp hv
    have hparse : tailParse (ε.getD (a - 1) false)
        (List.zipWith (fun d e => if d then ABC.C else ltr e) δ (ε.drop a))
        = (ε.drop a, δ) := by
      apply tailParse_zipWith
      · rw [List.length_drop]; omega
      · intro r hr hd
        have h' := htc r hr hd
        rw [getD_drop']
        cases r with
        | zero =>
            rw [List.getD_cons_zero]
            simpa [show a + 0 - 1 = a - 1 by omega] using h'
        | succ r =>
            rw [List.getD_cons_succ, getD_drop',
              show a + (r + 1) = a + r + 1 by omega]
            simpa [show a + (r + 1) - 1 = a + r by omega] using h'
    rw [hparse, List.take_append_drop]
  · -- case (II)
    subst hII
    have hn2 : 2 ≤ n := by omega
    have hialt : i < a := by omega
    have hi1ε : i - 1 ≤ ε.length := by omega
    rw [phi_shapeII δ ε hi hialt (by omega)]
    set e0 : Bool := ε.getD (a - 1) false with he0
    set TL := tailLetters n (shapeII a i δ) ε a with hTL
    have hm1len : ((ε.take (i - 1)).map ltr).length = i - 1 := by
      rw [List.length_map, List.length_take]; omega
    -- branch: σ₁ = C
    have hhead : (ABC.C :: ((ε.take (i - 1)).map ltr ++ List.replicate (a - i) ABC.C ++
        [ltr e0] ++ TL)).head? = some ABC.C := rfl
    -- `++` is left-associative; reassociate the body once and for all
    have hbodyassoc : (ε.take (i - 1)).map ltr ++ List.replicate (a - i) ABC.C ++
        [ltr e0] ++ TL = (ε.take (i - 1)).map ltr ++
          (List.replicate (a - i) ABC.C ++ ([ltr e0] ++ TL)) := by
      simp [List.append_assoc]
    have hrepcons : List.replicate (a - i) ABC.C
        = ABC.C :: List.replicate (a - i - 1) ABC.C := by
      rw [← List.replicate_succ]
      congr 1
      omega
    -- the parse recovers i
    have hI' : 1 + (((ABC.C :: ((ε.take (i - 1)).map ltr ++
        List.replicate (a - i) ABC.C ++ [ltr e0] ++ TL)).drop 1).takeWhile
          (· ≠ ABC.C)).length = i := by
      rw [List.drop_one, List.tail_cons, hbodyassoc,
        List.takeWhile_append_of_pos (by
          intro x hx
          obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
          simpa using ltr_ne_C b)]
      rw [show (List.replicate (a - i) ABC.C ++ ([ltr e0] ++ TL)).takeWhile
          (· ≠ ABC.C) = [] by
        rw [hrepcons, List.cons_append, List.takeWhile_cons_of_neg (by simp)]]
      rw [List.append_nil, hm1len]
      omega
    -- the parse recovers a
    have hA' : i + (((ABC.C :: ((ε.take (i - 1)).map ltr ++
        List.replicate (a - i) ABC.C ++ [ltr e0] ++ TL)).drop i).takeWhile
          (· = ABC.C)).length = a := by
      rw [drop_cons_of_pos _ _ hi, hbodyassoc, List.drop_left' hm1len,
        List.takeWhile_append_of_pos (by
          intro x hx
          rw [List.eq_of_mem_replicate hx]
          simp),
        List.singleton_append, List.takeWhile_cons_of_neg (by simp [ltr_ne_C e0])]
      simp only [List.append_nil, List.length_append, List.length_replicate]
      omega
    rw [psi_caseII hhead hI' hA']
    -- read off the components
    have hga := getD_phiII_at_a (ltr e0) TL hm1len hi hialt
    have hdrop1take : (((ABC.C :: ((ε.take (i - 1)).map ltr ++
        List.replicate (a - i) ABC.C ++ [ltr e0] ++ TL)).drop 1).take (i - 1)).map
          sgnOf = ε.take (i - 1) := by
      rw [List.drop_one, List.tail_cons, hbodyassoc, List.take_left' hm1len,
        map_sgnOf_map_ltr]
    have hdropA1 : (ABC.C :: ((ε.take (i - 1)).map ltr ++
        List.replicate (a - i) ABC.C ++ [ltr e0] ++ TL)).drop (a + 1) = TL := by
      rw [List.drop_succ_cons,
        List.drop_left' (by
          simp only [List.length_append, List.length_replicate, hm1len,
            List.length_cons, List.length_nil]
          omega)]
    have hTLz : TL = List.zipWith (fun d e => if d then ABC.C else ltr e) δ (ε.drop a) :=
      tailLetters_shapeII (by omega) hδ (by omega) hε
    have hvs := (validSign_shapeII_iff ha han hi hia hδ hε).mp hv
    have hparse : tailParse e0
        (List.zipWith (fun d e => if d then ABC.C else ltr e) δ (ε.drop a))
        = (ε.drop a, δ) := by
      apply tailParse_zipWith
      · rw [List.length_drop]; omega
      · intro r hr hd
        have h' := hvs.2 r hr hd
        rw [getD_drop']
        cases r with
        | zero =>
            rw [List.getD_cons_zero, he0]
            simpa [show a + 0 - 1 = a - 1 by omega] using h'
        | succ r =>
            rw [List.getD_cons_succ, getD_drop',
              show a + (r + 1) = a + r + 1 by omega]
            simpa [show a + (r + 1) - 1 = a + r by omega] using h'
    have hp1 : (tailParse (sgnOf ((ABC.C :: ((ε.take (i - 1)).map ltr ++
        List.replicate (a - i) ABC.C ++ [ltr e0] ++ TL)).getD a ABC.A))
          ((ABC.C :: ((ε.take (i - 1)).map ltr ++ List.replicate (a - i) ABC.C ++
            [ltr e0] ++ TL)).drop (a + 1))).1 = ε.drop a := by
      rw [hga, sgnOf_ltr, hdropA1, hTLz, hparse]
    have hp2 : (tailParse (sgnOf ((ABC.C :: ((ε.take (i - 1)).map ltr ++
        List.replicate (a - i) ABC.C ++ [ltr e0] ++ TL)).getD a ABC.A))
          ((ABC.C :: ((ε.take (i - 1)).map ltr ++ List.replicate (a - i) ABC.C ++
            [ltr e0] ++ TL)).drop (a + 1))).2 = δ := by
      rw [hga, sgnOf_ltr, hdropA1, hTLz, hparse]
    rw [hp1, hp2, hdrop1take, hga, sgnOf_ltr]
    -- the sign word is recovered: blocks from Lemma 6(II), tail from the parse
    have hεeq : ε.take (i - 1) ++ List.replicate (a - i) (! e0) ++ e0 :: ε.drop a
        = ε := by
      have htklen : (ε.take (i - 1)).length = i - 1 := by
        rw [List.length_take]; omega
      have hTRlen : (ε.take (i - 1) ++ List.replicate (a - i) (! e0)).length
          = a - 1 := by
        rw [List.length_append, htklen, List.length_replicate]; omega
      apply ext_getD false
      · simp only [List.length_append, List.length_take, List.length_replicate,
          List.length_cons, List.length_drop]
        omega
      intro k hk
      have hklt : k < n - 1 := by
        simp only [List.length_append, List.length_take, List.length_replicate,
          List.length_cons, List.length_drop] at hk
        omega
      by_cases h2 : k < a - 1
      · rw [List.getD_append _ _ _ _ (by rw [hTRlen]; omega)]
        by_cases h1 : k < i - 1
        · rw [List.getD_append _ _ _ _ (by rw [htklen]; omega),
            getD_take' _ _ _ _ h1]
        · rw [List.getD_append_right _ _ _ _ (by rw [htklen]; omega), htklen,
            List.getD_replicate _ (by omega)]
          have hb := hvs.1 (k - (i - 1)) (by omega)
          rw [show i - 1 + (k - (i - 1)) = k by omega] at hb
          rw [hb, he0]
      · rw [List.getD_append_right _ _ _ _ (by rw [hTRlen]; omega), hTRlen]
        by_cases h3 : k = a - 1
        · subst h3
          rw [Nat.sub_self, List.getD_cons_zero, he0]
        · rw [getD_cons_of_pos _ _ _ (by omega), getD_drop',
            show a + (k - (a - 1) - 1) = k by omega]
    rw [hεeq]

/-! ## Parse data extracted from membership in `W` (Theorem B step 2's analysis) -/

/-- Case-(I) branch data: for a string with a `C` not at the head, the maximal
`C`-free prefix has length `1 ≤ a < n`, position `a` carries a `C`, and the prefix
is `C`-free. -/
theorem parseI_data {n : ℕ} {σ : List ABC} (hlen : σ.length = n)
    (h1 : ABC.C ∈ σ) (h2 : σ.head? ≠ some ABC.C) :
    1 ≤ (σ.takeWhile (· ≠ ABC.C)).length ∧
      (σ.takeWhile (· ≠ ABC.C)).length < n ∧
      σ.getD (σ.takeWhile (· ≠ ABC.C)).length ABC.A = ABC.C ∧
      ∀ x ∈ σ.take (σ.takeWhile (· ≠ ABC.C)).length, x ≠ ABC.C := by
  have hltn : (σ.takeWhile (· ≠ ABC.C)).length < σ.length :=
    length_takeWhile_lt_of_mem h1 (by simp)
  refine ⟨?_, by omega, ?_, ?_⟩
  · cases σ with
    | nil => simp at h1
    | cons y t =>
        rw [List.head?_cons] at h2
        have hy : y ≠ ABC.C := fun hc => h2 (by rw [hc])
        rw [List.takeWhile_cons_of_pos (by simpa using hy)]
        simp
  · have h := getD_length_takeWhile (· ≠ ABC.C) σ ABC.A hltn
    simpa using h
  · intro x hx
    rw [← takeWhile_eq_take] at hx
    simpa using List.mem_takeWhile_imp hx

/-- Case-(II) branch data (the audit-fixed two-case witness argument of
bijection.md §8): with `i - 1` the length of the maximal `{A,B}`-run from position
1 and `a` the end of the maximal `C`-run from position `i`, the second `W`-bullet
forces `1 ≤ i`, `i + 1 ≤ a`, `a + 1 ≤ n`, a non-`C` at position `a`, a `C`-free
run at positions `1..i-1`, and an all-`C` run at positions `i..a-1`. -/
theorem parseII_data {n : ℕ} {σ : List ABC} {i a : ℕ} (hlen : σ.length = n)
    (h2 : σ.head? = some ABC.C)
    (hW : ∃ r t : Fin σ.length, 0 < (r : ℕ) ∧ r < t ∧ σ.get r = ABC.C ∧
      σ.get t ≠ ABC.C)
    (hidef : 1 + ((σ.drop 1).takeWhile (· ≠ ABC.C)).length = i)
    (hadef : i + ((σ.drop i).takeWhile (· = ABC.C)).length = a) :
    1 ≤ i ∧ i + 1 ≤ a ∧ a + 1 ≤ n ∧
      σ.getD a ABC.A ≠ ABC.C ∧
      (∀ x ∈ (σ.drop 1).take (i - 1), x ≠ ABC.C) ∧
      (σ.drop i).take (a - i) = List.replicate (a - i) ABC.C := by
  obtain ⟨r, t, hr0, hrt, hrC, htC⟩ := hW
  have hrn : (r : ℕ) < n := by rw [← hlen]; exact r.isLt
  have htn : (t : ℕ) < n := by rw [← hlen]; exact t.isLt
  have hrC' : σ.getD (r : ℕ) ABC.A = ABC.C := by
    rw [List.getD_eq_getElem _ _ r.isLt, ← List.get_eq_getElem]; exact hrC
  have htC' : σ.getD (t : ℕ) ABC.A ≠ ABC.C := by
    rw [List.getD_eq_getElem _ _ t.isLt, ← List.get_eq_getElem]; exact htC
  -- the C at position r lives in `σ.drop 1`
  have hCdrop : ABC.C ∈ σ.drop 1 := by
    have hk : (r : ℕ) - 1 < (σ.drop 1).length := by rw [List.length_drop]; omega
    have hg : (σ.drop 1).getD ((r : ℕ) - 1) ABC.A = ABC.C := by
      rw [getD_drop', show 1 + ((r : ℕ) - 1) = (r : ℕ) by omega]
      exact hrC'
    rw [List.getD_eq_getElem _ _ hk] at hg
    exact hg ▸ List.getElem_mem hk
  have hm : ((σ.drop 1).takeWhile (· ≠ ABC.C)).length < (σ.drop 1).length :=
    length_takeWhile_lt_of_mem hCdrop (by simp)
  have hdlen : (σ.drop 1).length = n - 1 := by rw [List.length_drop, hlen]
  have h1i : 1 ≤ i := by omega
  have hin : i ≤ n - 1 := by omega
  -- position i carries a C (boundary of the {A,B}-run)
  have hgi : σ.getD i ABC.A = ABC.C := by
    have h := getD_length_takeWhile (· ≠ ABC.C) (σ.drop 1) ABC.A hm
    rw [getD_drop', hidef] at h
    simpa using h
  -- the {A,B}-run is C-free
  have hABrun : ∀ x ∈ (σ.drop 1).take (i - 1), x ≠ ABC.C := by
    intro x hx
    rw [show i - 1 = ((σ.drop 1).takeWhile (· ≠ ABC.C)).length by omega,
      ← takeWhile_eq_take] at hx
    simpa using List.mem_takeWhile_imp hx
  -- the C-run is nonempty
  have hdropi : σ.drop i = ABC.C :: σ.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (show i < σ.length by omega)]
    rw [← List.getD_eq_getElem _ ABC.A, hgi]
  have hc1 : 1 ≤ ((σ.drop i).takeWhile (· = ABC.C)).length := by
    rw [hdropi, List.takeWhile_cons_of_pos (by simp)]
    simp
  have hia1 : i + 1 ≤ a := by omega
  -- the C-run is all-C
  have hrunrep : (σ.drop i).takeWhile (· = ABC.C) =
      List.replicate ((σ.drop i).takeWhile (· = ABC.C)).length ABC.C := by
    apply List.eq_replicate_of_mem
    intro b hb
    simpa using List.mem_takeWhile_imp hb
  have hrun : (σ.drop i).take (a - i) = List.replicate (a - i) ABC.C := by
    rw [show a - i = ((σ.drop i).takeWhile (· = ABC.C)).length by omega,
      ← takeWhile_eq_take]
    exact hrunrep
  have hCk : ∀ k < a - i, σ.getD (i + k) ABC.A = ABC.C := by
    intro k hk
    have hg := getD_take' (σ.drop i) ABC.A (a - i) k hk
    rw [hrun, List.getD_replicate _ hk, getD_drop'] at hg
    exact hg.symm
  -- the witness forces the C-run to end before position n
  have hri : i ≤ (r : ℕ) := by
    by_contra hlt
    rw [not_le] at hlt
    have hk : (r : ℕ) - 1 < i - 1 := by omega
    have hmem : (σ.drop 1).getD ((r : ℕ) - 1) ABC.A ∈ (σ.drop 1).take (i - 1) := by
      have hk' : (r : ℕ) - 1 < ((σ.drop 1).take (i - 1)).length := by
        rw [List.length_take]; omega
      rw [← getD_take' (σ.drop 1) ABC.A (i - 1) _ hk,
        List.getD_eq_getElem _ _ hk']
      exact List.getElem_mem hk'
    have := hABrun _ hmem
    rw [getD_drop', show 1 + ((r : ℕ) - 1) = (r : ℕ) by omega] at this
    exact this hrC'
  have han1 : a + 1 ≤ n := by
    rcases Nat.lt_or_ge (r : ℕ) a with hra | hra
    · -- r inside the run: the non-C witness t must be at position ≥ a
      by_contra hlt
      rw [not_le] at hlt
      have hta : (t : ℕ) < a := by omega
      have := hCk ((t : ℕ) - i) (by omega)
      rw [show i + ((t : ℕ) - i) = (t : ℕ) by omega] at this
      exact htC' this
    · omega
  -- position a is not a C (boundary of the C-run)
  have hclen : ((σ.drop i).takeWhile (· = ABC.C)).length < (σ.drop i).length := by
    rw [List.length_drop]; omega
  have hga : σ.getD a ABC.A ≠ ABC.C := by
    have h := getD_length_takeWhile (· = ABC.C) (σ.drop i) ABC.A hclen
    rw [getD_drop', hadef] at h
    simpa using h
  exact ⟨h1i, hia1, han1, hga, hABrun, hrun⟩

/-- Theorem B, step 2: "the parse Ψ is total on `W_n`" — its output is a valid pair
(`Lemma 5` gives admissibility of the rebuilt shape, `Lemma 6` validity of the
rebuilt sign word). (Sorry package "bijection".) -/
theorem psi_mem_validPairs {n : ℕ} {σ : List ABC} (hσ : σ ∈ W n) (hn : 1 ≤ n) :
    psi n σ ∈ validPairs n := by
  obtain ⟨hlen, hInW⟩ := mem_W.mp hσ
  by_cases hC : ABC.C ∈ σ
  · by_cases hhead : σ.head? = some ABC.C
    · -- case (II)
      obtain ⟨h1i, hia1, han1, hbnd, helems, hrun⟩ :=
        parseII_data hlen hhead (hInW.2 hhead) rfl rfl
      rw [psi_caseII hhead rfl rfl, mem_validPairs_mk]
      set i := 1 + ((σ.drop 1).takeWhile (· ≠ ABC.C)).length with hidef
      set a := i + ((σ.drop i).takeWhile (· = ABC.C)).length with hadef
      have ht2len : (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).2.length
          = n - a - 1 := by
        rw [(tailParse_length _ _).2, List.length_drop, hlen]; omega
      have ht1len : (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1.length
          = n - a - 1 := by
        rw [(tailParse_length _ _).1, List.length_drop, hlen]; omega
      have hεablen : (((σ.drop 1).take (i - 1)).map sgnOf).length = i - 1 := by
        rw [List.length_map, List.length_take, List.length_drop, hlen]; omega
      have hε'len : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).length
          = n - 1 := by
        simp only [List.length_append, List.length_replicate, List.length_cons,
          hεablen, ht1len]
        omega
      have hTRlen : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A))).length = a - 1 := by
        rw [List.length_append, hεablen, List.length_replicate]; omega
      -- the two getD computations on the rebuilt sign word
      have hgblock : ∀ k < a - i, ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).getD
          (i - 1 + k) false = ! sgnOf (σ.getD a ABC.A) := by
        intro k hk
        rw [List.getD_append _ _ _ _ (by rw [hTRlen]; omega),
          List.getD_append_right _ _ _ _ (by rw [hεablen]; omega), hεablen,
          show i - 1 + k - (i - 1) = k by omega, List.getD_replicate _ hk]
      have hga1 : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).getD
          (a - 1) false = sgnOf (σ.getD a ABC.A) := by
        rw [List.getD_append_right _ _ _ _ (le_of_eq hTRlen), hTRlen,
          Nat.sub_self, List.getD_cons_zero]
      have hdropa : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).drop a
          = (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1 := by
        rw [show (((σ.drop 1).take (i - 1)).map sgnOf) ++
            List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
            sgnOf (σ.getD a ABC.A) ::
              (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1
            = ((((σ.drop 1).take (i - 1)).map sgnOf ++
              List.replicate (a - i) (! sgnOf (σ.getD a ABC.A))) ++
              [sgnOf (σ.getD a ABC.A)]) ++
              (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1 by
            simp [List.append_assoc],
          List.drop_left' (by
            simp only [List.length_append, List.length_replicate,
              List.length_cons, List.length_nil, hεablen]
            omega)]
      refine ⟨?_, ?_, ?_⟩
      · exact isDyck_shapeII (by omega) (by omega) h1i (by omega) ht2len
      · exact hε'len
      · rw [validSign_shapeII_iff (by omega) (by omega) h1i (by omega) ht2len hε'len]
        constructor
        · intro k hk
          rw [hgblock k hk, hga1]
        · exact tailConstraint_of_tailParse hdropa.symm rfl
            (by rw [ht2len, List.length_drop, hlen]; omega) hga1 (by omega)
    · -- case (I)
      obtain ⟨ha1, haltn, hbnd, helems⟩ := parseI_data hlen hC hhead
      rw [psi_caseI hC hhead rfl, mem_validPairs_mk]
      set a := (σ.takeWhile (· ≠ ABC.C)).length with hadef
      have ht2len : (tailParse (((σ.take a).map sgnOf).getLastD false)
          (σ.drop (a + 1))).2.length = n - a - 1 := by
        rw [(tailParse_length _ _).2, List.length_drop, hlen]; omega
      have ht1len : (tailParse (((σ.take a).map sgnOf).getLastD false)
          (σ.drop (a + 1))).1.length = n - a - 1 := by
        rw [(tailParse_length _ _).1, List.length_drop, hlen]; omega
      have hheadlen : ((σ.take a).map sgnOf).length = a := by
        rw [List.length_map, List.length_take]; omega
      have hε'len : ((σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1).length = n - 1 := by
        rw [List.length_append, hheadlen, ht1len]; omega
      have hprev : ((σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1).getD (a - 1) false
          = ((σ.take a).map sgnOf).getLastD false := by
        rw [List.getD_append _ _ _ _ (by rw [hheadlen]; omega),
          getLastD_eq_getD, hheadlen]
      have hdropa : ((σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1).drop a
          = (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1 := List.drop_left' hheadlen
      refine ⟨?_, ?_, ?_⟩
      · exact isDyck_shapeI ha1 (by omega) ht2len hn
      · exact hε'len
      · rw [validSign_shapeI_iff ha1 (by omega) ht2len hn hε'len]
        exact tailConstraint_of_tailParse hdropa.symm rfl
          (by rw [ht2len, List.length_drop, hlen]; omega) hprev ha1
  · -- case (S)
    rw [psi_caseS hC, mem_validPairs_mk]
    refine ⟨isDyck_shapeS n, ?_, validSign_shapeS n _⟩
    rw [List.length_map, List.length_drop, hlen]

/-- Theorem B, step 4: `Φ ∘ Ψ = id` on `W_n` ("in each branch, Φ applied to Ψ's
output writes back exactly the letters read" — using Lemma 5's converse
(`firstAscent_shapeI` / `firstAscent_shapeII` / the `hasGap`/`gapIndex`
computations) to see the rebuilt shape classifies into the same case). -/
theorem phi_psi {n : ℕ} {σ : List ABC} (hσ : σ ∈ W n) (hn : 1 ≤ n) :
    phi n (psi n σ).1 (psi n σ).2 = σ := by
  obtain ⟨hlen, hInW⟩ := mem_W.mp hσ
  by_cases hC : ABC.C ∈ σ
  · by_cases hhead : σ.head? = some ABC.C
    · -- case (II)
      obtain ⟨h1i, hia1, han1, hbnd, helems, hrun⟩ :=
        parseII_data hlen hhead (hInW.2 hhead) rfl rfl
      set i := 1 + ((σ.drop 1).takeWhile (· ≠ ABC.C)).length with hidef
      set a := i + ((σ.drop i).takeWhile (· = ABC.C)).length with hadef
      have hpsi := psi_caseII (n := n) hhead hidef.symm hadef.symm
      rw [show (psi n σ).1 = shapeII a i
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).2 from by rw [hpsi],
        show (psi n σ).2 = ((σ.drop 1).take (i - 1)).map sgnOf ++
            List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
            sgnOf (σ.getD a ABC.A) ::
              (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1 from by
          rw [hpsi]]
      rw [phi_shapeII _ _ h1i (by omega) (by omega)]
      have hεablen : (((σ.drop 1).take (i - 1)).map sgnOf).length = i - 1 := by
        rw [List.length_map, List.length_take, List.length_drop, hlen]; omega
      have ht1len : (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1.length
          = n - a - 1 := by
        rw [(tailParse_length _ _).1, List.length_drop, hlen]; omega
      have ht2len : (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).2.length
          = n - a - 1 := by
        rw [(tailParse_length _ _).2, List.length_drop, hlen]; omega
      have hTRlen : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A))).length = a - 1 := by
        rw [List.length_append, hεablen, List.length_replicate]; omega
      have hε'len : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).length
          = n - 1 := by
        simp only [List.length_append, List.length_replicate, List.length_cons,
          hεablen, ht1len]
        omega
      -- piece 1: the {A,B}-run
      have htakei : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).take (i - 1)
          = ((σ.drop 1).take (i - 1)).map sgnOf := by
        rw [List.take_append_of_le_length (by rw [hTRlen]; omega),
          List.take_append_of_le_length (le_of_eq hεablen.symm),
          List.take_of_length_le (le_of_eq hεablen)]
      -- piece 2: the sign letter at a - 1
      have hga1 : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).getD
          (a - 1) false = sgnOf (σ.getD a ABC.A) := by
        rw [List.getD_append_right _ _ _ _ (le_of_eq hTRlen), hTRlen,
          Nat.sub_self, List.getD_cons_zero]
      -- piece 3: the tail
      have hdropa : ((((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1).drop a
          = (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1 := by
        rw [show (((σ.drop 1).take (i - 1)).map sgnOf) ++
            List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
            sgnOf (σ.getD a ABC.A) ::
              (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1
            = ((((σ.drop 1).take (i - 1)).map sgnOf ++
              List.replicate (a - i) (! sgnOf (σ.getD a ABC.A))) ++
              [sgnOf (σ.getD a ABC.A)]) ++
              (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1 by
            simp [List.append_assoc],
          List.drop_left' (by
            simp only [List.length_append, List.length_replicate,
              List.length_cons, List.length_nil, hεablen]
            omega)]
      have hTLz := tailLetters_shapeII (n := n)
        (i := i) (δ := (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).2)
        (ε := (((σ.drop 1).take (i - 1)).map sgnOf) ++
          List.replicate (a - i) (! sgnOf (σ.getD a ABC.A)) ++
          sgnOf (σ.getD a ABC.A) ::
            (tailParse (sgnOf (σ.getD a ABC.A)) (σ.drop (a + 1))).1)
        (by omega) ht2len (by omega) hε'len
      rw [htakei, map_ltr_map_sgnOf helems, hga1, ltr_sgnOf hbnd, hTLz, hdropa,
        zipWith_tailParse]
      -- reassemble σ
      have hσcons : σ = ABC.C :: σ.drop 1 := by
        cases σ with
        | nil => simp at hhead
        | cons y ρ =>
            rw [List.head?_cons, Option.some_inj] at hhead
            rw [hhead]
            rfl
      have hassemble := take_take_getD_drop (σ.drop 1) ABC.A
        (u := i - 1) (v := a - i) (by rw [List.length_drop]; omega)
      rw [show i - 1 + (a - i) = a - 1 by omega] at hassemble
      rw [show a - 1 + 1 = a by omega] at hassemble
      rw [show (σ.drop 1).drop (i - 1) = σ.drop i from by
          rw [List.drop_drop]; congr 1; omega] at hassemble
      rw [show (σ.drop 1).drop a = σ.drop (a + 1) from by
          rw [List.drop_drop]; congr 1; omega] at hassemble
      rw [getD_drop', show 1 + (a - 1) = a by omega, hrun] at hassemble
      conv_rhs => rw [hσcons]
      congr 1
      rw [List.append_assoc, List.append_assoc, List.singleton_append]
      exact hassemble
    · -- case (I)
      obtain ⟨ha1, haltn, hbnd, helems⟩ := parseI_data hlen hC hhead
      set a := (σ.takeWhile (· ≠ ABC.C)).length with hadef
      have hpsi := psi_caseI (n := n) hC hhead hadef.symm
      rw [show (psi n σ).1 = shapeI a
            (tailParse (((σ.take a).map sgnOf).getLastD false)
              (σ.drop (a + 1))).2 from by rw [hpsi],
        show (psi n σ).2 = (σ.take a).map sgnOf ++
            (tailParse (((σ.take a).map sgnOf).getLastD false)
              (σ.drop (a + 1))).1 from by rw [hpsi]]
      rw [phi_shapeI _ _ ha1 (by omega)]
      have hheadlen : ((σ.take a).map sgnOf).length = a := by
        rw [List.length_map, List.length_take]; omega
      have ht2len : (tailParse (((σ.take a).map sgnOf).getLastD false)
          (σ.drop (a + 1))).2.length = n - a - 1 := by
        rw [(tailParse_length _ _).2, List.length_drop, hlen]; omega
      have hε'len : ((σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1).length = n - 1 := by
        rw [List.length_append, hheadlen, (tailParse_length _ _).1,
          List.length_drop, hlen]
        omega
      have htake : ((σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1).take a = (σ.take a).map sgnOf :=
        List.take_left' hheadlen
      have hdropa : ((σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1).drop a
          = (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1 := List.drop_left' hheadlen
      have hTLz := tailLetters_shapeI (n := n)
        (δ := (tailParse (((σ.take a).map sgnOf).getLastD false)
          (σ.drop (a + 1))).2)
        (ε := (σ.take a).map sgnOf ++
          (tailParse (((σ.take a).map sgnOf).getLastD false)
            (σ.drop (a + 1))).1)
        ht2len (by omega) hε'len
      rw [htake, map_ltr_map_sgnOf helems, hTLz, hdropa, zipWith_tailParse]
      -- reassemble σ
      have hassemble := take_getD_drop σ ABC.A (show a < σ.length by omega)
      rw [hbnd] at hassemble
      exact hassemble
  · -- case (S)
    rw [psi_caseS hC, phi_shapeS]
    have hmap : ((σ.drop 1).map sgnOf).map ltr = σ.drop 1 :=
      map_ltr_map_sgnOf fun x hx hxC =>
        hC (hxC ▸ List.mem_of_mem_drop hx)
    rw [hmap]
    have hheadA := hInW.1 hC
    cases σ with
    | nil => simp at hlen; omega
    | cons y ρ =>
        rw [List.head?_cons, Option.some_inj] at hheadA
        rw [hheadA]
        rfl

/-- **Chain step 2** (Theorem B): `|validPairs n| = |W n|` for `n ≥ 1`.
(Sorry package "bijection" — headline; expected proof: `Finset.card_bij` with
`phi`/`psi` and the four steps above.) -/
theorem card_validPairs_eq_card_W (n : ℕ) (hn : 1 ≤ n) :
    (validPairs n).card = (W n).card := by
  apply Finset.card_bij (fun q _ => phi n q.1 q.2)
  · intro q hq
    exact phi_mem_W hn (show (q.1, q.2) ∈ validPairs n from by rwa [Prod.mk.eta])
  · intro q1 hq1 q2 hq2 heq
    have h1 := psi_phi (show (q1.1, q1.2) ∈ validPairs n from by rwa [Prod.mk.eta])
    have h2 := psi_phi (show (q2.1, q2.2) ∈ validPairs n from by rwa [Prod.mk.eta])
    calc q1 = (q1.1, q1.2) := by rw [Prod.mk.eta]
      _ = psi n (phi n q1.1 q1.2) := h1.symm
      _ = psi n (phi n q2.1 q2.2) := by rw [heq]
      _ = (q2.1, q2.2) := h2
      _ = q2 := by rw [Prod.mk.eta]
  · intro σ hσ
    exact ⟨psi n σ, psi_mem_validPairs hσ hn, phi_psi hσ hn⟩

end ElizaldeLuo
