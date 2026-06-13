/-
# Helper lemmas for the bijection package (`Bijection.lean`)

Generic list utilities (`getD`/`takeWhile`/append arithmetic), `openerPositions`
computations, `tailWord` structure, the start-height computation
`heightAt_oPos_tailWord` that powers the `tailLetters` description of Φ on the
admissible shapes (I) and (II), and membership unfoldings for `dycks`,
`validPairs`, `W`. Sorry-free.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo
import ElizaldeLuo.TheoremA
import ElizaldeLuo.Shapes
import ElizaldeLuo.WLang

namespace ElizaldeLuo

/-! ## Generic list utilities -/

theorem ext_getD {α : Type*} {l₁ l₂ : List α} (d : α) (hlen : l₁.length = l₂.length)
    (h : ∀ k < l₁.length, l₁.getD k d = l₂.getD k d) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro k h₁ h₂
  have hk := h k h₁
  rwa [List.getD_eq_getElem _ _ h₁, List.getD_eq_getElem _ _ h₂] at hk

theorem getD_drop' {α : Type*} (l : List α) (d : α) (m k : ℕ) :
    (l.drop m).getD k d = l.getD (m + k) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_take' {α : Type*} (l : List α) (d : α) (m k : ℕ) (h : k < m) :
    (l.take m).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem getD_append_length {α : Type*} (l₁ l₂ : List α) (d : α) :
    (l₁ ++ l₂).getD l₁.length d = l₂.getD 0 d := by
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]

theorem getD_cons_of_pos {α : Type*} (x : α) (l : List α) (d : α) {k : ℕ}
    (hk : 1 ≤ k) : (x :: l).getD k d = l.getD (k - 1) d := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp [List.getD_cons_succ]

theorem drop_cons_of_pos {α : Type*} (x : α) (l : List α) {k : ℕ} (hk : 1 ≤ k) :
    (x :: l).drop k = l.drop (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp [List.drop_succ_cons]

theorem getLastD_eq_getD {α : Type*} (l : List α) (d : α) :
    l.getLastD d = l.getD (l.length - 1) d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- The element just past `takeWhile p` (when it exists) fails `p`. -/
theorem getD_length_takeWhile {α : Type*} (p : α → Bool) (l : List α) (d : α)
    (h : (l.takeWhile p).length < l.length) :
    p (l.getD (l.takeWhile p).length d) = false := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
      by_cases hx : p x
      · rw [List.takeWhile_cons_of_pos hx] at h ⊢
        simpa [List.getD_cons_succ] using ih (by simpa using h)
      · rw [List.takeWhile_cons_of_neg hx]
        simpa [List.getD_cons_zero] using hx

theorem takeWhile_eq_take {α : Type*} (p : α → Bool) (l : List α) :
    l.takeWhile p = l.take (l.takeWhile p).length :=
  List.prefix_iff_eq_take.mp (List.takeWhile_prefix p)

theorem length_takeWhile_lt_of_mem {α : Type*} {p : α → Bool} {l : List α} {x : α}
    (hx : x ∈ l) (hpx : p x = false) :
    (l.takeWhile p).length < l.length := by
  rcases Nat.lt_or_ge (l.takeWhile p).length l.length with h | h
  · exact h
  · exfalso
    have heq : l.takeWhile p = l :=
      (List.takeWhile_prefix p).sublist.eq_of_length_le h
    have := List.mem_takeWhile_imp (x := x) (p := p) (by rw [heq]; exact hx)
    rw [hpx] at this
    exact Bool.false_ne_true this

/-! ## `openerPositions` -/

theorem openerPositions_cons (x : Bool) (l : List Bool) :
    openerPositions (x :: l) =
      (if x then [0] else []) ++ (openerPositions l).map (· + 1) := by
  unfold openerPositions
  rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
  cases x <;>
    simp [Function.comp_def, Nat.succ_eq_add_one, List.getD_cons_zero, List.getD_cons_succ]

theorem openerPositions_append (l₁ l₂ : List Bool) :
    openerPositions (l₁ ++ l₂) =
      openerPositions l₁ ++ (openerPositions l₂).map (· + l₁.length) := by
  induction l₁ with
  | nil => simp [openerPositions]
  | cons x t ih =>
      cases x <;>
        simp [openerPositions_cons, ih, List.map_map, Function.comp_def,
          Nat.add_assoc, List.append_assoc]

theorem length_openerPositions (l : List Bool) :
    (openerPositions l).length = l.count true := by
  induction l with
  | nil => simp [openerPositions]
  | cons x t ih =>
      rw [openerPositions_cons]
      cases x <;> simp [ih, List.count_cons]

theorem openerPositions_replicate_false (k : ℕ) :
    openerPositions (List.replicate k false) = [] := by
  have h := length_openerPositions (List.replicate k false)
  rw [List.count_replicate] at h
  simp only [show (false == true) = false from rfl, if_false] at h
  exact List.length_eq_zero_iff.mp h

/-! ## `tailWord` structure -/

theorem tailWord_cons (h : ℕ) (d : Bool) (ds : List Bool) :
    tailWord h (d :: ds) =
      List.replicate (h - (if d then 1 else 0)) false ++
        true :: tailWord ((if d then 1 else 0) + 1) ds := rfl

theorem count_true_tailWord (h : ℕ) (ds : List Bool) :
    (tailWord h ds).count true = ds.length := by
  induction ds generalizing h with
  | nil => simp [tailWord, List.count_replicate]
  | cons d ds ih => simp [tailWord_cons, List.count_replicate, List.count_cons, ih]

theorem count_false_tailWord (h : ℕ) (ds : List Bool) (hh : 1 ≤ h) :
    (tailWord h ds).count false = h + ds.length := by
  induction ds generalizing h with
  | nil => simp [tailWord, List.count_replicate]
  | cons d ds ih =>
      rw [tailWord_cons]
      simp only [List.count_append, List.count_replicate, List.count_cons]
      rw [ih _ (by cases d <;> simp)]
      cases d <;> simp <;> omega

/-! ## The start-height computation for tail arcs

For a word `u ++ tailWord h ds` whose prefix `u` has `c + h` openers and `c`
closers (so the path height after `u` is `h ≥ 1`), the arcs `u.count true + r`
(`r < ds.length`) are exactly the arcs opened inside the tail, and the height
of the path just before the opener of arc `u.count true + r` is the bit
`ds.getD r false` — the `δ_j` of bijection.md Lemma 5. -/

theorem heightAt_oPos_tailWord :
    ∀ (ds u : List Bool) (h : ℕ), 1 ≤ h → u.count true = u.count false + h →
      ∀ r < ds.length,
        heightAt (u ++ tailWord h ds) (oPos (u ++ tailWord h ds) (u.count true + r)) =
          (if ds.getD r false then 1 else 0) := by
  intro ds
  induction ds with
  | nil => intro u h _ _ r hr; simp at hr
  | cons d ds ih =>
      intro u h hh hcount r hr
      obtain ⟨bd, hbd, hbd1⟩ : ∃ bd : ℕ, (if d then 1 else 0) = bd ∧ bd ≤ 1 :=
        ⟨if d then 1 else 0, rfl, by cases d <;> simp⟩
      have htw : tailWord h (d :: ds) =
          List.replicate (h - bd) false ++ true :: tailWord (bd + 1) ds := by
        rw [tailWord_cons, hbd]
      cases r with
      | zero =>
          have hoPos : oPos (u ++ tailWord h (d :: ds)) (u.count true + 0) =
              u.length + (h - bd) := by
            unfold oPos
            rw [openerPositions_append,
              List.getD_append_right _ _ _ _ (by rw [length_openerPositions]; omega),
              length_openerPositions, htw, openerPositions_append,
              openerPositions_replicate_false, openerPositions_cons]
            simp
            omega
          rw [hoPos]
          unfold heightAt
          rw [List.take_append,
            List.take_of_length_le (show u.length ≤ u.length + (h - bd) by omega),
            show u.length + (h - bd) - u.length = h - bd by omega,
            htw,
            List.take_append_of_le_length
              (show h - bd ≤ (List.replicate (h - bd) false).length by simp),
            List.take_replicate, Nat.min_self]
          have hc1 : (u ++ List.replicate (h - bd) false).count true = u.count true := by
            simp [List.count_append, List.count_replicate]
          have hc2 : (u ++ List.replicate (h - bd) false).count false
              = u.count false + (h - bd) := by
            simp [List.count_append, List.count_replicate]
          rw [hc1, hc2, List.getD_cons_zero, hbd]
          omega
      | succ r =>
          have hdecomp : u ++ tailWord h (d :: ds) =
              (u ++ List.replicate (h - bd) false ++ [true]) ++ tailWord (bd + 1) ds := by
            rw [htw]; simp [List.append_assoc]
          rw [hdecomp, List.getD_cons_succ]
          have hct : (u ++ List.replicate (h - bd) false ++ [true]).count true
              = u.count true + 1 := by
            simp [List.count_append, List.count_replicate]
          have hcf : (u ++ List.replicate (h - bd) false ++ [true]).count false
              = u.count false + (h - bd) := by
            simp [List.count_append, List.count_replicate]
          rw [show u.count true + (r + 1)
              = (u ++ List.replicate (h - bd) false ++ [true]).count true + r by
            rw [hct]; omega]
          exact ih _ (bd + 1) (by omega) (by rw [hct, hcf]; omega) r (by simpa using hr)

/-! ## Decompositions and computations on the admissible shapes -/

/-- Case (I) as a prefix plus `tailWord 1 δ` (the leading `δ_{a+1} = 0` bit of the
definition is the `true` swallowed into the prefix). -/
theorem shapeI_decomp (a : ℕ) (δ : List Bool) :
    shapeI a δ =
      (List.replicate a true ++ List.replicate a false ++ [true]) ++ tailWord 1 δ := by
  unfold shapeI
  rw [tailWord_cons]
  simp [List.append_assoc]

/-- Case (II) as a prefix plus `tailWord 1 δ`. -/
theorem shapeII_decomp (a i : ℕ) (δ : List Bool) :
    shapeII a i δ =
      (List.replicate a true ++ List.replicate i false ++ true ::
        List.replicate (a - i) false) ++ tailWord 1 δ := by
  unfold shapeII
  simp [List.append_assoc]

theorem heightAt_oPos_shapeI {a : ℕ} {δ : List Bool} {r : ℕ} (hr : r < δ.length) :
    heightAt (shapeI a δ) (oPos (shapeI a δ) (a + 1 + r)) =
      (if δ.getD r false then 1 else 0) := by
  have hct : (List.replicate a true ++ List.replicate a false ++ [true]).count true
      = a + 1 := by simp [List.count_append, List.count_replicate]
  have hcf : (List.replicate a true ++ List.replicate a false ++ [true]).count false
      = a := by simp [List.count_append, List.count_replicate]
  have h := heightAt_oPos_tailWord δ
    (List.replicate a true ++ List.replicate a false ++ [true]) 1 le_rfl
    (by rw [hct, hcf]) r hr
  rw [hct, ← shapeI_decomp] at h
  exact h

theorem heightAt_oPos_shapeII {a i : ℕ} {δ : List Bool} (hia : i ≤ a) {r : ℕ}
    (hr : r < δ.length) :
    heightAt (shapeII a i δ) (oPos (shapeII a i δ) (a + 1 + r)) =
      (if δ.getD r false then 1 else 0) := by
  have hct : (List.replicate a true ++ List.replicate i false ++ true ::
      List.replicate (a - i) false).count true = a + 1 := by
    simp [List.count_append, List.count_replicate, List.count_cons]
  have hcf : (List.replicate a true ++ List.replicate i false ++ true ::
      List.replicate (a - i) false).count false = a := by
    simp [List.count_append, List.count_replicate, List.count_cons]
    omega
  have h := heightAt_oPos_tailWord δ
    (List.replicate a true ++ List.replicate i false ++ true ::
      List.replicate (a - i) false) 1 le_rfl (by rw [hct, hcf]) r hr
  rw [hct, ← shapeII_decomp] at h
  exact h

/-- `a(shapeS n) = n` (the `shapeS` case of Lemma 5's first-ascent computation;
"definitional" per Shapes.lean). -/
theorem firstAscent_shapeS (n : ℕ) : firstAscent (shapeS n) = n := by
  unfold firstAscent shapeS
  rw [List.takeWhile_append_of_pos (by intro x hx; simp_all [List.mem_replicate]),
    List.takeWhile_replicate]
  simp

theorem drop_a_shapeI (a : ℕ) (δ : List Bool) :
    (shapeI a δ).drop a = List.replicate a false ++ true :: tailWord 1 δ := by
  unfold shapeI
  rw [List.drop_append_of_le_length (by simp), tailWord_cons]
  simp

theorem drop_a_shapeII (a i : ℕ) (δ : List Bool) :
    (shapeII a i δ).drop a =
      List.replicate i false ++ true :: (List.replicate (a - i) false ++ tailWord 1 δ) := by
  unfold shapeII
  rw [List.drop_append_of_le_length (by simp)]
  simp

/-! ## Membership unfoldings -/

theorem mem_dycks {n : ℕ} {s : List Bool} : s ∈ dycks n ↔ IsDyck n s := by
  unfold dycks
  rw [Finset.mem_filter, mem_strings]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem mem_validPairs {n : ℕ} {q : List Bool × List Bool} :
    q ∈ validPairs n ↔ IsDyck n q.1 ∧ q.2.length = n - 1 ∧ ValidSign n q.1 q.2 := by
  unfold validPairs
  rw [Finset.mem_filter, Finset.mem_product, mem_dycks, mem_strings]
  tauto

theorem mem_validPairs_mk {n : ℕ} {s ε : List Bool} :
    (s, ε) ∈ validPairs n ↔ IsDyck n s ∧ ε.length = n - 1 ∧ ValidSign n s ε :=
  mem_validPairs

theorem mem_W {n : ℕ} {σ : List ABC} : σ ∈ W n ↔ σ.length = n ∧ InW σ := by
  unfold W
  rw [Finset.mem_filter, mem_strings]

end ElizaldeLuo
