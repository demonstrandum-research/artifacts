/-
# Helpers for the "signword" sorry package (SignWord.lean)

Auxiliary lemmas that depend only on `Defs`/`Fifo`: generic list facts
(`take`/`getD`/`foldl max`/`countP` over ranges), counting in `baseWord`,
first/second-occurrence machinery (`idxOf`/`sndIdx`), quadruple-to-`Contains`
constructors for the four patterns 1132/3312/1221/2112, and the
first-occurrence-order invariant of `openerLabels`.

Everything lives in the namespace `ElizaldeLuo.SW` to avoid clashes with other
packages' helper files. This file is sorry-free.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo

namespace ElizaldeLuo
namespace SW

/-! ## Generic list facts -/

theorem getD_mem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem getD_mem_take {l : List ℕ} {m j : ℕ} (hmj : m < j) (hml : m < l.length) :
    l.getD m 0 ∈ l.take j := by
  have h2 : m < (l.take j).length := by simp [List.length_take]; omega
  have h3 : (l.take j)[m]'h2 = l[m]'hml := by simp
  rw [List.getD_eq_getElem _ _ hml, ← h3]
  exact List.getElem_mem h2

theorem exists_getD_of_mem_take {l : List ℕ} {j a : ℕ} (h : a ∈ l.take j) :
    ∃ i, i < j ∧ i < l.length ∧ l.getD i 0 = a := by
  obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp h
  have hi' : i < j ∧ i < l.length := by
    simp only [List.length_take] at hi; omega
  refine ⟨i, hi'.1, hi'.2, ?_⟩
  rw [List.getD_eq_getElem _ _ hi'.2]
  simpa using hia

theorem mem_take_succ_iff {l : List ℕ} {j : ℕ} (hj : j < l.length) {a : ℕ} :
    a ∈ l.take (j + 1) ↔ a ∈ l.take j ∨ a = l.getD j 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj,
    Option.toList_some, List.mem_append, List.mem_singleton]

theorem getD_ne_of_nodup {l : List ℕ} (h : l.Nodup) {u v : ℕ} (hu : u < l.length)
    (hv : v < l.length) (huv : u ≠ v) : l.getD u 0 ≠ l.getD v 0 := by
  rw [List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv]
  intro he
  exact huv (h.getElem_inj_iff.mp he)

theorem nodup_idPerm (n : ℕ) : (idPerm n).Nodup := by
  unfold idPerm
  exact List.nodup_range'

/-! ## `foldl max` facts -/

theorem le_foldl_max (l : List ℕ) (b : ℕ) : b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons]
    exact le_trans (Nat.le_max_left b a) (ih (max b a))

theorem le_foldl_max_of_mem {l : List ℕ} {x : ℕ} (b : ℕ) (h : x ∈ l) :
    x ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp at h
  | cons a t ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hx
    · exact le_trans (Nat.le_max_right b x) (le_foldl_max t (max b x))
    · exact ih _ hx

theorem foldl_max_mem (l : List ℕ) (b : ℕ) : l.foldl max b = b ∨ l.foldl max b ∈ l := by
  induction l generalizing b with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons]
    rcases ih (max b a) with h | h
    · rw [h]
      rcases Nat.le_total a b with h' | h'
      · left; exact Nat.max_eq_left h'
      · right; rw [Nat.max_eq_right h']; simp
    · right; exact List.mem_cons_of_mem a h

/-! ## Counting -/

theorem count_true_add_count_false (l : List Bool) :
    l.count true + l.count false = l.length := by
  induction l with
  | nil => simp
  | cons b t ih => cases b <;> simp [List.count_cons] <;> omega

theorem countP_range'_lt (x : ℕ) : ∀ (len s : ℕ),
    (List.range' s len).countP (fun y => decide (y < x)) = min len (x - s) := by
  intro len
  induction len with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    rw [List.range'_succ, List.countP_cons, ih (s + 1)]
    by_cases h : s < x
    · rw [if_pos (by simpa using h)]; omega
    · rw [if_neg (by simpa using h)]; omega

theorem map_getD_range (l : List ℕ) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have h2 : ((fun i => (a :: t).getD i 0) ∘ Nat.succ) = fun i => t.getD i 0 := by
      funext i
      simp [Function.comp, List.getD_cons_succ]
    rw [h2, ih]
    simp

theorem countP_eq_countP_range (l : List ℕ) (pred : ℕ → Bool) :
    l.countP pred = (List.range l.length).countP (fun i => pred (l.getD i 0)) := by
  conv_lhs => rw [← map_getD_range l]
  rw [List.countP_map]
  rfl

theorem count_baseWord (n v : ℕ) :
    (baseWord n).count v = if 1 ≤ v ∧ v ≤ n then 2 else 0 := by
  induction n with
  | zero =>
    rw [if_neg (by omega)]
    simp [baseWord]
  | succ m ih =>
    have h1 : List.range' 1 (m + 1) = List.range' 1 m ++ [m + 1] := by
      simpa [Nat.add_comm] using (List.range'_concat (s := 1) (n := m) (step := 1))
    have hsplit : baseWord (m + 1) = baseWord m ++ [m + 1, m + 1] := by
      unfold baseWord
      rw [h1, List.flatMap_append]
      simp
    rw [hsplit, List.count_append, ih]
    have hc : List.count v [m + 1, m + 1] = if v = m + 1 then 2 else 0 := by
      by_cases h : v = m + 1 <;> simp [List.count_cons, h] <;> omega
    rw [hc]
    split_ifs <;> omega

/-! ## Second occurrences -/

/-- 0-based position of the second occurrence of `v` in `w` (junk if `v` occurs
fewer than twice). -/
def sndIdx (w : List ℕ) (v : ℕ) : ℕ :=
  w.idxOf v + 1 + (w.drop (w.idxOf v + 1)).idxOf v

theorem idxOf_lt_sndIdx (w : List ℕ) (v : ℕ) : w.idxOf v < sndIdx w v := by
  unfold sndIdx; omega

theorem getD_idxOf {w : List ℕ} {v : ℕ} (h : v ∈ w) : w.getD (w.idxOf v) 0 = v := by
  have hlt := List.idxOf_lt_length_of_mem h
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_idxOf hlt

theorem not_mem_take_idxOf (w : List ℕ) (v : ℕ) : v ∉ w.take (w.idxOf v) := by
  induction w with
  | nil => simp
  | cons a t ih =>
    by_cases h : a = v
    · rw [List.idxOf_cons_eq _ h]
      simp
    · rw [List.idxOf_cons_ne _ h]
      rw [List.take_succ_cons]
      intro hmem
      rcases List.mem_cons.mp hmem with h' | h'
      · exact h h'.symm
      · exact ih h'

theorem count_take_idxOf_succ {w : List ℕ} {v : ℕ} (h : v ∈ w) :
    (w.take (w.idxOf v + 1)).count v = 1 := by
  have hlt : w.idxOf v < w.length := List.idxOf_lt_length_of_mem h
  rw [List.take_succ, List.getElem?_eq_getElem hlt]
  rw [List.count_append]
  have h0 : (w.take (w.idxOf v)).count v = 0 :=
    List.count_eq_zero.mpr (not_mem_take_idxOf w v)
  rw [h0, List.getElem_idxOf hlt]
  simp

theorem sndIdx_spec {w : List ℕ} {v : ℕ} (h : 2 ≤ w.count v) :
    sndIdx w v < w.length ∧ w.getD (sndIdx w v) 0 = v := by
  have hv : v ∈ w := List.count_pos_iff.mp (by omega)
  have hlt : w.idxOf v < w.length := List.idxOf_lt_length_of_mem hv
  have hcount : (w.take (w.idxOf v + 1)).count v + (w.drop (w.idxOf v + 1)).count v
      = w.count v := by
    rw [← List.count_append, List.take_append_drop]
  have h1 : (w.take (w.idxOf v + 1)).count v = 1 := count_take_idxOf_succ hv
  have hv2 : v ∈ w.drop (w.idxOf v + 1) := List.count_pos_iff.mp (by omega)
  have hlt2 : (w.drop (w.idxOf v + 1)).idxOf v < (w.drop (w.idxOf v + 1)).length :=
    List.idxOf_lt_length_of_mem hv2
  have hlen : (w.drop (w.idxOf v + 1)).length = w.length - (w.idxOf v + 1) := by simp
  have hb : sndIdx w v < w.length := by unfold sndIdx; omega
  refine ⟨hb, ?_⟩
  rw [List.getD_eq_getElem _ _ hb]
  have hval := List.getElem_idxOf hlt2
  rw [List.getElem_drop] at hval
  exact hval

/-! ## Quadruple-to-`Contains` constructors

DEFINITIONS.md §2 containment is via a strictly increasing `f : Fin σ.length →
Fin w.length` with both biconditionals; for each of the four patterns the
explicit quadruple of positions/values below is exactly such an occurrence. -/

private theorem contains_of_quad {w : List ℕ} {i j k l : ℕ} (σ : List ℕ)
    (hσ : σ.length = 4)
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < w.length)
    (horder : ∀ r s : Fin σ.length,
      (w.get (![⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, by omega⟩, ⟨l, hl⟩]
        (Fin.cast hσ r)) < w.get (![⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, by omega⟩,
          ⟨l, hl⟩] (Fin.cast hσ s)) ↔ σ.get r < σ.get s))
    (heq : ∀ r s : Fin σ.length,
      (w.get (![⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, by omega⟩, ⟨l, hl⟩]
        (Fin.cast hσ r)) = w.get (![⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, by omega⟩,
          ⟨l, hl⟩] (Fin.cast hσ s)) ↔ σ.get r = σ.get s)) :
    Contains w σ := by
  refine ⟨fun r => ![⟨i, by omega⟩, ⟨j, by omega⟩, ⟨k, by omega⟩, ⟨l, hl⟩]
    (Fin.cast hσ r), ?_, horder, heq⟩
  intro r s hrs
  beta_reduce
  have hrs' : (Fin.cast hσ r : ℕ) < (Fin.cast hσ s : ℕ) := hrs
  clear hrs
  revert hrs'
  generalize Fin.cast hσ r = r'
  generalize Fin.cast hσ s = s'
  intro hrs'
  fin_cases r' <;> fin_cases s' <;>
    simp_all [Fin.mk_lt_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecTail,
      Matrix.vecHead] <;>
    omega

theorem contains_1132_of {w : List ℕ} {i j k l : ℕ}
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < w.length)
    (h1 : w.getD i 0 = w.getD j 0) (h2 : w.getD i 0 < w.getD l 0)
    (h3 : w.getD l 0 < w.getD k 0) : Contains w pat1132 := by
  have hi : i < w.length := by omega
  have hj : j < w.length := by omega
  have hk : k < w.length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h1
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hl] at h2
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hk] at h3
  refine contains_of_quad pat1132 rfl hij hjk hkl hl ?_ ?_ <;>
    (intro r s; fin_cases r <;> fin_cases s <;>
      simp_all [pat1132, Fin.lt_def, List.get_eq_getElem, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.vecTail, Matrix.vecHead] <;>
      omega)

theorem contains_3312_of {w : List ℕ} {i j k l : ℕ}
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < w.length)
    (h1 : w.getD i 0 = w.getD j 0) (h2 : w.getD k 0 < w.getD l 0)
    (h3 : w.getD l 0 < w.getD i 0) : Contains w pat3312 := by
  have hi : i < w.length := by omega
  have hj : j < w.length := by omega
  have hk : k < w.length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h1
  rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hl] at h2
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hi] at h3
  refine contains_of_quad pat3312 rfl hij hjk hkl hl ?_ ?_ <;>
    (intro r s; fin_cases r <;> fin_cases s <;>
      simp_all [pat3312, Fin.lt_def, List.get_eq_getElem, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.vecTail, Matrix.vecHead] <;>
      omega)

theorem contains_1221_of {w : List ℕ} {i j k l : ℕ}
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < w.length)
    (h1 : w.getD i 0 = w.getD l 0) (h2 : w.getD j 0 = w.getD k 0)
    (h3 : w.getD i 0 < w.getD j 0) : Contains w pat1221 := by
  have hi : i < w.length := by omega
  have hj : j < w.length := by omega
  have hk : k < w.length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hl] at h1
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk] at h2
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h3
  refine contains_of_quad pat1221 rfl hij hjk hkl hl ?_ ?_ <;>
    (intro r s; fin_cases r <;> fin_cases s <;>
      simp_all [pat1221, Fin.lt_def, List.get_eq_getElem, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.vecTail, Matrix.vecHead] <;>
      omega)

theorem contains_2112_of {w : List ℕ} {i j k l : ℕ}
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < w.length)
    (h1 : w.getD i 0 = w.getD l 0) (h2 : w.getD j 0 = w.getD k 0)
    (h3 : w.getD j 0 < w.getD i 0) : Contains w pat2112 := by
  have hi : i < w.length := by omega
  have hj : j < w.length := by omega
  have hk : k < w.length := by omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hl] at h1
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hk] at h2
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hi] at h3
  refine contains_of_quad pat2112 rfl hij hjk hkl hl ?_ ?_ <;>
    (intro r s; fin_cases r <;> fin_cases s <;>
      simp_all [pat2112, Fin.lt_def, List.get_eq_getElem, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.vecTail, Matrix.vecHead] <;>
      omega)

/-! ## Nonnesting: first occurrences ordered ⟹ second occurrences ordered

bijection.md Lemma 0, Step 2 (one direction): if `fst(u) < fst(v)` but
`snd(v) < snd(u)` the two arcs nest, producing a 1221 (if `u < v`) or 2112
(if `u > v`) occurrence. -/

theorem sndIdx_lt_sndIdx {w : List ℕ} (hnn : Nonnesting w) {u v : ℕ}
    (hu : 2 ≤ w.count u) (hv : 2 ≤ w.count v) (huv : u ≠ v)
    (hf : w.idxOf u < w.idxOf v) : sndIdx w u < sndIdx w v := by
  obtain ⟨hsu, hgu⟩ := sndIdx_spec hu
  obtain ⟨hsv, hgv⟩ := sndIdx_spec hv
  have humem : u ∈ w := List.count_pos_iff.mp (by omega)
  have hvmem : v ∈ w := List.count_pos_iff.mp (by omega)
  by_contra hcon
  push_neg at hcon
  have hne : sndIdx w v ≠ sndIdx w u := by
    intro he
    apply huv
    rw [← hgu, ← hgv, he]
  have hlt : sndIdx w v < sndIdx w u := by omega
  have hjk : w.idxOf v < sndIdx w v := idxOf_lt_sndIdx w v
  rcases Nat.lt_or_ge u v with hor | hor
  · -- u < v: occurrence of 1221 at fst(u) < fst(v) < snd(v) < snd(u)
    refine hnn.1 (contains_1221_of hf hjk hlt hsu ?_ ?_ ?_)
    · rw [getD_idxOf humem, hgu]
    · rw [getD_idxOf hvmem, hgv]
    · rw [getD_idxOf humem, getD_idxOf hvmem]; omega
  · -- v < u: occurrence of 2112
    have hor' : v < u := by omega
    refine hnn.2 (contains_2112_of hf hjk hlt hsu ?_ ?_ ?_)
    · rw [getD_idxOf humem, hgu]
    · rw [getD_idxOf hvmem, hgv]
    · rw [getD_idxOf humem, getD_idxOf hvmem]; omega

/-! ## `openerLabels` lists values in order of first occurrence -/

theorem openerLabels_go_not_mem_seen :
    ∀ (w seen : List ℕ) {x : ℕ}, x ∈ openerLabels.go w seen → x ∉ seen := by
  intro w
  induction w with
  | nil => intro seen x hx; simp [openerLabels.go] at hx
  | cons v rest ih =>
    intro seen x hx
    by_cases hv : v ∈ seen
    · rw [show openerLabels.go (v :: rest) seen = openerLabels.go rest seen by
        simp [openerLabels.go, hv]] at hx
      exact ih seen hx
    · rw [show openerLabels.go (v :: rest) seen
          = v :: openerLabels.go rest (v :: seen) by
        simp [openerLabels.go, hv]] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hv
      · intro hxs
        exact ih (v :: seen) hx' (List.mem_cons_of_mem v hxs)

theorem openerLabels_go_idxOf_lt :
    ∀ (w seen : List ℕ) {j m : ℕ}, j < m → m < (openerLabels.go w seen).length →
      w.idxOf ((openerLabels.go w seen).getD j 0)
        < w.idxOf ((openerLabels.go w seen).getD m 0) := by
  intro w
  induction w with
  | nil => intro seen j m hjm hm; simp [openerLabels.go] at hm
  | cons v rest ih =>
    intro seen j m hjm hm
    by_cases hv : v ∈ seen
    · rw [show openerLabels.go (v :: rest) seen = openerLabels.go rest seen by
        simp [openerLabels.go, hv]] at hm ⊢
      set L := openerLabels.go rest seen with hL
      have hxj : L.getD j 0 ∈ L := getD_mem (by omega)
      have hxm : L.getD m 0 ∈ L := getD_mem hm
      have hnej : v ≠ L.getD j 0 := by
        intro h
        exact openerLabels_go_not_mem_seen rest seen hxj (h ▸ hv)
      have hnem : v ≠ L.getD m 0 := by
        intro h
        exact openerLabels_go_not_mem_seen rest seen hxm (h ▸ hv)
      rw [List.idxOf_cons_ne _ hnej, List.idxOf_cons_ne _ hnem]
      exact Nat.succ_lt_succ (ih seen hjm hm)
    · rw [show openerLabels.go (v :: rest) seen
          = v :: openerLabels.go rest (v :: seen) by
        simp [openerLabels.go, hv]] at hm ⊢
      set L' := openerLabels.go rest (v :: seen) with hL'
      cases m with
      | zero => omega
      | succ m' =>
        have hm' : m' < L'.length := by simpa using hm
        have hxm : L'.getD m' 0 ∈ L' := getD_mem hm'
        have hnem : v ≠ L'.getD m' 0 := by
          intro h
          exact openerLabels_go_not_mem_seen rest (v :: seen) hxm
            (h ▸ List.mem_cons_self ..)
        cases j with
        | zero =>
          rw [List.getD_cons_zero, List.getD_cons_succ]
          rw [List.idxOf_cons_eq _ rfl, List.idxOf_cons_ne _ hnem]
          omega
        | succ j' =>
          have hxj : L'.getD j' 0 ∈ L' := getD_mem (by omega)
          have hnej : v ≠ L'.getD j' 0 := by
            intro h
            exact openerLabels_go_not_mem_seen rest (v :: seen) hxj
              (h ▸ List.mem_cons_self ..)
          rw [List.getD_cons_succ, List.getD_cons_succ]
          rw [List.idxOf_cons_ne _ hnej, List.idxOf_cons_ne _ hnem]
          exact Nat.succ_lt_succ (ih (v :: seen) (by omega) hm')

/-- The opener labels are listed in order of first occurrence: earlier label ⟹
strictly earlier first occurrence in `w`. -/
theorem openerLabels_idxOf_lt {w : List ℕ} {j m : ℕ} (hjm : j < m)
    (hm : m < (openerLabels w).length) :
    w.idxOf ((openerLabels w).getD j 0) < w.idxOf ((openerLabels w).getD m 0) :=
  openerLabels_go_idxOf_lt w [] hjm hm

end SW
end ElizaldeLuo
