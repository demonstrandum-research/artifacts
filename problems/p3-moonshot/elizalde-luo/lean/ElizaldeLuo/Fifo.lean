/-
# FIFO normal form: nonnesting words = (Dyck shape) × (label permutation)

bijection.md §1 (Lemma 0, Fact 0.1). A nonnesting word is identified with the pair
`(s, p)` of its opener/closer indicator (a Dyck word) and the list of values at the
openers in order; conversely `wd s p` interleaves them back ("FIFO matching": the i-th
closer carries the value of the i-th opener).

DEFINITIONS.md §3 ("Structured form (validated, not assumed)"): "a matching of $[2n]$
is nonnesting iff its $i$-th closer (second occurrence, in position order) is matched
to its $i$-th opener (first occurrence). Hence nonnesting words = (Dyck shape of
length $2n$) × (permutation $p\in S_n$ labeling the arcs in opener order)."

Encoding: shapes are `List Bool` (`true` = U = opener, `false` = D = closer),
0-based positions, 0-based arcs `0..n-1` (the draft's 1-based arc `J` is `J-1` here).

SORRY PACKAGE "fifo": `openerShape_isDyck`, `openerLabels_perm`, `wd_openerShape_openerLabels`,
`isMultisetPerm_wd`, `nonnesting_wd`, `openerShape_wd`, `openerLabels_wd`.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.WLang
import ElizaldeLuo.Helpers_fifo

namespace ElizaldeLuo

open FifoH

/-! ## Dyck words -/

/-- `s` is a Dyck word of semilength `n`: length `2n`, `n` openers (`true`), and every
prefix has at least as many openers as closers (bijection.md §1). -/
def IsDyck (n : ℕ) (s : List Bool) : Prop :=
  s.length = 2 * n ∧ s.count true = n ∧
    ∀ k ≤ s.length, (s.take k).count false ≤ (s.take k).count true

instance (n : ℕ) (s : List Bool) : Decidable (IsDyck n s) := by
  unfold IsDyck; infer_instance

/-- All Dyck words of semilength `n`. -/
def dycks (n : ℕ) : Finset (List Bool) :=
  (strings Bool (2 * n)).filter (IsDyck n)

/-! ## Positions, arcs, heights -/

/-- 0-based positions of the openers (`U`s) of a shape, in increasing order.
The draft's `o_1 < o_2 < ⋯ < o_n` is `openerPositions s = [o_1 - 1, …, o_n - 1]`. -/
def openerPositions (s : List Bool) : List ℕ :=
  (List.range s.length).filter fun k => s.getD k false = true

/-- 0-based positions of the closers (`D`s), in increasing order. -/
def closerPositions (s : List Bool) : List ℕ :=
  (List.range s.length).filter fun k => s.getD k false = false

/-- `oPos s j` = 0-based position of the opener of (0-based) arc `j`
(the draft's `o_{j+1}`, shifted to 0-based positions). Junk value 0 out of range. -/
def oPos (s : List Bool) (j : ℕ) : ℕ := (openerPositions s).getD j 0

/-- `qPos s j` = 0-based position of the `(j+1)`-th closer (the draft's `q_{j+1}`).
Under the FIFO matching this is the closer of arc `j`. Junk value 0 out of range. -/
def qPos (s : List Bool) (j : ℕ) : ℕ := (closerPositions s).getD j 0

/-- Height of the lattice path before (0-based) position `k`:
#openers − #closers among positions `< k` (ℕ-subtraction; nonnegative on Dyck
prefixes). bijection.md Lemma 3 uses this as the "start height" of tail openers. -/
def heightAt (s : List Bool) (k : ℕ) : ℕ :=
  ((s.take k).count true) - ((s.take k).count false)

/-- The first ascent `a(s) ≥ 1`: number of `U`s before the first `D`
(bijection.md §4). -/
def firstAscent (s : List Bool) : ℕ :=
  (s.takeWhile (· = true)).length

/-! ## Shape and labels of a word; the interleaving `wd` -/

/-- The opener/closer indicator of a word: position `k` is `true` iff it is the first
occurrence of its value (an *opener*), `false` if a *closer* (bijection.md §0). -/
def openerShape (w : List ℕ) : List Bool :=
  go w []
where
  go : List ℕ → List ℕ → List Bool
    | [], _ => []
    | v :: rest, seen => (if v ∈ seen then false else true) :: go rest (v :: seen)

/-- The label permutation of a word: its values in order of first occurrence
(`p_i` = value at the `i`-th opener, bijection.md Lemma 0). -/
def openerLabels (w : List ℕ) : List ℕ :=
  go w []
where
  go : List ℕ → List ℕ → List ℕ
    | [], _ => []
    | v :: rest, seen =>
        if v ∈ seen then go rest seen else v :: go rest (v :: seen)

/-- `wd s p`: the word with `p_i` at the `i`-th opener position of `s` and at the
`i`-th closer position (FIFO: the queue of currently open values is consumed
first-in-first-out). Junk (truncated) on inputs where `s` runs out of labels or
closes an empty queue. bijection.md §1: "For a Dyck word `s` and a permutation
`p = (p_1,…,p_n)` of `[n]` define `wd(s,p)` to be the word with `p_i` at position
`o_i` and at position `q_i`." -/
def wd (s : List Bool) (p : List ℕ) : List ℕ :=
  go s p []
where
  go : List Bool → List ℕ → List ℕ → List ℕ
    | [], _, _ => []
    | true :: s', v :: ps, queue => v :: go s' ps (queue ++ [v])
    | true :: _, [], _ => []
    | false :: s', ps, v :: queue => v :: go s' ps queue
    | false :: _, _, [] => []

/-- The identity labeling `[1, 2, …, n]`. -/
def idPerm (n : ℕ) : List ℕ := List.range' 1 n

/-- The permutations of `[n]` as words. -/
def permsOf (n : ℕ) : Finset (List ℕ) :=
  (idPerm n).permutations.toFinset

theorem mem_permsOf {n : ℕ} {p : List ℕ} : p ∈ permsOf n ↔ p.Perm (idPerm n) := by
  simp [permsOf, List.mem_permutations]

/-! ## Private helper lemmas (unfolding equations for the scans)

All helpers below are `private` (or live in `FifoH`, see `Helpers_fifo.lean`) so
that nothing leaks into the namespace used by the other sorry packages. -/

private theorem openerShape_go_nil (seen : List ℕ) :
    openerShape.go [] seen = [] := rfl

private theorem openerLabels_go_nil (seen : List ℕ) :
    openerLabels.go [] seen = [] := rfl

private theorem openerShape_go_cons (v : ℕ) (rest seen : List ℕ) :
    openerShape.go (v :: rest) seen
      = (if v ∈ seen then false else true) :: openerShape.go rest (v :: seen) := rfl

private theorem openerLabels_go_cons (v : ℕ) (rest seen : List ℕ) :
    openerLabels.go (v :: rest) seen
      = if v ∈ seen then openerLabels.go rest seen
        else v :: openerLabels.go rest (v :: seen) := rfl

private theorem wd_go_true_cons (s' : List Bool) (v : ℕ) (ps queue : List ℕ) :
    wd.go (true :: s') (v :: ps) queue = v :: wd.go s' ps (queue ++ [v]) := rfl

private theorem wd_go_false_cons (s' : List Bool) (ps : List ℕ) (v : ℕ)
    (queue : List ℕ) :
    wd.go (false :: s') ps (v :: queue) = v :: wd.go s' ps queue := rfl

/-! ### `openerLabels.go`: membership, nodup, congruence in the accumulator -/

private theorem openerLabels_go_mem : ∀ (w seen : List ℕ) (x : ℕ),
    x ∈ openerLabels.go w seen ↔ x ∈ w ∧ x ∉ seen
  | [], seen, x => by simp [openerLabels_go_nil]
  | v :: rest, seen, x => by
    rw [openerLabels_go_cons]
    by_cases hv : v ∈ seen
    · rw [if_pos hv, openerLabels_go_mem rest seen x]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact absurd hv h2
        · exact ⟨h1, h2⟩
    · rw [if_neg hv]
      constructor
      · intro hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact ⟨by simp, hv⟩
        · obtain ⟨h1, h2⟩ := (openerLabels_go_mem rest (v :: seen) x).mp hmem
          exact ⟨List.mem_cons_of_mem _ h1,
            fun hx => h2 (List.mem_cons_of_mem _ hx)⟩
      · rintro ⟨h1, h2⟩
        by_cases hxv : x = v
        · subst hxv
          exact by simp
        · rcases List.mem_cons.mp h1 with h | h1
          · exact absurd h hxv
          · refine List.mem_cons_of_mem _
              ((openerLabels_go_mem rest (v :: seen) x).mpr ⟨h1, fun hx => ?_⟩)
            rcases List.mem_cons.mp hx with h | h
            · exact hxv h
            · exact h2 h

private theorem openerLabels_go_nodup : ∀ (w seen : List ℕ),
    (openerLabels.go w seen).Nodup
  | [], _ => by simp [openerLabels_go_nil]
  | v :: rest, seen => by
    rw [openerLabels_go_cons]
    by_cases hv : v ∈ seen
    · rw [if_pos hv]
      exact openerLabels_go_nodup rest seen
    · rw [if_neg hv]
      refine List.nodup_cons.mpr ⟨fun hvmem => ?_, openerLabels_go_nodup rest (v :: seen)⟩
      exact ((openerLabels_go_mem rest (v :: seen) v).mp hvmem).2 (by simp)

private theorem openerLabels_go_congr : ∀ (w seen seen' : List ℕ),
    (∀ x ∈ w, x ∈ seen ↔ x ∈ seen') →
    openerLabels.go w seen = openerLabels.go w seen'
  | [], _, _, _ => rfl
  | v :: rest, seen, seen', h => by
    rw [openerLabels_go_cons, openerLabels_go_cons]
    have hv := h v (by simp)
    by_cases hvs : v ∈ seen
    · rw [if_pos hvs, if_pos (hv.mp hvs)]
      exact openerLabels_go_congr rest seen seen'
        (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · rw [if_neg hvs, if_neg (fun hh => hvs (hv.mpr hh))]
      rw [openerLabels_go_congr rest (v :: seen) (v :: seen')
        (fun x hx => by
          simp only [List.mem_cons]
          exact or_congr Iff.rfl (h x (List.mem_cons_of_mem _ hx)))]

/-! ### `openerShape.go`: length, count of openers, compatibility with `take` -/

private theorem openerShape_go_length : ∀ (w seen : List ℕ),
    (openerShape.go w seen).length = w.length
  | [], _ => rfl
  | v :: rest, seen => by
    rw [openerShape_go_cons, List.length_cons, List.length_cons,
      openerShape_go_length rest (v :: seen)]

private theorem openerShape_go_count_true : ∀ (w seen : List ℕ),
    (openerShape.go w seen).count true = (openerLabels.go w seen).length
  | [], _ => rfl
  | v :: rest, seen => by
    rw [openerShape_go_cons, openerLabels_go_cons]
    by_cases hv : v ∈ seen
    · rw [if_pos hv, if_pos hv,
        openerLabels_go_congr rest seen (v :: seen)
          (fun x _ => ⟨fun h => List.mem_cons_of_mem _ h, fun h => by
            rcases List.mem_cons.mp h with rfl | h
            · exact hv
            · exact h⟩),
        List.count_cons_of_ne (by decide), openerShape_go_count_true rest (v :: seen)]
    · rw [if_neg hv, if_neg hv, List.count_cons_self, List.length_cons,
        openerShape_go_count_true rest (v :: seen)]

private theorem openerShape_go_append : ∀ (w₁ w₂ seen : List ℕ),
    openerShape.go (w₁ ++ w₂) seen
      = openerShape.go w₁ seen ++ openerShape.go w₂ (w₁.reverse ++ seen)
  | [], w₂, seen => by simp [openerShape_go_nil]
  | v :: rest, w₂, seen => by
    rw [List.cons_append, openerShape_go_cons, openerShape_go_cons,
      openerShape_go_append rest w₂ (v :: seen), List.cons_append,
      show (v :: rest).reverse ++ seen = rest.reverse ++ (v :: seen) by
        simp [List.append_assoc]]

private theorem openerShape_take (w : List ℕ) (k : ℕ) :
    (openerShape w).take k = openerShape (w.take k) := by
  rcases Nat.le_total k w.length with hk | hk
  · have hsplit : openerShape w = openerShape.go (w.take k ++ w.drop k) [] := by
      rw [List.take_append_drop]; rfl
    have hlen : (openerShape.go (w.take k) []).length = k := by
      rw [openerShape_go_length, List.length_take]; omega
    rw [hsplit, openerShape_go_append, List.take_left' hlen]
    rfl
  · rw [List.take_of_length_le hk,
      List.take_of_length_le
        (by rw [show openerShape w = openerShape.go w [] from rfl,
          openerShape_go_length]; omega)]

/-! ### `idPerm` and `baseWord` facts -/

private theorem idPerm_length (n : ℕ) : (idPerm n).length = n := by
  simp [idPerm]

private theorem idPerm_nodup (n : ℕ) : (idPerm n).Nodup := List.nodup_range'

private theorem idPerm_mem {n x : ℕ} : x ∈ idPerm n ↔ 1 ≤ x ∧ x ≤ n := by
  rw [idPerm, List.mem_range'_1]
  omega

private theorem baseWord_perm_double (n : ℕ) :
    (baseWord n).Perm (idPerm n ++ idPerm n) := by
  rw [List.perm_iff_count]
  intro a
  rw [count_baseWord', List.count_append]
  by_cases h : 1 ≤ a ∧ a ≤ n
  · rw [if_pos h, List.count_eq_one_of_mem (idPerm_nodup n) (idPerm_mem.mpr h)]
  · rw [if_neg h, List.count_eq_zero_of_not_mem (fun hm => h (idPerm_mem.mp hm))]

/-! ### The forward scan invariant and reconstruction (Lemma 0, forward)

`seen` = values opened so far, `queue` = currently open values in opening order,
`w` = the remaining suffix. The nonnesting hypothesis is carried as
`¬ HasNesting (queue ++ w)`: the queue elements act as phantom openers in front of
the suffix, so both the "closers in queue order" and the "old arcs close before
new arcs" conditions of the draft's Lemma 0 Step 2 are single nesting conditions. -/

private structure FifoInv (seen queue w : List ℕ) : Prop where
  nodup : queue.Nodup
  sub : ∀ u ∈ queue, u ∈ seen
  closed : ∀ y ∈ seen, y ∉ queue → y ∉ w
  open_count : ∀ u ∈ queue, w.count u = 1
  fresh_count : ∀ x ∈ w, x ∉ seen → w.count x = 2
  nonnest : ¬ HasNesting (queue ++ w)

private theorem fifo_reconstruct : ∀ (w seen queue : List ℕ), FifoInv seen queue w →
    wd.go (openerShape.go w seen) (openerLabels.go w seen) queue = w
  | [], _, _, _ => rfl
  | v :: rest, seen, queue, inv => by
    rw [openerShape_go_cons, openerLabels_go_cons]
    by_cases hv : v ∈ seen
    · -- closer step
      rw [if_pos hv, if_pos hv]
      have hvq : v ∈ queue := by
        by_contra hvq
        exact inv.closed v hv hvq (by simp)
      obtain ⟨u, q', rfl⟩ : ∃ u q', queue = u :: q' := by
        cases queue with
        | nil => simp at hvq
        | cons u q' => exact ⟨u, q', rfl⟩
      -- the FIFO property: the closer v matches the *head* of the queue
      -- (otherwise the arcs of u and v nest, bijection.md Lemma 0 Step 2)
      have huv : u = v := by
        by_contra hne
        have hvq' : v ∈ q' := by
          rcases List.mem_cons.mp hvq with h | h
          · exact absurd h.symm hne
          · exact h
        obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hvq'
        have hur : u ∈ rest := by
          have hu1 : (v :: rest).count u = 1 := inv.open_count u (by simp)
          rw [List.count_cons_of_ne (Ne.symm hne)] at hu1
          exact List.count_pos_iff.mp (by omega)
        obtain ⟨m, hm, hmu⟩ := List.mem_iff_getElem.mp hur
        apply inv.nonnest
        refine ⟨0, j + 1, q'.length + 1, q'.length + 2 + m,
          by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
        · simp only [List.cons_append, List.length_cons, List.length_append]
          omega
        · rw [List.cons_append, List.getD_cons_zero]
          have h1 : q'.length + 2 + m = (q'.length + 1 + m) + 1 := by omega
          rw [h1, List.getD_cons_succ, getD_append_right (by omega)]
          have h2 : q'.length + 1 + m - q'.length = m + 1 := by omega
          rw [h2, List.getD_cons_succ, List.getD_eq_getElem _ _ hm, hmu]
        · rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ,
            getD_append_left hj, getD_append_right le_rfl, Nat.sub_self,
            List.getD_cons_zero, List.getD_eq_getElem _ _ hj, hjv]
        · rw [List.cons_append, List.getD_cons_zero, List.getD_cons_succ,
            getD_append_left hj, List.getD_eq_getElem _ _ hj, hjv]
          exact hne
      subst huv
      -- u = v: the closer consumes the queue head
      have hvrest : u ∉ rest := by
        have hv1 : (u :: rest).count u = 1 := inv.open_count u (by simp)
        rw [List.count_cons_self] at hv1
        exact List.count_eq_zero.mp (by omega)
      have hlab : openerLabels.go rest seen = openerLabels.go rest (u :: seen) :=
        openerLabels_go_congr rest seen (u :: seen) (fun x hx => by
          constructor
          · exact fun h => List.mem_cons_of_mem _ h
          · intro h
            rcases List.mem_cons.mp h with rfl | h
            · exact absurd hx hvrest
            · exact h)
      have hinv : FifoInv (u :: seen) q' rest := by
        refine ⟨(List.nodup_cons.mp inv.nodup).2, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun x hx => List.mem_cons_of_mem _ (inv.sub x (List.mem_cons_of_mem _ hx))
        · intro y hy hyq
          by_cases hyv : y = u
          · subst hyv
            exact hvrest
          · have hys : y ∈ seen := by
              rcases List.mem_cons.mp hy with h | h
              · exact absurd h hyv
              · exact h
            have hynq : y ∉ u :: q' := by
              intro hmem
              rcases List.mem_cons.mp hmem with h | h
              · exact hyv h
              · exact hyq h
            exact fun hyr => inv.closed y hys hynq (List.mem_cons_of_mem _ hyr)
        · intro x hx
          have hxv : x ≠ u := by
            intro h
            subst h
            exact (List.nodup_cons.mp inv.nodup).1 hx
          have := inv.open_count x (List.mem_cons_of_mem _ hx)
          rwa [List.count_cons_of_ne (Ne.symm hxv)] at this
        · intro x hx hxs
          have hxv : x ≠ u := by
            intro h
            subst h
            exact hxs (by simp)
          have hxseen : x ∉ seen := fun h => hxs (List.mem_cons_of_mem _ h)
          have := inv.fresh_count x (List.mem_cons_of_mem _ hx) hxseen
          rwa [List.count_cons_of_ne (Ne.symm hxv)] at this
        · intro hN
          apply inv.nonnest
          refine hN.sublist ?_
          rw [List.cons_append]
          exact ((List.sublist_cons_self u rest).append_left q').cons u
      rw [wd_go_false_cons, hlab, fifo_reconstruct rest (u :: seen) q' hinv]
    · -- opener step
      rw [if_neg hv, if_neg hv]
      have hinv : FifoInv (v :: seen) (queue ++ [v]) rest := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨inv.nodup, List.nodup_singleton v, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          intro heq
          subst heq
          exact hv (inv.sub a ha)
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact List.mem_cons_of_mem _ (inv.sub x h)
          · rw [List.mem_singleton] at h
            simp [h]
        · intro y hy hyq
          have hyv : y ≠ v := by
            intro h
            exact hyq (List.mem_append.mpr (Or.inr (by simp [h])))
          have hys : y ∈ seen := by
            rcases List.mem_cons.mp hy with h | h
            · exact absurd h hyv
            · exact h
          have hynq : y ∉ queue := fun h => hyq (List.mem_append.mpr (Or.inl h))
          exact fun hyr => inv.closed y hys hynq (List.mem_cons_of_mem _ hyr)
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · have hxv : x ≠ v := by
              intro he
              subst he
              exact hv (inv.sub x h)
            have := inv.open_count x h
            rwa [List.count_cons_of_ne (Ne.symm hxv)] at this
          · rw [List.mem_singleton] at h
            subst h
            have := inv.fresh_count x (by simp) hv
            rw [List.count_cons_self] at this
            omega
        · intro x hx hxs
          have hxv : x ≠ v := by
            intro he
            exact hxs (by simp [he])
          have hxseen : x ∉ seen := fun h => hxs (List.mem_cons_of_mem _ h)
          have := inv.fresh_count x (List.mem_cons_of_mem _ hx) hxseen
          rwa [List.count_cons_of_ne (Ne.symm hxv)] at this
        · have heq : (queue ++ [v]) ++ rest = queue ++ (v :: rest) := by
            rw [List.append_assoc, List.singleton_append]
          rw [heq]
          exact inv.nonnest
      rw [wd_go_true_cons, fifo_reconstruct rest (v :: seen) (queue ++ [v]) hinv]

/-! ### The converse scan: multiset content, shape/label recovery, nonnesting -/

private theorem wd_go_perm : ∀ (s : List Bool) (p queue : List ℕ),
    p.length = s.count true →
    (∀ k ≤ s.length, (s.take k).count false ≤ queue.length + (s.take k).count true) →
    s.count false = queue.length + s.count true →
    (wd.go s p queue).Perm (queue ++ (p ++ p))
  | [], p, queue, h1, _, h3 => by
    have hp : p = [] := List.length_eq_zero_iff.mp (by simpa using h1)
    have hq : queue = [] := List.length_eq_zero_iff.mp (by simpa using h3.symm)
    subst hp
    subst hq
    exact List.Perm.refl _
  | true :: s', p, queue, h1, h2, h3 => by
    obtain ⟨v, ps, rfl⟩ : ∃ v ps, p = v :: ps := by
      cases p with
      | nil =>
        exfalso
        rw [List.count_cons_self] at h1
        simp only [List.length_nil] at h1
        omega
      | cons v ps => exact ⟨v, ps, rfl⟩
    have h1' : ps.length = s'.count true := by
      rw [List.count_cons_self] at h1
      simp only [List.length_cons] at h1
      omega
    have h2' : ∀ k ≤ s'.length,
        (s'.take k).count false ≤ (queue ++ [v]).length + (s'.take k).count true := by
      intro k hk
      have h := h2 (k + 1) (by simpa using Nat.succ_le_succ hk)
      rw [List.take_succ_cons, List.count_cons_of_ne (by decide),
        List.count_cons_self] at h
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have h3' : s'.count false = (queue ++ [v]).length + s'.count true := by
      rw [List.count_cons_of_ne (by decide), List.count_cons_self] at h3
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [wd_go_true_cons]
    refine ((wd_go_perm s' ps (queue ++ [v]) h1' h2' h3').cons v).trans ?_
    rw [List.perm_iff_count]
    intro a
    by_cases ha : a = v <;>
      simp [List.count_append, List.count_cons, ha] <;> omega
  | false :: s', p, queue, h1, h2, h3 => by
    obtain ⟨u, q', rfl⟩ : ∃ u q', queue = u :: q' := by
      cases queue with
      | nil =>
        exfalso
        have h := h2 1 (by simp only [List.length_cons]; omega)
        rw [List.take_succ_cons, List.take_zero, List.count_cons_self,
          List.count_cons_of_ne (by decide)] at h
        simp at h
      | cons u q' => exact ⟨u, q', rfl⟩
    have h1' : p.length = s'.count true := by
      rwa [List.count_cons_of_ne (by decide)] at h1
    have h2' : ∀ k ≤ s'.length,
        (s'.take k).count false ≤ q'.length + (s'.take k).count true := by
      intro k hk
      have h := h2 (k + 1) (by simpa using Nat.succ_le_succ hk)
      rw [List.take_succ_cons, List.count_cons_self,
        List.count_cons_of_ne (by decide)] at h
      simp only [List.length_cons] at h
      omega
    have h3' : s'.count false = q'.length + s'.count true := by
      rw [List.count_cons_self, List.count_cons_of_ne (by decide)] at h3
      simp only [List.length_cons] at h3
      omega
    rw [wd_go_false_cons]
    exact (wd_go_perm s' p q' h1' h2' h3').cons u

private theorem openerShapeLabels_go_wd_go : ∀ (s : List Bool) (p queue seen : List ℕ),
    p.length = s.count true →
    (∀ k ≤ s.length, (s.take k).count false ≤ queue.length + (s.take k).count true) →
    s.count false = queue.length + s.count true →
    (queue ++ p).Nodup →
    (∀ u ∈ queue, u ∈ seen) →
    (∀ x ∈ p, x ∉ seen) →
    openerShape.go (wd.go s p queue) seen = s ∧
      openerLabels.go (wd.go s p queue) seen = p
  | [], p, queue, seen, h1, _, _, _, _, _ => by
    have hp : p = [] := List.length_eq_zero_iff.mp (by simpa using h1)
    subst hp
    exact ⟨rfl, rfl⟩
  | true :: s', p, queue, seen, h1, h2, h3, hnd, hI1, hI2 => by
    obtain ⟨v, ps, rfl⟩ : ∃ v ps, p = v :: ps := by
      cases p with
      | nil =>
        exfalso
        rw [List.count_cons_self] at h1
        simp only [List.length_nil] at h1
        omega
      | cons v ps => exact ⟨v, ps, rfl⟩
    have h1' : ps.length = s'.count true := by
      rw [List.count_cons_self] at h1
      simp only [List.length_cons] at h1
      omega
    have h2' : ∀ k ≤ s'.length,
        (s'.take k).count false ≤ (queue ++ [v]).length + (s'.take k).count true := by
      intro k hk
      have h := h2 (k + 1) (by simpa using Nat.succ_le_succ hk)
      rw [List.take_succ_cons, List.count_cons_of_ne (by decide),
        List.count_cons_self] at h
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have h3' : s'.count false = (queue ++ [v]).length + s'.count true := by
      rw [List.count_cons_of_ne (by decide), List.count_cons_self] at h3
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hnd' : ((queue ++ [v]) ++ ps).Nodup := by
      have heq : (queue ++ [v]) ++ ps = queue ++ (v :: ps) := by
        rw [List.append_assoc, List.singleton_append]
      rw [heq]
      exact hnd
    have hvps : v ∉ ps := by
      rcases List.nodup_append.mp hnd with ⟨-, hvp, -⟩
      exact (List.nodup_cons.mp hvp).1
    have hI1' : ∀ x ∈ queue ++ [v], x ∈ v :: seen := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_cons_of_mem _ (hI1 x h)
      · rw [List.mem_singleton] at h
        simp [h]
    have hI2' : ∀ x ∈ ps, x ∉ v :: seen := by
      intro x hx hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hvps (h ▸ hx)
      · exact hI2 x (List.mem_cons_of_mem _ hx) h
    have ih := openerShapeLabels_go_wd_go s' ps (queue ++ [v]) (v :: seen)
      h1' h2' h3' hnd' hI1' hI2'
    have hvseen : v ∉ seen := hI2 v (by simp)
    constructor
    · rw [wd_go_true_cons, openerShape_go_cons, if_neg hvseen, ih.1]
    · rw [wd_go_true_cons, openerLabels_go_cons, if_neg hvseen, ih.2]
  | false :: s', p, queue, seen, h1, h2, h3, hnd, hI1, hI2 => by
    obtain ⟨u, q', rfl⟩ : ∃ u q', queue = u :: q' := by
      cases queue with
      | nil =>
        exfalso
        have h := h2 1 (by simp only [List.length_cons]; omega)
        rw [List.take_succ_cons, List.take_zero, List.count_cons_self,
          List.count_cons_of_ne (by decide)] at h
        simp at h
      | cons u q' => exact ⟨u, q', rfl⟩
    have h1' : p.length = s'.count true := by
      rwa [List.count_cons_of_ne (by decide)] at h1
    have h2' : ∀ k ≤ s'.length,
        (s'.take k).count false ≤ q'.length + (s'.take k).count true := by
      intro k hk
      have h := h2 (k + 1) (by simpa using Nat.succ_le_succ hk)
      rw [List.take_succ_cons, List.count_cons_self,
        List.count_cons_of_ne (by decide)] at h
      simp only [List.length_cons] at h
      omega
    have h3' : s'.count false = q'.length + s'.count true := by
      rw [List.count_cons_self, List.count_cons_of_ne (by decide)] at h3
      simp only [List.length_cons] at h3
      omega
    have hnd' : (q' ++ p).Nodup := by
      have h := hnd
      rw [List.cons_append] at h
      exact (List.nodup_cons.mp h).2
    have hu_notin : u ∉ q' ++ p := by
      have h := hnd
      rw [List.cons_append] at h
      exact (List.nodup_cons.mp h).1
    have hu_out : u ∉ wd.go s' p q' := by
      intro hmem
      rw [List.Perm.mem_iff (wd_go_perm s' p q' h1' h2' h3')] at hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hu_notin (List.mem_append.mpr (Or.inl h))
      · rcases List.mem_append.mp h with h | h <;>
          exact hu_notin (List.mem_append.mpr (Or.inr h))
    have hI1' : ∀ x ∈ q', x ∈ u :: seen := fun x hx =>
      List.mem_cons_of_mem _ (hI1 x (List.mem_cons_of_mem _ hx))
    have hI2' : ∀ x ∈ p, x ∉ u :: seen := by
      intro x hx hmem
      rcases List.mem_cons.mp hmem with h | h
      · exact hu_notin (List.mem_append.mpr (Or.inr (h ▸ hx)))
      · exact hI2 x hx h
    have ih := openerShapeLabels_go_wd_go s' p q' (u :: seen)
      h1' h2' h3' hnd' hI1' hI2'
    have huseen : u ∈ seen := hI1 u (by simp)
    have hlab : openerLabels.go (wd.go s' p q') seen
        = openerLabels.go (wd.go s' p q') (u :: seen) :=
      openerLabels_go_congr (wd.go s' p q') seen (u :: seen) (fun x hx => by
        constructor
        · exact fun h => List.mem_cons_of_mem _ h
        · intro h
          rcases List.mem_cons.mp h with rfl | h
          · exact absurd hx hu_out
          · exact h)
    constructor
    · rw [wd_go_false_cons, openerShape_go_cons, if_pos huseen, ih.1]
    · rw [wd_go_false_cons, openerLabels_go_cons, if_pos huseen, hlab, ih.2]

private theorem wd_go_not_hasNesting : ∀ (s : List Bool) (p queue : List ℕ),
    p.length = s.count true →
    (∀ k ≤ s.length, (s.take k).count false ≤ queue.length + (s.take k).count true) →
    s.count false = queue.length + s.count true →
    (queue ++ p).Nodup →
    ¬ HasNesting (queue ++ wd.go s p queue)
  | [], p, queue, _, _, h3, _ => by
    have hq : queue = [] := List.length_eq_zero_iff.mp (by simpa using h3.symm)
    subst hq
    rintro ⟨i₁, i₂, i₃, i₄, -, -, -, h4, -, -, -⟩
    rw [show ([] : List ℕ) ++ wd.go [] p [] = [] from rfl] at h4
    simp at h4
  | true :: s', p, queue, h1, h2, h3, hnd => by
    obtain ⟨v, ps, rfl⟩ : ∃ v ps, p = v :: ps := by
      cases p with
      | nil =>
        exfalso
        rw [List.count_cons_self] at h1
        simp only [List.length_nil] at h1
        omega
      | cons v ps => exact ⟨v, ps, rfl⟩
    have h1' : ps.length = s'.count true := by
      rw [List.count_cons_self] at h1
      simp only [List.length_cons] at h1
      omega
    have h2' : ∀ k ≤ s'.length,
        (s'.take k).count false ≤ (queue ++ [v]).length + (s'.take k).count true := by
      intro k hk
      have h := h2 (k + 1) (by simpa using Nat.succ_le_succ hk)
      rw [List.take_succ_cons, List.count_cons_of_ne (by decide),
        List.count_cons_self] at h
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have h3' : s'.count false = (queue ++ [v]).length + s'.count true := by
      rw [List.count_cons_of_ne (by decide), List.count_cons_self] at h3
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hnd' : ((queue ++ [v]) ++ ps).Nodup := by
      have heq : (queue ++ [v]) ++ ps = queue ++ (v :: ps) := by
        rw [List.append_assoc, List.singleton_append]
      rw [heq]
      exact hnd
    have ih := wd_go_not_hasNesting s' ps (queue ++ [v]) h1' h2' h3' hnd'
    rw [wd_go_true_cons]
    have heq : queue ++ (v :: wd.go s' ps (queue ++ [v]))
        = (queue ++ [v]) ++ wd.go s' ps (queue ++ [v]) := by
      rw [List.append_assoc, List.singleton_append]
    rw [heq]
    exact ih
  | false :: s', p, queue, h1, h2, h3, hnd => by
    obtain ⟨u, q', rfl⟩ : ∃ u q', queue = u :: q' := by
      cases queue with
      | nil =>
        exfalso
        have h := h2 1 (by simp only [List.length_cons]; omega)
        rw [List.take_succ_cons, List.take_zero, List.count_cons_self,
          List.count_cons_of_ne (by decide)] at h
        simp at h
      | cons u q' => exact ⟨u, q', rfl⟩
    have h1' : p.length = s'.count true := by
      rwa [List.count_cons_of_ne (by decide)] at h1
    have h2' : ∀ k ≤ s'.length,
        (s'.take k).count false ≤ q'.length + (s'.take k).count true := by
      intro k hk
      have h := h2 (k + 1) (by simpa using Nat.succ_le_succ hk)
      rw [List.take_succ_cons, List.count_cons_self,
        List.count_cons_of_ne (by decide)] at h
      simp only [List.length_cons] at h
      omega
    have h3' : s'.count false = q'.length + s'.count true := by
      rw [List.count_cons_self, List.count_cons_of_ne (by decide)] at h3
      simp only [List.length_cons] at h3
      omega
    have hnd' : (q' ++ p).Nodup := by
      have := hnd
      rw [List.cons_append] at this
      exact (List.nodup_cons.mp this).2
    have hu_notin : u ∉ q' ++ p := by
      have := hnd
      rw [List.cons_append] at this
      exact (List.nodup_cons.mp this).1
    have hu_out : u ∉ wd.go s' p q' := by
      intro hmem
      rw [List.Perm.mem_iff (wd_go_perm s' p q' h1' h2' h3')] at hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hu_notin (List.mem_append.mpr (Or.inl h))
      · rcases List.mem_append.mp h with h | h <;>
          exact hu_notin (List.mem_append.mpr (Or.inr h))
    have ih := wd_go_not_hasNesting s' p q' h1' h2' h3' hnd'
    rw [wd_go_false_cons]
    intro hN
    set out := wd.go s' p q' with hout
    set W := (u :: q') ++ u :: out with hW
    set mid := q'.length + 1 with hmid
    obtain ⟨i₁, i₂, i₃, i₄, l12, l23, l34, hi4, e14, e23, hne⟩ := hN
    have hWlen : W.length = q'.length + out.length + 2 := by
      rw [hW]
      simp only [List.length_append, List.length_cons]
      omega
    have hg0 : W.getD 0 0 = u := by
      rw [hW, List.cons_append, List.getD_cons_zero]
    have hgq : ∀ j, j < q'.length → W.getD (j + 1) 0 = q'.getD j 0 := by
      intro j hj
      rw [hW, List.cons_append, List.getD_cons_succ, getD_append_left hj]
    have hgmid : W.getD mid 0 = u := by
      rw [hW, hmid, List.cons_append, List.getD_cons_succ,
        getD_append_right le_rfl, Nat.sub_self, List.getD_cons_zero]
    have hgout : ∀ m, W.getD (mid + 1 + m) 0 = out.getD m 0 := by
      intro m
      have h1 : mid + 1 + m = (q'.length + 1 + m) + 1 := by omega
      rw [hW, h1, List.cons_append, List.getD_cons_succ,
        getD_append_right (by omega)]
      have h2 : q'.length + 1 + m - q'.length = m + 1 := by omega
      rw [h2, List.getD_cons_succ]
    -- `u` occurs in `W` only at positions 0 and `mid`
    have hu_pos : ∀ i, i < W.length → W.getD i 0 = u → i = 0 ∨ i = mid := by
      intro i hi hval
      by_contra hcon
      have hi0 : i ≠ 0 := fun h => hcon (Or.inl h)
      have him : i ≠ mid := fun h => hcon (Or.inr h)
      rcases Nat.lt_or_ge i mid with hlt | hge
      · have hj : i - 1 < q'.length := by omega
        have hWi : W.getD i 0 = q'.getD (i - 1) 0 := by
          have h' := hgq (i - 1) hj
          have heq : i - 1 + 1 = i := by omega
          rwa [heq] at h'
        have hu_q : u ∈ q' := by
          rw [hWi, List.getD_eq_getElem _ _ hj] at hval
          exact hval ▸ List.getElem_mem hj
        exact hu_notin (List.mem_append.mpr (Or.inl hu_q))
      · have hbound : i - mid - 1 < out.length := by omega
        have hWi : W.getD i 0 = out.getD (i - mid - 1) 0 := by
          have h' := hgout (i - mid - 1)
          have heq : mid + 1 + (i - mid - 1) = i := by omega
          rwa [heq] at h'
        have hu_o : u ∈ out := by
          rw [hWi, List.getD_eq_getElem _ _ hbound] at hval
          exact hval ▸ List.getElem_mem hbound
        exact hu_out hu_o
    by_cases hz1 : i₁ = 0
    · -- position 0 carries `u`, so `i₄ = mid`; then `i₂ < i₃ < mid` lie in the
      -- nodup queue with equal values — impossible
      have h4u : W.getD i₄ 0 = u := by
        rw [← e14, hz1, hg0]
      rcases hu_pos i₄ hi4 h4u with h | h
      · omega
      · have hj2 : i₂ - 1 < q'.length := by omega
        have hj3 : i₃ - 1 < q'.length := by omega
        have hW2 : W.getD i₂ 0 = q'.getD (i₂ - 1) 0 := by
          have h' := hgq (i₂ - 1) hj2
          have heq : i₂ - 1 + 1 = i₂ := by omega
          rwa [heq] at h'
        have hW3 : W.getD i₃ 0 = q'.getD (i₃ - 1) 0 := by
          have h' := hgq (i₃ - 1) hj3
          have heq : i₃ - 1 + 1 = i₃ := by omega
          rwa [heq] at h'
        have heq23 : q'.getD (i₂ - 1) 0 = q'.getD (i₃ - 1) 0 := by
          rw [← hW2, ← hW3]
          exact e23
        rw [List.getD_eq_getElem _ _ hj2, List.getD_eq_getElem _ _ hj3] at heq23
        have hq'nd : q'.Nodup := by
          rcases List.nodup_append.mp hnd' with ⟨h, -, -⟩
          exact h
        have := (List.Nodup.getElem_inj_iff hq'nd).mp heq23
        omega
    · by_cases hm2 : i₂ = mid
      · have h3u : W.getD i₃ 0 = u := by rw [← e23, hm2, hgmid]
        rcases hu_pos i₃ (by omega) h3u with h | h <;> omega
      · by_cases hm3 : i₃ = mid
        · have h2u : W.getD i₂ 0 = u := by rw [e23, hm3, hgmid]
          rcases hu_pos i₂ (by omega) h2u with h | h <;> omega
        · by_cases hm1 : i₁ = mid
          · have h4u : W.getD i₄ 0 = u := by rw [← e14, hm1, hgmid]
            rcases hu_pos i₄ hi4 h4u with h | h <;> omega
          · by_cases hm4 : i₄ = mid
            · have h1u : W.getD i₁ 0 = u := by rw [e14, hm4, hgmid]
              rcases hu_pos i₁ (by omega) h1u with h | h <;> omega
            · -- none of the indices is 0 or mid: delete those two positions and
              -- transfer the nesting into `q' ++ out`, contradicting the IH
              have htrans : ∀ i, i < W.length → i ≠ 0 → i ≠ mid →
                  (if i < mid then i - 1 else i - 2) < (q' ++ out).length ∧
                  (q' ++ out).getD (if i < mid then i - 1 else i - 2) 0
                    = W.getD i 0 := by
                intro i hi hi0 himid
                by_cases hcase : i < mid
                · rw [if_pos hcase]
                  have hj : i - 1 < q'.length := by omega
                  refine ⟨by rw [List.length_append]; omega, ?_⟩
                  rw [getD_append_left hj]
                  have h' := hgq (i - 1) hj
                  have heq : i - 1 + 1 = i := by omega
                  rw [heq] at h'
                  exact h'.symm
                · rw [if_neg hcase]
                  refine ⟨by rw [List.length_append]; omega, ?_⟩
                  rw [getD_append_right (by omega)]
                  have h' := hgout (i - mid - 1)
                  have heq : mid + 1 + (i - mid - 1) = i := by omega
                  rw [heq] at h'
                  rw [h']
                  congr 1
                  omega
              have hφ : ∀ a b, a < b → a ≠ 0 → a ≠ mid → b ≠ 0 → b ≠ mid →
                  (if a < mid then a - 1 else a - 2)
                    < (if b < mid then b - 1 else b - 2) := by
                intro a b hab ha0 ham hb0 hbm
                split_ifs <;> omega
              have k1 := htrans i₁ (by omega) hz1 hm1
              have k2 := htrans i₂ (by omega) (by omega) hm2
              have k3 := htrans i₃ (by omega) (by omega) hm3
              have k4 := htrans i₄ hi4 (by omega) hm4
              exact ih ⟨_, _, _, _,
                hφ i₁ i₂ l12 hz1 hm1 (by omega) hm2,
                hφ i₂ i₃ l23 (by omega) hm2 (by omega) hm3,
                hφ i₃ i₄ l34 (by omega) hm3 (by omega) hm4,
                k4.1,
                by rw [k1.2, k4.2]; exact e14,
                by rw [k2.2, k3.2]; exact e23,
                by rw [k1.2, k2.2]; exact hne⟩

/-! ## Lemma 0 statements (sorry package "fifo") -/

/-- Lemma 0, forward direction (labels): the values of a permutation of `[n]₂` in
order of first occurrence form a permutation of `[n]`. (True for any multiset
permutation; nonnesting is not needed here.) -/
theorem openerLabels_perm {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w) :
    (openerLabels w).Perm (idPerm n) := by
  refine perm_of_nodup_of_mem_iff (openerLabels_go_nodup w []) (idPerm_nodup n) ?_
  intro a
  rw [show openerLabels w = openerLabels.go w [] from rfl,
    openerLabels_go_mem w [] a, idPerm_mem]
  have hmem : a ∈ w ↔ a ∈ baseWord n := List.Perm.mem_iff hw
  rw [mem_baseWord] at hmem
  simp [hmem]

set_option linter.unusedVariables false in
/-- Lemma 0, forward direction (shape): the opener/closer indicator of a nonnesting
permutation of `[n]₂` is a Dyck word of semilength `n`. (In fact `hnn` is not
needed: the shape of *any* multiset permutation is Dyck, since each closer's
opener precedes it.) -/
theorem openerShape_isDyck {n : ℕ} {w : List ℕ}
    (hw : IsMultisetPerm n w) (hnn : Nonnesting w) :
    IsDyck n (openerShape w) := by
  have hwlen : w.length = 2 * n := by
    rw [List.Perm.length_eq hw, length_baseWord]
  have hlab : (openerLabels w).length = n := by
    rw [List.Perm.length_eq (openerLabels_perm hw), idPerm_length]
  refine ⟨?_, ?_, ?_⟩
  · rw [show openerShape w = openerShape.go w [] from rfl, openerShape_go_length,
      hwlen]
  · rw [show openerShape w = openerShape.go w [] from rfl,
      openerShape_go_count_true]
    exact hlab
  · intro k _
    rw [openerShape_take]
    have hc : ∀ v, (w.take k).count v ≤ 2 := fun v =>
      le_trans ((List.take_sublist k w).count_le v)
        (count_le_two_of_perm_baseWord hw v)
    have hb := length_le_two_mul_of_count_le_two
      (openerLabels_go_nodup (w.take k) [])
      (fun x hx => (openerLabels_go_mem (w.take k) [] x).mpr ⟨hx, by simp⟩) hc
    have hsum := count_true_add_count_false' (openerShape (w.take k))
    have hlen' : (openerShape (w.take k)).length = (w.take k).length :=
      openerShape_go_length (w.take k) []
    have hct : (openerShape (w.take k)).count true
        = (openerLabels.go (w.take k) []).length :=
      openerShape_go_count_true (w.take k) []
    omega

/-- Lemma 0, forward direction (reconstruction): a nonnesting word is recovered from
its shape and labels — this is exactly the FIFO-matching property ("the i-th closer
carries the value of the i-th opener"). -/
theorem wd_openerShape_openerLabels {n : ℕ} {w : List ℕ}
    (hw : IsMultisetPerm n w) (hnn : Nonnesting w) :
    wd (openerShape w) (openerLabels w) = w := by
  refine fifo_reconstruct w [] [] ⟨List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    simp at hu
  · intro y hy
    simp at hy
  · intro u hu
    simp at hu
  · intro x hx _
    exact count_eq_two_of_perm_baseWord hw hx
  · rw [List.nil_append]
    exact nonnesting_iff_not_hasNesting.mp hnn

/-- Lemma 0, converse (membership): `wd s p` is a permutation of `[n]₂`. -/
theorem isMultisetPerm_wd {n : ℕ} {s : List Bool} {p : List ℕ}
    (hs : IsDyck n s) (hp : p.Perm (idPerm n)) :
    IsMultisetPerm n (wd s p) := by
  obtain ⟨hlen, htrue, hpre⟩ := hs
  have hplen : p.length = n := by rw [List.Perm.length_eq hp, idPerm_length]
  have hsum := count_true_add_count_false' s
  have hperm := wd_go_perm s p [] (by omega)
    (fun k hk => by simpa using hpre k hk)
    (by simp only [List.length_nil]; omega)
  rw [List.nil_append] at hperm
  exact hperm.trans ((hp.append hp).trans (baseWord_perm_double n).symm)

/-- Lemma 0, converse (nonnesting): "arcs simultaneously sorted by opener and closer
never nest, hence `wd(s,p)` is nonnesting." -/
theorem nonnesting_wd {n : ℕ} {s : List Bool} {p : List ℕ}
    (hs : IsDyck n s) (hp : p.Perm (idPerm n)) :
    Nonnesting (wd s p) := by
  obtain ⟨hlen, htrue, hpre⟩ := hs
  have hplen : p.length = n := by rw [List.Perm.length_eq hp, idPerm_length]
  have hsum := count_true_add_count_false' s
  rw [nonnesting_iff_not_hasNesting]
  have h := wd_go_not_hasNesting s p [] (by omega)
    (fun k hk => by simpa using hpre k hk)
    (by simp only [List.length_nil]; omega)
    (by simpa using (List.Perm.nodup_iff hp).mpr (idPerm_nodup n))
  rw [List.nil_append] at h
  exact h

/-- Lemma 0, uniqueness (shape recovery): the `i`-th `U`-position of `s` is the first
occurrence of `p_i` in `wd s p`. -/
theorem openerShape_wd {n : ℕ} {s : List Bool} {p : List ℕ}
    (hs : IsDyck n s) (hp : p.Perm (idPerm n)) :
    openerShape (wd s p) = s := by
  obtain ⟨hlen, htrue, hpre⟩ := hs
  have hplen : p.length = n := by rw [List.Perm.length_eq hp, idPerm_length]
  have hsum := count_true_add_count_false' s
  have hnd : p.Nodup := (List.Perm.nodup_iff hp).mpr (idPerm_nodup n)
  exact (openerShapeLabels_go_wd_go s p [] [] (by omega)
    (fun k hk => by simpa using hpre k hk)
    (by simp only [List.length_nil]; omega)
    (by simpa using hnd) (by simp) (by simp)).1

/-- Lemma 0, uniqueness (label recovery). -/
theorem openerLabels_wd {n : ℕ} {s : List Bool} {p : List ℕ}
    (hs : IsDyck n s) (hp : p.Perm (idPerm n)) :
    openerLabels (wd s p) = p := by
  obtain ⟨hlen, htrue, hpre⟩ := hs
  have hplen : p.length = n := by rw [List.Perm.length_eq hp, idPerm_length]
  have hsum := count_true_add_count_false' s
  have hnd : p.Nodup := (List.Perm.nodup_iff hp).mpr (idPerm_nodup n)
  exact (openerShapeLabels_go_wd_go s p [] [] (by omega)
    (fun k hk => by simpa using hpre k hk)
    (by simp only [List.length_nil]; omega)
    (by simpa using hnd) (by simp) (by simp)).2

end ElizaldeLuo
