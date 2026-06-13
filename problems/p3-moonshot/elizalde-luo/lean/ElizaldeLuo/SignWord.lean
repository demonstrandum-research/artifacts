/-
# The sign word: prefix-interval permutations and their {L,H}-encoding

bijection.md §3. "Call `p ∈ S_n` **prefix-interval** if every prefix set
`{p_1,…,p_j}` is an interval of integers; equivalently, for each `j ≥ 2` either
`p_j = min{p_1..p_{j-1}} - 1` (write `ε_j = L`) or `p_j = max{p_1..p_{j-1}} + 1`
(write `ε_j = H`). The word `ε = (ε_2,…,ε_n) ∈ {L,H}^(n-1)` is the **sign word**
of `p`."

Encoding: signs are `Bool` (`false` = L = "new low", `true` = H = "new high").
A sign word for `n` arcs is a `List Bool` of length `n-1`; the draft's 1-based
`ε_J` (J = 2..n) is `ε.getD (J - 2) false`, i.e. for a 0-based arc `j ≥ 1` the sign
is `ε.getD (j-1) false`.

SORRY PACKAGE "signword" (now fully proved): `signWordOf_permOfSigns`,
`permOfSigns_signWordOf`, `isPrefixInterval_permOfSigns`, `permOfSigns_perm`,
`signWordOf_length`, `comparison_rule` (Fact 3.2),
`labels_prefixInterval_of_avoider` (Lemma 2).

Auxiliary lemmas about `Defs`/`Fifo` objects live in `Helpers_signword.lean`
(namespace `SW`); the accumulator invariants for `signWordOf.go`/`permOfSigns.go`
are `private` lemmas in this file.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo
import ElizaldeLuo.Helpers_signword

namespace ElizaldeLuo

/-- `p` is **prefix-interval**: every prefix set `{p_1,…,p_k}` is an interval of
integers (bijection.md §3). Stated with the bound `z ≤ y` folded in so that the
proposition is decidable by bounded search. -/
def IsPrefixInterval (p : List ℕ) : Prop :=
  ∀ k ≤ p.length, ∀ x ∈ p.take k, ∀ y ∈ p.take k, ∀ z ≤ y, x ≤ z → z ∈ p.take k

instance (p : List ℕ) : Decidable (IsPrefixInterval p) := by
  unfold IsPrefixInterval; infer_instance

/-- The sign word `ε(p) ∈ {L,H}^(p.length - 1)` of a permutation: position `j-2`
(0-based) records whether `p_j` (1-based) is a new high (`true` = H) or not
(`false` = L, a new low for prefix-interval `p`). Junk-total: on non-prefix-interval
inputs the classification "greater than the current max" is still computed. -/
def signWordOf (p : List ℕ) : List Bool :=
  match p with
  | [] => []
  | v :: rest => go v rest
where
  go : ℕ → List ℕ → List Bool
    | _, [] => []
    | hi, v :: rest => if hi < v then true :: go v rest else (false :: go hi rest)

/-- Reconstruction of the unique prefix-interval permutation with a given sign word
(bijection.md Fact 3.1): "the L-steps fill values below `p_1` and the H-steps above,
so necessarily `p_1 = 1 + #{j : ε_j = L}`, and then every `p_j` is determined
(current min − 1 or current max + 1)." -/
def permOfSigns (ε : List Bool) : List ℕ :=
  let p1 := 1 + ε.count false
  p1 :: go p1 p1 ε
where
  go : ℕ → ℕ → List Bool → List ℕ
    | _, _, [] => []
    | lo, hi, true :: rest => (hi + 1) :: go lo (hi + 1) rest
    | lo, hi, false :: rest => (lo - 1) :: go (lo - 1) hi rest

/-! ## Accumulator invariants for `signWordOf.go` / `permOfSigns.go` -/

/-- `signWordOf.go` preserves length. -/
private theorem signWordOf_go_length : ∀ (l : List ℕ) (hi : ℕ),
    (signWordOf.go hi l).length = l.length := by
  intro l
  induction l with
  | nil => intro hi; simp [signWordOf.go]
  | cons v rest ih =>
    intro hi
    simp only [signWordOf.go]
    split <;> simp [ih]

/-- The sign word has length `n - 1`. -/
theorem signWordOf_length (p : List ℕ) :
    (signWordOf p).length = p.length - 1 := by
  cases p with
  | nil => simp [signWordOf]
  | cons v rest =>
    show (signWordOf.go v rest).length = (v :: rest).length - 1
    rw [signWordOf_go_length]
    simp

/-- The accumulator recursion of `permOfSigns` emits exactly the interval
`[lo - #L, lo - 1]` (from the `L`-steps, downwards) and `[hi + 1, hi + #H]`
(from the `H`-steps, upwards), as a multiset. -/
private theorem permOfSigns_go_perm :
    ∀ (ε : List Bool) (lo hi : ℕ), ε.count false < lo →
      (permOfSigns.go lo hi ε).Perm
        (List.range' (lo - ε.count false) (ε.count false) ++
          List.range' (hi + 1) (ε.count true)) := by
  intro ε
  induction ε with
  | nil =>
    intro lo hi _
    simp [permOfSigns.go]
  | cons b rest ih =>
    intro lo hi hlt
    cases b
    · -- b = false: emit lo - 1, recurse with lo - 1
      have hc : (false :: rest).count false = rest.count false + 1 :=
        List.count_cons_self
      have hct : (false :: rest).count true = rest.count true :=
        List.count_cons_of_ne (by simp)
      rw [hc] at hlt
      rw [hc, hct]
      simp only [permOfSigns.go]
      have e1 : lo - (rest.count false + 1) = lo - 1 - rest.count false := by omega
      have e2 : lo - 1 - rest.count false + 1 * rest.count false = lo - 1 := by omega
      rw [e1, List.range'_concat, e2, List.append_assoc, List.singleton_append]
      exact ((ih (lo - 1) hi (by omega)).cons (lo - 1)).trans List.perm_middle.symm
    · -- b = true: emit hi + 1, recurse with hi + 1
      have hc : (true :: rest).count false = rest.count false :=
        List.count_cons_of_ne (by simp)
      have hct : (true :: rest).count true = rest.count true + 1 :=
        List.count_cons_self
      rw [hc] at hlt
      rw [hc, hct]
      simp only [permOfSigns.go]
      rw [List.range'_succ]
      exact ((ih lo (hi + 1) hlt).cons (hi + 1)).trans List.perm_middle.symm

/-- Fact 3.1: the reconstruction from `ε ∈ {L,H}^(n-1)` "always yields a permutation
of `[n]`". -/
theorem permOfSigns_perm (ε : List Bool) :
    (permOfSigns ε).Perm (idPerm (ε.length + 1)) := by
  have h := permOfSigns_go_perm ε (1 + ε.count false) (1 + ε.count false) (by omega)
  rw [show 1 + ε.count false - ε.count false = 1 from by omega] at h
  show ((1 + ε.count false) ::
      permOfSigns.go (1 + ε.count false) (1 + ε.count false) ε).Perm
    (List.range' 1 (ε.length + 1))
  have hcnt := SW.count_true_add_count_false ε
  have h2 : List.range' 1 (ε.count false) ++
      (1 + ε.count false) :: List.range' (1 + ε.count false + 1) (ε.count true) =
      List.range' 1 (ε.length + 1) := by
    rw [show (1 + ε.count false) :: List.range' (1 + ε.count false + 1) (ε.count true)
        = List.range' (1 + ε.count false) (ε.count true + 1) from
      (List.range'_succ).symm]
    rw [List.range'_append_1,
      show List.count false ε + (List.count true ε + 1) = ε.length + 1 from by omega]
  have h3 : ((1 + ε.count false) :: (List.range' 1 (ε.count false) ++
      List.range' (1 + ε.count false + 1) (ε.count true))).Perm
        (List.range' 1 (ε.length + 1)) := by
    rw [← h2]
    exact List.perm_middle.symm
  exact (h.cons _).trans h3

/-- Truncating the reconstruction = reconstructing from the truncated sign word. -/
private theorem permOfSigns_go_take :
    ∀ (ε : List Bool) (j lo hi : ℕ),
      (permOfSigns.go lo hi ε).take j = permOfSigns.go lo hi (ε.take j) := by
  intro ε
  induction ε with
  | nil => intro j lo hi; simp [permOfSigns.go]
  | cons b rest ih =>
    intro j lo hi
    cases j with
    | zero => simp [permOfSigns.go]
    | succ j' =>
      cases b <;> simp only [permOfSigns.go, List.take_succ_cons] <;> rw [ih]

/-- Fact 3.1: the reconstruction is prefix-interval. -/
theorem isPrefixInterval_permOfSigns (ε : List Bool) :
    IsPrefixInterval (permOfSigns ε) := by
  intro k hk x hx y hy z hzy hxz
  cases k with
  | zero => simp at hx
  | succ j =>
    -- every prefix of the reconstruction is exactly an interval of integers
    have hcj : (ε.take j).count false ≤ ε.count false :=
      (List.take_sublist j ε).count_le false
    have key : ∀ a : ℕ, a ∈ (permOfSigns ε).take (j + 1) ↔
        (1 + ε.count false) - (ε.take j).count false ≤ a ∧
          a ≤ (1 + ε.count false) + (ε.take j).count true := by
      intro a
      have hperm := permOfSigns_go_perm (ε.take j) (1 + ε.count false)
        (1 + ε.count false) (by omega)
      have hunfold : (permOfSigns ε).take (j + 1) =
          (1 + ε.count false) ::
            permOfSigns.go (1 + ε.count false) (1 + ε.count false) (ε.take j) := by
        show ((1 + ε.count false) ::
            permOfSigns.go (1 + ε.count false) (1 + ε.count false) ε).take (j + 1) = _
        rw [List.take_succ_cons, permOfSigns_go_take]
      rw [hunfold]
      simp only [List.mem_cons, hperm.mem_iff, List.mem_append, List.mem_range'_1]
      omega
    rw [key] at hx hy ⊢
    omega

/-- Reading the sign word back off the reconstruction, relative to accumulators
`lo ≤ hi`: an `H`-step emits `hi + 1 > hi` (a new high), an `L`-step emits
`lo - 1 ≤ hi` (not a new high). -/
private theorem signWordOf_go_permOfSigns_go :
    ∀ (ε : List Bool) (lo hi : ℕ), lo ≤ hi →
      signWordOf.go hi (permOfSigns.go lo hi ε) = ε := by
  intro ε
  induction ε with
  | nil => intro lo hi _; simp [permOfSigns.go, signWordOf.go]
  | cons b rest ih =>
    intro lo hi hle
    cases b
    · simp only [permOfSigns.go, signWordOf.go]
      rw [if_neg (by omega)]
      rw [ih (lo - 1) hi (by omega)]
    · simp only [permOfSigns.go, signWordOf.go]
      rw [if_pos (by omega)]
      rw [ih lo (hi + 1) (by omega)]

/-- Fact 3.1, one inverse identity: `ε ∘ reconstruction = id` on `{L,H}^(n-1)`. -/
theorem signWordOf_permOfSigns (ε : List Bool) :
    signWordOf (permOfSigns ε) = ε := by
  show signWordOf.go (1 + ε.count false)
    (permOfSigns.go (1 + ε.count false) (1 + ε.count false) ε) = ε
  exact signWordOf_go_permOfSigns_go ε _ _ le_rfl

/-- The `getD`-level meaning of `signWordOf.go`: position `i` records whether
`l_i` exceeds the running maximum (of `hi` and the earlier entries). -/
private theorem signWordOf_go_getD :
    ∀ (l : List ℕ) (hi i : ℕ), i < l.length →
      ((signWordOf.go hi l).getD i false = true ↔
        (l.take i).foldl max hi < l.getD i 0) := by
  intro l
  induction l with
  | nil => intro hi i h; simp at h
  | cons v rest ih =>
    intro hi i h
    simp only [signWordOf.go]
    by_cases hv : hi < v
    · rw [if_pos hv]
      cases i with
      | zero => simp [hv]
      | succ i' =>
        have hlen : i' < rest.length := by simpa using h
        rw [List.getD_cons_succ, List.getD_cons_succ, List.take_succ_cons,
          List.foldl_cons, Nat.max_eq_right (Nat.le_of_lt hv)]
        exact ih v i' hlen
    · rw [if_neg hv]
      cases i with
      | zero => simp [hv]
      | succ i' =>
        have hlen : i' < rest.length := by simpa using h
        rw [List.getD_cons_succ, List.getD_cons_succ, List.take_succ_cons,
          List.foldl_cons, Nat.max_eq_left (Nat.le_of_not_lt hv)]
        exact ih hi i' hlen

/-- **Fact 3.2 (comparison rule).** "If `p` is prefix-interval with sign word `ε`,
then for all `1 ≤ u < v ≤ n`: `p_u < p_v ↔ ε_v = H` and `p_u > p_v ↔ ε_v = L`."
Stated 0-based: for `u < v < p.length`, the sign of (0-based) arc `v` is
`(signWordOf p).getD (v-1) false`. The second biconditional follows from the first
by linearity (entries of a permutation are distinct), so only the first is stated. -/
theorem comparison_rule {n : ℕ} {p : List ℕ}
    (hp : p.Perm (idPerm n)) (hpi : IsPrefixInterval p)
    {u v : ℕ} (huv : u < v) (hv : v < p.length) :
    p.getD u 0 < p.getD v 0 ↔ (signWordOf p).getD (v - 1) false = true := by
  cases p with
  | nil => simp at hv
  | cons p₀ rest =>
    obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
    have hv' : v' < rest.length := by simpa using hv
    have hsw : signWordOf (p₀ :: rest) = signWordOf.go p₀ rest := rfl
    rw [hsw, show v' + 1 - 1 = v' from by omega,
      signWordOf_go_getD rest p₀ v' hv', List.getD_cons_succ]
    -- `M` is the maximum of the length-(v'+1) prefix …
    have hub : (p₀ :: rest).getD u 0 ≤ (rest.take v').foldl max p₀ := by
      cases u with
      | zero => simpa using SW.le_foldl_max (rest.take v') p₀
      | succ u'' =>
        rw [List.getD_cons_succ]
        exact SW.le_foldl_max_of_mem p₀ (SW.getD_mem_take (by omega) (by omega))
    constructor
    · -- if `p_v` is not a new high, the interval property would force `p_v`
      -- into the prefix, contradicting distinctness
      intro hlt
      by_contra hMge
      push_neg at hMge
      have hMmem : (rest.take v').foldl max p₀ ∈ (p₀ :: rest).take (v' + 1) := by
        rw [List.take_succ_cons]
        rcases SW.foldl_max_mem (rest.take v') p₀ with h | h
        · rw [h]; simp
        · exact List.mem_cons_of_mem _ h
      have hxmem : (p₀ :: rest).getD u 0 ∈ (p₀ :: rest).take (v' + 1) :=
        SW.getD_mem_take (by omega) (by omega)
      have hzmem := hpi (v' + 1) (Nat.le_of_lt hv) _ hxmem _ hMmem
        ((p₀ :: rest).getD (v' + 1) 0)
        (by rw [List.getD_cons_succ]; exact hMge)
        (by rw [List.getD_cons_succ]; omega)
      have hnd : (p₀ :: rest).Nodup := hp.nodup_iff.mpr (SW.nodup_idPerm n)
      obtain ⟨iidx, hi1, hi2, hieq⟩ := SW.exists_getD_of_mem_take hzmem
      exact SW.getD_ne_of_nodup hnd hi2 hv (by omega) hieq
    · -- a new high exceeds the whole prefix, in particular `p_u`
      intro hsign
      omega

/-! ## Fact 3.1, the harder inverse: rank/order-isomorphism argument

Two prefix-interval permutations of `[n]` with the same sign word are equal: by
the comparison rule all pairwise comparisons agree, hence every entry has the
same rank, and a permutation of `[n]` is determined by its ranks. Applying this
to `p` and `permOfSigns (signWordOf p)` gives the identity. -/

/-- In a permutation of `[n]`, each entry equals one plus the number of strictly
smaller entries. -/
private theorem getD_eq_countP_lt {n : ℕ} {l : List ℕ} (hl : l.Perm (idPerm n))
    {v : ℕ} (hv : v < l.length) :
    l.getD v 0 = l.countP (fun y => decide (y < l.getD v 0)) + 1 := by
  have hxl : l.getD v 0 ∈ l := SW.getD_mem hv
  have hxr : 1 ≤ l.getD v 0 ∧ l.getD v 0 ≤ n := by
    have h := hl.mem_iff.mp hxl
    unfold idPerm at h
    rw [List.mem_range'_1] at h
    omega
  have hcount : l.countP (fun y => decide (y < l.getD v 0)) =
      min n (l.getD v 0 - 1) := by
    rw [hl.countP_eq]
    show (List.range' 1 n).countP _ = _
    exact SW.countP_range'_lt (l.getD v 0) n 1
  omega

/-- If all pairwise comparisons of two lists agree, the rank counts agree. -/
private theorem countP_index_congr {q p : List ℕ} (hlen : q.length = p.length)
    (hcomp : ∀ u v', u < q.length → v' < q.length →
      (q.getD u 0 < q.getD v' 0 ↔ p.getD u 0 < p.getD v' 0))
    {v : ℕ} (hv : v < q.length) :
    q.countP (fun y => decide (y < q.getD v 0)) =
      p.countP (fun y => decide (y < p.getD v 0)) := by
  rw [SW.countP_eq_countP_range q, SW.countP_eq_countP_range p, ← hlen]
  apply List.countP_congr
  intro u hu
  rw [List.mem_range] at hu
  simpa using hcomp u v hu hv

/-- Fact 3.1, the other inverse identity: reconstruction recovers any prefix-interval
permutation of `[n]` from its sign word.

(The hypothesis `1 ≤ n` is necessary: `permOfSigns` always returns a nonempty
list, so the identity fails for the empty permutation `p = []` at `n = 0`. The
sign-word correspondence of bijection.md Fact 3.1 is for permutations of `[n]`
with `n ≥ 1`.) -/
theorem permOfSigns_signWordOf {n : ℕ} {p : List ℕ} (hn : 1 ≤ n)
    (hp : p.Perm (idPerm n)) (hpi : IsPrefixInterval p) :
    permOfSigns (signWordOf p) = p := by
  have hplen : p.length = n := by simpa [idPerm] using hp.length_eq
  have hεlen : (signWordOf p).length = n - 1 := by rw [signWordOf_length, hplen]
  have hq1 : signWordOf (permOfSigns (signWordOf p)) = signWordOf p :=
    signWordOf_permOfSigns (signWordOf p)
  have hq2 : IsPrefixInterval (permOfSigns (signWordOf p)) :=
    isPrefixInterval_permOfSigns (signWordOf p)
  have hq3 : (permOfSigns (signWordOf p)).Perm (idPerm n) := by
    have h := permOfSigns_perm (signWordOf p)
    rw [hεlen, show n - 1 + 1 = n from by omega] at h
    exact h
  have hqlen : (permOfSigns (signWordOf p)).length = n := by
    simpa [idPerm] using hq3.length_eq
  set q := permOfSigns (signWordOf p) with hqdef
  have hndq : q.Nodup := hq3.nodup_iff.mpr (SW.nodup_idPerm n)
  have hndp : p.Nodup := hp.nodup_iff.mpr (SW.nodup_idPerm n)
  -- all pairwise comparisons of `q` and `p` agree (same sign word, Fact 3.2)
  have hcomp : ∀ u v', u < q.length → v' < q.length →
      (q.getD u 0 < q.getD v' 0 ↔ p.getD u 0 < p.getD v' 0) := by
    intro u v' hu hv'
    rcases Nat.lt_trichotomy u v' with huv | rfl | hvu
    · have hcq := comparison_rule hq3 hq2 huv hv'
      have hcp := comparison_rule hp hpi huv (by omega)
      rw [hq1] at hcq
      rw [hcq, hcp]
    · simp
    · have hcq := comparison_rule hq3 hq2 hvu hu
      have hcp := comparison_rule hp hpi hvu (by omega)
      rw [hq1] at hcq
      have hne_q : q.getD u 0 ≠ q.getD v' 0 :=
        SW.getD_ne_of_nodup hndq hu hv' (by omega)
      have hne_p : p.getD u 0 ≠ p.getD v' 0 :=
        SW.getD_ne_of_nodup hndp (by omega) (by omega) (by omega)
      by_cases hb : (signWordOf p).getD (u - 1) false = true
      · have h1 := hcq.mpr hb
        have h2 := hcp.mpr hb
        omega
      · have h1 : ¬ q.getD v' 0 < q.getD u 0 := fun hcon => hb (hcq.mp hcon)
        have h2 : ¬ p.getD v' 0 < p.getD u 0 := fun hcon => hb (hcp.mp hcon)
        omega
  -- hence the entries agree pointwise (equal ranks in equal value sets)
  apply List.ext_getElem (by omega)
  intro i h1 h2
  have hrq := getD_eq_countP_lt hq3 (show i < q.length from h1)
  have hrp := getD_eq_countP_lt hp (show i < p.length from h2)
  have hc := countP_index_congr (by omega) hcomp (show i < q.length from h1)
  have hgd : q.getD i 0 = p.getD i 0 := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hgd
  exact hgd

/-- **Lemma 2.** "If `(s,p)` is an avoider then `p` is prefix-interval."
Stated on the word side: the opener labels of an avoider form a prefix-interval
permutation.

Proof (bijection.md §3, recast to avoid closer positions): induct on the prefix
length. If the length-(j+1) prefix of `p = openerLabels w` violates the interval
property with witnesses `x ≤ z ≤ y`, `z` missing, then since the length-`j`
prefix is interval-closed the new entry `p_j` is `x` or `y`. Say `y = p_j` (the
other case is symmetric): then `z` exceeds the whole length-`j` prefix and
`z < p_j`, so `h := p_j - 1` satisfies `prefix < z ≤ h < p_j`, hence `h = p_m`
for some `m > j`. The first occurrences of `p_0, p_j, p_m` come in this order;
since `w` is nonnesting their second occurrences come in the same order
(`SW.sndIdx_lt_sndIdx`), and the four positions
`fst(p_0) < snd(p_0) < snd(p_j) < snd(p_m)` carry values `p_0, p_0, p_j, h` with
`p_0 < h < p_j` — an occurrence of 1132. The symmetric case (`x = p_j`,
`h := p_j + 1`) produces 3312. -/
theorem labels_prefixInterval_of_avoider {n : ℕ} {w : List ℕ}
    (hw : IsAvoider n w) :
    IsPrefixInterval (openerLabels w) := by
  obtain ⟨hperm, hnn, hav1, hav2⟩ := hw
  have hperm' : w.Perm (baseWord n) := hperm
  have hp : (openerLabels w).Perm (idPerm n) := openerLabels_perm hperm
  have hbounds : ∀ {x : ℕ}, x ∈ openerLabels w → 1 ≤ x ∧ x ≤ n := by
    intro x hx
    have h := hp.mem_iff.mp hx
    unfold idPerm at h
    rw [List.mem_range'_1] at h
    omega
  have hcount : ∀ {x : ℕ}, 1 ≤ x → x ≤ n → w.count x = 2 := by
    intro x h1 h2
    rw [hperm'.count_eq, SW.count_baseWord, if_pos ⟨h1, h2⟩]
  have hmemw : ∀ {x : ℕ}, 1 ≤ x → x ≤ n → x ∈ w := by
    intro x h1 h2
    have h := hcount h1 h2
    exact List.count_pos_iff.mp (by omega)
  intro k
  induction k with
  | zero =>
    intro _ x hx
    simp at hx
  | succ j ihj =>
    intro hk
    have hjlen : j < (openerLabels w).length := hk
    have hQj := ihj (by omega)
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hx, y, hy, z, hzy, hxz, hz⟩ := hcon
    rw [SW.mem_take_succ_iff hjlen] at hx hy
    have hz1 : z ∉ (openerLabels w).take j := fun h =>
      hz ((SW.mem_take_succ_iff hjlen).mpr (Or.inl h))
    have hz2 : z ≠ (openerLabels w).getD j 0 := fun h =>
      hz ((SW.mem_take_succ_iff hjlen).mpr (Or.inr h))
    rcases hx with hxtj | hxeq
    · rcases hy with hytj | hyeq
      · -- both endpoints in the closed length-j prefix: contradiction
        exact hz1 (hQj x hxtj y hytj z hzy hxz)
      · -- y = p_j: the "new high gap" case, produces 1132
        subst hyeq
        set pj := (openerLabels w).getD j 0 with hpj
        have hxlt : x < z := lt_of_le_of_ne hxz (fun h => hz1 (h ▸ hxtj))
        have hzlt : z < pj := lt_of_le_of_ne hzy hz2
        have hall : ∀ q' ∈ (openerLabels w).take j, q' < z := by
          intro q' hq'
          by_contra hge
          push_neg at hge
          exact hz1 (hQj x hxtj q' hq' z hge hxz)
        have h0j : 0 < j := by
          cases j with
          | zero => simp at hxtj
          | succ _ => omega
        have hxmem : x ∈ openerLabels w := List.mem_of_mem_take hxtj
        have hx1 : 1 ≤ x := (hbounds hxmem).1
        have hpjmem : pj ∈ openerLabels w := SW.getD_mem hjlen
        have hpjn : pj ≤ n := (hbounds hpjmem).2
        have hh1 : 1 ≤ pj - 1 := by omega
        have hhn : pj - 1 ≤ n := by omega
        have hhp : pj - 1 ∈ openerLabels w := by
          apply hp.mem_iff.mpr
          unfold idPerm
          rw [List.mem_range'_1]
          omega
        obtain ⟨m, hm, hpm⟩ := List.mem_iff_getElem.mp hhp
        have hpmD : (openerLabels w).getD m 0 = pj - 1 := by
          rw [List.getD_eq_getElem _ _ hm]; exact hpm
        have hmj : j < m := by
          rcases Nat.lt_trichotomy m j with hlt | heq | hgt
          · have hmem : pj - 1 ∈ (openerLabels w).take j :=
              hpmD ▸ SW.getD_mem_take hlt hm
            have := hall _ hmem
            omega
          · rw [heq] at hpmD
            rw [← hpj] at hpmD
            omega
          · exact hgt
        have h0len : 0 < (openerLabels w).length := by omega
        set a := (openerLabels w).getD 0 0 with ha
        have hamem' : a ∈ (openerLabels w).take j := SW.getD_mem_take h0j h0len
        have haz : a < z := hall a hamem'
        have hamem : a ∈ openerLabels w := SW.getD_mem h0len
        have ha1 : 1 ≤ a := (hbounds hamem).1
        have han : a ≤ n := (hbounds hamem).2
        have hca : w.count a = 2 := hcount ha1 han
        have hcc : w.count pj = 2 := hcount (by omega) hpjn
        have hch : w.count (pj - 1) = 2 := hcount hh1 hhn
        have hf1 : w.idxOf a < w.idxOf pj := by
          have h := SW.openerLabels_idxOf_lt h0j hjlen
          rwa [← ha, ← hpj] at h
        have hf2 : w.idxOf pj < w.idxOf (pj - 1) := by
          have h := SW.openerLabels_idxOf_lt hmj hm
          rwa [← hpj, hpmD] at h
        have hs1 : SW.sndIdx w a < SW.sndIdx w pj :=
          SW.sndIdx_lt_sndIdx hnn (by omega) (by omega) (by omega) hf1
        have hs2 : SW.sndIdx w pj < SW.sndIdx w (pj - 1) :=
          SW.sndIdx_lt_sndIdx hnn (by omega) (by omega) (by omega) hf2
        obtain ⟨hsl, hsv⟩ := SW.sndIdx_spec (w := w) (v := pj - 1) (by omega)
        obtain ⟨hsla, hsva⟩ := SW.sndIdx_spec (w := w) (v := a) (by omega)
        obtain ⟨hslc, hsvc⟩ := SW.sndIdx_spec (w := w) (v := pj) (by omega)
        refine hav1 (SW.contains_1132_of (SW.idxOf_lt_sndIdx w a) hs1 hs2 hsl
          ?_ ?_ ?_)
        · rw [SW.getD_idxOf (hmemw ha1 han), hsva]
        · rw [SW.getD_idxOf (hmemw ha1 han), hsv]; omega
        · rw [hsv, hsvc]; omega
    · rcases hy with hytj | hyeq
      · -- x = p_j: the "new low gap" case, produces 3312
        subst hxeq
        set pj := (openerLabels w).getD j 0 with hpj
        have hpjz : pj < z := lt_of_le_of_ne hxz (fun h => hz2 h.symm)
        have hzy' : z < y := lt_of_le_of_ne hzy (fun h => hz1 (h ▸ hytj))
        have hall : ∀ q' ∈ (openerLabels w).take j, z < q' := by
          intro q' hq'
          by_contra hge
          push_neg at hge
          exact hz1 (hQj q' hq' y hytj z (le_of_lt hzy') hge)
        have h0j : 0 < j := by
          cases j with
          | zero => simp at hytj
          | succ _ => omega
        have hymem : y ∈ openerLabels w := List.mem_of_mem_take hytj
        have hyn : y ≤ n := (hbounds hymem).2
        have hpjmem : pj ∈ openerLabels w := SW.getD_mem hjlen
        have hpj1 : 1 ≤ pj := (hbounds hpjmem).1
        have hh1 : 1 ≤ pj + 1 := by omega
        have hhn : pj + 1 ≤ n := by omega
        have hhp : pj + 1 ∈ openerLabels w := by
          apply hp.mem_iff.mpr
          unfold idPerm
          rw [List.mem_range'_1]
          omega
        obtain ⟨m, hm, hpm⟩ := List.mem_iff_getElem.mp hhp
        have hpmD : (openerLabels w).getD m 0 = pj + 1 := by
          rw [List.getD_eq_getElem _ _ hm]; exact hpm
        have hmj : j < m := by
          rcases Nat.lt_trichotomy m j with hlt | heq | hgt
          · have hmem : pj + 1 ∈ (openerLabels w).take j :=
              hpmD ▸ SW.getD_mem_take hlt hm
            have := hall _ hmem
            omega
          · rw [heq] at hpmD
            rw [← hpj] at hpmD
            omega
          · exact hgt
        have h0len : 0 < (openerLabels w).length := by omega
        set a := (openerLabels w).getD 0 0 with ha
        have hamem' : a ∈ (openerLabels w).take j := SW.getD_mem_take h0j h0len
        have hza : z < a := hall a hamem'
        have hamem : a ∈ openerLabels w := SW.getD_mem h0len
        have ha1 : 1 ≤ a := (hbounds hamem).1
        have han : a ≤ n := (hbounds hamem).2
        have hca : w.count a = 2 := hcount ha1 han
        have hcc : w.count pj = 2 := hcount hpj1 (by omega)
        have hch : w.count (pj + 1) = 2 := hcount hh1 hhn
        have hf1 : w.idxOf a < w.idxOf pj := by
          have h := SW.openerLabels_idxOf_lt h0j hjlen
          rwa [← ha, ← hpj] at h
        have hf2 : w.idxOf pj < w.idxOf (pj + 1) := by
          have h := SW.openerLabels_idxOf_lt hmj hm
          rwa [← hpj, hpmD] at h
        have hs1 : SW.sndIdx w a < SW.sndIdx w pj :=
          SW.sndIdx_lt_sndIdx hnn (by omega) (by omega) (by omega) hf1
        have hs2 : SW.sndIdx w pj < SW.sndIdx w (pj + 1) :=
          SW.sndIdx_lt_sndIdx hnn (by omega) (by omega) (by omega) hf2
        obtain ⟨hsl, hsv⟩ := SW.sndIdx_spec (w := w) (v := pj + 1) (by omega)
        obtain ⟨hsla, hsva⟩ := SW.sndIdx_spec (w := w) (v := a) (by omega)
        obtain ⟨hslc, hsvc⟩ := SW.sndIdx_spec (w := w) (v := pj) (by omega)
        refine hav2 (SW.contains_3312_of (SW.idxOf_lt_sndIdx w a) hs1 hs2 hsl
          ?_ ?_ ?_)
        · rw [SW.getD_idxOf (hmemw ha1 han), hsva]
        · rw [hsvc, hsv]; omega
        · rw [hsv, SW.getD_idxOf (hmemw ha1 han)]; omega
      · -- x = y = p_j forces z = p_j: contradiction
        subst hxeq
        subst hyeq
        exact hz2 (by omega)

end ElizaldeLuo
