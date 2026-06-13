/-
# Sanity instances: the definitions produce the right counts for n ≤ 4

Ground truth (DEFINITIONS.md §4/§6, verified by three independent brute-force
implementations): the avoider counts for n = 1, 2, 3, 4 are **1, 4, 16, 58**
(= 3^n - 3·2^(n-1) + 1), and the nonnesting totals are 1, 4, 30, 336 (= n!·Catalan n).

Two layers of checking, both native-free (no `native_decide` anywhere):

* `example … := by decide` — kernel-checked instances. `avoiders` is kernel-feasible
  for n ≤ 2 (n = 3 takes too long in the kernel; see scripts/SlowSanity.lean);
  `validPairs` and `W` are kernel-feasible through n = 4 (and `W 5`).
* `#guard` — build-time checks evaluated by the (non-native) interpreter through the
  very same `Decidable` instances. These cover the real definitions at n = 3 and the
  whole encode/decode pipeline (`openerShape`/`signWordOf`/`phi`/`psi`/`wd`/
  `permOfSigns`) at n = 3, 4 against the language `W`, including the worked examples
  of bijection.md §10. At n = 4 the word-level filter uses `avoiderFast` (the
  quadruple form of DEFINITIONS.md §2's concrete bullets), which is itself
  `#guard`-checked pointwise against the real `IsAvoider` for every word with n ≤ 3,
  and one-sidedly (all 58 survivors) against `IsAvoider` at n = 4.

If any definition in this development drifts from DEFINITIONS.md, these checks are
expected to fail the build.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.WLang
import ElizaldeLuo.Fifo
import ElizaldeLuo.SignWord
import ElizaldeLuo.TheoremA
import ElizaldeLuo.Shapes
import ElizaldeLuo.Bijection

namespace ElizaldeLuo

/-! ## Kernel-checked sanity instances (`decide`) -/

-- The avoider counts, kernel-checked (the n ≤ 4 instances 1, 4, 16, 58; kernel
-- reduction is feasible for n ≤ 2 — n = 3, 4 are covered by the `#guard`s below
-- and by scripts/SlowSanity.lean).
example : (avoiders 1).card = 1 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 200000 in
example : (avoiders 2).card = 4 := by decide

-- The middle object of the chain: |validPairs n| = 1, 4, 16, 58.
example : (validPairs 1).card = 1 := by decide

set_option maxHeartbeats 1000000 in
example : (validPairs 2).card = 4 := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
example : (validPairs 3).card = 16 := by decide

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 400000 in
example : (validPairs 4).card = 58 := by decide

-- The right end of the chain: |W n| = 1, 4, 16, 58, 196.
example : (W 1).card = 1 := by decide
example : (W 2).card = 4 := by decide
example : (W 3).card = 16 := by decide

set_option maxHeartbeats 1000000 in
example : (W 4).card = 58 := by decide

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
example : (W 5).card = 196 := by decide

/-! ## A fast clean-room enumerator and avoider check (for `#guard`s at n = 4)

`msetPerms` enumerates the distinct permutations of a multiset directly (no
quadratic dedup of a factorial-size list); `avoiderFast` checks avoidance via the
concrete quadruple bullets of DEFINITIONS.md §2. Both are cross-checked against the
real definitions below. -/

def msetPermsAux : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | fuel + 1, l =>
      if l.isEmpty then [[]]
      else l.dedup.flatMap fun v => (msetPermsAux fuel (l.erase v)).map (v :: ·)

/-- All distinct permutations of the multiset `l` (fuel-recursive enumerator). -/
def msetPerms (l : List ℕ) : List (List ℕ) := msetPermsAux l.length l

/-- DEFINITIONS.md §2: "w contains 1132 iff there are positions i<j<k<l and values
a<b<c with w_i=w_j=a, w_k=c, w_l=b" — as a boolean quadruple search. -/
def contains1132F (w : List ℕ) : Bool :=
  decide (∃ i j k l : Fin w.length, i < j ∧ j < k ∧ k < l ∧
    w.get i = w.get j ∧ w.get i < w.get l ∧ w.get l < w.get k)

/-- DEFINITIONS.md §2: "w contains 3312 iff there are positions i<j<k<l and values
a<b<c with w_i=w_j=c, w_k=a, w_l=b". -/
def contains3312F (w : List ℕ) : Bool :=
  decide (∃ i j k l : Fin w.length, i < j ∧ j < k ∧ k < l ∧
    w.get i = w.get j ∧ w.get k < w.get l ∧ w.get l < w.get i)

/-- 1221 occurrence: values u<v with w_i=w_l=u, w_j=w_k=v. -/
def contains1221F (w : List ℕ) : Bool :=
  decide (∃ i j k l : Fin w.length, i < j ∧ j < k ∧ k < l ∧
    w.get i = w.get l ∧ w.get j = w.get k ∧ w.get i < w.get j)

/-- 2112 occurrence: values u>v with w_i=w_l=u, w_j=w_k=v. -/
def contains2112F (w : List ℕ) : Bool :=
  decide (∃ i j k l : Fin w.length, i < j ∧ j < k ∧ k < l ∧
    w.get i = w.get l ∧ w.get j = w.get k ∧ w.get j < w.get i)

/-- Fast avoider check (only sound for multiset permutations, where the quadruple
forms above coincide with pattern containment — cross-checked below). -/
def avoiderFast (n : ℕ) (w : List ℕ) : Bool :=
  decide (IsMultisetPerm n w) && !contains1221F w && !contains2112F w &&
    !contains1132F w && !contains3312F w

/-- Encoding of an avoider as a (shape, sign word) pair (Lemma 0 + Fact 3.1). -/
def encodePair (w : List ℕ) : List Bool × List Bool :=
  (openerShape w, signWordOf (openerLabels w))

/-- Decoding of a ternary string to a word (Ψ then Fact 3.1 then Lemma 0). -/
def decodeWord (n : ℕ) (σ : List ABC) : List ℕ :=
  wd (psi n σ).1 (permOfSigns (psi n σ).2)

/-! ## Interpreted (`#guard`, native-free) sanity checks -/

-- The enumerator agrees with the real `words` Finset at n ≤ 3, and is duplicate-free
-- with the right totals at n = 4 (8!/2^4 = 2520).
#guard decide ((msetPerms (baseWord 2)).toFinset = words 2)
#guard decide ((msetPerms (baseWord 3)).toFinset = words 3)
#guard (msetPerms (baseWord 4)).length == 2520
#guard (msetPerms (baseWord 4)).dedup.length == 2520

-- Real-definition avoider counts (the n ≤ 3 instances), interpreted.
#guard ((msetPerms (baseWord 1)).filter fun w => decide (IsAvoider 1 w)).length == 1
#guard ((msetPerms (baseWord 2)).filter fun w => decide (IsAvoider 2 w)).length == 4
#guard ((msetPerms (baseWord 3)).filter fun w => decide (IsAvoider 3 w)).length == 16

-- The fast check agrees with the real definition pointwise for every word, n ≤ 3.
#guard (msetPerms (baseWord 2)).all fun w => avoiderFast 2 w == decide (IsAvoider 2 w)
#guard (msetPerms (baseWord 3)).all fun w => avoiderFast 3 w == decide (IsAvoider 3 w)

-- n = 4: count 58 via the cross-checked fast form; every survivor also satisfies
-- the real `IsAvoider` (one-sided real-definition check; the two-sided one is in
-- scripts/SlowSanity.lean).
#guard ((msetPerms (baseWord 4)).filter (avoiderFast 4)).length == 58
#guard ((msetPerms (baseWord 4)).filter (avoiderFast 4)).all fun w =>
  decide (IsAvoider 4 w)

-- Nonnesting totals are n!·Catalan(n) = 1, 4, 30, 336 (DEFINITIONS.md §3).
#guard ((msetPerms (baseWord 3)).filter fun w => decide (Nonnesting w)).length == 30
#guard ((msetPerms (baseWord 4)).filter fun w =>
  !contains1221F w && !contains2112F w).length == 336

-- Chain step 1 data: encoding the avoiders gives exactly `validPairs` (real
-- definitions at n = 3; fast filter at n = 4).
#guard decide ((avoiders 3).image encodePair = validPairs 3)
#guard decide ((((msetPerms (baseWord 4)).filter (avoiderFast 4)).map
  encodePair).toFinset = validPairs 4)

-- Chain step 2 data: Φ maps `validPairs` onto `W`, with Ψ a two-sided inverse.
#guard decide ((validPairs 3).image (fun q => phi 3 q.1 q.2) = W 3)
#guard decide ((validPairs 4).image (fun q => phi 4 q.1 q.2) = W 4)
#guard decide (∀ q ∈ validPairs 4, psi 4 (phi 4 q.1 q.2) = q)
#guard decide (∀ σ ∈ W 4, psi 4 σ ∈ validPairs 4)
#guard decide (∀ σ ∈ W 4, phi 4 (psi 4 σ).1 (psi 4 σ).2 = σ)

-- End-to-end: decoding W gives exactly the avoiders (real at n = 3, fast at n = 4).
#guard decide ((W 3).image (decodeWord 3) = avoiders 3)
#guard decide ((W 4).image (decodeWord 4) =
  ((msetPerms (baseWord 4)).filter (avoiderFast 4)).toFinset)

-- Fact 3.1 data: signWordOf/permOfSigns are mutually inverse, n = 4.
#guard decide (∀ ε ∈ strings Bool 3, signWordOf (permOfSigns ε) = ε)
#guard decide (∀ ε ∈ strings Bool 3,
  (permOfSigns ε).Perm (idPerm 4) ∧ IsPrefixInterval (permOfSigns ε))
#guard decide (∀ p ∈ permsOf 4, IsPrefixInterval p → permOfSigns (signWordOf p) = p)

-- A plain-list enumerator of `{L,H}^n` for the parameter sweeps below (nested
-- Finset-bounded quantifiers defeat `Decidable` instance synthesis, so these
-- guards iterate over lists with `decide` only at the leaves).
def stringsL : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (stringsL n).flatMap fun w => [true :: w, false :: w]

#guard decide ((stringsL 3).toFinset = strings Bool 3)
#guard decide ((stringsL 4).toFinset = strings Bool 4)

-- Lemma 5 statement sanity (n = 5): the parameterized shapes are Dyck words.
#guard (List.range' 1 4).all fun a => (stringsL (5 - a - 1)).all fun δ =>
  decide (IsDyck 5 (shapeI a δ))
#guard (List.range' 2 3).all fun a => (List.range' 1 (a - 1)).all fun i =>
  (stringsL (5 - a - 1)).all fun δ => decide (IsDyck 5 (shapeII a i δ))
#guard decide (IsDyck 5 (shapeS 5))

-- Lemmas 4+5 statement sanity (n = 5): every Dyck shape carrying a valid sign word
-- is of one of the three admissible forms (as stated in `admissible_classification`).
#guard decide (∀ s ∈ dycks 5, (∃ ε ∈ strings Bool 4, ValidSign 5 s ε) →
  (s = shapeS 5 ∨
    (∃ a ∈ Finset.Icc 1 4, ∃ δ ∈ strings Bool (5 - a - 1), s = shapeI a δ) ∨
    (∃ a ∈ Finset.Icc 2 4, ∃ i ∈ Finset.Icc 1 (a - 1),
      ∃ δ ∈ strings Bool (5 - a - 1), s = shapeII a i δ)))

-- Lemma 6 statement sanity (n = 5): the stated local forms of validity are
-- extensionally correct (catches index off-by-ones in the iff statements).
#guard (List.range' 1 4).all fun a => (stringsL (5 - a - 1)).all fun δ =>
  (stringsL 4).all fun ε =>
    decide (ValidSign 5 (shapeI a δ) ε ↔ TailConstraint a δ ε)
#guard (List.range' 2 3).all fun a => (List.range' 1 (a - 1)).all fun i =>
  (stringsL (5 - a - 1)).all fun δ => (stringsL 4).all fun ε =>
    decide (ValidSign 5 (shapeII a i δ) ε ↔
      ((∀ k < a - i, ε.getD (i - 1 + k) false = ! ε.getD (a - 1) false) ∧
        TailConstraint a δ ε))
#guard (stringsL 4).all fun ε => decide (ValidSign 5 (shapeS 5) ε)

-- Worked examples from bijection.md §10 (n = 3 table rows and the n = 6 example).
#guard decide (decodeWord 3 [ABC.A, ABC.A, ABC.A] = [3, 2, 1, 3, 2, 1])
#guard decide (decodeWord 3 [ABC.A, ABC.C, ABC.B] = [2, 2, 1, 1, 3, 3])
#guard decide (decodeWord 3 [ABC.C, ABC.C, ABC.B] = [2, 1, 2, 3, 1, 3])
#guard decide (decodeWord 3 [ABC.B, ABC.B, ABC.C] = [1, 2, 1, 2, 3, 3])
#guard decide
  (phi 6 (openerShape [2, 3, 4, 5, 2, 3, 1, 4, 5, 6, 1, 6])
      (signWordOf (openerLabels [2, 3, 4, 5, 2, 3, 1, 4, 5, 6, 1, 6])) =
    [ABC.C, ABC.B, ABC.C, ABC.C, ABC.A, ABC.C])
#guard decide (decodeWord 6 [ABC.C, ABC.B, ABC.C, ABC.C, ABC.A, ABC.C] =
  [2, 3, 4, 5, 2, 3, 1, 4, 5, 6, 1, 6])

end ElizaldeLuo
