/-
# Lemma 1 (positional criteria) and Theorem A (structural characterization)

bijection.md §2 and §4. Theorem A: a pair `(s,p)` is an avoider iff
1. `p` is prefix-interval, with sign word `ε`; and
2. for every late arc `J` (i.e. `o_J > q_1`) and every `K ∈ open(o_J)`
   (i.e. `o_K < o_J < q_K`): `ε_K ≠ ε_J`.

By Lemma 0 + Theorem A + Fact 3.1, avoiders biject with the pairs `(s, ε)` where `s`
is a Dyck word of semilength `n` and `ε ∈ {L,H}^(n-1)` is *valid for* `s`
(`validPairs n` below); this file's headline `card_avoiders_eq_card_validPairs` is
the first third of the proof chain.

SORRY PACKAGE "theoremA": COMPLETE — all 4 statements proven (no `sorry` left).
Position-level infrastructure lives in `Helpers_theoremA.lean` (namespace `TA`).
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.Fifo
import ElizaldeLuo.SignWord
import ElizaldeLuo.Helpers_theoremA

namespace ElizaldeLuo

/-! ## Lemma 1: positional criteria for 1132/3312 (concrete unfolding of containment)

DEFINITIONS.md §2 spells the two patterns out concretely: "since every value occurs
exactly twice in a permutation of $[n]_2$:
- $w$ **contains 1132** iff there are positions $i<j<k<l$ and values $a<b<c$ with
  $w_i=w_j=a$, $w_k=c$, $w_l=b$.
- $w$ **contains 3312** iff there are positions $i<j<k<l$ and values $a<b<c$ with
  $w_i=w_j=c$, $w_k=a$, $w_l=b$." -/

set_option linter.unusedVariables false in
/-- Lemma 1 / DEFINITIONS.md §2 bullet 1, with `a := w_i = w_j`, `b := w_l`,
`c := w_k`, so `a < b < c` reads `w_i < w_l < w_k`. Valid for any word using each
letter at most twice (we only apply it to multiset permutations).
(Sorry package "theoremA".) -/
theorem contains_1132_iff {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w) :
    Contains w pat1132 ↔
      ∃ i j k l : Fin w.length, i < j ∧ j < k ∧ k < l ∧
        w.get i = w.get j ∧ w.get i < w.get l ∧ w.get l < w.get k := by
  constructor
  · rintro ⟨f, hmono, horder, heq⟩
    refine ⟨f ⟨0, by decide⟩, f ⟨1, by decide⟩, f ⟨2, by decide⟩, f ⟨3, by decide⟩,
      hmono _ _ (by decide), hmono _ _ (by decide), hmono _ _ (by decide),
      ?_, ?_, ?_⟩
    · exact (heq _ _).mpr (by decide)
    · exact (horder _ _).mpr (by decide)
    · exact (horder _ _).mpr (by decide)
  · rintro ⟨i, j, k, l, hij, hjk, hkl, h1, h2, h3⟩
    have e : ∀ m : Fin w.length, w.getD (m : ℕ) 0 = w.get m := fun m => by
      rw [List.getD_eq_getElem _ _ m.isLt, List.get_eq_getElem]
    exact SW.contains_1132_of (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
      (Fin.lt_def.mp hkl) l.isLt (by rw [e i, e j]; exact h1)
      (by rw [e i, e l]; exact h2) (by rw [e l, e k]; exact h3)

set_option linter.unusedVariables false in
/-- Lemma 1 / DEFINITIONS.md §2 bullet 2, with `c := w_i = w_j`, `a := w_k`,
`b := w_l`, so `a < b < c` reads `w_k < w_l ∧ w_l < w_i`.
(Sorry package "theoremA".) -/
theorem contains_3312_iff {n : ℕ} {w : List ℕ} (hw : IsMultisetPerm n w) :
    Contains w pat3312 ↔
      ∃ i j k l : Fin w.length, i < j ∧ j < k ∧ k < l ∧
        w.get i = w.get j ∧ w.get k < w.get l ∧ w.get l < w.get i := by
  constructor
  · rintro ⟨f, hmono, horder, heq⟩
    refine ⟨f ⟨0, by decide⟩, f ⟨1, by decide⟩, f ⟨2, by decide⟩, f ⟨3, by decide⟩,
      hmono _ _ (by decide), hmono _ _ (by decide), hmono _ _ (by decide),
      ?_, ?_, ?_⟩
    · exact (heq _ _).mpr (by decide)
    · exact (horder _ _).mpr (by decide)
    · exact (horder _ _).mpr (by decide)
  · rintro ⟨i, j, k, l, hij, hjk, hkl, h1, h2, h3⟩
    have e : ∀ m : Fin w.length, w.getD (m : ℕ) 0 = w.get m := fun m => by
      rw [List.getD_eq_getElem _ _ m.isLt, List.get_eq_getElem]
    exact SW.contains_3312_of (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
      (Fin.lt_def.mp hkl) l.isLt (by rw [e i, e j]; exact h1)
      (by rw [e k, e l]; exact h2) (by rw [e l, e i]; exact h3)

/-! ## Validity of a sign word for a shape (Theorem A condition 2) -/

/-- Condition 2 of Theorem A: `ε` is **valid for** `s` if for every late arc `J`
(`o_J > q_1`) and every `K ∈ open(o_J)` (`o_K < o_J < q_K`): `ε_K ≠ ε_J`.

0-based arcs `J, K ∈ {0,…,n-1}`; the sign of arc `j ≥ 1` is `ε.getD (j-1) false`;
`qPos s 0` is the draft's `q_1`. For a genuine Dyck word the hypotheses force
`1 ≤ K < J` (Observation 4.1: `K = 0` cannot be open at the opener of a late arc,
and a late arc cannot be arc `0`), so the junk index `0 - 1 = 0` is never hit. -/
def ValidSign (n : ℕ) (s ε : List Bool) : Prop :=
  ∀ J < n, ∀ K < n,
    qPos s 0 < oPos s J →
    oPos s K < oPos s J → oPos s J < qPos s K →
    ε.getD (K - 1) false ≠ ε.getD (J - 1) false

instance (n : ℕ) (s ε : List Bool) : Decidable (ValidSign n s ε) := by
  unfold ValidSign; infer_instance

/-- The middle object of the proof chain: pairs `(s, ε)` of a Dyck word of
semilength `n` and a sign word valid for `s` (bijection.md §4, final Definition):
"`ε ∈ {L,H}^(n-1)` (indexed 2,…,n) is **valid for** `s` if condition 2 of Theorem A
holds." -/
def validPairs (n : ℕ) : Finset (List Bool × List Bool) :=
  ((dycks n) ×ˢ (strings Bool (n - 1))).filter fun q => ValidSign n q.1 q.2

/-- **Theorem A.** "A pair `(s,p)` is an avoider if and only if (1) `p` is
prefix-interval, with sign word `ε`; and (2) for every late arc `J` and every
`K ∈ open(o_J)`: `ε_K ≠ ε_J`." (Sorry package "theoremA".) -/
theorem theoremA {n : ℕ} {s : List Bool} {p : List ℕ}
    (hs : IsDyck n s) (hp : p.Perm (idPerm n)) :
    IsAvoider n (wd s p) ↔
      IsPrefixInterval p ∧ ValidSign n s (signWordOf p) := by
  have hmp : IsMultisetPerm n (wd s p) := isMultisetPerm_wd hs hp
  have hnn : Nonnesting (wd s p) := nonnesting_wd hs hp
  have hshape : openerShape (wd s p) = s := openerShape_wd hs hp
  have hlabels : openerLabels (wd s p) = p := openerLabels_wd hs hp
  have hplen : p.length = n := by simpa [idPerm] using hp.length_eq
  have hpnd : p.Nodup := (List.Perm.nodup_iff hp).mpr (SW.nodup_idPerm n)
  have hwlen : (wd s p).length = 2 * n := by
    rw [List.Perm.length_eq hmp, length_baseWord]
  have hs' : IsDyck n s := hs
  obtain ⟨hslen, hstrue, hspre⟩ := hs
  have hsfalse : s.count false = n := by
    have := TA.count_true_add_count_false s
    omega
  -- values at opener/closer positions (Helpers_theoremA, transported along
  -- `openerShape (wd s p) = s`, `openerLabels (wd s p) = p`)
  have hvo : ∀ {A : ℕ}, A < n → (wd s p).getD (oPos s A) 0 = p.getD A 0 := by
    intro A hA
    have h := TA.getD_oPos hmp hnn hA
    rwa [hshape, hlabels] at h
  have hvq : ∀ {A : ℕ}, A < n → (wd s p).getD (qPos s A) 0 = p.getD A 0 := by
    intro A hA
    have h := TA.getD_qPos hmp hnn hA
    rwa [hshape, hlabels] at h
  constructor
  · -- (⇒): bijection.md §4, first half
    intro hav
    have hav1 : Avoids (wd s p) pat1132 := hav.2.2.1
    have hav2 : Avoids (wd s p) pat3312 := hav.2.2.2
    have hpi : IsPrefixInterval p := by
      have h := labels_prefixInterval_of_avoider hav
      rwa [hlabels] at h
    refine ⟨hpi, ?_⟩
    intro J hJ K hK hlate hopen1 hopen2 heqs
    have hKJ : K < J := (TA.oPos_lt_oPos_iff (by omega) (by omega)).mp hopen1
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with rfl | h
      · omega
      · exact h
    -- the four positions o_1 < q_1 < o_J < q_K (1-based: arcs 1, J+1, K+1)
    have hij : oPos s 0 < qPos s 0 := TA.oPos_lt_qPos_self hs' (by omega)
    have hl : qPos s K < (wd s p).length := by
      rw [hwlen, ← hslen]
      exact TA.qPos_lt_length (by omega)
    have hv0o := hvo (show 0 < n by omega)
    have hv0q := hvq (show 0 < n by omega)
    have hvJ := hvo hJ
    have hvK := hvq hK
    cases hbJ : (signWordOf p).getD (J - 1) false with
    | true =>
      -- both signs H: p_1 < p_K < p_J gives a 1132 at (o_1, q_1, o_J, q_K)
      have hbK : (signWordOf p).getD (K - 1) false = true := by rw [heqs, hbJ]
      have h0K : p.getD 0 0 < p.getD K 0 :=
        (comparison_rule hp hpi (by omega) (by omega)).mpr hbK
      have hKJv : p.getD K 0 < p.getD J 0 :=
        (comparison_rule hp hpi hKJ (by omega)).mpr hbJ
      exact hav1 (SW.contains_1132_of hij hlate hopen2 hl
        (by rw [hv0o, hv0q]) (by rw [hv0o, hvK]; exact h0K)
        (by rw [hvK, hvJ]; exact hKJv))
    | false =>
      -- both signs L: p_J < p_K < p_1 gives a 3312 at the same positions
      have hbK : (signWordOf p).getD (K - 1) false = false := by rw [heqs, hbJ]
      have h0K : p.getD K 0 < p.getD 0 0 := by
        have hne := SW.getD_ne_of_nodup hpnd (show 0 < p.length by omega)
          (show K < p.length by omega) (by omega)
        have hnotlt : ¬ p.getD 0 0 < p.getD K 0 := by
          intro h
          have hc := (comparison_rule hp hpi (show 0 < K by omega)
            (show K < p.length by omega)).mp h
          rw [hbK] at hc
          exact Bool.noConfusion hc
        omega
      have hJK : p.getD J 0 < p.getD K 0 := by
        have hne := SW.getD_ne_of_nodup hpnd (show K < p.length by omega)
          (show J < p.length by omega) (by omega)
        have hnotlt : ¬ p.getD K 0 < p.getD J 0 := by
          intro h
          have hc := (comparison_rule hp hpi hKJ (show J < p.length by omega)).mp h
          rw [hbJ] at hc
          exact Bool.noConfusion hc
        omega
      exact hav2 (SW.contains_3312_of hij hlate hopen2 hl
        (by rw [hv0o, hv0q]) (by rw [hvJ, hvK]; exact hJK)
        (by rw [hvK, hv0o]; exact h0K))
  · -- (⇐): bijection.md §4, second half
    rintro ⟨hpi, hvs⟩
    -- shared spatial analysis of an occurrence: positions i < j with equal value
    -- pin the arc C (so j = q_C); positions k, l > j get arcs A, B > C.
    have spatial : ∀ (i j k l : ℕ), i < j → j < k → k < l →
        l < (wd s p).length →
        (wd s p).getD i 0 = (wd s p).getD j 0 →
        ∃ C A B : ℕ, C < n ∧ A < n ∧ B < n ∧ C < A ∧ C < B ∧
          (wd s p).getD i 0 = p.getD C 0 ∧
          (wd s p).getD k 0 = p.getD A 0 ∧
          (wd s p).getD l 0 = p.getD B 0 ∧
          (k = oPos s A ∨ k = qPos s A) ∧ (l = oPos s B ∨ l = qPos s B) ∧
          qPos s C < k := by
      intro i j k l hij hjk hkl hl heqv
      have hkw : k < (wd s p).length := by omega
      have hiw : i < (wd s p).length := by omega
      have hjw : j < (wd s p).length := by omega
      have hvw : (wd s p).getD i 0 ∈ wd s p := SW.getD_mem hiw
      have hcnt : (wd s p).count ((wd s p).getD i 0) = 2 :=
        FifoH.count_eq_two_of_perm_baseWord hmp hvw
      obtain ⟨hi_eq, hj_eq⟩ := TA.two_positions hcnt hij hjw rfl heqv.symm
      have hvp : (wd s p).getD i 0 ∈ p := by
        have h2 := (List.Perm.mem_iff hmp).mp hvw
        have h3 := mem_baseWord.mp h2
        refine (List.Perm.mem_iff hp).mpr ?_
        simp only [idPerm, List.mem_range'_1]
        omega
      have hC : p.idxOf ((wd s p).getD i 0) < n := by
        rw [← hplen]
        exact List.idxOf_lt_length_of_mem hvp
      have hpC : p.getD (p.idxOf ((wd s p).getD i 0)) 0 = (wd s p).getD i 0 :=
        SW.getD_idxOf hvp
      have hsnd : SW.sndIdx (wd s p) ((wd s p).getD i 0)
          = qPos s (p.idxOf ((wd s p).getD i 0)) := by
        have h := TA.snd_eq_qPos hmp hnn hC
        rwa [hshape, hlabels, hpC] at h
      have hqCk : qPos s (p.idxOf ((wd s p).getD i 0)) < k := by
        rw [← hsnd, ← hj_eq]
        exact hjk
      have harck := TA.arc_of_position hmp hnn hkw
      rw [hshape, hlabels] at harck
      obtain ⟨A, hA, hkA, hvA⟩ := harck
      have harcl := TA.arc_of_position hmp hnn (show l < (wd s p).length from hl)
      rw [hshape, hlabels] at harcl
      obtain ⟨B, hB, hlB, hvB⟩ := harcl
      have hCA : p.idxOf ((wd s p).getD i 0) < A := by
        by_contra hle
        have hle' : A ≤ p.idxOf ((wd s p).getD i 0) := by omega
        have hq : qPos s A ≤ qPos s (p.idxOf ((wd s p).getD i 0)) :=
          TA.qPos_le_qPos hle' (by omega)
        have ho : oPos s A < qPos s A := TA.oPos_lt_qPos_self hs' hA
        rcases hkA with rfl | rfl
        · omega
        · omega
      have hCB : p.idxOf ((wd s p).getD i 0) < B := by
        by_contra hle
        have hle' : B ≤ p.idxOf ((wd s p).getD i 0) := by omega
        have hq : qPos s B ≤ qPos s (p.idxOf ((wd s p).getD i 0)) :=
          TA.qPos_le_qPos hle' (by omega)
        have ho : oPos s B < qPos s B := TA.oPos_lt_qPos_self hs' hB
        rcases hlB with rfl | rfl
        · omega
        · omega
      exact ⟨p.idxOf ((wd s p).getD i 0), A, B, hC, hA, hB, hCA, hCB, hpC.symm,
        hvA, hvB, hkA, hlB, hqCk⟩
    -- shared position analysis: from B < A and k < l, the only consistent
    -- placement is k = o_A, l = q_B (so B ∈ open(o_A))
    have analysis : ∀ {A B k l : ℕ}, A < n → B < n → B < A → k < l →
        (k = oPos s A ∨ k = qPos s A) → (l = oPos s B ∨ l = qPos s B) →
        k = oPos s A ∧ l = qPos s B := by
      intro A B k l hA hB hBA hkl hkA hlB
      have hoo : oPos s B < oPos s A :=
        (TA.oPos_lt_oPos_iff (by omega) (by omega)).mpr hBA
      have hqq : qPos s B < qPos s A :=
        (TA.qPos_lt_qPos_iff (by omega) (by omega)).mpr hBA
      have hoqA : oPos s A < qPos s A := TA.oPos_lt_qPos_self hs' hA
      have hoqB : oPos s B < qPos s B := TA.oPos_lt_qPos_self hs' hB
      rcases hkA with rfl | rfl <;> rcases hlB with rfl | rfl
      · omega
      · exact ⟨rfl, rfl⟩
      · omega
      · omega
    refine ⟨hmp, hnn, ?_, ?_⟩
    · -- avoids 1132
      intro hcon
      obtain ⟨i, j, k, l, hij, hjk, hkl, h1, h2, h3⟩ :=
        (contains_1132_iff hmp).mp hcon
      have e : ∀ m : Fin (wd s p).length,
          (wd s p).getD (m : ℕ) 0 = (wd s p).get m := fun m => by
        rw [List.getD_eq_getElem _ _ m.isLt, List.get_eq_getElem]
      obtain ⟨C, A, B, hC, hA, hB, hCA, hCB, hvi, hvk, hvl, hkA, hlB, hqCk⟩ :=
        spatial i j k l (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
          (Fin.lt_def.mp hkl) l.isLt (by rw [e i, e j]; exact h1)
      -- value chain p_C < p_B < p_A
      have hCBv : p.getD C 0 < p.getD B 0 := by
        rw [← hvi, ← hvl, e i, e l]
        exact h2
      have hBAv : p.getD B 0 < p.getD A 0 := by
        rw [← hvl, ← hvk, e l, e k]
        exact h3
      have hεB : (signWordOf p).getD (B - 1) false = true :=
        (comparison_rule hp hpi hCB (by omega)).mp hCBv
      have hBA : B < A := by
        rcases Nat.lt_trichotomy A B with hAB | rfl | hBA
        · have hc : p.getD A 0 < p.getD B 0 :=
            (comparison_rule hp hpi hAB (by omega)).mpr hεB
          omega
        · omega
        · exact hBA
      have hεA : (signWordOf p).getD (A - 1) false = true :=
        (comparison_rule hp hpi hBA (by omega)).mp hBAv
      obtain ⟨hk_eq, hl_eq⟩ := analysis hA hB hBA (Fin.lt_def.mp hkl) hkA hlB
      have hlate : qPos s 0 < oPos s A := by
        have h0C : qPos s 0 ≤ qPos s C := TA.qPos_le_qPos (Nat.zero_le C) (by omega)
        omega
      have hopen1 : oPos s B < oPos s A :=
        (TA.oPos_lt_oPos_iff (by omega) (by omega)).mpr hBA
      have hopen2 : oPos s A < qPos s B := by
        have hkl' := Fin.lt_def.mp hkl
        omega
      exact hvs A hA B hB hlate hopen1 hopen2 (by rw [hεB, hεA])
    · -- avoids 3312
      intro hcon
      obtain ⟨i, j, k, l, hij, hjk, hkl, h1, h2, h3⟩ :=
        (contains_3312_iff hmp).mp hcon
      have e : ∀ m : Fin (wd s p).length,
          (wd s p).getD (m : ℕ) 0 = (wd s p).get m := fun m => by
        rw [List.getD_eq_getElem _ _ m.isLt, List.get_eq_getElem]
      obtain ⟨C, A, B, hC, hA, hB, hCA, hCB, hvi, hvk, hvl, hkA, hlB, hqCk⟩ :=
        spatial i j k l (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
          (Fin.lt_def.mp hkl) l.isLt (by rw [e i, e j]; exact h1)
      -- value chain p_A < p_B < p_C
      have hABv : p.getD A 0 < p.getD B 0 := by
        rw [← hvk, ← hvl, e k, e l]
        exact h2
      have hBCv : p.getD B 0 < p.getD C 0 := by
        rw [← hvl, ← hvi, e l, e i]
        exact h3
      have hεB : (signWordOf p).getD (B - 1) false = false := by
        have hnot : ¬ p.getD C 0 < p.getD B 0 := by omega
        cases hb : (signWordOf p).getD (B - 1) false with
        | false => rfl
        | true => exact absurd ((comparison_rule hp hpi hCB (by omega)).mpr hb) hnot
      have hBA : B < A := by
        rcases Nat.lt_trichotomy A B with hAB | rfl | hBA
        · have hc := (comparison_rule hp hpi hAB (by omega)).mp hABv
          rw [hεB] at hc
          exact Bool.noConfusion hc
        · omega
        · exact hBA
      have hεA : (signWordOf p).getD (A - 1) false = false := by
        have hnot : ¬ p.getD B 0 < p.getD A 0 := by omega
        cases hb : (signWordOf p).getD (A - 1) false with
        | false => rfl
        | true => exact absurd ((comparison_rule hp hpi hBA (by omega)).mpr hb) hnot
      obtain ⟨hk_eq, hl_eq⟩ := analysis hA hB hBA (Fin.lt_def.mp hkl) hkA hlB
      have hlate : qPos s 0 < oPos s A := by
        have h0C : qPos s 0 ≤ qPos s C := TA.qPos_le_qPos (Nat.zero_le C) (by omega)
        omega
      have hopen1 : oPos s B < oPos s A :=
        (TA.oPos_lt_oPos_iff (by omega) (by omega)).mpr hBA
      have hopen2 : oPos s A < qPos s B := by
        have hkl' := Fin.lt_def.mp hkl
        omega
      exact hvs A hA B hB hlate hopen1 hopen2 (by rw [hεB, hεA])

/-- **Chain step 1** (bijection.md §4, final Definition + display): by Lemma 0,
Theorem A and Fact 3.1, `w ↦ (openerShape w, signWordOf (openerLabels w))` is a
bijection from avoiders onto `validPairs n`, with inverse
`(s, ε) ↦ wd s (permOfSigns ε)`. (Sorry package "theoremA" — headline; expected
proof: `Finset.card_bij` with the Lemma-0 and Fact-3.1 lemmas.) -/
theorem card_avoiders_eq_card_validPairs (n : ℕ) :
    (avoiders n).card = (validPairs n).card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- n = 0: both sides are singletons ({[]} and {([], [])})
    decide
  · have hmemv : ∀ (s ε : List Bool),
        (s, ε) ∈ validPairs n ↔ IsDyck n s ∧ ε.length = n - 1 ∧ ValidSign n s ε := by
      intro s ε
      simp only [validPairs, dycks, Finset.mem_filter, Finset.mem_product,
        mem_strings]
      constructor
      · rintro ⟨⟨⟨-, hd⟩, hl⟩, hv⟩
        exact ⟨hd, hl, hv⟩
      · rintro ⟨hd, hl, hv⟩
        exact ⟨⟨⟨hd.1, hd⟩, hl⟩, hv⟩
    refine Finset.card_bij
      (fun w _ => (openerShape w, signWordOf (openerLabels w))) ?_ ?_ ?_
    · -- well-defined into validPairs
      intro w hw
      have hav : IsAvoider n w := mem_avoiders.mp hw
      have hd : IsDyck n (openerShape w) := openerShape_isDyck hav.1 hav.2.1
      have hp : (openerLabels w).Perm (idPerm n) := openerLabels_perm hav.1
      have hvs : ValidSign n (openerShape w) (signWordOf (openerLabels w)) := by
        have hwav : IsAvoider n (wd (openerShape w) (openerLabels w)) := by
          rw [wd_openerShape_openerLabels hav.1 hav.2.1]
          exact hav
        exact ((theoremA hd hp).mp hwav).2
      refine (hmemv _ _).mpr ⟨hd, ?_, hvs⟩
      rw [signWordOf_length, TA.labels_length hav.1]
    · -- injective (Lemma 0 uniqueness + Fact 3.1)
      intro w₁ hw₁ w₂ hw₂ heq
      have hav₁ : IsAvoider n w₁ := mem_avoiders.mp hw₁
      have hav₂ : IsAvoider n w₂ := mem_avoiders.mp hw₂
      have hsh : openerShape w₁ = openerShape w₂ := congrArg Prod.fst heq
      have hε : signWordOf (openerLabels w₁) = signWordOf (openerLabels w₂) :=
        congrArg Prod.snd heq
      have hlab : openerLabels w₁ = openerLabels w₂ := by
        rw [← permOfSigns_signWordOf hn (openerLabels_perm hav₁.1)
            (labels_prefixInterval_of_avoider hav₁),
          ← permOfSigns_signWordOf hn (openerLabels_perm hav₂.1)
            (labels_prefixInterval_of_avoider hav₂), hε]
      rw [← wd_openerShape_openerLabels hav₁.1 hav₁.2.1,
        ← wd_openerShape_openerLabels hav₂.1 hav₂.2.1, hsh, hlab]
    · -- surjective: (s, ε) ↦ wd s (permOfSigns ε)
      rintro ⟨s, ε⟩ hmem
      obtain ⟨hd, hεlen, hvs⟩ := (hmemv s ε).mp hmem
      have hperm : (permOfSigns ε).Perm (idPerm n) := by
        have h := permOfSigns_perm ε
        rwa [hεlen, Nat.sub_add_cancel hn] at h
      have hpi := isPrefixInterval_permOfSigns ε
      have hsw : signWordOf (permOfSigns ε) = ε := signWordOf_permOfSigns ε
      have hav : IsAvoider n (wd s (permOfSigns ε)) :=
        (theoremA hd hperm).mpr ⟨hpi, by rwa [hsw]⟩
      refine ⟨wd s (permOfSigns ε), mem_avoiders.mpr hav, ?_⟩
      show (openerShape (wd s (permOfSigns ε)),
        signWordOf (openerLabels (wd s (permOfSigns ε)))) = (s, ε)
      rw [openerShape_wd hd hperm, openerLabels_wd hd hperm, hsw]

end ElizaldeLuo
