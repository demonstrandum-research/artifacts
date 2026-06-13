/-
# Core definitions: multiset permutations, pattern containment, nonnesting, the avoider set

All conventions are pinned in `../../DEFINITIONS.md`, quoted verbatim from the published
paper (Elizalde–Luo, *Pattern avoidance in nonnesting permutations*, arXiv:2412.00336,
DMTCS 27:1 (2025), DOI 10.46298/dmtcs.14885). Verbatim quotes are reproduced in the
docstrings below; do NOT change these definitions without re-checking against
DEFINITIONS.md.

Encoding: a word is a `List ℕ` (1-based values 1..n, 0-based list positions).
This file is sorry-free: it contains only definitions, decidability instances,
and immediate membership lemmas.
-/
import Mathlib

namespace ElizaldeLuo

/-- All strings of length `n` over a finite alphabet `α`, as a `Finset (List α)`.
(Defined by structural recursion so that it reduces in the kernel — `decide` works.) -/
def strings (α : Type) [DecidableEq α] [Fintype α] : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun a : α => (strings α n).image (a :: ·)

theorem mem_strings {α : Type} [DecidableEq α] [Fintype α] :
    ∀ {n : ℕ} {l : List α}, l ∈ strings α n ↔ l.length = n
  | 0, l => by
    simp only [strings, Finset.mem_singleton, List.length_eq_zero_iff]
  | n + 1, l => by
    simp only [strings, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨a, w, hw, rfl⟩
      simp [mem_strings.mp hw]
    · intro hl
      cases l with
      | nil => simp at hl
      | cons a w =>
        exact ⟨a, w, mem_strings.mpr (by simpa using hl), rfl⟩

/-- The ground multiset as a canonical word: `baseWord n = [1,1,2,2,...,n,n]`.

DEFINITIONS.md §1 (verbatim from `src/formatted.tex` line 117):
"We denote by $\nn = \{1,1,2,2,\dots, n,n\}$ the multiset consisting of two copies of
each integer between $1$ and $n$." -/
def baseWord (n : ℕ) : List ℕ :=
  (List.range' 1 n).flatMap fun v => [v, v]

theorem mem_baseWord {n v : ℕ} : v ∈ baseWord n ↔ 1 ≤ v ∧ v ≤ n := by
  simp only [baseWord, List.mem_flatMap, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨u, hu, h | h⟩ <;> omega
  · intro h; exact ⟨v, by omega, Or.inl rfl⟩

theorem length_baseWord (n : ℕ) : (baseWord n).length = 2 * n := by
  suffices h : ∀ s m : ℕ, ((List.range' s m).flatMap fun v => [v, v]).length = 2 * m from
    h 1 n
  intro s m
  induction m generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [List.range'_succ, List.flatMap_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

/-- A *permutation of* `[n]₂`: a word of length `2n` over `{1,…,n}` using each letter
exactly twice, i.e. a list that is a permutation of `baseWord n`.

DEFINITIONS.md §1: "A *permutation of* $[n]_2$ is a word of length $2n$ over
$\{1,\dots,n\}$ using each letter exactly twice. **The count is over all such labeled
words — no quotient by relabeling is taken**." -/
def IsMultisetPerm (n : ℕ) (w : List ℕ) : Prop :=
  w.Perm (baseWord n)

instance (n : ℕ) (w : List ℕ) : Decidable (IsMultisetPerm n w) := by
  unfold IsMultisetPerm; infer_instance

/-- Equality-pattern containment, EXACTLY per DEFINITIONS.md §2 (verbatim from
`src/formatted.tex` lines 119-124):

"Given two words $\pi=\pi_1\pi_2\dots\pi_m$ and $\sigma=\sigma_1\sigma_2\dots\sigma_k$
over the positive integers $\bbN$, we say that $\pi$ *contains* the pattern $\sigma$ if
there exist indices $1\le i_1<i_2<\dots<i_k\le m$ such that the subsequence
$\pi_{i_1}\pi_{i_2}\dots\pi_{i_k}$ is in the same relative order as $\sigma$, that is,
- $\pi_{i_r}<\pi_{i_s}$ if and only if $\sigma_r<\sigma_s$, and
- $\pi_{i_r}=\pi_{i_s}$ if and only if $\sigma_r=\sigma_s$,

for all $r,s\in[k]$. This subsequence is called an *occurrence* of $\sigma$. If $\pi$
does not contain $\sigma$, we say that $\pi$ *avoids* the pattern $\sigma$."

Both conditions are **biconditional**: equal pattern letters must map to *equal* word
letters, and strictly ordered pattern letters to *strictly* ordered word letters.

Here `Contains w σ` means "`w` contains the pattern `σ`"; the indices are encoded as a
strictly increasing function `f : Fin σ.length → Fin w.length`. -/
def Contains (w σ : List ℕ) : Prop :=
  ∃ f : Fin σ.length → Fin w.length,
    (∀ r s : Fin σ.length, r < s → f r < f s) ∧
    (∀ r s : Fin σ.length, w.get (f r) < w.get (f s) ↔ σ.get r < σ.get s) ∧
    (∀ r s : Fin σ.length, w.get (f r) = w.get (f s) ↔ σ.get r = σ.get s)

instance (w σ : List ℕ) : Decidable (Contains w σ) := by
  unfold Contains; infer_instance

/-- `w` avoids the pattern `σ` (DEFINITIONS.md §2: "If $\pi$ does not contain $\sigma$,
we say that $\pi$ *avoids* the pattern $\sigma$."). -/
def Avoids (w σ : List ℕ) : Prop := ¬ Contains w σ

instance (w σ : List ℕ) : Decidable (Avoids w σ) := by
  unfold Avoids; infer_instance

/-- The pattern 1132 (as a word over positive integers). -/
def pat1132 : List ℕ := [1, 1, 3, 2]

/-- The pattern 3312. -/
def pat3312 : List ℕ := [3, 3, 1, 2]

/-- The pattern 1221. -/
def pat1221 : List ℕ := [1, 2, 2, 1]

/-- The pattern 2112. -/
def pat2112 : List ℕ := [2, 1, 1, 2]

/-- Nonnesting permutations, EXACTLY per DEFINITIONS.md §3 (verbatim from
`src/formatted.tex` line 135):

"With this perspective, it is natural to consider permutations of $\nn$ whose
corresponding matching is nonnesting, i.e., there are no two arcs $(i_1,i_4)$ and
$(i_2,i_3)$ where $i_1<i_2<i_3<i_4$. They can be defined as permutations of $\nn$ that
avoid the patterns $1221$ and $2112$. Following~\cite{elizalde_nonnesting}, we call
these *nonnesting permutations*, and we denote by $\cC_n$ the set of nonnesting
permutations of $\nn$."

I.e. nonnesting ⟺ no indices $i_1<i_2<i_3<i_4$ with
$w_{i_1}=w_{i_4}\neq w_{i_2}=w_{i_3}$. -/
def Nonnesting (w : List ℕ) : Prop :=
  Avoids w pat1221 ∧ Avoids w pat2112

instance (w : List ℕ) : Decidable (Nonnesting w) := by
  unfold Nonnesting; infer_instance

/-- An *avoider* (the objects being counted): a nonnesting permutation of `[n]₂`
avoiding both 1132 and 3312. -/
def IsAvoider (n : ℕ) (w : List ℕ) : Prop :=
  IsMultisetPerm n w ∧ Nonnesting w ∧ Avoids w pat1132 ∧ Avoids w pat3312

instance (n : ℕ) (w : List ℕ) : Decidable (IsAvoider n w) := by
  unfold IsAvoider; infer_instance

/-- The finite set of all permutations of `[n]₂` (raw labeled words; DEFINITIONS.md §5:
"Avoidance of $\{1132,3312\}$ depends on the actual values, so it is **not** invariant
under relabeling the letters; the count is over raw words.").

Enumerated as the length-`2n` strings over `{0,…,n}` that are multiset permutations
(rather than via `List.permutations`, which does not reduce in the kernel); the
characterization `mem_words` below is what matters. -/
def words (n : ℕ) : Finset (List ℕ) :=
  ((strings (Fin (n + 1)) (2 * n)).image fun l =>
    l.map (fun x : Fin (n + 1) => (x : ℕ))).filter (IsMultisetPerm n)

/-- The finite set of avoiders: nonnesting permutations of `[n]₂` avoiding 1132 and
3312. This is the set whose cardinality the conjecture computes. -/
def avoiders (n : ℕ) : Finset (List ℕ) :=
  (words n).filter fun w => Nonnesting w ∧ Avoids w pat1132 ∧ Avoids w pat3312

theorem mem_words {n : ℕ} {w : List ℕ} : w ∈ words n ↔ w.Perm (baseWord n) := by
  simp only [words, Finset.mem_filter, Finset.mem_image, IsMultisetPerm]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    have hbound : ∀ x : {v // v ∈ w}, (x : ℕ) < n + 1 := fun x =>
      Nat.lt_succ_of_le (mem_baseWord.mp (h.mem_iff.mp x.2)).2
    refine ⟨⟨w.attach.map (fun x => (⟨x.1, hbound x⟩ : Fin (n + 1))), ?_, ?_⟩, h⟩
    · exact mem_strings.mpr (by
        simp only [List.length_map, List.length_attach]
        rw [h.length_eq, length_baseWord])
    · rw [List.map_map]
      exact List.attach_map_subtype_val w

theorem mem_avoiders {n : ℕ} {w : List ℕ} : w ∈ avoiders n ↔ IsAvoider n w := by
  simp [avoiders, Finset.mem_filter, mem_words, IsAvoider, IsMultisetPerm]

/-- **The counting statement** (the Elizalde–Luo conjecture for `{1132, 3312}`).

DEFINITIONS.md §4 (verbatim, Table 4 row of `src/formatted.tex` line 1614):
"$\{1132,3312\}$ & $3^n-3\cdot2^{n-1}+1$ & A168583"
i.e. $\cc_n(1132,3312) = 3^n - 3\cdot 2^{n-1} + 1$ for $n\ge 1$.

(Stated over ℕ; for `n ≥ 1` we have `3^n ≥ 3·2^(n-1)`, so natural subtraction agrees
with the integer value.) -/
def ConjectureStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → (avoiders n).card = 3 ^ n - 3 * 2 ^ (n - 1) + 1

end ElizaldeLuo
