# READING-KIT — Elizalde–Luo {1132, 3312} conjecture (kernel-checked)

*A one-page, trust-nothing reader for the Lean 4 formalization. Every claim below is
either a verbatim quote of the source paper, a verbatim Lean statement, or the
verbatim output of a command you can rerun. Kit regenerated + all checks freshly
reproduced 2026-07-08 (Lean 4.30.0 / mathlib, on the build machine).*

---

## 1. The theorem, as stated in Lean

`ElizaldeLuo/Main.lean`:

```lean
/-- The number of nonnesting permutations of {1,1,2,2,…,n,n} avoiding the patterns
    1132 and 3312 equals 3^n − 3·2^(n−1) + 1 for every n ≥ 1. -/
theorem elizalde_luo_1132_3312 (n : ℕ) (hn : 1 ≤ n) :
    (avoiders n).card = 3 ^ n - 3 * 2 ^ (n - 1) + 1 := by
  rw [card_avoiders_eq_card_validPairs n, card_validPairs_eq_card_W n hn,
    card_W n hn]

/-- The counting statement of Defs.lean, discharged. -/
theorem conjecture_holds : ConjectureStatement :=
  elizalde_luo_1132_3312
```

where (`ElizaldeLuo/Defs.lean`)
`ConjectureStatement := ∀ n : ℕ, 1 ≤ n → (avoiders n).card = 3 ^ n - 3 * 2 ^ (n - 1) + 1`.

This proves the formula **for all n ≥ 1** — strictly stronger than the paper's
"checked for n up to 8". (Over ℕ the subtraction is exact: for n ≥ 1,
`3^n ≥ 3·2^(n−1)`, so ℕ-truncated `−` agrees with the integer value.)

---

## 2. English gloss of every definition in the statement's dependency chain

Walking outward from `(avoiders n).card`, each entry names the Lean object, its
paper meaning, and where it bottoms out. All definitions live in
`ElizaldeLuo/Defs.lean`, docstring-pinned verbatim to `../DEFINITIONS.md`
(itself quoting the published LaTeX `../src/formatted.tex`). Do not edit them.

- **`avoiders n : Finset (List ℕ)`** — the set being counted: all raw labeled
  words that are nonnesting permutations of `[n]₂` avoiding both 1132 and 3312.
  `avoiders n = (words n).filter (fun w => Nonnesting w ∧ Avoids w pat1132 ∧ Avoids w pat3312)`.
- **`.card`** — mathlib `Finset.card`: the number of elements of a finite set
  (bedrock: length of the underlying deduplicated `Multiset`/`List`).
- **`words n : Finset (List ℕ)`** — all permutations of the multiset `[n]₂`, as raw
  words. Built as the length-`2n` strings over `{0,…,n}` (`strings (Fin (n+1)) (2*n)`)
  filtered by `IsMultisetPerm n`. `mem_words`: `w ∈ words n ↔ w.Perm (baseWord n)`.
  Enumerated structurally (not via `List.permutations`) so it **reduces in the kernel**.
- **`baseWord n : List ℕ`** — the canonical ground word `[1,1,2,2,…,n,n]`
  (`(List.range' 1 n).flatMap fun v => [v, v]`). Paper §1: "the multiset consisting
  of two copies of each integer between 1 and n." `length_baseWord`: length `2n`.
- **`IsMultisetPerm n w := w.Perm (baseWord n)`** — `w` uses each letter `1..n`
  exactly twice. `List.Perm` is mathlib's permutation relation (bedrock: same
  multiset of elements). **No quotient by relabeling** — the count is over raw
  labeled words (paper §5 / DEFINITIONS.md §5).
- **`Nonnesting w := Avoids w pat1221 ∧ Avoids w pat2112`** — the matching of `w`
  has no nested arcs. Paper §3: "permutations of [n]₂ that avoid the patterns 1221
  and 2112." (`pat1221 = [1,2,2,1]`, `pat2112 = [2,1,1,2]`.)
- **`Avoids w σ := ¬ Contains w σ`** — `w` does not contain the pattern `σ`.
- **`Contains w σ`** — pattern containment, the crux. There is a strictly
  increasing index map `f : Fin σ.length → Fin w.length` such that the picked
  subsequence is order-isomorphic to `σ` under **both** biconditionals:
  `w.get (f r) < w.get (f s) ↔ σ.get r < σ.get s` **and**
  `w.get (f r) = w.get (f s) ↔ σ.get r = σ.get s`. Paper §2 (verbatim in the
  docstring): equal pattern letters force equal word letters; strict order forces
  strict order. Bedrock: `Fin`, `List.get`, `<`/`=` on ℕ. A `Decidable` instance is
  derived, so `Contains`/`Avoids`/`Nonnesting`/`IsAvoider` are all machine-decidable.
- **`pat1132 = [1,1,3,2]`, `pat3312 = [3,3,1,2]`** — the two avoided patterns
  (Table 4 row `{1132,3312}`).
- **`IsAvoider n w := IsMultisetPerm n w ∧ Nonnesting w ∧ Avoids w pat1132 ∧ Avoids w pat3312`**
  — the membership predicate for `avoiders`; `mem_avoiders : w ∈ avoiders n ↔ IsAvoider n w`.
- **RHS arithmetic** `3 ^ n - 3 * 2 ^ (n - 1) + 1` — mathlib `Nat` `HPow`/`HMul`/
  `HSub`/`HAdd`. Bedrock ℕ.

The proof itself factors through `validPairs n` (shape × sign-word pairs) and the
language `W n` (ternary words), but **none of those appear in the statement** — the
statement depends only on the objects above, all pinned to the paper.

---

## 3. Source claim (verbatim) → formal statement bridge

Paper: S. Elizalde and A. Luo, *Pattern avoidance in nonnesting permutations*,
arXiv:2412.00336; DMTCS 27:1 (2025), Permutation Patterns 2024, paper #13,
DOI 10.46298/dmtcs.14885.

Preamble to Table 4 (`src/formatted.tex` line 1600, verbatim):

> In Table~\ref{tab:conjecture} we list some cases that seem to give interesting
> enumeration sequences. All the conjectures have been checked for $n$ up to $8$.

The relevant row of Table 4 (`tab:conjecture`, `src/formatted.tex` line 1614, verbatim):

> `$\{1132,3312\}$ & $3^n-3\cdot2^{n-1}+1$ & A168583\\`

In the paper's notation this asserts `𝔠ₙ(1132,3312) = 3^n − 3·2^(n−1) + 1` for
`n ≥ 1`, where `𝔠ₙ(Λ)` counts nonnesting permutations of `[n]₂` avoiding every
pattern in `Λ`. **Bridge:** `𝔠ₙ(1132,3312) = (avoiders n).card` (Defs.lean pins
the avoidance/nonnesting/counting conventions verbatim; §2 above), and the RHS is
the literal Lean term `3 ^ n - 3 * 2 ^ (n - 1) + 1`. So the printed table cell is
exactly `theorem elizalde_luo_1132_3312`. OEIS cross-ref: the sequence is the
shift A168583(n+2) = 1, 4, 16, 58, 196, 634, 1996, 6178, … (DEFINITIONS.md §4).

---

## 4. Small-n validation (definitions need no trust)

`ElizaldeLuo/Sanity.lean` is built as part of the library and ties the *real*
definitions to the paper's data 1, 4, 16, 58, 196 (`= 3^n − 3·2^(n−1) + 1`):

- **Kernel-checked (`by decide`, no `native_decide`):**
  `(avoiders 1).card = 1`, `(avoiders 2).card = 4`;
  `(validPairs n).card = 1,4,16,58` for `n = 1..4`; `(W n).card = 1,4,16,58,196`
  for `n = 1..5`.
- **Interpreter-checked (`#guard`, native-free, over the real `IsAvoider`):**
  the real-definition avoider count is **16 at n = 3** and 1, 4 at n = 1, 2;
  the fast cross-checked form gives **58 at n = 4** with every survivor also
  satisfying the real `IsAvoider`; nonnesting totals `n!·Cₙ = 1, 4, 30, 336`; and
  the whole encode/decode pipeline (openerShape/signWordOf/phi/psi/wd) at n = 3, 4,
  plus the worked examples of `drafts/bijection.md §10`.

(Kernel `decide` on `avoiders 3` is too slow, so n = 3, 4 avoider counts are the
`#guard`/fast-form checks above; the two-sided real check at n = 4 is in
`scripts/SlowSanity.lean`.) If any definition drifts from DEFINITIONS.md, the
build fails. **No separate Validation.lean is needed — Sanity.lean already is it.**

---

## 5. Axiom audit (rerun fresh this pass — exit 0)

`lake env lean scripts/AxiomCheck.lean`, 2026-07-08, verbatim output:

```
'ElizaldeLuo.elizalde_luo_1132_3312' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElizaldeLuo.conjecture_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElizaldeLuo.card_avoiders_eq_card_validPairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElizaldeLuo.card_validPairs_eq_card_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElizaldeLuo.card_W' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElizaldeLuo.theoremA' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElizaldeLuo.contains_1132_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ElizaldeLuo.contains_3312_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the standard mathlib triple `[propext, Classical.choice, Quot.sound]` — **no
`sorryAx`, no extra axioms, no `native_decide`/`ofReduceBool`.** A grep for
`sorry`/`admit` over `ElizaldeLuo/*.lean` matches only comments/docstrings (the
originally-sorried modules are all marked COMPLETE). *(Note: repo `RESULTS.md` §9
still describes this formalization as incomplete "scaffolding" — that entry is
stale; STATUS.md dated it COMPLETE 2026-06-12 and this pass reconfirms it.)*

---

## 6. One command that rebuilds + re-audits

Toolchain pinned by `lean-toolchain` (`leanprover/lean4:v4.30.0`); needs
`elan`/`lake` on PATH (`%USERPROFILE%\.elan\bin`).

```
cd problems\p3-moonshot\elizalde-luo\lean
lake build                                 && ^
lake env lean scripts\AxiomCheck.lean
```

Expect: `Build completed successfully (8491 jobs).`, exit 0 (only pre-existing
style/unused-variable lints), then the eight axiom lines of §5. On the build
machine the incremental build is a no-op with the `.lake` cache present; a
cold first build fetches + compiles mathlib and can take hours (pinned by
`lean-toolchain`). **Build reproduced green this pass (8491 jobs, exit 0).**
