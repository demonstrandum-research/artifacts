/-
# Main theorem (bijection.md §9)

"**Theorem.** For all `n ≥ 1`, the number of nonnesting permutations of `[n]₂`
avoiding `{1132, 3312}` is `c_n = 3^n - 3·2^(n-1) + 1`."

Proof chain (each step a sorried headline in its own file/package):
  avoiders n  ──(Lemma 0 + Theorem A + Fact 3.1; TheoremA.lean)──▶ validPairs n
              ──(Theorem B = Φ/Ψ + Lemmas 4-6; Bijection.lean)──▶ W n
              ──(Lemma 7; WLang.lean)──▶ 3^n - 3·2^(n-1) + 1.

This file contains no `sorry` of its own — only the composition.
-/
import Mathlib
import ElizaldeLuo.Defs
import ElizaldeLuo.TheoremA
import ElizaldeLuo.Bijection
import ElizaldeLuo.WLang

namespace ElizaldeLuo

/-- **The Elizalde–Luo conjecture for {1132, 3312}** (arXiv:2412.00336, DMTCS 27:1
(2025), Table 4 row `$\{1132,3312\}$ & $3^n-3\cdot2^{n-1}+1$ & A168583`):
the number of nonnesting permutations of the multiset `{1,1,2,2,…,n,n}` avoiding
the patterns 1132 and 3312 equals `3^n - 3·2^(n-1) + 1` for every `n ≥ 1`. -/
theorem elizalde_luo_1132_3312 (n : ℕ) (hn : 1 ≤ n) :
    (avoiders n).card = 3 ^ n - 3 * 2 ^ (n - 1) + 1 := by
  rw [card_avoiders_eq_card_validPairs n, card_validPairs_eq_card_W n hn,
    card_W n hn]

/-- The counting statement of `Defs.lean`, discharged. -/
theorem conjecture_holds : ConjectureStatement :=
  elizalde_luo_1132_3312

end ElizaldeLuo
