# STATUS: Elizalde–Luo {1132, 3312} conjecture — Lean formalization

**Date:** 2026-06-12
**Verdict: COMPLETE.** The full theorem is formalized and kernel-checked, with no
`sorry`, no `admit`, no `native_decide`, and no extra axioms.

## The theorem

`ElizaldeLuo/Main.lean`:

```lean
theorem elizalde_luo_1132_3312 (n : ℕ) (hn : 1 ≤ n) :
    (avoiders n).card = 3 ^ n - 3 * 2 ^ (n - 1) + 1

theorem conjecture_holds : ConjectureStatement
```

where `avoiders n` is the `Finset` of raw labeled words of length `2n` over
`{1,…,n}` using each letter exactly twice (`List.Perm (baseWord n)`), avoiding
`1221` and `2112` (= nonnesting) and avoiding `1132` and `3312`, all under the
paper's equality-pattern containment convention (both biconditionals, strictly
increasing index map) — pinned verbatim from the published LaTeX in
`../DEFINITIONS.md` and reproduced in the docstrings of `ElizaldeLuo/Defs.lean`.
For `n ≥ 1` we have `3^n ≥ 3·2^(n-1)`, so the ℕ-subtraction statement is exactly
the integer claim.

## Verification gates (all green, 2026-06-12)

| Gate | Result |
|---|---|
| `lake build` (full project, 8491 jobs, incl. `Sanity` and `Main`) | **Success**, zero errors; only pre-existing style/deprecation lints in other packages' files |
| `sorry` / `admit` / `axiom` / `native_decide` grep over `ElizaldeLuo/*.lean` | **Clean** (matches occur only inside comments/docstrings) |
| `#print axioms elizalde_luo_1132_3312` (and `conjecture_holds`, plus all chain headlines) | exactly `[propext, Classical.choice, Quot.sound]` (see `scripts/AxiomCheck.lean`) |
| n ≤ 4 sanity layer (`ElizaldeLuo/Sanity.lean`, built as part of the library) | **Passing**: kernel `decide` for `(avoiders 1).card = 1`, `(avoiders 2).card = 4`, `(validPairs n).card` and `(W n).card` = 1, 4, 16, 58 (n ≤ 4), `(W 5).card = 196`; interpreted `#guard`s for the real-definition counts at n = 3 (16), the cross-checked fast form at n = 4 (58), nonnesting totals 30/336, and the whole encode/decode pipeline at n = 3, 4 |
| Codex hostile faithfulness review (GPT-5.5, thread `019ebb36-3ba6-7272-b767-af4a5784000a`) | **FAITHFUL** — all 7 audit items PASS (containment definition exact incl. both biconditionals; raw-word counting, no relabeling quotient; nonnesting = 1221∧2112 avoidance; patterns verbatim; ℕ-subtraction benign for n ≥ 1; sanity guards exercise the real definitions and match ground truth 1, 4, 16, 58 — re-derived independently by Codex from the literal paper definition; discharged statement is the full ∀-claim) |

## Proof chain (drafts/bijection.md)

```
avoiders n ──(Lemma 0 + Theorem A + Fact 3.1)──▶ validPairs n
           ──(Theorem B: Φ/Ψ + Lemmas 4–6)──▶ W n
           ──(Lemma 7)──▶ 3^n − 3·2^(n−1) + 1
```

- `card_avoiders_eq_card_validPairs` (TheoremA.lean) — explicit bijection
  `w ↦ (openerShape w, signWordOf (openerLabels w))`, inverse
  `(s, ε) ↦ wd s (permOfSigns ε)`; the n = 0 case (both sides = 1) by `decide`.
- `card_validPairs_eq_card_W` (Bijection.lean) — the letter-by-letter Φ/Ψ pair.
- `card_W` (WLang.lean) — the two-line disjointness count
  `3^n − 2^(n−1) − (2^n − 1)`.

## File map

| File | Role | Status |
|---|---|---|
| `Defs.lean` | pinned definitions (containment, nonnesting, avoiders, statement) | sorry-free, definitions never changed |
| `Fifo.lean` (+ `Helpers_fifo.lean`) | Lemma 0: nonnesting = wd(Dyck shape, label perm), FIFO reconstruction | complete |
| `SignWord.lean` (+ `Helpers_signword.lean`) | Facts 3.1/3.2 (sign-word bijection, comparison rule), Lemma 2 | complete |
| `TheoremA.lean` (+ `Helpers_theoremA.lean`, **new**) | Lemma 1 (positional criteria), Theorem A, chain step 1 | complete (this session) |
| `Shapes.lean` (+ `Helpers_shapes.lean`) | Lemmas 3–6: obstruction, S/I/II classification, local validity | complete |
| `Bijection.lean` (+ `Helpers_bijection.lean`) | Theorem B: Φ/Ψ bijection onto W | complete |
| `WLang.lean` (+ `Helpers_wlang.lean`) | Lemma 7: \|W n\| | complete |
| `Main.lean` | composition of the three card equalities | complete |
| `Sanity.lean` | n ≤ 4 ground-truth and pipeline checks (`decide` + `#guard`, native-free) | passing |
| `scripts/AxiomCheck.lean` | axiom audit (run: `lake env lean scripts\AxiomCheck.lean`) | clean |
| `scripts/SlowSanity.lean` | optional slow two-sided real-definition n = 4 check | available |

## What was finished in this session (package "theoremA")

The four remaining sorries — `contains_1132_iff`, `contains_3312_iff`,
`theoremA`, `card_avoiders_eq_card_validPairs` — plus a new sorry-free helper
file `ElizaldeLuo/Helpers_theoremA.lean` (namespace `ElizaldeLuo.TA`; it cannot
reuse `ShapesH` because `Helpers_shapes` imports `TheoremA`, so the small shared
`posOf` calculus is reproduced there). Key new infrastructure:

- `TA.openerShape_getD_true_iff/false_iff`: position `k` of `w` is an opener iff
  its value has not occurred in `w.take k` (accumulator induction over
  `openerShape.go`);
- `TA.fstList_eq` / `TA.sndList_eq`: the lists of first/second occurrences of the
  labels (in label order) are *equal as lists* to the opener/closer position
  lists of the shape — proved by the strictly-sorted-sublist-of-equal-length
  argument (`TA.sorted_eq_of_subset`), with strict monotonicity of second
  occurrences supplied by nonnesting (`SW.sndIdx_lt_sndIdx`); this is the
  position-level content of the FIFO matching;
- `TA.getD_oPos` / `TA.getD_qPos` / `TA.arc_of_position`: value transport between
  arcs and positions, plus arc recovery for an arbitrary position;
- `TA.two_positions`: in a word where `v` occurs exactly twice, two positions
  carrying `v` are forced to be (first, second) occurrence — the "i₂ = snd(v)"
  step of Lemma 1;
- Fact 0.1 (`TA.oPos_lt_qPos_self`) and the `oPos`/`qPos` order calculus.

`theoremA` then follows the draft §4 exactly: (⇒) Lemma 2 + comparison rule +
the explicit 1132/3312 occurrence at positions `o₁ < q₁ < o_J < q_K`;
(⇐) a shared `spatial` analysis (value of the repeated letter pins arc `C` and
`j = q_C`; positions `k, l > q_C` get arcs `A, B > C`), sign chase via the
comparison rule (`ε_B = ε_A` forced equal), and a shared four-case position
analysis forcing `k = o_A`, `l = q_B`, contradicting `ValidSign` at `(J, K) =
(A, B)`.

Statement hygiene: all four pinned statements are byte-identical to the
original sorried versions (the unused `hw` hypotheses of `contains_*_iff` are
kept, with a local `set_option linter.unusedVariables false`).

## Known statement deviations from the drafts (inherited, documented)

Three lemmas *internal to the chain* carry an `(hn : 1 ≤ n)` hypothesis that the
original sorried statements lacked, because the n = 0 instances were literally
false as first stated (`permOfSigns_signWordOf`, `phi_mem_W`, `compl_W`); the
draft itself only claims n ≥ 1. The main theorem and `ConjectureStatement` are
unaffected (the conjecture is for n ≥ 1; chain step 1 holds for all n, with
n = 0 discharged by `decide`).

## Caveats / honesty

- The axiom base is the standard Mathlib triple (propext, Classical.choice,
  Quot.sound); no `ofReduceBool`/native evaluation anywhere, so even the
  `decide`-based sanity instances are kernel-checked.
- Faithfulness rests on `DEFINITIONS.md` quoting the published LaTeX verbatim
  (`src/formatted.tex`, DOI 10.46298/dmtcs.14885); both the containment
  convention and the counting convention were re-checked against the paper
  source in the hostile review.
- The paper states the formula as a conjecture verified to n = 8; this
  formalization proves it for all n ≥ 1 via the bijection of
  `drafts/bijection.md` (audited sound by two independent hostile audits plus
  Codex referee rounds; see `../final-results.json`).
