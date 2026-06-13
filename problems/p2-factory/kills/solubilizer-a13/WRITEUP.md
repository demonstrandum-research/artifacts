# Refutation of Conjecture A.13 of arXiv:2412.16177 (LLM-generated solubilizer conjecture: normal core of Sol_G(x) vs. hypercenter)

Slug: `solubilizer-a13` | Gate-5 write-up, 2026-06-11 | Status: **REFUTED — verified, Codex-confirmed, fresh kill-check clean**

---

## Abstract (~120 words)

Conjecture A.13 of arXiv:2412.16177 ("Mining Math Conjectures from LLMs: A Pruning
Approach", NeurIPS 2024 MATH-AI workshop) asserts that for any non-solvable group G and
any x in G with Sol_G(x) a proper subgroup of G, the intersection of Sol_G(x) with all of
its conjugates in G is contained in the hypercenter of G. We refute it. In G = A5 x S3
(order 360) with x = ((0 1 2 3 4), id), Sol_G(x) = D10 x S3 is a proper subgroup of order
60 whose normal core is 1 x S3 (order 6), while Z(G) = 1 forces the hypercenter to be
trivial. An exhaustive exact sweep over all 360 elements shows A.13 fails at every
applicable x in this G. The mechanism — the solvable radical lies in every solubilizer —
kills A.13 in any non-solvable group with nontrivial solvable radical and trivial
hypercenter.

---

## Claim standard (FRAMEWORK.md section 9)

> **Result.** Conjecture A.13 of arXiv:2412.16177v1 is **false**. Verbatim statement
> refuted (PDF p. 60, appendix A.5.6 "Additional Conjectures"): "Let G be a non-solvable
> group. For any element x in G, if SolG(x) is a proper subgroup of G, then the
> intersection of SolG(x) with all of its conjugates in G is always contained in the
> hypercenter of G." Counterexample: G = A5 x S3, x = ((0 1 2 3 4), id); the intersection
> of Sol_G(x) with all of its G-conjugates is 1 x S3 (order 6), the hypercenter is trivial.
>
> **Status before this work.** Stated December 2024 (arXiv:2412.16177, single version v1,
> 9 Dec 2024; also OpenReview aYlKvzY6ob, NeurIPS 2024 MATH-AI workshop). Listed by the
> authors among conjectures whose checking "code was unable to be run" — i.e. never
> machine-validated by the source paper. No refutation found at selection time
> (2026-06-11) or at final kill-check (2026-06-11; section "Openness re-check" below).
>
> **Artifact.** `certificate_a13.json` (this directory): the element x, the full 60-element
> set Sol_G(x), the 6-element normal core, the upper central series orders, the witness
> element, derived-series orders of G, and the full-sweep summary, all as length-8
> permutation arrays.
>
> **Verification.** Clean-room checker `checker_a13.py` (pure Python 3, stdlib only, exact
> integer/permutation arithmetic; written by the Gate-4 verifier from the construction
> description only, without reading the discoverer's scratch work or the orchestrator's
> script). Mutation testing: 7/7 targeted certificate corruptions rejected
> (`mutation_test.py`, `mutation_test.log`). Hostile Codex (GPT-5.5) cross-examination
> with full shell+network access: independent recomputation by a different method,
> verdict "DEAD — the refutation stands" (threadId 019eb9a0-155d-7f70-bb16-6f839b10ef78;
> verbatim in `VERIFICATION.log`). Fresh re-run at Gate-5 (2026-06-11): `--verify` exits 0
> with ACCEPT in ~15 s. Note: the orchestrator's `verify_kills.py` (one level up) covers
> the sibling kills (Davila C9, solubilizer A.1, Graffiti 143/154, Pandey parity) but has
> no A.13 section as of this date; for A.13 the independent second check is Codex's
> direct-product recomputation, which used a different representation than the checker's
> 8-point permutation model.
>
> **Openness re-check.** 2026-06-11, nine searches/fetches across arXiv (search + API),
> Semantic Scholar citation graph, OpenReview, and general web: no prior or concurrent
> refutation of A.13 found. Details below.
>
> **What this does not show.** See dedicated section below.

---

## 1. Exact statement and provenance

**Source.** Jake Chuharski, Elias Rojas Collins, Mark Meringolo, *Mining Math Conjectures
from LLMs: A Pruning Approach*, arXiv:2412.16177 (v1, the only version, 9 Dec 2024);
also OpenReview `aYlKvzY6ob` (NeurIPS 2024 Workshop MATH-AI). PDF fetched 2026-06-11 from
<https://arxiv.org/pdf/2412.16177v1> and frozen as `paper-2412.16177v1.pdf` in this
directory (1,030,052 bytes). The HTML rendering at arxiv.org/html loses the `{conj}`
environment numbering, so the "A.13" label is only visible in the PDF.

**Verbatim statement** (PDF p. 60, appendix A.5.6 "Additional Conjectures", whose preamble
reads "The following conjectures are just a couple of the conjectures that had code that
was unable to be run but are still potentially interesting from Claude:"):

> **Conjecture A.13.** Let G be a non-solvable group. For any element x in G, if SolG(x)
> is a proper subgroup of G, then the intersection of SolG(x) with all of its conjugates
> in G is always contained in the hypercenter of G.

**Definitions and ambiguity resolution.**

- Definition 3.1 of the paper (verbatim): "Let G be a finite group. For any element x in
  G, the solubilizer of x in G is defined as: SolG(x) := {y in G | <x, y> is soluble}".
  The paper's scope is finite groups; our counterexample is finite (|G| = 360).
- "Hypercenter" occurs nowhere else in the paper and is never defined there, so the
  standard meaning applies: Z_inf(G), the stable term of the upper central series
  Z_0 = 1 <= Z_1 = Z(G) <= Z_2 <= ... (Baer). For finite G the series stabilizes.
- "The intersection of SolG(x) with all of its conjugates in G": grammatically "its" can
  refer to the set Sol_G(x) (giving the normal core of Sol_G(x)) or to x (giving the
  intersection of Sol_G(x^g) over g). Since Sol_G(x^g) = (Sol_G(x))^g — verified
  exhaustively for all 360 g in our G — **both readings define the same set**, so the
  refutation is reading-independent.
- Statement fidelity: the quote in `refuted-claims.json` and `certificate_a13.json`
  matches the PDF character-for-character (checked at Gate 4 and independently by Codex
  against the arXiv source).

## 2. The counterexample

**Group.** G = A5 x S3, realized as permutations of {0,...,7}: A5 = even permutations of
{0..4}, S3 = permutations of {5,6,7}. |G| = 360. G is non-solvable: its derived series has
orders 360 -> 180 -> 60, stabilizing at the perfect subgroup A5 x 1.

**Element.** x = ((0 1 2 3 4), id), i.e. the permutation `[1, 2, 3, 4, 0, 5, 6, 7]`
(image array: i -> x[i]).

**Solubilizer.** Sol_G(x) = N_A5(<(0 1 2 3 4)>) x S3 = D10 x S3, where
D10 = <(0 1 2 3 4), (1 4)(2 3)> is the dihedral group of order 10. Thus |Sol_G(x)| = 60,
it is closed under multiplication (a genuine subgroup, so A.13's hypothesis applies), and
it is proper (60 < 360). The full 60-element listing is in `certificate_a13.json`
(`sol_x`). Why it has this shape: for y = (u, v), <x, y> is a subdirect product inside
<(0 1 2 3 4), u> x <v>, and the S3 factor is solvable, so <x, y> is solvable iff
<(0 1 2 3 4), u> is solvable in A5; and Sol_A5(a) = N_A5(<a>) = D10 for a 5-cycle a.

**Normal core.** The intersection of Sol_G(x) with all of its conjugates in G,
K = cap over g in G of g^{-1} Sol_G(x) g, equals **1 x S3**, order 6 — the six
permutations fixing 0..4 pointwise:

```
[0,1,2,3,4,5,6,7]  (identity)
[0,1,2,3,4,5,7,6]  (6 7)
[0,1,2,3,4,6,5,7]  (5 6)
[0,1,2,3,4,6,7,5]  (5 6 7)
[0,1,2,3,4,7,5,6]  (5 7 6)
[0,1,2,3,4,7,6,5]  (5 7)
```

K is normal in G and solvable; in fact K = R(G), the solvable radical of G.

**Hypercenter.** Z(G) = Z(A5) x Z(S3) = 1 x 1 = 1, so the upper central series is
Z_0 = 1, already stable: **Z_inf(G) = 1** (computed directly, not via the product
formula: the checker tests all 360 elements for centrality at each level).

**The kill.** K has order 6, Z_inf(G) has order 1, so K is not contained in Z_inf(G).
Explicit witness in K \ Z_inf(G): (id, (6 7)) = `[0, 1, 2, 3, 4, 5, 7, 6]`.
**Conjecture A.13 is false.**

**Structural mechanism (why A.13 was doomed).** For every x = (u, v) and every
s = (1, w) in 1 x S3, <x, s> lies in <u> x S3, which is solvable; hence the solvable
radical R(G) = 1 x S3 is contained in Sol_G(x) for *every* x in G, and being normal it is
contained in every conjugate of every solubilizer, hence in every core. So **any**
non-solvable G with R(G) nontrivial and Z_inf(G) trivial (e.g. any centerless product
(non-abelian simple) x (centerless solvable)) refutes A.13 at every applicable x. The
source paper's GAP validation pipeline iterated mainly over simple groups, where R(G) = 1
hides this entire failure mode — and for A.13 specifically the generated code never ran
at all (the paper says so).

## 3. Verification procedure

**Clean-room checker: `checker_a13.py`** (pure Python 3, stdlib only, exact
integer/permutation arithmetic, no floats, no external libraries). Written at Gate 4 by an
independent verifier from the construction description in `refuted-claims.json` only
(clean-room protocol: the discoverer's `.scratch` and the orchestrator's `verify_kills.py`
were never opened). It rebuilds everything from scratch:

1. constructs G as 360 permutation tuples, builds the full 360x360 multiplication table,
   and verifies closure and inverses;
2. proves G non-solvable via its derived series (orders 360 -> 180 -> 60, terminating at
   a perfect subgroup);
3. computes Sol_G(x) directly from Definition 3.1 (subgroup closure + iterated derived
   subgroup solvability test for each of the 360 candidate y), verifies it is a proper
   subgroup of order 60 with shape (order-10 subgroup of A5) x S3;
4. computes the normal core as the literal intersection of g^{-1} Sol_G(x) g over all
   360 g, verifies order 6, normality, solvability, and the 1 x S3 shape;
5. computes the upper central series by the direct [z, g] in Z_i criterion over all of G,
   obtaining Z_inf(G) = 1;
6. asserts core not contained in hypercenter and exhibits the witness;
7. runs the full extension sweep (section 4) and the reading-equivalence check.

Usage (any machine with Python 3; runs in ~15 s):

```
python checker_a13.py --verify certificate_a13.json   # recompute + compare, exit 0 + ACCEPT
python checker_a13.py --emit  cert_out.json           # recompute + write certificate
```

Any failed assertion prints `REJECT: <reason>` and exits nonzero. Logs of the accepting
runs: `run_emit.log`, `run_verify.log`. A fresh Gate-5 re-run on 2026-06-11 reproduced
ACCEPT, exit 0, in 15.3 s.

**Mutation testing** (`mutation_test.py`, `mutation_test.log`): 7 targeted corruptions of
the certificate — drop-sol-element, extra-core-element, inflate-hypercenter, wrong-x,
bad-witness, tampered-statement, sweep-zeroed — were all rejected by `--verify` (7/7).

**Hostile Codex cross-examination** (GPT-5.5, full shell + network access, 2026-06-11,
threadId `019eb9a0-155d-7f70-bb16-6f839b10ef78`; verbatim verdict in `VERIFICATION.log`).
Codex independently fetched the arXiv v1 source/PDF, confirmed statement placement and
verbatim fidelity, and recomputed the counterexample *by a different method* (abstract
direct-product computation, not the checker's 8-point permutation model):
Sol_G(x) = D10 x S3 of order 60, core = core_A5(D10) x S3 = 1 x S3 of order 6,
Z(A5 x S3) = 1 hence trivial hypercenter. It attempted semantic escapes (alternative
reading of "its conjugates", finiteness restriction, a "simple G" restriction) and
reported none works. It audited the checker's nontrivial steps (positive-word BFS closure,
commutator-closure derived subgroup, conjugation direction, upper-central-series
criterion) and found them sound, flagging one cosmetic issue only (`--verify` does not
compare every narrative JSON field — it does recompute and compare all decisive
mathematical fields). Verdict: "DEAD. The refutation stands."

**Orchestrator script.** `problems/p2-factory/verify_kills.py` is the orchestrator's
independent re-verification harness for this factory's kills; it currently covers Davila
Conjecture 9, solubilizer A.1, Graffiti 154, Graffiti 143, and the Pandey parity kill, but
contains **no A.13 section** as of 2026-06-11 (this write-up does not modify
orchestrator-owned files). For A.13, the role of the second independent check is filled by
Codex's recomputation in a different representation; if the orchestrator wants a
same-style section, items (1)-(6) above specify it in ~50 lines.

**Reproduce in under an hour** (actually under a minute): open this directory, run the
`--verify` command above, observe `ACCEPT` and exit code 0; optionally run
`python mutation_test.py` and observe all mutants rejected; optionally diff the statement
in `certificate_a13.json` against p. 60 of `paper-2412.16177v1.pdf`.

## 4. Extension findings (beyond the single counterexample)

Full brute-force sweep over **all 360 elements** x of G (exact arithmetic, part of every
checker run):

- |Sol_G(x)| distribution: 60 for 144 elements (x = (5-cycle, anything)); 144 for 120
  elements; 216 for 90 elements; 360 for the 6 elements of 1 x S3. The size-144 and
  size-216 solubilizers are **not subgroups** (consistent with Lagrange: 144 and 216 do
  not divide 360), so Sol_G(x) is a subgroup for exactly 150 of 360 elements.
- Sol_G(x) is a **proper** subgroup for exactly 144 elements, and for **all 144** the
  normal core contains 1 x S3 while the hypercenter is trivial: **A.13 fails at every
  element of this G to which it applies**, not just the certificate x.
- The structural mechanism is confirmed computationally: 1 x S3 lies inside Sol_G(x) for
  every one of the 360 x.
- Reading equivalence verified exhaustively: Sol_G(x^g) = g^{-1} Sol_G(x) g for all
  360 g, so both grammatical readings of "its conjugates" give the same intersection.
- Derived series of G: 360 -> 180 -> 60 (perfect A5 x 1), certifying non-solvability;
  upper central series: already stable at Z_0 = 1.
- Infinite family for free: the same argument (radical-in-every-solubilizer + trivial
  hypercenter) refutes A.13 in (any non-abelian simple S) x (any centerless solvable H),
  e.g. A5 x S3 is merely the smallest natural instance we exhibited.

## 5. Openness re-check (fresh kill-check, 2026-06-11)

Searches run on 2026-06-11 (Gate 5, same day as Gate-4 verification), looking for any
prior or just-published refutation of this exact conjecture:

| # | Query / fetch | Result |
|---|---|---|
| 1 | Web search: `arXiv 2412.16177 "Mining Math Conjectures" refutation counterexample solubilizer` | Only the paper itself (arXiv abs/pdf/html) + unrelated spectral-graph refutation papers. No refutation of A.13. |
| 2 | Web search: `solubilizer "hypercenter" conjecture counterexample group theory` | Hits: profinite solubilizers (arXiv:2310.02034), Normalizer-Solubilizer Conjecture (arXiv:2501.11486), Baer's hypercenter, hypercenter of algebraic groups (arXiv:2603.27617). None concern A.13. |
| 3 | Semantic Scholar citation graph for arXiv:2412.16177 (API) | 3 citing papers (genetic-programming conjecture discovery 2026; "The Agentic Researcher" arXiv:2603.15914; LLM constraint-solving arXiv:2603.03668). None group-theoretic; none refute any appendix conjecture. |
| 4 | Fetched arXiv:2501.11486 ("On the Normalizer-Solubilizer Conjecture", v3 updated 2025-06-10) | Different conjecture (|N_G(<x>)| divides |Sol_G(x)|); no mention of hypercenter, A.13, or 2412.16177. |
| 5 | Web search: `"solubilizer" group theory arXiv 2025 OR 2026 "normal core" OR "intersection of conjugates"` | Known solubilizer literature (arXiv:2210.11564, 2309.09104, 2003.01205, 2310.02034). Nothing on A.13. |
| 6 | Web search: `"Mining Math Conjectures" Chuharski conjecture "A.13" OR "appendix" refuted` | Only copies of the paper (arXiv, OpenReview aYlKvzY6ob, ResearchGate). No refutation. |
| 7 | Fetched OpenReview forum aYlKvzY6ob (NeurIPS 2024 MATH-AI) | No public comments/replies discussing refutations of the appendix conjectures. |
| 8 | Web search: `"hypercenter" "Sol" solubilizer counterexample "A5" OR "alternating group" 2026` | Unrelated (F-hypercenter formations arXiv:2407.13606, algebraic-group hypercenter). No A.13 refutation. |
| 9 | arXiv API, `all:"solubilizer"`, 30 most recent by submission date | Newest relevant item is 2501.11486v3 (2025-06-10); no 2025-2026 paper mentions the hypercenter conjecture or refutes anything from 2412.16177. |

This matches the independent prior-art search Codex ran during Gate-4 cross-examination
(also 2026-06-11, also empty). **Conclusion: no prior or concurrent refutation of
Conjecture A.13 found as of 2026-06-11.** As always, web searches are evidence of
novelty, not proof.

## 6. What this does not show

- **Not a new open-problem resolution in the classical sense.** A.13 is an LLM-generated
  (Claude) conjecture from a December 2024 methods paper, explicitly listed among
  conjectures whose validation code "was unable to be run" — it was never
  machine-validated by its own authors and has, as far as we can tell, never been studied
  by a human group theorist. The refutation is correct and apparently novel, but its
  mathematical weight is modest.
- It says nothing about the *other* conjectures in that paper (A.1 and A.16 are handled
  by sibling kills in this factory; the rest are untouched), nor about the established
  solubilizer literature (e.g. the Normalizer-Solubilizer Conjecture of arXiv:2501.11486
  remains open and is unrelated).
- It does not show A.13 fails in *every* non-solvable group: in groups with trivial
  solvable radical (e.g. all non-abelian simple groups, where the core of a proper
  solubilizer-subgroup is trivial whenever it is a subgroup) the statement can hold
  vacuously or trivially. The refutation pinpoints exactly the regime the conjecture's
  validation pipeline never sampled.
- The "hypercenter" reading is the standard one (Z_inf(G)); the source paper never defines
  the term. No standard alternative reading rescues the conjecture (Codex probed this),
  but we cannot exclude that the generating LLM "meant" some non-standard notion.
- Novelty rests on the dated searches in section 5 — evidence, not proof.

## 7. Publication grouping

**Publication grouping:** bundle with the other two solubilizer kills —
`solubilizer-a1` (A.1: Sol_G(x) ∩ Sol_G(y) contains a nontrivial normal subgroup of G;
killed by G = A5) and `solubilizer-a16` (A.16: Sol_G(x) ∩ N_G(Sol_G(x)) is metabelian;
killed by G = A5 x S4) — as a single note ("Counterexamples to the LLM-generated
solubilizer conjectures of arXiv:2412.16177"), since all three share the source paper,
the Definition 3.1 framework, and the direct-product blind-spot mechanism. The two
Graffiti spectral kills (`graffiti-143`, `graffiti-154`) form a separate natural bundle
(same Written-on-the-Wall source, same ECAI-2025 openness evidence), and the two
TxGraffiti-family kills (Davila Conjecture 9 + Pandey parity) a third; A.13 does not
belong in either of those.

## Files in this directory

| File | Role |
|---|---|
| `WRITEUP.md` | this document |
| `paper-2412.16177v1.pdf` | frozen provenance copy of the source paper (arXiv v1) |
| `certificate_a13.json` | the certificate (x, Sol_G(x), core, UCS orders, witness, sweep) |
| `checker_a13.py` | clean-room checker, pure Python 3 stdlib, exact arithmetic |
| `run_emit.log`, `run_verify.log` | accepting runs (exit 0, ACCEPT) |
| `mutation_test.py`, `mutation_test.log` | checker validation: 7/7 mutants rejected |
| `VERIFICATION.log` | Gate-4 log: provenance quotes, recomputation, verbatim Codex verdict |
