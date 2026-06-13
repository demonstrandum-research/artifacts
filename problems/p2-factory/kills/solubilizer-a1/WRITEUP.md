# Refutation of Conjecture A.1 of arXiv:2412.16177 (LLM-generated solubilizer conjecture: Sol_G(x) ∩ Sol_G(y) contains a non-trivial normal subgroup of G)

Slug: `solubilizer-a1` | Gate-5 write-up, 2026-06-11 | Status: **REFUTED — verified, Codex-confirmed, fresh kill-check clean**

---

## Abstract (~120 words)

Conjecture A.1 of arXiv:2412.16177 ("Mining Math Conjectures from LLMs: A Pruning
Approach", NeurIPS 2024 MATH-AI workshop) asserts that in any non-solvable group G,
whenever Sol_G(x) ∩ Sol_G(y) is non-empty it contains a non-trivial normal subgroup of G.
The paper presents it as having survived GAP counterexample search over all non-solvable
(or simple) groups of order up to 1,000,000. It is false at the very first such group:
in G = A5 with x = y = (0 1 2 3 4), Sol_G(x) is the order-10 dihedral normalizer of
⟨x⟩, so the intersection is non-empty yet contains no non-trivial normal subgroup of G,
because A5 is simple. The distinct pair (x, x²) certifies the same under the
distinct-elements reading. A pure-Python exact checker recomputes everything from first
principles; 13/13 mutation tests reject corrupted certificates.

---

## Claim standard (FRAMEWORK.md section 9)

> **Result.** Conjecture A.1 of arXiv:2412.16177v1 is **false**. Verbatim statement
> refuted (main.tex lines 445–447 of the arXiv v1 source; first theorem-counter
> environment of the appendix, hence "Conjecture A.1" in the compiled PDF): "Let $G$ be a
> non-solvable group. For any two elements $x, y \in G$, if
> $\operatorname{Sol}_G(x) \cap Sol_G(y)$ is non-empty, then
> $\operatorname{Sol}_G(x) \cap Sol_G(y)$ contains a non-trivial normal subgroup of $G$."
> Counterexample: G = A5 with x = y = (0 1 2 3 4) (and also the distinct pair
> y = x² = (0 2 4 1 3)): the intersection Sol_G(x) ∩ Sol_G(y) is the order-10 dihedral
> group N_A5(⟨x⟩), non-empty, and contains no non-trivial normal subgroup of G since A5
> is simple.
>
> **Status before this work.** Stated December 2024 (arXiv:2412.16177, single version v1,
> 9 Dec 2024; also OpenReview aYlKvzY6ob, NeurIPS 2024 MATH-AI workshop), presented as
> "Example with no counterexamples from Claude" after the paper's GAP-based pruning over
> non-solvable/simple groups of order up to 10^6. No published refutation found at
> selection time (2026-06-11) or at final kill-check (2026-06-11; section 5 below).
>
> **Artifact.** `certificate_a1_a5.json` (this directory): frozen verbatim statement,
> solubilizer definition, provenance fields, and two certified pairs (x = y and x ≠ y),
> each with the full 10-element Sol_G(x), Sol_G(y), and intersection as length-5
> permutation arrays, plus claimed orders and structural flags.
>
> **Verification.** Clean-room checker `check_a1_refutation.py` (pure Python 3, stdlib
> only, exact integer/set arithmetic; written by the Gate-4 verifier from the construction
> description only). Independent second implementation: the orchestrator's
> `../../verify_kills.py` section [A.1] (different agent, different algorithmic route),
> fresh-run PASS on 2026-06-11. Third independent route: hostile Codex (GPT-5.5, full
> shell+network) recomputed everything with its own code and audited the checker over two
> rounds — "Verdict: VALID KILL" (thread 019eb9a0-27f7-7b90-8e4a-fe1919261cbb; verbatim in
> `verification_log.txt`). Mutation testing: 13/13 targeted certificate corruptions
> rejected, pristine accepted (`mutation_test.py`; one mutant designed by Codex). Fresh
> Gate-5 re-runs of checker, mutation suite, and orchestrator harness on 2026-06-11: all
> ACCEPT/PASS, exit 0.
>
> **Openness re-check.** 2026-06-11, eight searches/fetches across web search, the
> Semantic Scholar citation graph, the arXiv API, the arXiv abstract page, and OpenReview
> (the source venue): no prior or concurrent refutation of Conjecture A.1 found; the
> paper has no v2, no erratum. Details in section 5.
>
> **What this does not show.** See dedicated section 6 below.

---

## 1. Exact statement and provenance

**Source.** Jake Chuharski, Elias Rojas Collins, Mark Meringolo, *Mining Math Conjectures
from LLMs: A Pruning Approach*, arXiv:2412.16177 (v1, the only version, submitted
2024-12-09 19:00:38 UTC); also OpenReview `aYlKvzY6ob` (NeurIPS 2024 Workshop MATH-AI).
LaTeX e-print source downloaded 2026-06-11 from <https://arxiv.org/e-print/2412.16177>
and frozen in `src/` (tarball sha256
`9ee18ee8ca5822f3fe285a0caeb2ceda6b7f8a2cf1625c3e6011bda1458f0509`; Codex's independent
fresh download of `.../2412.16177v1` produced the **same** hash).

**Verbatim statement** (`src/main.tex`, lines 445–447; appendix subsection "Additional
Examples" → subsubsection "Claude", introduced at line 444 by "Example with no
counterexamples from Claude:"):

> **Conjecture A.1.** Let $G$ be a non-solvable group. For any two elements
> $x, y \in G$, if $\operatorname{Sol}_G(x) \cap Sol_G(y)$ is non-empty, then
> $\operatorname{Sol}_G(x) \cap Sol_G(y)$ contains a non-trivial normal subgroup of $G$.

**Numbering.** `neurips_2024.sty` defines `\newtheorem{thm}{Theorem}[section]` and
`\newtheorem{conj}[thm]{Conjecture}`; the appendix is a single `\section`, and this is
the first theorem-counter environment after `\appendix\section` (line 290), so it
compiles as **Conjecture A.1** in the PDF (confirmed by Codex PDF extraction). The arXiv
HTML (LaTeXML) renders the same statement as "Conjecture A.4.1" — same object, different
rendering counter.

**Definitions and ambiguity resolution.**

- Solubilizer (paper's Definition, Section 2.2 "Area of Focus", `src/main.tex` lines
  98–103, verbatim): "Let $G$ be a finite group. For any element $x \in G$, the
  solubilizer of $x$ in $G$ is defined as:
  $\operatorname{Sol}_G(x) := \{ y \in G \mid \langle x, y \rangle \text{ is soluble} \}.$"
  The paper's scope is finite groups; our counterexample is finite (|G| = 60).
- "Two elements x, y": both readings are certified — x = y (pair 0) and x ≠ y (pair 1,
  y = x²) — and the checker **requires** both, so neither interpretation of the
  quantifier survives.
- "Non-empty": the hypothesis is in fact vacuous (1 ∈ Sol_G(x) ∩ Sol_G(y) always, and
  x ∈ Sol_G(x)); the certificate certifies it explicitly anyway.
- "Normal subgroup **of G**": the printed statement is unambiguous. The charitable
  misreading "normal subgroup of the intersection" would be a different statement and is
  NOT refuted by this object (see section 6).
- Validation claim of the source paper (`src/main.tex` line 440): the experiments checked
  "all non-solvable (or in some cases just simple) groups of order up to 1,000,000".
- Statement fidelity: the quotes in `refuted-claims.json` and `certificate_a1_a5.json`
  match the LaTeX source character-for-character (checked at Gate 4; independently by
  Codex against a fresh arXiv download).

## 2. The counterexample

**Group.** G = A5, realized as the 60 even permutations of {0,1,2,3,4}; a permutation p
is the tuple (p(0),…,p(4)), composition (p·q)(i) = p(q(i)). G is non-solvable (its
derived series is the fixpoint G itself: A5 is perfect) and **simple** (certified
computationally: the normal closure of every one of the 59 non-identity elements is all
of G).

**Elements.** x = (0 1 2 3 4), i.e. the tuple `[1,2,3,4,0]`. Pair 0 takes y = x;
pair 1 takes y = x² = (0 2 4 1 3) = `[2,3,4,0,1]`.

**Solubilizer.** Recomputed from the definition (for each of the 60 candidates y: build
⟨x,y⟩ by closure, test solubility by the derived-series fixpoint), Sol_G(x) has
**exactly 10 elements**:

```
e                       [0,1,2,3,4]
x   = (0 1 2 3 4)       [1,2,3,4,0]
x^2 = (0 2 4 1 3)       [2,3,4,0,1]
x^3 = (0 3 1 4 2)       [3,4,0,1,2]
x^4 = (0 4 3 2 1)       [4,0,1,2,3]
(1 4)(2 3)              [0,4,3,2,1]
(0 1)(2 4)              [1,0,4,3,2]
(0 2)(3 4)              [2,1,0,4,3]
(0 3)(1 2)              [3,2,1,0,4]
(0 4)(1 3)              [4,3,2,1,0]
```

This is the dihedral group D10 = N_A5(⟨x⟩) — a non-abelian subgroup of order 10: the
identity, the four powers of x (order 5), and five involutions. Moreover Sol_G(x²) = Sol_G(x), so for both certified pairs

  Sol_G(x) ∩ Sol_G(y) = D10, order 10, containing 1 and x  (**hypothesis holds**).

**The kill.** A5 is simple, so its only non-trivial normal subgroup is A5 itself, of
order 60 — which cannot be contained in a 10-element set. Directly: for every
non-identity g in the intersection, the normal closure of g in G is all of G (60
elements), so no non-trivial normal subgroup of G lies inside the intersection
(**conclusion fails**). **Conjecture A.1 is false.** Both the direct route (normal
closures of intersection elements) and the simplicity route are checked independently by
the checker.

**Why the paper missed it.** A5 has order 60 — it is the *first* group the paper's
advertised GAP iterator over non-solvable/simple groups of order up to 10^6 should have
visited. The printed conjecture therefore cannot be what their pipeline tested; the
likely actual predicate was "normal in the intersection" or a reversed containment
check. The "no counterexamples" status is an artifact of the validation pipeline, not
evidence about the printed statement.

## 3. Verification procedure

**Clean-room checker: `check_a1_refutation.py`** (pure Python 3, stdlib only — json,
sys, itertools; exact integer/set arithmetic; no floats, no group-theory libraries).
Written at Gate 4 by an independent verifier from the construction description in
`refuted-claims.json` only (clean-room protocol: the discoverer's scratch scripts were
never opened). On every run it rebuilds everything from first principles:

1. validates the frozen verbatim statement, solubilizer definition, conventions, and
   provenance fields in the certificate against hard-coded frozen strings (statement
   tampering ⇒ REJECT);
2. constructs A5 as the 60 even permutations and exhaustively verifies the group axioms
   (closure under composition and inverse, identity);
3. verifies G is non-solvable via the derived-series fixpoint;
4. for each certified pair: recomputes Sol_G(x) and Sol_G(y) **from the definition**
   (subgroup closure + derived-series solubility test for all 60 candidates), and
   demands exact equality with the certificate's sets and orders;
5. verifies the conjecture's hypothesis holds (intersection non-empty, contains 1);
6. verifies the conclusion fails, twice over: (F1) every non-identity g in the
   intersection has normal closure ⊄ intersection; (F2) simplicity certificate — all 59
   non-identity normal closures equal G, and |intersection| < |G|;
7. verifies the structural side-claims (Sol is a subgroup, non-abelian, order 10);
8. requires reading coverage: at least one certified pair with x = y AND one with x ≠ y.

Usage (any machine with Python 3; runs in seconds, no dependencies):

```
python check_a1_refutation.py certificate_a1_a5.json    # exit 0 + ACCEPT
python gen_certificate.py                               # regenerates the certificate
python mutation_test.py                                 # 13 corruptions, all must REJECT
```

Fresh Gate-5 re-run (2026-06-11): ACCEPT, exit 0, both pairs reported as
|Sol(x)| = 10, |Sol(x) ∩ Sol(y)| = 10, non-empty, no non-trivial normal subgroup of G.

**Independent second implementation: orchestrator harness.** The orchestrator's
`problems/p2-factory/verify_kills.py` (one level up) contains an [A.1] section written
independently of this directory's checker, using a *different decision route*: it
recomputes Sol_A5(x) from scratch and then searches for a non-trivial normal subgroup of
A5 inside Sol ∩ Sol by enumerating the subgroups generated by up to 3 elements of Sol
and testing normality directly (rather than via normal closures / simplicity). Fresh run
2026-06-11:

```
[A.1] |A5|=60 |Sol(x)|=10 (expected 10, D10) PASS
[A.1] nontrivial normal subgroup of A5 inside Sol n Sol: found=False -> REFUTED: PASS
```

**Mutation testing** (`mutation_test.py`; fresh run 2026-06-11): pristine certificate
accepted; **13/13 mutants rejected** — statement typo (m1), x replaced by an odd
permutation (m2), element smuggled into / dropped from Sol(x) (m3, m4), intersection
inflated to all of G (m5), x = y = identity — a pair where the conjecture is *true* and
the bookkeeping is internally consistent — rejected on the mathematical core check
(m6), non-permutation entry (m7), y swapped with stale Sol(y) (m8), wrong order claim
(m9), empty pairs list (m10), distinct-pair coverage dropped (m11), tampered solubilizer
definition (m12), duplicate intersection entry (m13, designed by Codex). Mutant m6
proves the checker is not a rubber stamp: it rejects a well-formed certificate for an
instance where the conjecture actually holds.

**Hostile Codex cross-examination** (GPT-5.5, full shell + network access, 2026-06-11,
thread `019eb9a0-27f7-7b90-8e4a-fe1919261cbb`; verbatim verdicts in
`verification_log.txt`). Round 1: Codex independently re-downloaded the arXiv v1 source
(same sha256), confirmed the statement, its A.1 numbering (by PDF extraction), and the
absence of a v2 rescue; recomputed the counterexample **with its own code** — |A5| = 60,
Sol_A5(x) = N_A5(⟨x⟩) of order 10, Sol_A5(x) = Sol_A5(x²), both intersections of size
10, A5 non-solvable and simple; tried and failed to break the checker; verdict
"**VALID KILL**", flagging two hardening opportunities (unvalidated metadata fields; no
enforced x ≠ y pair). Both were implemented (frozen metadata checks; reading-coverage
requirement; mutants m11–m13). Round 2 re-audit: "Verdict remains VALID KILL … pristine
accepts, all 13 mutants reject, and m6 still fails on the normal-closure core check
before the new coverage check, so the additions do not mask the mathematical test."

**Bundle integrity (sha256).**

```
c5345138ab6944a7fade95da90675b31cf3fae92db9c3fd7507b47fb8560f96f  certificate_a1_a5.json
282f1538a00d497ca2f53d11955b462e4e7812ab867abcc88f9b5141d08a94a4  check_a1_refutation.py
98fd2d0c76acc572581ec708492e877f8fec8d4adee83aeed9f0b007c1305af5  mutation_test.py
2d40976d84aec0a712a68ad7feb2e041420d8d7dab34abf9a0dffe2cb672ebe1  gen_certificate.py
9ee18ee8ca5822f3fe285a0caeb2ceda6b7f8a2cf1625c3e6011bda1458f0509  src/2412.16177.tar.gz
229608521516e9f72a6f923e68dc934dfdee22d9c469553f0c4af4d23f4e3f4a  src/main.tex
```

**Reproduce in under an hour** (actually under a minute): run the three commands above,
observe ACCEPT / 13-of-13 REJECT; optionally run
`python ../../verify_kills.py` and observe the [A.1] PASS lines; optionally diff the
statement in `certificate_a1_a5.json` against `src/main.tex` lines 445–447.

## 4. Extension findings (beyond the single counterexample)

- **Both readings of "two elements" are killed.** Pair 0 (x = y) and pair 1 (x ≠ y,
  y = x²) are certified, and the checker *requires* both; no quantifier reading
  survives.
- **Full ⟨x,y⟩ census at x = (0 1 2 3 4)** (Codex's independent computation, matching
  ours): of the 60 choices of y, 5 give ⟨x,y⟩ = C5 and 5 give the order-10 dihedral
  group (these 10 form Sol_G(x) = N_A5(⟨x⟩)); the remaining 50 give ⟨x,y⟩ = A5. So
  Sol_A5(x) coincides exactly with the normalizer of ⟨x⟩.
- **The charitable variant is NOT refuted by this object.** Reading the conclusion as
  "contains a non-trivial normal subgroup of the *intersection*" makes the statement
  true in this instance (Sol_G(x) here is the subgroup D10, normal in itself) — exactly
  as anticipated by the claim record's residual-risk note. Killing that variant, if
  desired, needs a different witness.
- **Novelty caveat (Codex literature check).** No prior published refutation of the
  printed Conjecture A.1 was found, but the refuting ingredient — Sol_A5(5-cycle) =
  D10 of order 10 — follows immediately from the pre-existing solubilizer
  classification for minimal simple groups (Akbari–Chuharski–Sharan–Slonim,
  arXiv:2309.09104, PSL(2,4) = A5 row), a paper co-authored by one of the authors of
  the source paper. This is a correct kill of a sloppily validated LLM conjecture, not
  a deep new computation.
- **Pipeline diagnosis confirmed.** The paper claims validation over all
  non-solvable/simple groups of order up to 10^6, yet the conjecture fails at A5 — order
  60, the first group such an iterator visits. This confirms the claim record's
  diagnosis that the GAP validation tested a different predicate than the one printed,
  and it calibrates how much trust the paper's other "no counterexamples" labels
  deserve (see sibling kills A.13, A.16 for the never-validated pile).
- **Infinite family for free.** Any non-abelian simple group G with Sol_G(x) proper for
  some x refutes A.1 at (x, x) by the same argument (only non-trivial normal subgroup is
  G itself); A5 is simply the smallest natural instance.

## 5. Openness re-check (fresh kill-check, 2026-06-11)

Searches run on 2026-06-11 (Gate 5, same day as the Gate-4 verification), hunting for
any prior or just-published refutation of this exact conjecture:

| # | Query / fetch | Result |
|---|---|---|
| 1 | Web search: `arXiv 2412.16177 "Mining Math Conjectures" refutation counterexample solubilizer` | Only the paper itself (arXiv abs/pdf/html) plus unrelated spectral-graph refutation papers (2409.18626, 2207.03343). No refutation of A.1. |
| 2 | Web search: `solubilizer conjecture counterexample "normal subgroup" alternating group A5 2025 2026` | Normalizer–Solubilizer Conjecture (arXiv:2501.11486), profinite solubilizers (arXiv:2310.02034), the source paper's OpenReview copy. Nothing refuting A.1. |
| 3 | Semantic Scholar citation graph for arXiv:2412.16177 (API, `/citations`) | 3 citing papers (genetic-programming conjecture discovery 2026; "The Agentic Researcher" arXiv:2603.15914; LLM constraint-solving arXiv:2603.03668). None group-theoretic; none refute any appendix conjecture. |
| 4 | Fetched OpenReview forum `aYlKvzY6ob` (NeurIPS 2024 MATH-AI — the source venue) | No public comments/replies mentioning counterexamples, errata, or A.1/A5. |
| 5 | Web search: `"Sol_G(x)" OR "SolG(x)" intersection "non-trivial normal subgroup" conjecture false` | Established solubilizer literature only (arXiv:2501.11486, 2310.02034, 2309.09104, 2210.11564, 2202.09563, 2112.04220, 1909.12043, 1806.01012). None addresses A.1 or intersections of two solubilizers containing normal subgroups. |
| 6 | arXiv API: `all:"solubilizer"`, 30 most recent by submission date | Newest group-theoretic item is 2501.11486v3 (2025-06-10, different conjecture); every other 2025–2026 hit is chemistry/physics. No paper refutes or even cites 2412.16177's appendix conjectures. |
| 7 | Web search: `"Mining Math Conjectures" Chuharski "Conjecture A.1" OR "appendix" refuted OR false OR erratum` | Only copies of the paper (arXiv, OpenReview, ResearchGate). No erratum, no refutation. |
| 8 | Fetched <https://arxiv.org/abs/2412.16177> | Submission history still shows **v1 only** (2024-12-09); comments field "23 pages, 10 figures, NeurIPS MathAI Workshop 2024"; no errata/withdrawal note. |

This matches the independent prior-art search Codex ran during the Gate-4
cross-examination (also 2026-06-11, also empty: "no explicit published refutation of
this specific Conjecture A.1"). **Conclusion: no prior or concurrent refutation of
Conjecture A.1 found as of 2026-06-11.** As always, web searches are evidence of
novelty, not proof.

## 6. What this does not show

- **Not a deep new theorem.** A.1 is an LLM-generated (Claude) conjecture from a
  December 2024 methods paper; its refutation is mathematically elementary, and the
  decisive fact (Sol_A5(5-cycle) = D10, order 10) was already implicit in the existing
  minimal-simple-groups solubilizer classification (arXiv:2309.09104). The substantive
  contribution is the documented, machine-checkable demonstration that the paper's
  "no counterexamples" label is wrong for the statement as printed — a data point about
  LLM-conjecture validation pipelines, with modest group-theoretic weight.
- **The charitable variant survives this witness.** "Sol_G(x) ∩ Sol_G(y) contains a
  non-trivial normal subgroup *of the intersection*" holds trivially in this instance
  (the intersection is itself a subgroup). We refute only what the paper printed
  ("of $G$").
- It says nothing about the *other* conjectures of arXiv:2412.16177 beyond the sibling
  kills in this factory (A.13, A.16); the remaining appendix conjectures are untouched,
  and the genuine solubilizer literature (e.g. the Normalizer–Solubilizer Conjecture,
  arXiv:2501.11486) is unaffected and remains open.
- It does not show A.1 fails in *every* non-solvable group: in any group with
  non-trivial solvable radical R(G), the radical lies in every solubilizer, so
  R(G) ⊆ Sol_G(x) ∩ Sol_G(y) and the conclusion *holds* there. The conjecture fails
  precisely in the simple-group regime — the regime the paper claims to have tested
  most thoroughly.
- We cannot reconstruct what predicate the authors' GAP code actually evaluated (the
  paper does not publish the generated code for this conjecture); "they tested a
  different predicate than printed" is an inference from the order-60 miss, not an
  audited fact about their code.
- Novelty rests on the dated searches in section 5 — evidence, not proof.

## 7. Publication grouping

**Publication grouping:** bundle with the other two solubilizer kills —
`solubilizer-a13` (A.13: normal core of Sol_G(x) vs. hypercenter; killed by
G = A5 × S3) and `solubilizer-a16` (A.16: Sol_G(x) ∩ N_G(Sol_G(x)) metabelian; killed
by G = A5 × S4) — as a single note ("Counterexamples to the LLM-generated solubilizer
conjectures of arXiv:2412.16177"): all three share the source paper, the same
solubilizer definition, and a common moral (the validation pipeline's simple-groups
blind spots). Within that note, A.1 is the headline item because it is the only one of
the three the source paper claims to have machine-validated. The two Graffiti spectral
kills (`graffiti-143`, `graffiti-154`) form a separate natural bundle (same
Written-on-the-Wall source, same ECAI-2025 openness evidence), and the two
TxGraffiti-family kills (`davila-conj9`, `pandey-parity`) a third; A.1 belongs in
neither of those.

## Files in this directory

| File | Role |
|---|---|
| `WRITEUP.md` | this document |
| `certificate_a1_a5.json` | the certificate (frozen statement + two certified pairs with full solubilizers) |
| `check_a1_refutation.py` | clean-room checker, pure Python 3 stdlib, exact arithmetic |
| `gen_certificate.py` | regenerates the certificate from scratch |
| `mutation_test.py` | checker validation: 13/13 mutants rejected, pristine accepted |
| `verification_log.txt` | Gate-4 log: provenance, recomputation, hashes, verbatim Codex verdicts |
| `src/` | frozen arXiv v1 e-print source (tarball + extracted `main.tex`, style file, figures) |
| `../../verify_kills.py` | orchestrator's independent second implementation (section [A.1]) |
