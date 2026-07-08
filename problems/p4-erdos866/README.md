# Erdős problem #866 — the eventual value of h₄, and improved bounds (release 2026-07-08)

Release artifact set for the paper *"The eventual value of h₄, and improved
bounds for the Choi–Erdős–Szemerédi pairwise-sums problem (Erdős #866)"*
(Draft v5, frozen 2026-07-08; [`paper/draft-866.pdf`](paper/draft-866.pdf)).
Notation is van Doorn's g/h convention: for A ⊆ {1,…,2n}, g_k(n) is the least
m such that |A| ≥ n+m forces k distinct integers b₁,…,b_k (at most one
non-positive) with all pairwise sums b_i+b_j ∈ A; h_k is the variant with all
b_i distinct **positive** integers.

## Headline results

- **h₄(n) = 4 for all n ≥ 331,777** — the eventual value of the constant
  Choi, Erdős and Szemerédi (1975) proved exists ("we were too lazy to
  determine t"), under the modern positive-variant convention. Both halves
  verified by the Lean 4 kernel (`Erdos866.h4_eq_4`).
- En route: **4 ≤ h₄(n) ≤ 1000 for all n ≥ 3** (both halves kernel-verified;
  previous published/Lean bound 2270), giving with van Doorn's g₄ = 3 the
  first strict g/h separation beyond k = 3 (kernel-verified).
- **g₅(n) ≤ 3,519,219 for all n** (kernel-verified; previously 113,591,719
  in the paper, < 1.2·10⁸ in the formalization) — factor 32, by removing the
  disjoint-representations loss from the CES recursion via a forbidden-set
  variant of van Doorn's Lemma 7, proved in Lean at general k.
- **h₅(n) ≥ #{Fibonacci ≤ n} + 1** (family inequality kernel-verified),
  improving log₂ n by the asymptotic factor 1/log₂ φ ≈ 1.44.
- **Exact values** (frozen 298-cell set, k ≤ 6 initial segments): h₄(n) = 4
  on {3,4} ∪ [6,64] with h₄(5) = 5; g₅(n) = 4 for 15 ≤ n ≤ 23 and
  g₅(n) = 5 for 5 ≤ n ≤ 14 — bearing on van Doorn's question whether
  g₅(N) ≤ 4 for all large N.

## Evidence grades (the paper's own grading, header of `paper/draft-866.md`)

- **[K] kernel** — Lean 4, sorry-free, axioms exactly
  `[propext, Classical.choice, Quot.sound]`. All four headline bounds above.
- **[E] exact-computational** — each nontrivial cell certified by **dual
  independent SAT engines** with an archived DRAT/LRAT proof checked by the
  **formally verified checker cake_lpr**. The 298 exact cells
  (273 nontrivial + 25 trivial m = n).
- **[P] paper-grade / [D] derivation-grade** — the paper marks the remaining
  material (e.g. the conditional §10 structural route toward g₅ = 4, which
  is a route, **not** a theorem: three named gaps remain) at explicitly
  sub-[K] grades, claim by claim.

## Layout

- [`paper/`](paper/) — frozen Draft v5: PDF, markdown source, tables
- [`lean/`](lean/) — the complete Lean 4 development (pinned toolchain
  `leanprover/lean4:v4.28.0`, pinned mathlib `8f9d9cff`; van Doorn's public
  formalization vendored **byte-identical** in `lean/Erdos866/Upstream.lean`,
  sha256 `043731e3…9845e` — see [`lean/SETUP.md`](lean/SETUP.md))
- [`release/2026-07-08-freeze/`](release/2026-07-08-freeze/) — the frozen
  release evidence, verbatim, with sha256s in
  [`FREEZE.md`](release/2026-07-08-freeze/FREEZE.md): canonical 298-cell
  verification report (n_failed = 0, multi-run assembly disclosed), the
  pinned SAT-archive manifest, the late-cell dual-engine belt report, the
  Lean axiom-audit logs, and the paper
- [`verification/`](verification/) — the scripts that produced those reports:
  `verify_canonical_c5.py` (+ resume harness) recomputes every cell,
  `verify_new_cells_c5.py` is the dual-engine belt, `check_gate.py` is the
  mechanical release gate (G1–G3)
- [`sat/`](sat/) — the DRAT/LRAT certificate-archive **manifest** (per-cell
  sha256 for every CNF, DRAT and LRAT file + cake_lpr/drat-trim verification
  flags), the archive builder, and the semantic cross-check + mutation-test
  scripts with their outputs
- [`RETRIEVAL.md`](RETRIEVAL.md) — where the 4.4 GB certificate archive
  itself lives (Zenodo; it is deliberately not in this git repo)

## Verify it yourself

**Kernel claims.** Build the Lean project and run the audit scripts
(expect axioms exactly `propext, Classical.choice, Quot.sound`, zero
`sorryAx`; frozen audit logs `auditC4P1.log.txt`, `auditC4Synth.log.txt`
in the freeze dir):

```
cd problems/p4-erdos866/lean
lake build
lake env lean scripts/AuditC4P1.lean
lake env lean scripts/AuditC4Synth.lean
```

See [`lean/SETUP.md`](lean/SETUP.md) for the pinned-version table (the
project deliberately pins to upstream's v4.28.0, not this repo's v4.30.0).

**Certificate claims.** Download the certificate archive (see
[`RETRIEVAL.md`](RETRIEVAL.md)), check per-file sha256 against
[`sat/manifest.json`](sat/manifest.json) (whose own sha256,
`45f0eedc…1400e`, is pinned in `release/2026-07-08-freeze/FREEZE.md`), then
re-run cake_lpr / drat-trim per cell, or re-verify every cell from scratch
with `verification/verify_canonical_c5.py`.

## Scope note

The frozen, claimed set is exactly the 298 cells above (h₄ endpoint 64,
g₅ endpoint 23). Ladder cells computed after the freeze (h₄ 65–68,
g₅ 24–25) are **not** in the certified set and are claimed nowhere.

## Provenance / AI disclosure

Same protocol as the rest of this repository (see the root README): the
mathematics was produced by a verification-first multi-agent AI workflow;
nothing is accepted on a model's word; the paper carries a full
AI-authorship statement (§12) and grades every claim. John Erlbacher
(erlbacher.research@gmail.com, ORCID 0009-0003-6851-4139) directed the
campaign and takes full responsibility for the claims.
