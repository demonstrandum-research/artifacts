# Demonstrandum — wave-1 verified artifacts

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20673865.svg)](https://doi.org/10.5281/zenodo.20673865)
[![Code: MIT](https://img.shields.io/badge/code-MIT-blue.svg)](LICENSE)
[![Text & data: CC BY 4.0](https://img.shields.io/badge/text%20%26%20data-CC%20BY%204.0-lightgrey.svg)](LICENSE-CC-BY-4.0.md)
[![Repo size](https://img.shields.io/github/repo-size/demonstrandum-research/artifacts)](https://github.com/demonstrandum-research/artifacts)

**Demonstrandum** is a verification-first multi-agent AI mathematics pipeline,
directed and audited by John Erlbacher (Independent Researcher). Its house
rule: no claim is accepted on an AI's word — the unit of progress is an
artifact on disk plus an independently written checker that accepts it, so
every result below is mechanically checkable by you, with zero trust in any AI
or in the author. This repository is the complete wave-1 artifact bundle:
13 verified results (11 refutations of published conjectures, one proof of a
published conjecture, one numerical record), five accompanying papers, and a
one-command master verification battery.

- Exact claims, verbatim frozen statements, per-result caveats: [`RESULTS.md`](RESULTS.md)
- What each check does and does not establish (guide for an outside mathematician): [`VALIDATION.md`](VALIDATION.md)
- Archived, citable snapshot: DOI [10.5281/zenodo.20673865](https://doi.org/10.5281/zenodo.20673865)
- Contact: John Erlbacher — erlbacher.research@gmail.com — ORCID [0009-0003-6851-4139](https://orcid.org/0009-0003-6851-4139)

## Results

Grades, defined precisely in [`RESULTS.md`](RESULTS.md): **kernel** = the
entire claim is a Lean 4 theorem accepted by the Lean kernel with only the
three standard mathlib axioms; **dual-checker** = certificate accepted by ≥ 2
independently written checkers plus mutation testing; **audit-panel** = banked
runnable checker plus adversarial clean-room audits across model families.

| # | result | grade | paper | verify |
|---|---|---|---|---|
| 1 | IRIS Conjecture 6.1 ("NuevaMirada") — refuted | dual-checker | — | `python verify_all.py --only iris` |
| 2 | Discrete Borsuk Conjecture 3 (arXiv:2508.20009) — disproved in Lean 4 | **kernel** | [`papers/borsuk/`](papers/borsuk/) | `python verify_all.py --only borsuk` |
| 3 | Graffiti Conjecture 143 — refuted | dual-checker | [`papers/graffiti-143-154/`](papers/graffiti-143-154/) | `python verify_all.py --only g143` |
| 4 | Graffiti Conjecture 154 (std-dev reading) — refuted | dual-checker | [`papers/graffiti-143-154/`](papers/graffiti-143-154/) | `python verify_all.py --only g154` |
| 5 | TxGraffiti/Davila Conjecture 9 — refuted | dual-checker | — | `python verify_all.py --only dc9` |
| 6 | Pandey parity conjecture — refuted (both directions) | dual-checker | — | `python verify_all.py --only gp/` |
| 7 | Solubilizer Conjecture A.1 (arXiv:2412.16177) — refuted | dual-checker | — | `python verify_all.py --only a1/` |
| 8 | Solubilizer Conjecture A.13 — refuted | audit-panel | — | `python verify_all.py --only a13` |
| 9 | Solubilizer Conjecture A.16 — refuted | audit-panel | — | `python verify_all.py --only a16` |
| 10 | Sun Conjecture 4.6 (arXiv:2108.07723) — refuted | dual-checker | [`papers/sun-46/`](papers/sun-46/) | `python verify_all.py --only sun` |
| 11 | Koch–Narayan Conjecture 1 — refuted | dual-checker | — | `python verify_all.py --only kn/` |
| 12 | C(13) ≥ 36 record ("no 5 on a sphere") | dual-checker | [`papers/no5sphere-record/`](papers/no5sphere-record/) | `python verify_all.py --only no5` |
| 13 | Elizalde–Luo {1132, 3312} conjecture — resolved (audited proof, not kernel-checked) | audit-panel | [`papers/elizalde-luo/`](papers/elizalde-luo/) | `python verify_all.py --only eliz` |

Each result also carries an explicit "what this does NOT show" caveat in
[`RESULTS.md`](RESULTS.md) — claim calibration is part of the protocol.

## Quickstart

Requirements: Python 3.10+ with `numpy` and `sympy`. Prebuilt Windows x64 Rust
checker binaries are included; on other platforms they are rebuilt
automatically when `cargo` is installed.

```
git clone https://github.com/demonstrandum-research/artifacts.git
cd artifacts
python verify_all.py            # default battery: 33 checks, ~5-15 min
python verify_all.py --full     # adds long redundant layers, ~25-30 min
python verify_all.py --strict   # SKIPs become failures (full zero-trust mode)
python verify_all.py --list     # list all checks; --only SUBSTR runs a subset
```

Expected final line without a local Lean build cache (the two Borsuk Lean
checks SKIP with instructions rather than start a multi-hour mathlib build):

```
TOTAL: 31 PASS, 0 FAIL, 2 SKIP in ... s
WARNING: SKIPped checks mean the following results were NOT verified on this machine: Borsuk-C3
```

With the Lean build completed (next section): `TOTAL: 33 PASS, 0 FAIL, 0 SKIP`.
A SKIP always means "not verified on this machine" — the summary says so loudly.

## Papers

Five papers accompany the headline results. Each directory contains the LaTeX
source, the compiled PDF, build notes (`BUILD.md`), referee-round responses
(`RESPONSES.md`), and recompute scripts.

### Discrete Borsuk — [`papers/borsuk/note.pdf`](papers/borsuk/note.pdf)

*Counterexamples to a conjectured characterization of cubes.* Brose, De Loera,
Lopez-Campos and Torres proved that the lattice Borsuk number of a bounded set
S ⊂ Z^d is at most 2^d, and conjectured (arXiv:2508.20009, Conjecture 3) that
it equals 2^d iff conv(S) is unimodularly equivalent to a cube. The four-point
set {(0,0), (1,0), (0,1), (3,5)} has all pairwise differences primitive, so
its lattice Borsuk number is 4 = 2^2, while its hull contains 7 lattice points
and is therefore equivalent to no square. The disproof is formally verified: a
~1100-line Lean 4 development over mathlib proves `betaZ SA = 4`,
`latticeCount hullSA = 7`, and `conjecture3_false`; the axiom audit reports
only the three standard axioms. Two further counterexamples (exact arithmetic,
not formalized) close the natural repair in dimensions 2 and 3.

### Elizalde–Luo — [`papers/elizalde-luo/note.pdf`](papers/elizalde-luo/note.pdf)

*A proof of the Elizalde–Luo conjecture for nonnesting permutations avoiding
1132 and 3312.* Elizalde and Luo (DMTCS 27:1, 2025) conjectured from data for
n ≤ 8 that the number of nonnesting permutations of {1,1,…,n,n} avoiding both
1132 and 3312 is 3^n − 3·2^(n−1) + 1. The paper proves the conjecture with an
elementary, self-contained argument (Dyck shape carrying a label permutation;
avoidance forces prefix-interval labels; a two-coloring condition on crossing
arcs), plus a second, bijective proof onto an explicit ternary language. Every
lemma was verified mechanically far beyond the original data range, including
an exhaustive check over all 57,657,600 nonnesting words at n = 8. Graded
audit-panel: the general-n claim rests on the audited written proof, not a
Lean kernel.

### Sun 4.6 — [`papers/sun-46/note.pdf`](papers/sun-46/note.pdf)

*The sign pattern of Sun's trigonometric permanents.* Zhi-Wei Sun
(arXiv:2108.07723, Conjecture 4.6) conjectured sign patterns for two integer
sequences arising from permanents of trigonometric matrices. Part (ii) — hence
the conjecture as stated — fails at p = 29, the first prime beyond Sun's
published table: s_29 = 1,053,859 > 0 although 29 ≡ 5 (mod 12), and
s'_29 = −4,806,838,304 < 0 although 29 ≡ 5 (mod 8). Every value is certified
exactly by at least two of four independently written exact programs
(big-integer cyclotomic arithmetic; finite-field specialization with CRT
uniqueness proofs); the pipeline reproduces all nineteen of Sun's published
values. Part (i) survives all tests and remains open.

### No-5-on-a-sphere record — [`papers/no5sphere-record/note.pdf`](papers/no5sphere-record/note.pdf)

*A 36-point subset of the 13×13×13 grid.* For C(n), the largest subset of
{1,…,n}^3 with no five points on a common sphere or plane, the strongest
published lower bounds for 7 ≤ n ≤ 12 are due to AlphaEvolve, ending with
C(12) ≥ 33. The paper exhibits an explicit centrally symmetric 36-point subset
of {0,…,12}^3, proving C(13) ≥ 36. Verification is a finite exact-integer
computation — all 376,992 lifted 5×5 determinants are nonzero — reproduced by
a 21-line program printed in full and carried out by three independently
written checkers validated by mutation testing.

### Graffiti 143 & 154 — [`papers/graffiti-143-154/note.pdf`](papers/graffiti-143-154/note.pdf)

*Counterexamples to two conjectures of Graffiti on graph eigenvalues.* Two
spectral conjectures from Fajtlowicz's Graffiti program, both of which
survived the 1990–91 computational attack of Brewster–Dinneen–Faber and a
2025 eight-algorithm search, are refuted. Conjecture 143 fails on dumbbell
graphs (smallest certified counterexample: 39 vertices under both average-
distance conventions), with the two sides' ratio tending to 2. Conjecture 154
(standard-deviation reading) fails on lollipop graphs at 118/120 vertices,
with unbounded ratio. All counterexamples carry exact rational certificates
verified by two algorithmically independent routes per result.

## Lean projects

**Borsuk (the kernel-graded claim)** — `problems/p3-moonshot/borsuk/lean/`.
Pinned toolchain `leanprover/lean4:v4.30.0` and pinned mathlib manifest are
included; the multi-GB `.lake/` build cache is not. To run the kernel check:

```
cd problems/p3-moonshot/borsuk/lean
lake update     # resolves pinned deps; mathlib's hook fetches the build cache
lake build      # expect "Build completed successfully"
lake env lean scripts/CheckAxioms.lean   # expect only: propext, Classical.choice, Quot.sound
```

See [`problems/p3-moonshot/borsuk/lean/SETUP.md`](problems/p3-moonshot/borsuk/lean/SETUP.md)
for the full pinned-version table and troubleshooting. Once built,
`verify_all.py` picks the two Borsuk checks up automatically (33/33 PASS).

**Elizalde–Luo** — `problems/p3-moonshot/elizalde-luo/lean/` contains Lean
scaffolding only; it is **not** part of the claim, which is graded audit-panel
on the written proof.

## Layout

- [`RESULTS.md`](RESULTS.md), [`VALIDATION.md`](VALIDATION.md), [`verify_all.py`](verify_all.py) — catalog, reading guide, master battery
- `papers/` — five paper sources + PDFs, build notes, referee-round responses, recompute scripts
- `problems/p0-iris/` — IRIS 6.1 counterexamples: certificates, dual checkers (Python + Rust), mutation suite
- `problems/p2-factory/kills/` — one directory per refuted conjecture: frozen statement, certificate, checkers, mutation suites, writeups; `problems/p2-factory/verify_kills.py` re-derives five kills from scratch
- `problems/p2-factory/attacks/sun-46/` — clean-room verification side of the Sun 4.6 kill (exact subset-DP layer, exact cyclotomic layer, CRT uniqueness proof, original logs)
- `problems/p1-records/no-5-on-a-sphere-grid/` — the C(13) ≥ 36 certificate, three checker routes, hostile cross-model checker, provenance, construction-mining writeup
- `problems/p3-moonshot/borsuk/` — Lean 4 project (kernel proof), paper source, status
- `problems/p3-moonshot/elizalde-luo/` — pinned definitions, ground-truth enumerators (Python/Rust/clean-room), audited proof drafts, spot-audit, Lean scaffolding

## Differences from the internal working tree

This is a curated snapshot. For full transparency, every adjustment made while
staging it is listed here:

1. `verify_all.py`: the two Borsuk Lean checks now SKIP (with instructions)
   when `.lake/packages` is absent, instead of silently starting an hours-long
   from-scratch mathlib build. No other logic changed. The Lean checks were
   executed and PASSed against exactly these staged sources with the build
   cache present before release.
2. `problems/p1-records/no-5-on-a-sphere-grid/verification/codex_hostile_no5sphere_check.py`:
   the build machine's hardcoded absolute certificate path was replaced by the
   equivalent relative path (the certificate is byte-identical, sha256
   `333d36ec...` as recorded in RESULTS.md §12).
3. `problems/p2-factory/attacks/sun-46/` contains only the clean-room
   verification artifacts referenced by RESULTS.md §10 (checkers + original
   logs), not the attack-side working files.
4. Omitted: internal search/run directories (`runs/`, per-n binary pools,
   Rust `target/` build intermediates — the needed prebuilt `.exe` files are
   kept), `__pycache__`, the Elizalde–Luo internal audit work directories
   (except the banked `work/triage_spotcheck.py` used by `verify_all.py`),
   and third-party copyrighted material (e.g. the Sun and AlphaEvolve
   paper files); RESULTS.md cites the public sources for all of these.

## Methods and AI-use disclosure

The mathematical results in this repository were produced by Demonstrandum, a
verification-first multi-agent AI workflow built on Claude language models
(Anthropic), with adversarial cross-checks by a different model family (OpenAI
Codex/GPT) — the same disclosure carried in each paper. AI agents proposed
constructions, wrote checkers and proofs, and audited each other under a
protocol in which nothing is accepted on a model's word: every accepted claim
is backed by a machine-verifiable artifact in this repository (certificate +
independent checkers, or a Lean proof accepted by the kernel), and the one
result whose general-n statement rests on written proofs rather than a kernel
(Elizalde–Luo) is explicitly graded as such in `RESULTS.md`. Statements were
frozen verbatim from the authoritative sources before any attack. A human (the
author) directed the campaigns, audited the gates, and takes full
responsibility for the claims.

## Citing

Cite the archived snapshot via the Zenodo DOI (machine-readable metadata in
[`CITATION.cff`](CITATION.cff)):

```bibtex
@misc{erlbacher2026demonstrandum,
  author       = {Erlbacher, John},
  title        = {Demonstrandum --- wave-1 verified artifacts},
  year         = {2026},
  publisher    = {Zenodo},
  doi          = {10.5281/zenodo.20673865},
  url          = {https://doi.org/10.5281/zenodo.20673865},
  note         = {Code and verification artifacts, github.com/demonstrandum-research/artifacts}
}
```

For an individual result, please also cite the corresponding paper in
`papers/`.

## License

- **Code** (all scripts, checkers, Rust crates, Lean sources): MIT — see [`LICENSE`](LICENSE).
- **Text and data** (writeups, papers, certificates, JSON artifacts): CC BY 4.0 — see [`LICENSE-CC-BY-4.0.md`](LICENSE-CC-BY-4.0.md).
