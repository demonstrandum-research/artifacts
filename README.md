# Demonstrandum — wave-1 verified artifacts

This repository contains the complete verification artifacts accompanying five
papers by **John Erlbacher**:

| paper | result |
|---|---|
| `papers/borsuk/` | Discrete Borsuk: Conjecture 3 of arXiv:2508.20009 disproved, **kernel-checked in Lean 4** |
| `papers/elizalde-luo/` | The {1132, 3312} conjecture of Elizalde–Luo (DMTCS 27:1) resolved: count = 3^n − 3·2^(n−1) + 1 for all n |
| `papers/sun-46/` | Sun's Conjecture 4.6 (arXiv:2108.07723) refuted |
| `papers/no5sphere-record/` | C(13) ≥ 36 for the "no 5 on a sphere" grid problem (prior published bound: C(12) ≥ 33) |
| `papers/graffiti-143-154/` | Graffiti Conjectures 143 and 154 refuted |

All results were produced with **Demonstrandum**, a verification-first
multi-agent AI pipeline. The house rule: no claim is accepted on an AI's word —
the unit of progress is an artifact on disk plus a checker that accepts it, and
every claimed result here is **mechanically checkable by you, with zero trust
in any AI or in the authors**. Statements were frozen verbatim from the
authoritative sources before any attack; every certificate is accepted by
independently written checkers (different agents, where possible different
languages), hardened by mutation testing and hostile cross-model audits.

The full catalog — exact claims with verbatim source quotes, verification
grades, per-result commands, and explicit "what this does NOT show" caveats —
is in [`RESULTS.md`](RESULTS.md). [`VALIDATION.md`](VALIDATION.md) is the guide
for an outside mathematician: what each check does and does not establish.

## Results at a glance

| # | result | grade |
|---|---|---|
| 1 | IRIS Conjecture 6.1 ("NuevaMirada") — refuted | dual-checker |
| 2 | Borsuk Conjecture 3 (arXiv:2508.20009) — disproved in Lean 4 | **kernel** |
| 3 | Graffiti Conjecture 143 — refuted | dual-checker |
| 4 | Graffiti Conjecture 154 (std-dev reading) — refuted | dual-checker |
| 5 | TxGraffiti/Davila Conjecture 9 — refuted | dual-checker |
| 6 | Pandey parity conjecture — refuted (both directions) | dual-checker |
| 7 | Solubilizer Conjecture A.1 (arXiv:2412.16177) — refuted | dual-checker |
| 8 | Solubilizer Conjecture A.13 — refuted | audit-panel |
| 9 | Solubilizer Conjecture A.16 — refuted | audit-panel |
| 10 | Sun Conjecture 4.6 (arXiv:2108.07723) — refuted | dual-checker |
| 11 | Koch–Narayan Conjecture 1 — refuted | dual-checker |
| 12 | C(13) ≥ 36 record ("no 5 on a sphere") | dual-checker |
| 13 | Elizalde–Luo {1132, 3312} conjecture — resolved (audited proof, not kernel-checked) | audit-panel |

Grades (defined precisely in `RESULTS.md`): **kernel** = the entire claim is a
Lean 4 theorem accepted by the Lean kernel with only the three standard mathlib
axioms; **dual-checker** = certificate accepted by ≥ 2 independently written
checkers plus mutation testing; **audit-panel** = banked runnable checker plus
adversarial clean-room audits across model families.

## Quickstart

```
git clone <this repo>
cd <repo>
python verify_all.py          # default battery, ~5-15 min
python verify_all.py --full   # adds long redundant layers, ~25-30 min
python verify_all.py --strict # SKIPs become failures (full zero-trust mode)
```

Requirements: Python 3.10+ with `numpy` and `sympy`. Prebuilt Windows x64 Rust
checker binaries are included (`target/release/*.exe`); on other platforms (or
if deleted) they are rebuilt automatically when `cargo` is installed.

**Lean (Borsuk kernel check):** the Lean sources, pinned toolchain
(`leanprover/lean4:v4.30.0`) and pinned manifest (mathlib `v4.30.0`) are
included, but the multi-GB `.lake/` dependency/build cache is not. To run the
kernel verification:

```
cd problems/p3-moonshot/borsuk/lean
lake update     # resolves pinned deps; mathlib's hook fetches the build cache
lake build      # expect "Build completed successfully"
lake env lean scripts/CheckAxioms.lean   # axiom audit: only propext, Classical.choice, Quot.sound
```

See `problems/p3-moonshot/borsuk/lean/SETUP.md` for the full pinned-version
table and troubleshooting. Until you do this, `verify_all.py` reports the two
Borsuk Lean checks as SKIP with the same instructions (a SKIP always means
"not verified on this machine" — the summary says so loudly).

## Layout

- `RESULTS.md`, `VALIDATION.md`, `verify_all.py` — catalog, reading guide, master battery
- `papers/` — the five paper sources + PDFs, with build notes (`BUILD.md`),
  referee-round responses (`RESPONSES.md`), and recompute scripts
- `problems/p0-iris/` — IRIS 6.1 counterexamples: certificates, dual checkers (Python + Rust), mutation suite
- `problems/p2-factory/kills/` — one directory per refuted conjecture: frozen statement,
  certificate, checkers, mutation suites, writeups; `verify_kills.py` re-derives five kills from scratch
- `problems/p2-factory/attacks/sun-46/` — the clean-room verification side of the Sun 4.6 kill
  (exact subset-DP layer, exact cyclotomic layer, CRT uniqueness proof, original logs)
- `problems/p1-records/no-5-on-a-sphere-grid/` — the C(13) ≥ 36 certificate, three checker routes,
  hostile cross-model checker, provenance, and the construction-mining writeup with verified sets
- `problems/p3-moonshot/borsuk/` — Lean 4 project (kernel proof), paper source, status
- `problems/p3-moonshot/elizalde-luo/` — pinned definitions, ground-truth enumerators
  (Python/Rust/clean-room), audited proof drafts, spot-audit, Lean scaffolding (not part of the claim)

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

## License

- **Code** (all scripts, checkers, Rust crates, Lean sources): MIT — see [`LICENSE`](LICENSE).
- **Text and data** (writeups, papers, certificates, JSON artifacts): CC BY 4.0 — see [`LICENSE-CC-BY-4.0.md`](LICENSE-CC-BY-4.0.md).

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
(Elizalde–Luo) is explicitly graded as such in `RESULTS.md`. A human (the
author) directed the campaigns, audited the gates, and takes full
responsibility for the claims.
