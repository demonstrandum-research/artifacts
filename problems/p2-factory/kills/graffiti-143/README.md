# Kill bundle: Graffiti Conjecture 143 — Gate-4 clean-room verification

**Result.** Graffiti Conjecture 143 ("Written on the Wall", S. Fajtlowicz):
*"variance of positive eigenvalues ≤ size / average distance"* is **false**
for connected graphs, under both standard machine readings of "average
distance" (ordered-pairs-with-diagonal 2W/n², as in the Roucairol–Cazenave
search code, and distinct-pairs 2W/(n(n−1)), as in Aouchiche–Hansen).
Counterexamples: dumbbell graphs (two cliques joined by a path).
Smallest certified here: **n = 39** — dumbbell(7,12,20) — violating both
readings; **n = 37** — dumbbell(6,12,19) — violating the distinct-pairs
reading. (The discovery-session claim record had n = 40 as minimal; this
Gate-4 pass improved it.)

**Status before this work.** Open: listed "O", searched to size 100 with 8
algorithms, in Roucairol & Cazenave, ECAI 2025 (arXiv:2409.18626); no resolver
annotation in WoW (July 2004); passed the [BDF] refutation effort c. 1990–91;
no prior resolution found by web kill-checks (this session and Codex,
2026-06-11).

## Files

| file | role |
|---|---|
| `PROVENANCE.md` | frozen statement, decode method, conventions, openness evidence |
| `wow-july2004.pdf` | authoritative source (sha256 in log) |
| `wow_extracted_raw.txt`, `wow_decoded_test.txt`, `decode_wow.py` | PDF text decode chain (Type-3 glyph names, base-36) |
| `ecai2025.pdf`, `ecai2025_text.txt` | openness evidence (table row `143 O 100 any & tree -...-`) |
| `GenerateGraph.rs`, `calc.rs` | Roucairol–Cazenave formalization of conj. 143 (fetched from refutationGBR repo) |
| `certificate_g143.json` | **the certificate**: 5 instances, edge lists, exact rational claims |
| `checker_g143.py` | **the checker**: dual exact routes (sympy charpoly + isolation; pure-stdlib Berkowitz + quotient identity + Yun + Sturm + 2⁻⁷⁰ interval arithmetic); strict rational comparison, no floats in the accept path |
| `build_certificate.py` | regenerates the certificate |
| `mutation_tests.py` | 10 targeted corruptions, all must be (and are) rejected |
| `scan_dumbbells.py` | float scan of the whole dumbbell family n ≤ 48 (guidance, not certificate) |
| `local_search_probe.py` | heuristic beyond-family probe below record sizes |
| `verification_log.txt` | fresh run + hashes + mutation results |

## How to verify (under a minute, any machine with Python 3 + sympy + numpy)

```
python checker_g143.py certificate_g143.json   # expect: CHECKER VERDICT: ACCEPT, exit 0
python mutation_tests.py                       # expect: MUTATION TESTS: ALL KILLED
```

## Certified margins (exact rational lower bounds)

| instance | n | violates N2 (margin ≥) | violates PAIRS (margin ≥) |
|---|---|---|---|
| dumbbell(20,8,20) | 48 | +1.40597 | +2.82741 |
| dumbbell(8,12,20) | 40 | +0.49216 | +1.35218 |
| dumbbell(7,12,20) | 39 | +0.08040 | +0.95821 |
| dumbbell(6,12,20) | 38 | — | +0.50311 |
| dumbbell(6,12,19) | 37 | — | +0.07419 |

Mechanism: k positive eigenvalues = two large ≈(t−1) "clique" eigenvalues plus
k−2 small "path" eigenvalues; the variance grows like 2t²(k−2)/k² while
m/avg-dist grows like 2m/diam ≈ t²/k, so the LHS/RHS ratio → 2 as chains
lengthen — the conjecture fails asymptotically badly, e.g. dumbbell(40,10,40)
(n=90) violates by ~26% (float check; not part of the certificate).

## Codex cross-examination (GPT-5.5, full access, hostile-referee framing)

First pass: independently re-derived all five instances (numpy/mpmath),
confirmed statement fidelity from the decoded WoW text, tried alternate
readings (sample variance, size=n, average eccentricity — all still violated;
only illegitimate readings like "variance of ALL eigenvalues" survive),
searched FMS 1993 / arXiv / MATCH for prior resolution (none found). Flagged
one real bundle flaw (checker crashed printing "≤" on cp1252 consoles) and
two hygiene nits — all fixed. Final verdict: **"VERDICT: ACCEPT (kill
stands)"**.

## What this does not show

- Minimality is certified only within the dumbbell family (float-exhaustive
  scan n ≤ 48; nothing within 0.35 of either bound at n ≤ 36). Non-dumbbell
  counterexamples below n=37 are not excluded (heuristic probe found none).
- WoW's "≤" is non-strict; the violation is strict, as required.
- The n=90 asymptotic example is float-level color, not certified.
