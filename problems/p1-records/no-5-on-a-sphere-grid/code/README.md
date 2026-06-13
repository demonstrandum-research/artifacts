# Gate-2 tooling: no-5-on-a-sphere grid (AlphaEvolve Problem 6.60, n=13)

Exact-arithmetic certificate checker + incremental Rust search core for finding
34 points in {0..12}^3 with no 5 points on a common sphere or plane.
All arithmetic is exact integer (i64 internally, proof-bounded i32 hot path).
**No floats anywhere.**

## Layout

- `check_cert.py` — certificate checker, pure int Python (~30-line core).
- `core/` — Rust crate `no5core`: library + CLI binary.
  - `core/src/lib.rs` — cofactor-vector engine, `SearchState` (incremental
    blocked-cell maintenance), brute-force reference paths, unit tests
    (including the rank-degenerate-quadruple trap tests).
  - `core/src/ils.rs` — baseline ILS (attack angle 6): faithful port of the
    published evolved n=12 recipe with the admitted harness bug fixed (shared
    deduplicated elite population, reservoir-sampled, across threads). Two
    arms: `pure` (verbatim recipe, control) and `fixed` (elite re-seeding on
    the restart branch). Writes STATUS.json + found_sets_<ts>.jsonl + immediate
    CANDIDATE34 dumps to the chosen out dir. Code reviewed by Codex
    (thread 019eb9c8-edf7-7753-bd6a-d86048c0273b) before the first long run.
  - `core/src/main.rs` — CLI: `check` / `saturation` / `witness` / `bench` /
    `ils <out_dir> [--secs S] [--threads T] [--pure P] [--seed X]`.
  - `core/examples/profile.rs` — phase profiler (remove vs add vs cofactor vs scan).
- `validate_gate2.py` — Gate-2 orchestrator; writes `out/gate2_status.json`.
- `out/` — generated artifacts: `s12.json` (published 33-point record as a
  plain JSON list), `s12_bad34.json` (known-bad 34-set), shifted translates,
  status JSON.

## Build

```
cd core
cargo build --release        # target-cpu=native via core/.cargo/config.toml
cargo test --release         # 10 unit tests incl. 5 degenerate-quadruple traps
```

Scan kernel selects at compile time: AVX-512 (this machine) > AVX2 > portable
scalar. All three paths pass the full test suite
(`$env:RUSTFLAGS="-C target-cpu=x86-64"` to force scalar, etc.).

## Run

```
# exact full certificate check (all C(m,5) lifted 4x4 determinants, exit 0/1)
core\target\release\no5core.exe check out\s12.json 13

# incremental engine: addable-cell report; --brute cross-validates the whole
# blocked grid against an independent det5 recount
core\target\release\no5core.exe saturation out\s12.json --brute

# one blocking quadruple for a given cell
core\target\release\no5core.exe witness out\s12.json 0 0 0

# benchmark: remove+re-add churn at |S|=33 with full grid maintenance
core\target\release\no5core.exe bench out\s12.json --secs 5 --threads 1

# python checker (exit 0 = VALID)
python check_cert.py out\s12.json 13

# full Gate-2 validation (all steps below)
python validate_gate2.py
```

## Gate-2 validation status (2026-06-11): ALL PASS

1. Python checker accepts all six published records (n=7..12), incl. the
   33-point n=12 record as an n=13 certificate.
2. Known-bad 34-set (33-record + (0,0,0), which completes the zero 5-subset
   {(5,9,10),(6,10,6),(7,2,0),(0,9,2),(0,0,0)}) is rejected by both checkers.
3. `cargo test --release`: 10/10, incl. trap tests proving 4-collinear and
   4-cocircular quadruples yield the zero cofactor vector and block ALL 2197
   cells (axis/skew lines; axis-aligned, rotated and tilted-plane rectangles).
4. Rust dual checker agrees with the Python checker (VALID 33 / INVALID 34).
5. Saturation: 0 addable cells for the 33-record, for all 8 translates by
   {0,1}^3 — together covering the dossier's 2711-cell {-1..12}^3 scan.
   Incremental grid == brute-force det5 recount (40,920 quads x 2197 cells).
6. Benchmark (see below).

## Engine design

For each 4-subset Q of S keep the cofactor vector c_Q in Z^5 with
`dot(c_Q, (x,y,z,x^2+y^2+z^2,1)) == det5(Q,p)` for every p. Cell p is addable
iff no dot product vanishes; `blocked[cell]` counts vanishing quadruples and is
maintained incrementally on add/remove. Rank-degenerate quadruples give
c_Q = 0, the dot product vanishes everywhere, and the scan therefore blocks
every cell automatically — the trap that breaks sphere-center hashing.

Overflow proof (n=13): cofactor components <= 17,915,904; max |dot| over the
grid <= 89,579,520 < 2^29; enforced at runtime by `narrow_checked`, so the i32
SIMD path cannot silently overflow (and the 2^30 SIMD pad lane can never alias
a real zero).

Scan kernel: dot factors as gx(x) + ty(y) + tz(z), so one (x,y) column is a
single 16-lane broadcast-add-compare against the padded z-table; branch-free
mask stores + vptest hit harvesting (avg ~5 hits per quadruple).

## Benchmark (Ryzen 9950X3D; |S|=33, full blocked-grid maintenance)

Per remove+re-add cycle the engine processes C(32,3)=4960 quadruples
(cofactor + 2197-cell zero-scan each) and re-determines addability of every
grid cell. Best-stable measurements (HIGH priority; machine otherwise carried
unrelated 100%-load background jobs which suppress memory-bound phases up to
~3-5x — register-bound phases are immune):

- cofactor_vec: 12-14 ns/quadruple (stable under any load)
- add_point: 1.17 ms; remove_point: 0.19 ms => 1,456 state transitions/sec/thread
- primitive incremental zero-tests resolved: 7.9e9 /sec/thread
  (worst observed under full contention: 1.9e9 /sec/thread — both >> 1e6 target)
- amortized cell-addability determinations: 1.6e6 /sec/thread
  (contended: 3.8-4.8e5 /sec/thread)
- 32-thread aggregate under contention: 5,087 adds/sec, 5.5e10 zero-tests/sec

## Cautions

- CLI input must be a *plain* JSON array of [x,y,z] triples (the minimal
  parser rejects dicts like data/records.json — extract the list first, see
  validate_gate2.py).
- `blocked[]` for an occupied cell includes C(|S|-1,3) trivial self-incidences
  (quads containing the point block its own cell); `is_valid_set()` accounts
  for this exactly.
- The official notebook's float verifier is NOT a certificate; only the exact
  integer checkers here are.
