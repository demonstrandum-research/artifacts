# checker_rs — independent Rust certificate checker for IRIS Conjecture 6.1

Independent verifier (written from the specification only, without consulting the
Python checker in `../checker_py/`) for counterexamples to Conjecture 6.1
("NuevaMirada") of the IRIS paper (Davila, De Loera, Eddy, Fang, Lu, Yang;
ICML 2025 AI4Math workshop, OpenReview id `v6Ulp3U1ZT`):

> If P is a simple 3-polytope with face vector (p3, p4, ..., pm), such that
> sum_{k>=7} pk >= 3, then p6 >= 39/20 + p3/2 - p5/4 - sum_{k>=7} pk.

A counterexample is a simple 3-polytope (by Steinitz's theorem: a 3-connected,
3-regular, simple planar graph) satisfying the hypothesis S = sum_{k>=7} pk >= 3
whose face vector violates the inequality. Since all `pk` are integers, the
violation is checked exactly in integer arithmetic:

```
20*p6 < 39 + 10*p3 - 5*p5 - 20*S
```

## Certificate format

Each non-empty line of the input file is `<n> <rotation>`: a plantri ascii
(`-a`) encoding of a planar **triangulation** T on n vertices — n comma-separated
adjacency lists in rotation (cyclic embedding) order, vertices written as the
letters `a`, `b`, `c`, ... The counterexample polytope graph G is the planar
**dual** of T, which this checker constructs explicitly from the traced faces
of T (it does not shortcut via vertex degrees of T).

## What is verified per line

1. **Parse**: exactly n adjacency lists over letters `a` .. chr(`a`+n-1), n >= 4.
2. **T is a simple rotation system**: no loops, no duplicate neighbors in any
   rotation (no multi-edges), symmetric adjacency.
3. **T is a planar triangulation**: explicit BFS connectivity; face tracing of
   the rotation system (successor of dart v->u is u->w with w the neighbor
   after v in the rotation at u) partitions all 2E darts into faces;
   V - E + F = 2 (genus 0, so the rotation system is a planar embedding);
   every traced face is a triangle.
4. **G = dual(T)**: built from the face incidences of T (dual vertex per face
   of T; dual rotation at a face lists the opposite face of each boundary dart
   in boundary order). G must be simple (no loops = no edge of T with the same
   face on both sides; no multi-edges = no two faces of T sharing two edges),
   **3-regular**, connected, and **planar** by the same Euler/face-trace
   criterion (V_G - E_G + F_G = 2).
5. **G is 3-connected** (brute force: deleting any 0, 1, or 2 vertices leaves
   the remainder connected). By Steinitz, G is then the graph of a 3-polytope,
   simple because G is 3-regular; its 2-faces are the traced faces of G.
6. **Face vector** (p3, ..., pm) of G computed from the traced face sizes of G;
   every face size must be >= 3.
7. **Hypothesis**: S = sum_{k>=7} pk >= 3.
8. **Exact integer violation**: 20*p6 < 39 + 10*p3 - 5*p5 - 20*S.

The program prints `COUNTEREXAMPLE CONFIRMED` (with the face vector and the
two sides of the integer inequality) for each line and exits with code 0 only
if **all** checks pass on **all** lines. Any failure prints a reason for that
line and the process exits nonzero (1 for a failed check, 2 for usage/I-O
errors or an input containing no certificate lines). Arithmetic uses `i64`
with overflow checks enabled even in release builds.

## Build

```
cargo build --release --manifest-path "C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_rs\Cargo.toml"
```

(Built with cargo 1.93.0; no dependencies outside the Rust standard library.)

## Run

```
C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_rs\target\release\checker_rs.exe "C:\Users\jacks\source\repos\maths\problems\p0-iris\certificates\cex10.txt"
```

or equivalently:

```
cargo run --release --manifest-path "C:\Users\jacks\source\repos\maths\problems\p0-iris\verification\checker_rs\Cargo.toml" -- "C:\Users\jacks\source\repos\maths\problems\p0-iris\certificates\cex10.txt"
```

## Result on `certificates/cex10.txt` (2026-06-11)

All 5 certificates confirmed (exit code 0). Each dual graph G has V=16, E=24,
F=10 (n=10 triangulation faces -> 16 dual vertices since F_T = 2n-4):

| line | face vector of G                  | S | 20*p6 | 39+10*p3-5*p5-20*S |
|------|-----------------------------------|---|-------|---------------------|
| 1    | p3=3 p4=3 p5=1 p7=2 p8=1          | 3 | 0     | 4                   |
| 2    | p3=4 p4=1 p5=2 p7=2 p8=1          | 3 | 0     | 9                   |
| 3    | p3=3 p4=3 p5=1 p7=2 p8=1          | 3 | 0     | 4                   |
| 4    | p3=5 p5=1 p6=1 p7=2 p8=1          | 3 | 20    | 24                  |
| 5    | p3=4 p5=3 p7=3                    | 3 | 0     | 4                   |

Each line satisfies the hypothesis (S = 3) and strictly violates the
conjectured inequality, refuting Conjecture 6.1.

## Negative-input sanity tests (manually exercised)

- `4 bcd,acd,abd,abc` (a torus rotation of K4): rejected — Euler V-E+F = 0 != 2.
- `4 bcd,acd,abd,abd` (loop): rejected — loop at vertex 3.
- `6 bcde,aefc,abfd,acfe,adfb,bedc` (octahedron; dual is the cube, S=0):
  passes all structural checks, rejected at the hypothesis S >= 3.
- `3 ab,ba`: rejected — n < 4 / malformed.
