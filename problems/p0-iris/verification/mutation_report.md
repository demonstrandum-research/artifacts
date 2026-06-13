# Mutation test report: IRIS Conjecture 6.1 certificate checkers

Date: 2026-06-11. Target conjecture: Conjecture 6.1 ("NuevaMirada") of the IRIS paper
(Davila, De Loera, Eddy, Fang, Lu, Yang; ICML 2025 AI4Math workshop, OpenReview id v6Ulp3U1ZT):
if a simple 3-polytope has S = sum_{k>=7} pk >= 3 then p6 >= 39/20 + p3/2 - p5/4 - S;
integer violation check: `20*p6 < 39 + 10*p3 - 5*p5 - 20*S`.

Checkers under test:

- **A (Python)** `verification/checker_py/verify_counterexample.py "<line>"` —
  ACCEPT iff stdout contains `COUNTEREXAMPLE CONFIRMED`. (It exits 0 even when printing
  `not a counterexample`, so output, not the exit code, is the acceptance signal.)
- **B (Rust)** `verification/checker_rs/target/release/checker_rs.exe <file>` —
  ACCEPT iff exit code 0 **and** stdout contains `COUNTEREXAMPLE CONFIRMED`.
  Each mutant was run as a single-line temp file.

## 1. Originals (must be ACCEPTED by both)

| line | Python verdict | Python exit | Rust verdict | Rust exit |
|------|----------------|-------------|--------------|-----------|
| 1 | ACCEPT | 0 | ACCEPT | 0 |
| 2 | ACCEPT | 0 | ACCEPT | 0 |
| 3 | ACCEPT | 0 | ACCEPT | 0 |
| 4 | ACCEPT | 0 | ACCEPT | 0 |
| 5 | ACCEPT | 0 | ACCEPT | 0 |

Rust on the full 5-line `certificates/cex10.txt`: exit 0, 5 x `COUNTEREXAMPLE CONFIRMED` -> OK.

## 2. Mutant matrix (33 mutants, 11 of them valid triangulations)

Acceptance criterion: **every mutant must be REJECTED by BOTH checkers.**
Categories: (a) single-character adjacency edits; (b) swapped letters within a rotation;
(c) deleted/duplicated darts; (d) asymmetric adjacency; (e) valid triangulation, hypothesis
S>=3 fails; (f) wrong n header; (g) valid triangulation, inequality satisfied; (x) parser garbage.

| id | category | mutation | Python | py exit | Python rejection reason | Rust | rs exit | Rust rejection reason |
|----|----------|----------|--------|---------|-------------------------|------|---------|------------------------|
| a1 | a single-char edit | L1 vertex j: 'cgf' -> 'cgg' (f->g: duplicate neighbor g, dart j->f deleted) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: multi-edge 9-6 (duplicate neighbor in rotation) |
| a2 | a single-char edit | L1 vertex b: 'aigc' -> 'aigd' (c->d: b claims d, d does not list b) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: asymmetric adjacency: 1 lists 3 but not conversely |
| a3 | a single-char edit | L5 vertex d: 'ace' -> 'acf' (e->f: asymmetric both ways) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: asymmetric adjacency: 3 lists 5 but not conversely |
| a4 | a single-char edit | L1 vertex a: 'bcdefghi' -> 'bcdefghh' (i->h: duplicate neighbor h) | reject | 1 | AssertionError: multi-edge | reject | 1 | T: multi-edge 0-7 (duplicate neighbor in rotation) |
| b1 | b rotation swap | L1 vertex a: swap h,i -> 'bcdefgih' (graph unchanged, embedding mutated) | reject | 1 | AssertionError: Euler fails for T: 10-24+14 | reject | 1 | T: Euler characteristic V-E+F = 10-24+14 = 0 != 2 (not a planar embedding) |
| b2 | b rotation swap | L1 vertex c: swap e,d -> 'abgjfde' | reject | 1 | AssertionError: Euler fails for T: 10-24+14 | reject | 1 | T: Euler characteristic V-E+F = 10-24+14 = 0 != 2 (not a planar embedding) |
| b3 | b rotation swap | L5 vertex e: swap j,f -> 'adcigfj' | reject | 1 | AssertionError: Euler fails for T: 10-24+14 | reject | 1 | T: Euler characteristic V-E+F = 10-24+14 = 0 != 2 (not a planar embedding) |
| b4 | b rotation swap | L2 vertex d: swap f,e -> 'acbgjef' | reject | 1 | AssertionError: Euler fails for T: 10-24+14 | reject | 1 | T: Euler characteristic V-E+F = 10-24+14 = 0 != 2 (not a planar embedding) |
| c1 | c dart delete/dup | L1 vertex j: delete dart j->g: 'cgf' -> 'cf' | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: asymmetric adjacency: 6 lists 9 but not conversely |
| c2 | c dart delete/dup | L1 vertex j: duplicate dart j->g: 'cgf' -> 'cgfg' | reject | 1 | AssertionError: multi-edge | reject | 1 | T: multi-edge 9-6 (duplicate neighbor in rotation) |
| c3 | c dart delete/dup | L3 vertex b: delete dart b->a: 'aijc' -> 'ijc' | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: asymmetric adjacency: 0 lists 1 but not conversely |
| c4 | c dart delete/dup | L4 vertex j: duplicate dart j->b: 'bfd' -> 'bbfd' | reject | 1 | AssertionError: multi-edge | reject | 1 | T: multi-edge 9-1 (duplicate neighbor in rotation) |
| d1 | d asymmetric | L1 vertex b: extra dart b->e: 'aigc' -> 'aigce' (e does not list b) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: asymmetric adjacency: 1 lists 4 but not conversely |
| d2 | d asymmetric | L5 vertex h: 'bgc' -> 'bgd' (h claims d, d does not list h) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: asymmetric adjacency: 2 lists 7 but not conversely |
| d3 | d asymmetric | L1 vertex i: 'ahgb' -> 'ahgc' (i claims c, c does not list i) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | T: asymmetric adjacency: 1 lists 8 but not conversely |
| f1 | f wrong header | L1 header 10 -> 9 (still 10 adjacency lists) | reject | 1 | AssertionError | reject | 1 | expected 9 comma-separated adjacency lists, got 10 |
| f2 | f wrong header | L1 header 10 -> 11 (still 10 adjacency lists) | reject | 1 | AssertionError | reject | 1 | expected 11 comma-separated adjacency lists, got 10 |
| f3 | f wrong header | L1 header 10 kept but last adjacency list removed (9 lists) | reject | 1 | AssertionError | reject | 1 | expected 10 comma-separated adjacency lists, got 9 |
| f4 | f wrong header | L1 header 10 -> 0 | reject | 1 | AssertionError | reject | 1 | n = 0 but a planar triangulation needs n >= 4 |
| x1 | x parser | L1 vertex j: 'cgf' -> 'czf' (letter z out of range for n=10) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | vertex letter 'z' out of range for n = 10 |
| x2 | x parser | L1 vertex a: 'bcdefghi' -> 'Bcdefghi' (uppercase letter) | reject | 1 | KeyError: 'B' | reject | 1 | invalid character 'B' in rotation |
| x3 | x parser | L1 vertex j: adjacency list emptied (line ends with comma) | reject | 1 | AssertionError: asymmetric adjacency | reject | 1 | vertex 9 has an empty adjacency list |
| e1_tetrahedron | e valid, hypothesis fails | valid K4 triangulation; dual = tetrahedron, p3=4, S=0 (hypothesis fails) | reject | 1 | AssertionError: hypothesis sum_{k>=7} pk >= 3 FAILS | reject | 1 | hypothesis violated: S = sum_{k>=7} pk = 0 < 3, conjecture does not apply |
| e2_octahedron | e valid, hypothesis fails | valid octahedron; dual = cube, p4=6, S=0 (hypothesis fails) | reject | 1 | AssertionError: hypothesis sum_{k>=7} pk >= 3 FAILS | reject | 1 | hypothesis violated: S = sum_{k>=7} pk = 0 < 3, conjecture does not apply |
| e3_icosahedron | e valid, hypothesis fails | valid icosahedron; dual = dodecahedron, p5=12, S=0 (hypothesis fails) | reject | 1 | AssertionError: hypothesis sum_{k>=7} pk >= 3 FAILS | reject | 1 | hypothesis violated: S = sum_{k>=7} pk = 0 < 3, conjecture does not apply |
| e4_bipyramid5 | e valid, hypothesis fails | valid pentagonal bipyramid; dual: p4=5 p5=2, S=0 (hypothesis fails) | reject | 1 | AssertionError: hypothesis sum_{k>=7} pk >= 3 FAILS | reject | 1 | hypothesis violated: S = sum_{k>=7} pk = 0 < 3, conjecture does not apply |
| e5_bipyramid6 | e valid, hypothesis fails | valid hexagonal bipyramid; dual: p4=6 p6=2, S=0 (hypothesis fails; note 20*p6=40 >= 39) | reject | 1 | AssertionError: hypothesis sum_{k>=7} pk >= 3 FAILS | reject | 1 | hypothesis violated: S = sum_{k>=7} pk = 0 < 3, conjecture does not apply |
| e6_bipyramid7 | e valid, hypothesis fails | valid heptagonal bipyramid; dual: p4=7 p7=2, S=2 (hypothesis boundary: S=2 < 3) | reject | 1 | AssertionError: hypothesis sum_{k>=7} pk >= 3 FAILS | reject | 1 | hypothesis violated: S = sum_{k>=7} pk = 2 < 3, conjecture does not apply |
| e7_bipyramid8 | e valid, hypothesis fails | valid octagonal bipyramid; dual: p4=8 p8=2, S=2 (hypothesis fails) | reject | 1 | AssertionError: hypothesis sum_{k>=7} pk >= 3 FAILS | reject | 1 | hypothesis violated: S = sum_{k>=7} pk = 2 < 3, conjecture does not apply |
| g1_n14 | g valid, inequality holds | valid n=14 triangulation; dual: p4=6 p5=3 p6=2 p7=3, S=3, 40 >= -36 (inequality satisfied) | reject | 0 | prints 'not a counterexample' (exit 0) | reject | 1 | inequality NOT violated: 20*p6 = 40 >= -36 = 39 + 10*p3 - 5*p5 - 20*S |
| g2_n16 | g valid, inequality holds | valid n=16 triangulation; dual: p4=7 p5=4 p6=1 p7=3 p9=1, S=4, 20 >= -61 (inequality satisfied) | reject | 0 | prints 'not a counterexample' (exit 0) | reject | 1 | inequality NOT violated: 20*p6 = 20 >= -61 = 39 + 10*p3 - 5*p5 - 20*S |
| g3_n18 | g valid, inequality holds | valid n=18 triangulation; dual: p4=9 p5=4 p6=1 p7..p10, S=4, 20 >= -61 (inequality satisfied) | reject | 0 | prints 'not a counterexample' (exit 0) | reject | 1 | inequality NOT violated: 20*p6 = 20 >= -61 = 39 + 10*p3 - 5*p5 - 20*S |
| g4_small_margin | g valid, inequality holds | valid n=14 triangulation; dual: p3=5 p4=3 p5=2 p6=1 p9=1 p10=2, S=3, 20 >= 19 (margin 1!) | reject | 0 | prints 'not a counterexample' (exit 0) | reject | 1 | inequality NOT violated: 20*p6 = 20 >= 19 = 39 + 10*p3 - 5*p5 - 20*S |

### Mutant certificate lines

```
a1                 10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgg
a2                 10 bcdefghi,aigd,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
a3                 10 bcdef,afghc,abhgied,acf,adcigjf,aejgb,bfjeich,bgc,cge,egf
a4                 10 bcdefghh,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
b1                 10 bcdefgih,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
b2                 10 bcdefghi,aigc,abgjfde,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
b3                 10 bcdef,afghc,abhgied,ace,adcigfj,aejgb,bfjeich,bgc,cge,egf
b4                 10 bcdefghi,aigdc,abd,acbgjef,adf,aedjg,afjdbih,agi,ahgb,dgf
c1                 10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cf
c2                 10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgfg
c3                 10 bcdefghi,ijc,abjifed,ace,adcf,aecig,afih,agi,ahgfcjb,bic
c4                 10 bcdefghi,aihfjdc,abd,acbjfe,adf,aedjbhg,afh,agfbi,ahb,bbfd
d1                 10 bcdefghi,aigce,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
d2                 10 bcdef,afghc,abhgied,ace,adcigjf,aejgb,bfjeich,bgd,cge,egf
d3                 10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgc,cgf
f1                 9 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
f2                 11 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
f3                 10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb
f4                 0 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
x1                 10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,czf
x2                 10 Bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,cgf
x3                 10 bcdefghi,aigc,abgjfed,ace,adcf,aecjg,afjcbih,agi,ahgb,
e1_tetrahedron     4 bcd,adc,abd,acb
e2_octahedron      6 bcde,aefc,abfd,acfe,adfb,bedc
e3_icosahedron     12 hjgei,fkgjc,bjhlf,fliek,iagkd,dkbcl,ajbke,lcjai,edlha,gahcb,degbf,hidfc
e4_bipyramid5      7 bcdef,afgc,abgd,acge,adgf,aegb,fedcb
e5_bipyramid6      8 bcdefg,aghc,abhd,ache,adhf,aehg,afhb,gfedcb
e6_bipyramid7      9 bcdefgh,ahic,abid,acie,adif,aeig,afih,agib,hgfedcb
e7_bipyramid8      10 bcdefghi,aijc,abjd,acje,adjf,aejg,afjh,agji,ahjb,ihgfedcb
g1_n14             14 cijhm,hlem,amgkdei,ckfe,cdfmbli,medkg,fkcm,lbmajn,elnjac,hain,gfdc,hnieb,fgcahbe,hjil
g2_n16             16 cjfbn,gnaf,angkoej,opfje,codj,jdpmikgba,fkcnb,oklm,lkfm,edfac,filhocg,imhk,fpohli,bgca,hmpdeck,mfdo
g3_n18             18 bgpckdoefh,ahlnfcjig,apjbfrk,akro,aorf,bnmhaerc,iqpab,fmlba,qgbj,cpqib,crda,hmnb,lhfn,lmfb,eadr,gqjca,ijpg,feodkc
g4_small_margin    14 hfcmlidgeb,efha,mafni,aikfeg,agdfb,bedkijncah,dea,fab,njfkdalmc,inf,dif,iam,cila,jicf
```

## 3. Control (not a mutant)

Mirror of line 1 (every rotation reversed = the reflected planar embedding) is a genuine
counterexample certificate and is expected to be ACCEPTED by both checkers:

```
10 ihgfedcb,cgia,defjgba,eca,fcda,gjcea,hibcjfa,iga,bgha,fgc
```

Python: ACCEPT (exit 0); Rust: ACCEPT (exit 0). Both accept the mirrored embedding, as they should (this confirms the b-category rejections are about the *embedding*, not orientation pickiness).

## 4. Summary

- Originals: all 5 ACCEPTED by both checkers.
- Mutants: 33 tested, 11 valid triangulations among them (categories e/g).
- All 33 mutants REJECTED by BOTH checkers. No mutant survived.
- The category e/g mutants are structurally perfect certificates that pass parsing, simplicity,
  symmetry, planarity (Euler), triangulation, dual 3-regularity and 3-connectivity, and are
  rejected only at the final mathematical steps (hypothesis S>=3, or the integer inequality),
  so the mathematical checks - not just the parser - are demonstrably load-bearing.
- g4 is the sharpest test: S=3 and 20*p6 = 20 vs RHS = 19 (margin 1); both checkers correctly
  report the inequality as NOT violated.
- Disagreement note: for mutants where the polytope is valid but the inequality holds (g1-g4),
  the Python checker exits 0 while printing 'not a counterexample'; the Rust checker exits 1.
  Under the agreed acceptance semantics (CONFIRMED string for A, exit+string for B) both reject;
  but anyone gating on the Python checker's *exit code* alone would be misled.
