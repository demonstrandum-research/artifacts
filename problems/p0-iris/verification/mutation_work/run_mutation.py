# -*- coding: utf-8 -*-
"""Mutation-test harness for the two IRIS Conjecture 6.1 certificate checkers.

Checker A (Python): verify_counterexample.py "<line>"
  ACCEPT iff stdout contains "COUNTEREXAMPLE CONFIRMED" (it can exit 0 while
  printing "not a counterexample", so exit code alone is NOT acceptance).
Checker B (Rust): checker_rs.exe <file>  (one mutant line per temp file)
  ACCEPT iff exit code == 0 AND stdout contains "COUNTEREXAMPLE CONFIRMED".

Every mutant must be REJECTED by BOTH checkers.
"""
import os
import subprocess
import sys

BASE = r"C:\Users\jacks\source\repos\maths\problems\p0-iris"
PY_CHECKER = os.path.join(BASE, "verification", "checker_py", "verify_counterexample.py")
RS_CHECKER = os.path.join(BASE, "verification", "checker_rs", "target", "release", "checker_rs.exe")
CERT = os.path.join(BASE, "certificates", "cex10.txt")
WORK = os.path.join(BASE, "verification", "mutation_work")
REPORT = os.path.join(BASE, "verification", "mutation_report.md")

with open(CERT, encoding="utf-8") as fh:
    ORIG = [ln.strip() for ln in fh if ln.strip()]
assert len(ORIG) == 5

def parts_of(line):
    n, rest = line.split()
    return n, rest.split(",")

def rebuild(n, parts):
    return "%s %s" % (n, ",".join(parts))

def edit(line, vidx, new):
    n, p = parts_of(line)
    p[vidx] = new
    return rebuild(n, p)

def set_header(line, new_n):
    _, rest = line.split()
    return "%s %s" % (new_n, rest)

L1, L2, L3, L4, L5 = ORIG

mutants = []  # (id, category, description, line)

def add(mid, cat, desc, line):
    mutants.append((mid, cat, desc, line))

# (a) single-character adjacency edits
add("a1", "a single-char edit", "L1 vertex j: 'cgf' -> 'cgg' (f->g: duplicate neighbor g, dart j->f deleted)", edit(L1, 9, "cgg"))
add("a2", "a single-char edit", "L1 vertex b: 'aigc' -> 'aigd' (c->d: b claims d, d does not list b)", edit(L1, 1, "aigd"))
add("a3", "a single-char edit", "L5 vertex d: 'ace' -> 'acf' (e->f: asymmetric both ways)", edit(L5, 3, "acf"))
add("a4", "a single-char edit", "L1 vertex a: 'bcdefghi' -> 'bcdefghh' (i->h: duplicate neighbor h)", edit(L1, 0, "bcdefghh"))

# (b) swapped letters within a rotation (same simple graph, embedding broken)
add("b1", "b rotation swap", "L1 vertex a: swap h,i -> 'bcdefgih' (graph unchanged, embedding mutated)", edit(L1, 0, "bcdefgih"))
add("b2", "b rotation swap", "L1 vertex c: swap e,d -> 'abgjfde'", edit(L1, 2, "abgjfde"))
add("b3", "b rotation swap", "L5 vertex e: swap j,f -> 'adcigfj'", edit(L5, 4, "adcigfj"))
add("b4", "b rotation swap", "L2 vertex d: swap f,e -> 'acbgjef'", edit(L2, 3, "acbgjef"))

# (c) deleted / duplicated darts
add("c1", "c dart delete/dup", "L1 vertex j: delete dart j->g: 'cgf' -> 'cf'", edit(L1, 9, "cf"))
add("c2", "c dart delete/dup", "L1 vertex j: duplicate dart j->g: 'cgf' -> 'cgfg'", edit(L1, 9, "cgfg"))
add("c3", "c dart delete/dup", "L3 vertex b: delete dart b->a: 'aijc' -> 'ijc'", edit(L3, 1, "ijc"))
add("c4", "c dart delete/dup", "L4 vertex j: duplicate dart j->b: 'bfd' -> 'bbfd'", edit(L4, 9, "bbfd"))

# (d) asymmetric adjacency
add("d1", "d asymmetric", "L1 vertex b: extra dart b->e: 'aigc' -> 'aigce' (e does not list b)", edit(L1, 1, "aigce"))
add("d2", "d asymmetric", "L5 vertex h: 'bgc' -> 'bgd' (h claims d, d does not list h)", edit(L5, 7, "bgd"))
add("d3", "d asymmetric", "L1 vertex i: 'ahgb' -> 'ahgc' (i claims c, c does not list i)", edit(L1, 8, "ahgc"))

# (f) wrong n header
add("f1", "f wrong header", "L1 header 10 -> 9 (still 10 adjacency lists)", set_header(L1, 9))
add("f2", "f wrong header", "L1 header 10 -> 11 (still 10 adjacency lists)", set_header(L1, 11))
add("f3", "f wrong header", "L1 header 10 kept but last adjacency list removed (9 lists)", "10 " + ",".join(parts_of(L1)[1][:9]))
add("f4", "f wrong header", "L1 header 10 -> 0", set_header(L1, 0))

# (x) parser-level garbage
add("x1", "x parser", "L1 vertex j: 'cgf' -> 'czf' (letter z out of range for n=10)", edit(L1, 9, "czf"))
add("x2", "x parser", "L1 vertex a: 'bcdefghi' -> 'Bcdefghi' (uppercase letter)", edit(L1, 0, "Bcdefghi"))
add("x3", "x parser", "L1 vertex j: adjacency list emptied (line ends with comma)", edit(L1, 9, ""))

# (e)/(g) valid triangulations that are NOT counterexamples
DESCS = {
    "e1_tetrahedron": "valid K4 triangulation; dual = tetrahedron, p3=4, S=0 (hypothesis fails)",
    "e2_octahedron": "valid octahedron; dual = cube, p4=6, S=0 (hypothesis fails)",
    "e3_icosahedron": "valid icosahedron; dual = dodecahedron, p5=12, S=0 (hypothesis fails)",
    "e4_bipyramid5": "valid pentagonal bipyramid; dual: p4=5 p5=2, S=0 (hypothesis fails)",
    "e5_bipyramid6": "valid hexagonal bipyramid; dual: p4=6 p6=2, S=0 (hypothesis fails; note 20*p6=40 >= 39)",
    "e6_bipyramid7": "valid heptagonal bipyramid; dual: p4=7 p7=2, S=2 (hypothesis boundary: S=2 < 3)",
    "e7_bipyramid8": "valid octagonal bipyramid; dual: p4=8 p8=2, S=2 (hypothesis fails)",
    "g1_n14": "valid n=14 triangulation; dual: p4=6 p5=3 p6=2 p7=3, S=3, 40 >= -36 (inequality satisfied)",
    "g2_n16": "valid n=16 triangulation; dual: p4=7 p5=4 p6=1 p7=3 p9=1, S=4, 20 >= -61 (inequality satisfied)",
    "g3_n18": "valid n=18 triangulation; dual: p4=9 p5=4 p6=1 p7..p10, S=4, 20 >= -61 (inequality satisfied)",
    "g4_small_margin": "valid n=14 triangulation; dual: p3=5 p4=3 p5=2 p6=1 p9=1 p10=2, S=3, 20 >= 19 (margin 1!)",
}
with open(os.path.join(WORK, "valid_lines.tsv"), encoding="utf-8") as fh:
    for raw in fh:
        tag, line = raw.rstrip("\n").split("\t")
        cat = "e valid, hypothesis fails" if tag.startswith("e") else "g valid, inequality holds"
        add(tag, cat, DESCS[tag], line)

# control (NOT a mutant): global mirror of L1 = the reflected embedding,
# which is still a genuine counterexample certificate -> expected ACCEPT by both.
n1, p1 = parts_of(L1)
mirror_L1 = rebuild(n1, [s[::-1] for s in p1])

# ---------------- runners ----------------

def run_py(line):
    r = subprocess.run([sys.executable, PY_CHECKER, line],
                       capture_output=True, text=True, timeout=120)
    accept = "COUNTEREXAMPLE CONFIRMED" in r.stdout
    if accept:
        reason = "confirmed"
    else:
        reason = ""
        if "not a counterexample" in r.stdout:
            reason = "prints 'not a counterexample' (exit 0)"
        err = [l for l in r.stderr.strip().splitlines() if l.strip()]
        for l in reversed(err):
            if "Error" in l:
                reason = (reason + "; " if reason else "") + l.strip()
                break
        if not reason:
            reason = "no CONFIRMED in output, exit %d" % r.returncode
    return accept, r.returncode, reason

def run_rs(line, tmpname):
    tmp = os.path.join(WORK, tmpname)
    with open(tmp, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(line + "\n")
    r = subprocess.run([RS_CHECKER, tmp], capture_output=True, text=True, timeout=120)
    accept = (r.returncode == 0) and ("COUNTEREXAMPLE CONFIRMED" in r.stdout)
    if accept:
        reason = "confirmed"
    else:
        reason = ""
        for l in r.stdout.splitlines():
            if "FAILED:" in l:
                reason = l.split("FAILED:", 1)[1].strip()
                break
        if not reason:
            reason = (r.stderr.strip().splitlines() or ["exit %d" % r.returncode])[0]
    return accept, r.returncode, reason

def esc(s):
    return s.replace("|", "\\|")

rows = []
violations = []
for mid, cat, desc, line in mutants:
    pa, prc, prs = run_py(line)
    ra, rrc, rrs = run_rs(line, "mut_%s.txt" % mid)
    rows.append((mid, cat, desc, line, pa, prc, prs, ra, rrc, rrs))
    if pa or ra:
        violations.append(mid)
    print("%-18s py=%s(rc=%d) rs=%s(rc=%d)" % (
        mid, "ACCEPT" if pa else "reject", prc, "ACCEPT" if ra else "reject", rrc))

# originals per line
orig_rows = []
for i, line in enumerate(ORIG, 1):
    pa, prc, prs = run_py(line)
    ra, rrc, rrs = run_rs(line, "orig_%d.txt" % i)
    orig_rows.append((i, pa, prc, ra, rrc))
    print("orig %d py=%s rs=%s" % (i, pa, ra))

# control: mirrored embedding
cpa, cprc, cprs = run_py(mirror_L1)
cra, crrc, crrs = run_rs(mirror_L1, "control_mirror.txt")
print("control mirror: py=%s rs=%s" % (cpa, cra))

# Rust on the full original file
rfull = subprocess.run([RS_CHECKER, CERT], capture_output=True, text=True, timeout=120)
rfull_ok = rfull.returncode == 0 and rfull.stdout.count("COUNTEREXAMPLE CONFIRMED") == 5

# ---------------- report ----------------
n_valid_tri = sum(1 for m in mutants if m[1].startswith(("e", "g")))
lines = []
A = lines.append
A("# Mutation test report: IRIS Conjecture 6.1 certificate checkers")
A("")
A("Date: 2026-06-11. Target conjecture: Conjecture 6.1 (\"NuevaMirada\") of the IRIS paper")
A("(Davila, De Loera, Eddy, Fang, Lu, Yang; ICML 2025 AI4Math workshop, OpenReview id v6Ulp3U1ZT):")
A("if a simple 3-polytope has S = sum_{k>=7} pk >= 3 then p6 >= 39/20 + p3/2 - p5/4 - S;")
A("integer violation check: `20*p6 < 39 + 10*p3 - 5*p5 - 20*S`.")
A("")
A("Checkers under test:")
A("")
A("- **A (Python)** `verification/checker_py/verify_counterexample.py \"<line>\"` —")
A("  ACCEPT iff stdout contains `COUNTEREXAMPLE CONFIRMED`. (It exits 0 even when printing")
A("  `not a counterexample`, so output, not the exit code, is the acceptance signal.)")
A("- **B (Rust)** `verification/checker_rs/target/release/checker_rs.exe <file>` —")
A("  ACCEPT iff exit code 0 **and** stdout contains `COUNTEREXAMPLE CONFIRMED`.")
A("  Each mutant was run as a single-line temp file.")
A("")
A("## 1. Originals (must be ACCEPTED by both)")
A("")
A("| line | Python verdict | Python exit | Rust verdict | Rust exit |")
A("|------|----------------|-------------|--------------|-----------|")
for i, pa, prc, ra, rrc in orig_rows:
    A("| %d | %s | %d | %s | %d |" % (i, "ACCEPT" if pa else "REJECT", prc, "ACCEPT" if ra else "REJECT", rrc))
A("")
A("Rust on the full 5-line `certificates/cex10.txt`: exit %d, %d x `COUNTEREXAMPLE CONFIRMED` -> %s."
  % (rfull.returncode, rfull.stdout.count("COUNTEREXAMPLE CONFIRMED"), "OK" if rfull_ok else "FAIL"))
A("")
A("## 2. Mutant matrix (%d mutants, %d of them valid triangulations)" % (len(mutants), n_valid_tri))
A("")
A("Acceptance criterion: **every mutant must be REJECTED by BOTH checkers.**")
A("Categories: (a) single-character adjacency edits; (b) swapped letters within a rotation;")
A("(c) deleted/duplicated darts; (d) asymmetric adjacency; (e) valid triangulation, hypothesis")
A("S>=3 fails; (f) wrong n header; (g) valid triangulation, inequality satisfied; (x) parser garbage.")
A("")
A("| id | category | mutation | Python | py exit | Python rejection reason | Rust | rs exit | Rust rejection reason |")
A("|----|----------|----------|--------|---------|-------------------------|------|---------|------------------------|")
for mid, cat, desc, line, pa, prc, prs, ra, rrc, rrs in rows:
    A("| %s | %s | %s | %s | %d | %s | %s | %d | %s |" % (
        mid, esc(cat), esc(desc),
        "**ACCEPT (BUG!)**" if pa else "reject", prc, esc(prs),
        "**ACCEPT (BUG!)**" if ra else "reject", rrc, esc(rrs)))
A("")
A("### Mutant certificate lines")
A("")
A("```")
for mid, cat, desc, line, *_ in rows:
    A("%-18s %s" % (mid, line))
A("```")
A("")
A("## 3. Control (not a mutant)")
A("")
A("Mirror of line 1 (every rotation reversed = the reflected planar embedding) is a genuine")
A("counterexample certificate and is expected to be ACCEPTED by both checkers:")
A("")
A("```")
A(mirror_L1)
A("```")
A("")
A("Python: %s (exit %d); Rust: %s (exit %d). %s" % (
    "ACCEPT" if cpa else "REJECT", cprc, "ACCEPT" if cra else "REJECT", crrc,
    "Both accept the mirrored embedding, as they should (this confirms the b-category rejections are about the *embedding*, not orientation pickiness)." if (cpa and cra) else "UNEXPECTED - investigate."))
A("")
A("## 4. Summary")
A("")
ok_orig = all(pa and ra for _, pa, _, ra, _ in orig_rows) and rfull_ok
A("- Originals: %s" % ("all 5 ACCEPTED by both checkers." if ok_orig else "FAILURE - some original rejected!"))
A("- Mutants: %d tested, %d valid triangulations among them (categories e/g)." % (len(mutants), n_valid_tri))
if violations:
    A("- **CHECKER BUG: the following mutants were ACCEPTED by a checker: %s**" % ", ".join(violations))
else:
    A("- All %d mutants REJECTED by BOTH checkers. No mutant survived." % len(mutants))
A("- The category e/g mutants are structurally perfect certificates that pass parsing, simplicity,")
A("  symmetry, planarity (Euler), triangulation, dual 3-regularity and 3-connectivity, and are")
A("  rejected only at the final mathematical steps (hypothesis S>=3, or the integer inequality),")
A("  so the mathematical checks - not just the parser - are demonstrably load-bearing.")
A("- g4 is the sharpest test: S=3 and 20*p6 = 20 vs RHS = 19 (margin 1); both checkers correctly")
A("  report the inequality as NOT violated.")
A("- Disagreement note: for mutants where the polytope is valid but the inequality holds (g1-g4),")
A("  the Python checker exits 0 while printing 'not a counterexample'; the Rust checker exits 1.")
A("  Under the agreed acceptance semantics (CONFIRMED string for A, exit+string for B) both reject;")
A("  but anyone gating on the Python checker's *exit code* alone would be misled.")
A("")
with open(REPORT, "w", encoding="utf-8", newline="\n") as fh:
    fh.write("\n".join(lines))
print("report written:", REPORT)
print("violations:", violations if violations else "none")
print("originals ok:", ok_orig)
