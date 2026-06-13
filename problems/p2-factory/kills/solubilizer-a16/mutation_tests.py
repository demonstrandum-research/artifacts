"""
Mutation tests for checker.py (Gate-4 doctrine: a checker that never rejects
anything proves nothing). Each mutation corrupts the certificate in a targeted
way; checker.py must exit non-zero on every one, and exit 0 on the original.

Also runs a POSITIVE CONTROL: the same pipeline on G2 = A5 x S3 (where the
A.16 instance is TRUE: Sol = D10 x S3 is metabelian), confirming the
metabelian test does not unconditionally report 'not metabelian'.
"""

import copy
import json
import os
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8", errors="replace")

D = os.path.dirname(os.path.abspath(__file__))
CHECKER = os.path.join(D, "checker.py")
CERT = os.path.join(D, "certificate.json")

with open(CERT, encoding="utf-8") as f:
    base = json.load(f)

results = []

def run_checker(cert_dict, name):
    p = os.path.join(D, f"_mut_{name}.json")
    with open(p, "w", encoding="utf-8") as f:
        json.dump(cert_dict, f)
    r = subprocess.run([sys.executable, CHECKER, p],
                       capture_output=True, text=True, timeout=900)
    os.remove(p)
    return r.returncode, r.stdout

def expect_reject(cert_dict, name, why):
    rc, out = run_checker(cert_dict, name)
    ok = rc != 0
    last_fail = [l for l in out.splitlines() if "[FAIL]" in l]
    results.append((name, "REJECTED as required" if ok else "ACCEPTED (BUG!)", why,
                    last_fail[-1].strip() if last_fail else ""))
    print(f"  [{'OK' if ok else 'BUG'}] {name}: exit={rc}  ({why})")
    if last_fail:
        print(f"        first failing check: {last_fail[-1].strip()}")
    return ok

print("Mutation tests on checker.py")
print("=" * 70)
allok = True

# M0: the genuine certificate must be ACCEPTED
rc, out = run_checker(base, "original")
print(f"  [{'OK' if rc == 0 else 'BUG'}] M0 original certificate: exit={rc} (must be 0)")
results.append(("M0-original", "ACCEPTED as required" if rc == 0 else "REJECTED (BUG!)",
                "genuine certificate", ""))
allok &= (rc == 0)

# M1: wrong claimed order of Sol
m = copy.deepcopy(base); m["claimed_sol_order"] = 120
allok &= expect_reject(m, "M1-wrong-sol-order", "claims |Sol|=120 instead of 240")

# M2: claimed Sol generators give D10 x A4 (order 120), not D10 x S4
m = copy.deepcopy(base)
m["claimed_sol_generators"] = [
    [1, 2, 3, 4, 0, 5, 6, 7, 8],          # (01234)
    [0, 4, 3, 2, 1, 5, 6, 7, 8],          # (14)(23)
    [0, 1, 2, 3, 4, 6, 7, 5, 8],          # (567)  — only even S4-part
    [0, 1, 2, 3, 4, 6, 5, 8, 7],          # (56)(78)
]
allok &= expect_reject(m, "M2-D10xA4", "claimed subgroup is D10 x A4, order 120")

# M3: wrong x — 3-cycle first component ((012), id); Sol_G(x) is then not the claimed set
m = copy.deepcopy(base); m["x"] = [1, 2, 0, 3, 4, 5, 6, 7, 8]
allok &= expect_reject(m, "M3-wrong-x", "x = ((012), id) has a different solubilizer")

# M4: corrupted derived-series claim (pretends I is metabelian-compatible)
m = copy.deepcopy(base); m["claimed_derived_orders_of_intersection"] = [240, 60, 1]
allok &= expect_reject(m, "M4-fake-derived-orders", "claims derived orders [240,60,1]")

# M5: x = identity (Sol = G, hypothesis fails; checker must not accept)
m = copy.deepcopy(base); m["x"] = [0, 1, 2, 3, 4, 5, 6, 7, 8]
allok &= expect_reject(m, "M5-x-identity", "Sol_G(1) = G, not the claimed proper subgroup")

# M6: corrupted group generators -> S5 x S4 (order 2880), not A5 x S4
m = copy.deepcopy(base)
m["generators_G"][1] = [1, 0, 2, 3, 4, 5, 6, 7, 8]   # transposition (01): odd
allok &= expect_reject(m, "M6-S5xS4", "generators give S5 x S4 of order 2880")

# ---------------------------------------------------------------- positive control
print()
print("Positive control: G2 = A5 x S3 on 8 points (A.16 instance is TRUE there)")
sys.path.insert(0, D)
import checker as C

a   = C.perm_from_cycles(8, [[0, 1, 2, 3, 4]])
t3  = C.perm_from_cycles(8, [[0, 1, 2]])
s56 = C.perm_from_cycles(8, [[5, 6]])
s567 = C.perm_from_cycles(8, [[5, 6, 7]])
G2 = C.closure([a, t3, s56, s567])
assert len(G2) == 360, f"|A5 x S3| = {len(G2)} != 360"
assert not C.is_solvable(G2)
x2 = a
cache = {}
Sol2 = set()
for y in G2:
    H = frozenset(C.closure([x2, y]))
    if H not in cache:
        cache[H] = C.is_solvable(H)
    if cache[H]:
        Sol2.add(y)
assert len(Sol2) == 60, f"|Sol| = {len(Sol2)} != 60 (D10 x S3)"
assert C.is_subgroup(Sol2) and len(Sol2) < len(G2)
N2 = C.normalizer(Sol2, G2)
assert N2 == Sol2
I2 = Sol2 & N2
orders2 = [len(h) for h in C.derived_series(I2)]
meta = C.is_metabelian(I2)
print(f"  Sol_G2(x) order = {len(Sol2)}, N=Sol: True, derived orders {orders2}, "
      f"is_metabelian = {meta}")
assert orders2 == [60, 15, 1] and meta, "positive control failed"
print("  [OK] pipeline correctly reports the A5 x S3 instance as METABELIAN")
print("       (conjecture A.16 holds there; no kill reported) — the checker is")
print("       not biased toward rejection of the conjecture.")
results.append(("P1-A5xS3-control", "metabelian=True as required",
                "A.16 instance true for A5 x S3", ""))

print()
print("=" * 70)
print("ALL MUTATION TESTS PASSED" if allok else "SOME MUTATION TESTS FAILED")
with open(os.path.join(D, "mutation_tests.log"), "w", encoding="utf-8") as f:
    for r in results:
        f.write(" | ".join(r) + "\n")
    f.write(("ALL MUTATION TESTS PASSED" if allok else "SOME MUTATION TESTS FAILED") + "\n")
sys.exit(0 if allok else 1)
