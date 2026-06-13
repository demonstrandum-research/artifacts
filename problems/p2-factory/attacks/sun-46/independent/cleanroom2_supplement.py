#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cleanroom2_supplement.py -- clean-room session 2026-06-12 (verifier agent).
Exact CRT verification of the SUPPLEMENTARY claimed values
    s_53  = 1540679755916971              (53 == 5 mod 12, conjecture demands < 0)
    s'_61 = -2904784276786469053142518062479  (61 == 5 mod 8, conjecture demands >= 0)
using the same homomorphism construction as cleanroom2_checker.py (imported), but
with the m=26 / m=30 permanents mod q computed by my own OpenMP C helper
(cleanroom2_perm.c) under WSL.  Fresh prime seed, recorded.  The C path is first
validated against Sun's published anchors s_23 and s'_23 before any claim is tested.
"""
import math, subprocess, sys, time

sys.path.insert(0, r"C:\Users\jacks\source\repos\maths\problems\p2-factory\attacks\sun-46\independent")
import cleanroom2_checker as cc

HERE = r"C:\Users\jacks\source\repos\maths\problems\p2-factory\attacks\sun-46\independent"
WSL_HERE = "/mnt/c/Users/jacks/source/repos/maths/problems/p2-factory/attacks/sun-46/independent"

cc.RNG.seed(0xC1EA62)  # fresh seed for this supplementary layer, distinct from checker's

LOG = open(HERE + r"\cleanroom2_supplement.log", "w", encoding="utf-8")
def log(s=""):
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()

def perm_mod_c(A, q, tag):
    path = HERE + rf"\job_{tag}.txt"
    with open(path, "w") as f:
        f.write(f"{len(A)} {q}\n")
        for row in A:
            f.write(" ".join(map(str, row)) + "\n")
    out = subprocess.run(["wsl", "-d", "Ubuntu", f"{WSL_HERE}/cleanroom2_perm", f"{WSL_HERE}/job_{tag}.txt"],
                         capture_output=True, text=True, timeout=3600)
    assert out.returncode == 0, out.stderr
    assert out.stdout.startswith("PER "), out.stdout
    return int(out.stdout.split()[1])

def residue_mod_q_c(n, kind, q, tag):
    """Same construction as cc.residue_mod_q but the permanent runs in C."""
    m = (n - 1) // 2
    w = cc.root_of_unity(q, 4 * n)
    i_q = pow(w, n, q)
    assert i_q * i_q % q == q - 1
    G = sum(pow(w, (4 * a * a) % (4 * n), q) for a in range(n)) % q
    sqrt_n = G if n % 4 == 1 else G * (q - i_q) % q
    assert sqrt_n * sqrt_n % q == n % q
    A = [[(q - i_q) * (pow(w, (4 * j * k) % (4 * n), q)
                       - pow(w, (-4 * j * k) % (4 * n), q)) % q
          for k in range(1, m + 1)] for j in range(1, m + 1)]
    if kind == "sin":
        return perm_mod_c(A, q, tag) * pow(sqrt_n, q - 2, q) % q
    for row in A:
        assert all(x % q for x in row)
    Ainv = [[pow(x, q - 2, q) for x in row] for row in A]
    return perm_mod_c(Ainv, q, tag) * sqrt_n % q

def exact_value_c(n, kind, label):
    B = cc.magnitude_bound(n, kind)
    primes, prod = [], 1
    while prod <= 2 * B + 2:
        q = cc.fresh_prime_1mod(4 * n)
        if q not in primes:
            primes.append(q)
            prod *= q
    holdout = cc.fresh_prime_1mod(4 * n)
    while holdout in primes:
        holdout = cc.fresh_prime_1mod(4 * n)
    t0 = time.time()
    residues = [residue_mod_q_c(n, kind, q, f"{kind}{n}_{i}") for i, q in enumerate(primes)]
    val, M = cc.crt_symmetric(residues, primes)
    assert abs(val) <= B and 2 * B < M, f"{label}: CRT uniqueness violated"
    rh = residue_mod_q_c(n, kind, holdout, f"{kind}{n}_h")
    assert val % holdout == rh, f"{label}: held-out prime mismatch"
    log(f"  {label} = {val}   [{len(primes)} CRT primes + 1 held-out, B={B:.3e}, {time.time()-t0:.1f}s]")
    return val

def main():
    ok = True
    log("== C-path validation against published anchors ==")
    v = exact_value_c(23, "sin", "s_23")
    ok &= (v == 12145); log(f"  {'PASS' if v == 12145 else 'FAIL'}  s_23 == 12145 (paper)")
    v = exact_value_c(23, "csc", "s'_23")
    ok &= (v == -7094142); log(f"  {'PASS' if v == -7094142 else 'FAIL'}  s'_23 == -7094142 (paper)")

    log("\n== Supplementary claimed values ==")
    s53 = exact_value_c(53, "sin", "s_53")
    c = (s53 == 1540679755916971)
    ok &= c; log(f"  {'PASS' if c else 'FAIL'}  s_53 == 1540679755916971 (claimed)")
    c = (s53 % 53 == 52)  # Thm 1.6(iii): s_p == (-1)^((p+1)/2) = -1 for p=53
    ok &= c; log(f"  {'PASS' if c else 'FAIL'}  s_53 == -1 (mod 53)  [proven congruence]")
    c = (53 % 12 == 5 and s53 > 0)
    ok &= c; log(f"  {'PASS' if c else 'FAIL'}  53 == 5 (mod 12) but s_53 > 0  -> extra clause-1 failure")

    sp61 = exact_value_c(61, "csc", "s'_61")
    c = (sp61 == -2904784276786469053142518062479)
    ok &= c; log(f"  {'PASS' if c else 'FAIL'}  s'_61 == -2904784276786469053142518062479 (claimed)")
    c = (sp61 % 61 == 1)
    ok &= c; log(f"  {'PASS' if c else 'FAIL'}  s'_61 == 1 (mod 61)  [proven congruence]")
    c = (61 % 8 == 5 and sp61 < 0)
    ok &= c; log(f"  {'PASS' if c else 'FAIL'}  61 == 5 (mod 8) (not 7) but s'_61 < 0  -> extra clause-2 failure")

    log("\nSUPPLEMENT VERDICT: " + ("ALL CHECKS PASSED" if ok else "FAILURE -- see above"))
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
