#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cleanroom2_checker.py -- clean-room verification (session 2026-06-12, verifier agent)
of the claimed counterexample to Conjecture 4.6 of arXiv:2108.07723v7 (Z.-W. Sun,
"Arithmetic properties of some permanents").

Statement (pinned from paper.tex lines 285-296 and 1109-1114, and from the compiled
PDF text where it is numbered Conjecture 4.6):

  Definitions (Theorem 1.6 / Th-sin, PROVEN integers):
    s_n  = (2^((n-1)/2) / sqrt(n)) * per[ sin(2*pi*j*k/n) ]_{1<=j,k<=(n-1)/2}   (n odd > 1)
    s'_p = (sqrt(p) / 2^((p-1)/2)) * per[ csc(2*pi*j*k/p) ]_{1<=j,k<=(p-1)/2}   (p odd prime)
  Conjecture 4.6(ii):  for every odd prime p,
    s_p  < 0  <=>  p == 5 (mod 12)
    s'_p < 0  <=>  p == 7 (mod 8)

Claimed counterexample: p = 29 (29 == 5 mod 12, 29 == 5 mod 8) with
    s_29  = 1053859      > 0   (violates clause 1, "if" direction)
    s'_29 = -4806838304  < 0   (violates clause 2, "only if" direction)
Supplementary: s_41 = 5574476521 > 0 with 41 == 5 (mod 12).

This checker is written from the DESCRIPTION only; it shares no code with the attack
pipeline (driver.py/ryser_mod.c/checker.py) nor with the earlier clean-room layer
(independent_checker.py/crt_verify.py/perm_modq.c).  Two methods:

  METHOD A (exact):  ring homomorphism Z[zeta_{4n}] -> F_q for fresh random ~60-bit
    primes q == 1 (mod 4n).  Entries 2*sin(2*pi*jk/n) = -i*(z^(jk) - z^(-jk)) with
    z = zeta_n, i = zeta_{4n}^n; sqrt(n) via the quadratic Gauss sum
    G = sum_a zeta_n^(a^2) which equals +sqrt(n) for n == 1 (mod 4) and +i*sqrt(n)
    for n == 3 (mod 4) (Gauss's sign theorem).  Since s_n and s'_p are RATIONAL,
    every homomorphism maps them to their residue mod q, independent of the choice
    of root of unity.  Permanents by my own Gray-code Ryser mod q.  CRT with
    rigorous a-priori magnitude bounds, symmetric lift, plus one HELD-OUT prime
    per value that must agree with the reconstruction.
  METHOD B (rigorous enclosure, Gauss-sum-free):  mpmath interval arithmetic (iv)
    at 192 bits, direct real sin/csc entries, same-algorithm-different-arithmetic
    Gray-code Ryser; final interval must have width < 1 and contain exactly the
    claimed integer.  This closes any global-sign-convention hole in Method A.

Both permanent routines are self-tested against a naive permutation-expansion
permanent on random small matrices before use.
"""

import json
import math
import random
import sys
import time
from fractions import Fraction
from itertools import permutations

from mpmath import iv, mp

HERE = r"C:\Users\jacks\source\repos\maths\problems\p2-factory\attacks\sun-46\independent"
LOG_PATH = HERE + r"\cleanroom2_checker.log"
RESULTS_PATH = HERE + r"\cleanroom2_results.json"

RNG = random.Random(0x20260612)  # fresh deterministic seed, recorded for reproducibility

_logf = None  # opened lazily so that IMPORTING this module never truncates the log
def log(msg=""):
    global _logf
    if _logf is None:
        _logf = open(LOG_PATH, "w", encoding="utf-8")
    print(msg, flush=True)
    _logf.write(msg + "\n")
    _logf.flush()

# ----------------------------------------------------------------------------
# Published anchor values, transcribed by ME from paper.tex Remark 1.6 (Rem-sin),
# lines 297-307 of the TeX source.
# ----------------------------------------------------------------------------
SUN_S = {3: 1, 5: -1, 7: 1, 9: 9, 11: 1, 13: 51, 15: 45, 17: -239, 19: 913,
         21: 2835, 23: 12145}
SUN_SP = {3: 1, 5: 1, 7: -6, 11: 111, 13: 261, 17: 6784, 19: 245101, 23: -7094142}

# Claimed counterexample values (from the attack report being verified).
CLAIM_S = {29: 1053859, 41: 5574476521}
CLAIM_SP = {29: -4806838304}

# ----------------------------------------------------------------------------
# Number-theory utilities (all my own).
# ----------------------------------------------------------------------------
_MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)  # deterministic < 3.3e24

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for sp in _MR_BASES:
        if n % sp == 0:
            return n == sp
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in _MR_BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True

def fresh_prime_1mod(modulus: int, bits: int = 60) -> int:
    """Random prime q == 1 (mod modulus), roughly `bits` bits."""
    lo = (1 << (bits - 1)) // modulus
    hi = (1 << bits) // modulus
    while True:
        t = RNG.randrange(lo, hi)
        q = modulus * t + 1
        if is_prime(q):
            return q

def small_prime_factors(n: int):
    fs, d = set(), 2
    while d * d <= n:
        while n % d == 0:
            fs.add(d)
            n //= d
        d += 1
    if n > 1:
        fs.add(n)
    return sorted(fs)

def root_of_unity(q: int, order: int) -> int:
    """Element of F_q of EXACT multiplicative order `order` (requires order | q-1)."""
    assert (q - 1) % order == 0
    cof = (q - 1) // order
    pf = small_prime_factors(order)
    while True:
        w = pow(RNG.randrange(2, q - 1), cof, q)
        if w != 1 and all(pow(w, order // r, q) != 1 for r in pf):
            assert pow(w, order, q) == 1
            return w

def crt_pair(r1, m1, r2, m2):
    g, x, _ = ext_gcd(m1, m2)
    assert g == 1
    lift = (r1 + (r2 - r1) * x % m2 * m1) % (m1 * m2)
    return lift, m1 * m2

def ext_gcd(a, b):
    if b == 0:
        return a, 1, 0
    g, x, y = ext_gcd(b, a % b)
    return g, y, x - (a // b) * y

def crt_symmetric(residues, moduli):
    r, m = residues[0] % moduli[0], moduli[0]
    for rr, mm in zip(residues[1:], moduli[1:]):
        r, m = crt_pair(r, m, rr % mm, mm)
    if r > m // 2:
        r -= m
    return r, m

# ----------------------------------------------------------------------------
# Permanents (my own implementations).
# ----------------------------------------------------------------------------
def perm_naive(A):
    m = len(A)
    tot = 0
    for sigma in permutations(range(m)):
        pr = 1
        for i in range(m):
            pr *= A[i][sigma[i]]
        tot += pr
    return tot

def perm_ryser_mod(A, q):
    """Ryser with Gray code:  per(A) = sum_{S != empty} (-1)^(m-|S|) prod_i sum_{j in S} a_ij  (mod q)."""
    m = len(A)
    r = [0] * m
    total = 0
    prev = 0
    cnt = 0
    for g in range(1, 1 << m):
        gray = g ^ (g >> 1)
        bit = gray ^ prev
        j = bit.bit_length() - 1
        col = [A[i][j] for i in range(m)]
        if gray & bit:
            cnt += 1
            for i in range(m):
                r[i] = (r[i] + col[i]) % q
        else:
            cnt -= 1
            for i in range(m):
                r[i] = (r[i] - col[i]) % q
        pr = 1
        for x in r:
            pr = pr * x % q
        total = (total - pr if (m - cnt) & 1 else total + pr) % q
        prev = gray
    return total % q

def perm_ryser_iv(A):
    """Same Ryser/Gray-code algorithm over mpmath interval numbers."""
    m = len(A)
    zero = iv.mpf(0)
    r = [zero] * m
    total = zero
    prev = 0
    cnt = 0
    for g in range(1, 1 << m):
        gray = g ^ (g >> 1)
        bit = gray ^ prev
        j = bit.bit_length() - 1
        if gray & bit:
            cnt += 1
            for i in range(m):
                r[i] = r[i] + A[i][j]
        else:
            cnt -= 1
            for i in range(m):
                r[i] = r[i] - A[i][j]
        pr = iv.mpf(1)
        for x in r:
            pr = pr * x
        total = total - pr if (m - cnt) & 1 else total + pr
        prev = gray
    return total

# ----------------------------------------------------------------------------
# METHOD A: exact value of s_n (kind='sin') or s'_p (kind='csc') via CRT in F_q.
# ----------------------------------------------------------------------------
def residue_mod_q(n: int, kind: str, q: int) -> int:
    """Image of s_n (kind='sin') or s'_n (kind='csc', n prime) under Z[zeta_4n] -> F_q."""
    m = (n - 1) // 2
    w = root_of_unity(q, 4 * n)          # plays the role of zeta_{4n}
    i_q = pow(w, n, q)                   # zeta_{4n}^n = i
    assert i_q * i_q % q == q - 1, "i^2 != -1"
    # quadratic Gauss sum  G = sum_{a mod n} zeta_n^{a^2},  zeta_n = w^4
    G = sum(pow(w, (4 * a * a) % (4 * n), q) for a in range(n)) % q
    if n % 4 == 1:
        sqrt_n = G                       # G = +sqrt(n)        (Gauss)
    else:
        sqrt_n = G * (q - i_q) % q       # G = +i*sqrt(n)  =>  sqrt(n) = -i*G
    assert sqrt_n * sqrt_n % q == n % q, "Gauss sum square check failed"
    # matrix of 2*sin(2*pi*jk/n) = -i*(zeta_n^{jk} - zeta_n^{-jk})
    A = [[(q - i_q) * (pow(w, (4 * j * k) % (4 * n), q)
                       - pow(w, (-4 * j * k) % (4 * n), q)) % q
          for k in range(1, m + 1)] for j in range(1, m + 1)]
    if kind == "sin":
        # s_n = per[2 sin]/sqrt(n)
        return perm_ryser_mod(A, q) * pow(sqrt_n, q - 2, q) % q
    elif kind == "csc":
        # s'_p = sqrt(p) * per[(2 sin)^(-1)]
        for row in A:
            assert all(x % q != 0 for x in row), "csc entry not invertible"
        Ainv = [[pow(x, q - 2, q) for x in row] for row in A]
        return perm_ryser_mod(Ainv, q) * sqrt_n % q
    raise ValueError(kind)

def magnitude_bound(n: int, kind: str) -> int:
    """Rigorous integer bound B with |value| <= B.
    sin:  |s_n| = |per[2sin]|/sqrt(n) <= 2^m * m!          (entries |2sin| <= 2)
    csc:  |s'_p| = sqrt(p)*|per[(2sin)^{-1}]| <= sqrt(p)*m!*(p/4)^m <= p^{m+1}*m!/4^m
          (|1/(2 sin(2 pi t/p))| <= 1/(2 sin(pi/p)) <= p/4 because sin x >= 2x/pi)."""
    m = (n - 1) // 2
    if kind == "sin":
        return (1 << m) * math.factorial(m)
    return (n ** (m + 1)) * math.factorial(m) // (4 ** m) + 1

def exact_value(n: int, kind: str, label: str) -> int:
    B = magnitude_bound(n, kind)
    need = 2 * B + 2
    primes, prod = [], 1
    while prod <= need:
        q = fresh_prime_1mod(4 * n)
        if q in primes:
            continue
        primes.append(q)
        prod *= q
    holdout = fresh_prime_1mod(4 * n)
    while holdout in primes:
        holdout = fresh_prime_1mod(4 * n)
    t0 = time.time()
    residues = [residue_mod_q(n, kind, q) for q in primes]
    val, M = crt_symmetric(residues, primes)
    assert abs(val) <= B, f"{label}: CRT lift exceeds magnitude bound"
    assert 2 * B < M, f"{label}: modulus too small for uniqueness"
    rh = residue_mod_q(n, kind, holdout)
    assert val % holdout == rh, f"{label}: HELD-OUT prime mismatch"
    log(f"  {label} = {val}   [{len(primes)} CRT primes + 1 held-out, "
        f"B={B:.3e}, {time.time()-t0:.1f}s]")
    return val

# ----------------------------------------------------------------------------
# METHOD B: rigorous interval enclosure (no Gauss sums, direct real entries).
# ----------------------------------------------------------------------------
def interval_value(n: int, kind: str):
    m = (n - 1) // 2
    two_pi = 2 * iv.pi
    A = []
    for j in range(1, m + 1):
        row = []
        for k in range(1, m + 1):
            r = (j * k) % n
            s = iv.sin(two_pi * r / n)
            row.append(s if kind == "sin" else 1 / s)
        A.append(row)
    P = perm_ryser_iv(A)
    if kind == "sin":
        z = P * (1 << m) / iv.sqrt(n)
    else:
        z = P * iv.sqrt(n) / (1 << m)
    lo = int(mp.ceil(mp.mpf(z.a)))
    hi = int(mp.floor(mp.mpf(z.b)))
    return z, lo, hi   # integers in the enclosure are exactly lo..hi

# ----------------------------------------------------------------------------
# Self-tests.
# ----------------------------------------------------------------------------
def self_tests():
    log("== Self-tests ==")
    # Ryser-mod vs naive permanent, signed random matrices
    bigq = (1 << 89) - 1  # Mersenne prime
    assert is_prime(bigq)
    for m in range(1, 7):
        for _ in range(6):
            A = [[RNG.randrange(-25, 26) for _ in range(m)] for _ in range(m)]
            assert perm_ryser_mod([[x % bigq for x in row] for row in A], bigq) \
                   == perm_naive(A) % bigq, f"Ryser-mod self-test failed at m={m}"
    log("  perm_ryser_mod == perm_naive (mod 2^89-1) on 36 random signed matrices, m<=6: OK")
    # Interval Ryser vs naive
    for m in range(1, 6):
        A = [[RNG.randrange(-9, 10) for _ in range(m)] for _ in range(m)]
        z = perm_ryser_iv([[iv.mpf(x) for x in row] for row in A])
        v = perm_naive(A)
        assert z.a <= v <= z.b and float(z.delta) < 1e-20
    log("  perm_ryser_iv encloses perm_naive on random integer matrices, m<=5: OK")
    # CRT round-trip
    for _ in range(20):
        x = RNG.randrange(-10 ** 40, 10 ** 40)
        ps, pr = [], 1
        while pr <= 2 * abs(x) + 2:
            p = fresh_prime_1mod(2, 40)
            if p not in ps:
                ps.append(p)
                pr *= p
        v, M = crt_symmetric([x % p for p in ps], ps)
        assert v == x
    log("  symmetric CRT round-trip on 20 random 40-digit signed integers: OK")
    # Miller-Rabin sanity
    assert all(is_prime(p) for p in (2, 3, 5, 29, 41, 61, 10 ** 18 + 9))
    assert not any(is_prime(c) for c in (1, 561, 1105, 25326001, 3215031751, 10 ** 18 + 7))
    log("  Miller-Rabin on known primes/Carmichaels: OK")

# ----------------------------------------------------------------------------
# Main.
# ----------------------------------------------------------------------------
def main():
    mp.prec = 220
    iv.prec = 192
    results = {"seed": "0x20260612", "method_A": {}, "method_B": {}, "checks": []}
    ok = True

    def check(desc, cond):
        nonlocal ok
        results["checks"].append({"check": desc, "pass": bool(cond)})
        log(("  PASS  " if cond else "  FAIL  ") + desc)
        if not cond:
            ok = False

    self_tests()

    log("\n== METHOD A: exact CRT values ==")
    log(" Anchor sweep: all 19 values published in Remark 1.6 of the paper")
    for n, want in sorted(SUN_S.items()):
        v = exact_value(n, "sin", f"s_{n}")
        check(f"s_{n} == {want} (paper)", v == want)
        results["method_A"][f"s_{n}"] = v
    for p, want in sorted(SUN_SP.items()):
        v = exact_value(p, "csc", f"s'_{p}")
        check(f"s'_{p} == {want} (paper)", v == want)
        results["method_A"][f"sp_{p}"] = v

    log(" Targets:")
    s29 = exact_value(29, "sin", "s_29")
    sp29 = exact_value(29, "csc", "s'_29")
    s41 = exact_value(41, "sin", "s_41")
    results["method_A"].update({"s_29": s29, "sp_29": sp29, "s_41": s41})
    check("s_29  == 1053859 (claimed)", s29 == CLAIM_S[29])
    check("s'_29 == -4806838304 (claimed)", sp29 == CLAIM_SP[29])
    check("s_41  == 5574476521 (claimed)", s41 == CLAIM_S[41])

    log("\n Proven-congruence cross-checks (Theorem 1.6(iii)):")
    check("s_29 == -1 (mod 29)", s29 % 29 == 28)
    check("s'_29 == 1 (mod 29)", sp29 % 29 == 1)
    check("s_41 == -1 (mod 41)", s41 % 41 == 40)

    log("\n== METHOD B: rigorous interval enclosures (192-bit, Gauss-sum-free) ==")
    targets_B = [(5, "sin", SUN_S[5]), (17, "sin", SUN_S[17]),
                 (7, "csc", SUN_SP[7]), (23, "csc", SUN_SP[23]),
                 (29, "sin", CLAIM_S[29]), (29, "csc", CLAIM_SP[29]),
                 (41, "sin", CLAIM_S[41])]
    for n, kind, want in targets_B:
        t0 = time.time()
        z, lo, hi = interval_value(n, kind)
        name = (f"s_{n}" if kind == "sin" else f"s'_{n}")
        log(f"  {name} in [{mp.nstr(mp.mpf(z.a), 25)}, {mp.nstr(mp.mpf(z.b), 25)}]"
            f"  width={mp.nstr(mp.mpf(z.delta), 5)}  ({time.time()-t0:.1f}s)")
        check(f"{name}: enclosure contains exactly one integer, = {want}",
              lo == hi == want)
        results["method_B"][name.replace("'", "p")] = {"lo": lo, "hi": hi}

    log("\n== Conjecture 4.6(ii) verdict logic ==")
    check("29 == 5 (mod 12)  [conjecture demands s_29 < 0]", 29 % 12 == 5)
    check("s_29 > 0  -> clause 1 ('<=' direction) FALSE at p=29", s29 > 0)
    check("29 == 5 (mod 8), i.e. NOT 7 (mod 8)  [conjecture demands s'_29 >= 0]",
          29 % 8 == 5)
    check("s'_29 < 0  -> clause 2 ('=>' direction... only-if) FALSE at p=29", sp29 < 0)
    check("41 == 5 (mod 12) and s_41 > 0  -> clause 1 fails at p=41 too",
          41 % 12 == 5 and s41 > 0)

    log("")
    if ok:
        log("VERDICT: ALL CHECKS PASSED.")
        log("Conjecture 4.6(ii) of arXiv:2108.07723v7 is FALSE at p = 29 (both clauses),")
        log("hence Conjecture 4.6 (the conjunction of (i) and (ii)) is FALSE as stated.")
        log("Part (i) (n | s_n for odd composite n) is NOT addressed by this counterexample.")
    else:
        log("VERDICT: AT LEAST ONE CHECK FAILED -- kill NOT confirmed by this checker.")
    results["all_passed"] = ok
    with open(RESULTS_PATH, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=1, default=str)
    log(f"\nResults written to {RESULTS_PATH}")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
