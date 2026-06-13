#!/usr/bin/env python3
"""ref_check.py — hostile-referee recomputation of EVERY number in
papers/sun-46/note.tex (2026-06-12).

Fresh implementation, written for this referee pass; shares no code with the
kill bundle.  Method: the cyclotomic identities of Lemma 3.1 of the note
(independently re-derived and re-proved by the referee), evaluated in F_q at
a verified root w of exact multiplicative order 4n for fresh random primes
q = 1 (mod 4n) in [2^61, 2^62) (seed 20260612 — disjoint by construction
from all three prime sets used in the bundle: 57-bit, 59-bit, [2^60,2^61)),
with rigorous magnitude bounds, prod(q) > 4*bound CRT-uniqueness
reconstruction, and one extra held-out prime per value.

Expected values below were transcribed BY THE REFEREE from note.tex itself
(Tables 1, 2, 3 and the abstract/theorem), not from any bundle file, so a
transcription error anywhere in the note will surface as a MISMATCH.

Also audits every numerical side-claim of the note: residues mod 12 / mod 8,
the "violates" column, the quotients s_n/n, Sun's proven congruences, digit
counts, set claims ("nine primes", "fifteen odd composites", sign patterns),
and the kernel itself (brute-force and pure-Python cross-checks).

Run inside WSL Ubuntu next to the compiled kernel:
    gcc -O3 -march=native -fopenmp -o ref_perm_modq ref_perm_modq.c
    python3 ref_check.py            # expect final line: REFEREE: ALL CHECKS PASS
"""
import itertools
import math
import os
import random
import subprocess
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
KERNEL = os.path.join(HERE, "ref_perm_modq")
rng = random.Random(20260612)

FAILURES = []


def check(label, cond):
    print(("  OK   " if cond else "  FAIL ") + label, flush=True)
    if not cond:
        FAILURES.append(label)


# ---------------------------------------------------------------- expected
# Transcribed from note.tex (referee's own reading of the tables).
NOTE_S = {
    # Table 3 (calibration = Sun's Remark 1.6)
    3: 1, 5: -1, 7: 1, 9: 9, 11: 1, 13: 51, 15: 45, 17: -239, 19: 913,
    21: 2835, 23: 12145,
    # Table 1 (primes 29..61)
    29: 1053859, 31: 10542977, 37: 1519663259, 41: 5574476521,
    43: 453435884081, 47: 4570760060257, 53: 1540679755916971,
    59: 493044351638203633, 61: 3864901746617921299,
    # Table 2 (odd composites <= 65)
    25: 63125, 27: 59049, 33: -1643895, 35: 334186125, 39: 9154298673,
    45: 696741294375, 49: 3078195713761, 51: 113109498706113,
    55: 9553828212328125, 57: 89237136634668369, 63: 14357464732984700313,
    65: 23595726326056828125,
}
NOTE_SP = {
    # Table 3 (calibration)
    3: 1, 5: 1, 7: -6, 11: 111, 13: 261, 17: 6784, 19: 245101, 23: -7094142,
    # Table 1
    29: -4806838304, 31: -1518806869720, 37: 43041655439377,
    41: 88188655594502880, 43: 7817331967711147274,
    47: -208210243110377949730, 53: 1364915376262405923148317,
    59: 7313054784852201235037895089487,
    61: -2904784276786469053142518062479,
}
NOTE_QUOTIENTS = {  # Table 2, column s_n/n
    9: 1, 15: 3, 21: 135, 25: 2525, 27: 2187, 33: -49815, 35: 9548175,
    39: 234725607, 45: 15483139875, 49: 62820320689, 51: 2217833307963,
    55: 173705967496875, 57: 1565563800608217, 63: 227896265602931751,
    65: 363011174247028125,
}
NOTE_VIOLATES = {  # Table 1, "violates" column
    29: "both", 31: "none", 37: "none", 41: "mod12", 43: "none",
    47: "none", 53: "mod12", 59: "none", 61: "mod8",
}

PRIMES_NEW = [29, 31, 37, 41, 43, 47, 53, 59, 61]
COMPOSITES = [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 57, 63, 65]
CAL_S = [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23]
CAL_SP = [3, 5, 7, 11, 13, 17, 19, 23]


# ---------------------------------------------------------------- number theory
def is_prime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def fresh_prime(mult, avoid=()):
    """random prime q = 1 (mod mult) with q in [2^61, 2^62)."""
    while True:
        k = rng.randrange((1 << 61) // mult, (1 << 62) // mult)
        q = mult * k + 1
        if q >> 61 and not q >> 62 and q not in avoid and is_prime(q):
            return q


def factor_small(x):
    fs, d = set(), 2
    while d * d <= x:
        while x % d == 0:
            fs.add(d)
            x //= d
        d += 1
    if x > 1:
        fs.add(x)
    return fs


def elem_of_order(q, order):
    fs = factor_small(order)
    assert (q - 1) % order == 0
    while True:
        w = pow(rng.randrange(2, q - 1), (q - 1) // order, q)
        if w != 1 and all(pow(w, order // r, q) != 1 for r in fs):
            assert pow(w, order, q) == 1
            return w


# ---------------------------------------------------------------- permanents
def per_kernel(m, q, mat):
    flat = " ".join(str(x % q) for row in mat for x in row)
    r = subprocess.run([KERNEL, str(m), str(q)], input=flat,
                       capture_output=True, text=True, timeout=7200)
    assert r.returncode == 0, r.stderr
    return int(r.stdout.strip())


def per_brute(mat, q):
    m = len(mat)
    tot = 0
    for sigma in itertools.permutations(range(m)):
        prod = 1
        for j in range(m):
            prod = prod * mat[j][sigma[j]] % q
        tot = (tot + prod) % q
    return tot


def per_ryser_py(mat, q):
    """independent pure-Python Ryser (no Gray code) for medium m."""
    m = len(mat)
    tot = 0
    for S in range(1, 1 << m):
        prod = 1
        for j in range(m):
            s = 0
            for k in range(m):
                if S >> k & 1:
                    s += mat[j][k]
            prod = prod * s % q
        tot = (tot + (-1) ** (m - bin(S).count("1")) * prod) % q
    return tot


# ---------------------------------------------------------------- bounds
def bound(n, kind):
    m = (n - 1) // 2
    if kind == "sin":
        return (1 << m) * math.factorial(m)  # |per| <= m!, sqrt(n) >= 1
    p = n  # csc: |csc(2pi jk/p)| <= p / (2 dist(2jk/p,Z)*p) = p/(2 r)
    tot = Fraction(1)
    for j in range(1, m + 1):
        row = Fraction(0)
        for k in range(1, m + 1):
            r0 = (2 * j * k) % p
            r = min(r0, p - r0)
            assert r > 0
            row += Fraction(p, 2 * r)
        tot *= row
    b = Fraction(math.isqrt(p) + 1, 1 << m) * tot
    return b.numerator // b.denominator + 1


# ---------------------------------------------------------------- residues
def residue(n, kind, q):
    """s_n (resp. s'_n) mod q via the cyclotomic identity at a root of
    exact order 4n in F_q.  Lemma 3.1 of the note, re-derived by referee:
      per[zeta^{4jk}-zeta^{-4jk}]      = s_n  * i^m * sqrt(n)
      per[n(zeta^{4jk}-zeta^{-4jk})^-1] = s'_n * n^{m-1} * sqrt(n) * i^{-m}
    """
    m = (n - 1) // 2
    N = 4 * n
    w = elem_of_order(q, N)
    g = 0
    for a in range(n):
        g = (g + pow(w, (4 * a * a) % N, q)) % q
    if n % 4 == 3:
        g = g * pow(w, (3 * n) % N, q) % q  # zeta^{-n} = w^{3n}: G~ = -iG
    assert g * g % q == n % q, "Gauss-sum image fails g^2 = n"
    i_img = pow(w, n, q)
    assert i_img * i_img % q == q - 1, "i image fails i^2 = -1"

    M = [[(pow(w, (4 * j * k) % N, q) - pow(w, (-4 * j * k) % N, q)) % q
          for k in range(1, m + 1)] for j in range(1, m + 1)]
    if kind == "sin":
        P = per_kernel(m, q, M)
        denom = pow(i_img, m % 4, q) * g % q
    else:
        for row in M:
            for x in row:
                assert x != 0
        U = [[n * pow(x, q - 2, q) % q for x in row] for row in M]
        P = per_kernel(m, q, U)
        denom = pow(n, m - 1, q) * g % q * pow(i_img, (4 - m % 4) % 4, q) % q
    return P * pow(denom, q - 2, q) % q


def crt_sym(rs, qs):
    x, M = 0, 1
    for r, q in zip(rs, qs):
        t = (r - x) * pow(M, -1, q) % q
        x += M * t
        M *= q
    return (x - M if x > M // 2 else x), M


def certify(n, kind, expected):
    t0 = time.time()
    B = bound(n, kind)
    qs, rs, prod = [], [], 1
    while prod <= 4 * B:
        q = fresh_prime(4 * n, avoid=set(qs))
        qs.append(q)
        rs.append(residue(n, kind, q))
        prod *= q
    val, M = crt_sym(rs, qs)
    ok = abs(val) <= B
    qh = fresh_prime(4 * n, avoid=set(qs))
    ok = ok and val % qh == residue(n, kind, qh)
    ok = ok and val == expected
    el = time.time() - t0
    name = ("s_%d" if kind == "sin" else "s'_%d") % n
    check(f"{name} = {expected}  [recomputed {val}; {len(qs)}+1 primes, "
          f"prod 2^{M.bit_length()}, bound 2^{B.bit_length()}, {el:.1f}s]",
          ok)
    return val


# ================================================================= run
def main():
    print("== 0. kernel self-tests ==", flush=True)
    for m in range(1, 8):
        q = fresh_prime(4, ())
        mat = [[rng.randrange(q) for _ in range(m)] for _ in range(m)]
        check(f"kernel vs brute-force permutation sum, m={m}",
              per_kernel(m, q, mat) == per_brute(mat, q))
    for m in (10, 13):
        q = fresh_prime(4, ())
        mat = [[rng.randrange(q) for _ in range(m)] for _ in range(m)]
        check(f"kernel vs pure-Python Ryser, m={m}",
              per_kernel(m, q, mat) == per_ryser_py(mat, q))

    print("== 1. calibration: Sun's nineteen published values ==", flush=True)
    for n in CAL_S:
        certify(n, "sin", NOTE_S[n])
    for p in CAL_SP:
        certify(p, "csc", NOTE_SP[p])

    print("== 2. Table 1: s_p, s'_p for the nine primes 29..61 ==", flush=True)
    for p in PRIMES_NEW:
        certify(p, "sin", NOTE_S[p])
        certify(p, "csc", NOTE_SP[p])

    print("== 3. Table 2: s_n for the fifteen odd composites <= 65 ==",
          flush=True)
    for n in COMPOSITES:
        certify(n, "sin", NOTE_S[n])

    print("== 4. table-audit: every numerical side-claim of the note ==",
          flush=True)
    check("nine primes 29<=p<=61 exactly",
          PRIMES_NEW == [x for x in range(29, 62) if is_prime(x)])
    check("fifteen odd composites n<=65 exactly",
          COMPOSITES == [x for x in range(9, 66, 2) if not is_prime(x)])
    # (the first run of this script asserted {25, 49} here, mirroring the
    # pre-revision note, and FAILED -- that exposed finding R3 of
    # RESPONSES.md; the note now says "the prime squares 9, 25, 49")
    check("prime squares among them: 9, 25, 49",
          {x for x in COMPOSITES if math.isqrt(x) ** 2 == x} == {9, 25, 49})
    check("composites coprime to 3: exactly 25,35,49,55,65",
          [x for x in COMPOSITES if x % 3] == [25, 35, 49, 55, 65])
    # Table 1 columns
    resid = {29: (5, 5), 31: (7, 7), 37: (1, 5), 41: (5, 1), 43: (7, 3),
             47: (11, 7), 53: (5, 5), 59: (11, 3), 61: (1, 5)}
    for p in PRIMES_NEW:
        check(f"p={p}: (p mod 12, p mod 8) = {resid[p]} as printed",
              (p % 12, p % 8) == resid[p])
        v12 = (p % 12 == 5) != (NOTE_S[p] < 0)
        v8 = (p % 8 == 7) != (NOTE_SP[p] < 0)
        word = {(True, True): "both", (True, False): "mod12",
                (False, True): "mod8", (False, False): "none"}[(v12, v8)]
        check(f"p={p}: 'violates' column = {NOTE_VIOLATES[p]}",
              word == NOTE_VIOLATES[p])
    # proven congruences (Thm 1.6(iii)) on every prime value in the note
    for p in sorted(set(CAL_S) & set(NOTE_S) | set(PRIMES_NEW)):
        if is_prime(p):
            check(f"s_{p} = (-1)^((p+1)/2) (mod {p})",
                  NOTE_S[p] % p == (-1) ** ((p + 1) // 2) % p)
    for p in CAL_SP + PRIMES_NEW:
        check(f"s'_{p} = 1 (mod {p})", NOTE_SP[p] % p == 1)
    check("kill-pair residues as quoted: s_29=28, s'_29=1 (mod 29)",
          NOTE_S[29] % 29 == 28 and NOTE_SP[29] % 29 == 1)
    # Table 2 quotients
    for n in COMPOSITES:
        check(f"n={n}: n | s_n and s_n/n = {NOTE_QUOTIENTS[n]} as printed",
              NOTE_S[n] % n == 0 and NOTE_S[n] // n == NOTE_QUOTIENTS[n])
    # sign-pattern claims (Remark 2.3)
    check("s_p > 0 for every prime 29..61",
          all(NOTE_S[p] > 0 for p in PRIMES_NEW))
    check("negative s'_p in 29..61 exactly at {29,31,47,61}",
          {p for p in PRIMES_NEW if NOTE_SP[p] < 0} == {29, 31, 47, 61})
    check("31 = 47 = 7 (mod 8); 29 = 61 = 5 (mod 8)",
          31 % 8 == 47 % 8 == 7 and 29 % 8 == 61 % 8 == 5)
    check("Sun-table negatives exactly s_5, s_17, s'_7, s'_23",
          [n for n in CAL_S if NOTE_S[n] < 0] == [5, 17]
          and [p for p in CAL_SP if NOTE_SP[p] < 0] == [7, 23])
    check("eight primes in each of Sun's two prime data sets",
          len([n for n in CAL_S if is_prime(n)]) == 8 and len(CAL_SP) == 8)
    # headline/abstract numbers
    check("abstract kill pair: s_29 = 1053859 > 0, s'_29 = -4806838304 < 0",
          NOTE_S[29] == 1053859 > 0 and NOTE_SP[29] == -4806838304 < 0)
    check("abstract: s_41 = 5574476521, s_53 = 1540679755916971, both > 0",
          NOTE_S[41] == 5574476521 and NOTE_S[53] == 1540679755916971)
    check("abstract: s'_61 = -2904784276786469053142518062479 < 0",
          NOTE_SP[61] == -2904784276786469053142518062479)
    # size claims
    newvals = [NOTE_S[p] for p in PRIMES_NEW] + \
              [NOTE_SP[p] for p in PRIMES_NEW] + \
              [NOTE_S[n] for n in COMPOSITES]
    maxdig = max(len(str(abs(v))) for v in newvals)
    check(f"values grow to 31 digits (max digits = {maxdig})", maxdig == 31)
    check("m up to 32 (n = 65)", (65 - 1) // 2 == 32)
    check("|s_n| <= 2^m m! for every sin value in the note",
          all(abs(NOTE_S[n]) <= (1 << ((n - 1) // 2)) *
              math.factorial((n - 1) // 2) for n in NOTE_S))
    check("counts: 19 calibration values, 18 new prime values, "
          "15 composites, 30 new beyond Sun's table",
          len(CAL_S) + len(CAL_SP) == 19
          and 2 * len(PRIMES_NEW) == 18
          and len(COMPOSITES) == 15
          and 2 * len(PRIMES_NEW) + len(COMPOSITES) - 3 == 30)

    print(flush=True)
    if FAILURES:
        print(f"REFEREE: {len(FAILURES)} CHECK(S) FAILED:")
        for f in FAILURES:
            print("   " + f)
        sys.exit(1)
    print("REFEREE: ALL CHECKS PASS")
    sys.exit(0)


if __name__ == "__main__":
    main()
