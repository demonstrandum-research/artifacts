#!/usr/bin/env python3
"""
INDEPENDENT CRT/finite-field verification layer for sun-46 (clean room).

For each claimed integer value V of s_n or s'_p, this script proves V is
exactly the true value, by:

  1. a RIGOROUS magnitude bound B >= |true value| computed with exact
     rational arithmetic (chord bound |sin(pi x)| >= 2 dist(x, Z)),
  2. evaluating the cyclotomic identity at a root w of Phi_{4n} in F_q for
     enough random 61-bit primes q == 1 (mod 4n) that prod(q) > 4B:
        sin:  per[(w^{4jk} - w^{-4jk})]  ==  V * g * w^{nm}        (mod q)
        csc:  V  ==  g * w^{nm} * per[(w^{4jk} - w^{-4jk})^{-1}]   (mod q)
     where g in F_q is the image of sqrt(n): the Gauss sum
     sum_{a<n} w^{4a^2}, times w^{3n} if n == 3 (mod 4)  (Gauss's theorem),
     sanity-checked by g^2 == n (mod q).
  3. Since the true value T satisfies the same congruence for every such q
     (the identity per(M) = s_n i^m sqrt(n) holds in Z[zeta_4n] and maps to
     F_q under zeta -> w), V == T (mod prod q) and |V - T| <= 2B < prod q
     forces V == T exactly.

Permanent mod q computed by my own C program perm_modq.c (WSL, OpenMP).
Primes: my own Miller-Rabin, seeded RNG (seed 20260611), 61-bit -- disjoint
from the attack's 59-bit primes by construction.
"""
import json, math, random, subprocess, sys, time
from fractions import Fraction

WSLDIR = "/mnt/c/Users/jacks/source/repos/maths/problems/p2-factory/attacks/sun-46/independent"
LOG = []
def log(s):
    print(s, flush=True)
    LOG.append(s)

# ---------------- Miller-Rabin (deterministic < 3.3e24) ----------------
def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def gen_prime(N, rng, avoid):
    """one random 61-bit prime q == 1 (mod N), not in avoid."""
    while True:
        t = rng.randrange((1 << 60) // N, (1 << 61) // N)
        q = N * t + 1
        if q not in avoid and is_prime(q):
            return q

def prime_factors(x):
    out, d = set(), 2
    while d * d <= x:
        while x % d == 0: out.add(d); x //= d
        d += 1
    if x > 1: out.add(x)
    return out

def find_root_of_order(N, q, rng):
    fs = prime_factors(N)
    while True:
        w = pow(rng.randrange(2, q - 1), (q - 1) // N, q)
        if w != 1 and all(pow(w, N // r, q) != 1 for r in fs):
            assert pow(w, N, q) == 1
            return w

# ---------------- rigorous magnitude bounds (exact rationals) ----------
def bound_s(n):
    m = (n - 1) // 2
    return (1 << m) * m ** m          # |sin|<=1, sqrt(n)>1

def bound_sprime(p):
    m = (p - 1) // 2
    prod = Fraction(1)
    for j in range(1, m + 1):
        row = Fraction(0)
        for k in range(1, m + 1):
            r0 = (2 * j * k) % p
            r = min(r0, p - r0)
            assert r > 0
            row += Fraction(p, 2 * r)
        prod *= row
    sq_up = Fraction(math.isqrt(p) + 1)
    b = sq_up / (1 << m) * prod
    return b.numerator // b.denominator + 1

# ---------------- per-prime check -------------------------------------
def perm_modq_C(m, q, mat):
    inp = " ".join(str(x) for x in mat)
    r = subprocess.run(["wsl", "-d", "Ubuntu", "-e", WSLDIR + "/perm_modq",
                        str(m), str(q)],
                       input=inp, capture_output=True, text=True, timeout=3600)
    assert r.returncode == 0, r.stderr
    return int(r.stdout.strip())

def check_value(n, V, mode, rng, primes_cache={}):
    """mode in ('sin','csc'). Returns (ok, primes_used)."""
    m = (n - 1) // 2
    N = 4 * n
    B = bound_s(n) if mode == "sin" else bound_sprime(n)
    assert abs(V) <= B, f"claimed |V| exceeds rigorous bound for n={n}"
    need = 4 * B
    if (N, "p") not in primes_cache:
        primes_cache[(N, "p")] = []
    primes = primes_cache[(N, "p")]
    prodq = 1
    used = []
    t0 = time.time()
    i = 0
    while prodq <= need:
        if i >= len(primes):
            primes.append(gen_prime(N, rng, set(primes)))
        q = primes[i]; i += 1
        w = find_root_of_order(N, q, rng)
        # Gauss-sum image of sqrt(n)
        g = sum(pow(w, (4 * a * a) % N, q) for a in range(n)) % q
        if n % 4 == 3:
            g = g * pow(w, 3 * n, q) % q
        assert g * g % q == n % q, f"Gauss sanity failed n={n} q={q}"
        if mode == "sin":
            mat = []
            for j in range(1, m + 1):
                for k in range(1, m + 1):
                    a = (4 * j * k) % N
                    mat.append((pow(w, a, q) - pow(w, (N - a) % N, q)) % q)
            P = perm_modq_C(m, q, mat)
            lhs, rhs = P, V * g % q * pow(w, (n * m) % N, q) % q
        else:
            mat = []
            for j in range(1, m + 1):
                for k in range(1, m + 1):
                    a = (4 * j * k) % N
                    d = (pow(w, a, q) - pow(w, (N - a) % N, q)) % q
                    mat.append(pow(d, q - 2, q))
            P = perm_modq_C(m, q, mat)
            lhs, rhs = V % q, g * pow(w, (n * m) % N, q) % q * P % q
        ok = lhs == rhs
        log(f"      q={q}: {'match' if ok else 'MISMATCH'} "
            f"(lhs={lhs}, rhs={rhs})")
        if not ok:
            return False, used
        prodq *= q
        used.append(q)
    log(f"   {mode} n={n}: V={V} PROVED exact "
        f"(bound 2^{B.bit_length()}, prod(q) 2^{prodq.bit_length()}, "
        f"{len(used)} primes, {time.time()-t0:.1f}s)")
    return True, used

# ---------------- job table -------------------------------------------
SMALL_VALIDATION = [  # ground truth: Sun Remark 1.6 + my exact checker
    (17, -239, "sin"), (23, 12145, "sin"), (29, 1053859, "sin"),
    (17, 6784, "csc"), (23, -7094142, "csc"), (29, -4806838304, "csc"),
]
CLAIMS_S = {31: 10542977, 33: -1643895, 35: 334186125, 37: 1519663259,
            39: 9154298673, 41: 5574476521, 43: 453435884081,
            45: 696741294375, 47: 4570760060257, 49: 3078195713761,
            51: 113109498706113, 53: 1540679755916971,
            55: 9553828212328125, 57: 89237136634668369,
            59: 493044351638203633, 61: 3864901746617921299,
            63: 14357464732984700313, 65: 23595726326056828125}
CLAIMS_SP = {31: -1518806869720, 37: 43041655439377,
             41: 88188655594502880, 43: 7817331967711147274,
             47: -208210243110377949730, 53: 1364915376262405923148317,
             59: 7313054784852201235037895089487,
             61: -2904784276786469053142518062479}

def main():
    rng = random.Random(20260611)
    t0 = time.time()
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 65
    results = {}
    log("INDEPENDENT CRT VERIFICATION (clean-room layer 2) -- sun-46")
    log("== validation against ground truth (Sun's table / exact checker) ==")
    allok = True
    for n, V, mode in SMALL_VALIDATION:
        ok, _ = check_value(n, V, mode, rng)
        allok &= ok
        results[f"{mode}_{n}"] = {"V": str(V), "ok": ok, "role": "validation"}
    assert allok, "validation layer failed!"
    log("")
    log("== claimed values (kill-certificate full_data) ==")
    for n, V in sorted(CLAIMS_S.items()):
        if n > cap: continue
        ok, _ = check_value(n, V, "sin", rng)
        allok &= ok
        results[f"sin_{n}"] = {"V": str(V), "ok": ok}
    for p, V in sorted(CLAIMS_SP.items()):
        if p > cap: continue
        ok, _ = check_value(p, V, "csc", rng)
        allok &= ok
        results[f"csc_{p}"] = {"V": str(V), "ok": ok}
    log("")
    log(f"OVERALL: {'ALL PROVED EXACT' if allok else 'FAILURES PRESENT'} "
        f"({time.time()-t0:.0f}s)")
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    with open(here + "/crt_verify.log", "w", encoding="utf-8") as f:
        f.write("\n".join(LOG) + "\n")
    with open(here + "/crt_verify_results.json", "w", encoding="utf-8") as f:
        json.dump(results, f, indent=1)
    return 0 if allok else 1

if __name__ == "__main__":
    sys.exit(main())
