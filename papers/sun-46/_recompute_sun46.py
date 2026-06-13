# Helper for the sun-46 note: recompute / cross-check every number quoted
# in note.tex from the verified kill bundle plus fresh computation.
#
#   python _recompute_sun46.py        (expects final line: ALL NOTE CHECKS PASS)
#
# Part A: arithmetic consistency of all 38 certified integers from
#         problems/p2-factory/attacks/sun-46/results.json:
#         - Sun's proven congruences s_p == (-1)^((p+1)/2), s'_p == 1 (mod p)
#           for all primes 29..61;
#         - part (i) divisibility n | s_n for all 15 odd composites n <= 65
#           (and the integer quotients s_n/n printed for the note's table);
#         - residues mod 12 / mod 8 and the sign-violation bookkeeping for
#           the five violated instances.
# Part B: fresh independent float recomputation (numpy Gray-code Ryser,
#         float64) of every table entry with m = (n-1)/2 <= 18 -- all
#         nineteen calibration values (n <= 23), s_p, s'_p for
#         p = 29, 31, 37, and s_n for n = 25, 27, 33, 35 -- from scratch,
#         on top of the bundle's exact layers.  (Extended 2026-06-12,
#         referee pass: calibration entries added so that the coverage
#         claim in note.tex is literally exhaustive.)

import json
import math
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "..", "..", "problems", "p2-factory",
                       "attacks", "sun-46", "results.json")

with open(RESULTS, encoding="utf-8") as fh:
    raw = {k: int(v) for k, v in json.load(fh).items()}

S = {int(k.split("_")[1]): v for k, v in raw.items() if k.startswith("sin")}
SP = {int(k.split("_")[1]): v for k, v in raw.items() if k.startswith("csc")}

PRIMES = [29, 31, 37, 41, 43, 47, 53, 59, 61]
COMPOSITES = [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 57, 63, 65]

ok = True


def check(label, cond):
    global ok
    print(f"  {label}: {'OK' if cond else 'FAIL'}")
    if not cond:
        ok = False


print("== A1: proven congruences (Thm 1.6(iii)) on all new prime values ==")
for p in PRIMES:
    check(f"s_{p} == (-1)^((p+1)/2) (mod {p})",
          S[p] % p == (-1) ** ((p + 1) // 2) % p)
    check(f"s'_{p} == 1 (mod {p})", SP[p] % p == 1)

print("== A2: part (i) divisibility n | s_n, quotients for the note ==")
for n in COMPOSITES:
    check(f"{n} | s_{n}", S[n] % n == 0)
    print(f"    s_{n} = {S[n]}   s_{n}/{n} = {S[n] // n}")

print("== A3: residues and sign violations ==")
check("29 == 5 (mod 12) and 29 == 5 (mod 8)", 29 % 12 == 5 and 29 % 8 == 5)
check("41 == 5 (mod 12)", 41 % 12 == 5)
check("53 == 5 (mod 12)", 53 % 12 == 5)
check("61 == 5 (mod 8)", 61 % 8 == 5)
check("s_29 > 0 (violates s_p<0 <= p==5 mod 12)", S[29] > 0)
check("s'_29 < 0 (violates s'_p<0 => p==7 mod 8)", SP[29] < 0)
check("s_41 > 0", S[41] > 0)
check("s_53 > 0", S[53] > 0)
check("s'_61 < 0", SP[61] < 0)
print("  signs of s_p, 29..61:",
      {p: '+' if S[p] > 0 else '-' for p in PRIMES})
print("  signs of s'_p, 29..61:",
      {p: '+' if SP[p] > 0 else '-' for p in PRIMES})
check("every s_p > 0 for p = 29..61", all(S[p] > 0 for p in PRIMES))
check("negative s'_p exactly at p = 29, 31, 47, 61",
      {p for p in PRIMES if SP[p] < 0} == {29, 31, 47, 61})
check("primes == 5 (mod 12) in range: exactly 29, 41, 53",
      [p for p in PRIMES if p % 12 == 5] == [29, 41, 53])
check("primes == 7 (mod 8) in range: exactly 31, 47",
      [p for p in PRIMES if p % 8 == 7] == [31, 47])

print("== B: fresh numpy float64 Gray-code Ryser recompute (m <= 18) ==")


def ryser_np(A):
    """Permanent by Ryser/Gray code; A is (m, m) float64."""
    m = A.shape[0]
    row = np.zeros(m)
    total = 0.0
    sign = 1  # sign of (-1)^(m - |T|) bookkeeping via Gray walk
    gray = 0
    for c in range(1, 1 << m):
        nxt = c ^ (c >> 1)
        bit = gray ^ nxt
        j = bit.bit_length() - 1
        if nxt & bit:
            row += A[:, j]
        else:
            row -= A[:, j]
        gray = nxt
        k = bin(gray).count("1")
        total += (-1) ** (m - k) * np.prod(row)
    return total


def s_float(n):
    m = (n - 1) // 2
    jk = np.outer(np.arange(1, m + 1), np.arange(1, m + 1))
    M = np.sin(2 * np.pi * jk / n)
    return 2 ** m / math.sqrt(n) * ryser_np(M)


def sp_float(p):
    m = (p - 1) // 2
    jk = np.outer(np.arange(1, m + 1), np.arange(1, m + 1))
    M = 1.0 / np.sin(2 * np.pi * jk / p)
    return math.sqrt(p) / 2 ** m * ryser_np(M)


for n in [3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37]:
    v = s_float(n)
    check(f"float Ryser s_{n} ~ {S[n]} (got {v:.3f})",
          abs(v - S[n]) < max(1e-6 * abs(S[n]), 0.5))
for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
    v = sp_float(p)
    check(f"float Ryser s'_{p} ~ {SP[p]} (got {v:.3f})",
          abs(v - SP[p]) < max(1e-6 * abs(SP[p]), 0.5))

print()
print("ALL NOTE CHECKS PASS" if ok else "SOME CHECKS FAILED")
raise SystemExit(0 if ok else 1)
