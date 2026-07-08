# Ground truth: verify Kurkov 2018 conjecture in A000670 numerically, n=1..20
# a284005 per OEIS definition: a(0)=1, a(n)=(1+wt(n))*a(n//2)
import sys
from functools import lru_cache

@lru_cache(maxsize=None)
def a284005(n):
    if n == 0: return 1
    return (1 + bin(n).count('1')) * a284005(n // 2)

def fubini(n):  # independent route: recurrence F(n) = sum C(n,k) F(n-k), k>=1
    from math import comb
    F = [1]
    for m in range(1, n+1):
        F.append(sum(comb(m, k) * F[m-k] for k in range(1, m+1)))
    return F[n]

ok = True
for n in range(1, 21):
    lhs = fubini(n)
    rhs = sum(a284005(k) for k in range(2**(n-1)))
    match = (lhs == rhs)
    ok &= match
    if n <= 8 or not match:
        print(f"n={n}: Fubini={lhs}  sum={rhs}  match={match}")
print("ALL MATCH n=1..20:", ok)
