# Checker: accepts iff (1) identity holds n=1..NMAX, (2) refined lemma holds exhaustively n<=7
# Mutations: corrupt the a284005 recursion / minima map and confirm rejection.
from functools import lru_cache
from collections import Counter
import sys

def make_a(mult_offset=1, base=1):
    @lru_cache(maxsize=None)
    def a(n):
        return base if n == 0 else (mult_offset + bin(n).count('1')) * a(n // 2)
    return a

def fubini_list(N):
    from math import comb
    F=[1]
    for m in range(1,N+1): F.append(sum(comb(m,k)*F[m-k] for k in range(1,m+1)))
    return F

def gen_osps(n):
    current=[((1,),)]
    for j in range(2,n+1):
        nxt=[]
        for osp in current:
            m=len(osp)
            for i in range(m):
                nxt.append(tuple(osp[t]+((j,) if t==i else ()) for t in range(m)))
            for pos in range(m+1):
                nxt.append(tuple(list(osp[:pos])+[(j,)]+list(osp[pos:])))
        current=nxt
    return current

def run(a, minshift=2):
    NMAX=14
    F=fubini_list(NMAX)
    for n in range(1,NMAX+1):
        if F[n]!=sum(a(k) for k in range(2**(n-1))): return False,f"identity fails n={n}"
    for n in range(1,8):
        cnt=Counter()
        for osp in gen_osps(n):
            cnt[frozenset(min(b) for b in osp)]+=1
        for k in range(2**(n-1)):
            bits=[(k>>(n-2-i))&1 for i in range(n-1)] if n>1 else []
            M=frozenset([1]+[i+minshift for i,b in enumerate(bits) if b])
            if cnt.get(M,0)!=a(k): return False,f"lemma fails n={n} k={k}"
    return True,"ok"

ok,msg = run(make_a())
print("PRISTINE:", "ACCEPT" if ok else "REJECT", msg)
muts = [("mult_offset=2", make_a(mult_offset=2), 2),
        ("base=2",        make_a(base=2), 2),
        ("minima shifted",make_a(), 3)]
allkilled=True
for name,a,shift in muts:
    ok,msg = run(a,minshift=shift)
    print(f"MUTANT {name}:", "REJECTED" if not ok else "!!! ACCEPTED !!!", f"({msg})")
    allkilled &= not ok
print("VERDICT:", "PASS" if allkilled else "FAIL")
