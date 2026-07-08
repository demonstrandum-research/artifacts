# Refined lemma: for b = b_1..b_{n-1} (MSB-first bits of k, zero-padded),
#   a284005(k) = #{ordered set partitions P of [n] : element j is a block-min of P iff j=1 or b_{j-1}=1}
# Exhaustive check for n = 1..8 by direct enumeration of ALL ordered set partitions.
from functools import lru_cache
from itertools import permutations
import sys
sys.setrecursionlimit(10000)

@lru_cache(maxsize=None)
def a284005(n):
    return 1 if n == 0 else (1 + bin(n).count('1')) * a284005(n // 2)

def gen_osps(n):
    # incremental insertion generator: yields tuple of frozensets in order
    parts = [ (( (1,), ),) ]
    current = [((1,),)]
    for j in range(2, n+1):
        nxt = []
        for osp in current:
            m = len(osp)
            for i in range(m):  # join block i
                nxt.append(tuple(osp[t] + ((j,) if t == i else ()) for t in range(m)))
            for pos in range(m+1):  # new singleton at position pos
                nxt.append(tuple(list(osp[:pos]) + [(j,)] + list(osp[pos:])))
        current = nxt
    return current

NMAX = 8
allok = True
for n in range(1, NMAX+1):
    from collections import Counter
    cnt = Counter()
    for osp in gen_osps(n):
        mins = frozenset(min(b) for b in osp)
        cnt[mins] += 1
    total = sum(cnt.values())
    ok = True
    for k in range(2**(n-1)):
        bits = [(k >> (n-2-i)) & 1 for i in range(n-1)] if n > 1 else []
        M = frozenset([1] + [i+2 for i, b in enumerate(bits) if b])
        if cnt.get(M, 0) != a284005(k):
            ok = False
            print(f"MISMATCH n={n} k={k}: enum={cnt.get(M,0)} a284005={a284005(k)}")
    allok &= ok
    print(f"n={n}: OSPs={total} (Fubini ok: {total==sum(a284005(k) for k in range(2**(n-1)))}), refined lemma all {2**(n-1)} minima-sets: {'OK' if ok else 'FAIL'}")
print("REFINED LEMMA EXHAUSTIVE n<=%d:" % NMAX, "PASS" if allok else "FAIL")
