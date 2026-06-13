import numpy as np, itertools
from collections import deque

def dumbbell_check(t1, p, t2):
    n = t1 + p + t2
    E  = list(itertools.combinations(range(t1), 2))
    E += list(itertools.combinations(range(t1 + p, n), 2))
    chain = [0] + list(range(t1, t1 + p)) + [t1 + p]
    E += list(zip(chain, chain[1:]))
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    W = 0
    for s in range(n):
        d = [-1] * n; d[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if d[w] < 0: d[w] = d[u] + 1; q.append(w)
        W += sum(d)
    W //= 2
    A = np.zeros((n, n))
    for u, v in E: A[u, v] = A[v, u] = 1
    pos = np.linalg.eigvalsh(A); pos = pos[pos > 1e-9]
    m, var = len(E), pos.var()
    rhs_n2 = m*n*n/(2*W); rhs_pairs = m*n*(n-1)/(2*W)
    print(f"dumbbell({t1},{p},{t2}) n={n} m={m} W={W} k={len(pos)} "
          f"var={var:.9f} RHS_N2={rhs_n2:.9f} RHS_PAIRS={rhs_pairs:.9f} "
          f"marginN2={var-rhs_n2:+.6f} ratioN2={var/rhs_n2:.4f}")

for args in [(7,12,20),(6,12,19),(20,8,20),(8,12,20),(6,12,20),(40,10,40)]:
    dumbbell_check(*args)

# 154 proposition base cases, pure integers
def lolli(t, p):
    n, m = t+p, t*(t-1)//2 + p
    W = t*(t-1)//2 + sum(k + (t-1)*(k+1) for k in range(1, p+1)) + (p+1)*p*(p-1)//6
    return n, m, W

for t in [70, 71, 72, 100, 200]:
    n, m, W = lolli(t, t)
    Wclosed = (2*t**3 + 6*t**2 - 5*t)//3
    assert W == Wclosed, (t, W, Wclosed)
    dp = 8*m*W*W > n**5*(n-1)**2
    n2 = 8*m*W*W > n**7
    print(f"lollipop({t},{t}): n={n} W={W} closed-form-ok violates DP={dp} N2={n2}")
