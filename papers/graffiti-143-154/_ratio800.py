import numpy as np, itertools
from collections import deque

def ratio(t1, p, t2):
    n = t1 + p + t2
    E = list(itertools.combinations(range(t1), 2)) \
        + list(itertools.combinations(range(t1 + p, n), 2))
    chain = [0] + list(range(t1, t1 + p)) + [t1 + p]
    E += list(zip(chain, chain[1:]))
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v); adj[v].append(u)
    W = 0
    for s in range(n):
        d = [-1] * n; d[s] = 0; q = deque([s])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if d[w] < 0:
                    d[w] = d[u] + 1; q.append(w)
        W += sum(d)
    W //= 2
    A = np.zeros((n, n))
    for u, v in E:
        A[u, v] = A[v, u] = 1
    pos = np.linalg.eigvalsh(A); pos = pos[pos > 1e-9]
    m = len(E); var = pos.var()
    rhs_n2 = m * n * n / (2 * W)
    rhs_dp = m * n * (n - 1) / (2 * W)
    print(f"D({t1},{p},{t2}) n={n} k={len(pos)} var={var:.3f} "
          f"ratio_N2={var/rhs_n2:.4f} ratio_DP={var/rhs_dp:.4f}")

ratio(800, 40, 800)
