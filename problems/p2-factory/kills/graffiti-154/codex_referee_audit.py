from collections import deque
import math

import numpy as np


def lollipop_edges(t, p):
    edges = []
    for i in range(t):
        for j in range(i + 1, t):
            edges.append((i, j))
    if p:
        edges.append((0, t))
        for k in range(p - 1):
            edges.append((t + k, t + k + 1))
    return edges


def wiener_by_bfs(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    total = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        q = deque([s])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1
                    q.append(v)
        if any(d < 0 for d in dist):
            raise RuntimeError("disconnected")
        total += sum(dist)
    assert total % 2 == 0
    return total // 2


def wiener_formula(t, p):
    clique = t * (t - 1) // 2
    cross = sum(k + (t - 1) * (k + 1) for k in range(1, p + 1))
    path = (p + 1) * p * (p - 1) // 6
    return clique + cross + path


def integer_margins(t, p):
    n = t + p
    m = t * (t - 1) // 2 + p
    W = wiener_formula(t, p)
    lhs = 8 * m * W * W
    rhs_dp = n**5 * (n - 1) ** 2
    rhs_n2 = n**7
    return n, m, W, lhs, rhs_dp, rhs_n2


def dense_energy(t, p):
    n = t + p
    A = np.zeros((n, n), dtype=float)
    for u, v in lollipop_edges(t, p):
        A[u, v] = 1.0
        A[v, u] = 1.0
    vals = np.linalg.eigvalsh(A)
    return float(np.abs(vals).sum()), float(vals.sum()), float((vals * vals).sum())


def audit_instance(t, p):
    n, m, W, lhs, rhs_dp, rhs_n2 = integer_margins(t, p)
    W_bfs = wiener_by_bfs(n, lollipop_edges(t, p))
    if W != W_bfs:
        raise AssertionError((t, p, W, W_bfs))
    energy, tr, tr2 = dense_energy(t, p)
    mad = energy / n
    std = math.sqrt(2 * m / n)
    bound_dp = n * n * (n - 1) / (2 * W)
    bound_n2 = n**3 / (2 * W)
    print(f"({t},{p}) n={n} m={m} W={W}")
    print(f"  lhs={lhs}")
    print(f"  rhs_dp={rhs_dp} margin_dp={lhs-rhs_dp} violates_dp={lhs>rhs_dp}")
    print(f"  rhs_n2={rhs_n2} margin_n2={lhs-rhs_n2} violates_n2={lhs>rhs_n2}")
    print(f"  std={std:.15f} dp_bound={bound_dp:.15f} n2_bound={bound_n2:.15f}")
    print(f"  energy={energy:.15f} MAD={mad:.15f} trace={tr:.3e} trace2={tr2:.12f}")
    print(f"  MAD gaps: dp={bound_dp-mad:.12f} n2={bound_n2-mad:.12f}")


def scan_no_lollipop_below(limit):
    bad = []
    for n in range(2, limit + 1):
        for t in range(1, n):
            p = n - t
            _, _, _, lhs, rhs_dp, rhs_n2 = integer_margins(t, p)
            if lhs > rhs_dp or lhs > rhs_n2:
                bad.append((n, t, p, lhs > rhs_dp, lhs > rhs_n2))
    return bad


if __name__ == "__main__":
    for pair in [(72, 72), (50, 70), (48, 70)]:
        audit_instance(*pair)
    bad117 = scan_no_lollipop_below(117)
    print(f"violating lollipops with n<=117: {bad117[:10]} count={len(bad117)}")
    bad118 = scan_no_lollipop_below(118)
    print(f"first n<=118 violators: {bad118[:10]} count={len(bad118)}")
