#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
validate_induction.py -- computational validation for theorem/induction-transfer.md
(Davila Conjecture 9 chain family: Z(G_k) = 3k+1, gamma(G_k) = floor(7k/3)).

Pure stdlib (random tests are deterministic, seeded). Exit code 0 iff every
check passes; every check prints PASS/FAIL.

Sections
  A  construction hygiene (k <= KMAX): cubic, connected, triangle-free;
     edge-set comparison against ../chain_indep_k*.edges for k = 2..8
  B  pieces B1, B2: Z(B1) = Z(B2) = 4 exactly (exhaustive over all 3-sets,
     witness 4-sets verified); emits b1.edges / b2.edges for the Rust
     cross-check; also recomputes Z on every piece of G_5 cut at its bridges
  C  transfer-lemma arithmetic vs certified values (k = 2..5): the bound
     sum_i Z(P_i) - (k-1) = 3k+1 equals the certified Z at every point
  D  randomized validation of the cut lemma Z(G) >= sum_i Z(G[V_i]) - |B|
     (single-bridge sums, three-piece bridge chains, random partitions)
  E  gamma window gadgets: quasi-domination minima with free boundary
     vertices: EMM = MMM = MME = 7, EME (= G_3, no free vertices) >= 7;
     single-block minima = 2; two independent implementations cross-checked;
     plus the closed-neighborhood counting facts used in the by-hand proof
  F  explicit dominating pattern D_k: dominates, |D_k| = floor(7k/3), k = 2..KMAX
  G  explicit forcing set S_k: forces, |S_k| = 3k+1, k = 2..KMAX
  H  exhaustive re-verification: k=2 (no 3-set dominates, no 6-set forces),
     k=3 (no 6-set dominates, no 9-set forces)  [k=3 zf is the slow one,
     ~1-2 min; skip with --skip-slow]

Usage:  python validate_induction.py [--kmax N] [--skip-slow]
"""

import os
import sys
import random
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
KILLDIR = os.path.dirname(HERE)

FAILURES = []


def report(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    print(f"  [{tag}] {name}" + (f"  -- {detail}" if detail else ""), flush=True)
    if not ok:
        FAILURES.append(name)


# ------------------------------------------------------------------ family
def chain(k):
    """The family G_k ('indep' variant), identical to chain_study.chain(k).

    Returns (n, edges, blocks); blocks[i] = dict with keys a, b, subs, verts.
    Block 0 and block k-1 (end blocks): one subdivided edge a0b0 -> s.
    Middle blocks: subdivided a0b0 -> s (in) and a1b1 -> t (out).
    Bridge: previous block's last sub -> this block's first sub.
    """
    edges = []
    blocks = []
    offset = 0
    out_prev = None
    for i in range(k):
        a = [offset + 0, offset + 1, offset + 2]
        b = [offset + 3, offset + 4, offset + 5]
        if i == 0 or i == k - 1:
            subdiv = [(a[0], b[0])]
        else:
            subdiv = [(a[0], b[0]), (a[1], b[1])]
        subs = [offset + 6 + j for j in range(len(subdiv))]
        for u in a:
            for v in b:
                if (u, v) not in subdiv:
                    edges.append((u, v))
        for (u, v), s in zip(subdiv, subs):
            edges.append((u, s))
            edges.append((v, s))
        if out_prev is not None:
            edges.append((out_prev, subs[0]))
        blocks.append({"a": a, "b": b, "subs": subs,
                       "verts": list(range(offset, offset + 6 + len(subs)))})
        out_prev = subs[-1]
        offset += 6 + len(subs)
    return offset, edges, blocks


# ------------------------------------------------------------------ basics
def masks(n, edges):
    nbr = [0] * n
    for u, v in edges:
        assert u != v and not (nbr[u] >> v) & 1, "multi-edge/loop"
        nbr[u] |= 1 << v
        nbr[v] |= 1 << u
    return nbr


def is_connected(n, nbr):
    if n == 0:
        return True
    seen = 1
    frontier = 1
    while frontier:
        newly = 0
        b = frontier
        v = 0
        while b:
            if b & 1:
                newly |= nbr[v]
            b >>= 1
            v += 1
        frontier = newly & ~seen
        seen |= newly
    return seen == (1 << n) - 1


def triangle_free(n, nbr):
    for u in range(n):
        for v in range(u + 1, n):
            if (nbr[u] >> v) & 1 and nbr[u] & nbr[v]:
                return False
    return True


def closure(n, nbr, blue):
    while True:
        forced = 0
        b = blue
        v = 0
        while b:
            if b & 1:
                w = nbr[v] & ~blue
                if w and (w & (w - 1)) == 0:
                    forced |= w
            b >>= 1
            v += 1
        forced &= ~blue
        if not forced:
            return blue
        blue |= forced
    return blue


def forces(n, nbr, S):
    blue = 0
    for v in S:
        blue |= 1 << v
    return closure(n, nbr, blue) == (1 << n) - 1


def z_exact(n, nbr):
    """Exhaustive zero forcing number (small n only)."""
    full = (1 << n) - 1
    if n == 0:
        return 0
    for r in range(1, n + 1):
        for sub in combinations(range(n), r):
            blue = 0
            for v in sub:
                blue |= 1 << v
            if closure(n, nbr, blue) == full:
                return r
    raise AssertionError("unreachable")


def no_forcing_set_of_size(n, nbr, r):
    full = (1 << n) - 1
    for sub in combinations(range(n), r):
        blue = 0
        for v in sub:
            blue |= 1 << v
        if closure(n, nbr, blue) == full:
            return False, sub
    return True, None


def dominates(n, closed, S, target):
    cov = 0
    for v in S:
        cov |= closed[v]
    return cov & target == target


def no_dominating_set_of_size(n, nbr, r, target=None):
    closed = [nbr[v] | (1 << v) for v in range(n)]
    if target is None:
        target = (1 << n) - 1
    for sub in combinations(range(n), r):
        if dominates(n, closed, sub, target):
            return False, sub
    return True, None


def induced(n, edges, keep):
    keep = sorted(keep)
    idx = {v: i for i, v in enumerate(keep)}
    ks = set(keep)
    e2 = [(idx[u], idx[v]) for u, v in edges if u in ks and v in ks]
    return len(keep), e2, idx


# ============================================================== section A
def section_A(kmax):
    print("== A: construction hygiene ==")
    for k in range(2, kmax + 1):
        n, edges, blocks = chain(k)
        nbr = masks(n, edges)
        ok = (n == 8 * k - 2
              and all(bin(m).count("1") == 3 for m in nbr)
              and is_connected(n, nbr)
              and triangle_free(n, nbr))
        if k <= 6 or k == kmax:
            report(f"G_{k}: n=8k-2={n}, cubic, connected, triangle-free", ok)
        elif not ok:
            report(f"G_{k}: hygiene", False)
    # not bipartite: exhibit the 5-cycle a0-b1-a1-b0-s in block 0
    n, edges, blocks = chain(2)
    es = set(map(frozenset, edges))
    c5 = [(0, 4), (4, 1), (1, 3), (3, 6), (6, 0)]
    report("G_k not bipartite (5-cycle a0-b1-a1-b0-s exists in block 1)",
           all(frozenset(e) in es for e in c5))
    # compare with the shipped edge files
    for k in range(2, 9):
        path = os.path.join(KILLDIR, f"chain_indep_k{k}.edges")
        with open(path) as f:
            first = f.readline().split()
            nf, mf = int(first[0]), int(first[1])
            ef = [tuple(map(int, line.split())) for line in f if line.strip()]
        n, edges, _ = chain(k)
        same = (nf == n and mf == len(edges)
                and set(map(frozenset, ef)) == set(map(frozenset, edges)))
        report(f"chain({k}) edge set == chain_indep_k{k}.edges", same)


# ============================================================== section B
def piece_graphs():
    """B1 (end piece, 7 vts) and B2 (middle piece, 8 vts), built directly."""
    # B1: K3,3 on {0,1,2}|{3,4,5}, edge (0,3) subdivided by 6
    e1 = [(u, v) for u in (0, 1, 2) for v in (3, 4, 5) if (u, v) != (0, 3)]
    e1 += [(0, 6), (3, 6)]
    # B2: additionally (1,4) subdivided by 7
    e2 = [(u, v) for u in (0, 1, 2) for v in (3, 4, 5)
          if (u, v) not in ((0, 3), (1, 4))]
    e2 += [(0, 6), (3, 6), (1, 7), (4, 7)]
    return (7, e1), (8, e2)


def section_B():
    print("== B: pieces B1, B2 ==")
    (n1, e1), (n2, e2) = piece_graphs()
    nbr1, nbr2 = masks(n1, e1), masks(n2, e2)
    # upper bounds: the explicit witnesses used in the writeup
    report("B1: {a0,a1,b0,b1} = {0,1,3,4} is a forcing set",
           forces(n1, nbr1, [0, 1, 3, 4]))
    report("B2: {s,a1,b0,b1} = {6,1,3,4} is a forcing set",
           forces(n2, nbr2, [6, 1, 3, 4]))
    # lower bounds: exhaustive
    ok1, wit1 = no_forcing_set_of_size(n1, nbr1, 3)
    report("B1: NO 3-set forces (all C(7,3)=35 checked)  => Z(B1) = 4",
           ok1, f"counterexample {wit1}" if not ok1 else "")
    ok2, wit2 = no_forcing_set_of_size(n2, nbr2, 3)
    report("B2: NO 3-set forces (all C(8,3)=56 checked)  => Z(B2) = 4",
           ok2, f"counterexample {wit2}" if not ok2 else "")
    # exact values via independent exhaustive routine
    report("B1: z_exact == 4", z_exact(n1, nbr1) == 4)
    report("B2: z_exact == 4", z_exact(n2, nbr2) == 4)
    # emit edge files for the Rust dual check
    for name, (n, e) in (("b1.edges", (n1, e1)), ("b2.edges", (n2, e2))):
        with open(os.path.join(HERE, name), "w", newline="\n") as f:
            f.write(f"{n} {len(e)}\n")
            for u, v in e:
                f.write(f"{u} {v}\n")
    print("  (emitted b1.edges, b2.edges for rust_check dual verification)")
    # every piece of G_5 cut at its bridges has Z = 4
    n, edges, blocks = chain(5)
    bridge_set = bridges_of(blocks)
    e_cut = [e for e in edges if frozenset(e) not in bridge_set]
    allok = True
    for i, blk in enumerate(blocks):
        np_, ep_, _ = induced(n, e_cut, blk["verts"])
        zi = z_exact(np_, masks(np_, ep_))
        if zi != 4:
            allok = False
    report("G_5 cut at all 4 bridges: every piece has Z = 4", allok)


def bridges_of(blocks):
    out = set()
    for i in range(len(blocks) - 1):
        out.add(frozenset((blocks[i]["subs"][-1], blocks[i + 1]["subs"][0])))
    return out


# ============================================================== section C
def section_C():
    print("== C: transfer bound vs certified values ==")
    certified_Z = {2: 7, 3: 10, 4: 13, 5: 16}
    ok = True
    for k, z in certified_Z.items():
        bound = 4 * k - (k - 1)
        line = f"k={k}: bound sum Z(P_i)-(k-1) = {bound}, certified Z = {z}"
        if bound != z:
            ok = False
        print(f"    {line}")
    report("transfer bound 3k+1 EQUALS certified Z at k = 2,3,4,5 (tight)", ok)


# ============================================================== section D
def random_connected(rng, n, p=0.42):
    while True:
        edges = [(u, v) for u in range(n) for v in range(u + 1, n)
                 if rng.random() < p]
        nbr = masks(n, edges)
        if is_connected(n, nbr):
            return edges


def z_of_subgraph(n, edges, part):
    np_, ep_, _ = induced(n, edges, part)
    return z_exact(np_, masks(np_, ep_)) if np_ else 0


def section_D():
    print("== D: randomized cut-lemma validation ==")
    rng = random.Random(20260612)
    t0 = time.time()
    # 1) single bridge sums
    viol = 0
    trials1 = 300
    for _ in range(trials1):
        na, nb = rng.randint(4, 7), rng.randint(4, 7)
        ea = random_connected(rng, na)
        eb = random_connected(rng, nb)
        za = z_exact(na, masks(na, ea))
        zb = z_exact(nb, masks(nb, eb))
        u, v = rng.randrange(na), rng.randrange(nb)
        n = na + nb
        edges = ea + [(na + x, na + y) for x, y in eb] + [(u, na + v)]
        zg = z_exact(n, masks(n, edges))
        if zg < za + zb - 1:
            viol += 1
    report(f"single-bridge: Z(A#B) >= Z(A)+Z(B)-1 in {trials1} random trials",
           viol == 0, f"{viol} violations")
    # 2) three-piece bridge chains
    viol = 0
    trials2 = 120
    for _ in range(trials2):
        sizes = [rng.randint(3, 5) for _ in range(3)]
        pieces = [random_connected(rng, s) for s in sizes]
        zs = [z_exact(s, masks(s, e)) for s, e in zip(sizes, pieces)]
        off = [0, sizes[0], sizes[0] + sizes[1]]
        n = sum(sizes)
        edges = []
        for i, e in enumerate(pieces):
            edges += [(off[i] + x, off[i] + y) for x, y in e]
        edges.append((off[0] + rng.randrange(sizes[0]),
                      off[1] + rng.randrange(sizes[1])))
        edges.append((off[1] + rng.randrange(sizes[1]),
                      off[2] + rng.randrange(sizes[2])))
        zg = z_exact(n, masks(n, edges))
        if zg < sum(zs) - 2:
            viol += 1
    report(f"three-piece chain: Z >= Z1+Z2+Z3-2 in {trials2} random trials",
           viol == 0, f"{viol} violations")
    # 3) arbitrary partitions, arbitrary crossing-edge sets
    viol = 0
    trials3 = 200
    for _ in range(trials3):
        n = rng.randint(7, 9)
        edges = random_connected(rng, n)
        r = rng.choice((2, 3))
        while True:
            lab = [rng.randrange(r) for _ in range(n)]
            if len(set(lab)) == r:
                break
        parts = [[v for v in range(n) if lab[v] == i] for i in range(r)]
        nb = sum(1 for u, v in edges if lab[u] != lab[v])
        zsum = sum(z_of_subgraph(n, edges, p) for p in parts)
        zg = z_exact(n, masks(n, edges))
        if zg < zsum - nb:
            viol += 1
    report(f"random partition: Z(G) >= sum Z(G[V_i]) - |B| in {trials3} trials",
           viol == 0, f"{viol} violations")
    print(f"    (section D time: {time.time()-t0:.1f}s)")


# ============================================================== section E
def quasidom_min_bitmask(n, edges, target_verts, maxsize):
    """Smallest X with N[X] >= target (bitmask impl); None if > maxsize."""
    nbr = masks(n, edges)
    closed = [nbr[v] | (1 << v) for v in range(n)]
    target = 0
    for v in target_verts:
        target |= 1 << v
    for r in range(0, maxsize + 1):
        for sub in combinations(range(n), r):
            cov = 0
            for v in sub:
                cov |= closed[v]
            if cov & target == target:
                return r
    return None


def quasidom_min_sets(n, edges, target_verts, maxsize):
    """Same computation, independent set-based implementation."""
    adj = {v: {v} for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    target = set(target_verts)
    for r in range(0, maxsize + 1):
        for sub in combinations(range(n), r):
            cov = set()
            for v in sub:
                cov |= adj[v]
            if target <= cov:
                return r
    return None


def window_gadget(k, i):
    """Window = blocks i, i+1, i+2 of G_k. Returns (nw, ew, target_local).

    target = window vertices that MUST be dominated from inside the window
    (everything except boundary sub-vertices that have a G-neighbor outside).
    """
    n, edges, blocks = chain(k)
    W = blocks[i]["verts"] + blocks[i + 1]["verts"] + blocks[i + 2]["verts"]
    free = set()
    if i > 0:
        free.add(blocks[i]["subs"][0])        # s_i, dominated by t_{i-1}
    if i + 2 < k - 1:
        free.add(blocks[i + 2]["subs"][-1])   # t_{i+2}, dominated by s_{i+3}
    nw, ew, idx = induced(n, edges, W)
    target = [idx[v] for v in W if v not in free]
    # sanity: every non-free window vertex has all its G-neighbors inside W
    nbr = masks(n, edges)
    ws = set(W)
    for v in W:
        outside = [u for u in range(n) if (nbr[v] >> u) & 1 and u not in ws]
        if v in free:
            assert len(outside) == 1, "free vertex must have exactly 1 outside nbr"
        else:
            assert not outside, f"non-free window vertex {v} has outside nbr"
    return nw, ew, target


def single_block_gadget(k, i):
    n, edges, blocks = chain(k)
    V = blocks[i]["verts"]
    free = set(blocks[i]["subs"])  # subs that have an outside neighbor
    if i == 0:
        free = {blocks[i]["subs"][0]}   # end block: s only (its bridge nbr)
    if i == k - 1:
        free = {blocks[i]["subs"][-1]}
    nv, ev, idx = induced(n, edges, V)
    target = [idx[v] for v in V if v not in free]
    return nv, ev, target


def section_E():
    print("== E: gamma window gadgets ==")
    t0 = time.time()
    shapes = [("EMM (blocks 1..3 of G_5)", 5, 0),
              ("MMM (blocks 2..4 of G_5)", 5, 1),
              ("MME (blocks 3..5 of G_5)", 5, 2)]
    for name, k, i in shapes:
        nw, ew, target = window_gadget(k, i)
        m1 = quasidom_min_bitmask(nw, ew, target, 7)
        m2 = quasidom_min_sets(nw, ew, target, 7)
        report(f"window {name}: quasi-domination minimum = 7 "
               f"(all <=6-subsets of {nw} vertices fail)",
               m1 == 7 and m2 == 7, f"impl1={m1}, impl2={m2}")
    # EME = the whole of G_3, no free vertices: gamma(G_3) >= 7
    n3, e3, _ = chain(3)
    m1 = quasidom_min_bitmask(n3, e3, list(range(n3)), 7)
    m2 = quasidom_min_sets(n3, e3, list(range(n3)), 7)
    report("window EME (= G_3 itself): domination minimum = 7  (gamma(G_3)=7)",
           m1 == 7 and m2 == 7, f"impl1={m1}, impl2={m2}")
    # single blocks need >= 2 even with all boundary subs free
    for name, k, i in [("end block", 5, 0), ("middle block", 5, 2),
                       ("end block (right)", 5, 4)]:
        nv, ev, target = single_block_gadget(k, i)
        m1 = quasidom_min_bitmask(nv, ev, target, 3)
        m2 = quasidom_min_sets(nv, ev, target, 3)
        report(f"single {name}: quasi-domination minimum = 2", m1 == 2 == m2,
               f"impl1={m1}, impl2={m2}")
    # counting fact used in the by-hand proof of Lemma (block >= 2):
    # every vertex of a block covers at most 4 of the block's six K3,3 vertices,
    # and those six vertices have closed neighborhoods inside the block
    n, edges, blocks = chain(5)
    nbr = masks(n, edges)
    okA = okB = True
    for blk in blocks:
        six = set(blk["a"] + blk["b"])
        ws = set(blk["verts"])
        for v in six:
            nb = {u for u in range(n) if (nbr[v] >> u) & 1}
            if not nb <= ws:
                okA = False
        for v in blk["verts"]:
            nb = {u for u in range(n) if (nbr[v] >> u) & 1} | {v}
            if len(nb & six) > 4:
                okB = False
    report("six K3,3-vertices of each block have N[.] inside the block", okA)
    report("every block vertex covers <= 4 of its block's six K3,3-vertices", okB)
    print(f"    (section E time: {time.time()-t0:.1f}s)")


# ============================================================== section F
def dominating_pattern(k):
    """Explicit dominating set of size floor(7k/3) (Theorem gamma-upper).

    Configurations (local labels within a block):
      2A  = {a0, b0}            2B  = {a1, b1}
      T3  = {s, t, a2}          T3' = {a0, b0, t}
    Sequence:
      k = 2:          [2A, 2A]
      k = 3m+1, m>=1: [2A] + m * [2A, T3, 2B]
      k = 3m+2, m>=0: [2A] + m * [2A, T3, 2B] + [2A]
      k = 3m,   m>=1: [2A] + (m-1) * [2A, T3, 2B] + [T3', 2B]
    """
    n, edges, blocks = chain(k)

    def conf(i, c):
        blk = blocks[i]
        a, b, subs = blk["a"], blk["b"], blk["subs"]
        if c == "2A":
            return [a[0], b[0]]
        if c == "2B":
            return [a[1], b[1]]
        if c == "T3":
            return [subs[0], subs[1], a[2]]
        if c == "T3p":
            return [a[0], b[0], subs[1]]
        raise ValueError(c)

    if k == 2:
        seq = ["2A", "2A"]
    elif k % 3 == 1:
        seq = ["2A"] + ["2A", "T3", "2B"] * ((k - 1) // 3)
    elif k % 3 == 2:
        seq = ["2A"] + ["2A", "T3", "2B"] * ((k - 2) // 3) + ["2A"]
    else:
        seq = ["2A"] + ["2A", "T3", "2B"] * ((k - 3) // 3) + ["T3p", "2B"]
    assert len(seq) == k
    D = []
    for i, c in enumerate(seq):
        D += conf(i, c)
    return n, edges, D


def section_F(kmax):
    print("== F: explicit dominating pattern ==")
    allok = True
    for k in range(2, kmax + 1):
        n, edges, D = dominating_pattern(k)
        nbr = masks(n, edges)
        closed = [nbr[v] | (1 << v) for v in range(n)]
        ok = dominates(n, closed, D, (1 << n) - 1) and len(D) == 7 * k // 3
        if not ok:
            allok = False
            report(f"pattern k={k}", False, f"|D|={len(D)} vs {7*k//3}")
    report(f"D_k dominates G_k and |D_k| = floor(7k/3) for k = 2..{kmax}", allok)


# ============================================================== section G
def forcing_pattern(k):
    """Explicit forcing set of size 3k+1: block 1 gets {a0,a1,b0,b1},
    every other block gets {a1, b0, b1}."""
    n, edges, blocks = chain(k)
    S = blocks[0]["a"][0:2] + blocks[0]["b"][0:2]
    for blk in blocks[1:]:
        S += [blk["a"][1], blk["b"][0], blk["b"][1]]
    return n, edges, S


def section_G(kmax):
    print("== G: explicit forcing set ==")
    allok = True
    for k in range(2, kmax + 1):
        n, edges, S = forcing_pattern(k)
        nbr = masks(n, edges)
        ok = forces(n, nbr, S) and len(S) == 3 * k + 1
        if not ok:
            allok = False
            report(f"forcing pattern k={k}", False, f"|S|={len(S)}")
    report(f"S_k forces G_k and |S_k| = 3k+1 for k = 2..{kmax}", allok)


# ============================================================== section H
def section_H(skip_slow):
    print("== H: exhaustive re-verification (k=2, k=3) ==")
    n2, e2, _ = chain(2)
    nbr2 = masks(n2, e2)
    ok, wit = no_dominating_set_of_size(n2, nbr2, 3)
    report("G_2: no 3-set dominates (C(14,3)=364)  => gamma >= 4", ok)
    ok, wit = no_forcing_set_of_size(n2, nbr2, 6)
    report("G_2: no 6-set forces (C(14,6)=3003)    => Z >= 7", ok)
    n3, e3, _ = chain(3)
    nbr3 = masks(n3, e3)
    ok, wit = no_dominating_set_of_size(n3, nbr3, 6)
    report("G_3: no 6-set dominates (C(22,6)=74613) => gamma >= 7", ok)
    if skip_slow:
        print("    (skipping G_3 zero-forcing brute force, --skip-slow)")
    else:
        t0 = time.time()
        ok, wit = no_forcing_set_of_size(n3, nbr3, 9)
        report(f"G_3: no 9-set forces (C(22,9)=497420, {time.time()-t0:.0f}s) "
               "=> Z >= 10", ok)


# ================================================================== main
def main():
    kmax = 40
    skip_slow = "--skip-slow" in sys.argv
    for i, a in enumerate(sys.argv):
        if a == "--kmax":
            kmax = int(sys.argv[i + 1])
    t0 = time.time()
    section_A(kmax)
    section_B()
    section_C()
    section_D()
    section_E()
    section_F(kmax)
    section_G(kmax)
    section_H(skip_slow)
    print()
    if FAILURES:
        print(f"OVERALL: {len(FAILURES)} FAILURES: {FAILURES}")
        sys.exit(1)
    print(f"OVERALL: ALL CHECKS PASS  ({time.time()-t0:.1f}s total)")
    sys.exit(0)


if __name__ == "__main__":
    main()
