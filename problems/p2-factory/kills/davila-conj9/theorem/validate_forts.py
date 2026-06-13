"""
validate_forts.py -- computational validation of every finite claim in
theorem/forcing-fort.md (the fort-lens proof that Z(G_k) = 3k+1 and
gamma(G_k) = floor(7k/3), hence Z - gamma -> infinity on the chain family).

Pure stdlib (no ortools), exact bitmask arithmetic. Exits nonzero on failure.
Independent of the sibling scripts validate_theorem.py / validate_gamma_exact.py
(same graphs, fresh code, fort-centric checks).

Sections:
  F1  construction == certified .edges artifacts (k=2..8); hypotheses k<=20
  F2  fort machinery sanity, in situ on G_2: every non-forcing 6-set has a
      disjoint fort (transversal equivalence, exhaustive over C(14,6)=3003);
      every forcing 7-set hits every fort of G_2 (obstruction, exhaustive)
  F3  standalone block graphs R_end (7 vts), R_mid (8 vts):
      Z = 4 by brute force; full fort census; minimal forts; certificate:
      every 3-subset is disjoint from some minimal fort; minimum certificate
      subfamily; Aut groups; orbit tables emitted to fort_tables.md
  F4  local forts inside G_k (k<=6): block cores and F12/F13/F23 are forts;
      every fort of G_k contained in one block region avoids subdivision
      vertices; minimal region-local forts classified; per-region local
      transversal number = 2 (so local forts alone certify only Z >= 2k)
  F5  cut superadditivity lemma validated in situ:
      k=2: ALL forcing 7- and 8-sets, chronological replay, per-block
      accounting |B cap R_i| >= 4 - (injections into R_i), sum inj <= k-1;
      k=3,4: 300 random forcing sets each
  F6  Z upper bound: W_k forces, |W_k| = 3k+1 (k=2..40); W_2 == certified witness
  F7  gamma upper bound: D_k dominates, |D_k| = floor(7k/3) (k=2..40);
      D_2 == certified witness {0,3,7,10}
  F8  gamma lower bound block lemmas: single closed nbhd covers <=4 core
      vertices; 2-subsets of a region dominating the core are exactly the
      diagonal pairs (mid) / the five listed pairs (end); none contains a
      subdivision vertex; core isolation (k<=8)
  F9  independent gamma DP: gamma(G_k) == floor(7k/3) for k=2..60; anchors
      vs certified values k=2..8
  F10 formula consistency with the certified table
"""
import os
import random
import sys
from itertools import combinations, permutations

random.seed(126)
HERE = os.path.dirname(os.path.abspath(__file__))
KILLDIR = os.path.dirname(HERE)
FAIL = []


def check(cond, msg):
    print(f"  [{'ok ' if cond else 'FAIL'}] {msg}")
    if not cond:
        FAIL.append(msg)


# ----------------------------------------------------------------- structure
def chain(k):
    """G_k ('indep' variant), identical to the certified generator.
    blocks[i]: dict(a, b, s_in, s_out, verts)."""
    edges, blocks = [], []
    offset, out_sub_prev = 0, None
    for i in range(k):
        a = [offset, offset + 1, offset + 2]
        b = [offset + 3, offset + 4, offset + 5]
        subdiv = [(a[0], b[0])] if i in (0, k - 1) else [(a[0], b[0]), (a[1], b[1])]
        subs = [offset + 6 + j for j in range(len(subdiv))]
        for u in a:
            for v in b:
                if (u, v) not in subdiv:
                    edges.append((u, v))
        for (u, v), s in zip(subdiv, subs):
            edges.append((u, s))
            edges.append((v, s))
        if out_sub_prev is not None:
            edges.append((out_sub_prev, subs[0]))
        out_sub_prev = subs[-1]
        s_in = None if i == 0 else subs[0]
        s_out = None if i == k - 1 else subs[-1]
        blocks.append(dict(a=a, b=b, s_in=s_in, s_out=s_out,
                           verts=set(a) | set(b) | set(subs)))
        offset += 6 + len(subs)
    return offset, edges, blocks


def nbrm(n, edges):
    nbr = [0] * n
    for u, v in edges:
        assert u != v and not (nbr[u] >> v) & 1
        nbr[u] |= 1 << v
        nbr[v] |= 1 << u
    return nbr


def closure(n, nbr, blue):
    while True:
        forced = 0
        for v in range(n):
            if (blue >> v) & 1:
                w = nbr[v] & ~blue
                if w and (w & (w - 1)) == 0:
                    forced |= w
        if not forced:
            return blue
        blue |= forced


def is_fort(n, nbr, F):
    if F == 0:
        return False
    for v in range(n):
        if not (F >> v) & 1:
            x = nbr[v] & F
            if x and (x & (x - 1)) == 0:
                return False
    return True


def mask(vs):
    m = 0
    for v in vs:
        m |= 1 << v
    return m


def bits(m):
    out, v = [], 0
    while m:
        if m & 1:
            out.append(v)
        m >>= 1
        v += 1
    return out


# ================================================================ F1
print("== F1: construction vs artifacts; hypotheses ==")
for k in range(2, 9):
    n, edges, _ = chain(k)
    with open(os.path.join(KILLDIR, f"chain_indep_k{k}.edges")) as f:
        t = f.read().split()
    fn, fm = int(t[0]), int(t[1])
    fed = sorted(tuple(sorted((int(t[2 + 2 * i]), int(t[3 + 2 * i]))))
                 for i in range(fm))
    check(n == fn and sorted(tuple(sorted(e)) for e in edges) == fed,
          f"k={k}: rebuilt G_k == chain_indep_k{k}.edges")
for k in range(2, 21):
    n, edges, _ = chain(k)
    nbr = nbrm(n, edges)
    cubic = all(bin(m).count('1') == 3 for m in nbr)
    seen, fr = 1, 1
    while fr:
        nw = 0
        for v in bits(fr):
            nw |= nbr[v]
        fr = nw & ~seen
        seen |= nw
    conn = seen == (1 << n) - 1
    tri = all(nbr[u] & nbr[v] == 0 for u in range(n) for v in bits(nbr[u]) if v > u)
    check(cubic and conn and tri and n == 8 * k - 2,
          f"k={k}: cubic, connected, triangle-free, n=8k-2={n}")

# ================================================================ F2
print("== F2: fort machinery in situ on G_2 (transversal equivalence) ==")
n, edges, blocks = chain(2)
nbr = nbrm(n, edges)
full = (1 << n) - 1
allforts2 = [F for F in range(1, 1 << n) if is_fort(n, nbr, F)]
print(f"     G_2 has {len(allforts2)} forts")
ok = True
for S in combinations(range(n), 6):
    B = mask(S)
    cl = closure(n, nbr, B)
    if cl == full:
        ok = False  # would contradict certified Z(G_2)=7
        break
    F = full & ~cl
    if not is_fort(n, nbr, F) or F & B:
        ok = False
        break
check(ok, "G_2: every 6-set stalls and V minus closure is a fort disjoint from it "
          "(all C(14,6)=3003)")
ok = True
cnt = 0
for S in combinations(range(n), 7):
    B = mask(S)
    if closure(n, nbr, B) == full:
        cnt += 1
        if any(F & B == 0 for F in allforts2):
            ok = False
check(ok and cnt > 0, f"G_2: every forcing 7-set ({cnt} of them) hits every fort")

# ================================================================ F3
print("== F3: standalone block graphs, fort census + certificates ==")
# R_end: K3,3 on a={0,1,2}|b={3,4,5}, edge (a1,b1)=(0,3) subdivided by s=6.
# R_mid: also (a2,b2)=(1,4) subdivided; s1=6 (on a1b1), s2=7 (on a2b2).
def r_end():
    e = [(u, v) for u in (0, 1, 2) for v in (3, 4, 5) if (u, v) != (0, 3)]
    return 7, e + [(0, 6), (3, 6)]


def r_mid():
    e = [(u, v) for u in (0, 1, 2) for v in (3, 4, 5)
         if (u, v) not in ((0, 3), (1, 4))]
    return 8, e + [(0, 6), (3, 6), (1, 7), (4, 7)]


NM = {0: "a1", 1: "a2", 2: "a3", 3: "b1", 4: "b2", 5: "b3", 6: "s1", 7: "s2"}
NE = {0: "a1", 1: "a2", 2: "a3", 3: "b1", 4: "b2", 5: "b3", 6: "s"}


def pset(F, names):
    return "{" + ",".join(names[v] for v in bits(F)) + "}"


def autgroup(n, edges):
    es = set(tuple(sorted(e)) for e in edges)
    deg = [0] * n
    for u, v in es:
        deg[u] += 1
        deg[v] += 1
    return [p for p in permutations(range(n))
            if all(deg[p[v]] == deg[v] for v in range(n))
            and all(tuple(sorted((p[u], p[v]))) in es for u, v in es)]


emit = ["# Machine-emitted fort certificate tables for forcing-fort.md",
        "", "Generated by `validate_forts.py`. Vertex names: block parts "
        "a1,a2,a3 | b1,b2,b3; subdivision vertices s (end block), s1 on a1b1 "
        "and s2 on a2b2 (middle block).", ""]
CERT = {}
for name, build, names in (("R_end", r_end, NE), ("R_mid", r_mid, NM)):
    n, edges = build()
    nbr = nbrm(n, edges)
    full = (1 << n) - 1
    # Z(R) = 4 brute force
    no3 = all(closure(n, nbr, mask(c)) != full for c in combinations(range(n), 3))
    w4 = next(c for c in combinations(range(n), 4)
              if closure(n, nbr, mask(c)) == full)
    check(no3, f"{name}: NO 3-set forces (all C({n},3))")
    check(True, f"{name}: 4-set {pset(mask(w4), names)} forces => Z({name}) = 4")
    # fort census
    forts = [F for F in range(1, 1 << n) if is_fort(n, nbr, F)]
    minimal = [F for F in forts if not any(G != F and G & ~F == 0 for G in forts)]
    minimal.sort(key=lambda F: (bin(F).count('1'), F))
    print(f"     {name}: {len(forts)} forts, {len(minimal)} minimal: "
          + " ".join(pset(F, names) for F in minimal))
    bad = [c for c in combinations(range(n), 3)
           if all(mask(c) & F for F in minimal)]
    check(not bad, f"{name}: every 3-subset is disjoint from some minimal fort")
    # minimum certificate subfamily
    threes = [mask(c) for c in combinations(range(n), 3)]
    best = None
    for sz in range(1, len(minimal) + 1):
        for fam in combinations(minimal, sz):
            if all(any(F & B == 0 for F in fam) for B in threes):
                best = fam
                break
        if best:
            break
    CERT[name] = (best, minimal)
    print(f"     {name}: minimum certificate family, {len(best)} forts: "
          + " ".join(pset(F, names) for F in best))
    check(all(any(F & B == 0 for F in best) for B in threes),
          f"{name}: certificate family of {len(best)} forts covers all 3-subsets")
    # automorphisms preserve forts (needed for the orbit reduction)
    auts = autgroup(n, edges)
    pres = all(is_fort(n, nbr, mask([p[v] for v in bits(F)]))
               for p in auts for F in minimal)
    check(pres, f"{name}: |Aut| = {len(auts)}; automorphism images of forts are forts")
    # orbit table of 3-subsets with witness forts
    orb = {}
    for c in combinations(range(n), 3):
        canon = min(mask(sorted(p[v] for v in c)) for p in auts)
        orb.setdefault(canon, 0)
        orb[canon] += 1
    emit.append(f"## {name} (Z = 4): orbit table of 3-subsets, |Aut| = {len(auts)}, "
                f"{len(orb)} orbits")
    emit.append("")
    emit.append("| orbit representative B | orbit size | disjoint minimal fort |")
    emit.append("|---|---|---|")
    tot = 0
    for canon in sorted(orb):
        wit = next(F for F in minimal if F & canon == 0)
        emit.append(f"| {pset(canon, names)} | {orb[canon]} | {pset(wit, names)} |")
        tot += orb[canon]
    emit.append("")
    nv = 7 if name == "R_end" else 8
    check(tot == len(threes), f"{name}: orbit sizes sum to C({nv},3) = {len(threes)}")
with open(os.path.join(HERE, "fort_tables.md"), "w", encoding="utf-8") as f:
    f.write("\n".join(emit))
print("     orbit tables written to theorem/fort_tables.md")

# ================================================================ F4
print("== F4: local forts inside G_k ==")
for k in range(2, 7):
    n, edges, blocks = chain(k)
    nbr = nbrm(n, edges)
    okc = all(is_fort(n, nbr, mask(bl["a"] + bl["b"])) for bl in blocks)
    okf = all(is_fort(n, nbr, mask([bl["a"][i], bl["a"][j], bl["b"][i], bl["b"][j]]))
              for bl in blocks for i, j in ((0, 1), (0, 2), (1, 2)))
    check(okc and okf,
          f"k={k}: every block core and every F12/F13/F23 is a fort of G_k")
n, edges, blocks = chain(4)
nbr = nbrm(n, edges)
for bi, kind in ((0, "end"), (1, "mid"), (3, "end")):
    bl = blocks[bi]
    reg = sorted(bl["verts"])
    subs = [s for s in (bl["s_in"], bl["s_out"]) if s is not None]
    local = []
    for sub in range(1, 1 << len(reg)):
        F = mask([reg[i] for i in range(len(reg)) if (sub >> i) & 1])
        if is_fort(n, nbr, F):
            local.append(F)
    check(all(F & mask(subs) == 0 for F in local),
          f"G_4 block {bi} ({kind}): no region-contained fort of G_4 uses a "
          f"subdivision vertex ({len(local)} local forts)")
    minloc = [F for F in local if not any(G != F and G & ~F == 0 for G in local)]
    base = min(bl["verts"])
    names = {}
    for i in range(3):
        names[bl["a"][i]] = f"a{i+1}"
        names[bl["b"][i]] = f"b{i+1}"
    for s in subs:
        names[s] = "s?"
    pretty = sorted(pset(F, names) for F in minloc)
    print(f"     block {bi} ({kind}) minimal local forts: {pretty}")
    if kind == "mid":
        check(pretty == sorted(["{a1,a2,b1,b2}", "{a1,a3,b1,b3}", "{a2,a3,b2,b3}"]),
              f"block {bi}: minimal local forts are exactly F12, F13, F23")
    # local transversal number (over ALL local forts)
    tau = None
    for sz in range(1, 5):
        hit = next((c for c in combinations(reg, sz)
                    if all(mask(c) & F for F in minloc)), None)
        if hit:
            tau = sz
            hitset = hit
            break
    expect_tau = 2 if kind == "mid" else 3
    check(tau == expect_tau,
          f"block {bi} ({kind}): local fort transversal number = {tau} "
          f"(expected {expect_tau}; witness {pset(mask(hitset), names)})")

# ================================================================ F5
print("== F5: cut superadditivity lemma, in situ ==")


def chrono(n, nbr, B):
    """Random chronological forcing run; returns (final, list of forces (u,v))."""
    blue, forces = B, []
    while True:
        cand = []
        for v in range(n):
            if (blue >> v) & 1:
                w = nbr[v] & ~blue
                if w and (w & (w - 1)) == 0:
                    cand.append((v, w.bit_length() - 1))
        if not cand:
            return blue, forces
        u, w = random.choice(cand)
        forces.append((u, w))
        blue |= 1 << w


def cutlemma_holds(k, n, nbr, blocks, B, orders=4):
    """Validate: replay restricted to each component R_i of G_k - bridges,
    starting from (B cap R_i) + (bridge-forced vertices in R_i), forces R_i;
    each bridge transmits <= 1 force; per-block accounting reaches 3k+1."""
    bridges = {frozenset((blocks[i]["s_out"], blocks[i + 1]["s_in"]))
               for i in range(k - 1)}
    # standalone region adjacency (bridge edges removed)
    regm = [mask(sorted(bl["verts"])) for bl in blocks]
    radj = []
    for bl in blocks:
        sub = {}
        for v in sorted(bl["verts"]):
            sub[v] = nbr[v] & mask(sorted(bl["verts"]))
        radj.append(sub)
    for _ in range(orders):
        fin, forces = chrono(n, nbr, B)
        assert fin == (1 << n) - 1
        percnt = {}
        for u, v in forces:
            if frozenset((u, v)) in bridges:
                percnt[frozenset((u, v))] = percnt.get(frozenset((u, v)), 0) + 1
        if any(c > 1 for c in percnt.values()):
            return False
        if sum(percnt.values()) > k - 1:
            return False
        X = mask([v for u, v in forces if frozenset((u, v)) in bridges])
        tot = 0
        for i, bl in enumerate(blocks):
            Bi = (B | X) & regm[i]
            # closure within the standalone region graph
            blue = Bi
            while True:
                forced = 0
                for v in sorted(bl["verts"]):
                    if (blue >> v) & 1:
                        w = radj[i][v] & ~blue
                        if w and (w & (w - 1)) == 0:
                            forced |= w
                if not forced:
                    break
                blue |= forced
            if blue != regm[i]:
                return False           # replay claim
            need = 4 - bin(X & regm[i]).count('1')
            if bin(B & regm[i]).count('1') < need:
                return False           # accounting claim |B cap R_i| >= 4 - inj_i
            tot += need
        if bin(B).count('1') < tot:
            return False
    return True


k = 2
n, edges, blocks = chain(k)
nbr = nbrm(n, edges)
full = (1 << n) - 1
f7 = [mask(S) for S in combinations(range(n), 7) if closure(n, nbr, mask(S)) == full]
check(f7 and all(cutlemma_holds(k, n, nbr, blocks, B, 6) for B in f7),
      f"k=2: replay + accounting hold for ALL {len(f7)} forcing 7-sets x 6 orders")
f8 = [mask(S) for S in combinations(range(n), 8) if closure(n, nbr, mask(S)) == full]
check(all(cutlemma_holds(k, n, nbr, blocks, B, 3) for B in f8),
      f"k=2: replay + accounting hold for ALL {len(f8)} forcing 8-sets x 3 orders")
for k in (3, 4):
    n, edges, blocks = chain(k)
    nbr = nbrm(n, edges)
    full = (1 << n) - 1
    samples = []
    Zk = 3 * k + 1
    while len(samples) < 300:
        S = random.sample(range(n), random.randint(Zk, Zk + 5))
        if closure(n, nbr, mask(S)) == full:
            samples.append(mask(S))
    check(all(cutlemma_holds(k, n, nbr, blocks, B, 4) for B in samples),
          f"k={k}: replay + accounting hold for 300 random forcing sets x 4 orders")

# ================================================================ F6
print("== F6: Z upper bound pattern W_k ==")


def W_pattern(blocks):
    W = []
    for i, bl in enumerate(blocks):
        if i == 0:
            W += [bl["a"][0], bl["a"][1], bl["b"][0], bl["b"][1]]
        else:
            W += [bl["a"][0], bl["a"][1], bl["b"][1]]
    return W


for k in list(range(2, 21)) + [30, 40]:
    n, edges, blocks = chain(k)
    nbr = nbrm(n, edges)
    W = W_pattern(blocks)
    check(len(W) == 3 * k + 1 and closure(n, nbr, mask(W)) == (1 << n) - 1,
          f"k={k}: |W_k| = 3k+1 = {len(W)} and W_k forces")
n, edges, blocks = chain(2)
check(sorted(W_pattern(blocks)) == [0, 1, 3, 4, 7, 8, 11],
      "W_2 == certified Z-witness {0,1,3,4,7,8,11}")

# ================================================================ F7
print("== F7: gamma upper bound motif pattern D_k ==")


def D_pattern(k, blocks):
    q, r = divmod(k, 3)
    if r == 2:
        pat = ["E"] + ["PA", "T", "PB"] * q + ["EL"]
    elif r == 0:
        pat = ["E"] + ["PA", "T", "PB"] * (q - 1) + ["PA", "Ep"]
    else:
        pat = ["E"] + ["PA", "T", "PB"] * (q - 1) + ["PA", "W", "EL"]
    assert len(pat) == k
    D = []
    for i, p in enumerate(pat):
        bl = blocks[i]
        if p in ("E", "EL", "PA"):
            D += [bl["a"][0], bl["b"][0]]
        elif p == "PB":
            D += [bl["a"][1], bl["b"][1]]
        elif p == "T":
            D += [bl["s_in"], bl["s_out"], bl["a"][2]]
        elif p in ("W", "Ep"):
            D += [bl["s_in"], bl["a"][1], bl["b"][1]]
    return D, "".join({"E": "E", "EL": "E", "PA": "A", "PB": "B",
                       "T": "T", "W": "W", "Ep": "P"}[p] for p in pat)


for k in list(range(2, 21)) + [30, 40]:
    n, edges, blocks = chain(k)
    nbr = nbrm(n, edges)
    D, pat = D_pattern(k, blocks)
    cov = 0
    for v in D:
        cov |= nbr[v] | (1 << v)
    check(len(D) == (7 * k) // 3 and cov == (1 << n) - 1,
          f"k={k}: |D_k| = floor(7k/3) = {len(D)}, dominates (pattern {pat})")
n, edges, blocks = chain(2)
check(sorted(D_pattern(2, blocks)[0]) == [0, 3, 7, 10],
      "D_2 == certified gamma-witness {0,3,7,10}")

# ================================================================ F8
print("== F8: gamma lower bound block lemmas ==")
for name, build, names, expect in (
        ("R_mid", r_mid, NM, {frozenset((0, 3)), frozenset((1, 4)), frozenset((2, 5))}),
        ("R_end", r_end, NE, {frozenset((0, 3)), frozenset((1, 4)), frozenset((1, 5)),
                              frozenset((2, 4)), frozenset((2, 5))})):
    n, edges = build()
    nbr = nbrm(n, edges)
    core = mask(range(6))
    check(all(bin((nbr[v] | (1 << v)) & core).count('1') <= 4 for v in range(n)),
          f"{name}: every closed neighbourhood covers <= 4 of the 6 core vertices")
    good = {frozenset(c) for c in combinations(range(n), 2)
            if (nbr[c[0]] | (1 << c[0]) | nbr[c[1]] | (1 << c[1])) & core == core}
    check(good == expect,
          f"{name}: core-dominating 2-subsets are exactly "
          f"{sorted(sorted(names[v] for v in s) for s in expect)} (none uses an s)")
    # which subdivision vertices does each pair dominate?
    for s in sorted(good):
        cov = 0
        for v in s:
            cov |= nbr[v] | (1 << v)
        doms = [names[u] for u in range(6, n) if (cov >> u) & 1]
        print(f"     {name} pair {sorted(names[v] for v in s)} dominates subs: {doms}")
for k in range(2, 9):
    n, edges, blocks = chain(k)
    nbr = nbrm(n, edges)
    iso = all(set(bits(nbr[v])) <= bl["verts"]
              for bl in blocks for v in bl["a"] + bl["b"])
    check(iso, f"k={k}: core closed neighbourhoods stay inside the own block")

# ================================================================ F9
print("== F9: independent gamma DP cross-check ==")


def gamma_dp(k):
    n, edges, blocks = chain(k)
    nbr = nbrm(n, edges)
    INF = 10 ** 9
    cur = {"start": 0}
    for i, bl in enumerate(blocks):
        reg = sorted(bl["verts"])
        nxt = {}
        for st, cost in cur.items():
            for sub in range(1 << len(reg)):
                S = [reg[j] for j in range(len(reg)) if (sub >> j) & 1]
                Sm = mask(S)
                cov = 0
                for v in S:
                    cov |= nbr[v] | (1 << v)
                if bl["s_in"] is not None:
                    if st == 0:                       # prev s_out in D
                        cov |= 1 << bl["s_in"]
                    if st == 2 and not (Sm >> bl["s_in"]) & 1:
                        continue                       # prev s_out needs s_in in D
                need = mask(reg)
                if bl["s_out"] is not None:
                    need &= ~(1 << bl["s_out"])
                if cov & need != need:
                    continue
                if bl["s_out"] is None:
                    ns = "done"
                elif (Sm >> bl["s_out"]) & 1:
                    ns = 0
                elif (cov >> bl["s_out"]) & 1:
                    ns = 1
                else:
                    ns = 2
                c = cost + len(S)
                if c < nxt.get(ns, INF):
                    nxt[ns] = c
        cur = nxt
    return cur["done"]


ok = all(gamma_dp(k) == (7 * k) // 3 for k in range(2, 61))
check(ok, "DP: gamma(G_k) == floor(7k/3) for all 2 <= k <= 60")
for k, g in ((2, 4), (3, 7), (4, 9), (5, 11), (6, 14), (7, 16), (8, 18)):
    check(gamma_dp(k) == g, f"DP reproduces certified gamma(G_{k}) = {g}")

# ================================================================ F10
print("== F10: formulas vs certified table ==")
for k, z in ((2, 7), (3, 10), (4, 13), (5, 16)):
    check(3 * k + 1 == z, f"k={k}: 3k+1 == certified Z = {z}")
for k, g in ((2, 4), (3, 7), (4, 9), (5, 11), (6, 14), (7, 16), (8, 18)):
    check((7 * k) // 3 == g, f"k={k}: floor(7k/3) == certified gamma = {g}")
for k in (2, 3, 4, 5):
    gap = 3 * k + 1 - (7 * k) // 3
    check(gap == (2 * k + 3 + 2) // 3, f"k={k}: gap == ceil((2k+3)/3) = {gap}")

print()
if FAIL:
    print(f"*** {len(FAIL)} FAILURES ***")
    for m in FAIL:
        print("   -", m)
    sys.exit(1)
print("ALL CHECKS PASSED")
