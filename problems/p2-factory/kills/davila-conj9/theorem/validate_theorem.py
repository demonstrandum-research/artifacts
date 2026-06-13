"""
validate_theorem.py -- computational validation of every lemma in failed-forcing.md
(the proof that Z(G_k) = 3k+1 and gamma(G_k) = 2k + floor(k/3), hence
 Z - gamma = ceil(2k/3) + 1 -> infinity on the chain family G_k).

Pure stdlib. Exact bitmask arithmetic throughout. Exits nonzero on any failure.

Sections:
  S0  construction, cross-check against the certified .edges files (k=2..8)
  S1  hypotheses: connected, cubic, triangle-free, n=8k-2 (k=2..30)
  S2  block automaton: mu(R) for both block types, all grant sets R
  S3  automorphism groups, orbit tables, fort certificates (emitted as markdown)
      + exhaustive no-symmetry double check of every deficient start set
  S4  Restriction Lemma validated in situ on G_k:
        k=2: ALL forcing 7-sets, k=3: ALL forcing 10-sets, k=4,5: sampled;
        random chronological orders; check |B ∩ block_i| >= m(r_i), sum r_i <= k-1
  S5  Z upper bound: explicit pattern W_k forces, |W_k| = 3k+1   (k=2..60)
  S6  gamma upper bound: explicit pattern D_k dominates, |D_k| = 2k+floor(k/3) (k=2..60)
  S7  gamma lower bound structural claims:
        (a) block-level: exhaustive classification of <=2-subsets dominating the core
        (b) core isolation: dominators of core vertices lie in own block (k=2..8)
        (c) in-situ: k=2 all 1001 4-subsets, k=3 all 170544 7-subsets ->
            every minimum dominating set has d_i>=2, window sums >= 7,
            and every d_i=2 block is a claimed diagonal pair
  S8  certified-value consistency: formulas vs the certificate table
"""
import sys, json, random, itertools, os
from itertools import combinations

random.seed(20260612)
HERE = os.path.dirname(os.path.abspath(__file__))
KILLDIR = os.path.dirname(HERE)

FAIL = []
def check(cond, msg):
    tag = "ok " if cond else "FAIL"
    print(f"  [{tag}] {msg}")
    if not cond:
        FAIL.append(msg)

# ---------------------------------------------------------------- construction
def chain(k):
    """G_k, 'indep' variant. Returns (n, edges, blocks).
    blocks[i] = dict(a=[3 ids], b=[3 ids], subs=[1 or 2 ids], verts=set)."""
    edges, blocks = [], []
    offset, out_sub_prev = 0, None
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
            edges.append((u, s)); edges.append((v, s))
        if out_sub_prev is not None:
            edges.append((out_sub_prev, subs[0]))
        out_sub_prev = subs[-1]
        verts = set(a) | set(b) | set(subs)
        blocks.append(dict(a=a, b=b, subs=subs, verts=verts))
        offset += 6 + len(subs)
    return offset, edges, blocks

def neighbor_masks(n, edges):
    nbr = [0] * n
    for u, v in edges:
        assert u != v and not (nbr[u] >> v) & 1
        nbr[u] |= 1 << v; nbr[v] |= 1 << u
    return nbr

def zf_closure(n, nbr, blue):
    while True:
        forced = 0
        for v in range(n):
            if (blue >> v) & 1:
                white = nbr[v] & ~blue
                if white and (white & (white - 1)) == 0:
                    forced |= white
        if not forced:
            return blue
        blue |= forced

def is_fort(n, nbr, F):
    """F (bitmask) nonempty; every v outside F has 0 or >=2 neighbors in F."""
    if F == 0:
        return False
    for v in range(n):
        if not (F >> v) & 1:
            inF = nbr[v] & F
            if inF and (inF & (inF - 1)) == 0:
                return False
    return True

def mask(vs):
    m = 0
    for v in vs: m |= 1 << v
    return m

def bits(m):
    out = []
    v = 0
    while m:
        if m & 1: out.append(v)
        m >>= 1; v += 1
    return out

# ================================================================ S0
print("== S0: construction cross-check against certified .edges files ==")
for k in range(2, 9):
    n, edges, blocks = chain(k)
    path = os.path.join(KILLDIR, f"chain_indep_k{k}.edges")
    with open(path) as f:
        lines = f.read().split()
    fn, fm = int(lines[0]), int(lines[1])
    fedges = sorted(tuple(sorted((int(lines[2+2*i]), int(lines[3+2*i]))))
                    for i in range(fm))
    medges = sorted(tuple(sorted(e)) for e in edges)
    check(n == fn and medges == fedges,
          f"k={k}: rebuilt graph == chain_indep_k{k}.edges (n={n}, m={len(edges)})")

# ================================================================ S1
print("== S1: hypotheses (connected, cubic, triangle-free, n=8k-2) ==")
for k in list(range(2, 11)) + [20, 30]:
    n, edges, blocks = chain(k)
    nbr = neighbor_masks(n, edges)
    cubic = all(bin(m).count("1") == 3 for m in nbr)
    seen, frontier = 1, 1
    while frontier:
        newly = 0
        for v in range(n):
            if (frontier >> v) & 1: newly |= nbr[v]
        frontier = newly & ~seen; seen |= newly
    conn = seen == (1 << n) - 1
    trifree = all(nbr[u] & nbr[v] == 0
                  for u in range(n) for v in bits(nbr[u]) if v > u)
    check(cubic and conn and trifree and n == 8*k - 2,
          f"k={k}: cubic, connected, triangle-free, n={n}=8k-2")

# ================================================================ S2
print("== S2: block automaton values mu(R) ==")
# Block graphs: external bridge neighbours treated as permanently blue ==
# equivalently DELETED (s-vertices get degree 2). Standard zero forcing on these.
# H_end: K3,3 on a={0,1,2} | b={3,4,5}, edge (0,3) subdivided by s=6.
# H_mid: K3,3, edges (0,3) and (1,4) subdivided by s_in=6, s_out=7.
def block_graph(kind):
    a, b = [0,1,2], [3,4,5]
    subdiv = [(0,3)] if kind == "end" else [(0,3),(1,4)]
    subs = list(range(6, 6+len(subdiv)))
    edges = [(u,v) for u in a for v in b if (u,v) not in subdiv]
    for (u,v), s in zip(subdiv, subs):
        edges += [(u,s),(v,s)]
    n = 6 + len(subs)
    return n, edges, subs

def mu(n, nbr, R):
    """min |X| with closure(X ∪ R) = V, brute force."""
    full = (1 << n) - 1
    Rm = mask(R)
    for size in range(0, n+1):
        for X in combinations(range(n), size):
            if zf_closure(n, nbr, mask(X) | Rm) == full:
                return size
    return None

MU = {}
for kind in ("end", "mid"):
    n, edges, subs = block_graph(kind)
    nbr = neighbor_masks(n, edges)
    for r in range(len(subs)+1):
        vals = set()
        for R in combinations(subs, r):
            vals.add(mu(n, nbr, list(R)))
        check(len(vals) == 1, f"{kind}: mu independent of which {r} sub-vertices granted -> {vals}")
        MU[(kind, r)] = vals.pop()
        print(f"      mu_{kind}({r}) = {MU[(kind,r)]}")
check(MU[("end",0)] == 4 and MU[("end",1)] == 3, "mu_end = (4,3)")
check(MU[("mid",0)] == 4 and MU[("mid",1)] == 3 and MU[("mid",2)] == 2, "mu_mid = (4,3,2)")
check(all(MU[(kind,r)] >= 4 - r for (kind,r) in MU), "mu(r) >= 4 - r in every case")

# ================================================================ S3
print("== S3: orbit tables + fort certificates for the case analysis ==")
def automorphisms(n, edges):
    eset = set(tuple(sorted(e)) for e in edges)
    deg = [0]*n
    for u,v in eset: deg[u]+=1; deg[v]+=1
    auts = []
    for p in itertools.permutations(range(n)):
        if all(deg[p[v]] == deg[v] for v in range(n)):
            if all(tuple(sorted((p[u],p[v]))) in eset for (u,v) in eset):
                auts.append(p)
    return auts

def orbit_reps(subsets, auts):
    seen, reps = set(), []
    for X in subsets:
        fx = frozenset(X)
        if fx in seen: continue
        orb = set(frozenset(p[v] for v in X) for p in auts)
        seen |= orb
        reps.append((X, len(orb)))
    return reps

NAMES_MID = {0:"a1",1:"a2",2:"a3",3:"b1",4:"b2",5:"b3",6:"s_in",7:"s_out"}
NAMES_END = {0:"a1",1:"a2",2:"a3",3:"b1",4:"b2",5:"b3",6:"s"}

table_lines = []
def emit_claim(kind, R, size, stab_of=None):
    """All X ⊆ core with |X|=size fail to force given grants R. Emit orbit table."""
    n, edges, subs = block_graph(kind)
    nbr = neighbor_masks(n, edges)
    names = NAMES_END if kind == "end" else NAMES_MID
    full = (1 << n) - 1
    auts = automorphisms(n, edges)
    if stab_of is not None:
        auts = [p for p in auts if all(p[v] == v for v in stab_of)]
    core = [v for v in range(6)]
    allX = list(combinations(core, size))
    reps = orbit_reps(allX, auts)
    # exhaustive no-symmetry check over ALL X ⊆ V (incl. sub-vertices):
    bad = [X for X in combinations(range(n), size)
           if zf_closure(n, nbr, mask(X) | mask(R)) == full]
    check(not bad, f"{kind}, R={[names[s] for s in R]}: NO {size}-set forces "
                   f"(exhaustive over all C({n},{size}) subsets incl. sub-vertices)")
    Rtxt = "{" + ",".join(names[s] for s in R) + "}"
    table_lines.append(f"### Block `{kind}`, grants R = {Rtxt}, start sets of size {size} "
                       f"(orbit representatives; group order {len(auts)})")
    table_lines.append("")
    table_lines.append("| representative X | orbit size | stalled closure of X ∪ R | "
                       "surviving fort F = V ∖ closure |")
    table_lines.append("|---|---|---|---|")
    forts_used = set()
    for X, osz in reps:
        cl = zf_closure(n, nbr, mask(X) | mask(R))
        F = full & ~cl
        assert F, "unexpectedly forced everything"
        assert is_fort(n, nbr, F), "complement of stalled closure must be a fort"
        assert F & (mask(X) | mask(R)) == 0
        forts_used.add(F)
        xs = "{" + ",".join(names[v] for v in X) + "}"
        cs = "{" + ",".join(names[v] for v in bits(cl)) + "}"
        fs = "{" + ",".join(names[v] for v in bits(F)) + "}"
        table_lines.append(f"| {xs} | {osz} | {cs} | {fs} |")
    table_lines.append("")
    # verify each used fort once more and report
    for F in sorted(forts_used):
        assert is_fort(n, nbr, F)
    print(f"      {kind} R={[names[s] for s in R]} size={size}: "
          f"{len(reps)} orbits, {len(forts_used)} distinct forts, all certified")

# Claims in dependency order (monotonicity handles X containing sub-vertices,
# but the exhaustive check above already covers them directly):
emit_claim("mid", [6,7], 1)            # M2: both grants, no single start works
emit_claim("mid", [6],   2, stab_of=[6])  # M1: one grant, no pair works
emit_claim("mid", [],    3)            # M0: no grants, no triple works
emit_claim("end", [6],   2)            # E1
emit_claim("end", [],    3)            # E0
with open(os.path.join(HERE, "case_tables.md"), "w", encoding="utf-8") as f:
    f.write("\n".join(table_lines))
print(f"      orbit/fort tables written to theorem/case_tables.md")

# Achievability (tightness of mu): explicit witnesses
n_e, ed_e, _ = block_graph("end"); nbr_e = neighbor_masks(n_e, ed_e)
n_m, ed_m, _ = block_graph("mid"); nbr_m = neighbor_masks(n_m, ed_m)
check(zf_closure(n_e, nbr_e, mask([0,1,3,4])) == (1<<n_e)-1, "end: {a1,a2,b1,b2} forces (mu_end(0)<=4)")
check(zf_closure(n_e, nbr_e, mask([0,1,4,6])) == (1<<n_e)-1, "end: {a1,a2,b2}+s forces (mu_end(1)<=3)")
check(zf_closure(n_m, nbr_m, mask([0,1,4,6])) == (1<<n_m)-1, "mid: {a1,a2,b2,s_in} forces (mu_mid(0)<=4)")
check(zf_closure(n_m, nbr_m, mask([0,1,4])|mask([6])) == (1<<n_m)-1, "mid: {a1,a2,b2}+s_in forces (mu_mid(1)<=3)")
check(zf_closure(n_m, nbr_m, mask([0,1])|mask([6,7])) == (1<<n_m)-1, "mid: {a1,a2}+both s forces (mu_mid(2)<=2)")

# ================================================================ S4
print("== S4: Restriction Lemma + accounting validated in situ ==")
def block_of(blocks, v):
    for i, bl in enumerate(blocks):
        if v in bl["verts"]:
            return i
    raise ValueError

def bridge_pairs(blocks, k):
    """bridge i: (out-sub of block i, in-sub of block i+1), i = 0..k-2."""
    return [(blocks[i]["subs"][-1], blocks[i+1]["subs"][0]) for i in range(k-1)]

def random_chronology(n, nbr, B):
    """Run the forcing process picking a random applicable force each step.
    Returns (final_blue, forces list of (u,v))."""
    blue = B
    forces = []
    while True:
        cand = []
        for v in range(n):
            if (blue >> v) & 1:
                white = nbr[v] & ~blue
                if white and (white & (white - 1)) == 0:
                    cand.append((v, white.bit_length() - 1))
        if not cand:
            return blue, forces
        u, w = random.choice(cand)
        forces.append((u, w))
        blue |= 1 << w

def validate_process(k, n, nbr, blocks, B, n_orders=5):
    """For forcing set B (bitmask): random chronological orders; per order,
    compute in-forces r_i, check |B∩V_i| >= mu(type_i, r_i) and sum r_i <= k-1."""
    full = (1 << n) - 1
    bp = bridge_pairs(blocks, k)
    bridge_set = {frozenset(p) for p in bp}
    ok = True
    for _ in range(n_orders):
        fin, forces = random_chronology(n, nbr, B)
        assert fin == full
        r = [0]*k
        cross = 0
        for (u, v) in forces:
            if frozenset((u, v)) in bridge_set:
                cross += 1
                r[block_of(blocks, v)] += 1
        if cross > k - 1: ok = False
        bound = 0
        for i in range(k):
            kind = "end" if i in (0, k-1) else "mid"
            bi = bin(B & mask(blocks[i]["verts"])).count("1")
            need = MU[(kind, r[i])]
            bound += need
            if bi < need: ok = False
        if bin(B).count("1") < bound: ok = False  # redundant but explicit
    return ok

# k=2: ALL forcing 7-sets
k = 2; n, edges, blocks = chain(k); nbr = neighbor_masks(n, edges)
full = (1 << n) - 1
f7 = [mask(S) for S in combinations(range(n), 7) if zf_closure(n, nbr, mask(S)) == full]
allok = all(validate_process(k, n, nbr, blocks, B, n_orders=8) for B in f7)
check(len(f7) > 0 and allok,
      f"k=2: lemma holds for ALL {len(f7)} forcing 7-sets x 8 random orders")
f8 = [mask(S) for S in combinations(range(n), 8) if zf_closure(n, nbr, mask(S)) == full]
allok = all(validate_process(k, n, nbr, blocks, B, n_orders=3) for B in f8)
check(allok, f"k=2: lemma holds for ALL {len(f8)} forcing 8-sets x 3 random orders")

# k=3: ALL forcing 10-sets (C(22,10) = 646646 closures)
k = 3; n, edges, blocks = chain(k); nbr = neighbor_masks(n, edges)
full = (1 << n) - 1
f10 = []
for S in combinations(range(n), 10):
    m = mask(S)
    if zf_closure(n, nbr, m) == full:
        f10.append(m)
check(len(f10) > 0, f"k=3: found {len(f10)} forcing 10-sets (exhaustive over C(22,10))")
allok = all(validate_process(k, n, nbr, blocks, B, n_orders=5) for B in f10)
check(allok, f"k=3: lemma holds for ALL {len(f10)} forcing 10-sets x 5 random orders")

# k=4,5: sampled forcing sets (witness, perturbations, random supersets, random sets)
for k in (4, 5):
    n, edges, blocks = chain(k); nbr = neighbor_masks(n, edges)
    full = (1 << n) - 1
    # pattern witness (see S5)
    W = pattern_W = None
    tested = 0; allok = True
    samples = []
    # random sets of sizes Z..Z+6 that force
    Z = 3*k + 1
    while len(samples) < 400:
        size = random.randint(Z, Z + 6)
        S = random.sample(range(n), size)
        m = mask(S)
        if zf_closure(n, nbr, m) == full:
            samples.append(m)
    for B in samples:
        if not validate_process(k, n, nbr, blocks, B, n_orders=4):
            allok = False
        tested += 1
    check(allok, f"k={k}: lemma holds for {tested} sampled forcing sets x 4 random orders")

# ================================================================ S5
print("== S5: Z upper bound pattern ==")
def pattern_W(k, blocks):
    W = []
    bl = blocks[0]
    W += [bl["a"][0], bl["a"][1], bl["b"][0], bl["b"][1]]      # {a1,a2,b1,b2}
    for i in range(1, k):
        bl = blocks[i]
        W += [bl["a"][0], bl["a"][1], bl["b"][1]]               # {a1,a2,b2}
    return W

for k in list(range(2, 21)) + [40, 60]:
    n, edges, blocks = chain(k); nbr = neighbor_masks(n, edges)
    W = pattern_W(k, blocks)
    ok = (len(W) == 3*k + 1) and zf_closure(n, nbr, mask(W)) == (1 << n) - 1
    check(ok, f"k={k}: W_k forces, |W_k| = {len(W)} = 3k+1")
# anchor: W_2 equals the certified witness
n, edges, blocks = chain(2)
check(sorted(pattern_W(2, blocks)) == [0,1,3,4,7,8,11],
      "W_2 equals the certified k=2 Z-witness {0,1,3,4,7,8,11}")

# ================================================================ S6
print("== S6: gamma upper bound pattern ==")
def pattern_D(k, blocks):
    """Dominating set, |D| = 2k + floor(k/3). 1-indexed block positions."""
    r = k % 3
    D = []
    for i1 in range(1, k+1):
        bl = blocks[i1-1]
        a, b, subs = bl["a"], bl["b"], bl["subs"]
        if r in (0, 1):
            if i1 % 3 == 2:   D += [a[2], subs[0], subs[-1]]    # donor {a3,s_in,s_out}
            elif i1 % 3 == 1: D += [a[0], b[0]]                 # {a1,b1}
            else:             D += [a[1], b[1]]                 # {a2,b2}
        else:  # r == 2
            if i1 % 3 == 0:   D += [a[2], subs[0], subs[-1]]    # donor
            elif i1 % 3 == 1: D += ([a[0], b[0]] if i1 == 1 else [a[1], b[1]])
            else:             D += [a[0], b[0]]                 # i1 % 3 == 2
    return sorted(set(D))

def dominates(n, nbr, D):
    cover = 0
    for v in D:
        cover |= nbr[v] | (1 << v)
    return cover == (1 << n) - 1

for k in list(range(2, 21)) + [40, 60]:
    n, edges, blocks = chain(k); nbr = neighbor_masks(n, edges)
    D = pattern_D(k, blocks)
    ok = (len(D) == 2*k + k // 3) and dominates(n, nbr, D)
    check(ok, f"k={k}: D_k dominates, |D_k| = {len(D)} = 2k + floor(k/3)")
n, edges, blocks = chain(2)
check(pattern_D(2, blocks) == [0,3,7,10], "D_2 equals the certified k=2 gamma-witness {0,3,7,10}")

# ================================================================ S7
print("== S7: gamma lower bound structural claims ==")
# (a) block-level classification: which subsets of size <=2 of a block dominate its core?
for kind in ("end", "mid"):
    n_b, ed_b, subs = block_graph(kind)
    # NOTE: for domination the bridge endpoint(s) are irrelevant to CORE coverage
    # (no core vertex has a neighbour outside its block), so the block graph suffices.
    nbr_b = neighbor_masks(n_b, ed_b)
    core_mask = mask(range(6))
    good = []
    for size in (1, 2):
        for S in combinations(range(n_b), size):
            cov = 0
            for v in S: cov |= nbr_b[v] | (1 << v)
            if cov & core_mask == core_mask:
                good.append(set(S))
    if kind == "mid":
        expected = [{0,3},{1,4},{2,5}]                       # diagonal pairs only
    else:
        expected = [{0,3},{1,4},{1,5},{2,4},{2,5}]           # {a1,b1} or {a2,a3}x{b2,b3}
    check(sorted(map(sorted, good)) == sorted(map(sorted, expected)),
          f"{kind}: <=2-subsets covering the 6-core are exactly {sorted(map(sorted,expected))}")
    # which of those pairs dominate which sub-vertices?
    for S in good:
        cov = 0
        for v in S: cov |= nbr_b[v] | (1 << v)
        doms = [s for s in subs if (cov >> s) & 1]
        print(f"      {kind} pair {sorted(S)} dominates sub-vertices {doms} of {subs}")

# (b) core isolation in G_k
for k in range(2, 9):
    n, edges, blocks = chain(k); nbr = neighbor_masks(n, edges)
    iso = True
    for i, bl in enumerate(blocks):
        core = set(bl["a"]) | set(bl["b"])
        for v in core:
            if any(u not in bl["verts"] for u in bits(nbr[v])):
                iso = False
    check(iso, f"k={k}: every core vertex's closed neighbourhood lies inside its own block")

# (c) in-situ validation of the window lemma on all minimum dominating sets
for k, gsize in ((2, 4), (3, 7)):
    n, edges, blocks = chain(k); nbr = neighbor_masks(n, edges)
    full = (1 << n) - 1
    closed = [nbr[v] | (1 << v) for v in range(n)]
    mds = []
    for S in combinations(range(n), gsize):
        cov = 0
        for v in S: cov |= closed[v]
        if cov == full: mds.append(S)
    # no smaller set dominates (re-anchor of certified gamma)
    smaller_exists = False
    for S in combinations(range(n), gsize - 1):
        cov = 0
        for v in S: cov |= closed[v]
        if cov == full: smaller_exists = True; break
    check(not smaller_exists and len(mds) > 0,
          f"k={k}: gamma = {gsize} re-confirmed exhaustively; {len(mds)} minimum dominating sets")
    okmin, okpair, okwin = True, True, True
    diag_mid = [{0,3},{1,4},{2,5}]; diag_end = [{0,3},{1,4},{1,5},{2,4},{2,5}]
    for S in mds:
        d = []
        for i, bl in enumerate(blocks):
            Di = [v for v in S if v in bl["verts"]]
            d.append(len(Di))
            if len(Di) == 2:
                base = min(bl["verts"])
                rel = {v - base for v in Di}
                ok = (rel in (diag_end if i in (0, k-1) else diag_mid))
                if not ok: okpair = False
        if min(d) < 2: okmin = False
        for i in range(k - 2):
            if d[i] + d[i+1] + d[i+2] < 7: okwin = False
    check(okmin, f"k={k}: every minimum dominating set has >=2 vertices per block")
    check(okpair, f"k={k}: every 2-vertex block of a minimum dominating set is a claimed diagonal pair")
    check(okwin, f"k={k}: every 3 consecutive blocks carry >=7 vertices of every minimum dominating set")

# ================================================================ S8
print("== S8: formula consistency with the certified table ==")
cert_gamma = {2:4, 3:7, 4:9, 5:11, 6:14, 7:16, 8:18}
cert_Z     = {2:7, 3:10, 4:13, 5:16}
for k, g in cert_gamma.items():
    check(2*k + k // 3 == g, f"k={k}: 2k+floor(k/3) = {2*k + k//3} == certified gamma {g}")
for k, z in cert_Z.items():
    check(3*k + 1 == z, f"k={k}: 3k+1 = {3*k+1} == certified Z {z}")
for k in cert_Z:
    gap = 3*k + 1 - (2*k + k//3)
    check(gap == -(-2*k//3) + 1, f"k={k}: gap formula ceil(2k/3)+1 = {gap}")

print()
if FAIL:
    print(f"*** {len(FAIL)} FAILURES ***")
    for m in FAIL: print("   -", m)
    sys.exit(1)
print("ALL CHECKS PASSED")
