#!/usr/bin/env python3
"""Symmetry analysis of the certificate pools.

- pool_34.jsonl   (central-symmetric run, 4126 sets, size>=34)
- pool_total33.jsonl (same run, total-33 sets: sym core + extensions)
- baseline ILS found_sets_*.jsonl (asymmetric search residue)

Questions: stabilizer orders (does anything exceed C2?), canonical dedup,
shell-usage statistics across the pool, overlap/cluster structure vs the
36-set, symmetric-core sizes of asymmetric/odd sets.
"""
import json, os, sys, glob
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import symlib as sl
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
BASE = os.path.normpath(os.path.join(HERE, "..", ".."))
MR = os.path.join(BASE, "runs", "central-symmetric", "main-run")

out = {}

# ---------------- pool_34
pool = sl.load_jsonl_sets(os.path.join(MR, "pool_34.jsonl"))
sizes = Counter(len(s) for s in pool)
print(f"pool_34: {len(pool)} sets, size histogram {sorted(sizes.items())}")

# stabilizers (cheap: 48 ops x 4126 sets)
stab_hist = Counter()
nonC2 = []
for S in pool:
    st = sl.stabilizer(S)
    stab_hist[len(st)] += 1
    if len(st) > 2:
        nonC2.append(S)
print("stabilizer order histogram:", dict(stab_hist), "| sets with |stab|>2:", len(nonC2))
out["pool34_stab_hist"] = dict(stab_hist)

# centrally symmetric? (should all contain -I)
n_sym = sum(1 for S in pool if len(sl.sym_core(S)) == len(S))
print(f"fully centrally symmetric: {n_sym}/{len(pool)}")

# canonical dedup under B3
canon = {}
for S in pool:
    canon.setdefault(sl.canonical_form(S), 0)
    canon[sl.canonical_form(S)] += 1
print(f"B3-inequivalent classes: {len(canon)} (from {len(pool)} sets)")
out["pool34_classes_B3"] = len(canon)

# shell usage across pool (4r2 about (6,6,6); these are odd-n sets so r2 integral = /4)
shell_freq = Counter()
shell_profiles = Counter()
for S in pool:
    sh = sorted(set(s // 4 for s in sl.shells(S)))
    shell_profiles[tuple(sh)] += 1
    for v in sh:
        shell_freq[v] += 1
print(f"distinct shell profiles: {len(shell_profiles)}")
avail = sorted({a*a + b*b + c*c for a in range(7) for b in range(7) for c in range(7)})
freq_sorted = sorted(shell_freq.items(), key=lambda kv: -kv[1])
print("shell usage freq (r2: count/4126), top 20:", freq_sorted[:20])
never = [v for v in avail if shell_freq[v] == 0]
print(f"shells NEVER used in any pool 34-set: {never}")
always = [v for v in avail if shell_freq[v] == len(pool)]
print(f"shells used in EVERY pool 34-set: {always}")
out["pool34_shell_freq"] = {str(k): v for k, v in sorted(shell_freq.items())}
out["pool34_shells_never"] = never
out["pool34_shells_always"] = always

# 36-set shell profile for contrast
S36 = sl.load_json_set(os.path.join(BASE, "certificates", "record36_centralsym.json"))
sh36 = sorted(set(s // 4 for s in sl.shells(S36)))
print("36-set shells:", sh36)

# overlap with 36 (as pair sets): max |S ^ S36| over pool, histogram
S36f = frozenset(S36)
ov_hist = Counter()
best_ov, best_set = -1, None
for S in pool:
    ov = len(frozenset(S) & S36f)
    ov_hist[ov] += 1
    if ov > best_ov:
        best_ov, best_set = ov, S
print("overlap-with-36 histogram (points):", sorted(ov_hist.items()))
out["pool34_overlap36_hist"] = {str(k): v for k, v in sorted(ov_hist.items())}

# pairwise overlap structure within pool (sample): cluster or spread?
rng = np.random.default_rng(1)
idxs = rng.choice(len(pool), size=min(300, len(pool)), replace=False)
ovs = []
for i in range(len(idxs)):
    for j in range(i + 1, len(idxs)):
        ovs.append(len(frozenset(pool[idxs[i]]) & frozenset(pool[idxs[j]])))
ovs = np.array(ovs)
print(f"pool pairwise overlap (300-sample): mean {ovs.mean():.2f}, median {np.median(ovs)}, "
      f"max {ovs.max()}, min {ovs.min()}")
out["pool34_pairwise_overlap"] = {"mean": float(ovs.mean()), "median": float(np.median(ovs)),
                                  "max": int(ovs.max()), "min": int(ovs.min())}

# ---------------- pool_total33 (sym-core + extension structure)
pool33 = sl.load_jsonl_sets(os.path.join(MR, "pool_total33.jsonl"))
print(f"\npool_total33: {len(pool33)} sets, sizes {sorted(Counter(len(s) for s in pool33).items())}")
core_hist = Counter()
for S in pool33:
    core_hist[len(sl.sym_core(S))] += 1
print("sym-core-size histogram of total33 sets:", sorted(core_hist.items()))
out["pool33_core_hist"] = {str(k): v for k, v in sorted(core_hist.items())}

# ---------------- baseline ILS sets
bl_files = glob.glob(os.path.join(BASE, "runs", "baseline-ils", "main", "found_sets_*.jsonl"))
bl = []
for f in bl_files:
    bl += sl.load_jsonl_sets(f, key="points")
szs = Counter(len(s) for s in bl)
print(f"\nbaseline ILS: {len(bl)} sets, sizes {sorted(szs.items())}")
# symmetric-core (best inversion center) for the largest baseline sets
big = [S for S in bl if len(S) >= 34]
for S in big[:10]:
    inv = sl.inversion_scores(S)
    bc = max(inv.items(), key=lambda kv: kv[1])
    print(f"  size {len(S)}: best inversion core {bc[1]} @ 2c'={bc[0]}")
core_sizes = []
for S in bl:
    if len(S) >= 33:
        inv = sl.inversion_scores(S)
        core_sizes.append(max(inv.values()))
if core_sizes:
    print(f"baseline >=33 sets: best-inversion-core mean {np.mean(core_sizes):.2f} "
          f"max {max(core_sizes)} (set size ~33-35)")
    out["baseline_core_sizes"] = {"mean": float(np.mean(core_sizes)), "max": int(max(core_sizes)),
                                  "n": len(core_sizes)}

with open(os.path.join(HERE, "pools_analysis.json"), "w") as f:
    json.dump(out, f, indent=1)
print("\nwritten pools_analysis.json")
