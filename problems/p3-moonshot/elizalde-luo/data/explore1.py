#!/usr/bin/env python3
"""Exploration 1: per-shape structure of valid label permutations."""
import sys, os
from itertools import permutations
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enumerator import (dyck_shapes, word_from_shape_perm, second_positions,
                        contains_1132_fast, contains_3312_fast, is_avoider_fast)

def avoiders_by_shape(n):
    """dict shape(str) -> list of perms p (tuples) such that word avoids."""
    out = defaultdict(list)
    for shape in dyck_shapes(n):
        sstr = "".join("U" if st else "D" for st in shape)
        for p in permutations(range(1, n + 1)):
            w = word_from_shape_perm(shape, p)
            if is_avoider_fast(w):
                out[sstr].append(p)
    return out

def shape_str_props(s):
    """Various stats of a Dyck word string."""
    # heights
    h = 0
    heights = []
    for ch in s:
        h += 1 if ch == 'U' else -1
        heights.append(h)
    peaks = s.count("UD")
    valleys = s.count("DU")
    returns = sum(1 for i, hh in enumerate(heights) if hh == 0)
    maxh = max(heights)
    return dict(peaks=peaks, valleys=valleys, returns=returns, maxh=maxh)

def main():
    for n in range(2, 7):
        ab = avoiders_by_shape(n)
        print(f"=== n={n}: shapes with avoiders: {len(ab)}, total {sum(len(v) for v in ab.values())}")
        # all Dyck shapes
        allshapes = ["".join("U" if st else "D" for st in sh) for sh in dyck_shapes(n)]
        zero = [s for s in allshapes if s not in ab]
        print(f"  zero-count shapes ({len(zero)}):")
        for s in zero:
            print(f"    {s}  {shape_str_props(s)}")
        print(f"  nonzero shapes:")
        for s in sorted(ab, key=lambda x: (-len(ab[x]), x)):
            cnt = len(ab[s])
            import math
            lg = math.log2(cnt)
            print(f"    {s}  count={cnt} (2^{lg:.1f})  {shape_str_props(s)}")

if __name__ == "__main__":
    main()
