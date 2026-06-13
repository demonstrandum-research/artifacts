#!/usr/bin/env python3
"""Exploration 2: print the actual valid label perms per shape, n=3,4,5."""
import sys, os
from itertools import permutations
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enumerator import dyck_shapes, word_from_shape_perm, is_avoider_fast

def main():
    for n in [3, 4]:
        print(f"########## n={n}")
        for shape in dyck_shapes(n):
            sstr = "".join("U" if st else "D" for st in shape)
            good = []
            for p in permutations(range(1, n + 1)):
                w = word_from_shape_perm(shape, p)
                if is_avoider_fast(w):
                    good.append(p)
            print(f"  {sstr}: {len(good)} perms")
            for p in good:
                w = word_from_shape_perm(shape, p)
                print(f"      p={''.join(map(str,p))}  w={''.join(map(str,w))}")

if __name__ == "__main__":
    main()
