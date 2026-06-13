"""Emit edge files (n m / u v lines) for the chain graphs, for rust_check."""
import sys
from chain_study import chain, neighbor_masks, check_hypotheses

for variant in ("indep", "shared"):
    for k in range(2, 6):
        n, edges = chain(k, variant)
        nbr = neighbor_masks(n, edges)
        check_hypotheses(n, nbr)
        path = f"chain_{variant}_k{k}.edges"
        with open(path, "w", newline="\n") as f:
            f.write(f"{n} {len(edges)}\n")
            for u, v in edges:
                f.write(f"{u} {v}\n")
        print(path, n, len(edges))
