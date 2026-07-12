#!/usr/bin/env python3
"""Bank completed disjoint n=9 shards into the authoritative census.json."""
import json
from collections import Counter
from pathlib import Path

lane=Path(__file__).resolve().parent.parent
chosen=[]
unfinished_base=[]
for r in range(32):
    d=lane/f"census_shards/s{r}"
    if (d/"stdout.log").exists() and (d/"stdout.log").stat().st_size:
        chosen.append(next(d.glob("*_maj.jsonl")))
    else: unfinished_base.append(r)
unfinished_sub=[]
for r in unfinished_base:
    for j in range(4):
        a=r+32*j; d=lane/f"census_subshards/t{a}"
        if (d/"stdout.log").exists() and (d/"stdout.log").stat().st_size:
            chosen.append(next(d.glob("*_maj.jsonl")))
        else: unfinished_sub.append(a)
for a in unfinished_sub:
    for j in range(4):
        b=a+128*j; d=lane/f"census_micro/u{b}"
        if (d/"stdout.log").exists() and (d/"stdout.log").stat().st_size:
            chosen.append(next(d.glob("*_maj.jsonl")))

seen=set(); dist=Counter()
for p in chosen:
    for line in p.open(encoding="utf-8"):
        r=json.loads(line); assert r["n"]==9 and r["graph6"] not in seen
        seen.add(r["graph6"]); dist[r["maj"]]+=1
data=json.loads((lane/"census.json").read_text())
data["partial_n9"]={
    "status":"PARTIAL: disjoint completed canonical geng residue shards only",
    "covered_admissible_connected_graphs":len(seen),
    "full_admissible_connected_total":256838,
    "distribution":{str(k):dist[k] for k in range(1,7)},
    "value5_occurs_in_partial":dist[5]>0,
    "maximum_maj_in_partial":max(dist) if dist else None,
    "files":[str(p.relative_to(lane)) for p in chosen],
    "warning":"Not an exhaustive or statistically representative n=9 census."
}
(lane/"census.json").write_text(json.dumps(data,indent=2)+"\n")
print(json.dumps(data["partial_n9"],indent=2))
