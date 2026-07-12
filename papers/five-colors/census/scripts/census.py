#!/usr/bin/env python3
"""Recompute graph6 census and concise summaries used by scout.md."""
import json
from pathlib import Path
from search import read_g6, admissible

root=Path(__file__).parent
rows=[]
for n in range(1,10):
    gs=list(read_g6(root/f"connected_n{n}.g6")); adm=[g for g in gs if admissible(g)]
    rows.append({"n":n,"connected_unlabeled":len(gs),"admissible":len(adm),
                 "admissible_edge_min":min(g.number_of_edges() for g in adm),
                 "admissible_edge_max":max(g.number_of_edges() for g in adm)})
t=json.loads((root/"targeted.json").read_text())
tr=[r for r in t["records"] if r.get("admissible")]
summary={"connected_census":rows,
 "connected_totals":{"graphs":sum(r["connected_unlabeled"] for r in rows),
                     "admissible":sum(r["admissible"] for r in rows)},
 "targeted":{"records":len(t["records"]),"admissible":len(tr),
             "n_min":min(r["n"] for r in tr),"n_max":max(r["n"] for r in tr),
             "m_min":min(r["m"] for r in tr),"m_max":max(r["m"] for r in tr),
             "unsat5":sum(not r["sat5"] for r in tr),
             "unsat4":sum(not r["sat4"] for r in tr),
             "hardest5":max(tr,key=lambda r:r["stats5"].get("conflicts",0)),
             "hardest4":max(tr,key=lambda r:r["stats4"].get("conflicts",0))}}
(root/"census.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary["connected_census"],indent=2))
