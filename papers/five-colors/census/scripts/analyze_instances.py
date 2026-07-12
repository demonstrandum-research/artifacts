#!/usr/bin/env python3
"""Count distinct edge-colour assignments (first edge fixed to colour 0)."""
import argparse, json
import networkx as nx
from pysat.solvers import Cadical195
from search import make_cnf, verify_coloring, graph_record

def count(g, q, limit):
    cnf, x = make_cnf(g, q); total=0
    with Cadical195(bootstrap_with=cnf.clauses) as s:
        while total < limit and s.solve():
            model=set(v for v in s.get_model() if v>0)
            colors=[next(a for a,v in enumerate(vs) if v in model) for vs in x]
            assert verify_coloring(g,colors,q)
            total += 1
            s.add_clause([-x[e][colors[e]] for e in range(len(x))])
        complete = total < limit
    return {"count":total, "complete":complete, "limit":limit,
            "normalization":"first lexicographic edge has color 0"}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("graph6",nargs="+")
    ap.add_argument("--limit",type=int,default=100000);ap.add_argument("--output",required=True)
    a=ap.parse_args(); out=[]
    for code in a.graph6:
        g=nx.from_graph6_bytes(code.encode())
        out.append(graph_record(g, solutions4=count(g,4,a.limit),
                                solutions5=count(g,5,a.limit)))
    open(a.output,"w").write(json.dumps(out,indent=2)+"\n")
if __name__=="__main__":main()
