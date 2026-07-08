"""C5-P2: dual-engine belt verification of the late C4-ladder cells
(h4_n062 h4_n063 h4_n064 g5_n023). Lens-local report; does NOT touch the
canonical lab/data/verify_report.json. Hard cap via per-cell timing in log."""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.normpath(os.path.join(HERE, "..", "..", "lab", "src"))
sys.path.insert(0, SRC)

from util import set_idle_priority, read_json  # noqa: E402
from verify_cert import verify_cell  # noqa: E402

set_idle_priority()
cells_dir = os.path.normpath(os.path.join(HERE, "..", "..", "lab", "data", "cells"))
ids = sys.argv[1:] or ["h4_n062", "h4_n063", "h4_n064", "g5_n023"]
reports, bad = [], 0
for cid in ids:
    t0 = time.time()
    rec = read_json(os.path.join(cells_dir, cid + ".json"))
    rep = verify_cell(rec, both_engines=True)
    reports.append(rep)
    if not rep["ok"]:
        bad += 1
        print(f"FAIL {rep['cell']}: {rep['problems']} t={time.time()-t0:.1f}s",
              flush=True)
    else:
        print(f"ok   {rep['cell']}  {rep.get('unsat_check','')} "
              f"t={time.time()-t0:.1f}s", flush=True)
out = os.path.join(HERE, "verify_new_cells_c5_report.json")
with open(out, "w", encoding="utf-8") as f:
    json.dump({"n_cells": len(reports), "n_failed": bad, "reports": reports},
              f, indent=1)
print(f"{len(reports)} cells verified, {bad} failures -> {out}", flush=True)
sys.exit(1 if bad else 0)
