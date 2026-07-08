"""C5-P2: mechanical release-gate check (SUBMIT.md G1-G3). Run any time;
prints one line per gate + final verdict. Read-only."""
import json
import os
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
ok_all = True


def gate(name, cond, detail):
    global ok_all
    ok_all &= bool(cond)
    print(f"{name}: {'GREEN' if cond else 'CLOSED'} — {detail}")


# G1: canonical verify report — fresh, complete, 0 failures
rp = os.path.join(ROOT, "lab", "data", "verify_report.json")
try:
    r = json.load(open(rp, encoding="utf-8"))
    age_h = (time.time() - os.path.getmtime(rp)) / 3600
    g1 = (r.get("n_failed") == 0 and r.get("n_cells", 0) >= 298
          and age_h < 7 * 24)
    gate("G1 canonical", g1,
         f"n_cells={r.get('n_cells')} n_failed={r.get('n_failed')} "
         f"age={age_h:.1f}h (need >=298 cells, 0 failed, fresh)")
except Exception as e:
    gate("G1 canonical", False, f"unreadable: {e}")

# G2: archive manifest — claimed nontrivial cells VERIFIED, summary honest
mp = os.path.join(ROOT, "lenses", "P5-hygiene", "sat_archive",
                  "manifest.json")
try:
    m = json.load(open(mp, encoding="utf-8"))
    ent = m["entries"]
    need = ["h4_n062", "h4_n063", "h4_n064", "g5_n023"]
    bad = [c for c in need
           if ent.get(c, {}).get("result") != "VERIFIED"]
    nfail = sum(1 for e in ent.values()
                if str(e.get("result", "")).startswith(("FAIL", "ERROR")))
    summ = m.get("summary", {})
    summ_total = sum(summ.values())
    gate("G2 archive", not bad and nfail == 0,
         f"new-cells not VERIFIED: {bad or 'none'}; FAIL/ERROR entries: "
         f"{nfail}; summary={summ} (total {summ_total} vs "
         f"{len(ent)} entries)")
except Exception as e:
    gate("G2 archive", False, f"unreadable: {e}")

# G3: belt dual-engine report on the late cells
bp = os.path.join(HERE, "verify_new_cells_c5_report.json")
try:
    b = json.load(open(bp, encoding="utf-8"))
    gate("G3 belt", b.get("n_failed") == 0 and b.get("n_cells") == 4,
         f"n_cells={b.get('n_cells')} n_failed={b.get('n_failed')}")
except Exception as e:
    gate("G3 belt", False, f"missing/unreadable: {e}")

print()
print("RELEASE GATE:", "OPEN (G1-G3 mechanical checks green; complete G4-G7"
      " + same-day kill-check per SUBMIT.md before any public step)"
      if ok_all else "CLOSED")
