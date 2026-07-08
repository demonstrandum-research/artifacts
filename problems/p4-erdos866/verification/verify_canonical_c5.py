"""C5-P2: canonical verify_report regeneration, detached, gate-first.

Differences from C4P4's verify_full_lab_orchestrator.py (which this supersedes;
that process was killed by C5-P2 at launch of this one, see STATUS):
  - NO ladder wait: every claimable cell (h4 through n=64, g5 through n=23) is
    already on disk with status OK*. The in-flight g5(24) sweep cell is
    unclaimed C6 harvest and must not gate the release.
  - HARD WALL-CLOCK CAP: 4.5 h on the verify subprocess (C4 evidence: full pass
    needs ~70-90 min; cap is generous). On timeout the canonical report is NOT
    written (verify_cert writes only at successful completion) and the log says
    TIMEOUT - the gate then stays closed, honestly.
  - Heartbeat: verify_cert -u streams one line per cell into this log; a
    HEARTBEAT file is rewritten per cell with progress.
  - G1 RELAUNCH 2026-07-08: cell list comes from the EXPLICIT frozen 298-cell
    release manifest (C6P4 reconciliation pin, sha256 45f0eedc...), NOT from a
    glob of lab/data/cells. Cells that landed after the freeze (g5_n024,
    g5_n025, h4_n065..068, ...) must NOT enter this pass (Codex C5 finding 5 /
    C6P4 handoff). Aborts without launching if the manifest hash drifts or any
    frozen cell is missing/non-OK on disk. CAP_S raised 16200 -> 43200 per
    SUBMIT.md section 0a (prior pass TIMEOUTed at 4.5 h).

Run detached:
  powershell Start-Process python -ArgumentList '-u <this file>' -WindowStyle Hidden
Transcript: lenses/C5P2-publication-gate/verify_canonical_c5.log
"""
import hashlib
import json
import os
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
SRC = os.path.join(ROOT, "lab", "src")
CELLS = os.path.join(ROOT, "lab", "data", "cells")
LOG = os.path.join(HERE, "verify_canonical_c5.log")
HB = os.path.join(HERE, "verify_canonical_c5.HEARTBEAT")
MANIFEST = os.path.join(ROOT, "lenses", "P5-hygiene", "sat_archive",
                        "manifest.json")
MANIFEST_SHA256 = ("45f0eedccfa5e22636108f633cde6c1c"
                   "28f139d06446d92be6a09858bfc1400e")
N_FROZEN = 298
CAP_S = 43200  # 12 h hard wall-clock self-kill (SUBMIT.md 0a; was 16200)


def beat(msg):
    with open(HB, "w", encoding="ascii", errors="replace") as f:
        f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {msg}\n")


def abort(reason):
    with open(LOG, "w", encoding="utf-8") as f:
        f.write(f"ABORT (nothing launched): {reason}\n")
    beat(f"ABORT {reason[:120]}")
    sys.exit(3)


def main():
    # FROZEN release set: explicit list from the pinned manifest. NO GLOB.
    raw = open(MANIFEST, "rb").read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != MANIFEST_SHA256:
        abort(f"manifest sha256 {digest} != pinned {MANIFEST_SHA256}")
    ids = sorted(json.loads(raw.decode("utf-8"))["entries"].keys())
    if len(ids) != N_FROZEN:
        abort(f"manifest has {len(ids)} entries, expected {N_FROZEN}")
    bad = []
    for cid in ids:
        p = os.path.join(CELLS, cid + ".json")
        try:
            st = str(json.load(open(p, encoding="utf-8")).get("status", ""))
        except Exception:
            st = "UNREADABLE"
        if not st.startswith("OK"):
            bad.append((cid, st))
    if bad:
        abort(f"frozen cells missing/non-OK on disk: {bad}")

    with open(LOG, "w", encoding="utf-8") as f:
        f.write("C5-P2 canonical verify pass "
                "(G1 RELAUNCH 2026-07-08, frozen-manifest cell list)\n")
        f.write(f"start={time.strftime('%Y-%m-%d %H:%M:%S')} cap={CAP_S}s "
                f"pid={os.getpid()}\n")
        f.write(f"cell list: {len(ids)} cells from FROZEN manifest "
                f"sha256={digest} (no glob)\n")
        f.flush()
        p = subprocess.Popen(
            [sys.executable, "-u", os.path.join(SRC, "verify_cert.py"),
             "--both"] + ids,
            cwd=SRC, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", errors="replace")
        timed_out = threading.Event()

        def kill():
            timed_out.set()
            p.kill()

        timer = threading.Timer(CAP_S, kill)
        timer.start()
        t0 = time.time()
        done = 0
        beat(f"LAUNCH 0/{len(ids)} verify_cert pid={p.pid}")
        for line in p.stdout:
            f.write(line)
            f.flush()
            if line.startswith("ok") or line.startswith("FAIL"):
                done += 1
                beat(f"{done}/{len(ids)} el={int(time.time() - t0)}s "
                     f"last={line.strip()[:90]}")
        rc = p.wait()
        timer.cancel()
        if timed_out.is_set():
            f.write(f"\nTIMEOUT after {CAP_S}s - canonical report NOT "
                    "written; gate stays closed\n")
            beat(f"TIMEOUT after {CAP_S}s at {done}/{len(ids)}")
            rc = 99
        else:
            f.write(f"\nverify_cert EXIT={rc}\n")
            beat(f"DONE rc={rc} {done}/{len(ids)} "
                 f"el={int(time.time() - t0)}s")
        f.write(f"end={time.strftime('%Y-%m-%d %H:%M:%S')}\n")
    sys.exit(rc)


if __name__ == "__main__":
    main()
