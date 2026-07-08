"""C5-P2 canonical verify pass -- RESUME-capable runner (2026-07-08).

Companion to verify_canonical_c5.py. IDENTICAL semantics for the frozen
298-cell release set:
  - same pinned manifest + sha256 (45f0eedc...), same N_FROZEN=298;
  - same per-cell verify_cert.py --both invocation (identical verification);
  - same hard-abort conditions (hash drift, wrong entry count, any frozen
    cell missing/non-OK on disk) -> exit 3, nothing launched;
  - same hard wall-clock CAP_S self-kill; on TIMEOUT NO report is written and
    the gate stays closed, honestly.

ADDED here (does NOT touch the original):
  --resume-from-logs : collect the cells already marked "ok" in
      verify_canonical_c5.log AND any verify_canonical_c5.resume-*.log,
      assert that set is a SUBSET of the frozen 298, SKIP exactly those, and
      run verify_cert only on the remainder. This run's transcript goes to
      verify_canonical_c5.resume-<timestamp>.log (identical per-cell format,
      because it is the same verify_cert stdout streamed through).
  --dry-run : do the resume-set collection only, print
      "would skip N=?, would run M=?, first 3 to run: ...", and exit WITHOUT
      launching verify. Prints skip/run against the live logs.
  --shard K/N : PARALLEL sharding (e.g. --shard 1/4). After the remaining
      (non-skipped) cell list is computed in frozen-manifest order, process
      only the cells at index i where i % N == K-1. This run's log =
      verify_canonical_c5.resume-shard{K}of{N}-<timestamp>.log (still matches
      the resume-*.log glob, so sibling shards re-collect each other's ok
      lines); heartbeat = verify_canonical_c5.resume.HEARTBEAT-shard{K}of{N}.
      A shard writes the final 298-cell verify_report.json ONLY when, at its
      own completion, the ok-set re-collected across ALL logs (incl. every
      other shard's) covers all 298 -- i.e. only the last shard to finish
      assembles; the write is atomic (temp file + os.replace) so a
      near-simultaneous finish can't leave a torn report. Launch N shards
      detached via launch_g1_resume_shards.ps1. Sharding needs
      --resume-from-logs too (or --dry-run).

FINAL REPORT (only when the remaining cells ALL pass): assemble
lab/data/verify_report.json covering ALL 298 cells (n_cells=298, n_failed=0)
with "resumed": true and a "runs" list naming each contributing log file +
its ok-count + the manifest sha256 -- so the gate harvester sees one
complete, honest record. Skipped-cell entries are reconstructed from their
original "ok" log lines (themselves genuine verify_cert output); the
remaining cells get fresh genuine verify_cert per-cell reports.

Launch detached via launch_g1_resume.ps1 (mirrors launch_g1_relaunch_*.ps1).
USE ONLY AFTER the live run (verify_canonical_c5.py) TIMEOUTs -- see
lenses/C6P2-release-gate/G1-RESUME-PLAN.md.
"""
import glob as _glob
import hashlib
import json
import os
import re
import subprocess
import sys
import threading
import time


def norm(cid):
    """Canonical cell id: strip zero-padding on the _nNNN suffix.

    The frozen manifest keys are zero-padded (g4_n031) and are what the cell
    files on disk are named / what must be passed to verify_cert.py. But
    verify_cert PRINTS the record's own unpadded id (rep['cell'] =
    f'{variant}{k}_n{n}' -> g4_n31). Both collapse to the same canonical id
    here so the skip/subset comparison is exact across the two spellings."""
    return re.sub(r"_n0*(\d+)$", r"_n\1", cid)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
SRC = os.path.join(ROOT, "lab", "src")
CELLS = os.path.join(ROOT, "lab", "data", "cells")
REPORT = os.path.join(ROOT, "lab", "data", "verify_report.json")
LOG = os.path.join(HERE, "verify_canonical_c5.log")              # original run
RESUME_GLOB = os.path.join(HERE, "verify_canonical_c5.resume-*.log")
MANIFEST = os.path.join(ROOT, "lenses", "P5-hygiene", "sat_archive",
                        "manifest.json")
MANIFEST_SHA256 = ("45f0eedccfa5e22636108f633cde6c1c"
                   "28f139d06446d92be6a09858bfc1400e")
N_FROZEN = 298
CAP_S = 43200  # fresh 12 h hard wall-clock self-kill for the resumed run

# this run's own transcript + heartbeat (timestamped; never clobbers the live)
STAMP = time.strftime("%Y%m%dT%H%M%S")
RESUME_LOG = os.path.join(HERE, f"verify_canonical_c5.resume-{STAMP}.log")
HB = os.path.join(HERE, "verify_canonical_c5.resume.HEARTBEAT")


def beat(msg):
    with open(HB, "w", encoding="ascii", errors="replace") as f:
        f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {msg}\n")


def _atomic_write_json(path, obj):
    """Write obj as JSON to a per-pid temp file, then os.replace onto path.

    os.replace is atomic on the same volume, so two shards that finish at
    (nearly) the same instant and both observe full coverage can each write a
    complete report without ever leaving a half-written verify_report.json --
    the last replace wins and both candidates are valid full 298-cell records."""
    tmp = f"{path}.tmp.{os.getpid()}"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=1, sort_keys=True)
    os.replace(tmp, path)


def abort(reason, logpath=None):
    # Writes to the RESUME log only -- never clobbers verify_canonical_c5.log.
    # logpath resolves at call time so a shard aborts to its own (reassigned)
    # RESUME_LOG rather than a default bound at def time.
    if logpath is None:
        logpath = RESUME_LOG
    with open(logpath, "w", encoding="utf-8") as f:
        f.write(f"ABORT (nothing launched): {reason}\n")
    beat(f"ABORT {reason[:120]}")
    sys.exit(3)


def load_frozen():
    """Return (sorted_ids, sha256). Aborts on hash drift / wrong count."""
    raw = open(MANIFEST, "rb").read()
    digest = hashlib.sha256(raw).hexdigest()
    if digest != MANIFEST_SHA256:
        abort(f"manifest sha256 {digest} != pinned {MANIFEST_SHA256}")
    ids = sorted(json.loads(raw.decode("utf-8"))["entries"].keys())
    if len(ids) != N_FROZEN:
        abort(f"manifest has {len(ids)} entries, expected {N_FROZEN}")
    return ids, digest


def preflight_cells(ids):
    """Same on-disk OK* guard as the original runner."""
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


def collect_ok(logpaths):
    """Scan the given logs for 'ok   <cell>  <unsat_check>' lines.

    Returns dict norm(cid) -> (cid, unsat_check, source_log_basename) and an
    ordered list of (basename, n_ok) contributions. Keyed by the canonical
    (unpadded) id via norm(). Later logs override earlier for a repeated cell
    (should not happen, but safe)."""
    ok = {}
    contrib = []
    for lp in logpaths:
        if not os.path.exists(lp):
            continue
        n = 0
        with open(lp, encoding="utf-8", errors="replace") as f:
            for line in f:
                if not line.startswith("ok"):
                    continue
                parts = line.rstrip("\n").split(None, 2)
                # parts == ["ok", cid, unsat_check?]
                if len(parts) < 2 or parts[0] != "ok":
                    continue
                cid = parts[1]
                uchk = parts[2] if len(parts) > 2 else ""
                ok[norm(cid)] = (cid, uchk, os.path.basename(lp))
                n += 1
        contrib.append((os.path.basename(lp), n))
    return ok, contrib


def resume_logs():
    """Ordered list: original log first, then resume-*.log sorted by name."""
    return [LOG] + sorted(_glob.glob(RESUME_GLOB))


def compute_resume_sets():
    """Return (frozen_ids, sha, ok_map, contrib, skip_ids, run_ids).

    Aborts if the ok-set is not a subset of the frozen 298."""
    frozen, sha = load_frozen()          # padded manifest keys (g4_n031)
    fnorm = {norm(k) for k in frozen}    # canonical (unpadded) frozen ids
    ok_map, contrib = collect_ok(resume_logs())   # keyed by canonical id
    stray = sorted(set(ok_map) - fnorm)
    if stray:
        abort(f"resume ok-set not a subset of frozen 298: stray={stray}")
    skip_ids = sorted(k for k in frozen if norm(k) in ok_map)
    run_ids = [k for k in frozen if norm(k) not in ok_map]   # padded keys
    return frozen, sha, ok_map, contrib, skip_ids, run_ids


def assemble_full_report(frozen, sha, ok_map, contrib, run_ids):
    """Merge reconstructed skipped-cell entries with the fresh subset report
    verify_cert just wrote, into ONE honest 298-cell verify_report.json."""
    # fresh per-cell reports for the cells we just ran (genuine verify_cert).
    # verify_cert keys by its own unpadded id -> normalize both sides.
    sub = json.load(open(REPORT, encoding="utf-8"))
    sub_reports = {norm(r["cell"]): r for r in sub.get("reports", [])}
    missing_run = [c for c in run_ids if norm(c) not in sub_reports]
    if missing_run:
        # subset report incomplete -> do NOT fabricate; leave gate closed.
        raise RuntimeError(f"subset report missing cells: {missing_run}")
    reports = []
    for key in frozen:                 # padded manifest keys
        nid = norm(key)
        if nid in sub_reports:
            reports.append(sub_reports[nid])
        else:  # skipped: reconstruct from its original ok log line
            cid, uchk, src = ok_map[nid]
            reports.append({"cell": cid, "ok": True, "problems": [],
                            "unsat_check": uchk, "from_log": src})
    n_failed = sum(1 for r in reports if not r.get("ok"))
    runs = [{"log": b, "n_ok_cells": n} for (b, n) in contrib]
    runs.append({"log": os.path.basename(RESUME_LOG),
                 "n_run_cells": len(run_ids)})
    out = {"n_cells": len(reports), "n_failed": n_failed,
           "resumed": True, "manifest_sha256": sha, "runs": runs,
           "reports": reports}
    _atomic_write_json(REPORT, out)
    return len(reports), n_failed


def shard_slice(run_ids, K, N):
    """Deterministic index-mod shard of the remaining (non-skipped) cell list.

    run_ids is already in frozen-manifest order -- compute_resume_sets builds it
    by iterating the sorted frozen keys -- so it is the identical list for every
    shard co-launched against the same baseline logs. Shard K keeps the cells at
    positions i with i % N == K-1.

    INTERLEAVE NOTE: the expensive g4 giants (4-6 h/cell) cluster contiguously at
    the tail of the frozen order (the g4 ladder). Stride-N (index-mod) sharding
    therefore deals those giants round-robin across the shards -- shard 1 takes
    g4 giant #0, shard 2 #1, ... -- rather than dumping the whole g4 block onto a
    single shard the way a contiguous block-split would. Giants end up evenly
    distributed, so no one shard becomes the long pole."""
    return [c for i, c in enumerate(run_ids) if i % N == (K - 1)]


def assemble_full_report_from_logs(frozen, sha, ok_map, contrib):
    """Sharded assembly: reconstruct ALL 298 cell entries from their genuine
    verify_cert 'ok' log lines (each cell's ok line lives in the cold log or in
    some shard's resume log). Used only when a shard has observed full coverage
    across every log. Same per-cell record shape as the skipped-cell path in the
    non-shard assembler -- every entry carries "from_log". Atomic write."""
    reports = []
    for key in frozen:                 # padded manifest keys, frozen order
        nid = norm(key)
        if nid not in ok_map:
            raise RuntimeError(f"coverage gap at assembly: {key}")
        cid, uchk, src = ok_map[nid]
        reports.append({"cell": cid, "ok": True, "problems": [],
                        "unsat_check": uchk, "from_log": src})
    n_failed = sum(1 for r in reports if not r.get("ok"))
    runs = [{"log": b, "n_ok_cells": n} for (b, n) in contrib]
    out = {"n_cells": len(reports), "n_failed": n_failed,
           "resumed": True, "sharded": True, "manifest_sha256": sha,
           "runs": runs, "reports": reports}
    _atomic_write_json(REPORT, out)
    return len(reports), n_failed


def parse_shard(args):
    """Parse --shard K/N -> (K, N), or (None, None) if absent. Aborts if
    malformed or out of range."""
    if "--shard" not in args:
        return None, None
    i = args.index("--shard")
    if i + 1 >= len(args):
        abort("--shard requires a K/N value (e.g. --shard 1/4)")
    val = args[i + 1].strip()
    m = re.fullmatch(r"(\d+)/(\d+)", val)
    if not m:
        abort(f"--shard value must be K/N, got {val!r}")
    K, N = int(m.group(1)), int(m.group(2))
    if N < 1 or K < 1 or K > N:
        abort(f"--shard out of range: {K}/{N} (need 1 <= K <= N)")
    return K, N


def finalize_shard(f, frozen, sha, t0, my_run_ids, K, N):
    """After this shard's own verify_cert passed: re-collect ok across ALL logs
    (incl. sibling shards' resume-*.log) and, ONLY if that now covers all 298,
    write the single atomic full report. Otherwise this is not the last shard --
    write nothing and let the last one assemble."""
    ok2, contrib2 = collect_ok(resume_logs())
    covered = sum(1 for k in frozen if norm(k) in ok2)
    if covered < len(frozen):
        f.write(f"\nshard {K}/{N} slice done ({len(my_run_ids)} cells ok); "
                f"coverage {covered}/{len(frozen)} across all logs -- not the "
                f"last shard, report NOT written (another shard assembles)\n")
        beat(f"SHARD-DONE {K}/{N} coverage {covered}/{len(frozen)} waiting")
        return None
    n, nf = assemble_full_report_from_logs(frozen, sha, ok2, contrib2)
    f.write(f"\nshard {K}/{N} observed FULL coverage {covered}/{len(frozen)}; "
            f"assembled verify_report.json n_cells={n} n_failed={nf} "
            f"resumed=true sharded=true across {len(contrib2)} logs "
            f"(atomic os.replace)\n")
    beat(f"DONE-ASSEMBLE {K}/{N} n_cells={n} n_failed={nf} "
         f"el={int(time.time() - t0)}s")
    return (n, nf)


def main():
    args = sys.argv[1:]
    dry = "--dry-run" in args
    resume = "--resume-from-logs" in args or dry
    if not resume:
        abort("resume runner requires --resume-from-logs (or --dry-run); "
              "use verify_canonical_c5.py for a cold pass")

    K, N = parse_shard(args)
    sharded = K is not None
    if sharded:
        # redirect this shard's transcript + heartbeat to shard-scoped paths
        # BEFORE any further work (the shard log still matches RESUME_GLOB, so
        # sibling shards re-collect its ok lines). Resolved by abort/beat at
        # call time.
        global RESUME_LOG, HB
        RESUME_LOG = os.path.join(
            HERE, f"verify_canonical_c5.resume-shard{K}of{N}-{STAMP}.log")
        HB = os.path.join(
            HERE, f"verify_canonical_c5.resume.HEARTBEAT-shard{K}of{N}")

    frozen, sha, ok_map, contrib, skip_ids, run_ids = compute_resume_sets()
    my_run_ids = shard_slice(run_ids, K, N) if sharded else run_ids

    if dry:
        if sharded:
            print(f"shard {K}/{N}: skip N={len(skip_ids)}, remaining "
                  f"M={len(run_ids)}, this shard S={len(my_run_ids)}, "
                  f"first 3: {my_run_ids[:3]}")
            # full id list so a test harness can check sum + disjointness.
            print(f"shard {K}/{N} ids: {my_run_ids}")
        else:
            print(f"would skip N={len(skip_ids)}, would run M={len(run_ids)}, "
                  f"first 3 to run: {run_ids[:3]}")
        print(f"contrib logs: {contrib}")
        print(f"manifest sha256={sha} (frozen={len(frozen)})")
        return 0

    # real run: full integrity guard (same as the original), then verify
    preflight_cells(frozen)

    if not my_run_ids:
        # nothing for this run to do.
        if sharded:
            # empty slice: still check whether all shards together now cover
            # all 298, and if so assemble (this shard may be the last).
            ok2, contrib2 = collect_ok(resume_logs())
            covered = sum(1 for k in frozen if norm(k) in ok2)
            if covered >= len(frozen):
                n, nf = assemble_full_report_from_logs(frozen, sha, ok2,
                                                       contrib2)
                beat(f"DONE-ASSEMBLE {K}/{N} empty-slice full n_cells={n} "
                     f"n_failed={nf}")
            else:
                beat(f"SHARD-EMPTY {K}/{N} coverage {covered}/{len(frozen)}")
            return 0
        # non-shard: everything already ok in logs -> just assemble the report.
        assemble_full_report(frozen, sha, ok_map, contrib, run_ids)
        beat("DONE (nothing to run; report assembled from logs)")
        return 0

    tag = f" shard {K}/{N}" if sharded else ""
    with open(RESUME_LOG, "w", encoding="utf-8") as f:
        f.write("C5-P2 canonical verify pass -- RESUME" + tag +
                " (2026-07-08, frozen-manifest cell list)\n")
        f.write(f"start={time.strftime('%Y-%m-%d %H:%M:%S')} cap={CAP_S}s "
                f"pid={os.getpid()}\n")
        f.write(f"resume: skip={len(skip_ids)} (from {contrib}); "
                f"remaining={len(run_ids)} of {len(frozen)} frozen; "
                f"this run={len(my_run_ids)}"
                + (f" (shard {K}/{N}, stride-{N})" if sharded else "") +
                f" sha256={sha} (no glob)\n")
        f.flush()
        p = subprocess.Popen(
            [sys.executable, "-u", os.path.join(SRC, "verify_cert.py"),
             "--both"] + my_run_ids,
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
        beat(f"LAUNCH{tag} 0/{len(my_run_ids)} verify_cert pid={p.pid} "
             f"(skip={len(skip_ids)})")
        for line in p.stdout:
            f.write(line)
            f.flush()
            if line.startswith("ok") or line.startswith("FAIL"):
                done += 1
                beat(f"{done}/{len(my_run_ids)}{tag} "
                     f"el={int(time.time() - t0)}s "
                     f"last={line.strip()[:90]}")
        rc = p.wait()
        timer.cancel()
        if timed_out.is_set():
            f.write(f"\nTIMEOUT after {CAP_S}s - canonical report NOT "
                    "written; gate stays closed\n")
            beat(f"TIMEOUT{tag} after {CAP_S}s at {done}/{len(my_run_ids)}")
            f.write(f"end={time.strftime('%Y-%m-%d %H:%M:%S')}\n")
            sys.exit(99)
        f.write(f"\nverify_cert (this run {len(my_run_ids)}) EXIT={rc}\n")
        if rc != 0:
            f.write("cells in this run did not all pass - full report NOT "
                    "assembled; gate stays closed\n")
            beat(f"DONE-FAIL{tag} rc={rc} {done}/{len(my_run_ids)}")
            f.write(f"end={time.strftime('%Y-%m-%d %H:%M:%S')}\n")
            sys.exit(rc)
        # this run's cells all passed. Non-shard: assemble the honest full 298
        # report. Shard: assemble ONLY if this shard now observes full coverage
        # across ALL logs (else another shard is the last one).
        try:
            if sharded:
                finalize_shard(f, frozen, sha, t0, my_run_ids, K, N)
            else:
                n, nf = assemble_full_report(frozen, sha, ok_map, contrib,
                                             run_ids)
                f.write(f"assembled verify_report.json n_cells={n} "
                        f"n_failed={nf} resumed=true across "
                        f"{len(contrib) + 1} logs\n")
                beat(f"DONE rc=0 assembled n_cells={n} n_failed={nf} "
                     f"el={int(time.time() - t0)}s")
        except Exception as e:
            f.write(f"\nASSEMBLY FAILED: {e}; report NOT written\n")
            beat(f"ASSEMBLY FAILED {str(e)[:100]}")
            f.write(f"end={time.strftime('%Y-%m-%d %H:%M:%S')}\n")
            sys.exit(4)
        f.write(f"end={time.strftime('%Y-%m-%d %H:%M:%S')}\n")
    sys.exit(0)


if __name__ == "__main__":
    main()
