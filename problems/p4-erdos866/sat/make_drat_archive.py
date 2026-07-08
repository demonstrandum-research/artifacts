"""P5(c): emit + archive DRAT/LRAT proof certificates for every exact SAT cell.

For each completed cell record (lab/data/cells/*.json) the *upper half* of the
certificate is the claim: no configuration-free A subseteq {1..2n} with
|A| >= M+1 exists.  Soundness chain archived here:

  1. CNF generation (this script, trusted-but-small + cross-checked):
       var i (1 <= i <= N=2n)  <=>  "i in A".
       For every recorded clause tuple b (re-validated against the definition:
       k distinct integers, variant positivity, all C(k,2) pairwise sums in
       [1,N]) add the clause  OR_{s in sumset(b)} (NOT x_s).  These clauses are
       *necessary conditions* for configuration-freeness, so UNSAT of
       (clauses + |A| >= M+1) proves the upper half regardless of whether the
       clause set is complete.
       Cardinality |A| >= M+1: pysat CardEnc.atleast, sequential counter.
       (The same instance is independently re-proved UNSAT by verify_cert.py
       with z3's *native* AtLeast and by the search engine's totalizer —
       three distinct cardinality encodings agreeing pins the semantics.)
  2. Solver: reference CaDiCaL binary (arminbiere/cadical, built from source
     in WSL Ubuntu) solves the DIMACS file and emits a DRAT proof.  NOTE: this
     is a *different solver build* from the pysat Cadical153 that ran the
     search, and the z3 reproof in verify_cert.py is a third engine.
  3. drat-trim (Heule; WSL Ubuntu, gcc -std=gnu11) verifies the DRAT proof
     against the DIMACS file and emits an LRAT proof ("s VERIFIED").
  4. lrat-check (drat-trim repo) checks the LRAT file ("VERIFIED").
  5. cake_lpr (CakeML *formally verified* LRAT checker; cake_lpr.S sha256
     2f3af32d... matches the repo-pinned hash) checks the LRAT file
     ("s VERIFIED UNSAT").  This is the FRAMEWORK final-verification standard.

Artifacts per cell, under sat_archive/cells/<cell>/:
  <cell>.cnf       DIMACS (kept uncompressed; header comments carry metadata)
  <cell>.drat.gz   solver proof (gzipped after checking)
  <cell>.lrat.gz   trimmed LRAT proof (gzipped after checking)
  check.log        full checker transcripts
manifest.json records sha256 of every artifact (computed pre-compression for
the proofs) + checker verdicts.  Cells with M = N are trivial (upper bound is
the whole window) and are recorded as such with no proof files.

RESIDUAL TRUST (state this wherever "certified" is claimed): the DRAT/LRAT
chain certifies UNSAT *of the generated CNF*.  The bridge from the CNF to the
mathematical statement rests on step 1 above (tuple validation, sumset(),
CardEnc semantics) — small, documented, and cross-checked by the independent
engines/encodings of verify_cert.py, but not itself formally verified.

Run:  python make_drat_archive.py [--cells g5_n015 g5_n016 ...]
"""
import argparse
import glob
import gzip
import hashlib
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LAB_SRC = os.path.normpath(os.path.join(HERE, "..", "..", "..", "lab", "src"))
sys.path.insert(0, LAB_SRC)

from util import set_idle_priority, read_json, write_json, data_dir  # noqa: E402
from witness import sumset  # noqa: E402
from verify_cert import validate_tuple  # noqa: E402

WSL_TOOLS = "~/sat-tools"


def to_wsl(path):
    p = os.path.abspath(path).replace("\\", "/")
    return "/mnt/" + p[0].lower() + p[2:]


def wsl_run(cmd, timeout=3600):
    """Run a command line in WSL Ubuntu at lowest niceness."""
    full = ["wsl", "-d", "Ubuntu", "--", "bash", "-lc", "nice -n 19 " + cmd]
    r = subprocess.run(full, capture_output=True, text=True, timeout=timeout)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def gzip_and_remove(path):
    with open(path, "rb") as fin, gzip.open(path + ".gz", "wb", 6) as fout:
        while True:
            chunk = fin.read(1 << 20)
            if not chunk:
                break
            fout.write(chunk)
    os.remove(path)


def build_cnf(rec):
    """Return (clauses, nvars). Raises on any invalid tuple."""
    from pysat.card import CardEnc, EncType
    from pysat.formula import IDPool
    n, k, variant, M = rec["n"], rec["k"], rec["variant"], rec["M"]
    N = 2 * n
    clauses = []
    for idx, bt in enumerate(rec["clause_tuples"]):
        if not validate_tuple(bt, n, k, variant):
            raise ValueError(f"invalid clause tuple {idx}: {bt}")
        clauses.append([-s for s in sorted(sumset(bt))])
    pool = IDPool(start_from=N + 1)
    card = CardEnc.atleast(lits=list(range(1, N + 1)), bound=M + 1,
                           vpool=pool, encoding=EncType.seqcounter)
    clauses += card.clauses
    nvars = max(N, pool.top)
    return clauses, nvars


def archive_cell(cell_file, out_root):
    rec = read_json(cell_file)
    cell = f"{rec['variant']}{rec['k']}_n{rec['n']:03d}"
    n, M = rec["n"], rec["M"]
    N = 2 * n
    entry = {"cell": cell, "variant": rec["variant"], "k": rec["k"],
             "n": n, "N": N, "M": M, "value": rec["value"],
             "status": rec["status"], "n_clause_tuples": len(rec["clause_tuples"])}
    if rec["status"] not in ("OK", "OK_ENUM_TIME_CAP", "OK_ENUM_UNKNOWN"):
        entry["result"] = "SKIP_INCOMPLETE"
        return entry
    if M >= N:
        entry["result"] = "TRIVIAL_M_EQ_N"
        return entry

    t0 = time.time()
    cdir = os.path.join(out_root, "cells", cell)
    os.makedirs(cdir, exist_ok=True)
    cnf_path = os.path.join(cdir, cell + ".cnf")
    drat_path = os.path.join(cdir, cell + ".drat")
    lrat_path = os.path.join(cdir, cell + ".lrat")
    log_path = os.path.join(cdir, "check.log")

    clauses, nvars = build_cnf(rec)
    with open(cnf_path, "w", encoding="ascii", newline="\n") as f:
        f.write(f"c cell {cell}: no config-free A in [1,{N}] with |A| >= {M + 1}\n")
        f.write(f"c variant={rec['variant']} k={rec['k']} n={n} M={M} "
                f"config_clauses={len(rec['clause_tuples'])} "
                f"card=seqcounter(atleast {M + 1} of vars 1..{N})\n")
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(map(str, cl)) + " 0\n")

    wcnf, wdrat = to_wsl(cnf_path), to_wsl(drat_path)
    wlrat = to_wsl(lrat_path)
    # Attempt 1: default cadical. Attempt 2 (fallback, recorded in the entry):
    # cadical --plain (inprocessing off => CDCL-only proof). Rationale: modern
    # CaDiCaL inprocessing can emit DRAT deletion patterns that drat-trim's
    # backward RAT check rejects (first seen: h4_n062, C5 harvest sweep);
    # --plain proofs avoid the issue. Soundness is unchanged: whichever proof
    # is archived must still pass the FULL drat-trim -> lrat-check -> cake_lpr
    # chain; the fallback only changes how the proof is produced.
    ok = False
    logs = []  # accumulated across attempts: a failed default-proof
    # transcript is preserved in check.log alongside the fallback's
    for opts in ("", "--plain "):
        rc0, out0 = wsl_run(
            f"{WSL_TOOLS}/cadical/build/cadical {opts}-q --no-binary {wcnf} {wdrat}")
        if rc0 != 20 or "s UNSATISFIABLE" not in out0:
            entry["result"] = f"FAIL_SOLVE rc={rc0}"
            return entry
        entry["solve_s"] = round(time.time() - t0, 2)
        entry["cnf_sha256"] = sha256_file(cnf_path)
        entry["drat_sha256"] = sha256_file(drat_path)
        if opts:
            entry["solver_opts"] = (opts.strip() + " (fallback: default-proof "
                                    "DRAT rejected by drat-trim)")
        logs.append(f"== cadical {opts}==\n" + out0)
        rc1, out1 = wsl_run(
            f"{WSL_TOOLS}/drat-trim/drat-trim {wcnf} {wdrat} -L {wlrat}")
        logs.append("== drat-trim ==\n" + out1)
        entry["drat_trim_verified"] = ("s VERIFIED" in out1)
        if entry["drat_trim_verified"]:
            entry["lrat_sha256"] = sha256_file(lrat_path)
            rc2, out2 = wsl_run(f"{WSL_TOOLS}/drat-trim/lrat-check {wcnf} {wlrat}")
            logs.append("== lrat-check ==\n" + out2)
            entry["lrat_check_verified"] = ("VERIFIED" in out2)
            rc3, out3 = wsl_run(f"{WSL_TOOLS}/cake_lpr/cake_lpr {wcnf} {wlrat}")
            logs.append("== cake_lpr (formally verified) ==\n" + out3)
            entry["cake_lpr_verified"] = ("s VERIFIED UNSAT" in out3)
        with open(log_path, "w", encoding="utf-8", newline="\n") as f:
            f.write("\n".join(logs))
        ok = bool(entry.get("drat_trim_verified")
                  and entry.get("lrat_check_verified")
                  and entry.get("cake_lpr_verified"))
        if ok:
            break
    entry["result"] = "VERIFIED" if ok else "FAIL_CHECK"
    if ok:
        gzip_and_remove(drat_path)
        gzip_and_remove(lrat_path)
    entry["total_s"] = round(time.time() - t0, 2)
    return entry


def main():
    set_idle_priority()
    ap = argparse.ArgumentParser()
    ap.add_argument("--cells", nargs="*", default=None,
                    help="cell ids (e.g. g5_n015); default: all")
    a = ap.parse_args()
    cells_dir = os.path.join(data_dir(), "cells")
    files = sorted(glob.glob(os.path.join(cells_dir, "*.json")))
    if a.cells:
        want = set(a.cells)
        files = [f for f in files
                 if os.path.splitext(os.path.basename(f))[0] in want]
    # order by clause count ascending (cheap cells first)
    files.sort(key=lambda f: len(read_json(f)["clause_tuples"]))
    manifest_path = os.path.join(HERE, "manifest.json")
    manifest = read_json(manifest_path) if os.path.exists(manifest_path) else {
        "description": "DRAT/LRAT archive for Erdos #866 exact SAT cells",
        "toolchain": {
            "solver": "CaDiCaL 3.0.0 reference binary (arminbiere/cadical, "
                      "WSL Ubuntu build); independent of the pysat "
                      "Cadical153 search engine and the z3 reproof engine",
            "drat_trim": "github.com/marijnheule/drat-trim (WSL Ubuntu, gcc 15.2 -std=gnu11)",
            "lrat_check": "lrat-check.c from the drat-trim repo",
            "cake_lpr": "github.com/tanyongkiam/cake_lpr, cake_lpr.S sha256 "
                        "2f3af32d55083839b3fa0e693afd817679c0b8944bef41def05a8b0ec72b7d4a "
                        "(matches repo-pinned cake_lpr.sha256); formally verified LRAT checker",
        },
        "entries": {}}
    done = manifest["entries"]
    todo = [f for f in files
            if done.get(os.path.splitext(os.path.basename(f))[0].replace(
                "_n", "_n"), {}).get("result") not in ("VERIFIED", "TRIVIAL_M_EQ_N")]
    print(f"{len(todo)} cells to archive (of {len(files)} requested)")
    nfail = 0
    for i, f in enumerate(todo):
        cid = os.path.splitext(os.path.basename(f))[0]
        try:
            entry = archive_cell(f, HERE)
        except Exception as e:  # noqa: BLE001
            entry = {"cell": cid, "result": f"ERROR: {e}"}
        done[cid] = entry
        flag = "ok  " if entry["result"] in ("VERIFIED", "TRIVIAL_M_EQ_N") else "FAIL"
        if flag == "FAIL":
            nfail += 1
        print(f"[{i + 1}/{len(todo)}] {flag} {cid}: {entry['result']} "
              f"t={entry.get('total_s', 0)}s", flush=True)
        write_json(manifest_path, manifest)
    summary = {}
    for e in done.values():
        summary[e["result"]] = summary.get(e["result"], 0) + 1
    manifest["summary"] = summary
    write_json(manifest_path, manifest)
    print("summary:", summary)
    sys.exit(1 if nfail else 0)


if __name__ == "__main__":
    main()
