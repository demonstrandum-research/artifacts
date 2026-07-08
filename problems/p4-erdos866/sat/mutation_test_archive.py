"""Negative controls for the DRAT/LRAT archive: corrupted artifacts must be
rejected by the checkers. Mutations (on copies in a temp dir; archive
untouched):
  M1: DRAT with the final empty-clause derivation steps removed -> drat-trim
      must NOT verify.
  M2: CNF with one config clause deleted (weaker formula; the archived LRAT
      references original clause ids) -> cake_lpr must reject the LRAT.
  M3: LRAT with one literal flipped in a lemma -> lrat-check and cake_lpr
      must reject.
Run on a small verified cell (default g4_n005).
"""
import gzip
import os
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def to_wsl(p):
    p = os.path.abspath(p).replace("\\", "/")
    return "/mnt/" + p[0].lower() + p[2:]


def wsl(cmd):
    r = subprocess.run(["wsl", "-d", "Ubuntu", "--", "bash", "-lc", cmd],
                       capture_output=True, text=True, timeout=600)
    return (r.stdout or "") + (r.stderr or "")


def main(cell="g4_n005"):
    src = os.path.join(HERE, "cells", cell)
    tmp = os.path.join(HERE, "mutation_tmp")
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)
    cnf = os.path.join(tmp, "m.cnf")
    drat = os.path.join(tmp, "m.drat")
    lrat = os.path.join(tmp, "m.lrat")
    shutil.copy(os.path.join(src, cell + ".cnf"), cnf)
    with gzip.open(os.path.join(src, cell + ".drat.gz"), "rt") as f:
        drat_lines = f.read().splitlines()
    with gzip.open(os.path.join(src, cell + ".lrat.gz"), "rt") as f:
        lrat_lines = f.read().splitlines()
    results = {}

    # M1: truncate the proof before the empty clause
    with open(drat, "w", newline="\n") as f:
        f.write("\n".join(drat_lines[: max(1, len(drat_lines) // 2)]) + "\n")
    out = wsl(f"~/sat-tools/drat-trim/drat-trim {to_wsl(cnf)} {to_wsl(drat)}")
    results["M1_truncated_drat_rejected"] = "s VERIFIED" not in out

    # M2: delete a config clause from the CNF (header count fixed up),
    # keep the original LRAT -> resolution steps cite a missing clause
    with open(cnf) as f:
        lines = f.read().splitlines()
    hdr = next(i for i, l in enumerate(lines) if l.startswith("p cnf"))
    nv, nc = lines[hdr].split()[2:4]
    del lines[hdr + 1]
    lines[hdr] = f"p cnf {nv} {int(nc) - 1}"
    cnf2 = os.path.join(tmp, "m2.cnf")
    with open(cnf2, "w", newline="\n") as f:
        f.write("\n".join(lines) + "\n")
    with open(lrat, "w", newline="\n") as f:
        f.write("\n".join(lrat_lines) + "\n")
    out = wsl(f"~/sat-tools/cake_lpr/cake_lpr {to_wsl(cnf2)} {to_wsl(lrat)}")
    results["M2_deleted_clause_cakelpr_rejected"] = "s VERIFIED UNSAT" not in out

    # M3: flip one literal inside a mid-proof LRAT addition step
    mid = len(lrat_lines) // 2
    toks = lrat_lines[mid].split()
    for j in range(1, len(toks)):
        if toks[j] not in ("0", "d") and toks[j].lstrip("-").isdigit():
            toks[j] = str(-int(toks[j]))
            break
    bad = lrat_lines[:]
    bad[mid] = " ".join(toks)
    with open(lrat, "w", newline="\n") as f:
        f.write("\n".join(bad) + "\n")
    out1 = wsl(f"~/sat-tools/drat-trim/lrat-check {to_wsl(cnf)} {to_wsl(lrat)}")
    out2 = wsl(f"~/sat-tools/cake_lpr/cake_lpr {to_wsl(cnf)} {to_wsl(lrat)}")
    results["M3_flipped_lit_lratcheck_rejected"] = \
        "c VERIFIED" not in out1 and "s VERIFIED" not in out1
    results["M3_flipped_lit_cakelpr_rejected"] = "s VERIFIED UNSAT" not in out2

    shutil.rmtree(tmp, ignore_errors=True)
    ok = all(results.values())
    for k, v in results.items():
        print(("PASS " if v else "FAIL ") + k)
    print("mutation tests:", "ALL PASS" if ok else "FAILURES PRESENT")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main(*sys.argv[1:])
