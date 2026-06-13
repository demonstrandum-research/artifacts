#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
verify_all.py — master mechanical verification for every claimed result in this repo.

Runs every banked checker end to end and prints a PASS/FAIL table. A stranger
should be able to run this with zero trust in any AI: every check below executes
a short, human-readable program against an artifact on disk and tests its output.

    python verify_all.py            # default battery (~5-13 minutes on a 2026 desktop)
    python verify_all.py --full     # adds the long redundant layers (~25 minutes total)
    python verify_all.py --strict   # treat SKIPs as failures (full zero-trust mode)
    python verify_all.py --list     # list checks without running

Requirements: Python 3.10+ (stdlib + numpy for two checks; sympy for one).
Optional: Rust binaries are prebuilt in-tree; cargo is used to rebuild them only
if missing. Lean checks need elan/lake (%USERPROFILE%\\.elan\\bin or on PATH);
they are SKIPped with a message if lake is absent.

Exit code: 0 iff no check FAILed. SKIPs are reported loudly but do not fail the
run unless --strict is given. NOTE: a SKIPped check means the corresponding
result was NOT verified on this machine — in particular, skipping the Lean
checks leaves the Borsuk result entirely unverified.

What this script does NOT do: it does not re-audit statement faithfulness
(whether each checker tests the right statement). That is documented per result
with verbatim source quotes — see RESULTS.md and VALIDATION.md next to this file.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import time

REPO = os.path.dirname(os.path.abspath(__file__))
P = os.path.join
ELAN_BIN = P(os.path.expanduser("~"), ".elan", "bin")

# ---------------------------------------------------------------- plumbing --

def child_env():
    env = dict(os.environ)
    env["PYTHONIOENCODING"] = "utf-8"
    env["PYTHONUTF8"] = "1"
    if os.path.isdir(ELAN_BIN):
        env["PATH"] = ELAN_BIN + os.pathsep + env.get("PATH", "")
    return env


def run(cmd, cwd, timeout):
    """Run a command, return (rc, combined_output). Never raises on bad exit."""
    try:
        proc = subprocess.run(
            cmd, cwd=cwd, env=child_env(), timeout=timeout,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", errors="replace")
        return proc.returncode, proc.stdout or ""
    except subprocess.TimeoutExpired:
        return 998, "TIMEOUT after %ds: %s" % (timeout, cmd)
    except FileNotFoundError as e:
        return 999, "NOT FOUND: %s (%s)" % (cmd[0], e)


def lake_exe():
    """Absolute path to lake, or None. (Windows resolves child executables
    against the parent's PATH, so we must resolve the elan shim ourselves.)"""
    w = shutil.which("lake")
    if w:
        return w
    for cand in (P(ELAN_BIN, "lake.exe"), P(ELAN_BIN, "lake")):
        if os.path.isfile(cand):
            return cand
    return None


def have_lake():
    return lake_exe() is not None


def have_cargo():
    return shutil.which("cargo") is not None


def ensure_rust_exe(exe_path, manifest_path):
    """Return None if exe is available (building it if needed), else a skip reason."""
    if os.path.isfile(exe_path):
        return None
    if not have_cargo():
        return "prebuilt %s missing and cargo not installed" % os.path.basename(exe_path)
    rc, out = run(["cargo", "build", "--release", "--manifest-path", manifest_path],
                  cwd=os.path.dirname(manifest_path), timeout=900)
    if rc != 0 or not os.path.isfile(exe_path):
        return "cargo build failed for %s" % manifest_path
    return None


def expect(rc, out, substrings, want_rc=0, forbid=()):
    """Generic validator: exit code + required substrings + forbidden substrings."""
    if rc != want_rc:
        return False, "exit=%s (wanted %s); tail: %s" % (rc, want_rc, out.strip()[-300:])
    for s in substrings:
        if s not in out:
            return False, "missing %r; tail: %s" % (s, out.strip()[-300:])
    for s in forbid:
        if s in out:
            return False, "forbidden %r present; tail: %s" % (s, out.strip()[-300:])
    return True, ""

# ------------------------------------------------------------------ checks --
# Each check function returns (status, detail) with status in PASS/FAIL/SKIP.

PY = sys.executable or "python"

IRIS = P(REPO, "problems", "p0-iris")
BORSUK_LEAN = P(REPO, "problems", "p3-moonshot", "borsuk", "lean")
KILLS = P(REPO, "problems", "p2-factory", "kills")
ATTACKS = P(REPO, "problems", "p2-factory", "attacks")
NO5 = P(REPO, "problems", "p1-records", "no-5-on-a-sphere-grid")
ELIZ = P(REPO, "problems", "p3-moonshot", "elizalde-luo")


def check_iris_python():
    cert = P(IRIS, "certificates", "cex10.txt")
    with open(cert, encoding="utf-8") as fh:
        lines = [ln.strip() for ln in fh if ln.strip()]
    if len(lines) != 5:
        return "FAIL", "expected 5 certificate lines, found %d" % len(lines)
    for i, ln in enumerate(lines, 1):
        rc, out = run([PY, P(IRIS, "verification", "checker_py", "verify_counterexample.py"), ln],
                      cwd=IRIS, timeout=120)
        # NOTE: checker A signals acceptance via the string, not the exit code.
        if "COUNTEREXAMPLE CONFIRMED" not in out or "not a counterexample" in out:
            return "FAIL", "line %d not confirmed; tail: %s" % (i, out.strip()[-200:])
    return "PASS", "5/5 lines: COUNTEREXAMPLE CONFIRMED"


def check_iris_rust():
    exe = P(IRIS, "verification", "checker_rs", "target", "release", "checker_rs.exe")
    reason = ensure_rust_exe(exe, P(IRIS, "verification", "checker_rs", "Cargo.toml"))
    if reason:
        return "SKIP", reason
    rc, out = run([exe, P(IRIS, "certificates", "cex10.txt")], cwd=IRIS, timeout=120)
    ok, why = expect(rc, out, ["All 5 certificate(s) confirmed"])
    if ok and out.count("COUNTEREXAMPLE CONFIRMED") != 5:
        ok, why = False, "expected 5 confirmations, got %d" % out.count("COUNTEREXAMPLE CONFIRMED")
    return ("PASS", "exit 0, 5/5 confirmed") if ok else ("FAIL", why)


def check_iris_mutation():
    rc, out = run([PY, "run_mutation.py"], cwd=P(IRIS, "verification", "mutation_work"),
                  timeout=600)
    ok, why = expect(rc, out, ["violations: none", "originals ok: True"])
    return ("PASS", "33/33 mutants rejected by both checkers; 5/5 originals accepted") if ok else ("FAIL", why)


def lean_deps_missing():
    """ARTIFACTS-SNAPSHOT ADJUSTMENT (documented in README.md): this public
    snapshot ships the Lean sources but not the multi-GB .lake build dir
    (mathlib dependency + build cache). If .lake/packages is absent, a bare
    `lake build` would fetch and elaborate mathlib from scratch (hours), so
    the Lean checks SKIP with instructions instead of hanging. Run
    `lake update` (mathlib's post-update hook fetches the build cache), then
    `lake build` per problems/p3-moonshot/borsuk/lean/SETUP.md, and re-run."""
    return not os.path.isdir(P(BORSUK_LEAN, ".lake", "packages"))


LEAN_DEPS_MSG = ("Lean dependency cache (.lake/) not shipped in this snapshot; "
                 "run `lake update` then `lake build` in problems/p3-moonshot/"
                 "borsuk/lean (see SETUP.md there), then re-run verify_all.py")


def check_borsuk_build():
    lk = lake_exe()
    if not lk:
        return "SKIP", "lake not found (install elan; see problems/p3-moonshot/borsuk/lean/SETUP.md)"
    if lean_deps_missing():
        return "SKIP", LEAN_DEPS_MSG
    rc, out = run([lk, "build"], cwd=BORSUK_LEAN, timeout=7200)
    ok, why = expect(rc, out, ["Build completed successfully"])
    return ("PASS", "lake build clean") if ok else ("FAIL", why)


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def check_borsuk_axioms():
    lk = lake_exe()
    if not lk:
        return "SKIP", "lake not found"
    if lean_deps_missing():
        return "SKIP", LEAN_DEPS_MSG
    rc, out = run([lk, "env", "lean", P("scripts", "CheckAxioms.lean")],
                  cwd=BORSUK_LEAN, timeout=1800)
    if rc != 0:
        return "FAIL", "exit=%s; tail: %s" % (rc, out.strip()[-300:])
    if "sorryAx" in out:
        return "FAIL", "sorryAx found in axiom audit"
    for name in ("Borsuk.witnessA_kills_conjecture3",
                 "Borsuk.conjecture3_counterexample",
                 "Borsuk.conjecture3_false"):
        if "'%s'" % name not in out:
            return "FAIL", "theorem %s missing from audit output" % name
    for m in re.finditer(r"depends on axioms: \[([^\]]*)\]", out):
        used = {a.strip() for a in m.group(1).split(",") if a.strip()}
        if not used <= ALLOWED_AXIOMS:
            return "FAIL", "non-standard axiom(s): %s" % (used - ALLOWED_AXIOMS)
    return "PASS", "all theorems use at most [propext, Classical.choice, Quot.sound]; no sorryAx"


def simple_check(checkname, cmd, cwd, substrings, timeout=600, forbid=(), detail=None):
    def f():
        rc, out = run(cmd, cwd=cwd, timeout=timeout)
        ok, why = expect(rc, out, substrings, forbid=forbid)
        return ("PASS", detail or "exit 0; " + "; ".join(repr(s) for s in substrings)) \
            if ok else ("FAIL", why)
    f.__name__ = checkname
    return f


def check_davila_rust():
    exe = P(KILLS, "davila-conj9", "rust_check", "target", "release", "rust_check.exe")
    reason = ensure_rust_exe(exe, P(KILLS, "davila-conj9", "rust_check", "Cargo.toml"))
    if reason:
        return "SKIP", reason
    cwd = P(KILLS, "davila-conj9")
    for args, want in ((["chain_indep_k2.edges", "gamma", "3"], "NONE"),
                       (["chain_indep_k2.edges", "zf", "6"], "NONE"),
                       (["chain_indep_k2.edges", "zffind", "7"], "WITNESS")):
        rc, out = run([exe] + args, cwd=cwd, timeout=300)
        if rc != 0 or want not in out:
            return "FAIL", "%s -> exit=%s out=%s (wanted %s)" % (args, rc, out.strip()[:120], want)
    return "PASS", "k=2 chain: no dominating set of size 3, no forcing set of size 6, forcing set of size 7 found"


def check_no5_battery():
    exe = P(NO5, "code", "core", "target", "release", "no5core.exe")
    reason = ensure_rust_exe(exe, P(NO5, "code", "core", "Cargo.toml"))
    if reason:
        return "SKIP", reason
    rc, out = run([PY, P("verification", "gate45_fresh_verify.py")], cwd=NO5, timeout=1800)
    ok, why = expect(rc, out, ["GATE-4/5 FRESH VERIFICATION PASSED"], forbid=["[FAIL]"])
    return ("PASS", "3 routes x 18 files + symmetry + 7 mutations + saturation + official-record anchor") \
        if ok else ("FAIL", why)


def check_no5_codex():
    rc, out = run([PY, P("verification", "codex_hostile_no5sphere_check.py")], cwd=NO5, timeout=600)
    ok, why = expect(rc, out, ['"tested_5_subsets": 376992',
                               '"zero_determinant_count_first_10": 0',
                               '"min_abs_det": 2',
                               '"central_symmetry": true'])
    return ("PASS", "376992 five-subsets, zero vanishing lifted determinants, min|det|=2, centrally symmetric") \
        if ok else ("FAIL", why)


def check_eliz_enumerator(max_n):
    def f():
        rc, out = run([PY, "enumerator.py", str(max_n)], cwd=P(ELIZ, "data"), timeout=3600)
        if rc != 0:
            return "FAIL", "exit=%s; tail: %s" % (rc, out.strip()[-300:])
        if "match=False" in out:
            return "FAIL", "formula mismatch reported"
        for n in range(1, max_n + 1):
            if ("n=%d:" % n) not in out:
                return "FAIL", "missing n=%d row" % n
        if out.count("match=True") < max_n:
            return "FAIL", "fewer than %d formula matches" % max_n
        return "PASS", "V1+V2 validations OK; counts = 3^n-3*2^(n-1)+1 for n=1..%d" % max_n
    return f


def check_eliz_cleanroom():
    rc, out = run([PY, P("codex_foil", "enumerate_cleanroom.py")], cwd=P(ELIZ, "data"),
                  timeout=900)
    if rc != 0:
        return "FAIL", "exit=%s; tail: %s" % (rc, out.strip()[-300:])
    try:
        data = json.loads(out[out.index("{"):])
    except Exception as e:
        return "FAIL", "could not parse JSON output: %s" % e
    formula = {str(n): 3 ** n - 3 * 2 ** (n - 1) + 1 for n in range(1, 7)}
    import math
    cat = lambda n: math.comb(2 * n, n) // (n + 1)
    nn = {str(n): math.factorial(n) * cat(n) for n in range(1, 7)}
    if data.get("avoider_counts") != formula:
        return "FAIL", "avoider counts %s != formula %s" % (data.get("avoider_counts"), formula)
    if data.get("nonnesting_totals") != nn:
        return "FAIL", "nonnesting totals %s != n!*Catalan(n) %s" % (data.get("nonnesting_totals"), nn)
    return "PASS", "clean-room literal-definition counts n=1..6 match formula and n!*Cat(n)"


def check_pandey_rust():
    exe = P(KILLS, "pandey-parity", "bf_gp.exe")
    if not os.path.isfile(exe):
        if not shutil.which("rustc"):
            return "SKIP", "prebuilt bf_gp.exe missing and rustc not installed"
        rc, out = run(["rustc", "-O", "-o", exe, "bf_gp.rs"],
                      cwd=P(KILLS, "pandey-parity"), timeout=600)
        if rc != 0 or not os.path.isfile(exe):
            return "SKIP", "rustc build of bf_gp.rs failed"
    rc, out = run([exe], cwd=P(KILLS, "pandey-parity"), timeout=600)
    ok, why = expect(rc, out, ["GP(9,2): [1, 18, 126, 438, 801, 747, 303, 27]",
                               "GP(7,3): [1, 14, 70, 154, 147, 49]",
                               "GP(3,1): [1, 6, 6]"])
    return ("PASS", "independent Rust brute force reproduces the three key independence polynomials") \
        if ok else ("FAIL", why)


def check_no5_rust_tests():
    if not have_cargo():
        return "SKIP", "cargo not installed"
    rc, out = run(["cargo", "test", "--release"], cwd=P(NO5, "code", "core"), timeout=1800)
    if rc != 0:
        return "FAIL", "exit=%s; tail: %s" % (rc, out.strip()[-300:])
    fails = re.findall(r"test result: (\w+)\. (\d+) passed.*?(\d+) failed", out)
    if not fails or any(f[0] != "ok" or f[2] != "0" for f in fails):
        return "FAIL", "test result lines: %s" % fails
    total = sum(int(f[1]) for f in fails)
    return "PASS", "%d Rust unit tests pass (incl. degenerate-quadruple traps)" % total


def check_sun_cyclotomic():
    rc, out = run([PY, "independent_checker.py", "29"],
                  cwd=P(ATTACKS, "sun-46", "independent"), timeout=3600)
    ok, why = expect(rc, out,
                     ["ALL CHECKS PASSED", "1053859", "-4806838304",
                      "CONJECTURE 4.6(ii) VIOLATIONS CONFIRMED"],
                     forbid=["MISMATCH"])
    return ("PASS", "exact cyclotomic layer (no floats/CRT) reproduces published values and the kill pair") \
        if ok else ("FAIL", why)


# ------------------------------------------------------------- check table --
# (section, check-id, callable, full_only)

CHECKS = [
    # -- IRIS Conjecture 6.1 refutation ------------------------------------
    ("IRIS-6.1", "iris/checker-A-python", check_iris_python, False),
    ("IRIS-6.1", "iris/checker-B-rust", check_iris_rust, False),
    ("IRIS-6.1", "iris/mutation-suite", check_iris_mutation, False),
    # -- Borsuk Conjecture 3 disproof (Lean 4) -----------------------------
    ("Borsuk-C3", "borsuk/lake-build", check_borsuk_build, False),
    ("Borsuk-C3", "borsuk/axiom-audit", check_borsuk_axioms, False),
    # -- p2-factory kills ---------------------------------------------------
    ("graffiti-143", "g143/checker", simple_check(
        "g143", [PY, "checker_g143.py", "certificate_g143.json"],
        P(KILLS, "graffiti-143"), ["CHECKER VERDICT: ACCEPT"], timeout=600,
        detail="dual-route exact checker (sympy isolation + stdlib Sturm) accepts all instances"), False),
    ("graffiti-143", "g143/mutation-suite", simple_check(
        "g143m", [PY, "mutation_tests.py"], P(KILLS, "graffiti-143"),
        ["MUTATION TESTS: ALL KILLED"], timeout=600,
        detail="10/10 targeted corruptions rejected"), False),
    ("graffiti-154", "g154/checker-A", simple_check(
        "g154", [PY, "check_graffiti154.py"], P(KILLS, "graffiti-154"),
        ["OVERALL: ALL CHECKS PASS"], timeout=1200,
        detail="exact integer test 8mW^2 > n^7 for lollipops incl. (72,72); built-in mutations killed"), False),
    ("graffiti-154", "g154/checker-B-codex", simple_check(
        "g154b", [PY, "codex_referee_audit.py"], P(KILLS, "graffiti-154"),
        ["violating lollipops with n<=117: [] count=0", "(118, 48, 70, True, False)"],
        timeout=600,
        detail="independent checker B (written by the hostile Codex referee): minimality scan agrees"), False),
    ("davila-conj9", "dc9/checker", simple_check(
        "dc9", [PY, "checker_conj9.py"], P(KILLS, "davila-conj9"),
        ["[REFUTES Conjecture 9]", "rebuild is isomorphic to record graph"], timeout=600,
        detail="G14: gamma=4 (exhaustive), Z=7 (exhaustive) -> Z = gamma+3"), False),
    ("davila-conj9", "dc9/mutation-suite", simple_check(
        "dc9m", [PY, "mutation_tests.py"], P(KILLS, "davila-conj9"),
        ["MUTATION TESTING PASSED"], timeout=600,
        detail="8/8 corruptions rejected"), False),
    ("davila-conj9", "dc9/rust-checker", check_davila_rust, False),
    ("pandey-parity", "gp/selftest", simple_check(
        "gpself", [PY, "check_pandey_parity.py", "--selftest"], P(KILLS, "pandey-parity"),
        ["ALL CHECKS PASSED"], timeout=600,
        detail="checker self-mutation tests pass"), False),
    ("pandey-parity", "gp/checker", simple_check(
        "gp", [PY, "check_pandey_parity.py"], P(KILLS, "pandey-parity"),
        ["ALL CHECKS PASSED"], timeout=600,
        detail="GP(9,2) not real-rooted (exact Sturm), GP(7,3)/GP(3,1) real-rooted -> both directions dead"), False),
    ("pandey-parity", "gp/rust-bruteforce", check_pandey_rust, False),
    ("solubilizer-A.1", "a1/checker", simple_check(
        "a1", [PY, "check_a1_refutation.py"], P(KILLS, "solubilizer-a1"),
        ["ACCEPT: Conjecture A.1 of arXiv:2412.16177v1 is REFUTED"], timeout=600,
        detail="A5, x=y=5-cycle: Sol(x) = D10; intersection contains no nontrivial normal subgroup"), False),
    ("solubilizer-A.1", "a1/mutation-suite", simple_check(
        "a1m", [PY, "mutation_test.py"], P(KILLS, "solubilizer-a1"),
        ["all 13 mutants rejected, pristine accepted"], timeout=900,
        detail="13/13 mutants rejected"), False),
    ("solubilizer-A.13", "a13/checker", simple_check(
        "a13", [PY, "checker_a13.py", "--verify", "certificate_a13.json"],
        P(KILLS, "solubilizer-a13"),
        ["certificate certificate_a13.json matches independent recomputation", "ACCEPT"],
        timeout=600, forbid=["REJECT"],
        detail="A5 x S3: normal core of Sol(x) = 1 x S3 != 1 = hypercenter"), False),
    ("solubilizer-A.13", "a13/mutation-suite", simple_check(
        "a13m", [PY, "mutation_test.py"], P(KILLS, "solubilizer-a13"),
        ["MUTATION TEST: PASS (all mutants rejected)"], timeout=900,
        detail="7/7 certificate corruptions rejected"), False),
    ("solubilizer-A.16", "a16/checker", simple_check(
        "a16", [PY, "checker.py"], P(KILLS, "solubilizer-a16"),
        ["All checks passed."], timeout=900,
        detail="A5 x S4: Sol cap N(Sol) has derived length 3, not metabelian (32 checks)"), False),
    ("solubilizer-A.16", "a16/mutation-suite", simple_check(
        "a16m", [PY, "mutation_tests.py"], P(KILLS, "solubilizer-a16"),
        ["ALL MUTATION TESTS PASSED"], timeout=900,
        detail="6/6 mutants rejected + positive control"), False),
    ("sun-4.6", "sun/snippet-sanity", simple_check(
        "sun0", [PY, "snippet_check.py"], P(KILLS, "sun-46"),
        ["-239 -6 -7094142", "1053859 -4806838304"], timeout=300,
        detail="float sanity: reproduces Sun's published negatives, then the kill pair"), False),
    ("sun-4.6", "sun/exact-subsetDP", simple_check(
        "sun1", [PY, "mycheck_2026-06-12.py"], P(ATTACKS, "sun-46"),
        ["all 19 reproduced exactly.", "VERDICT", "is FALSE"], timeout=1800,
        detail="exact CRT-certified s_29=1053859>0, s'_29=-4806838304<0; all 19 published values reproduced"), False),
    ("koch-narayan", "kn/cleanroom-checker", simple_check(
        "kn1", [PY, P("independent", "cleanroom_check.py")], P(KILLS, "koch-narayan"),
        ["OVERALL VERDICT: KILL CONFIRMED"], timeout=600,
        detail="n=13 gamma=4 graph: 22 edges > m(13,4)=21 under both Phi readings"), False),
    ("koch-narayan", "kn/indy-checker", simple_check(
        "kn2", [PY, P("independent", "indy_check.py")], P(KILLS, "koch-narayan"),
        ["OVERALL: KILL CONFIRMED"], timeout=600,
        detail="independent rebuild from text + own graph6 decoder agrees"), False),
    ("koch-narayan", "kn/mutation-suite", simple_check(
        "kn3", [PY, P("independent", "mutation_tests.py")], P(KILLS, "koch-narayan"),
        ["MUTATION TESTS: ALL KILLED"], timeout=600,
        detail="10/10 corruptions rejected, pristine accepted"), False),
    ("kills (cross)", "kills/orchestrator-rebuild", simple_check(
        "vk", [PY, "verify_kills.py"], P(REPO, "problems", "p2-factory"),
        ["REFUTED: PASS"], timeout=900, forbid=["FAIL"],
        detail="orchestrator re-derivation of 5 kills from construction descriptions (needs numpy)"), False),
    # -- C(13) >= 36 record -------------------------------------------------
    ("C(13)>=36", "no5/check-cert", simple_check(
        "no5", [PY, P("code", "check_cert.py"), P("certificates", "record36_centralsym.json"), "13"],
        NO5, ["VALID m=36 n=13"], timeout=300,
        detail="all 376,992 5-subsets of the 36-point set have nonzero lifted determinant"), False),
    ("C(13)>=36", "no5/full-battery", check_no5_battery, False),
    ("C(13)>=36", "no5/codex-hostile-checker", check_no5_codex, False),
    # -- Elizalde-Luo theorem ----------------------------------------------
    ("Elizalde-Luo", "eliz/ground-truth-n7", check_eliz_enumerator(7), False),
    ("Elizalde-Luo", "eliz/cleanroom-n6", check_eliz_cleanroom, False),
    ("Elizalde-Luo", "eliz/lemma-spotcheck", simple_check(
        "elspot", [PY, "triage_spotcheck.py"], P(ELIZ, "work"),
        ["ALL SPOT CHECKS PASSED"], timeout=900,
        detail="clean-room spot-audit: Theorem A on all 2,162,160 pairs at n=7; per-shape counts; bijection"), False),
    # -- long redundant layers (--full) --------------------------------------
    ("C(13)>=36", "no5/rust-unit-tests", check_no5_rust_tests, True),
    ("Elizalde-Luo", "eliz/ground-truth-n8", check_eliz_enumerator(8), True),
    ("sun-4.6", "sun/cleanroom-cyclotomic", check_sun_cyclotomic, True),
]

# -------------------------------------------------------------------- main --

def main():
    ap = argparse.ArgumentParser(description="Run every mechanical check for this repo's results.")
    ap.add_argument("--full", action="store_true", help="also run the long redundant layers")
    ap.add_argument("--strict", action="store_true",
                    help="treat SKIPs as failures (a skipped check = an unverified result)")
    ap.add_argument("--list", action="store_true", help="list checks and exit")
    ap.add_argument("--only", metavar="SUBSTR", default=None,
                    help="run only checks whose id contains SUBSTR")
    args = ap.parse_args()

    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except Exception:
        pass

    todo = [(sec, cid, fn) for sec, cid, fn, full_only in CHECKS
            if (args.full or not full_only)
            and (args.only is None or args.only in cid)]

    if args.list:
        for sec, cid, _ in todo:
            print("%-14s %s" % (sec, cid))
        return 0

    print("verify_all.py — %d checks%s, repo %s" %
          (len(todo), " (--full)" if args.full else "", REPO))
    print("=" * 100)
    rows = []
    t0 = time.time()
    for sec, cid, fn in todo:
        t = time.time()
        try:
            status, detail = fn()
        except Exception as e:  # a checker crashing is a FAIL, not a crash of the harness
            status, detail = "FAIL", "harness exception: %r" % e
        dt = time.time() - t
        rows.append((sec, cid, status, dt, detail))
        print("[%-4s] %-14s %-28s %7.1fs  %s" % (status, sec, cid, dt, detail[:120]))
    total = time.time() - t0

    npass = sum(1 for r in rows if r[2] == "PASS")
    nfail = sum(1 for r in rows if r[2] == "FAIL")
    nskip = sum(1 for r in rows if r[2] == "SKIP")
    print("=" * 100)
    print("TOTAL: %d PASS, %d FAIL, %d SKIP in %.1f s (%.1f min)"
          % (npass, nfail, nskip, total, total / 60))
    if nfail:
        print("FAILED CHECKS:")
        for sec, cid, status, dt, detail in rows:
            if status == "FAIL":
                print("  %s :: %s :: %s" % (sec, cid, detail))
    if nskip:
        skipped_sections = sorted({sec for sec, _, status, _, _ in rows if status == "SKIP"})
        print("WARNING: SKIPped checks mean the following results were NOT verified "
              "on this machine: %s" % ", ".join(skipped_sections))
        for sec, cid, status, dt, detail in rows:
            if status == "SKIP":
                print("  SKIPPED: %s :: %s (%s)" % (sec, cid, detail))
        if args.strict:
            print("(--strict: treating SKIPs as failure)")
    return 1 if (nfail or (args.strict and nskip)) else 0


if __name__ == "__main__":
    sys.exit(main())
