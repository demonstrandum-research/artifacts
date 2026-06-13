# mutation_test.py -- validates checker_a13.py --verify by corrupting the certificate
# in targeted ways; EVERY mutant must be REJECTED (checker exit != 0).
import json, copy, subprocess, sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(HERE, "certificate_a13.json")
CHECKER = os.path.join(HERE, "checker_a13.py")

with open(CERT, encoding="utf-8") as f:
    base = json.load(f)

def mutants():
    m = copy.deepcopy(base)                       # 1: drop an element of Sol_G(x)
    m["sol_x"] = m["sol_x"][1:]
    yield "drop-sol-element", m

    m = copy.deepcopy(base)                       # 2: smuggle a wrong element into the core
    m["core"] = m["core"] + [[1, 0, 2, 3, 4, 5, 6, 7]]
    m["core_order"] = 7
    yield "extra-core-element", m

    m = copy.deepcopy(base)                       # 3: claim the hypercenter equals the core
    m["hypercenter"] = m["core"]
    m["hypercenter_order"] = 6
    m["upper_central_series_orders"] = [1, 6]
    yield "inflate-hypercenter", m

    m = copy.deepcopy(base)                       # 4: swap x for the identity
    m["x"] = [0, 1, 2, 3, 4, 5, 6, 7]
    yield "wrong-x", m

    m = copy.deepcopy(base)                       # 5: witness outside the core
    m["witness_in_core_not_in_hypercenter"] = [1, 2, 3, 4, 0, 5, 6, 7]
    yield "bad-witness", m

    m = copy.deepcopy(base)                       # 6: tamper with the verbatim statement
    m["statement_verbatim"] = m["statement_verbatim"].replace("hypercenter", "center")
    yield "tampered-statement", m

    m = copy.deepcopy(base)                       # 7: misreport the sweep
    m["sweep_all_x"]["a13_violation_count"] = 0
    yield "sweep-zeroed", m

all_rejected = True
for name, m in mutants():
    path = os.path.join(HERE, "mutant_%s.json" % name)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(m, f)
    r = subprocess.run([sys.executable, CHECKER, "--verify", path],
                       capture_output=True, text=True)
    verdict = "REJECTED" if r.returncode != 0 else "ACCEPTED (BUG!)"
    last = (r.stdout.strip().splitlines() or ["<no output>"])[-1]
    print("%-22s -> %s | %s" % (name, verdict, last))
    if r.returncode == 0:
        all_rejected = False
    os.remove(path)

print("MUTATION TEST:", "PASS (all mutants rejected)" if all_rejected else "FAIL")
sys.exit(0 if all_rejected else 1)
