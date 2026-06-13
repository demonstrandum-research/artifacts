import sys, time
sys.path.insert(0, r"C:/Users/jacks/source/repos/maths/problems/p2-factory/attacks/sun-46/independent")
import independent_checker as ic

CLAIMS = {29: -4806838304, 31: -1518806869720}
lines = []
for p, claim in CLAIMS.items():
    t0 = time.time()
    val = ic.compute_sprime(p)
    fl = ic.sprime_float(p)
    ok = (val == claim) and (val % p == 1) and abs(fl - val) / abs(val) < 1e-6
    msg = (f"s'_{p} = {val}  claim={claim}  match={val==claim}  "
           f"mod-p={val%p} (want 1)  float~{fl:.6g}  {time.time()-t0:.1f}s  "
           f"{'PASS' if ok else 'FAIL'}")
    print(msg, flush=True)
    lines.append(msg)
with open("sprime_kill.log", "w") as f:
    f.write("\n".join(lines) + "\n")
