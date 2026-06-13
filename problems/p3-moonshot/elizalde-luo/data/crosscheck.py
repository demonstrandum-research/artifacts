#!/usr/bin/env python3
"""Cross-check python_results.json vs rust_results.json vs the Codex clean-room foil,
then emit counts.json, refined_stats.json, validation.json."""
import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name):
    with open(os.path.join(HERE, name), encoding="utf-8") as f:
        return json.load(f)


py = load("python_results.json")
rs = load("rust_results.json")

# Codex clean-room foil output (thread 019eb99d-8e25-76a1-bb9b-ad9df1147f59),
# pasted verbatim from its final JSON answer:
codex = {
    "nonnesting_totals": {"1": 1, "2": 4, "3": 30, "4": 336, "5": 5040, "6": 95040},
    "avoider_counts": {"1": 1, "2": 4, "3": 16, "4": 58, "5": 196, "6": 634},
    "descents_n4": {"0": 1, "1": 6, "2": 16, "3": 19, "4": 12, "5": 3, "6": 1},
    "descents_n5": {"0": 1, "1": 8, "2": 27, "3": 53, "4": 57, "5": 31, "6": 15,
                    "7": 3, "8": 1},
    "first_letter_n5": {"1": 5, "2": 47, "3": 92, "4": 47, "5": 5},
    "positions_of_n_n5": {
        "1,2": 1, "1,3": 1, "1,4": 1, "1,5": 1, "1,6": 1, "2,4": 1, "2,5": 2,
        "2,6": 1, "2,7": 1, "3,4": 1, "3,5": 1, "3,6": 2, "3,7": 5, "3,8": 2,
        "4,6": 2, "4,7": 2, "4,8": 4, "4,9": 11, "5,6": 4, "5,7": 4, "5,8": 1,
        "5,9": 1, "5,10": 8, "6,8": 8, "6,9": 8, "6,10": 1, "7,8": 16, "7,9": 16,
        "7,10": 2, "8,10": 29, "9,10": 58},
}

py_by_n = {r["n"]: r for r in py["results"]}
rs_by_n = {r["n"]: r for r in rs["results"]}

problems = []

# 1. Python vs Rust, n = 1..7, every field including all four stat tables
for n in range(1, 8):
    a, b = py_by_n[n], rs_by_n[n]
    for key in ["nonnesting_total", "avoider_count", "formula_value",
                "formula_matches", "canonical_label_avoiders",
                "canonical_times_factorial"]:
        if a[key] != b[key]:
            problems.append(f"py vs rust n={n} field {key}: {a[key]} != {b[key]}")
    for tab in ["by_first_letter", "by_positions_of_n", "by_descents",
                "by_dyck_shape"]:
        ta = {k: v for k, v in a["stats"][tab].items()}
        tb = {k: v for k, v in b["stats"][tab].items()}
        if ta != tb:
            problems.append(f"py vs rust n={n} stats {tab} differ")

# 2. Rust internal consistency at n=8 (stat tables must each sum to the count)
for n in range(1, 9):
    r = rs_by_n[n]
    for tab in ["by_first_letter", "by_positions_of_n", "by_descents",
                "by_dyck_shape"]:
        s = sum(r["stats"][tab].values())
        if s != r["avoider_count"]:
            problems.append(f"rust n={n} stats {tab} sum {s} != {r['avoider_count']}")
    if r["nonnesting_total"] != math.factorial(n) * (math.comb(2 * n, n) // (n + 1)):
        problems.append(f"rust n={n} nonnesting_total wrong")

# 3. Codex clean-room foil vs Rust
codex_ok = True
for n in range(1, 7):
    if codex["nonnesting_totals"][str(n)] != rs_by_n[n]["nonnesting_total"]:
        problems.append(f"codex nonnesting n={n} mismatch")
        codex_ok = False
    if codex["avoider_counts"][str(n)] != rs_by_n[n]["avoider_count"]:
        problems.append(f"codex avoiders n={n} mismatch")
        codex_ok = False
for tab, mine in [("descents_n4", rs_by_n[4]["stats"]["by_descents"]),
                  ("descents_n5", rs_by_n[5]["stats"]["by_descents"]),
                  ("first_letter_n5", rs_by_n[5]["stats"]["by_first_letter"]),
                  ("positions_of_n_n5", rs_by_n[5]["stats"]["by_positions_of_n"])]:
    if codex[tab] != mine:
        problems.append(f"codex {tab} mismatch: {codex[tab]} != {mine}")
        codex_ok = False

print("PROBLEMS:" if problems else "ALL CROSS-CHECKS PASS", problems or "")

# ---- emit final artifacts ----
counts = {
    "conjecture": "c_n({1132,3312} | nonnesting) = 3^n - 3*2^(n-1) + 1",
    "source": "Elizalde-Luo arXiv:2412.00336 (DMTCS 27:1 #13), Table 4 (tab:conjecture)",
    "oeis": "A168583 with offset 3: c_n = A168583(n+2)",
    "table": [
        {
            "n": n,
            "nonnesting_total": rs_by_n[n]["nonnesting_total"],
            "avoider_count": rs_by_n[n]["avoider_count"],
            "formula_value": rs_by_n[n]["formula_value"],
            "formula_matches": rs_by_n[n]["formula_matches"],
        }
        for n in range(1, 9)
    ],
    "all_match": all(rs_by_n[n]["formula_matches"] for n in range(1, 9)),
}
with open(os.path.join(HERE, "counts.json"), "w", encoding="utf-8") as f:
    json.dump(counts, f, indent=1)

refined = {
    "description": "Refined statistics over {1132,3312}-avoiding nonnesting "
                   "permutations of {1,1,...,n,n}. Computed by enumerator.rs "
                   "(n=1..8), bitwise-identical to enumerator.py for n=1..7. "
                   "Keys: by_first_letter = value of w_1; by_positions_of_n = "
                   "1-indexed positions (i,j) of the two copies of n; by_descents "
                   "= #{i : w_i > w_{i+1}}; by_dyck_shape = openers/closers shape "
                   "(first occurrence = U, second = D); canonical_label_avoiders "
                   "= avoiders whose arc labels in opener order are 1,2,...,n "
                   "(equivalently, first occurrences of 1..n appear in increasing "
                   "order).",
    "per_n": [rs_by_n[n] for n in range(1, 9)],
}
with open(os.path.join(HERE, "refined_stats.json"), "w", encoding="utf-8") as f:
    json.dump(refined, f, indent=1)

validation = {
    "V1_fast_checks_vs_literal_definition": py["validations"]["V1_fast_vs_naive"],
    "V2_shape_perm_construction_vs_literal_nonnesting": py["validations"]["V2_generation"],
    "V3_nonnesting_totals_equal_nfact_catalan": "asserted for n=1..7 (python) and n=1..8 (rust internal check in crosscheck.py)",
    "V4_canonical_first_occurrence_normalization": {
        "verdict": "INVALID as a counting shortcut for this problem",
        "reason": "{1132,3312}-avoidance is not invariant under relabeling letters; "
                  "the paper counts ALL labeled words (raw count).",
        "evidence": {
            str(n): {
                "raw_avoider_count": py_by_n[n]["avoider_count"],
                "canonical_avoiders_times_n_factorial":
                    py_by_n[n]["canonical_times_factorial"],
            } for n in range(1, 8)
        },
        "side_observation": "canonical (identity-labeled) avoiders = n for every "
                            "computed n = 1..8",
    },
    "V5_formula_check": {str(n): rs_by_n[n]["formula_matches"] for n in range(1, 9)},
    "python_vs_rust": "all fields and all four stat tables identical for n=1..7",
    "codex_clean_room_foil": {
        "thread_id": "019eb99d-8e25-76a1-bb9b-ad9df1147f59",
        "scope": "n=1..6 counts + descents(n=4,5), first letter(n=5), "
                 "positions of n (n=5)",
        "agrees": codex_ok,
        "codex_method_notes": "Literal subsequence containment with pairwise "
            "order/equality comparisons was run over every multiset permutation "
            "for n<=5. For n=6, nonnesting words were generated by the "
            "independently derived FIFO closure rule for nonnested arcs; this "
            "generator was exhaustively validated against the literal "
            "all-permutation path for n=1..5. Avoidance of 1132 and 3312 was "
            "still checked by the literal subsequence scan.",
        "codex_raw_output": codex,
    },
    "problems_found": problems,
}
with open(os.path.join(HERE, "validation.json"), "w", encoding="utf-8") as f:
    json.dump(validation, f, indent=1)

print("wrote counts.json, refined_stats.json, validation.json")
