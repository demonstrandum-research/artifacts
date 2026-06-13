import itertools
import json
from pathlib import Path


# ARTIFACTS-SNAPSHOT ADJUSTMENT (documented in README.md at the repo root):
# the original banked checker hardcoded the absolute path of the build machine
# (C:\Users\...\maths\problems\...\record36_centralsym.json). For the public
# snapshot the path is resolved relative to this file; the target file is
# byte-identical (sha256 333d36ec... as recorded in RESULTS.md section 12).
CERT = Path(__file__).resolve().parents[1] / "certificates" / "record36_centralsym.json"


def is_strict_int(value):
    return type(value) is int


def bareiss_det(matrix):
    """Exact integer determinant using fraction-free Gaussian elimination."""
    a = [row[:] for row in matrix]
    n = len(a)
    sign = 1
    prev = 1

    for k in range(n - 1):
        pivot = None
        for r in range(k, n):
            if a[r][k] != 0:
                pivot = r
                break
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign

        p = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (a[i][j] * p - a[i][k] * a[k][j]) // prev
        prev = p
        for i in range(k + 1, n):
            a[i][k] = 0
        for j in range(k + 1, n):
            a[k][j] = 0

    return sign * a[n - 1][n - 1]


def lifted_row(point):
    x, y, z = point
    return [x, y, z, x * x + y * y + z * z, 1]


def main():
    raw = CERT.read_text(encoding="utf-8")
    data = json.loads(raw)

    if not isinstance(data, list):
        raise SystemExit("top-level JSON value is not a list")
    if len(data) != 36:
        raise SystemExit(f"point count is {len(data)}, not 36")

    points = []
    for idx, point in enumerate(data):
        if not isinstance(point, list):
            raise SystemExit(f"point {idx} is not a JSON list")
        if len(point) != 3:
            raise SystemExit(f"point {idx} has length {len(point)}, not 3")
        if not all(is_strict_int(c) for c in point):
            raise SystemExit(f"point {idx} has a non-integer or bool coordinate: {point!r}")
        if not all(0 <= c <= 12 for c in point):
            raise SystemExit(f"point {idx} has coordinate outside 0..12: {point!r}")
        points.append(tuple(point))

    if len(set(points)) != len(points):
        raise SystemExit("points are not distinct")

    point_set = set(points)
    reflected = {tuple(12 - c for c in p) for p in points}
    if reflected != point_set:
        missing = sorted(reflected - point_set)
        extra = sorted(point_set - reflected)
        raise SystemExit(f"central symmetry failure: missing={missing}, extra={extra}")

    fixed = [p for p in points if p == tuple(12 - c for c in p)]
    orbit_reps = set()
    orbit_pairs = []
    for p in sorted(points):
        q = tuple(12 - c for c in p)
        pair = tuple(sorted((p, q)))
        if pair not in orbit_reps:
            orbit_reps.add(pair)
            orbit_pairs.append(pair)

    rows = [lifted_row(p) for p in points]
    total = 0
    zero_subsets = []
    min_abs = None
    min_records = []
    max_abs = 0

    for combo in itertools.combinations(range(len(points)), 5):
        det = bareiss_det([rows[i] for i in combo])
        abs_det = abs(det)
        total += 1
        if det == 0:
            zero_subsets.append((combo, [points[i] for i in combo]))
            if len(zero_subsets) >= 10:
                break
        if min_abs is None or abs_det < min_abs:
            min_abs = abs_det
            min_records = [(combo, det, [points[i] for i in combo])]
        elif abs_det == min_abs and len(min_records) < 10:
            min_records.append((combo, det, [points[i] for i in combo]))
        if abs_det > max_abs:
            max_abs = abs_det

    print(json.dumps(
        {
            "point_count": len(points),
            "distinct_count": len(set(points)),
            "strict_json_int_coordinates": True,
            "coordinate_min": min(min(p) for p in points),
            "coordinate_max": max(max(p) for p in points),
            "central_symmetry": reflected == point_set,
            "fixed_points_under_reflection": fixed,
            "orbit_pair_count": len(orbit_pairs),
            "tested_5_subsets": total,
            "expected_5_subsets": 376_992,
            "zero_determinant_count_first_10": len(zero_subsets),
            "zero_determinant_examples": zero_subsets,
            "min_abs_det": min_abs,
            "min_abs_det_examples": min_records,
            "max_abs_det": max_abs,
        },
        indent=2,
    ))


if __name__ == "__main__":
    main()
