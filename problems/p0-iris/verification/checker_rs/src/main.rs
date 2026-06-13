//! Independent certificate checker refuting Conjecture 6.1 ("NuevaMirada") of the
//! IRIS paper (Davila, De Loera, Eddy, Fang, Lu, Yang; ICML 2025 AI4Math workshop,
//! OpenReview id v6Ulp3U1ZT).
//!
//! Conjecture 6.1 (verbatim): "If P is a simple 3-polytope with face vector
//! (p3, p4, ..., pm), such that sum_{k>=7} pk >= 3, then
//!     p6 >= 39/20 + p3/2 - p5/4 - sum_{k>=7} pk."
//!
//! A certificate line is "<n> <rotation>": a plantri ascii (-a) encoding of a
//! planar triangulation T on n vertices (comma-separated adjacency lists in
//! rotation order, vertices a, b, c, ...). The counterexample polytope graph G
//! is the planar dual of T; this program builds that dual explicitly from the
//! traced faces of T and re-derives everything from scratch.
//!
//! For each line this checker verifies, in order:
//!   1. parse: exactly n adjacency lists over the letters a..(a+n-1);
//!   2. T is a valid simple rotation system: no loops, no duplicate entries
//!      in any rotation (no multi-edges), symmetric adjacency;
//!   3. T is connected (explicit BFS), and face tracing of the rotation system
//!      partitions all darts into faces with V - E + F = 2 (genus 0, i.e. the
//!      rotation system is a planar embedding) and every face a triangle;
//!   4. G = dual(T) (built from the face incidences of T) is simple, 3-regular,
//!      and its inherited rotation system is planar by the same Euler/face-trace
//!      criterion;
//!   5. G is 3-connected (brute force: removing any 0, 1 or 2 vertices leaves
//!      the rest connected), hence by Steinitz G is the graph of a simple
//!      3-polytope P whose 2-faces are the traced faces of G;
//!   6. the face vector (p3, ..., pm) of G is computed from the traced face
//!      sizes of G; all faces have size >= 3;
//!   7. hypothesis: S = sum_{k>=7} pk >= 3;
//!   8. exact integer violation: 20*p6 < 39 + 10*p3 - 5*p5 - 20*S
//!      (equivalent to p6 < 39/20 + p3/2 - p5/4 - S over the rationals).
//!
//! Exit code 0 and "COUNTEREXAMPLE CONFIRMED" per line only if every check
//! passes on every line; otherwise a reason is printed and the exit code is
//! nonzero.

use std::env;
use std::fs;
use std::process::exit;

type Adj = Vec<Vec<usize>>;
type Dart = (usize, usize); // directed edge (from, to)

/// Parse one certificate line "<n> <comma-separated rotation lists>".
fn parse_line(line: &str) -> Result<Adj, String> {
    let toks: Vec<&str> = line.split_whitespace().collect();
    if toks.len() != 2 {
        return Err(format!(
            "expected 2 whitespace-separated tokens (n and rotation), got {}",
            toks.len()
        ));
    }
    let n: usize = toks[0]
        .parse()
        .map_err(|e| format!("cannot parse vertex count '{}': {}", toks[0], e))?;
    if n < 4 {
        return Err(format!("n = {} but a planar triangulation needs n >= 4", n));
    }
    if n > 26 {
        return Err(format!("n = {} exceeds the 26 letters of the ascii encoding", n));
    }
    let parts: Vec<&str> = toks[1].split(',').collect();
    if parts.len() != n {
        return Err(format!(
            "expected {} comma-separated adjacency lists, got {}",
            n,
            parts.len()
        ));
    }
    let mut adj: Adj = Vec::with_capacity(n);
    for (v, part) in parts.iter().enumerate() {
        if part.is_empty() {
            return Err(format!("vertex {} has an empty adjacency list", v));
        }
        let mut row = Vec::with_capacity(part.len());
        for ch in part.chars() {
            if !ch.is_ascii_lowercase() {
                return Err(format!("invalid character '{}' in rotation", ch));
            }
            let u = (ch as u8 - b'a') as usize;
            if u >= n {
                return Err(format!("vertex letter '{}' out of range for n = {}", ch, n));
            }
            row.push(u);
        }
        adj.push(row);
    }
    Ok(adj)
}

/// Validate that `adj` is the rotation system of a simple graph:
/// no loops, no duplicate neighbors, symmetric adjacency.
/// Returns the number of undirected edges.
fn validate_rotation_system(adj: &Adj, name: &str) -> Result<usize, String> {
    let n = adj.len();
    let mut darts = 0usize;
    for (v, row) in adj.iter().enumerate() {
        let mut seen = vec![false; n];
        for &u in row {
            if u == v {
                return Err(format!("{}: loop at vertex {}", name, v));
            }
            if seen[u] {
                return Err(format!(
                    "{}: multi-edge {}-{} (duplicate neighbor in rotation)",
                    name, v, u
                ));
            }
            seen[u] = true;
        }
        darts += row.len();
    }
    for (v, row) in adj.iter().enumerate() {
        for &u in row {
            if !adj[u].contains(&v) {
                return Err(format!(
                    "{}: asymmetric adjacency: {} lists {} but not conversely",
                    name, v, u
                ));
            }
        }
    }
    if darts % 2 != 0 {
        return Err(format!("{}: odd number of darts", name));
    }
    Ok(darts / 2)
}

/// BFS connectivity of the graph with the vertices in `removed` deleted.
fn connected_without(adj: &Adj, removed: &[usize]) -> bool {
    let n = adj.len();
    let mut gone = vec![false; n];
    for &r in removed {
        gone[r] = true;
    }
    let start = match (0..n).find(|&v| !gone[v]) {
        Some(s) => s,
        None => return true, // nothing left: vacuously connected
    };
    let mut seen = vec![false; n];
    let mut stack = vec![start];
    seen[start] = true;
    let mut count = 1usize;
    while let Some(v) = stack.pop() {
        for &u in &adj[v] {
            if !gone[u] && !seen[u] {
                seen[u] = true;
                count += 1;
                stack.push(u);
            }
        }
    }
    count == n - removed.len()
}

/// Trace the faces of the embedding defined by the rotation system `adj`.
/// Rule: the successor of dart (v -> u) is (u -> w) where w is the neighbor
/// immediately after v in the cyclic rotation at u. Every dart lies on exactly
/// one face cycle; the cycles (as dart sequences) are returned.
fn trace_faces(adj: &Adj, name: &str) -> Result<Vec<Vec<Dart>>, String> {
    let n = adj.len();
    // pos[v][u] = index of u within adj[v] (validated unique beforehand)
    let mut pos: Vec<Vec<Option<usize>>> = vec![vec![None; n]; n];
    for v in 0..n {
        for (i, &u) in adj[v].iter().enumerate() {
            pos[v][u] = Some(i);
        }
    }
    let mut visited: Vec<Vec<bool>> = adj.iter().map(|r| vec![false; r.len()]).collect();
    let mut faces: Vec<Vec<Dart>> = Vec::new();
    for v0 in 0..n {
        for i0 in 0..adj[v0].len() {
            if visited[v0][i0] {
                continue;
            }
            let mut face: Vec<Dart> = Vec::new();
            let (mut v, mut i) = (v0, i0);
            loop {
                if visited[v][i] {
                    return Err(format!(
                        "{}: face tracing revisited a dart; corrupt rotation system",
                        name
                    ));
                }
                visited[v][i] = true;
                let u = adj[v][i];
                face.push((v, u));
                let j = pos[u][v]
                    .ok_or_else(|| format!("{}: missing reverse dart {}->{}", name, u, v))?;
                let next_i = (j + 1) % adj[u].len();
                v = u;
                i = next_i;
                if (v, i) == (v0, i0) {
                    break;
                }
            }
            faces.push(face);
        }
    }
    Ok(faces)
}

struct Confirmed {
    n_t: usize,
    v_g: usize,
    e_g: usize,
    face_vector: Vec<(usize, i64)>, // (k, p_k) with p_k > 0, sorted by k
    p3: i64,
    p5: i64,
    p6: i64,
    s: i64,
    lhs: i64,
    rhs: i64,
}

fn check_certificate(line: &str) -> Result<Confirmed, String> {
    // ---- 1+2: parse and validate the triangulation T's rotation system ----
    let adj_t = parse_line(line)?;
    let n = adj_t.len();
    let e_t = validate_rotation_system(&adj_t, "T")?;
    if !connected_without(&adj_t, &[]) {
        return Err("T: graph is disconnected".to_string());
    }

    // ---- 3: face-trace T, check planarity (Euler) and that all faces are triangles ----
    let faces_t = trace_faces(&adj_t, "T")?;
    let f_t = faces_t.len();
    let euler_t = n as i64 - e_t as i64 + f_t as i64;
    if euler_t != 2 {
        return Err(format!(
            "T: Euler characteristic V-E+F = {}-{}+{} = {} != 2 (not a planar embedding)",
            n, e_t, f_t, euler_t
        ));
    }
    for face in &faces_t {
        if face.len() != 3 {
            return Err(format!(
                "T: traced face of length {} found; T is not a triangulation",
                face.len()
            ));
        }
    }

    // ---- 4: build the dual G explicitly from the face incidences of T ----
    // face_of[(v,u)] = id of the face whose boundary contains the dart v->u
    let mut face_of: Vec<Vec<usize>> = vec![vec![usize::MAX; n]; n];
    for (fid, face) in faces_t.iter().enumerate() {
        for &(v, u) in face {
            face_of[v][u] = fid;
        }
    }
    // Around the dual vertex f, the dual edges cross the boundary edges of the
    // face f in boundary order, so listing the face on the other side of each
    // boundary dart, in dart order, gives a rotation system for G.
    let mut adj_g: Adj = Vec::with_capacity(f_t);
    for face in &faces_t {
        let mut row = Vec::with_capacity(face.len());
        for &(v, u) in face {
            let g = face_of[u][v]; // face on the other side of edge {v,u}
            if g == usize::MAX {
                return Err("G: internal error: dart without a face".to_string());
            }
            row.push(g);
        }
        adj_g.push(row);
    }
    // Simplicity of G: validate_rotation_system rejects a loop (an edge of T
    // with the same face on both sides) and a multi-edge (two faces of T
    // sharing two edges).
    let e_g = validate_rotation_system(&adj_g, "G")?;
    let v_g = adj_g.len();
    if v_g < 4 {
        return Err(format!("G: only {} vertices; cannot be a 3-polytope graph", v_g));
    }
    for (f, row) in adj_g.iter().enumerate() {
        if row.len() != 3 {
            return Err(format!(
                "G: vertex {} has degree {}; G is not 3-regular",
                f,
                row.len()
            ));
        }
    }
    if !connected_without(&adj_g, &[]) {
        return Err("G: graph is disconnected".to_string());
    }

    // Planarity of G via Euler on its traced faces.
    let faces_g = trace_faces(&adj_g, "G")?;
    let f_g = faces_g.len();
    let euler_g = v_g as i64 - e_g as i64 + f_g as i64;
    if euler_g != 2 {
        return Err(format!(
            "G: Euler characteristic V-E+F = {}-{}+{} = {} != 2 (not a planar embedding)",
            v_g, e_g, f_g, euler_g
        ));
    }

    // ---- 5: 3-connectivity of G by brute force ----
    for x in 0..v_g {
        if !connected_without(&adj_g, &[x]) {
            return Err(format!("G: cut vertex {}; G is not 2-connected", x));
        }
    }
    for x in 0..v_g {
        for y in (x + 1)..v_g {
            if !connected_without(&adj_g, &[x, y]) {
                return Err(format!(
                    "G: {{{}, {}}} is a 2-vertex cut; G is not 3-connected",
                    x, y
                ));
            }
        }
    }

    // ---- 6: face vector of G ----
    let max_k = faces_g.iter().map(|f| f.len()).max().unwrap_or(0);
    let mut p = vec![0i64; max_k + 1];
    for face in &faces_g {
        let k = face.len();
        if k < 3 {
            return Err(format!(
                "G: face of size {} traced; not the boundary complex of a polytope",
                k
            ));
        }
        p[k] += 1;
    }
    let face_vector: Vec<(usize, i64)> = (3..=max_k).filter(|&k| p[k] > 0).map(|k| (k, p[k])).collect();
    let p3 = p[3];
    let p5 = if max_k >= 5 { p[5] } else { 0 };
    let p6 = if max_k >= 6 { p[6] } else { 0 };
    let s: i64 = (7..=max_k).map(|k| p[k]).sum();

    // ---- 7: hypothesis of the conjecture ----
    if s < 3 {
        return Err(format!(
            "hypothesis violated: S = sum_{{k>=7}} pk = {} < 3, conjecture does not apply",
            s
        ));
    }

    // ---- 8: exact integer violation of the conjectured inequality ----
    // Conjecture: p6 >= 39/20 + p3/2 - p5/4 - S.  Multiply by 20:
    // violated iff 20*p6 < 39 + 10*p3 - 5*p5 - 20*S.
    let lhs = 20 * p6;
    let rhs = 39 + 10 * p3 - 5 * p5 - 20 * s;
    if lhs >= rhs {
        return Err(format!(
            "inequality NOT violated: 20*p6 = {} >= {} = 39 + 10*p3 - 5*p5 - 20*S",
            lhs, rhs
        ));
    }

    Ok(Confirmed {
        n_t: n,
        v_g,
        e_g,
        face_vector,
        p3,
        p5,
        p6,
        s,
        lhs,
        rhs,
    })
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: checker_rs <certificate-file>");
        exit(2);
    }
    let content = match fs::read_to_string(&args[1]) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cannot read '{}': {}", args[1], e);
            exit(2);
        }
    };

    let mut checked = 0usize;
    let mut failed = 0usize;
    for (idx, raw) in content.lines().enumerate() {
        let lineno = idx + 1;
        let line = raw.trim();
        if line.is_empty() {
            continue;
        }
        checked += 1;
        match check_certificate(line) {
            Ok(c) => {
                let fv: Vec<String> = c
                    .face_vector
                    .iter()
                    .map(|(k, cnt)| format!("p{}={}", k, cnt))
                    .collect();
                println!(
                    "line {}: COUNTEREXAMPLE CONFIRMED  T: n={}  G=dual(T): V={} E={} F={}  \
                     face vector: {}  S=sum_{{k>=7}} pk={}  \
                     violation: 20*p6 = {} < {} = 39 + 10*p3 - 5*p5 - 20*S  \
                     (p3={}, p5={}, p6={})",
                    lineno,
                    c.n_t,
                    c.v_g,
                    c.e_g,
                    c.face_vector.iter().map(|(_, cnt)| cnt).sum::<i64>(),
                    fv.join(" "),
                    c.s,
                    c.lhs,
                    c.rhs,
                    c.p3,
                    c.p5,
                    c.p6
                );
            }
            Err(reason) => {
                println!("line {}: FAILED: {}", lineno, reason);
                failed += 1;
            }
        }
    }

    if checked == 0 {
        eprintln!("no certificate lines found");
        exit(2);
    }
    if failed > 0 {
        eprintln!(
            "{} of {} certificate(s) FAILED; conjecture refutation NOT confirmed by this run",
            failed, checked
        );
        exit(1);
    }
    println!(
        "All {} certificate(s) confirmed: each is a simple 3-connected planar 3-regular graph \
         (a simple 3-polytope by Steinitz) with S >= 3 violating Conjecture 6.1.",
        checked
    );
}
