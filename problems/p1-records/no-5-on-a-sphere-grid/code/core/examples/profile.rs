//! Phase profiler: remove vs add vs raw cofactor cost at |S| = 33.
use no5core::*;
use std::time::Instant;

fn main() {
    let path = std::env::args().nth(1).expect("usage: profile <points.json>");
    let text = std::fs::read_to_string(&path).unwrap();
    let mut nums: Vec<i32> = Vec::new();
    let mut cur = String::new();
    for ch in text.chars() {
        if ch.is_ascii_digit() || ch == '-' {
            cur.push(ch);
        } else if !cur.is_empty() {
            nums.push(cur.parse().unwrap());
            cur.clear();
        }
    }
    let pts: Vec<Point> = nums.chunks(3).map(|c| [c[0], c[1], c[2]]).collect();
    println!("|S| = {}", pts.len());

    let mut st = SearchState::from_points(&pts);
    let iters = 400usize;
    let (mut t_rem, mut t_add) = (0.0f64, 0.0f64);
    for it in 0..iters {
        let p = pts[it % pts.len()];
        let t0 = Instant::now();
        st.remove_point(p);
        t_rem += t0.elapsed().as_secs_f64();
        let t1 = Instant::now();
        st.add_point(p);
        t_add += t1.elapsed().as_secs_f64();
    }
    println!(
        "remove: {:.3} ms/op   add: {:.3} ms/op",
        t_rem / iters as f64 * 1e3,
        t_add / iters as f64 * 1e3
    );

    // raw cofactor cost over all C(33,4) quadruples
    let m = pts.len();
    let t0 = Instant::now();
    let mut acc = 0i64;
    let mut count = 0u64;
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let cv = cofactor_vec(&[pts[a], pts[b], pts[c], pts[d]]);
                    acc ^= cv[0] ^ cv[4];
                    count += 1;
                }
            }
        }
    }
    let el = t0.elapsed().as_secs_f64();
    println!(
        "cofactor_vec: {} quads in {:.3} ms = {:.1} ns/quad (acc {})",
        count,
        el * 1e3,
        el / count as f64 * 1e9,
        acc
    );

    // standalone scan replica (same algorithm as SearchState::scan_zero_cells)
    let mut out: Vec<u16> = Vec::with_capacity(64);
    let mut total_hits = 0u64;
    let t0 = Instant::now();
    let mut count2 = 0u64;
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let cv = cofactor_vec(&[pts[a], pts[b], pts[c], pts[d]]);
                    let cc = [cv[0] as i32, cv[1] as i32, cv[2] as i32, cv[3] as i32, cv[4] as i32];
                    out.clear();
                    scan_replica(cc, &mut out);
                    total_hits += out.len() as u64;
                    count2 += 1;
                }
            }
        }
    }
    let el = t0.elapsed().as_secs_f64();
    println!(
        "cofactor+scan(replica): {} quads in {:.3} ms = {:.1} ns/quad, avg hits/quad = {:.2}",
        count2,
        el * 1e3,
        el / count2 as f64 * 1e9,
        total_hits as f64 / count2 as f64
    );

    // the PRODUCTION scan path (whatever cfg selected: AVX2 or scalar)
    let mut st2 = SearchState::new();
    let mut out2: Vec<u16> = Vec::with_capacity(256);
    let mut hits3 = 0u64;
    let t0 = Instant::now();
    let mut count3 = 0u64;
    for a in 0..m {
        for b in a + 1..m {
            for c in b + 1..m {
                for d in c + 1..m {
                    let cv = cofactor_vec(&[pts[a], pts[b], pts[c], pts[d]]);
                    out2.clear();
                    st2.profile_scan(cv, &mut out2);
                    hits3 += out2.len() as u64;
                    count3 += 1;
                }
            }
        }
    }
    let el = t0.elapsed().as_secs_f64();
    println!(
        "cofactor+scan(production): {} quads in {:.3} ms = {:.1} ns/quad, avg hits/quad = {:.2}",
        count3,
        el * 1e3,
        el / count3 as f64 * 1e9,
        hits3 as f64 / count3 as f64
    );
}

#[inline(never)]
fn scan_replica(c: [i32; 5], out: &mut Vec<u16>) {
    let (c0, c1, c2, c3, c4) = (c[0], c[1], c[2], c[3], c[4]);
    let mut tz = [0i32; 13];
    let mut ty = [0i32; 13];
    let (mut tzmin, mut tzmax) = (i32::MAX, i32::MIN);
    for v in 0..13i32 {
        let t = c2 * v + c3 * v * v;
        tz[v as usize] = t;
        tzmin = tzmin.min(t);
        tzmax = tzmax.max(t);
        ty[v as usize] = c1 * v + c3 * v * v;
    }
    let mut idx = 0u16;
    for x in 0..13i32 {
        let gx = c0 * x + c3 * x * x + c4;
        for y in 0..13usize {
            let base = gx + ty[y];
            if base + tzmax >= 0 && base + tzmin <= 0 {
                let mut any = 0u32;
                for z in 0..13usize {
                    any |= ((base + tz[z]) == 0) as u32;
                }
                if any != 0 {
                    for z in 0..13usize {
                        if base + tz[z] == 0 {
                            out.push(idx + z as u16);
                        }
                    }
                }
            }
            idx += 13;
        }
    }
}
