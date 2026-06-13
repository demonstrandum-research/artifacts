// Independent Rust verifier (second language, second implementation) for
// exact gamma / Z lower bounds on small graphs.
//
//   rust_check <edgefile> gamma <s>   -- prove NO dominating set of size s
//   rust_check <edgefile> zf <s>      -- prove NO zero forcing set of size s
//   rust_check <edgefile> gammafind <s> / zffind <s> -- find a witness
//
// Edge file: first line "n m", then m lines "u v" (0-based).
// Exhaustive search by DFS over vertex subsets in increasing order with a
// sound monotone pruning rule:
//   - zero forcing closure is monotone: B1 subseteq B2 => cl(B1) subseteq
//     cl(B2). At a DFS node with chosen set P and candidate pool R (all
//     vertices > last chosen), if cl(P u R) != V then no extension of P by
//     vertices of R forces, so the subtree is pruned.
//   - domination coverage is monotone likewise.
// Exit prints "NONE" if no subset of size s achieves the goal (the proved
// lower bound is then s+1), or "WITNESS v1 v2 ..." if one is found.

use std::env;
use std::fs;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Mutex;

#[derive(Clone)]
struct Graph {
    n: usize,
    nbr: Vec<u64>,
    closed: Vec<u64>,
    full: u64,
}

fn closure(g: &Graph, mut blue: u64) -> u64 {
    loop {
        let mut forced: u64 = 0;
        let mut b = blue;
        while b != 0 {
            let v = b.trailing_zeros() as usize;
            b &= b - 1;
            let white = g.nbr[v] & !blue;
            if white != 0 && (white & (white - 1)) == 0 {
                forced |= white;
            }
        }
        if forced == 0 {
            return blue;
        }
        blue |= forced;
    }
}

fn cover(g: &Graph, set: u64) -> u64 {
    let mut c: u64 = 0;
    let mut b = set;
    while b != 0 {
        let v = b.trailing_zeros() as usize;
        b &= b - 1;
        c |= g.closed[v];
    }
    c
}

// returns true if goal achieved by P (as a mask)
fn goal(g: &Graph, p: u64, zf: bool) -> bool {
    if zf {
        closure(g, p) == g.full
    } else {
        cover(g, p) == g.full
    }
}

// optimistic check: can ANY subset of P ∪ pool achieve the goal?
fn optimistic(g: &Graph, p: u64, pool: u64, zf: bool) -> bool {
    if zf {
        closure(g, p | pool) == g.full
    } else {
        cover(g, p | pool) == g.full
    }
}

fn dfs(
    g: &Graph,
    p: u64,
    pcount: usize,
    next: usize,
    s: usize,
    zf: bool,
    found: &AtomicBool,
    witness: &Mutex<Option<u64>>,
) {
    if found.load(Ordering::Relaxed) {
        return;
    }
    if pcount == s {
        if goal(g, p, zf) {
            let mut w = witness.lock().unwrap();
            *w = Some(p);
            found.store(true, Ordering::Relaxed);
        }
        return;
    }
    let remaining = s - pcount;
    if g.n - next < remaining {
        return;
    }
    // pool of all still-choosable vertices
    let pool: u64 = (g.full >> next) << next;
    if !optimistic(g, p, pool, zf) {
        return; // sound monotone pruning
    }
    for v in next..=(g.n - remaining) {
        dfs(g, p | (1u64 << v), pcount + 1, v + 1, s, zf, found, witness);
        if found.load(Ordering::Relaxed) {
            return;
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        eprintln!("usage: rust_check <edgefile> gamma|zf|gammafind|zffind <s>");
        std::process::exit(2);
    }
    let text = fs::read_to_string(&args[1]).expect("read edge file");
    let mut it = text.split_whitespace().map(|t| t.parse::<usize>().unwrap());
    let n = it.next().unwrap();
    let m = it.next().unwrap();
    assert!(n <= 64);
    let mut nbr = vec![0u64; n];
    for _ in 0..m {
        let u = it.next().unwrap();
        let v = it.next().unwrap();
        assert!(u < n && v < n && u != v);
        assert!(nbr[u] >> v & 1 == 0, "duplicate edge");
        nbr[u] |= 1 << v;
        nbr[v] |= 1 << u;
    }
    let closed: Vec<u64> = (0..n).map(|v| nbr[v] | (1u64 << v)).collect();
    let full: u64 = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    let g = Graph { n, nbr, closed, full };

    let mode = args[2].as_str();
    let s: usize = args[3].parse().unwrap();
    let zf = mode == "zf" || mode == "zffind";

    // parallelize over the first two chosen vertices
    let mut starts: Vec<(usize, usize)> = Vec::new();
    for a in 0..n {
        for b in (a + 1)..n {
            starts.push((a, b));
        }
    }
    let found = AtomicBool::new(false);
    let witness: Mutex<Option<u64>> = Mutex::new(None);
    let idx = AtomicUsize::new(0);
    let nthreads = std::thread::available_parallelism()
        .map(|x| x.get())
        .unwrap_or(8);

    if s < 2 {
        // tiny cases: serial
        let mut wit = None;
        if s == 0 {
            if goal(&g, 0, zf) {
                wit = Some(0u64);
            }
        } else {
            for v in 0..n {
                if goal(&g, 1u64 << v, zf) {
                    wit = Some(1u64 << v);
                    break;
                }
            }
        }
        report(wit, n);
        return;
    }

    std::thread::scope(|scope| {
        for _ in 0..nthreads {
            scope.spawn(|| loop {
                let i = idx.fetch_add(1, Ordering::Relaxed);
                if i >= starts.len() || found.load(Ordering::Relaxed) {
                    return;
                }
                let (a, b) = starts[i];
                let p = (1u64 << a) | (1u64 << b);
                dfs(&g, p, 2, b + 1, s, zf, &found, &witness);
            });
        }
    });

    let wit = *witness.lock().unwrap();
    report(wit, n);
}

fn report(wit: Option<u64>, n: usize) {
    match wit {
        None => println!("NONE"),
        Some(w) => {
            let vs: Vec<String> = (0..n)
                .filter(|v| w >> v & 1 == 1)
                .map(|v| v.to_string())
                .collect();
            println!("WITNESS {}", vs.join(" "));
        }
    }
}
