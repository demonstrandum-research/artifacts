// Independent Rust enumerator for the Elizalde-Luo conjecture:
//   #{ nonnesting permutations of {1,1,...,n,n} avoiding 1132 and 3312 }
//     =?= 3^n - 3*2^(n-1) + 1
//
// Conventions (arXiv:2412.00336):
//   - nonnesting word = (Dyck shape) x (label permutation): the i-th closer is
//     matched to the i-th opener, arc i labeled p_i. (This construction is
//     validated exhaustively against the literal 1221/2112-avoidance definition
//     in enumerator.py, V2.)
//   - w contains 1132 iff exists value a (2nd occurrence at q) and q < k < l with
//     w_k > w_l > a; contains 3312 iff exists value c (2nd occurrence at q) and
//     q < k < l with w_k < w_l < c. (Validated against the literal containment
//     definition in enumerator.py, V1.)
//
// Output: rust_results.json (same schema as python_results.json "results").
// Build:  rustc -O enumerator.rs -o enumerator_rs.exe
// Run:    ./enumerator_rs.exe [max_n]      (default 8)

use std::collections::BTreeMap;
use std::env;
use std::fs::File;
use std::io::Write;
use std::sync::Mutex;
use std::thread;

fn dyck_shapes(n: usize) -> Vec<Vec<bool>> {
    let mut out = Vec::new();
    let mut cur = Vec::with_capacity(2 * n);
    fn rec(n: usize, u: usize, d: usize, cur: &mut Vec<bool>, out: &mut Vec<Vec<bool>>) {
        if u == n && d == n {
            out.push(cur.clone());
            return;
        }
        if u < n {
            cur.push(true);
            rec(n, u + 1, d, cur, out);
            cur.pop();
        }
        if d < u {
            cur.push(false);
            rec(n, u, d + 1, cur, out);
            cur.pop();
        }
    }
    rec(n, 0, 0, &mut cur, &mut out);
    out
}

#[derive(Clone)]
struct Stats {
    count: u64,
    nonnesting_total: u64,
    canonical: u64,
    first_letter: Vec<u64>,    // index = value (1..=n)
    pos_of_n: BTreeMap<(usize, usize), u64>,
    descents: Vec<u64>,        // index = #descents (0..2n)
    shapes: BTreeMap<String, u64>,
}

impl Stats {
    fn new(n: usize) -> Stats {
        Stats {
            count: 0,
            nonnesting_total: 0,
            canonical: 0,
            first_letter: vec![0; n + 1],
            pos_of_n: BTreeMap::new(),
            descents: vec![0; 2 * n],
            shapes: BTreeMap::new(),
        }
    }
    fn merge(&mut self, o: &Stats) {
        self.count += o.count;
        self.nonnesting_total += o.nonnesting_total;
        self.canonical += o.canonical;
        for i in 0..self.first_letter.len() {
            self.first_letter[i] += o.first_letter[i];
        }
        for (k, v) in &o.pos_of_n {
            *self.pos_of_n.entry(*k).or_insert(0) += v;
        }
        for i in 0..self.descents.len() {
            self.descents[i] += o.descents[i];
        }
        for (k, v) in &o.shapes {
            *self.shapes.entry(k.clone()).or_insert(0) += v;
        }
    }
}

fn contains_1132(w: &[u8], p: &[u8], cpos: &[usize]) -> bool {
    let n = p.len();
    let len = w.len();
    for i in 0..n {
        let a = p[i];
        let q = cpos[i];
        let mut mx: u8 = 0;
        for t in (q + 1)..len {
            let v = w[t];
            if v > a {
                if v < mx {
                    return true;
                }
                if v > mx {
                    mx = v;
                }
            }
        }
    }
    false
}

fn contains_3312(w: &[u8], p: &[u8], cpos: &[usize]) -> bool {
    let n = p.len();
    let len = w.len();
    for i in 0..n {
        let c = p[i];
        let q = cpos[i];
        let mut mn: u8 = u8::MAX;
        for t in (q + 1)..len {
            let v = w[t];
            if v < c {
                if v > mn {
                    return true;
                }
                if v < mn {
                    mn = v;
                }
            }
        }
    }
    false
}

fn process_shape(n: usize, shape: &[bool], stats: &mut Stats) {
    let mut opos = Vec::with_capacity(n);
    let mut cpos = Vec::with_capacity(n);
    for (i, &st) in shape.iter().enumerate() {
        if st {
            opos.push(i);
        } else {
            cpos.push(i);
        }
    }
    let sstr: String = shape.iter().map(|&s| if s { 'U' } else { 'D' }).collect();

    // iterate all permutations of [1..n] via Heap's algorithm
    let mut p: Vec<u8> = (1..=(n as u8)).collect();
    let mut c = vec![0usize; n];
    let mut w = vec![0u8; 2 * n];

    let mut handle = |p: &[u8], stats: &mut Stats| {
        stats.nonnesting_total += 1;
        for i in 0..n {
            w[opos[i]] = p[i];
            w[cpos[i]] = p[i];
        }
        if contains_1132(&w, p, &cpos) || contains_3312(&w, p, &cpos) {
            return;
        }
        stats.count += 1;
        stats.first_letter[w[0] as usize] += 1;
        let i_n = p.iter().position(|&x| x == n as u8).unwrap();
        *stats
            .pos_of_n
            .entry((opos[i_n] + 1, cpos[i_n] + 1))
            .or_insert(0) += 1;
        let d = (0..2 * n - 1).filter(|&i| w[i] > w[i + 1]).count();
        stats.descents[d] += 1;
        *stats.shapes.entry(sstr.clone()).or_insert(0) += 1;
        if p.iter().enumerate().all(|(i, &x)| x == (i + 1) as u8) {
            stats.canonical += 1;
        }
    };

    handle(&p, stats);
    let mut i = 0;
    while i < n {
        if c[i] < i {
            if i % 2 == 0 {
                p.swap(0, i);
            } else {
                p.swap(c[i], i);
            }
            handle(&p, stats);
            c[i] += 1;
            i = 0;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
}

fn enumerate_n(n: usize, nthreads: usize) -> Stats {
    let shapes = dyck_shapes(n);
    let global = Mutex::new(Stats::new(n));
    let next = std::sync::atomic::AtomicUsize::new(0);
    thread::scope(|s| {
        for _ in 0..nthreads {
            s.spawn(|| {
                let mut local = Stats::new(n);
                loop {
                    let idx = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    if idx >= shapes.len() {
                        break;
                    }
                    process_shape(n, &shapes[idx], &mut local);
                }
                global.lock().unwrap().merge(&local);
            });
        }
    });
    global.into_inner().unwrap()
}

fn factorial(n: usize) -> u64 {
    (1..=n as u64).product()
}

fn json_escape_free_map<K: std::fmt::Display>(m: &BTreeMap<K, u64>) -> String {
    let items: Vec<String> = m.iter().map(|(k, v)| format!("\"{}\": {}", k, v)).collect();
    format!("{{{}}}", items.join(", "))
}

fn main() {
    let max_n: usize = env::args().nth(1).and_then(|a| a.parse().ok()).unwrap_or(8);
    let nthreads = thread::available_parallelism().map(|x| x.get()).unwrap_or(8);
    let mut blocks: Vec<String> = Vec::new();

    for n in 1..=max_n {
        let t0 = std::time::Instant::now();
        let st = enumerate_n(n, nthreads);
        let formula: i64 = 3i64.pow(n as u32) - 3 * 2i64.pow(n as u32 - 1) + 1;
        let matches = st.count as i64 == formula;
        eprintln!(
            "n={}: nonnesting={} avoiders={} formula={} match={} canonical={} [{:?}]",
            n, st.nonnesting_total, st.count, formula, matches, st.canonical,
            t0.elapsed()
        );

        let fl: BTreeMap<usize, u64> = (1..=n)
            .filter(|&v| st.first_letter[v] > 0)
            .map(|v| (v, st.first_letter[v]))
            .collect();
        let posn: BTreeMap<String, u64> = st
            .pos_of_n
            .iter()
            .map(|(&(i, j), &v)| (format!("{},{}", i, j), v))
            .collect();
        let desc: BTreeMap<usize, u64> = st
            .descents
            .iter()
            .enumerate()
            .filter(|(_, &v)| v > 0)
            .map(|(d, &v)| (d, v))
            .collect();

        // NOTE: posn keys like "3,8" sort as strings here, but the comparison
        // script parses JSON into dicts, so ordering is immaterial.
        blocks.push(format!(
            " {{\n  \"n\": {},\n  \"nonnesting_total\": {},\n  \"avoider_count\": {},\n  \"formula_value\": {},\n  \"formula_matches\": {},\n  \"canonical_label_avoiders\": {},\n  \"canonical_times_factorial\": {},\n  \"stats\": {{\n   \"by_first_letter\": {},\n   \"by_positions_of_n\": {},\n   \"by_descents\": {},\n   \"by_dyck_shape\": {}\n  }}\n }}",
            n,
            st.nonnesting_total,
            st.count,
            formula,
            matches,
            st.canonical,
            st.canonical * factorial(n),
            json_escape_free_map(&fl),
            json_escape_free_map(&posn),
            json_escape_free_map(&desc),
            json_escape_free_map(&st.shapes),
        ));
    }

    let out = format!(
        "{{\n\"description\": \"Rust independent enumeration, Elizalde-Luo {{1132,3312}} nonnesting avoiders\",\n\"results\": [\n{}\n]\n}}\n",
        blocks.join(",\n")
    );
    let mut f = File::create("rust_results.json").expect("create file");
    f.write_all(out.as_bytes()).expect("write");
    println!("wrote rust_results.json");
}
