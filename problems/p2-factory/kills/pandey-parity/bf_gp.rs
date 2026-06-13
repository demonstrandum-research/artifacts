// Independent brute-force cross-check for the Pandey parity-conjecture kill.
// Written from scratch (no shared code with the Python checker beyond the
// published Definition 2.1 of GP(n,k)).
//
// For every legal pair (n,k) with 3 <= n <= 14, 1 <= k < n/2, enumerate ALL
// 2^(2n) vertex subsets of GP(n,k) and count independent sets by size, via
// the subset DP:  indep[S] = indep[S \ {v}] && (N(v) & (S \ {v})) == 0,
// v = lowest set bit of S.  Exact u128/u64 integer arithmetic only.
//
// Vertex numbering: u_i -> i, v_i -> n+i  (0 <= i < n)  -- deliberately a
// DIFFERENT numbering from the Python checker's interleaved one; the
// polynomial must agree anyway.
//
// Output: lines "GP(n,k): [i_0, i_1, ...]"
//
// Build: rustc -O bf_gp.rs    Run: ./bf_gp

fn main() {
    for n in 3usize..=14 {
        for k in 1usize..=(n - 1) / 2 {
            let nv = 2 * n;
            let mut adj = vec![0u32; nv];
            let mut add = |a: usize, b: usize, adj: &mut Vec<u32>| {
                adj[a] |= 1 << b;
                adj[b] |= 1 << a;
            };
            for i in 0..n {
                add(i, (i + 1) % n, &mut adj); // outer cycle u_i u_{i+1}
                add(n + i, n + (i + k) % n, &mut adj); // inner chords v_i v_{i+k}
                add(i, n + i, &mut adj); // spokes u_i v_i
            }
            // sanity: 3-regular, 3n edges
            let mut deg_sum = 0usize;
            for v in 0..nv {
                assert_eq!(adj[v].count_ones(), 3, "GP({},{}) not cubic", n, k);
                deg_sum += adj[v].count_ones() as usize;
            }
            assert_eq!(deg_sum, 6 * n);

            let total: usize = 1usize << nv;
            let mut indep = vec![false; total];
            indep[0] = true;
            let mut counts = vec![0u64; nv + 1];
            counts[0] = 1;
            for s in 1..total {
                let v = s.trailing_zeros() as usize;
                let rest = s & (s - 1);
                if indep[rest] && (adj[v] as usize & rest) == 0 {
                    indep[s] = true;
                    counts[s.count_ones() as usize] += 1;
                }
            }
            while counts.len() > 1 && *counts.last().unwrap() == 0 {
                counts.pop();
            }
            let strs: Vec<String> = counts.iter().map(|c| c.to_string()).collect();
            println!("GP({},{}): [{}]", n, k, strs.join(", "));
        }
    }
}
