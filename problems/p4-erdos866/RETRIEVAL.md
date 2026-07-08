# Retrieving the 866 SAT certificate archive (DRAT/LRAT proofs)

The full certificate archive for the 298-cell exact-value set — one
directory per nontrivial cell containing the CNF, the gzipped DRAT and LRAT
proofs, and the per-cell verification log (273 cells, ~4.4 GB) — is **not**
stored in this git repository.

Where to get it:

1. **Zenodo (primary, citable):** the archived release
   [10.5281/zenodo.21269439](https://doi.org/10.5281/zenodo.21269439)
   contains `erdos866-sat-certificates.zip` — the complete `cells/` tree
   plus the pinned `manifest.json`, exactly as inventoried here.
2. **On request:** erlbacher.research@gmail.com — any individual cell or the
   full archive.

Integrity: every CNF/DRAT/LRAT file's sha256 is listed per cell in
[`sat/manifest.json`](sat/manifest.json) (273 VERIFIED + 25 TRIVIAL_M_EQ_N
entries), and that manifest's own sha256
(`45f0eedccfa5e22636108f633cde6c1c28f139d06446d92be6a09858bfc1400e`) is
pinned in [`release/2026-07-08-freeze/FREEZE.md`](release/2026-07-08-freeze/FREEZE.md),
which was frozen under the git tag `866-freeze-2026-07-08` of the internal
working tree before anything was published. Verify a downloaded archive
against the manifest before trusting any cell.

Re-checking a cell: `<cell>/check.log` records the original dual-engine +
cake_lpr run; to re-verify, decompress the `.drat.gz`/`.lrat.gz` and run
cake_lpr (formally verified LRAT checker) or drat-trim on the CNF. The
archive builder and its semantic cross-check / mutation-test harnesses are
in [`sat/`](sat/).
