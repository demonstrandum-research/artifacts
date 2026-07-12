#!/bin/sh
# One command that rebuilds the whole chain and re-prints the axiom audit.
# Requires elan/lake; the pinned toolchain (lean-toolchain) is fetched
# automatically. Building mathlib from source the first time is slow; use
# `lake exe cache get` first if you want prebuilt mathlib oleans.
set -e
cd "$(dirname "$0")"

# Build the theorem. Rung5Lam5 ends with `#print axioms
# SMaj.Synthesis.maj_le_five`, so a successful build already prints the
# footprint of the headline theorem.
lake build Rung5Lam5

# Re-print the per-layer audit (headline theorem + every named layer).
lake env lean audit_final_gateS.lean
