# Reading kit — a machine-checked four-color strong-majority theorem for 4-regular graphs

A self-checking one-page guide to the kernel-clean theorem `Rung4Moonshot.R4_four_regular`.
It contains: (1) the theorem exactly as the Lean kernel sees it; (2) an English gloss of
every definition it depends on, down to mathlib bedrock — a reader with no Lean should
understand what was proved; (3) the bridge from the source result (KKPW Proposition 21)
to our formal statement, stating exactly where they differ; (4) the axiom-audit output;
(5) the one command that rebuilds and re-audits everything.

You do **not** have to trust this document. Section 4's audit output is printed by the
build, and the rebuild command in Section 5 reproduces it from source. Provenance,
hashes, and the full double-confirmation are in `CONFIRM-R4FOURREG.md`.

**Calibration (BINDING — see `KILL-CHECK-R4.md`).** The *mathematical statement* proved
here is **known**: every 4-regular graph has even degrees, so KKPW Proposition 21 already
gives Maj′(G) ≤ 4 (one-paragraph Euler-tour argument). Our contribution is the **first
machine-checked (Lean/kernel) proof of a strong-majority bound of four for a nontrivial
graph class**, delivered by a *different argument* (capacitated-Hall defect avoidance, not
an Euler tour). Nothing here claims the mathematics was open, and nothing here is a first
*proof* for 4-regular graphs. See Section 3 for the exact scope and the forbidden wordings.

---

## 1. The theorem, as stated in Lean

From `constructive_route/Pins2.lean` (line ~3447), verbatim, with the file-level
variables `variable {V : Type*} [Fintype V] [DecidableEq V]` (line 28):

```lean
theorem R4_four_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c
```

`V` is a finite vertex type with decidable equality; `G : SimpleGraph V` is a simple graph
with decidable adjacency; `hreg` says every vertex has degree exactly 4. In words:
**every finite simple 4-regular graph admits a coloring of its edges by four colors that
is strong majority** (Maj′(G) ≤ 4). The empty-vertex case is handled explicitly by the
constant coloring, so the theorem is non-vacuous. The full printed name is
`Rung4Moonshot.R4_four_regular`.

---

## 2. Every definition, down to mathlib bedrock

The statement rests on the frozen base definitions in
`papers/rung5-five-colors/artifact/lean/Maj5Base.lean` (namespace `SMaj`; file-level
`variable (G : SimpleGraph V) [DecidableRel G.Adj]`, `variable {C : Type*} [DecidableEq C]`),
verbatim:

```lean
def side (u v : V) : Finset (Sym2 V) := (G.incidenceFinset u).erase s(u, v)

def row (u v : V) : Finset (Sym2 V) := side G u v ∪ side G v u

def nColor (c : Sym2 V → C) (u v : V) (α : C) : ℕ :=
  #{f ∈ row G u v | c f = α}

def IsStrongMajority (c : Sym2 V → C) : Prop :=
  ∀ u v, G.Adj u v → ∀ α : C, nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2
```

Glossed to bedrock, each term named is a mathlib definition unless noted:

- **`SimpleGraph V`** (mathlib): an irreflexive symmetric adjacency relation `Adj` on `V`.
  Its edges are elements of `Sym2 V`.
- **`Sym2 V`** (mathlib): the type of unordered pairs from `V`; `s(u, v)` is the unordered
  pair `{u, v}`. An edge of `G` is such a pair with `G.Adj u v`.
- **`Fin 4`** (mathlib): the four-element type — the palette "four colors". A coloring is a
  *total* function `c : Sym2 V → Fin 4`; its values on non-edges never matter because
  `row` contains only genuine edges.
- **`G.degree u`** (mathlib): the number of neighbours of `u`, i.e.
  `(G.neighborFinset u).card`. The hypothesis `hreg : ∀ v, G.degree v = 4` is 4-regularity.
- **`G.incidenceFinset u`** (mathlib): the finite set of edges of `G` containing `u` —
  every `s(u, w)` with `G.Adj u w`.
- **`Finset.erase`** and **`∪`** (mathlib): set-minus-one-element and union on `Finset`. So
  **`side G u v`** is "the edges at `u`, except the edge `s(u,v)` itself", and
  **`row G u v`** is "all edges sharing an endpoint with `s(u,v)`, that edge excluded" —
  the *adjacent* edges. (`Maj5Base` theorem `card_row` certifies `#(row G u v) =
  d(u)+d(v)−2`, the paper's line-degree d_L(e).)
- **`#{f ∈ s | p f}`** is `Finset.card` of the filtered finset. So **`nColor G c u v α`**
  is the number of adjacent edges carrying color `α`.
- **`(G.degree u + G.degree v - 2) / 2`** is Lean `ℕ` arithmetic: `-` is truncated
  subtraction (harmless — an edge's endpoint degrees sum to ≥ 2) and `/` is floor
  division. This is `⌊(d(u)+d(v)−2)/2⌋`, i.e. ⌊|row|/2⌋ = "at most half of the adjacent
  edges".
- **`IsStrongMajority G c`**: for every edge `uv` and *every* color `α` (the quantifier
  includes `α = c(uv)`, as the source definition requires), the number of adjacent
  `α`-edges is at most that floor threshold.

For a 4-regular graph the threshold on every edge is `⌊(4+4−2)/2⌋ = 3`: no color may
appear on more than 3 of an edge's 6 adjacent edges.

**Executable sanity of the definitions.** `Pins2.lean` and `Maj5Base.lean` carry **no**
`#eval`/`decide` demos of `nColor`/`row`/`IsStrongMajority` on tiny graphs, but a companion
witness file does: **`constructive_route/Demos.lean`** (imports only the frozen `Maj5Base`;
no theorems, axioms, or `sorry`; not imported by `Pins2.lean`, so deleting it cannot affect
the theorem). It computes all four definitions on the smallest 4-regular graph `K5` and on
the triangle `K3`: degrees (`K5.degree 0` prints `4` — 4-regular), `#eval (SMaj.side K5 0 1).card`
(`3`), `#eval (SMaj.row K5 0 1).card` (`6`), the cap surfacing as `#eval (K5.degree 0 + K5.degree 1 - 2)/2`
(`3 = ⌊(4+4−2)/2⌋`), `nColor` under both the all-0 coloring (`6`) and an explicit strong-majority
coloring `cK5 = (i+j) mod 4`, and `IsStrongMajority` itself checked by `decide` — printing
`true` on `cK5`/`K5` (a concrete four-coloring meeting the cap on a 4-regular graph, exactly
what `R4_four_regular` asserts) and `false` on the all-0 coloring (the predicate genuinely
rejects bad colorings), with the matching `K3` example/non-example. These mirror the five-color
artifact's reading-kit demos (`papers/rung5-five-colors/artifact/READING-KIT.md`, Section 2)
on the byte-identical frozen definitions (see `CONFIRM-R4FOURREG.md` §1: `IsStrongMajority`
line-slice sha256 `da728245…`, whole-file sha256 identical). One command re-checks every
printed value against the built libraries:

```
cd C:\t\r4cdx && lake env lean Demos.lean     # prints, in order: 4 4 2 3 6 3 2 1 6 2 1 true false true false ; exit 0
```

Each `#eval` in `Demos.lean` carries its expected value in a trailing comment, so the file
self-documents; `decide` over `K5` (25 vertex pairs × 4 colors) is fully tractable — no
timeout, no `native_decide`.

---

## 3. Bridge: source result (KKPW Prop 21) → our formal statement

**Source, quoted verbatim** (from `KILL-CHECK-R4.md`, pulled from the arXiv HTML full
text of Kalinowski, Kamyczura, Pilśniak, Woźniak, *Strong majority colorings of graphs*,
arXiv:2605.23828):

> **Proposition 21.** If all vertices of a graph G have even degrees, then Maj′(G) ≤ 4.
> Moreover, if G is connected and the size of G satisfies ‖G‖ ≡ 0 mod 3, then Maj′(G) ≤ 3.

with the regular-graph remark (verbatim):

> Maj′(G) ≤ 4 for r ∈ {3,6} by Proposition 15, and **for r ∈ {4,8} by Proposition 21**.

**Correspondence.**

| KKPW Prop 21 (4-regular instance) | Lean `R4_four_regular` |
|---|---|
| "G … all vertices even degree", specialized to 4-regular | `hreg : ∀ v, G.degree v = 4` |
| "Maj′(G) ≤ 4" | `∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c` |
| "at most half the edges adjacent to e have color i" | `nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2` |

**Where they differ — stated plainly.**

1. **Scope.** Proposition 21 covers *all even-degree* graphs (degrees 2, 4, 6, 8, …). We
   formalize **only the 4-regular slice** (`∀ v, degree v = 4`). The theorem here is a
   proper special case of Prop 21's statement, not the full proposition.
2. **Argument.** Prop 21's proof is a one-paragraph Euler tour colored periodically
   `1,2,3,1,2,3,…` with color 4 on the ≤2 leftover edges. Our proof takes a *different
   route*: an edge split into two max-degree-2 subgraphs (`exists_edge_split_pin`), then
   capacitated-Hall defect avoidance (`Avoid.avoidance_core`, mathlib
   `Finset.all_card_le_biUnion_card_iff_existsInjective'`) placing one defect per odd
   cycle so that no color exceeds cap 3 on any edge. For 4-regular graphs every vertex is
   "clean" (`cap_eq_three_iff`), so no minimality/descent/connectivity is needed — the
   route recovers Prop 21's 4-regular case without special-casing.
3. **What is new here is the *machine check*, not the mathematics.** The bound Maj′ ≤ 4
   for 4-regular graphs is due to KKPW. What did not exist before is a kernel-verified
   proof of it: `R4_four_regular` is (to our knowledge, per the `KILL-CHECK-R4.md`
   literature sweep) the first machine-checked strong-majority bound of four for any
   nontrivial class.

**Forbidden wordings** (from `KILL-CHECK-R4.md`, obeyed throughout this kit): NOT "first
proof that 4-regular graphs satisfy Maj′ ≤ 4"; NOT "first infinite class/family"; NOT
"resolves/advances Conjecture 14 for regular graphs"; nothing implying degrees-{3,4} was
wholly open (only the *mixed* degree-3-and-4 slice is open, and that is a *separate,
conditional* theorem — `R4_three_four` — not this one).

---

## 4. Axiom audit (verbatim from `CONFIRM-R4FOURREG.md` §3)

Fresh isolated harness `C:\t\r4final`, target commit `420ba1e`, Lean v4.28.0, mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Per-declaration `#print axioms`
(`AuditR4Final.lean`) — flagship plus stated chain, all EXACTLY the standard triple, no
`sorryAx`:

```
'Rung4Moonshot.R4_four_regular'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.exists_edge_split_pin'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.Avoid.avoidance_core'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.placement_of_clean_transversal' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.strongMajority_of_safe_defects' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Audit-machinery control** (proves `#print axioms` here really detects `sorryAx`): the
file's one open-crux lemma is correctly flagged, and `R4_four_regular` provably does NOT
route through it:

```
'Rung4Moonshot.strict_descent_of_no_clean_transversal'
    depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

That lemma (`Pins2.lean:2932`, sorry token at line 2949) is the file's only `sorry` and
belongs to the *conditional* mixed-degree route (`R4_three_four`), not to
`R4_four_regular`, which runs a parallel clean-vertex chain. `Maj5Base.lean` has zero
`sorry`. Subversion scan (§6 of the confirmation): no `axiom`, `native_decide`,
`implemented_by`/`extern`/`opaque`/`unsafe`, `macro`/`elab`, or `reduceBool`/`ofReduceBool`
anywhere; `set_option` only sets `autoImplicit false` and `maxHeartbeats`.

---

## 5. One command that rebuilds + re-audits (do not run — copy from `CONFIRM-R4FOURREG.md` §7)

```
mkdir C:\t\r4final && cd C:\t\r4final
# lakefile.toml (mathlib rev 8f9d9cff…, libs Maj5Base + Pins2 + AuditR4Final),
# lean-toolchain v4.28.0, lake-manifest.json copied from a built r4* harness
git show 420ba1e:papers/rung5-five-colors/artifact/lean/Maj5Base.lean > Maj5Base.lean
git show 420ba1e:problems/p5-strongmajority/rung4-moonshot/constructive_route/Pins2.lean > Pins2.lean
mklink /J .lake\packages <built-harness>\.lake\packages     # immutable mathlib cache only
lake build Pins2            # green, 8028 jobs
lake build AuditR4Final     # emits the #print axioms lines in Section 4
```

`lake build Pins2` is green (exit 0, 8028 jobs; `Built Maj5Base`, `Built Pins2`) with only
linter warnings and the single expected `declaration uses sorry` at `Pins2.lean:2932`.
`lake build AuditR4Final` prints the Section 4 lines. Toolchain and provenance hashes:
`CONFIRM-R4FOURREG.md` §1.

---

# Reading-kit addendum — the unconditional t ≤ 2 degree-{3,4} theorem

A self-checking guide to the kernel-checked theorem
`Rung4Moonshot.R4_three_four_t2`. This addendum uses the same five-part format as
the 4-regular reading kit above: exact Lean statement, definitions and proof route,
axiom audit, scope, and a single clean rebuild-plus-re-audit invocation.

**Calibration (BINDING).** This theorem covers the slice with at most two degree-3
vertices, not the full mixed degree-{3,4} class. The general case with arbitrarily many
degree-3 vertices remains open. The two release theorems `R4_three_four_t2` and
`R4_four_regular` are, to our knowledge, the first machine-checked proofs of a
strong-majority bound of **four**; `R4_three_four_t2` is also, to our knowledge, the
first bound-4 theorem covering any part of the mixed class. The earlier E5 result is
our prior machine-checked strong-majority result, at five colors.

## 1. The theorem, as stated in Lean

From `constructive_route/Pins3.lean` (line ~10624), verbatim, with the file-level
variables `variable {V : Type*} [Fintype V] [DecidableEq V]` (line 28):

```lean
theorem R4_three_four_t2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v = 3 ∨ G.degree v = 4)
    (ht2 : numDeg3 G ≤ 2) :
    ∃ c : Sym2 V → Fin 4, SMaj.IsStrongMajority G c
```

`V` is a finite vertex type with decidable equality; `G : SimpleGraph V` is a simple
graph with decidable adjacency; `hdeg` says every vertex has degree 3 or 4; and `ht2`
says at most two vertices have degree 3. In words: **every finite simple graph whose
degrees lie in `{3,4}` and which has at most two degree-3 vertices admits a strong-majority
edge-coloring with four colors**. The full printed name is
`Rung4Moonshot.R4_three_four_t2`.

## 2. `numDeg3`, down to mathlib bedrock, and the migration proof

The count is defined in `constructive_route/Pins2.lean` and imported by `Pins3.lean`,
verbatim:

```lean
def numDeg3 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v : V => G.degree v = 3)).card
```

Glossed to bedrock: `Fintype V` makes all vertices available as the finite set
`Finset.univ`; `Finset.filter` retains exactly those vertices satisfying
`G.degree v = 3`; `G.degree v` is the cardinality of the mathlib neighbour finset of
`v`; and `.card` counts the retained vertices. Thus `numDeg3 G` is literally the
number of degree-3 vertices, and `numDeg3 G ≤ 2` is the stated at-most-two condition.
The roles of `SimpleGraph`, `DecidableRel`, `Sym2`, `Fin 4`, and
`SMaj.IsStrongMajority` are exactly as glossed in Section 2 of the main kit above.

**Proof story.** For a connected graph, `exists_oddCycleMinimal_split` supplies an
existentially chosen `IsOddCycleMinimalSplit`. If an odd-cycle support is poisoned,
`migration_step` analyzes its canonical toggle. The even branch would strictly lower
the odd-cycle objective and so contradict minimality. In the odd branch the objective
cannot rise on either half; minimality therefore forces Δω = 0, leaving another minimal
split, while `mig_unpoisons` proves that the toggled split has a clean vertex on every
odd support in both cross-directions. This is the poison-exit mechanism: it exits poison
without descending the objective. Because at most one ordered half can have the poisoned
shape, `migration_descent` needs at most one such step. Then
`migration_safe_split_placement_t2` applies `nonbip_void_t2` and
`placement_of_clean_transversal` in both directions to obtain the safe defect placements
consumed by `strongMajority_of_safe_defects`; `R4_three_four_connected_t2` assembles the
four-coloring, and `R4_three_four_t2` lifts it over connected components using
`numDeg3_induce_le`.

## 3. Axiom audit

Fresh isolated Modal-farm rebuild at the release bytes (clean container, warm
pinned mathlib cache; repo HEAD `6c7f364`, Pins3 unchanged since the kernel-check
commit `121821a`; Modal call `fc-01KXEC3Z42KZZGRX2J5SD5V5MR`, `Build completed
successfully (8029 jobs)`, exit 0). Per-declaration `#print axioms` for the flagship
theorem and its full migration cone — every line is EXACTLY the standard triple, no
`sorryAx`:

```
'Rung4Moonshot.R4_three_four_t2'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.R4_three_four_connected_t2'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.migration_safe_split_placement_t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.mig_unpoisons'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.navchar_of_blocked'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.exists_alternating_euler_trail'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

(The companion `Rung4Moonshot.R4_four_regular` audits to the same triple in the same
build — see the 4-regular kit above.)

## 4. Scope

**Binding scope sentence:** `R4_three_four_t2` covers graphs with at most two degree-3
vertices; the general mixed degree-{3,4} case with arbitrarily many degree-3 vertices
remains open. This theorem is a slice of the mixed class, not “the mixed class.”

## 5. One command that rebuilds + re-audits (do not run here)

From the repository root in PowerShell, this sends the complete source chain to the
isolated pinned Modal harness, builds `Pins3`, and prints the theorem's axiom line:

```powershell
python .\problems\p5-strongmajority\rung4-kernel\scripts\modal_farm\submit_build.py `
  --file .\papers\rung5-five-colors\artifact\lean\Maj5Base.lean `
  --file .\problems\p5-strongmajority\rung4-moonshot\constructive_route\Pins2.lean `
  --file .\problems\p5-strongmajority\rung4-moonshot\constructive_route\Pins3.lean `
  --target Pins3 `
  --decl Rung4Moonshot.R4_three_four_t2
```

Each uploaded basename is already the required project filename, so no `--as` option is
used. The farm is pinned to Lean v4.28.0 and mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
