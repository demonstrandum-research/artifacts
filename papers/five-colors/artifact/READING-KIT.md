# Reading kit — Strong Majority Edge-Coloring with Five Colors

A self-checking one-page guide to the machine-checked theorem in this artifact.
It contains: (1) the theorem exactly as the Lean kernel sees it; (2) an English
gloss of every definition it depends on, down to mathlib bedrock; (3) the bridge
from the source paper's Theorem 2 to our formal statement; (4) the axiom-audit
output; (5) the single command that rebuilds and re-audits everything.

You do **not** have to trust this document. Everything below is either printed by
the build (Sections 4–5) or checkable by the small `#eval`/`decide` demos in
Section 2.

---

## 1. The theorem, as stated in Lean

From `lean/Rung5Lam5.lean` (the final file), verbatim:

```lean
theorem maj_le_five (G : SimpleGraph V) [DecidableRel G.Adj]
    (hadm : Admissible G) :
    ∃ c : Sym2 V → Fin 5, IsStrongMajority G c
```

`V` is a finite vertex type with decidable equality (`[Fintype V] [DecidableEq V]`,
declared as file-level variables); `G : SimpleGraph V` is a simple graph with
decidable adjacency. In words: **every admissible graph admits a coloring of its
edges by five colors that is strong majority.** The full names printed by the
audit are `SMaj.Synthesis.maj_le_five` (this statement) and its Λ4 prerequisite
`SMaj.exists_isGlueColoring_five`.

---

## 2. Every definition, down to mathlib bedrock

The four definitions the statement rests on, verbatim from `lean/Maj5Base.lean`
(file-level: `variable (G : SimpleGraph V) [DecidableRel G.Adj]`,
`variable {C : Type*} [DecidableEq C]`):

```lean
def side (u v : V) : Finset (Sym2 V) := (G.incidenceFinset u).erase s(u, v)

def row (u v : V) : Finset (Sym2 V) := side G u v ∪ side G v u

def nColor (c : Sym2 V → C) (u v : V) (α : C) : ℕ :=
  #{f ∈ row G u v | c f = α}

def IsStrongMajority (c : Sym2 V → C) : Prop :=
  ∀ u v, G.Adj u v → ∀ α : C, nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2

def Admissible : Prop :=
  ∀ u v, G.Adj u v → G.degree u + G.degree v ≠ 3
```

Glossed to bedrock, each term named is a mathlib definition unless noted:

- **`SimpleGraph V`** (mathlib): an irreflexive symmetric relation `Adj` on `V`.
  Its edges are elements of `Sym2 V`.
- **`Sym2 V`** (mathlib): the type of unordered pairs from `V`; `s(u, v)` is the
  unordered pair `{u, v}`. An edge of `G` is such a pair with `G.Adj u v`.
- **`G.degree u`** (mathlib): the number of neighbours of `u`, i.e.
  `(G.neighborFinset u).card`.
- **`G.incidenceFinset u`** (mathlib): the finite set of edges of `G` that contain
  `u` — every `s(u, w)` with `G.Adj u w`.
- **`Finset.erase s`** and **`∪`** (mathlib): set-minus-one-element and union on
  `Finset`. So **`side G u v`** is exactly "the edges at `u`, except the edge
  `s(u,v)` itself", and **`row G u v`** is "all edges sharing an endpoint with
  `s(u,v)`, the edge itself excluded" — the *adjacent* edges.
- **`#{f ∈ s | p f}`** is `Finset.card` of the filtered finset. So **`nColor`** is
  the number of adjacent edges that carry color `α`.
- **`(G.degree u + G.degree v - 2) / 2`** is Lean `ℕ` arithmetic: `-` is truncated
  subtraction (harmless — endpoint degrees of an edge sum to ≥ 2) and `/` is floor
  division. This is `⌊(d(u)+d(v)−2)/2⌋`.
- **`IsStrongMajority c`**: for every edge `uv` and *every* color `α` (the
  quantifier ranges over `α = c(uv)` too, as the source definition requires), the
  number of adjacent `α`-edges is at most that floor threshold.
- **`Admissible G`**: no edge has endpoint degrees summing to 3, i.e. no edge with
  degree pair `{1,2}` — extensionally the source papers' "no pendant path of
  length two".
- **`Fin 5`** (mathlib): the five-element type — the palette "at most five colors".

The coloring is a *total* function `c : Sym2 V → C`; values on non-edges are
irrelevant because `row` contains only genuine edges.

**Executable sanity checks** (all verified against the built artifact; drop into a
file that imports `Maj5Base`, then `lake env lean Check.lean`). `Admissible` is a
`def` wrapping a `∀`, so we inline it for `decide` to find the `Decidable`
instance:

```lean
import Maj5Base
open SMaj
abbrev K3 : SimpleGraph (Fin 3) := ⊤                                    -- triangle
abbrev P3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel (fun a b : Fin 3 => a.val + 1 = b.val)  -- path 0—1—2

-- Admissibility (inlined): K3 admissible (every edge degree-sum 4 ≠ 3);
-- P3 NOT admissible (edge {0,1} has degrees {1,2}, sum 3 — a pendant path of length two).
#eval decide (∀ u v : Fin 3, K3.Adj u v → K3.degree u + K3.degree v ≠ 3)   -- true
#eval decide (∀ u v : Fin 3, P3.Adj u v → P3.degree u + P3.degree v ≠ 3)   -- false

-- Degrees: K3 all 2; P3 ends degree 1, middle degree 2.
#eval K3.degree 0     -- 2
#eval P3.degree 0     -- 1
#eval P3.degree 1     -- 2

-- `row` and `nColor` compute: the row of edge {0,1} in K3 is the two other edges
-- {0,2},{1,2} (card 2); under the all-color-0 coloring, both are color 0.
#eval (row K3 0 1).card                          -- 2
#eval nColor K3 (fun _ => (0 : Fin 5)) 0 1 0     -- 2
```

(The all-0 coloring gives count 2 > threshold ⌊(2+2−2)/2⌋ = 1 on K3, so it is *not*
strong majority — illustrating why five colors are needed even on a triangle;
`maj_le_five` supplies a coloring that is. The demos show the *definitions* compute
as intended on tiny cases.)

---

## 3. Bridge: source Theorem 2 → our formal statement

**[APS] Theorem 2** (Antoniuk, Prorok, Salia, arXiv:2607.00212v1), quoted verbatim
from the arXiv LaTeX source (label `thm:five`, compiled number 2):

> **Theorem 2.** For every admissible graph $G$, $\mathrm{Maj}'(G) \le 5$.

where the paper defines $\mathrm{Maj}'(G) \le k$ to mean the edges of $G$ can be
colored with $k$ colors so that for every edge $e$ and every color $\alpha$, at
most $\frac{d(u)+d(v)}{2} - 1$ of the edges adjacent to $e = uv$ have color
$\alpha$, and "admissible" to mean $G$ has no pendant path of length two.

**Correspondence.**

| [APS] Theorem 2 | Lean `maj_le_five` |
|---|---|
| "edges of $G$ colored with 5 colors" | `∃ c : Sym2 V → Fin 5` |
| "for every edge $e = uv$" | `∀ u v, G.Adj u v` |
| "every color $\alpha$" | `∀ α : Fin 5` |
| "$\le \frac{d(u)+d(v)}{2} - 1$ adjacent edges of color $\alpha$" | `nColor G c u v α ≤ (G.degree u + G.degree v - 2) / 2` |
| "admissible ($G$)" | `Admissible G` |

The one non-syntactic step is the threshold: for an integer count $n$, the
rational condition $n \le \frac{d(u)+d(v)}{2} - 1$ is equivalent to
$n \le \lfloor \frac{d(u)+d(v)-2}{2}\rfloor$ in both parities (at $d(u)+d(v)=2$,
a $K_2$ edge, both sides are 0 over an empty row). This parity equivalence is
written out in the paper's §3.1 and its transplant record.

Our formalized *proof* follows a different route from [APS] (contraction to a
bounded-degree multigraph + Vizing at Δ ≤ 4 + chain transport, not equitable
colorings + ear reductions); the *statement* proved is Theorem 2 as above.

---

## 4. Axiom audit (pasted output)

`lean/audit_final_gateS.lean` re-prints, for the headline theorem and every named
layer of the chain:

```
'SMaj.Synthesis.maj_le_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'SMaj.exists_isGlueColoring_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'SMaj.maj_le_five_of_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
'SMaj.strongMajority_of_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
'SMaj.Lam2.exists_five_multicoloring_of_simple' depends on axioms: [propext, Classical.choice, Quot.sound]
'SMaj.exists_five_multicoloring_of_reinsertable' depends on axioms: [propext, Classical.choice, Quot.sound]
'SimpleGraph.reachable_kempeGraph_of_missing' depends on axioms: [propext, Classical.choice, Quot.sound]
audit exit: 0
```

`[propext, Classical.choice, Quot.sound]` is the standard mathlib axiom triple and
nothing else — in particular **no `sorryAx`** (there is no `sorry` anywhere in the
dependency cone), no `native_decide`, no custom axioms. This footprint is what a
successful build of `Rung5Lam5` also prints for `maj_le_five` on its last line.

---

## 5. One command to rebuild and re-audit

From the `lean/` directory (requires `elan`/`lake`; the pinned toolchain
`leanprover/lean4:v4.28.0` and mathlib pin `8f9d9cff…` are fetched automatically —
run `lake exe cache get` first for prebuilt mathlib oleans):

```
lake build Rung5Lam5
```

`Rung5Lam5.lean` ends with `#print axioms SMaj.Synthesis.maj_le_five`, so a
successful build prints the headline footprint. For the full per-layer audit:

```
lake env lean audit_final_gateS.lean
```

or run both at once with `./rebuild_and_audit.sh`. SHA-256 of every source file is
recorded in `lean/HASHES.txt` (`sha256sum -c HASHES.txt`).
