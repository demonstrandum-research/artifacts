/-
Demos.lean — executable small-n demonstrations of the frozen base definitions
behind the kernel-clean theorem `Rung4Moonshot.R4_four_regular`.

This file is READ-ONLY WITNESS material: it imports the frozen `Maj5Base`
interface, adds NO theorems, axioms, or `sorry`, and only computes `#eval` /
`decide` values on concrete tiny graphs so a reader can watch the definitions
`side` / `row` / `nColor` / `IsStrongMajority` — and the 4-regular cap value
`3 = ⌊(4+4−2)/2⌋` — compute on the page. Every `#eval` prints the value written
in its trailing `-- expected` comment (verified against the built libs).

Nothing here is imported by `Pins2.lean`; deleting this file does not affect the
theorem. It exists solely to make the READING-KIT definitions self-checking.
-/

import Maj5Base

set_option autoImplicit false

open SMaj

/-! ## Two concrete tiny graphs -/

/-- The complete graph on five vertices: the smallest 4-regular graph. -/
abbrev K5 : SimpleGraph (Fin 5) := ⊤

/-- The triangle (complete graph on three vertices), for a clean example/non-example
of `IsStrongMajority` mirroring the five-color artifact's reading-kit demos. -/
abbrev K3 : SimpleGraph (Fin 3) := ⊤

/-! ## Explicit colorings -/

/-- A four-coloring of `K5`'s ten edges by `(i+j) mod 4`. Because no residue class
is hit more than three times, every color is used on at most three edges of the
whole graph — so automatically on at most three of any edge's six neighbours. -/
def cK5 : Sym2 (Fin 5) → Fin 4 :=
  Sym2.lift ⟨fun i j => ⟨(i.val + j.val) % 4, Nat.mod_lt _ (by norm_num)⟩,
            fun i j => Fin.ext (by simp [Nat.add_comm])⟩

/-- A proper three-coloring of the triangle's edges by `(i+j) mod 3`
(edges `{0,1},{0,2},{1,2}` get three distinct colors). -/
def cK3 : Sym2 (Fin 3) → Fin 4 :=
  Sym2.lift ⟨fun i j => ⟨(i.val + j.val) % 3,
              by have : (i.val + j.val) % 3 < 3 := Nat.mod_lt _ (by norm_num); omega⟩,
            fun i j => Fin.ext (by simp [Nat.add_comm])⟩

/-! ## 1. Degrees: `K5` is 4-regular, `K3` is 2-regular. -/

-- Reader concludes: every vertex of K5 has degree 4 (this is the 4-regular hypothesis).
#eval K5.degree 0            -- expected: 4
#eval K5.degree 3            -- expected: 4
-- Reader concludes: the triangle is 2-regular.
#eval K3.degree 0            -- expected: 2

/-! ## 2. `side`, `row`, and the cap `3 = ⌊(4+4−2)/2⌋` compute concretely. -/

-- Reader concludes: `side G 0 1` is the edges at vertex 0 other than {0,1} — three of them in K5.
#eval (SMaj.side K5 0 1).card                     -- expected: 3
-- Reader concludes: `row G 0 1` is all edges adjacent to the edge {0,1} — six of them in K5.
#eval (SMaj.row K5 0 1).card                      -- expected: 6
-- Reader concludes: on a 4-regular graph the strong-majority cap is exactly 3 = ⌊(4+4−2)/2⌋.
#eval (K5.degree 0 + K5.degree 1 - 2) / 2         -- expected: 3
-- Reader concludes: in the triangle `row` has two edges and the cap is 1 = ⌊(2+2−2)/2⌋.
#eval (SMaj.row K3 0 1).card                      -- expected: 2
#eval (K3.degree 0 + K3.degree 1 - 2) / 2         -- expected: 1

/-! ## 3. `nColor` counts adjacent same-colored edges. -/

-- Reader concludes: under the all-color-0 coloring EVERY one of the six edges adjacent
-- to {0,1} in K5 is color 0, so nColor = 6 — which exceeds the cap 3 (see §4).
#eval nColor K5 (fun _ => (0 : Fin 4)) 0 1 0       -- expected: 6
-- Reader concludes: under cK5, the edge {0,1} sees color 0 on at most a few neighbours (≤ 3).
#eval nColor K5 cK5 0 1 0                           -- expected: 2
#eval nColor K5 cK5 0 1 1                           -- expected: 1

/-! ## 4. `IsStrongMajority` — the predicate says YES and NO on concrete inputs.

`IsStrongMajority` is a `def` wrapping a `∀`; to let `decide` locate the
`Decidable` instance we inline it as the equivalent explicit `∀` (same `nColor`
and same cap as the frozen definition). -/

-- EXAMPLE (4-regular headline): cK5 IS strong majority on K5 → the predicate says YES.
-- Reader concludes: a four-coloring meeting the cap 3 on every edge of a 4-regular graph
-- exists concretely — exactly what R4_four_regular asserts, here witnessed on K5.
#eval decide (∀ u v : Fin 5, K5.Adj u v → ∀ α : Fin 4,
    nColor K5 cK5 u v α ≤ (K5.degree u + K5.degree v - 2) / 2)   -- expected: true

-- NON-EXAMPLE (4-regular): the all-0 coloring is NOT strong majority on K5 →
-- the predicate says NO (some edge has a color on 6 > 3 of its neighbours).
-- Reader concludes: the predicate genuinely rejects bad colorings.
#eval decide (∀ u v : Fin 5, K5.Adj u v → ∀ α : Fin 4,
    nColor K5 (fun _ => (0 : Fin 4)) u v α ≤ (K5.degree u + K5.degree v - 2) / 2)  -- expected: false

-- EXAMPLE (triangle): the proper 3-coloring cK3 IS strong majority on K3 → YES.
#eval decide (∀ u v : Fin 3, K3.Adj u v → ∀ α : Fin 4,
    nColor K3 cK3 u v α ≤ (K3.degree u + K3.degree v - 2) / 2)   -- expected: true

-- NON-EXAMPLE (triangle): the all-0 coloring fails the cap 1 on K3 → NO.
#eval decide (∀ u v : Fin 3, K3.Adj u v → ∀ α : Fin 4,
    nColor K3 (fun _ => (0 : Fin 4)) u v α ≤ (K3.degree u + K3.degree v - 2) / 2)  -- expected: false
