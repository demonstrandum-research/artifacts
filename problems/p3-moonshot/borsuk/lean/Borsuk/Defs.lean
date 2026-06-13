/-
# Borsuk/Defs.lean — Formal definitions (FROZEN — do not edit; fill sorries elsewhere)

Formal definitions for the disproof of **Conjecture 3** of

  A. E. Brose, J. A. De Loera, G. Lopez-Campos, A. J. Torres,
  "On Lattice Diameter Segments and A Discrete Borsuk Partition Problem",
  arXiv:2508.20009v1 (27 Aug 2025).

Every definition below is documented against the verbatim paper text (quoted from
the arXiv v1 LaTeX source, with TeX macros `\bx, \by, \bu, \bt` rendered as
`x, y, u, t`).  The Lean kernel verifies the proofs; faithfulness of THESE
definitions to the paper is the one thing it cannot check, so each docstring
quotes the paper and justifies every encoding choice.

## Global encoding choices (d = 2)

* The paper's conjecture quantifies over all dimensions `d`; a counterexample in
  any single dimension refutes it.  We work in `d = 2`, encoding `ℤ²` as `ℤ × ℤ`
  and `ℝ²` as `ℝ × ℝ` (the product `ℝ`-module structure of `ℝ × ℝ` is the
  standard vector-space structure of the plane, and `segment`/`convexHull` from
  mathlib specialize to the textbook notions there).
* "**bounded set** `S ⊂ ℤ^d`" (paper, Conjecture 3 and Definition 1.3): a subset
  of `ℤ²` is bounded iff it is finite (a bounded region of the plane contains
  finitely many lattice points; conversely finite sets are bounded).  We
  therefore represent bounded subsets of `ℤ²` as `Finset (ℤ × ℤ)`.  For the
  *refutation* this encoding is conservative in the safe direction: our witness
  is an explicit 4-element set, which is certainly bounded, so it falsifies the
  paper's statement under any reading of "bounded".
* `2^d = 4` for `d = 2`; we keep the literal `2 ^ 2` in the final conjecture
  statement.
-/
import Mathlib

namespace Borsuk

/-- `ℤ²`, encoded as the product `ℤ × ℤ`. -/
abbrev Z2 : Type := ℤ × ℤ

/-- `ℝ²`, encoded as the product `ℝ × ℝ` with its standard `ℝ`-module structure. -/
abbrev R2 : Type := ℝ × ℝ

/-- The canonical embedding `ℤ² ↪ ℝ²` (coordinatewise `Int.cast`).
The paper treats `ℤ^d` as a subset of `ℝ^d`; in Lean we make the inclusion an
explicit (injective) map. -/
def toR (p : Z2) : R2 := ((p.1 : ℝ), (p.2 : ℝ))

@[simp] theorem toR_fst (p : Z2) : (toR p).1 = (p.1 : ℝ) := rfl

@[simp] theorem toR_snd (p : Z2) : (toR p).2 = (p.2 : ℝ) := rfl

theorem toR_injective : Function.Injective toR := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [toR, Prod.mk.injEq, Int.cast_injective.eq_iff] at h
  simp [h.1, h.2]

/-- Paper (Notation, §1): "a vector `u = (u_1, …, u_d) ∈ ℤ^d` is called
**primitive** if `gcd(u_1, …, u_d) = 1`." -/
def Primitive (v : Z2) : Prop := Int.gcd v.1 v.2 = 1

instance : DecidablePred Primitive := fun v =>
  inferInstanceAs (Decidable (Int.gcd v.1 v.2 = 1))

/-!
## The lattice-length semimetric `f` and the lattice diameter

Paper (Notation, §1): "The segment between two points `x, y ∈ ℝ^d` is denoted
`[x,y] := conv({x,y})`".

Paper (§4.2, first display): "the function `f : ℤ^d × ℤ^d → ℝ` defined by
`f(x, y) = nvol([x, y]) = |[x, y] ∩ ℤ^d| − 1` is a semi-metric".

Encoding: `[x,y] ∩ ℤ^d` is the set of *lattice* points on the real segment.  We
encode it as a subset of `ℤ²` — the preimage `{p : ℤ² | toR p ∈ segment ℝ x y}` —
rather than a subset of `ℝ²`; since `toR` is injective these two sets are in
cardinality-preserving bijection, and the preimage form is what `|· ∩ ℤ^d|`
*means*.  mathlib's `segment ℝ a b` is the closed segment
`{z | ∃ u v ≥ 0, u + v = 1, u • a + v • b = z}`, which equals
`convexHull ℝ {a, b}` (lemma `segLatticePts_eq_pullback_convexHull` below makes
the paper's `[x,y] = conv({x,y})` reading explicit and is *proved*, not assumed).

`f` takes values in `{0, 1, 2, …} ⊆ ℝ` (the paper's codomain `ℝ` is an
artifact of calling it a semimetric); we give it codomain `ℕ`.  Since `x` itself
always lies on `[x,y]`, the set is nonempty and the `ℕ`-truncated subtraction
`ncard − 1` computes the exact integer value `|[x,y] ∩ ℤ²| − 1 ≥ 0`.
-/

/-- The set of lattice points on the closed segment `[x,y]`, as a subset of `ℤ²`:
`{p ∈ ℤ² | p ∈ [x,y]}`.  This encodes the paper's `[x, y] ∩ ℤ^d`. -/
def segLatticePts (x y : Z2) : Set Z2 :=
  {p : Z2 | toR p ∈ segment ℝ (toR x) (toR y)}

/-- Faithfulness bridge for the segment encoding: mathlib's `segment` is exactly
the paper's `[x,y] := conv({x,y})`. -/
theorem segLatticePts_eq_pullback_convexHull (x y : Z2) :
    segLatticePts x y = {p : Z2 | toR p ∈ convexHull ℝ {toR x, toR y}} := by
  unfold segLatticePts
  rw [convexHull_pair]

/-- Paper (§4.2): "`f(x, y) = nvol([x, y]) = |[x, y] ∩ ℤ^d| − 1`" — the number of
lattice points on the segment `[x,y]`, minus one.  (Called `latticeLength`
here; it is the lattice diameter of the single segment `[x,y]`.) -/
noncomputable def latticeLength (x y : Z2) : ℕ :=
  (segLatticePts x y).ncard - 1

/-- Both endpoints lie on the segment. -/
theorem left_mem_segLatticePts (x y : Z2) : x ∈ segLatticePts x y :=
  left_mem_segment ℝ (toR x) (toR y)

theorem right_mem_segLatticePts (x y : Z2) : y ∈ segLatticePts x y :=
  right_mem_segment ℝ (toR x) (toR y)

@[simp] theorem segLatticePts_self (x : Z2) : segLatticePts x x = {x} := by
  ext p
  simp only [segLatticePts, Set.mem_setOf_eq, segment_same, Set.mem_singleton_iff]
  exact ⟨fun h => toR_injective h, fun h => by rw [h]⟩

@[simp] theorem latticeLength_self (x : Z2) : latticeLength x x = 0 := by
  unfold latticeLength
  rw [segLatticePts_self, Set.ncard_singleton]

/-- Paper (Definition 1.1, label `def:ld-non-convex`): "For a compact set
`S ⊂ ℝ^d`, define `ldiam(S) := max_{x,y ∈ S ∩ ℤ^d} |conv({x,y}) ∩ ℤ^d| − 1` as
the **lattice diameter** of `S`."  For a bounded set `S ⊂ ℤ^d` (the case used in
§4.2 and in Conjecture 3, where it is written `diam_ℤ(S)`) this is
`max_{x,y ∈ S} f(x,y)`.

Encoding: `Finset.sup` over both arguments.  For `S = ∅`, `Finset.sup` returns
`0`; the paper never takes the diameter of the empty set, and the value is
irrelevant to the refutation (our witness is nonempty). -/
noncomputable def latticeDiam (S : Finset Z2) : ℕ :=
  S.sup fun x => S.sup fun y => latticeLength x y

@[simp] theorem latticeDiam_singleton (x : Z2) : latticeDiam ({x} : Finset Z2) = 0 := by
  unfold latticeDiam
  simp

/-!
## The lattice Borsuk number `β_ℤ`

Paper (Definition 1.3, Introduction): "Let `S ⊂ ℤ^d` be a bounded set.  Define
the **lattice Borsuk number** of `S`, `β_ℤ(S)`, as the minimal size of a
partition of `S` where each part has a smaller lattice diameter than `ldiam(S)`."

Paper (§4.2, restatement): "Recall that for a bounded set `S` the *lattice
Borsuk number* of `S`, denoted `β_ℤ(S)`, is the smallest number of subsets into
which `S` can be partitioned, such that each subset has strictly smaller lattice
diameter than `diam_ℤ(S)`."

Encoding: partitions of a `Finset` are mathlib's `Finpartition S` (pairwise
disjoint nonempty parts whose union is `S` — the standard notion of partition),
and "minimal size" is `sInf` of the achievable part-counts.

Degenerate-case audit (the kernel can't check faithfulness, so we do):
* If `latticeDiam S ≥ 1`, the partition into singletons is admissible (each
  singleton has diameter `0`), so the `sInf` ranges over a nonempty set and
  equals the paper's minimum.  This covers every set the paper's conjecture is
  really about (a set with `β_ℤ(S) = 2^d ≥ 4` has at least 2 points, hence
  diameter `≥ 1`).
* If `S` is empty or a singleton then `latticeDiam S = 0`, no part can have
  strictly smaller diameter, the set of achievable counts is empty (for `∅`,
  the empty partition IS admissible and gives `0`), and `sInf ∅ = 0` by
  convention.  These junk values are `0 ≠ 2^2`, so they can never make our
  formalized Conjecture 3 *easier to refute* than the paper's statement: the
  left side `β_ℤ(S) = 2^2` of the iff is false for them under both the paper's
  reading and ours, and our refutation witness has honest diameter `1`.
-/

/-- A **Borsuk partition** of `S`: a partition of `S` in which every part has
strictly smaller lattice diameter than `S` itself. -/
def IsBorsukPartition (S : Finset Z2) (P : Finpartition S) : Prop :=
  ∀ p ∈ P.parts, latticeDiam p < latticeDiam S

/-- Paper (Definition 1.3): the **lattice Borsuk number** `β_ℤ(S)` — "the
minimal size of a partition of `S` where each part has a smaller lattice
diameter than `ldiam(S)`". -/
noncomputable def betaZ (S : Finset Z2) : ℕ :=
  sInf {n : ℕ | ∃ P : Finpartition S, IsBorsukPartition S P ∧ P.parts.card = n}

/-!
## Unimodular equivalence and the cube `[0,m]²`

Paper (Notation, §1): "We say two lattice `d`-polytopes `P` and `Q` are
**unimodularly equivalent** if there exists a unimodular matrix `A ∈ GL(d,ℤ)`
and `t ∈ ℤ^d` such that `P = AQ + t`, i.e., these transformations correspond to
lattice preserving maps."

Encoding (d = 2): a `2 × 2` integer matrix is in `GL(2,ℤ)` (i.e. invertible
over `ℤ`, "unimodular") iff its determinant is `±1` — over a commutative ring a
square matrix is invertible iff its determinant is a unit, and the units of `ℤ`
are `{1, -1}`.  We store the four entries `a b c d` and the translation
`(t1, t2)` as explicit integers with the determinant condition
`a*d − b*c = ±1`; this avoids `Matrix` plumbing while keeping the textbook
definition in plain sight.  The equivalence `P = AQ + t` is between subsets of
`ℝ^d` (the paper applies `A` and `t` to polytopes `P, Q ⊆ ℝ^d`), so the map
acts on `ℝ²` via the cast entries; `UnimodMap.realMap_toR` records that it
restricts to `ℤ²` (the "lattice preserving" clause).

We state `UnimodEquiv` for *arbitrary* subsets of `ℝ²`.  The paper defines it
for lattice polytopes; `conv(S_A)` and `[0,m]²` are lattice polytopes, so on
the objects appearing in Conjecture 3 the two readings agree, and quantifying
over a wider class only makes our refutation statement stronger nowhere — the
refutation *denies* an equivalence, and the denial for the wider class is the
same statement as for the narrower one on these objects. -/
structure UnimodMap where
  /-- matrix entry (1,1) -/
  a : ℤ
  /-- matrix entry (1,2) -/
  b : ℤ
  /-- matrix entry (2,1) -/
  c : ℤ
  /-- matrix entry (2,2) -/
  d : ℤ
  /-- translation, first coordinate -/
  t1 : ℤ
  /-- translation, second coordinate -/
  t2 : ℤ
  /-- `A ∈ GL(2,ℤ)`: the determinant is a unit of `ℤ`, i.e. `±1`. -/
  det_eq : a * d - b * c = 1 ∨ a * d - b * c = -1

namespace UnimodMap

/-- The action `p ↦ Ap + t` on `ℤ²`. -/
def intMap (φ : UnimodMap) (p : Z2) : Z2 :=
  (φ.a * p.1 + φ.b * p.2 + φ.t1, φ.c * p.1 + φ.d * p.2 + φ.t2)

/-- The action `p ↦ Ap + t` on `ℝ²` (the paper's `AQ + t` for `Q ⊆ ℝ^d`). -/
def realMap (φ : UnimodMap) (p : R2) : R2 :=
  ((φ.a : ℝ) * p.1 + (φ.b : ℝ) * p.2 + (φ.t1 : ℝ),
   (φ.c : ℝ) * p.1 + (φ.d : ℝ) * p.2 + (φ.t2 : ℝ))

/-- The real action restricts to the integer action on lattice points —
the paper's "these transformations correspond to lattice preserving maps". -/
@[simp] theorem realMap_toR (φ : UnimodMap) (p : Z2) :
    φ.realMap (toR p) = toR (φ.intMap p) := by
  unfold realMap intMap toR
  simp only [Prod.mk.injEq]
  constructor <;> push_cast <;> ring

end UnimodMap

/-- Paper: "`P` and `Q` are unimodularly equivalent if there exists a unimodular
matrix `A ∈ GL(d,ℤ)` and `t ∈ ℤ^d` such that `P = AQ + t`." -/
def UnimodEquiv (P Q : Set R2) : Prop :=
  ∃ φ : UnimodMap, φ.realMap '' Q = P

/-- The `d`-cube `[0,m]^d` for `d = 2`: the square `[0,m] × [0,m] ⊆ ℝ²`. -/
def cube (m : ℕ) : Set R2 :=
  {p : R2 | (0 ≤ p.1 ∧ p.1 ≤ (m : ℝ)) ∧ (0 ≤ p.2 ∧ p.2 ≤ (m : ℝ))}

/-- `|P ∩ ℤ²|` — the number of lattice points in a plane set `P`, encoded as the
(extended-natural-truncated) cardinality of the pulled-back set of lattice
points.  Since `toR` is injective, this equals the cardinality of `P ∩ ℤ²` as a
subset of `ℝ²`.  (`Set.ncard` of an infinite set is `0`; every set we count is
finite, and all our counting lemmas prove exact finite values.) -/
noncomputable def latticeCount (P : Set R2) : ℕ :=
  {p : Z2 | toR p ∈ P}.ncard

/-!
## Conjecture 3, formal statement (d = 2 instance)

Paper (§4.2, label `conj:Borsuk` — **Conjecture 3** in the compiled paper, the
third `conjecture` environment): "Let `S ⊂ ℤ^d` be a bounded set. Then
`β_ℤ(S) = 2^d` if and only if `conv(S)` is unimodularly equivalent to a
`d`-cube `[0,m]^d` for any `m ∈ ℕ`."

Reading notes (faithfulness):
* "for any `m ∈ ℕ`" in context means "for *some* `m`" (`P` is one polytope; it
  can only be equivalent to a single size of cube) — we render it `∃ m : ℕ`.
  Our refutation below in fact proves `∀ m, ¬ equiv`, which negates the
  right-hand side under **either** reading of "any", so nothing hinges on this.
* The conjecture asserts a statement for every `d`; refuting the `d = 2`
  instance refutes the conjecture as stated.  `2^d = 2^2`.
* "bounded set `S ⊂ ℤ²`" is encoded as `S : Finset Z2`, see the module
  docstring: bounded subsets of `ℤ²` are exactly the finite ones.
* `conv(S)` is `convexHull ℝ` of the image of `S` in `ℝ²`. -/
def Conjecture3For2D : Prop :=
  ∀ S : Finset Z2,
    (betaZ S = 2 ^ 2 ↔
      ∃ m : ℕ, UnimodEquiv (convexHull ℝ (toR '' (S : Set Z2))) (cube m))

end Borsuk
