import UCFrankl.Frankl

/-!
# Census regression tests (decide-based)

Program UC, lens C4L4 (campaign C4, 2026-06-13). Charter item N5.5: wire
census data as kernel-checked `decide` regression tests against the formal
`UnionClosed`/`freq` definitions of `Frankl.lean`. Each test pins a fact the
Python census infrastructure (lab/, L3, C2L5) reports, so the formal
definitions and the census code can never silently drift apart.

Test families:

1. `FC5` — the union-closure of the 5-cycle's edges plus `∅` (17 sets): the
   UNIQUE MT-failure class on `n ≤ 5` (G-L3-A4); the census reports all five
   frequencies `= 10` (uniform 10/17). The first three tests pin exactly that.
2. `powersetFin3` — `2^[3]` (8 sets): T1's equality case; frequencies 4 = m/2.
3. `gapless3` — `P(3) = 2^[3] minus one singleton` (7 sets): the PROVED
   maximizer family of the gaplessness lemma (N4.1, C2L5); the product test
   pins its T1 (reverse trace-Shearer) instance `4·4·3 = 48 ≤ 49 = 7²`.

## EPISTEMIC-STATUS LEDGER (program law)

* Every `theorem` here: MACHINE-VERIFIED (kernel `decide`; axiom audit in
  `scripts/CheckAxioms.lean`). These are finite facts about explicit
  families — regression pins, not mathematics.
-/

namespace UCFrankl

/-- `UnionClosed` is decidable for concrete families (route the
strict-implicit binders through the explicit bounded-forall form).
[PROVED: definitional.] -/
instance {n : ℕ} (F : Finset (Finset (Fin n))) : Decidable (UnionClosed F) :=
  decidable_of_iff (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    ⟨fun h _ hA _ hB => h _ hA _ hB, fun h _ hA _ hB => h hA hB⟩

/-- `F_C5`: union-closure of the edges of the 5-cycle on `Fin 5`, plus `∅`
(census convention). 17 sets. [PROVED: definition; matches L3
`data/certificates.json` CERT1 family.] -/
def FC5 : Finset (Finset (Fin 5)) :=
  { ∅,
    {0, 1}, {0, 4}, {1, 2}, {2, 3}, {3, 4},
    {0, 1, 2}, {0, 1, 4}, {0, 3, 4}, {1, 2, 3}, {2, 3, 4},
    {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4},
    {0, 1, 2, 3, 4} }

/-- `F_C5` has 17 members. [MACHINE-VERIFIED: kernel decide.] -/
theorem fc5_card : FC5.card = 17 := by decide

/-- `F_C5` is union-closed. [MACHINE-VERIFIED: kernel decide.] -/
theorem fc5_unionClosed : UnionClosed FC5 := by decide

/-- Every element of the ground set has frequency exactly 10 in `F_C5` —
the census's "all frequencies 10/17". [MACHINE-VERIFIED: kernel decide.] -/
theorem fc5_freq_uniform : ∀ i : Fin 5, freq FC5 i = 10 := by decide

/-- `F_C5` satisfies the Frankl 1/2-bound with strict slack: 10/17 > 1/2,
i.e. the unique small MT-failure class is NOT a Frankl near-witness.
[MACHINE-VERIFIED: kernel decide.] -/
theorem fc5_majority : ∀ i : Fin 5, FC5.card < 2 * freq FC5 i := by decide

/-- `2^[3]`: the full powerset family on `Fin 3` (8 sets). [PROVED:
definition.] -/
def powersetFin3 : Finset (Finset (Fin 3)) := (Finset.univ : Finset (Fin 3)).powerset

/-- The powerset family is union-closed with every frequency exactly half
the family size (T1's equality case). [MACHINE-VERIFIED: kernel decide.] -/
theorem powersetFin3_card : powersetFin3.card = 8 := by decide

theorem powersetFin3_unionClosed : UnionClosed powersetFin3 := by decide

theorem powersetFin3_freq : ∀ i : Fin 3, 2 * freq powersetFin3 i = powersetFin3.card := by
  decide

/-- `P(3)`: the powerset of `[3]` minus the singleton `{0}` (7 sets) — the
proved maximizer family of the gaplessness lemma (N4.1/C2L5). [PROVED:
definition.] -/
def gapless3 : Finset (Finset (Fin 3)) :=
  powersetFin3.erase {0}

theorem gapless3_card : gapless3.card = 7 := by decide

theorem gapless3_unionClosed : UnionClosed gapless3 := by decide

/-- Frequencies of `P(3)`: the deleted singleton's element drops to 3, the
others stay at 4. [MACHINE-VERIFIED: kernel decide.] -/
theorem gapless3_freq : freq gapless3 0 = 3 ∧ freq gapless3 1 = 4 ∧ freq gapless3 2 = 4 := by
  decide

/-- The reverse trace-Shearer (T1, N4.1) instance at the gapless maximizer:
`N₀·N₁·N₂ = 48 ≤ 49 = m^(u-1)`. The census's worst non-powerset T1 ratio at
`u = 3`, pinned in kernel. [MACHINE-VERIFIED: kernel decide.] -/
theorem gapless3_traceShearer :
    freq gapless3 0 * freq gapless3 1 * freq gapless3 2 ≤ gapless3.card ^ 2 := by decide

end UCFrankl
