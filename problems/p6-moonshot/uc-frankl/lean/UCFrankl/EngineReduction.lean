import Mathlib
import UCFrankl.Frankl
import UCFrankl.Entropy
import UCFrankl.Gilmer
import UCFrankl.CondEntropy

/-!
# The Gilmer engine reduced to one scalar inequality, kernel-checked

Program UC, lens C2L4 (Lean bridge, campaign C2, 2026-06-13). C1 left the
program with the kernel-checked reduction `GilmerEngine c → FranklWithConstant
c` and the analytic half (`GilmerEngine c` itself) unformalized, estimated at
3–6k lines. This file collapses that estimate by formalizing the analytic half
*modulo a single pointwise two-variable inequality*:

  `WeakBoppana K`:  `∀ x y ∈ [0,1] : K·(x·h(y) + y·h(x)) ≤ h(x·y)`

(`h = Real.binEntropy`; sharp at `K = (1+√5)/4 = 1/(2φ)`, equality at
`x = y = 1/φ` — Chase–Lovett arXiv:2211.11689; see ledger below). The chain is:

  `WeakBoppana K` → `GilmerEngine c` for every `c` with `1 < 2K(1−c)`
                  → `FranklWithConstant c`,

and with the sharp constant, `FranklWithConstant c` for every `c < ψ`, hence —
via the supremum-closure lemma `franklWithConstant_of_forall_lt` — exactly
`FranklWithConstant ψ`, the Gilmer–AHS–Chase–Lovett–Sawin–Pebody theorem.

Proof architecture (the mathematical point of the file): the expectation-form
per-coordinate inequality that makes Gilmer-type arguments hard is here
*bilinear*. In complement-mass form, the per-coordinate term factorizes through
the marginal exactly:

  `Σ_{a,b} w_a w_b h(t_a t_b) ≥ K Σ_{a,b} w_a w_b (t_a h(t_b) + t_b h(t_a))
                              = 2K (Σ_a w_a t_a)(Σ_b w_b h(t_b))`,

so the average-marginal hypothesis is consumed with no case analysis. The
coordinate induction uses only the `condBit` layer of `CondEntropy.lean`
(chain rule + superadditivity); no conditional pmfs, no divisions, no
zero-mass case splits appear in the induction.

## EPISTEMIC-STATUS LEDGER (program law)

* `WeakBoppana`, `orFun`, `bitMarginal`, `splitEquiv`, `finsetBoolEquiv`,
  `boppanaConst` — definitions [PROVED].
* `WeakBoppana K` for `0 < K ≤ (1+√5)/4` — **SUPERSEDED at C3L1 (2026-06-13):
  now kernel-PROVED in this development** (`weakBoppana_sharp` in
  `DiagonalReduction.lean`, via the Ho atom port `HoBoppana.lean` + the
  diagonal-reduction lemma). Original C2L4 entry kept below for history:
  PROVED-in-literature, NOT
  formalized (hostile-pass corrected attribution, 2026-06-13): the sharp
  two-variable form is exactly Chase–Lovett arXiv:2211.11689 (as-fetched from
  the PDF: `h(xy) ≥ (1/(2φ))(x·h(y) + y·h(x))` with their `φ = (√5−1)/2`;
  `1/(2φ) = (1+√5)/4`); Boppana arXiv:2301.09664 proves the one-variable
  diagonal form `h(x²) ≥ ((√5+1)/2)·x·h(x)`. Independently MACHINE-VERIFIED
  numerically here (1200² grid + 2·10⁵ local refinements, min ratio
  `h(xy)/(x h(y)+y h(x)) = 0.80902 = (1+√5)/4` to 9 digits at `x = y = 1/φ_golden`;
  `lenses/C2L4-lean-bridge/scratch/check_architecture.py`). It is the single
  residual formalization atom; possible prior Lean work: Ho arXiv:2601.19327
  (as-fetched, unvetted — inspect before reinventing).
* Every `theorem` below — MACHINE-VERIFIED (kernel-checked; axiom audit in
  `scripts/CheckAxioms.lean`). In particular:
  - `gilmerEngine_of_weakBoppana` : `WeakBoppana K → GilmerEngine c` whenever
    `0 ≤ K` and `1 < 2K(1−c)`;
  - `franklWithConstant_of_weakBoppana` : same hypotheses → Frankl with `c`;
  - `franklWithConstant_centile_of_weakBoppana` : `WeakBoppana (11/20)` →
    Frankl with `c = 1/100` (Gilmer's original constant; `11/20` has 47%
    numerical margin against the sharp `φ/2`);
  - `franklWithConstant_psi_of_weakBoppana` : `WeakBoppana ((1+√5)/4)` →
    `FranklWithConstant ψ` — the full golden-constant theorem, kernel-checked
    modulo exactly one scalar inequality.
* (C2L4 scope note, SUPERSEDED at C3L1 2026-06-13: `DiagonalReduction.lean`
  now proves `WeakBoppana boppanaConst` in-kernel, so the unconditional
  `franklWithConstant_psi` and `franklWithConstant_centile` exist there.
  Within THIS FILE every Frankl conclusion remains stated conditionally on
  its `WeakBoppana` hypothesis.) Original: No claim of an unconditional
  kernel-checked Frankl constant is made: every Frankl conclusion below is
  conditional on its `WeakBoppana` hypothesis, which was open in this
  development at C2 close.
-/

namespace UCFrankl

open Finset

/-! ## The scalar atom -/

/-- **The two-variable binary-entropy inequality** at multiplier `K` (the
Gilmer-conjectured / Boppana–Chase–Lovett family): for `x, y ∈ [0,1]`,
`K(x·h(y) + y·h(x)) ≤ h(xy)` with `h = Real.binEntropy`.

LEDGER: a *statement* (`Prop`), not a claim. The sharp case
`K = (1+√5)/4 = 1/(2φ)` is PROVED in the literature (Chase–Lovett
arXiv:2211.11689, two-variable form; Boppana arXiv:2301.09664, one-variable
diagonal) but NOT formalized here. Numerically the optimum is
`(1+√5)/4 ≈ 0.809`, equality at `x = y = 1/φ`. Any `K > 1/2` already yields a
positive Frankl constant via `franklWithConstant_of_weakBoppana`. The
`K = 1/2` case is provable by elementary concavity but yields nothing
(multiplier `2K(1−c) < 1`); the gap `K > 1/2` is the analytic content. -/
def WeakBoppana (K : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
    K * (x * Real.binEntropy y + y * Real.binEntropy x) ≤ Real.binEntropy (x * y)

/-- **Mass form of the weak Boppana inequality** (division-free): what the
engine consumes per pair of histories. `σ` is the complement (bit = false)
mass, `τ` the bit = true mass of each cell. Degenerate (zero-mass) cells give
`0 ≤ 0`. [MACHINE-VERIFIED, given the `WeakBoppana K` hypothesis.] -/
theorem massKey_of_weakBoppana {K : ℝ} (hWB : WeakBoppana K)
    {σa τa σb τb : ℝ} (hσa : 0 ≤ σa) (hτa : 0 ≤ τa) (hσb : 0 ≤ σb) (hτb : 0 ≤ τb) :
    K * (σa * condBit σb τb + σb * condBit σa τa) ≤
      condBit (σa * σb) (σa * τb + τa * σb + τa * τb) := by
  rcases eq_or_lt_of_le (add_nonneg hσa hτa) with ha | ha
  · have h1 : σa = 0 := by linarith
    have h2 : τa = 0 := by linarith
    simp [h1, h2]
  rcases eq_or_lt_of_le (add_nonneg hσb hτb) with hb | hb
  · have h1 : σb = 0 := by linarith
    have h2 : τb = 0 := by linarith
    simp [h1, h2]
  -- both cells have positive mass
  have hwa0 : σa + τa ≠ 0 := ne_of_gt ha
  have hwb0 : σb + τb ≠ 0 := ne_of_gt hb
  have e1 : condBit σb τb = (σb + τb) * Real.binEntropy (σb / (σb + τb)) := by
    have harg : σb / (σb + τb) = 1 - τb / (σb + τb) := by field_simp; ring
    rw [condBit_eq hb, harg, Real.binEntropy_one_sub]
  have e2 : condBit σa τa = (σa + τa) * Real.binEntropy (σa / (σa + τa)) := by
    have harg : σa / (σa + τa) = 1 - τa / (σa + τa) := by field_simp; ring
    rw [condBit_eq ha, harg, Real.binEntropy_one_sub]
  have hww : (0 : ℝ) < (σa + τa) * (σb + τb) := mul_pos ha hb
  have e3 : σa * σb + (σa * τb + τa * σb + τa * τb) = (σa + τa) * (σb + τb) := by ring
  have e4 : condBit (σa * σb) (σa * τb + τa * σb + τa * τb)
      = ((σa + τa) * (σb + τb)) *
        Real.binEntropy ((σa / (σa + τa)) * (σb / (σb + τb))) := by
    have hsum : 0 < σa * σb + (σa * τb + τa * σb + τa * τb) := by rw [e3]; exact hww
    have harg : (σa * τb + τa * σb + τa * τb) / (σa * σb + (σa * τb + τa * σb + τa * τb))
        = 1 - σa / (σa + τa) * (σb / (σb + τb)) := by
      rw [e3]
      field_simp
      ring
    rw [condBit_eq hsum, harg, Real.binEntropy_one_sub, e3]
  rw [e1, e2, e4]
  have hxa0 : 0 ≤ σa / (σa + τa) := div_nonneg hσa ha.le
  have hxa1 : σa / (σa + τa) ≤ 1 := by rw [div_le_one ha]; linarith
  have hxb0 : 0 ≤ σb / (σb + τb) := div_nonneg hσb hb.le
  have hxb1 : σb / (σb + τb) ≤ 1 := by rw [div_le_one hb]; linarith
  have key := hWB _ hxa0 hxa1 _ hxb0 hxb1
  have hmul := mul_le_mul_of_nonneg_left key hww.le
  have hexp : ((σa + τa) * (σb + τb)) *
      (K * (σa / (σa + τa) * Real.binEntropy (σb / (σb + τb)) +
            σb / (σb + τb) * Real.binEntropy (σa / (σa + τa))))
      = K * (σa * ((σb + τb) * Real.binEntropy (σb / (σb + τb))) +
             σb * ((σa + τa) * Real.binEntropy (σa / (σa + τa)))) := by
    field_simp
  rw [hexp] at hmul
  exact hmul

/-! ## Pushforward of the paired OR on `γ × Bool` -/

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- Value of the paired-OR pushforward at `(c, false)`: only (false, false)
bit-pairs land on false. [MACHINE-VERIFIED.] -/
theorem orPush_apply_false (f : γ → γ → γ) (p q : γ × Bool → ℝ) (c : γ) :
    pushforward₂ (fun x y => (f x.1 y.1, x.2 || y.2)) p q (c, false)
      = ∑ d : γ × γ, if f d.1 d.2 = c then p (d.1, false) * q (d.2, false) else 0 := by
  show (∑ x : γ × Bool, ∑ y : γ × Bool,
      if (f x.1 y.1, x.2 || y.2) = (c, false) then p x * q y else 0) = _
  rw [← Fintype.sum_prod_type (f := fun z : (γ × Bool) × (γ × Bool) =>
      if (f z.1.1 z.2.1, z.1.2 || z.2.2) = (c, false) then p z.1 * q z.2 else 0)]
  rw [← Equiv.sum_comp (Equiv.prodProdProdComm γ Bool γ Bool).symm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hf : f d.1 d.2 = c
  · simp [Equiv.prodProdProdComm, Fintype.sum_prod_type, Fintype.sum_bool,
      Prod.mk.injEq, hf]
  · simp [Equiv.prodProdProdComm, Fintype.sum_prod_type, Fintype.sum_bool,
      Prod.mk.injEq, hf]

/-- Value of the paired-OR pushforward at `(c, true)`: the three bit-pairs
with at least one true. [MACHINE-VERIFIED.] -/
theorem orPush_apply_true (f : γ → γ → γ) (p q : γ × Bool → ℝ) (c : γ) :
    pushforward₂ (fun x y => (f x.1 y.1, x.2 || y.2)) p q (c, true)
      = ∑ d : γ × γ, if f d.1 d.2 = c then
          p (d.1, false) * q (d.2, true) + p (d.1, true) * q (d.2, false)
            + p (d.1, true) * q (d.2, true) else 0 := by
  show (∑ x : γ × Bool, ∑ y : γ × Bool,
      if (f x.1 y.1, x.2 || y.2) = (c, true) then p x * q y else 0) = _
  rw [← Fintype.sum_prod_type (f := fun z : (γ × Bool) × (γ × Bool) =>
      if (f z.1.1 z.2.1, z.1.2 || z.2.2) = (c, true) then p z.1 * q z.2 else 0)]
  rw [← Equiv.sum_comp (Equiv.prodProdProdComm γ Bool γ Bool).symm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hf : f d.1 d.2 = c
  · simp [Equiv.prodProdProdComm, Fintype.sum_prod_type, Fintype.sum_bool,
      Prod.mk.injEq, hf]
    ring
  · simp [Equiv.prodProdProdComm, Fintype.sum_prod_type, Fintype.sum_bool,
      Prod.mk.injEq, hf]

/-- The first-component marginal of the paired-OR pushforward is the
`f`-pushforward of the first-component marginals. [MACHINE-VERIFIED.] -/
theorem fstMarg_orPush (f : γ → γ → γ) (p : γ × Bool → ℝ) :
    fstMarg (pushforward₂ (fun x y => (f x.1 y.1, x.2 || y.2)) p p)
      = pushforward₂ f (fstMarg p) (fstMarg p) := by
  funext c
  show pushforward₂ _ p p (c, false) + pushforward₂ _ p p (c, true) = _
  rw [orPush_apply_false, orPush_apply_true, ← Finset.sum_add_distrib]
  show _ = ∑ a, ∑ b, if f a b = c then fstMarg p a * fstMarg p b else 0
  rw [← Fintype.sum_prod_type (f := fun d : γ × γ =>
      if f d.1 d.2 = c then fstMarg p d.1 * fstMarg p d.2 else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hf : f d.1 d.2 = c
  · simp only [hf, if_true]
    unfold fstMarg
    ring
  · simp [hf]

/-- **The engine step**: conditional entropy of the bit coordinate under the
paired-OR pushforward is at least `2K·(complement mass)·(conditional entropy
of the original bit)`. This is the bilinear collapse: the average-marginal
hypothesis will be consumed exactly, with no case analysis.
[MACHINE-VERIFIED, given `WeakBoppana K`.] -/
theorem condH_orPush_ge {K : ℝ} (hWB : WeakBoppana K) (f : γ → γ → γ)
    {p : γ × Bool → ℝ} (hp : ∀ x, 0 ≤ p x) :
    2 * K * (∑ a, p (a, false)) * condH p
      ≤ condH (pushforward₂ (fun x y => (f x.1 y.1, x.2 || y.2)) p p) := by
  classical
  -- abbreviations: per-pair masses
  set R₀ : γ × γ → ℝ := fun d => p (d.1, false) * p (d.2, false) with hR₀
  set R₁ : γ × γ → ℝ := fun d =>
    p (d.1, false) * p (d.2, true) + p (d.1, true) * p (d.2, false)
      + p (d.1, true) * p (d.2, true) with hR₁
  have hR₀nn : ∀ d : γ × γ, 0 ≤ R₀ d := fun d => mul_nonneg (hp _) (hp _)
  have hR₁nn : ∀ d : γ × γ, 0 ≤ R₁ d := fun d => by
    have h1 : 0 ≤ p (d.1, false) * p (d.2, true) := mul_nonneg (hp _) (hp _)
    have h2 : 0 ≤ p (d.1, true) * p (d.2, false) := mul_nonneg (hp _) (hp _)
    have h3 : 0 ≤ p (d.1, true) * p (d.2, true) := mul_nonneg (hp _) (hp _)
    simp only [hR₁]
    linarith
  -- A. fiberwise superadditivity: condH of the pushforward dominates the
  -- pairwise sum of condBits
  have hA : ∑ d : γ × γ, condBit (R₀ d) (R₁ d)
      ≤ condH (pushforward₂ (fun x y => (f x.1 y.1, x.2 || y.2)) p p) := by
    unfold condH
    have hstep : ∀ c : γ,
        ∑ d : γ × γ, (if f d.1 d.2 = c then condBit (R₀ d) (R₁ d) else 0)
          ≤ condBit
              (pushforward₂ (fun x y => (f x.1 y.1, x.2 || y.2)) p p (c, false))
              (pushforward₂ (fun x y => (f x.1 y.1, x.2 || y.2)) p p (c, true)) := by
      intro c
      rw [orPush_apply_false, orPush_apply_true]
      have := sum_condBit_le (Finset.univ : Finset (γ × γ))
        (fun d => if f d.1 d.2 = c then R₀ d else 0)
        (fun d => if f d.1 d.2 = c then R₁ d else 0)
        (fun d _ => by dsimp only; split_ifs with h; exacts [hR₀nn d, le_rfl])
        (fun d _ => by dsimp only; split_ifs with h; exacts [hR₁nn d, le_rfl])
      calc ∑ d : γ × γ, (if f d.1 d.2 = c then condBit (R₀ d) (R₁ d) else 0)
          = ∑ d : γ × γ, condBit (if f d.1 d.2 = c then R₀ d else 0)
              (if f d.1 d.2 = c then R₁ d else 0) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            split_ifs with h
            · rfl
            · simp
        _ ≤ condBit (∑ d : γ × γ, if f d.1 d.2 = c then R₀ d else 0)
              (∑ d : γ × γ, if f d.1 d.2 = c then R₁ d else 0) := this
    calc ∑ d : γ × γ, condBit (R₀ d) (R₁ d)
        = ∑ d : γ × γ, ∑ c : γ, (if f d.1 d.2 = c then condBit (R₀ d) (R₁ d) else 0) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [Finset.sum_ite_eq (Finset.univ : Finset γ) (f d.1 d.2)]
          simp
      _ = ∑ c : γ, ∑ d : γ × γ, (if f d.1 d.2 = c then condBit (R₀ d) (R₁ d) else 0) :=
          Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun c _ => hstep c
  -- B. pointwise mass-form weak Boppana on each pair
  have hB : ∀ d : γ × γ,
      K * (p (d.1, false) * condBit (p (d.2, false)) (p (d.2, true))
            + p (d.2, false) * condBit (p (d.1, false)) (p (d.1, true)))
        ≤ condBit (R₀ d) (R₁ d) :=
    fun d => massKey_of_weakBoppana hWB (hp _) (hp _) (hp _) (hp _)
  -- C. the bilinear collapse
  have hC : ∑ d : γ × γ,
      K * (p (d.1, false) * condBit (p (d.2, false)) (p (d.2, true))
            + p (d.2, false) * condBit (p (d.1, false)) (p (d.1, true)))
      = 2 * K * (∑ a, p (a, false)) * condH p := by
    have key2 : ∀ u v : γ → ℝ, ∑ d : γ × γ, u d.1 * v d.2 = (∑ a, u a) * ∑ b, v b := by
      intro u v
      rw [Fintype.sum_prod_type (f := fun d : γ × γ => u d.1 * v d.2)]
      dsimp only
      rw [← Finset.sum_mul_sum]
    have key2' : ∀ u v : γ → ℝ, ∑ d : γ × γ, v d.2 * u d.1 = (∑ a, u a) * ∑ b, v b := by
      intro u v
      rw [← key2 u v]
      exact Finset.sum_congr rfl fun d _ => mul_comm _ _
    rw [← Finset.mul_sum]
    unfold condH
    have hsplit : ∑ d : γ × γ,
        (p (d.1, false) * condBit (p (d.2, false)) (p (d.2, true))
          + p (d.2, false) * condBit (p (d.1, false)) (p (d.1, true)))
        = (∑ a, p (a, false)) * (∑ c, condBit (p (c, false)) (p (c, true)))
          + (∑ a, condBit (p (a, false)) (p (a, true))) * ∑ b, p (b, false) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact key2 (fun a => p (a, false)) fun b => condBit (p (b, false)) (p (b, true))
      · exact key2' (fun a => condBit (p (a, false)) (p (a, true))) fun b => p (b, false)
    rw [hsplit]
    ring
  calc 2 * K * (∑ a, p (a, false)) * condH p
      = ∑ d : γ × γ,
          K * (p (d.1, false) * condBit (p (d.2, false)) (p (d.2, true))
                + p (d.2, false) * condBit (p (d.1, false)) (p (d.1, true))) := hC.symm
    _ ≤ ∑ d : γ × γ, condBit (R₀ d) (R₁ d) := Finset.sum_le_sum fun d _ => hB d
    _ ≤ _ := hA

/-! ## Transport along equivalences -/

/-- Entropy is invariant under relabeling by an equivalence.
[MACHINE-VERIFIED.] -/
theorem entropy_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (p : α → ℝ) : entropy (p ∘ e.symm) = entropy p := by
  unfold entropy
  exact Equiv.sum_comp e.symm fun a => Real.negMulLog (p a)

/-- Being a pmf is invariant under relabeling. [MACHINE-VERIFIED.] -/
theorem isPMF_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    {p : α → ℝ} (hp : IsPMF p) : IsPMF (p ∘ e.symm) where
  nonneg b := hp.nonneg _
  sum_one := by
    have h := Equiv.sum_comp e.symm p
    calc ∑ b, (p ∘ e.symm) b = ∑ a, p a := h
      _ = 1 := hp.sum_one

/-- The two-sample pushforward transports along an equivalence intertwining
the binary operations. [MACHINE-VERIFIED.] -/
theorem pushforward₂_comp_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (f : α → α → α) (F : β → β → β)
    (hcompat : ∀ a b, e (f a b) = F (e a) (e b)) (p q : α → ℝ) :
    pushforward₂ F (p ∘ e.symm) (q ∘ e.symm) = pushforward₂ f p q ∘ e.symm := by
  funext c
  show (∑ x : β, ∑ y : β, if F x y = c then p (e.symm x) * q (e.symm y) else 0)
    = pushforward₂ f p q (e.symm c)
  rw [← Equiv.sum_comp e fun x : β =>
    ∑ y : β, if F x y = c then p (e.symm x) * q (e.symm y) else 0]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp e fun y : β =>
    if F (e a) y = c then p (e.symm (e a)) * q (e.symm y) else 0]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.symm_apply_apply, ← hcompat, Equiv.apply_eq_iff_eq_symm_apply]

/-! ## The coordinate induction over `Fin n → Bool` -/

/-- Pointwise OR on bit vectors: the union operation in indicator form.
[PROVED: definition.] -/
def orFun (n : ℕ) : (Fin n → Bool) → (Fin n → Bool) → Fin n → Bool :=
  fun f g i => f i || g i

/-- `i`-th marginal of a distribution on bit vectors. [PROVED: definition.] -/
noncomputable def bitMarginal {n : ℕ} (p : (Fin n → Bool) → ℝ) (i : Fin n) : ℝ :=
  ∑ f, if f i = true then p f else 0

/-- Splitting off coordinate `0` of a bit vector. [PROVED: definition.] -/
def splitEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ (Fin n → Bool) × Bool where
  toFun f := (Fin.tail f, f 0)
  invFun g := Fin.cons g.2 g.1
  left_inv f := Fin.cons_self_tail f
  right_inv g := by simp

/-- Coordinate-0 marginal in split form. [MACHINE-VERIFIED.] -/
theorem bitMarginal_zero_eq {n : ℕ} (p : (Fin (n + 1) → Bool) → ℝ) :
    bitMarginal p 0 = ∑ c, (p ∘ (splitEquiv n).symm) (c, true) := by
  unfold bitMarginal
  rw [← Equiv.sum_comp (splitEquiv n).symm fun f => if f 0 = true then p f else 0]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_bool]
  show (if (Fin.cons true c : Fin (n + 1) → Bool) 0 = true then p (Fin.cons true c) else 0)
      + (if (Fin.cons false c : Fin (n + 1) → Bool) 0 = true then p (Fin.cons false c) else 0)
    = p ((splitEquiv n).symm (c, true))
  simp [splitEquiv]

/-- Successor marginals in split form: marginals of the first-block marginal.
[MACHINE-VERIFIED.] -/
theorem bitMarginal_succ_eq {n : ℕ} (p : (Fin (n + 1) → Bool) → ℝ) (i : Fin n) :
    bitMarginal (fstMarg (p ∘ (splitEquiv n).symm)) i = bitMarginal p i.succ := by
  unfold bitMarginal
  rw [← Equiv.sum_comp (splitEquiv n).symm fun f => if f i.succ = true then p f else 0]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_bool]
  show (if c i = true then fstMarg (p ∘ (splitEquiv n).symm) c else 0)
    = (if (Fin.cons true c : Fin (n + 1) → Bool) i.succ = true
        then p (Fin.cons true c) else 0)
      + (if (Fin.cons false c : Fin (n + 1) → Bool) i.succ = true
        then p (Fin.cons false c) else 0)
  by_cases hc : c i = true
  · simp only [hc, if_true, Fin.cons_succ]
    show fstMarg (p ∘ (splitEquiv n).symm) c = _
    unfold fstMarg
    show p ((splitEquiv n).symm (c, false)) + p ((splitEquiv n).symm (c, true)) = _
    simp [splitEquiv]
    ring
  · simp [hc, Fin.cons_succ]

/-- Total complement mass of the split-off bit. [MACHINE-VERIFIED.] -/
theorem sum_false_eq_one_sub {n : ℕ} {p : (Fin (n + 1) → Bool) → ℝ} (hp : IsPMF p) :
    ∑ c, (p ∘ (splitEquiv n).symm) (c, false) = 1 - bitMarginal p 0 := by
  have hsum := (isPMF_comp_equiv (splitEquiv n) hp).sum_one
  rw [Fintype.sum_prod_type] at hsum
  have hexp : ∑ c, ∑ b, (p ∘ (splitEquiv n).symm) (c, b)
      = (∑ c, (p ∘ (splitEquiv n).symm) (c, false))
        + ∑ c, (p ∘ (splitEquiv n).symm) (c, true) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_bool]
    ring
  rw [hexp] at hsum
  rw [bitMarginal_zero_eq]
  linarith

/-- **The engine inequality, coordinate induction**: if every marginal of a
pmf `p` on bit vectors is at most `m`, then the OR-convolution square of `p`
has entropy at least `2K(1−m)·H(p)`, given `WeakBoppana K` and `0 ≤ K`.
[MACHINE-VERIFIED, given `WeakBoppana K`.] -/
theorem entropy_orPush_ge {K m : ℝ} (hK : 0 ≤ K) (hWB : WeakBoppana K) :
    ∀ (n : ℕ) (p : (Fin n → Bool) → ℝ), IsPMF p → (∀ i, bitMarginal p i ≤ m) →
      2 * K * (1 - m) * entropy p ≤ entropy (pushforward₂ (orFun n) p p) := by
  intro n
  induction n with
  | zero =>
    intro p hp _
    have hkey : ∀ q : (Fin 0 → Bool) → ℝ, IsPMF q → entropy q = 0 := by
      intro q hq
      have hone : q (fun i => i.elim0) = 1 := by
        have h := hq.sum_one
        rwa [Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)] at h
      unfold entropy
      rw [Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0), hone, Real.negMulLog_one]
    have hq : IsPMF (pushforward₂ (orFun 0) p p) := isPMF_pushforward₂ _ hp hp
    rw [hkey p hp, hkey _ hq]
    simp
  | succ n IH =>
    intro p hp hmarg
    set P : (Fin n → Bool) × Bool → ℝ := p ∘ (splitEquiv n).symm with hPdef
    have hPMF : IsPMF P := isPMF_comp_equiv (splitEquiv n) hp
    set F : ((Fin n → Bool) × Bool) → ((Fin n → Bool) × Bool) → (Fin n → Bool) × Bool :=
      fun x y => (orFun n x.1 y.1, x.2 || y.2) with hFdef
    have hcompat : ∀ f g : Fin (n + 1) → Bool,
        splitEquiv n (orFun (n + 1) f g) = F (splitEquiv n f) (splitEquiv n g) :=
      fun f g => rfl
    have hpush : pushforward₂ F P P = pushforward₂ (orFun (n + 1)) p p ∘ (splitEquiv n).symm :=
      pushforward₂_comp_equiv (splitEquiv n) (orFun (n + 1)) F hcompat p p
    have hentq : entropy (pushforward₂ F P P) = entropy (pushforward₂ (orFun (n + 1)) p p) := by
      rw [hpush]
      exact entropy_comp_equiv (splitEquiv n) _
    have hentp : entropy P = entropy p := entropy_comp_equiv (splitEquiv n) p
    -- chain rules on both sides
    have hchainP : entropy P = entropy (fstMarg P) + condH P :=
      entropy_eq_fstMarg_add_condH P
    have hchainQ : entropy (pushforward₂ F P P)
        = entropy (fstMarg (pushforward₂ F P P)) + condH (pushforward₂ F P P) :=
      entropy_eq_fstMarg_add_condH _
    have hS1 : fstMarg (pushforward₂ F P P)
        = pushforward₂ (orFun n) (fstMarg P) (fstMarg P) := fstMarg_orPush (orFun n) P
    -- induction hypothesis on the first-block marginal
    have hPM : IsPMF (fstMarg P) := isPMF_fstMarg hPMF
    have hmarg' : ∀ i, bitMarginal (fstMarg P) i ≤ m := fun i => by
      rw [bitMarginal_succ_eq]
      exact hmarg i.succ
    have hIH := IH (fstMarg P) hPM hmarg'
    -- the engine step on the split-off bit
    have hstep : 2 * K * (∑ a, P (a, false)) * condH P ≤ condH (pushforward₂ F P P) :=
      condH_orPush_ge hWB (orFun n) hPMF.nonneg
    -- the complement mass dominates 1 − m
    have hσ : 1 - m ≤ ∑ a, P (a, false) := by
      have h1 : ∑ a, P (a, false) = 1 - bitMarginal p 0 := sum_false_eq_one_sub hp
      have h2 := hmarg 0
      linarith
    have hcondH : 0 ≤ condH P := condH_nonneg hPMF.nonneg
    have hKc : 2 * K * (1 - m) * condH P ≤ 2 * K * (∑ a, P (a, false)) * condH P := by
      have h2K : 0 ≤ 2 * K := by linarith
      nlinarith [mul_nonneg h2K hcondH, hσ]
    calc 2 * K * (1 - m) * entropy p
        = 2 * K * (1 - m) * entropy (fstMarg P) + 2 * K * (1 - m) * condH P := by
          rw [← hentp, hchainP]; ring
      _ ≤ entropy (pushforward₂ (orFun n) (fstMarg P) (fstMarg P))
            + condH (pushforward₂ F P P) := by
          have := le_trans hKc hstep
          linarith [hIH]
      _ = entropy (pushforward₂ (orFun (n + 1)) p p) := by
          rw [← hS1, ← hchainQ, hentq]

/-! ## Transfer to set families and the engine -/

/-- Indicator equivalence between set families and bit vectors.
[PROVED: definition.] -/
def finsetBoolEquiv {n : ℕ} : Finset (Fin n) ≃ (Fin n → Bool) where
  toFun A := fun i => decide (i ∈ A)
  invFun f := Finset.univ.filter fun i => f i = true
  left_inv A := by ext i; simp
  right_inv f := by funext i; simp

/-- The indicator equivalence intertwines union and pointwise OR.
[MACHINE-VERIFIED.] -/
theorem finsetBoolEquiv_union {n : ℕ} (A B : Finset (Fin n)) :
    finsetBoolEquiv (A ∪ B) = orFun n (finsetBoolEquiv A) (finsetBoolEquiv B) := by
  funext i
  show decide (i ∈ A ∪ B) = (decide (i ∈ A) || decide (i ∈ B))
  simp [Finset.mem_union]

/-- Marginals transport along the indicator equivalence. [MACHINE-VERIFIED.] -/
theorem bitMarginal_finsetBoolEquiv {n : ℕ} (p : Finset (Fin n) → ℝ) (i : Fin n) :
    bitMarginal (p ∘ (finsetBoolEquiv (n := n)).symm) i = marginal p i := by
  unfold bitMarginal marginal
  rw [← Equiv.sum_comp (finsetBoolEquiv (n := n)) fun f =>
    if f i = true then (p ∘ (finsetBoolEquiv (n := n)).symm) f else 0]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp [finsetBoolEquiv]

/-- **The bridge**: the weak Boppana inequality at multiplier `K` implies
Gilmer's entropic engine at every threshold `c` with `1 < 2K(1−c)`.
[MACHINE-VERIFIED, given `WeakBoppana K`.] -/
theorem gilmerEngine_of_weakBoppana {K c : ℝ} (hK : 0 ≤ K) (hWB : WeakBoppana K)
    (hc : 1 < 2 * K * (1 - c)) : GilmerEngine c := by
  intro n p hpmf hent hmarg
  classical
  set P : (Fin n → Bool) → ℝ := p ∘ (finsetBoolEquiv (n := n)).symm with hPdef
  have hPMF : IsPMF P := isPMF_comp_equiv _ hpmf
  have hmargP : ∀ i, bitMarginal P i ≤ c := fun i => by
    rw [hPdef, bitMarginal_finsetBoolEquiv]
    exact (hmarg i).le
  have hmain := entropy_orPush_ge hK hWB n P hPMF hmargP
  have hentP : entropy P = entropy p := entropy_comp_equiv _ p
  have hcompat : ∀ A B : Finset (Fin n),
      finsetBoolEquiv (A ∪ B) = orFun n (finsetBoolEquiv A) (finsetBoolEquiv B) :=
    finsetBoolEquiv_union
  have hpush : pushforward₂ (orFun n) P P
      = pushforward₂ (· ∪ ·) p p ∘ (finsetBoolEquiv (n := n)).symm :=
    pushforward₂_comp_equiv _ (· ∪ ·) (orFun n) hcompat p p
  have hentQ : entropy (pushforward₂ (orFun n) P P)
      = entropy (pushforward₂ (· ∪ ·) p p) := by
    rw [hpush]
    exact entropy_comp_equiv _ _
  rw [hentP, hentQ] at hmain
  nlinarith [hmain, hent, hc]

/-- `WeakBoppana K` with `1 < 2K(1−c)` gives the union-closed conjecture with
constant `c`, end-to-end. [MACHINE-VERIFIED, given `WeakBoppana K`.] -/
theorem franklWithConstant_of_weakBoppana {K c : ℝ} (hK : 0 ≤ K)
    (hWB : WeakBoppana K) (hc : 1 < 2 * K * (1 - c)) : FranklWithConstant c := by
  have hc1 : c ≤ 1 := by nlinarith
  exact franklWithConstant_of_gilmerEngine hc1 (gilmerEngine_of_weakBoppana hK hWB hc)

/-- Gilmer's original constant: `WeakBoppana (11/20)` (47% numerical margin
below the sharp `φ/2 ≈ 0.809`) already gives the union-closed conjecture with
constant `1/100`. [MACHINE-VERIFIED, given `WeakBoppana (11/20)`.] -/
theorem franklWithConstant_centile_of_weakBoppana (hWB : WeakBoppana (11 / 20)) :
    FranklWithConstant (1 / 100) :=
  franklWithConstant_of_weakBoppana (by norm_num) hWB (by norm_num)

/-! ## Supremum closure and the golden constant -/

/-- `FranklWithConstant` is closed under suprema: if every constant below `c`
works, so does `c`. (Frequencies take finitely many values, so a maximal
counterexample frequency would already violate some smaller constant.)
[MACHINE-VERIFIED.] -/
theorem franklWithConstant_of_forall_lt {c : ℝ}
    (h : ∀ c' : ℝ, c' < c → FranklWithConstant c') : FranklWithConstant c := by
  intro n F hUC hne hne'
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no elements at all: F must be {∅}, excluded
    obtain ⟨A, hA⟩ := hne
    have hA0 : A = ∅ := Finset.eq_empty_of_isEmpty A
    refine hne' ?_
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hA0 ▸ hA, fun B hB => ?_⟩
    exact Finset.eq_empty_of_isEmpty B
  · have hcard : (0 : ℝ) < (F.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
      have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact Finset.univ_nonempty
    obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => freq F i) huniv
    have hr : (freq F i₀ : ℝ) < c * F.card := hcon i₀
    set c' : ℝ := ((freq F i₀ : ℝ) / F.card + c) / 2 with hc'def
    have hrc : (freq F i₀ : ℝ) / F.card < c := by
      rw [div_lt_iff₀ hcard]
      exact hr
    have hc' : c' < c := by
      rw [hc'def]
      linarith
    obtain ⟨j, hj⟩ := h c' hc' n F hUC hne hne'
    have h1 : (freq F j : ℝ) ≤ (freq F i₀ : ℝ) := by
      exact_mod_cast hmax j (Finset.mem_univ j)
    have h2 : (freq F i₀ : ℝ) < c' * F.card := by
      have hcc : c' * F.card = ((freq F i₀ : ℝ) + c * F.card) / 2 := by
        rw [hc'def]
        field_simp
      rw [hcc]
      linarith
    linarith

/-- The sharp constant `(1+√5)/4 = 1/(2φ) ≈ 0.809` of the two-variable
binary-entropy inequality (Chase–Lovett arXiv:2211.11689; one-variable
diagonal form Boppana arXiv:2301.09664). [PROVED: definition; `WeakBoppana`
at this constant is PROVED-in-literature, not formalized here.] -/
noncomputable def boppanaConst : ℝ := (1 + Real.sqrt 5) / 4

/-- **The golden theorem, kernel-checked modulo one scalar inequality**:
`WeakBoppana ((1+√5)/4)` implies the union-closed conjecture with constant
`ψ = (3−√5)/2` — the Gilmer–AHS–Chase–Lovett–Sawin–Pebody bound, with the
supremum closure absorbing the endpoint. [MACHINE-VERIFIED, given
`WeakBoppana boppanaConst`.] -/
theorem franklWithConstant_psi_of_weakBoppana (hWB : WeakBoppana boppanaConst) :
    FranklWithConstant psi := by
  apply franklWithConstant_of_forall_lt
  intro c hc
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hK : 0 ≤ boppanaConst := by
    unfold boppanaConst
    linarith
  apply franklWithConstant_of_weakBoppana hK hWB
  unfold boppanaConst
  unfold psi at hc
  have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by linarith
  have hgap : 0 < (1 - c) - (Real.sqrt 5 - 1) / 2 := by linarith
  nlinarith [mul_pos hpos hgap, h5]

end UCFrankl
