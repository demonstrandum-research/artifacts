import Mathlib
import UCFrankl.EngineReduction
import UCFrankl.HoBoppana

/-!
# The diagonal reduction and the unconditional kernel ψ-theorem

Program UC, lens C3L1 (campaign C3, 2026-06-13). C2L4 left the program with
the entire Gilmer line kernel-checked modulo ONE scalar atom:

  `WeakBoppana K : ∀ x y ∈ [0,1], K(x·h(y) + y·h(x)) ≤ h(xy)`.

This file CLOSES that atom at the sharp constant `K = (1+√5)/4` and derives —
to our knowledge the first (novelty CONJECTURED(strong), two sweeps,
2026-06-13; nearest prior art: Hachimori–Kashiwabara arXiv:2504.13454,
averaged ideal-family fragment; Marić et al., Coq/Isabelle FC-families) —
a kernel-checked proof of a universal positive constant for Frankl's
union-closed sets conjecture, at the state-of-the-art ψ. Two ingredients:

1. **The diagonal-reduction lemma** (`mul_binEntropy_add_le`, new
   formalization following Chase–Lovett arXiv:2211.11689): for `x,y ∈ [0,1]`,
   `x·h(y) + y·h(x) ≤ 2·√(xy)·h(√(xy))`. Proof: in coordinates `u = −ln x`,
   the inequality is exactly midpoint concavity of
   `η(u) = eᵘ·negMulLog(1−e^{−u})`, and `η'' ≤ 0` reduces to the standard
   bound `ln t ≤ t − 1`. (The binEntropy "−xy·ln(xy)" parts of the two sides
   are exactly EQUAL; the inequality lives entirely in the `(1−·)ln(1−·)`
   parts.)

2. **The sharp one-variable atom** (`sharp_boppana_diag`): Boppana's
   `h(t²) ≥ ((1+√5)/2)·t·h(t)`, extracted as the `k = 2` case of Ho's
   generalized inequality (`HoBoppana.generalized_boppana`, vendored port of
   arXiv:2601.19327, MIT).

Composition: `K(xh(y)+yh(x)) ≤ 2K·s·h(s) ≤ h(s²) = h(xy)` with `s = √(xy)`,
`2K = (1+√5)/2`. Then the C2L4 bridge gives the headline theorems.

## EPISTEMIC-STATUS LEDGER (program law)

* Every `theorem`/`lemma` in this file: MACHINE-VERIFIED once `lake build`
  passes and `scripts/CheckAxioms.lean` reports standard axioms only.
* `franklWithConstant_psi : FranklWithConstant psi` — UNCONDITIONAL: no
  hypothesis beyond the imports' axioms. The mathematics is
  Gilmer–AHS–Chase–Lovett–Sawin–Pebody (the ψ-theorem) + Boppana/Ho (the
  atom); the formalization is the contribution, not the bound.
* `franklWithConstant_centile : FranklWithConstant (1/100)` — Gilmer's
  original constant, unconditional.
-/

namespace UCFrankl

open Real

/-! ## The comparison function η and its concavity -/

/-- The Chase–Lovett comparison function `η(u) = eᵘ·negMulLog(1 − e^{−u})`
(`= −(eᵘ−1)·ln(1−e^{−u})` for `u > 0`, continuously extended by `η(0) = 0`).
Multiplicative-midpoint concavity of `t ↦ negMulLog(1−t)/t` in disguise.
[PROVED: definition.] -/
noncomputable def etaCL (u : ℝ) : ℝ := Real.exp u * Real.negMulLog (1 - Real.exp (-u))

/-- `η` is continuous (the `negMulLog` form absorbs the `0·log 0` boundary).
[MACHINE-VERIFIED.] -/
lemma continuous_etaCL : Continuous etaCL :=
  Real.continuous_exp.mul
    (Real.continuous_negMulLog.comp (continuous_const.sub (Real.continuous_exp.comp continuous_neg)))

/-- For `u > 0` the inner argument `1 − e^{−u}` is positive. [MACHINE-VERIFIED.] -/
lemma one_sub_exp_neg_pos {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-u) := by
  have h : Real.exp (-u) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_zero] at h
  linarith

/-- Derivative of the inner function `w ↦ 1 − e^{−w}`. [MACHINE-VERIFIED.] -/
lemma hasDerivAt_inner (u : ℝ) :
    HasDerivAt (fun w : ℝ => 1 - Real.exp (-w)) (Real.exp (-u)) u := by
  have h1 : HasDerivAt (fun w : ℝ => -w) (-1 : ℝ) u := (hasDerivAt_id u).neg
  have h2 : HasDerivAt (fun w : ℝ => Real.exp (-w)) (Real.exp (-u) * (-1)) u :=
    (Real.hasDerivAt_exp (-u)).comp u h1
  have h3 := h2.const_sub 1
  convert h3 using 1
  ring

/-- `η'(u) = −eᵘ·ln(1−e^{−u}) − 1` for `u > 0`. [MACHINE-VERIFIED.] -/
lemma hasDerivAt_etaCL {u : ℝ} (hu : 0 < u) :
    HasDerivAt etaCL (-Real.exp u * Real.log (1 - Real.exp (-u)) - 1) u := by
  have hz := one_sub_exp_neg_pos hu
  have hcomp : HasDerivAt (fun w : ℝ => Real.negMulLog (1 - Real.exp (-w)))
      ((-Real.log (1 - Real.exp (-u)) - 1) * Real.exp (-u)) u := by
    have h := (Real.hasDerivAt_negMulLog hz.ne').comp u (hasDerivAt_inner u)
    simpa [Function.comp_def] using h
  have hprod := (Real.hasDerivAt_exp u).mul hcomp
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  convert hprod using 1
  unfold Real.negMulLog
  linear_combination he

/-- `η''(u) = −eᵘ·ln(1−e^{−u}) − 1/(1−e^{−u})` for `u > 0`. [MACHINE-VERIFIED.] -/
lemma hasDerivAt_etaCL' {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun w : ℝ => -Real.exp w * Real.log (1 - Real.exp (-w)) - 1)
      (-Real.exp u * Real.log (1 - Real.exp (-u)) - 1 / (1 - Real.exp (-u))) u := by
  have hz := one_sub_exp_neg_pos hu
  have hlog : HasDerivAt (fun w : ℝ => Real.log (1 - Real.exp (-w)))
      (Real.exp (-u) / (1 - Real.exp (-u))) u := (hasDerivAt_inner u).log hz.ne'
  have hneg : HasDerivAt (fun w : ℝ => -Real.exp w) (-Real.exp u) u :=
    (Real.hasDerivAt_exp u).neg
  have h := (hneg.mul hlog).sub_const 1
  have he : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  convert h using 1
  have hcalc : Real.exp u * (Real.exp (-u) / (1 - Real.exp (-u)))
      = 1 / (1 - Real.exp (-u)) := by
    rw [← mul_div_assoc, he]
  linarith [hcalc]

/-- **The scalar heart**: `η'' ≤ 0` on `(0,∞)` — equivalent to the standard
log bound `ln(1/w) ≤ (1−w)/w`. [MACHINE-VERIFIED.] -/
lemma etaCL''_nonpos {u : ℝ} (hu : 0 < u) :
    -Real.exp u * Real.log (1 - Real.exp (-u)) - 1 / (1 - Real.exp (-u)) ≤ 0 := by
  have hw0 : 0 < 1 - Real.exp (-u) := one_sub_exp_neg_pos hu
  have hkey : -Real.log (1 - Real.exp (-u)) ≤ (1 - Real.exp (-u))⁻¹ - 1 := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hw0)
    rwa [Real.log_inv] at h
  have hE : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  rw [sub_nonpos, le_div_iff₀ hw0]
  -- goal: (−eᵘ·ln w)·w ≤ 1 with w = 1 − e^{−u}
  have h4 : (-Real.log (1 - Real.exp (-u))) * (Real.exp u * (1 - Real.exp (-u)))
      ≤ ((1 - Real.exp (-u))⁻¹ - 1) * (Real.exp u * (1 - Real.exp (-u))) :=
    mul_le_mul_of_nonneg_right hkey (by positivity)
  have h5 : ((1 - Real.exp (-u))⁻¹ - 1) * (Real.exp u * (1 - Real.exp (-u)))
      = Real.exp u * Real.exp (-u) := by
    field_simp
    ring
  calc -Real.exp u * Real.log (1 - Real.exp (-u)) * (1 - Real.exp (-u))
      = (-Real.log (1 - Real.exp (-u))) * (Real.exp u * (1 - Real.exp (-u))) := by ring
    _ ≤ Real.exp u * Real.exp (-u) := by rw [← h5]; exact h4
    _ = 1 := hE

/-- `η` is concave on `[0,∞)`. [MACHINE-VERIFIED.] -/
lemma concaveOn_etaCL : ConcaveOn ℝ (Set.Ici (0 : ℝ)) etaCL := by
  have hev : ∀ u : ℝ, 0 < u → deriv etaCL =ᶠ[nhds u]
      (fun w : ℝ => -Real.exp w * Real.log (1 - Real.exp (-w)) - 1) := by
    intro u hu
    filter_upwards [isOpen_Ioi.mem_nhds hu] with y hy
    exact (hasDerivAt_etaCL hy).deriv
  apply concaveOn_of_deriv2_nonpos (convex_Ici 0) continuous_etaCL.continuousOn
  · rw [interior_Ici]
    intro u hu
    exact (hasDerivAt_etaCL hu).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro u hu
    exact ((hasDerivAt_etaCL' hu).differentiableAt.congr_of_eventuallyEq
      (hev u hu)).differentiableWithinAt
  · rw [interior_Ici]
    intro u hu
    show deriv (deriv etaCL) u ≤ 0
    rw [Filter.EventuallyEq.deriv_eq (hev u hu), (hasDerivAt_etaCL' hu).deriv]
    exact etaCL''_nonpos hu

/-- Midpoint form of η-concavity. [MACHINE-VERIFIED.] -/
lemma etaCL_add_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    etaCL u + etaCL v ≤ 2 * etaCL ((u + v) / 2) := by
  have h := concaveOn_etaCL.2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have harg : (1/2 : ℝ) * u + (1/2 : ℝ) * v = (u + v) / 2 := by ring
  rw [harg] at h
  linarith

/-! ## Transfer back to `[0,1]`: the diagonal-reduction lemma -/

/-- The transfer identity `x·η(−ln x) = negMulLog(1−x)` for `x > 0`.
[MACHINE-VERIFIED.] -/
lemma mul_etaCL_neg_log {x : ℝ} (hx : 0 < x) :
    x * etaCL (-Real.log x) = Real.negMulLog (1 - x) := by
  unfold etaCL
  rw [neg_neg, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]
  rw [← mul_assoc, mul_inv_cancel₀ hx.ne', one_mul]

/-- The `(1−·)`-part of the diagonal reduction:
`x·negMulLog(1−y) + y·negMulLog(1−x) ≤ 2√(xy)·negMulLog(1−√(xy))`.
[MACHINE-VERIFIED.] -/
lemma negMulLog_one_sub_diag {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    x * Real.negMulLog (1 - y) + y * Real.negMulLog (1 - x)
      ≤ 2 * Real.sqrt (x * y) * Real.negMulLog (1 - Real.sqrt (x * y)) := by
  have hu : 0 ≤ -Real.log x := neg_nonneg.2 (Real.log_nonpos hx0.le hx1)
  have hv : 0 ≤ -Real.log y := neg_nonneg.2 (Real.log_nonpos hy0.le hy1)
  have hxy : 0 < x * y := mul_pos hx0 hy0
  have hs0 : 0 < Real.sqrt (x * y) := Real.sqrt_pos.2 hxy
  have hslog : -Real.log (Real.sqrt (x * y)) = (-Real.log x + -Real.log y) / 2 := by
    rw [Real.log_sqrt hxy.le, Real.log_mul hx0.ne' hy0.ne']
    ring
  have hmid := etaCL_add_le hu hv
  have h1 : x * y * (etaCL (-Real.log x) + etaCL (-Real.log y))
      ≤ x * y * (2 * etaCL ((-Real.log x + -Real.log y) / 2)) :=
    mul_le_mul_of_nonneg_left hmid hxy.le
  have hA : x * y * etaCL (-Real.log x) = y * Real.negMulLog (1 - x) := by
    have hid := mul_etaCL_neg_log hx0
    calc x * y * etaCL (-Real.log x) = y * (x * etaCL (-Real.log x)) := by ring
      _ = y * Real.negMulLog (1 - x) := by rw [hid]
  have hB : x * y * etaCL (-Real.log y) = x * Real.negMulLog (1 - y) := by
    have hid := mul_etaCL_neg_log hy0
    calc x * y * etaCL (-Real.log y) = x * (y * etaCL (-Real.log y)) := by ring
      _ = x * Real.negMulLog (1 - y) := by rw [hid]
  have hC : x * y * (2 * etaCL ((-Real.log x + -Real.log y) / 2))
      = 2 * Real.sqrt (x * y) * Real.negMulLog (1 - Real.sqrt (x * y)) := by
    have hid := mul_etaCL_neg_log hs0
    rw [hslog] at hid
    have hss : Real.sqrt (x * y) * Real.sqrt (x * y) = x * y := Real.mul_self_sqrt hxy.le
    linear_combination (-2 : ℝ) * etaCL ((-Real.log x + -Real.log y) / 2) * hss
      + 2 * Real.sqrt (x * y) * hid
  rw [mul_add, hA, hB, hC] at h1
  linarith

/-- **The Chase–Lovett diagonal-reduction lemma** (arXiv:2211.11689, here
formalized): for `x, y ∈ [0,1]`,
`x·h(y) + y·h(x) ≤ 2·√(xy)·h(√(xy))` with `h = Real.binEntropy`.
The two-variable inequality is dominated by its value on the diagonal.
[MACHINE-VERIFIED.] -/
theorem mul_binEntropy_add_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    x * Real.binEntropy y + y * Real.binEntropy x
      ≤ 2 * Real.sqrt (x * y) * Real.binEntropy (Real.sqrt (x * y)) := by
  rcases eq_or_lt_of_le hx0 with rfl | hx0'
  · simp
  rcases eq_or_lt_of_le hy0 with rfl | hy0'
  · simp
  have hxy : 0 < x * y := mul_pos hx0' hy0'
  have hpsi := negMulLog_one_sub_diag hx0' hx1 hy0' hy1
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hlogpart : x * Real.negMulLog y + y * Real.negMulLog x
      = 2 * Real.sqrt (x * y) * Real.negMulLog (Real.sqrt (x * y)) := by
    have hss : Real.sqrt (x * y) * Real.sqrt (x * y) = x * y := Real.mul_self_sqrt hxy.le
    unfold Real.negMulLog
    rw [Real.log_sqrt hxy.le, Real.log_mul hx0'.ne' hy0'.ne']
    linear_combination (Real.log x + Real.log y) * hss
  nlinarith [hpsi, hlogpart]

/-! ## The sharp atom from Ho's `k = 2` case -/

/-- `alpha 2 = (√5 − 1)/2 = 1/φ` — identification of Ho's implicit constant
at `k = 2`. [MACHINE-VERIFIED.] -/
lemma hoAlpha_two : HoBoppana.alpha 2 = (Real.sqrt 5 - 1) / 2 := by
  obtain ⟨hpos, hspec⟩ := HoBoppana.alpha_spec 2 (by norm_num)
  rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one] at hspec
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hfac : (HoBoppana.alpha 2 - (Real.sqrt 5 - 1) / 2)
      * (HoBoppana.alpha 2 + (Real.sqrt 5 + 1) / 2) = 0 := by
    linear_combination hspec - h5 / 4
  rcases mul_eq_zero.1 hfac with h | h
  · linarith
  · nlinarith [hpos, h5']

/-- **The sharp one-variable Boppana atom** (Boppana arXiv:2301.09664; here
obtained as the `k = 2` case of Ho arXiv:2601.19327, vendored port):
`((1+√5)/2)·t·h(t) ≤ h(t²)` for `t ∈ [0,1]`. Equality at `t = 1/φ`.
[MACHINE-VERIFIED.] -/
theorem sharp_boppana_diag {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + Real.sqrt 5) / 2 * (t * Real.binEntropy t) ≤ Real.binEntropy (t * t) := by
  have hHo := HoBoppana.generalized_boppana 2 (by norm_num) t ⟨ht0, ht1⟩
  rw [hoAlpha_two, show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      show t ^ (2:ℝ) = t * t by
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]; ring] at hHo
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hc : (0:ℝ) ≤ (1 + Real.sqrt 5) / 2 := by positivity
  have h1 : t * Real.binEntropy t ≤ (Real.sqrt 5 - 1) / 2 * Real.binEntropy (t * t) := hHo
  have h2 := mul_le_mul_of_nonneg_left h1 hc
  have h3 : (1 + Real.sqrt 5) / 2 * ((Real.sqrt 5 - 1) / 2 * Real.binEntropy (t * t))
      = Real.binEntropy (t * t) := by
    linear_combination Real.binEntropy (t * t) * h5 / 4
  linarith

/-! ## The atom closed: `WeakBoppana` at the sharp constant -/

/-- **The two-variable scalar atom, kernel-proved at the sharp constant**:
`WeakBoppana ((1+√5)/4)`. This was the single residual hypothesis of the
C2L4 bridge. [MACHINE-VERIFIED.] -/
theorem weakBoppana_sharp : WeakBoppana boppanaConst := by
  intro x hx0 hx1 y hy0 hy1
  have hdiag := mul_binEntropy_add_le hx0 hx1 hy0 hy1
  have hxy0 : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxy1 : x * y ≤ 1 := mul_le_one₀ hx1 hy0 hy1
  have hs0 : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (x * y) ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hxy1
  have hatom := sharp_boppana_diag hs0 hs1
  rw [Real.mul_self_sqrt hxy0] at hatom
  have hK : (0:ℝ) ≤ boppanaConst := by
    unfold boppanaConst
    positivity
  have h1 := mul_le_mul_of_nonneg_left hdiag hK
  have h2 : boppanaConst * (2 * Real.sqrt (x * y) * Real.binEntropy (Real.sqrt (x * y)))
      = (1 + Real.sqrt 5) / 2 * (Real.sqrt (x * y) * Real.binEntropy (Real.sqrt (x * y))) := by
    unfold boppanaConst
    ring
  rw [h2] at h1
  linarith

/-- `WeakBoppana` is downward monotone in the multiplier. [MACHINE-VERIFIED.] -/
theorem weakBoppana_mono {K K' : ℝ} (h0 : 0 ≤ K') (hKK : K' ≤ K)
    (hWB : WeakBoppana K) : WeakBoppana K' := by
  intro x hx0 hx1 y hy0 hy1
  have hnn : 0 ≤ x * Real.binEntropy y + y * Real.binEntropy x :=
    add_nonneg (mul_nonneg hx0 (Real.binEntropy_nonneg hy0 hy1))
      (mul_nonneg hy0 (Real.binEntropy_nonneg hx0 hx1))
  exact le_trans (mul_le_mul_of_nonneg_right hKK hnn) (hWB x hx0 hx1 y hy0 hy1)

/-- The fallback multiplier `11/20`, now unconditional. [MACHINE-VERIFIED.] -/
theorem weakBoppana_eleven_twentieths : WeakBoppana (11 / 20) := by
  refine weakBoppana_mono (by norm_num) ?_ weakBoppana_sharp
  unfold boppanaConst
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]

/-! ## The headline theorems: unconditional kernel Frankl constants -/

/-- Gilmer's entropic engine holds unconditionally for every `c < ψ`.
[MACHINE-VERIFIED.] -/
theorem gilmerEngine_of_lt_psi {c : ℝ} (hc : c < psi) : GilmerEngine c := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hK : 0 ≤ boppanaConst := by
    unfold boppanaConst
    linarith
  apply gilmerEngine_of_weakBoppana hK weakBoppana_sharp
  unfold boppanaConst
  unfold psi at hc
  have hpos : (0 : ℝ) < 1 + Real.sqrt 5 := by linarith
  have hgap : 0 < (1 - c) - (Real.sqrt 5 - 1) / 2 := by linarith
  nlinarith [mul_pos hpos hgap, h5]

/-- **THE UNCONDITIONAL KERNEL ψ-THEOREM**: every finite union-closed family
(≠ {∅}) has an element in at least `ψ = (3−√5)/2 ≈ 0.38197` of its sets —
the Gilmer–AHS–Chase–Lovett–Sawin–Pebody bound, end-to-end in the kernel
with NO open hypothesis. [MACHINE-VERIFIED.] -/
theorem franklWithConstant_psi : FranklWithConstant psi :=
  franklWithConstant_psi_of_weakBoppana weakBoppana_sharp

/-- Gilmer's original constant `1/100`, unconditional. [MACHINE-VERIFIED.] -/
theorem franklWithConstant_centile : FranklWithConstant (1 / 100) :=
  franklWithConstant_centile_of_weakBoppana weakBoppana_eleven_twentieths

end UCFrankl
