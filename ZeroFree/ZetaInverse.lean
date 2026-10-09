/-
Adapted from OpenAI/math Hecke/Signal.lean under Apache-2.0.
Upstream revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
Upstream raw SHA-256: ec7a4403c352dee276850ea4418122c03dd3a5bc108ac8352fcd866578be36f6
Changes by Li Xiang / lixiang90 (2026-10-09): actual Mathlib zeta in place
of the Hecke character; reciprocal bound proved from the Moebius series;
use sigmaStar for the correction domain. No arithmetic probe bound is assumed
in the construction, integrability, or origin-decay lemmas.
-/

import ZeroFree.ZetaConcrete
import ZeroFree.ContinuationContour

namespace ZeroFree

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology FourierTransform
namespace ZetaInverse
open Continuation

def quotient (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  H s * (riemannZeta s)⁻¹

def amplitude (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5/6)^2) * quotient H s

def signal (H : ℂ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ)^(c : ℂ) * mellinInv (-2) (fun s => amplitude H (-s)) x

private theorem isOpen_re_gt (a : ℝ) : IsOpen {s : ℂ | a < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

def reciprocalBound : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (fun k => (ArithmeticFunction.moebius k : ℂ)) 2 n‖

theorem reciprocalBound_nonneg : 0 ≤ reciprocalBound := tsum_nonneg (fun _ => norm_nonneg _)

theorem reciprocal_eq_moebius {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = LSeries (fun k => (ArithmeticFunction.moebius k : ℂ)) s := by
  have h := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at h
  apply (mul_left_cancel₀ (riemannZeta_ne_zero_of_one_lt_re hs))
  simpa [riemannZeta_ne_zero_of_one_lt_re hs] using h.symm

theorem reciprocal_norm_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ reciprocalBound := by
  have hs1 : 1 < s.re := by linarith
  rw [reciprocal_eq_moebius hs1]
  have hsum : LSeriesSummable (fun k => (ArithmeticFunction.moebius k : ℂ)) 2 :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)
  have hsum' := hsum.of_re_le_re (by simpa using hs)
  apply (norm_tsum_le_tsum_norm hsum'.norm).trans
  apply Summable.tsum_le_tsum
  · intro n
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n
  · exact hsum'.norm
  · exact hsum.norm

theorem quotient_differentiableAt (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re}) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (quotient H) s := by
  have h1 : s ≠ 1 := by intro heq; simp [heq] at hs
  exact (hH.differentiableAt ((isOpen_re_gt sigmaStar).mem_nhds
    (by linarith [sigmaStar_lt_seven_eighths] : sigmaStar < s.re))).mul
      ((differentiableAt_riemannZeta h1).inv (riemannZeta_ne_zero_of_one_lt_re hs))

theorem quotient_bound (H : ℂ → ℂ)
    (hH : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2)
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖quotient H s‖ ≤ (3/2) * reciprocalBound := by
  have hn : ‖H s‖ ≤ 3/2 := by
    have h := norm_add_le (H s - 1) (1 : ℂ)
    have h' := hH s (by linarith [sigmaStar_lt_seven_eighths])
    simp only [sub_add_cancel, norm_one] at h
    linarith
  unfold quotient
  rw [norm_mul]
  exact mul_le_mul hn (reciprocal_norm_le hs)
    (norm_nonneg _) (by norm_num)

theorem normalizedSignal_eq (H : ℂ → ℂ) (c : ℝ)
    {x : ℝ} (hx : 0 < x) :
    normalizedSignal (signal H c) c x =
      mellinInv (-2) (fun s => amplitude H (-s)) x := by
  unfold normalizedSignal signal
  simp only [smul_eq_mul, ← mul_assoc]
  rw [Complex.cpow_neg, inv_mul_cancel₀]
  · simp
  · exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hx.ne'])

theorem signal_eq_contour (H : ℂ → ℂ) (c : ℝ)
    {x : ℝ} (hx : 0 < x) :
    signal H c x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (quotient H) c x ((2 : ℂ) + y * I) := by
  unfold signal mellinInv
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with y
  unfold gaussianContourIntegrand amplitude
  have he : -(((-2 : ℝ) : ℂ) + (-y : ℝ) * I) = (2 : ℂ) + y * I := by push_cast; ring
  rw [he, ← mul_assoc, ← Complex.cpow_add]
  · ring_nf
  · exact Complex.ofReal_ne_zero.mpr hx.ne'

def quotientBound : ℝ := (3/2) * reciprocalBound

theorem quotientBound_nonneg : 0 ≤ quotientBound := by
  unfold quotientBound
  exact mul_nonneg (by norm_num) reciprocalBound_nonneg

theorem amplitude_continuous_line (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re}) (a : ℝ) (ha : 1 < a) :
    Continuous (fun y : ℝ => amplitude H ((a : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : DifferentiableAt ℂ (amplitude H) ((a : ℂ) + y * I) := by
    unfold amplitude
    exact (((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul
      (quotient_differentiableAt H hH (by simpa using ha))
  have hm : Continuous (fun v : ℝ => (a : ℂ) + v * I) := by fun_prop
  exact hd.continuousAt.comp (f := fun v : ℝ => (a : ℂ) + v * I) hm.continuousAt

theorem amplitude_norm_bound (H : ℂ → ℂ)
    (hH : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2)
    (a y : ℝ) (ha : 2 ≤ a) :
    ‖amplitude H ((a : ℂ) + y * I)‖ ≤
      (Real.exp ((a-5/6)^2) * quotientBound) * Real.exp (-(y^2)) := by
  have hn := norm_gaussianContourIntegrand (quotient H) 0 a y (Z := 1) zero_lt_one
  simp only [gaussianContourIntegrand, Complex.ofReal_one, Complex.ofReal_zero,
    add_zero, Complex.one_cpow, one_mul, Real.one_rpow] at hn
  change ‖amplitude H ((a : ℂ) + y * I)‖ = _ at hn
  rw [hn]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (quotient_bound H hH (by simpa using ha))
      (Real.exp_pos _).le) (Real.exp_pos _).le

theorem amplitude_integrable_line (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2)
    (a : ℝ) (ha : 2 ≤ a) : Integrable (fun y : ℝ => amplitude H ((a : ℂ) + y * I)) :=
  integrable_of_gaussian_bound _ _
    (amplitude_continuous_line H hH a (by linarith)).aestronglyMeasurable
    (fun y => amplitude_norm_bound H hb a y ha)

theorem contour_shift (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2)
    (c B : ℝ) (hB : 2 ≤ B) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    signal H c x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (quotient H) c x ((B : ℂ) + y * I) := by
  rw [signal_eq_contour H c hx]
  congr 1
  apply vertical_integral_eq_of_gaussian_bound (C :=
    x^(2+c) * Real.exp ((B-5/6)^2) * quotientBound) _ hB
  · apply gaussianContourIntegrand_differentiableOn _ c hx
    intro z hz
    exact (quotient_differentiableAt H hH (by linarith [hz.1])).differentiableWithinAt
  · intro a ha y
    rw [norm_gaussianContourIntegrand _ _ _ _ hx]
    have hxpow : x^(a+c) ≤ x^(2+c) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [ha.1])
    have hexp : Real.exp ((a-5/6)^2) ≤ Real.exp ((B-5/6)^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha.1, ha.2]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul _ (quotient_bound H hb (by simpa using ha.1)) (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)
    exact mul_le_mul hxpow hexp (Real.exp_pos _).le (Real.rpow_nonneg hx.le _)

def endpointConstant (B : ℝ) : ℝ :=
  ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((B-5/6)^2) * quotientBound *
    ∫ y : ℝ, Real.exp (-(y^2))

theorem endpointConstant_nonneg (B : ℝ) : 0 ≤ endpointConstant B := by
  unfold endpointConstant
  have hq := quotientBound_nonneg
  have hg : 0 ≤ ∫ y : ℝ, Real.exp (-(y^2)) := integral_nonneg (fun _ => (Real.exp_pos _).le)
  positivity

theorem signal_bound_at_zero (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2)
    (c B : ℝ) (hB : 2 ≤ B) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖signal H c x‖ ≤ endpointConstant B * x^(B+c) := by
  rw [contour_shift H hH hb c B hB hx hx1, norm_mul]
  have hg : Integrable (fun y : ℝ => Real.exp (-(y^2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hint := norm_integral_le_of_norm_le
    (hg.const_mul (x^(B+c) * Real.exp ((B-5/6)^2) * quotientBound))
    (f := fun y : ℝ => gaussianContourIntegrand (quotient H) c x ((B : ℂ) + y * I))
    (ae_of_all _ (fun y => by
      rw [norm_gaussianContourIntegrand _ _ _ _ hx]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (quotient_bound H hb (by simpa using hB))
        (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le)))
  have h := mul_le_mul_of_nonneg_left hint (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at h
  simpa only [endpointConstant, mul_assoc, mul_left_comm, mul_comm] using h

theorem signal_rapidDecayAtZero (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2)
    (c : ℝ) : RapidDecayAtZero (signal H c) := by
  intro R
  let B : ℝ := max 2 (R-c)
  apply IsBigO.of_bound (endpointConstant B)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx hx1
  have hpow : x^(B+c) ≤ x^R :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 (by dsimp [B]; linarith [le_max_right (2 : ℝ) (R-c)])
  have h := (signal_bound_at_zero H hH hb c B (le_max_left _ _) hx hx1).trans
    (mul_le_mul_of_nonneg_left hpow (endpointConstant_nonneg B))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le R)] using h

theorem amplitude_integrable_reflected (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2) :
    Integrable (fun y : ℝ => amplitude H ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (amplitude_integrable_line H hH hb 2 le_rfl).comp_mul_left'
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem amplitude_continuous_reflected (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re}) :
    Continuous (fun y : ℝ => amplitude H ((2 : ℂ) - 2 * Real.pi * y * I)) := by
  have h := (amplitude_continuous_line H hH 2 (by norm_num)).comp
    (show Continuous (fun y : ℝ => -(2*Real.pi)*y) by fun_prop)
  convert h using 1
  ext y
  congr 1
  push_cast
  ring

theorem signal_continuousOn (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2) (c : ℝ) :
    ContinuousOn (signal H c) (Ioi 0) := by
  let F : ℝ → ℂ := fun y => amplitude H (-(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I))
  have harg (y : ℝ) : -(((-2 : ℝ) : ℂ) + 2 * Real.pi * y * I) =
      (2 : ℂ) - 2 * Real.pi * y * I := by push_cast; ring
  have hF : Integrable F := by
    simpa only [F, harg] using amplitude_integrable_reflected H hH hb
  have hfour : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hF
  have hinv : Continuous (𝓕⁻ F) := by
    have heq : 𝓕⁻ F = fun w : ℝ => 𝓕 F (-w) := funext (Real.fourierInv_eq_fourier_neg F)
    rw [heq]
    exact hfour.comp continuous_neg
  have hpow (z : ℂ) : ContinuousOn (fun x : ℝ => (x : ℂ)^z) (Ioi 0) :=
    Complex.continuous_ofReal.continuousOn.cpow_const (fun _ hx => Complex.ofReal_mem_slitPlane.mpr hx)
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (Ioi 0) := by
    intro x hx
    exact (Real.continuousAt_log hx.ne').neg.continuousWithinAt
  apply ((hpow (c : ℂ)).mul ((hpow (2 : ℂ)).mul (hinv.comp_continuousOn hlog))).congr
  intro x hx
  unfold signal
  rw [mellinInv_eq_fourierInv _ _ hx]
  simp only [smul_eq_mul, Complex.ofReal_neg, neg_neg, Complex.ofReal_ofNat,
    F, Pi.mul_apply, Function.comp_apply]

theorem signal_locallyIntegrable (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2) (c : ℝ) :
    LocallyIntegrableOn (signal H c) (Ioi 0) :=
  (signal_continuousOn H hH hb c).locallyIntegrableOn measurableSet_Ioi

theorem signalMellin_eq_amplitude_on_line (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2) (c a : ℝ) (ha : a < 2)
    (htop : signal H c =O[atTop] (fun x : ℝ => x^(a+c))) (y : ℝ) :
    signalMellin (signal H c) c ((2 : ℂ) - 2 * Real.pi * y * I) =
      amplitude H ((2 : ℂ) - 2 * Real.pi * y * I) := by
  apply signalMellin_eq_on_line _ _ c 2
    (signalMellin_convergent _ a c (signal_locallyIntegrable H hH hb c) htop
      (signal_rapidDecayAtZero H hH hb c) (by simpa using ha))
    (amplitude_integrable_reflected H hH hb) (amplitude_continuous_reflected H hH)
  intro x hx
  exact normalizedSignal_eq H c hx

end ZetaInverse

end

end ZeroFree
