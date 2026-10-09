/-
Adapted from OpenAI/math Hecke/SignalIdentity.lean under Apache-2.0.
Upstream revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
Upstream raw SHA-256: 2ff1e2aab2956d512457f121068804d65b34d790ab70520f2836041c44776c2e
Changes by Li Xiang / lixiang90 (2026-10-09): actual Mathlib zeta and
sigmaStar; connect the constructed inverse Mellin signal to raw probe estimates.
-/
import ZeroFree.ZetaInverse
import Mathlib.Analysis.Analytic.IsolatedZeros

set_option autoImplicit false

noncomputable section
namespace ZeroFree.ZetaInverse
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open Continuation

private theorem isOpen_re_gt (a : ℝ) : IsOpen {s : ℂ | a < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem line_tendsto_punctured :
    Tendsto (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Continuous (fun y : ℝ => (2 : ℂ) - 2 * Real.pi * y * I) := by fun_prop
    simpa using (h.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hy (by nlinarith [Real.pi_pos])

theorem signalMellin_eq_amplitude (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s - 1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    signalMellin (signal H c) c s = amplitude H s := by
  have hF := signalMellin_analytic (signal H c) a c
    (signal_locallyIntegrable H hH hb c) htop (signal_rapidDecayAtZero H hH hb c)
  have hFa : AnalyticOnNhd ℂ (signalMellin (signal H c) c) {z : ℂ | max a 1 < z.re} :=
    hF.mono (fun _ hz => (le_max_left a 1).trans_lt hz)
  have hA : AnalyticOnNhd ℂ (amplitude H) {z : ℂ | max a 1 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (isOpen_re_gt _)).2
    intro z hz
    have hq := quotient_differentiableAt H hH ((le_max_right a 1).trans_lt hz)
    exact ((((differentiable_id.sub_const (5/6 : ℂ)).pow 2).cexp.differentiableAt).mul hq).differentiableWithinAt
  apply hFa.eqOn_of_preconnected_of_frequently_eq hA (convex_halfSpace_re_gt _).isPreconnected
    (z₀ := (2 : ℂ)) (by simpa using max_lt ha (by norm_num : (1 : ℝ) < 2)) _ hs
  apply line_tendsto_punctured.frequently
  exact Filter.Frequently.of_forall (fun y => signalMellin_eq_amplitude_on_line H hH hb c a ha htop y)

theorem regularZeta_mul_signalMellin (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | sigmaStar < s.re})
    (hb : ∀ s : ℂ, sigmaStar < s.re → ‖H s-1‖ ≤ 1/2)
    (c a : ℝ) (ha : a < 2)
    (htop : signal H c =O[atTop] (fun x : ℝ => x^(a+c)))
    {s : ℂ} (hs : max a 1 < s.re) :
    ZetaConcrete.regularZeta s * signalMellin (signal H c) c s =
      (s-1) * gaussianMultiplier H s := by
  have hs1 : 1 < s.re := (le_max_right a 1).trans_lt hs
  have h1 : s ≠ 1 := by intro heq; simp [heq] at hs1
  rw [ZetaConcrete.regularZeta_eq h1,
    signalMellin_eq_amplitude H hH hb c a ha htop hs]
  unfold amplitude quotient gaussianMultiplier
  have hn := riemannZeta_ne_zero_of_one_lt_re hs1
  field_simp

/-- The only unconstructed objects now are the arithmetic correction H and
physical probe J. The principal signal is the explicit inverse Mellin integral. -/
structure ProbeData (ω c m A B τ₀ : ℝ) where
  correction : ℂ → ℂ
  physical : ℝ → ℂ
  correction_analytic : AnalyticOnNhd ℂ correction {s : ℂ | sigmaStar < s.re}
  correction_bound : ∀ s, sigmaStar < s.re → ‖correction s-1‖ ≤ (1/2 : ℝ)
  low_bound : physical =O[atTop] (fun x : ℝ => x^(sigmaStar+c+ω))
  high_estimate : HeightClosure.HighEstimate
    (fun x => physical x-signal correction c x) (sSup ZetaConcrete.zeroReals) c m A B τ₀

def ProbeData.toRawSignal {ω c m A B τ₀ : ℝ} (data : ProbeData ω c m A B τ₀)
    (hω : ω < sSup ZetaConcrete.zeroReals-sigmaStar)
    (hm : 0 < m) (hA : 0 ≤ A) (hτ₀ : 0 < τ₀) :
    ZetaConcrete.RawSignalData sigmaStar (sSup ZetaConcrete.zeroReals) ω c m A B τ₀ where
  correction := data.correction
  physical := data.physical
  principal := signal data.correction c
  correction_analytic := data.correction_analytic
  correction_bound := data.correction_bound
  local_integrability := signal_locallyIntegrable data.correction
    data.correction_analytic.differentiableOn data.correction_bound c
  rapid_decay := signal_rapidDecayAtZero data.correction
    data.correction_analytic.differentiableOn data.correction_bound c
  low_bound := data.low_bound
  high_estimate := data.high_estimate
  mellin_identity := by
    have hmargin : 0 < Signal.margin sigmaStar (sSup ZetaConcrete.zeroReals) ω (m/2) :=
      Signal.margin_pos hω (by positivity)
    have ha : sSup ZetaConcrete.zeroReals-
        Signal.margin sigmaStar (sSup ZetaConcrete.zeroReals) ω (m/2) < 2 := by
      have h := ZetaConcrete.zero_supremum_bounds.2
      linarith
    have htop := HeightClosure.common_signal_bound_of_high_estimate
      data.physical (signal data.correction c) sigmaStar
      (sSup ZetaConcrete.zeroReals) ω c m A B τ₀ hm hA hτ₀ data.low_bound data.high_estimate
    intro s hs
    apply regularZeta_mul_signalMellin data.correction
      data.correction_analytic.differentiableOn data.correction_bound c _ ha ?_ hs
    convert htop using 1
    ring_nf

def ArithmeticProbeObligation : Prop :=
  sigmaStar < sSup ZetaConcrete.zeroReals →
    ∃ ω c m A B τ₀ : ℝ, 0 < ω ∧ ω < sSup ZetaConcrete.zeroReals-sigmaStar ∧
      0 < m ∧ 0 ≤ A ∧ 0 < τ₀ ∧ Nonempty (ProbeData ω c m A B τ₀)

theorem arithmeticProbeObligation_suffices (h : ArithmeticProbeObligation) :
    ZetaConcrete.RawArithmeticSignalObligation := by
  intro hb
  obtain ⟨ω, c, m, A, B, τ₀, hω0, hω, hm, hA, hτ₀, ⟨data⟩⟩ := h hb
  exact ⟨ω, c, m, A, B, τ₀, hω0, hω, hm, hA, hτ₀,
    ⟨data.toRawSignal hω hm hA hτ₀⟩⟩

theorem riemannZeta_ne_zero_of_arithmetic_probe (h : ArithmeticProbeObligation)
    {s : ℂ} (hs : sigmaStar < s.re) (hpole : s ≠ 1) : riemannZeta s ≠ 0 :=
  ZetaConcrete.riemannZeta_ne_zero_of_raw_arithmetic_signal
    (arithmeticProbeObligation_suffices h) hs hpole

end ZeroFree.ZetaInverse
