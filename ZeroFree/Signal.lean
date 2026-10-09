
import ZeroFree.Boundary
import ZeroFree.Continuation

/- Variable-boundary continuation for the actual low/high signal contract.
   The arithmetic construction of this contract is not asserted by this module. -/
noncomputable section
namespace ZeroFree.Signal
open Filter Asymptotics MeasureTheory
open scoped Topology

def margin (σ β ω high : ℝ) : ℝ := min (β - σ - ω) high

theorem margin_pos {σ β ω high : ℝ} (hω : ω < β - σ) (hh : 0 < high) :
    0 < margin σ β ω high := by
  unfold margin
  exact lt_min (by linarith) hh

theorem continuation_boundary_gt {σ β ω high : ℝ} (hω : 0 < ω) :
    σ < β - margin σ β ω high := by
  have h := min_le_left (β - σ - ω) high
  unfold margin
  linarith

theorem max_signal_exponents (σ β ω high c : ℝ) :
    max (σ+c+ω) (β+c-high) = β+c-margin σ β ω high := by
  unfold margin
  rcases le_total (β-σ-ω) high with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]

theorem common_signal_bound_with_margin (J f : ℝ → ℂ) (σ β ω high c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (σ+c+ω)))
    (herror : (fun x => J x-f x) =O[atTop]
      (fun x : ℝ => x ^ (β+c-high))) :
    f =O[atTop] (fun x : ℝ => x ^ (β+c-margin σ β ω high)) := by
  simpa only [max_signal_exponents] using
    Continuation.common_signal_bound J f (σ+c+ω) (β+c-high) hJ herror

/-- Conditional analytic theorem with real functions and genuine Mellin integrals.
All low/high bounds, regularization and identity hypotheses remain explicit. -/
theorem nonzero_of_common_signal (σ β ω high c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | β-margin σ β ω high < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | β-margin σ β ω high < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | σ < s.re})
    (hcontract : ∀ s : ℂ, σ < s.re → ‖H s-1‖ ≤ (1/2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : Continuation.RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (σ+c+ω)))
    (herror : (fun x => J x-f x) =O[atTop]
      (fun x : ℝ => x ^ (β+c-high)))
    (heq : ∀ s : ℂ, max (β-margin σ β ω high) 1 < s.re →
      Lregular s * Continuation.signalMellin f c s =
        R s * Continuation.gaussianMultiplier H s)
    {ρ : ℂ} (hρ : β-margin σ β ω high < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) : L ρ ≠ 0 := by
  have hb := continuation_boundary_gt (β:=β) (high:=high) (σ:=σ) hω
  have hH' : AnalyticOnNhd ℂ H {s : ℂ | β-margin σ β ω high < s.re} :=
    hH.mono (fun _ hs => lt_trans hb hs)
  have htop : f =O[atTop] (fun x : ℝ =>
      x ^ ((β-margin σ β ω high)+c)) := by
    have hexp : (β-margin σ β ω high)+c = β+c-margin σ β ω high := by ring
    simpa only [hexp] using common_signal_bound_with_margin J f σ β ω high c hJ herror
  exact Continuation.nonzero_of_regularized_signal _ 1 c
    L Lregular R (Continuation.gaussianMultiplier H) f
    hL hR (Continuation.gaussianMultiplier_analytic hH') hlocal htop hzero
    heq hρ hregular hRρ
    (Continuation.gaussianMultiplier_ne_zero (hcontract ρ (lt_trans hb hρ)))

/-- Specialization to the actual Mathlib zeta function; the signal hypotheses
are required arguments, not introduced axioms. -/
theorem riemannZeta_ne_zero_of_signal (β ω high c : ℝ) (hω : 0 < ω)
    (Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular
      {s : ℂ | β-margin sigmaStar β ω high < s.re})
    (hR : AnalyticOnNhd ℂ R
      {s : ℂ | β-margin sigmaStar β ω high < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | sigmaStar < s.re})
    (hcontract : ∀ s : ℂ, sigmaStar < s.re → ‖H s-1‖ ≤ (1/2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : Continuation.RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (sigmaStar+c+ω)))
    (herror : (fun x => J x-f x) =O[atTop]
      (fun x : ℝ => x ^ (β+c-high)))
    (heq : ∀ s : ℂ, max (β-margin sigmaStar β ω high) 1 < s.re →
      Lregular s * Continuation.signalMellin f c s =
        R s * Continuation.gaussianMultiplier H s)
    {ρ : ℂ} (hρ : β-margin sigmaStar β ω high < ρ.re)
    (hregular : Lregular ρ = R ρ * riemannZeta ρ) (hRρ : R ρ ≠ 0) :
    riemannZeta ρ ≠ 0 :=
  nonzero_of_common_signal sigmaStar β ω high c hω riemannZeta
    Lregular R H J f hL hR hH hcontract hlocal hzero hJ herror heq hρ hregular hRρ

end ZeroFree.Signal

