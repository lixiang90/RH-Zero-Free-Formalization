
import ZeroFree.Boundary
import ZeroFree.Certificate
import ZeroFree.Geometry
import ZeroFree.Feedback
import ZeroFree.Family

noncomputable section
namespace ZeroFree

theorem certificate_root : Certificate.rootPoly ellStar = 0 := ellStar_spec.1
theorem certificate_lower : Certificate.lower < ellStar := ellStar_spec.2.1
theorem certificate_upper : ellStar < Certificate.upper := by
  have heq : Certificate.upper = ellHi := by norm_num [Certificate.upper, ellHi]
  rw [heq]
  exact ellStar_spec.2.2

theorem reference_certificate {y δ : ℝ} (hy : 0 ≤ y)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3/4) :
    Certificate.endpoint ellStar y δ ≤ 0 :=
  Certificate.endpoint_nonpositive certificate_root certificate_lower certificate_upper hy hd0 hd1

theorem reference_c : Certificate.c ellStar = 1/(3*kappaStar) := by
  have hc := Certificate.c_inverse certificate_root
  have hk := kappaStar_range.1
  have hk0 : 0 < kappaStar := by linarith
  apply (eq_div_iff (by positivity : 3*kappaStar ≠ 0)).2
  dsimp [kappaStar] at *
  nlinarith only [hc]

theorem reference_D (x : ℝ) :
    Feedback.D kappaStar x = Certificate.D ellStar (1/2-x) := by
  unfold Feedback.D Certificate.D
  rw [reference_c]
  ring

theorem reference_P (x : ℝ) :
    Feedback.P kappaStar x = Certificate.P ellStar (1/2-x) := by
  unfold Feedback.P Certificate.P
  rw [reference_c]
  ring

theorem reference_J (x δ : ℝ) :
    Feedback.J kappaStar δ x = Certificate.J ellStar (1/2-x) δ := by
  unfold Feedback.J Certificate.J
  rw [reference_D, reference_P]

theorem reference_count (x δ : ℝ) :
    Feedback.count kappaStar δ x = Certificate.R ellStar (1/2-x) δ := by
  unfold Feedback.count Certificate.R
  rw [reference_P, reference_J]

theorem physical_h_range :
    0 < Certificate.h ellStar ∧ Certificate.h ellStar < 1 := by
  have hb := bStar_range
  have he := ellStar_coarse
  have hbdef : bStar = Certificate.b ellStar := rfl
  rw [hbdef] at hb
  unfold Certificate.h
  constructor <;> linarith only [hb.1, hb.2, he.1, he.2]

/-- The actual high-envelope strict saving at the best algebraic boundary.
The count is the explicit rational envelope, not an imported Lipschitz bound. -/
theorem cubic_physical_saving {β δ x d : ℝ}
    (hβ0 : sigmaStar < β) (hβ1 : β ≤ 7/8)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3/4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (hd : d ≤ Certificate.h ellStar + (β-sigmaStar)/32) :
    Certificate.endpoint ellStar (1/2-x) δ - (β-sigmaStar) +
      Certificate.h ellStar *
        (Feedback.count (2*β-1) δ x - Feedback.count kappaStar δ x) +
      (d-Certificate.h ellStar) *
        (Feedback.count (2*β-1) δ x + δ/2-17/50)
      ≤ -(359/400)*(β-sigmaStar) := by
  have href := reference_certificate (δ:=δ) (by linarith : 0 ≤ 1/2-x) hd0 hd1
  have hp := Feedback.actual_parameter_range
    (by have h := sigmaStar_decimal_isolated.1; linarith : 87/100 ≤ sigmaStar)
    (le_of_lt hβ0) hβ1
  have hactual : (2*β-1)-kappaStar = 2*(β-sigmaStar) := by
    rw [kappaStar_identity]
    ring
  exact Feedback.physical_feedback_saving (le_of_lt kappaStar_range.1) hp.1
    hd0 hd1 hx0 hx1 (sub_pos.mpr hβ0) hactual
    (le_of_lt physical_h_range.1) (le_of_lt physical_h_range.2) href hd

theorem zeta_buffer_range {β : ℝ} (hβ0 : sigmaStar < β) (hβ1 : β ≤ 7/8) :
    0 < (β-sigmaStar)/32 ∧
      (β-sigmaStar)/32 ≤ (ellStar-1/6)/128 ∧
      (ellStar-1/6)/128 < 1/384000 := by
  have he := Geometry.zeta_ceiling_margin_pos certificate_lower certificate_upper
  rw [Geometry.zeta_ceiling_margin_identity] at he
  dsimp [sigmaStar] at hβ0 ⊢
  constructor
  · linarith
  constructor <;> linarith

theorem actual_supply {β : ℝ} (hβ0 : sigmaStar < β) (hβ1 : β ≤ 7/8) :
    5*ellStar-Certificate.h ellStar-(β-sigmaStar)/32 > 1/50 ∧
      Certificate.h ellStar+(β-sigmaStar)/32 < 1 := by
  have hb := zeta_buffer_range hβ0 hβ1
  have hg := Geometry.supply_margin_pos certificate_lower certificate_upper
  have ho := Geometry.outer_ceiling_pos certificate_lower certificate_upper
  rw [Geometry.supply_margin_identity] at hg
  rw [Geometry.outer_ceiling_identity] at ho
  constructor <;> linarith

theorem low_normalizer_identity :
    (1-ellStar)/4-bStar/6 = sigmaStar-2/3-bStar/6 := by
  unfold sigmaStar
  ring

/-- The remaining arithmetic input for zeta, expressed as actual signal objects.
Its existence is deliberately not asserted as a proved theorem. -/
def ZetaSignalObligation : Prop :=
  let L : Unit → ℂ → ℂ := fun _ => riemannZeta
  let Allowed : Unit → ℂ → Prop := fun _ s => s ≠ 1
  BddAbove (insert (1/2 : ℝ) (Family.zeroRealParts L Allowed)) ∧
    (sigmaStar < sSup (insert (1/2 : ℝ) (Family.zeroRealParts L Allowed)) →
      ∃ ω high c : ℝ, 0 < ω ∧
        ω < sSup (insert (1/2 : ℝ) (Family.zeroRealParts L Allowed))-sigmaStar ∧
        0 < high ∧ Nonempty (Family.SignalData L Allowed sigmaStar
          (sSup (insert (1/2 : ℝ) (Family.zeroRealParts L Allowed))) ω high c))

/-- Conditional best-boundary theorem about Mathlib's actual Riemann zeta.
Axiom audits do not remove the explicit unproved signal obligation. -/
theorem riemannZeta_ne_zero_of_cubic_signal
    (hdata : ZetaSignalObligation) {s : ℂ}
    (hs : sigmaStar < s.re) (hpole : s ≠ 1) : riemannZeta s ≠ 0 := by
  have hσ : (1/2 : ℝ) ≤ sigmaStar := by
    have h := sigmaStar_decimal_isolated.1
    linarith
  exact Family.no_zero_of_signal_data (fun _ : Unit => riemannZeta)
    (fun _ s => s ≠ 1) sigmaStar hσ hdata.1 hdata.2 (i:=()) hpole hs

end ZeroFree

