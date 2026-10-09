/-
The complex-power identity is adapted from OpenAI/math
PrincipalSignalComparison.source_power_identity, Apache-2.0.
Upstream revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream raw SHA-256: fb59ccaed042ea0d445ca08b5333d0fd248b8db8ee12e691f79a32a351e1b08d.
Generalized by Li Xiang / lixiang90: total slot exponent ell and scale
imbalance b vary, while the intrinsic sixfold Mellin pole 1/6 and
Gaussian center 5/6 remain fixed.
This normalizes the principal expression; it does not construct an
arithmetic correction or prove physical probe estimates.
-/
import ZeroFree.ZetaSignal

set_option autoImplicit false

noncomputable section
namespace ZeroFree.SourceScaling

def lx (ell b : ℝ) : ℝ := (1-ell-b)/2
def ly (ell b : ℝ) : ℝ := (1-ell+b)/2
def shift (b : ℝ) : ℝ := -(4+b)/6

theorem total_scales (ell b : ℝ) : lx ell b+ly ell b+ell=1 := by
  unfold lx ly
  ring

theorem shift_identity (ell b : ℝ) :
    lx ell b/3-5/6+ell/6=shift b := by
  unfold lx shift
  ring

/-- The paper uses h=(1+3*ell+b)/2. Its Mellin exponent equals the
shift derived directly from the actual source residue. -/
theorem paper_shift_identity (ell b : ℝ) :
    lx ell b/2-1+((1+3*ell+b)/2)/6=shift b := by
  unfold lx shift
  ring

theorem legacy_scales :
    lx (1/6) (1/8)=17/48 ∧ ly (1/6) (1/8)=23/48 ∧ shift (1/8)=-11/16 := by
  norm_num [lx, ly, shift]

/-- The factor Z^(-ell/6) comes from slot normalization. Its variable ell
does not change the intrinsic Mellin evaluation at z=1/6. -/
theorem source_power_identity {Z : ℝ} (hZ : 0<Z) (ell b : ℝ) (s : ℂ) :
    ((Z^(lx ell b) : ℝ) : ℂ)^(1/3 : ℂ)*(Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-ell/6 : ℝ) : ℂ))*(Z : ℂ)^(s+(shift b : ℂ)) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (lx ell b) (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  unfold lx shift
  push_cast
  ring

theorem slot_normalizer_ne_zero {Z : ℝ} (hZ : 0<Z) (ell : ℝ) :
    (Z : ℂ)^(((-ell/6 : ℝ) : ℂ)) ≠ 0 :=
  (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])

theorem normalized_source_power {Z : ℝ} (hZ : 0<Z) (ell b : ℝ) (s : ℂ) :
    (((Z^(lx ell b) : ℝ) : ℂ)^(1/3 : ℂ)*(Z : ℂ)^(s-5/6)) /
      (Z : ℂ)^(((-ell/6 : ℝ) : ℂ)) = (Z : ℂ)^(s+(shift b : ℂ)) := by
  rw [source_power_identity hZ ell b s]
  exact mul_div_cancel_left₀ _ (slot_normalizer_ne_zero hZ ell)

/-- The normalized expression is exactly the amplitude used by the actual
inverse Mellin zeta signal, with its correction H still explicit. -/
theorem normalized_zeta_source {Z : ℝ} (hZ : 0<Z) (ell b : ℝ)
    (H : ℂ→ℂ) (s : ℂ) :
    (((Z^(lx ell b) : ℝ) : ℂ)^(1/3 : ℂ)*(Z : ℂ)^(s-5/6) *
      (Complex.exp ((s-5/6)^2)*H s / riemannZeta s)) /
      (Z : ℂ)^(((-ell/6 : ℝ) : ℂ)) =
        (Z : ℂ)^(s+(shift b : ℂ))*ZetaInverse.amplitude H s := by
  rw [mul_div_right_comm, normalized_source_power hZ ell b s]
  unfold ZetaInverse.amplitude ZetaInverse.quotient
  ring

theorem best_low_exponent :
    sigmaStar+shift bStar=(1-ellStar)/4-bStar/6 := by
  unfold sigmaStar shift
  ring

theorem best_source_power {Z : ℝ} (hZ : 0<Z) (s : ℂ) :
    (((Z^(lx ellStar bStar) : ℝ) : ℂ)^(1/3 : ℂ)*(Z : ℂ)^(s-5/6)) /
      (Z : ℂ)^(((-ellStar/6 : ℝ) : ℂ)) =
        (Z : ℂ)^(s+(shift bStar : ℂ)) :=
  normalized_source_power hZ ellStar bStar s

end ZeroFree.SourceScaling
