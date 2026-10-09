/-
Adapted from OpenAI/math GlobalCorrection and PrincipalSignalComparison
under Apache-2.0. Upstream revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Changes by Li Xiang / lixiang90 (2026-10-09): lift the independently proved
21/25 local domain to the SAME globalClosedCorrection, CorrectionTail S,
and sourceCorrection eta S. Bounds remain uniform for all actual Hecke
characters and retain the original prime majorant and fixed z = 1/6 pole.
-/
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import OAI.NumberTheory.DirichletL.Detector.GlobalRegionLowKappa

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma idealClosedCorrection_bound_lowKappa (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 21/25≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBound P := by
  apply unramifiedClosed_open_region_bound_lowKappa
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_bound_lowKappa (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 21/25≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_bound_lowKappa η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma globalClosedCorrection_multipliable_lowKappa (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 21/25≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    idealClosedCorrection_bound_lowKappa η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem globalClosedCorrection_analytic_x_lowKappa (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|21/25<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_x_lowKappa
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_bound_lowKappa η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem globalClosedCorrection_analytic_w_lowKappa (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 21/25≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_w_lowKappa
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_bound_lowKappa η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_analytic_z_lowKappa (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 21/25≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_z_lowKappa
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_bound_lowKappa η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end SevenEighths.ProbePhysical

namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily ProbePhysical

/-- The original arithmetic correction, with the identical excluded set S. -/
theorem sourceCorrection_analytic_lowKappa (eta : Character)
    (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S) :
    AnalyticOnNhd ℂ (sourceCorrection eta S) {s : ℂ | 21/25 < s.re} := by
  change AnalyticOnNhd ℂ (fun s : ℂ => globalClosedCorrection eta S s 1 (1/6))
    {s : ℂ | 21/25 < s.re}
  exact globalClosedCorrection_analytic_x_lowKappa eta S hS.tail 1 (1/6)
    (by norm_num) (by norm_num)

theorem sourceCorrection_differentiable_lowKappa (eta : Character)
    (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S) :
    DifferentiableOn ℂ (sourceCorrection eta S) {s : ℂ | 21/25 < s.re} :=
  (sourceCorrection_analytic_lowKappa eta S hS).differentiableOn

theorem sourceCorrection_bound_lowKappa (eta : Character)
    (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (s : ℂ) (hs : 21/25 <= s.re) :
    ‖sourceCorrection eta S s - 1‖ <= (1/2 : ℝ) := by
  exact globalClosedCorrection_bound_lowKappa eta S hS.tail s 1 (1/6)
    hs (by norm_num) (by norm_num)

/-- Any later target sigma >= 21/25 uses exactly the same correction and S. -/
theorem sourceCorrection_on_lower_halfplane_lowKappa (eta : Character)
    (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    {sigma : ℝ} (hsigma : 21/25 <= sigma) :
    AnalyticOnNhd ℂ (sourceCorrection eta S) {s : ℂ | sigma < s.re} ∧
      (∀ s : ℂ, sigma < s.re → ‖sourceCorrection eta S s - 1‖ <= (1/2 : ℝ)) := by
  constructor
  · exact (sourceCorrection_analytic_lowKappa eta S hS).mono
      (fun _ hs => hsigma.trans_lt hs)
  · intro s hs
    exact sourceCorrection_bound_lowKappa eta S hS s (hsigma.trans hs.le)

end SevenEighths.PrincipalSignalComparison
end
end OAI
