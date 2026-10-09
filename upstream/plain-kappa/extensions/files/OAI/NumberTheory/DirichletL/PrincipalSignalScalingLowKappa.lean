/-
Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Generalizes the actual principal-source normalization from OpenAI/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0.
The total slot exponent varies; the intrinsic Mellin pole remains z=1/6.
These identities do not assert the physical low/high estimates.
-/
import OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import OAI.NumberTheory.DirichletL.Detector.PrincipalNormalizer

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate PrincipalMellinResidues
variable {κ ι : Type*}

theorem source_power_identity_total {Z : ℝ} (hZ : 0<Z) (ell b : ℝ) (s : ℂ) :
    ((Z^((1-ell-b)/2) : ℝ) : ℂ)^(1/3 : ℂ)*(Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-ell/6 : ℝ) : ℂ))*(Z : ℂ)^(s+((-(4+b)/6 : ℝ) : ℂ)) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le ((1-ell-b)/2) (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring

theorem normalized_source_double_residue_total (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (Y Z ell b : ℝ) (hZ : 0<Z) (s : ℂ) (H B : ℂ→ℂ→ℂ)
    (S : Finset κ) (T : κ→Finset ι) (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6)=slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M^2/6 *
      sourceMultiplier W0 W1 (Z^((1-ell-b)/2)) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s+((-(4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*H 1 (1/6) /
        LFunction χ s * slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := source_power_identity_total hZ ell b s
  have hz : (Z : ℂ)^(((-ell/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M*(sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-ell/6 : ℝ) : ℂ))*((Z : ℂ)^(((-ell/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s+((-(4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem sourceResidueIntegral_normalized_total (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z ell b : ℝ) (hZ : 0<Z)
    (H B : ℂ→ℂ→ℂ→ℂ) (S : Finset κ) (T : κ→Finset ι)
    (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀j∈S,0<slotMass T w j)
    (hB : ∀t : ℝ,B ((a : ℂ)+t*I) 1 (1/6)=slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^((1-ell-b)/2)) Y Z H B /
      (sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
        verticalIntegral a (fun s =>
          (Z : ℂ)^(s+((-(4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*H s 1 (1/6) /
            LFunction χ s * slotRatio S T w Q A η s) := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm),?_⟩
  unfold sourceResidueIntegral verticalIntegral
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalized_source_double_residue_total W0 W1 M χ Y Z ell b hZ _ (H _) (B _)
    S T w Q A η hc (hB _)

theorem source_double_residue_integrable_total (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z ell b : ℝ) (hZ : 0<Z)
    (H B : ℂ→ℂ→ℂ→ℂ) (S : Finset κ) (T : κ→Finset ι)
    (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀j∈S,0<slotMass T w j)
    (hB : ∀t : ℝ,B ((a : ℂ)+t*I) 1 (1/6)=slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)+((-(4+b)/6 : ℝ) : ℂ))*
        Complex.exp ((((a : ℂ)+t*I)-5/6)^2)*H ((a : ℂ)+t*I) 1 (1/6) /
          LFunction χ ((a : ℂ)+t*I)*slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M^2/6 *
      sourceMultiplier W0 W1 (Z^((1-ell-b)/2)) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ:=ell))
  apply (hi.mul_const
    (sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (normalized_source_double_residue_total W0 W1 M χ Y Z ell b hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

theorem sourceResidueIntegral_normalized_total_of_positive_windows
    (M : Ideal HeckeFamily.O) [NeZero M] (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0)
    (χ : Character) (a Y Z ell b : ℝ) (hZ : 0<Z) (H B : ℂ→ℂ→ℂ→ℂ)
    (S : Finset κ) (T : κ→Finset ι) (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hm : ∀j∈S,0<slotMass T w j)
    (hB : ∀t : ℝ,B ((a : ℂ)+t*I) 1 (1/6)=slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^((1-ell-b)/2)) Y Z H B /
      (sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
        verticalIntegral a (fun s =>
          (Z : ℂ)^(s+((-(4+b)/6 : ℝ) : ℂ))*Complex.exp ((s-5/6)^2)*H s 1 (1/6) /
            LFunction χ s * slotRatio S T w Q A η s) :=
  sourceResidueIntegral_normalized_total W0 W1 M χ a Y Z ell b hZ H B S T w Q A η
    (ProbePrincipalNormalizer.sourceResidueConstant_ne_zero M W0 W1 a0 b0 a1 b1 ha0 ha1
      hW0 hW1 hreal0 hreal1 hpos0 hpos1 hne0 hne1) hm hB

end SevenEighths.PrincipalSignalComparison
end
end OAI
