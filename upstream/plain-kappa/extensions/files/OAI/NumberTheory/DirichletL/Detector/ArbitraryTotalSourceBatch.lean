/-
Copyright (c) 2026 Li Xiang.
Author: Li Xiang
-/
import OAI.NumberTheory.DirichletL.Detector.DetectorBatch

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch
open HeckeDetectorSupportedWitness ProbePhysical
local notation "O" => HeckeFamily.O

/-- The actual Batch supply gate with arbitrary positive total slot length. -/
lemma physical_slot_widths_total {N : ℕ} (ell : Fin N → ℝ)
    (d dmin mesh Λ : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ d) (hΛ : 0 < Λ)
    (hcap : d ≤ 37 * Λ / 7)
    (hell : ∀ j, 0 < ell j) (hsmall : ∀ j, ell j ≤ dmin * mesh)
    (hsum : ∑ j, ell j = Λ) :
    (∀ j, 0 < ell j / d) ∧ (∀ j, ell j / d ≤ mesh) ∧
      7 / 37 ≤ ∑ j, ell j / d := by
  have hd0 : 0 < d := hdmin.trans_le hd
  have hm : 0 ≤ mesh := by
    by_contra hn
    have hm : mesh < 0 := lt_of_not_ge hn
    have hn : (∑ j, ell j) ≤ 0 := Finset.sum_nonpos fun j _ =>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    linarith only [hn, hΛ]
  refine ⟨fun j => div_pos (hell j) hd0, fun j => ?_, ?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith only [hd, hm])
  · rw [← Finset.sum_div, hsum]
    apply (le_div_iff₀ hd0).mpr
    linarith only [hcap]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Construct the real source-family Batch from actual supported witnesses.
The constructor keeps the supplied windows, upper scales and complex
external parameters, and accepts any positive slot total meeting supply. -/
def retainedSourceBatchTotal {N : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0 ∈ R)
    (Z d dmin a ε tstar T allowance Λ : ℝ) (i : ℕ)
    (hw : ∀ u ∈ R, SupportedWitness
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (Z ^ d) a ε tstar T allowance i)
    (hrow : ∀ u ∈ R, rowNorm u ≤ Z ^ d)
    (ell : Fin N → ℝ) (profile : Fin N → ℝ → ℂ)
    (upper : Fin N → ℝ) (external : Fin N → ℂ)
    (mesh binWidth : ℝ) (hm : 0 ≤ mesh) (hb : 0 < binWidth)
    (hdmin : 0 < dmin) (hd : dmin ≤ d) (hΛ : 0 < Λ)
    (hcap : d ≤ 37 * Λ / 7)
    (hell : ∀ j, 0 < ell j) (hsmall : ∀ j, ell j ≤ dmin * mesh)
    (hsum : ∑ j, ell j = Λ) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z ^ d) a ε tstar T allowance i :=
  let hwidth := physical_slot_widths_total ell d dmin mesh Λ
    hdmin hd hΛ hcap hell hsmall hsum
  retainedSourceBatch M H hH S hS η R u0 h0 (Z ^ d) a ε tstar T allowance i
    hw hrow Finset.univ profile upper (fun j => ell j / d) external mesh binWidth hm hb
    (fun j _ => hwidth.1 j) (fun j _ => hwidth.2.1 j) hwidth.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
