/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual detector-fiber plain energy is bounded by the same relative ray-slot
energy, for every ray character on the identity-class prime pool.
The dictionary, common profile/upper, coprimality and radial cover gates are
explicit; this is not a complete Batch or Moments construction. -/
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
import OAI.NumberTheory.DirichletL.Moments.RayIdentityClassCoefficient
import OAI.NumberTheory.DirichletL.Moments.FinitePositiveRowDomination

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace OAI.SevenEighths.FiberRelativeEnergyBridge
set_option autoImplicit false
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy
open CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open HeckeDetectorDyadicProfiles ConcretePrimeRowBridge ConcreteTraceCRT
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial
open FinitePositiveRowDomination
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid HeckeFamily.K
variable (hH : RayOrthogonality.globalUnits M ≤ H)

theorem relative_coefficient_on_actual_primePool (η : Character)
    (θ : RayQuotient.Characters M H) (b D : ℝ) {I : Ideal O}
    (hI : I ∈ primePool M H b D) :
    idealCoeff (relativeCharacter M H hH η θ) I = idealCoeff η.inverse I := by
  rw [relativeCharacter_ideal, HeckeRayQuotient.idealCoeff_character,
    RayQuotient.idealCharacter_eq_one_of_identityClass M H hH θ
      (Finset.mem_filter.mp hI).2.2, one_mul]

variable {M H}
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem actual_fiber_plain_le_relative_energy
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (hdata : F.rowData = ProbeHighRowFamily.momentData η)
    (hMm : M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement}) (hU : 0 < U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s ∈ selected, ∀J ∈ primePool M H (F.upper s) (U ^ (F.widths s)),
      F.profile s ((J.absNorm : ℝ) / (U ^ (F.widths s))) ≠ 0 → IsCoprime J η.modulus)
    (W : ℝ → ℂ) (bslot : ℝ)
    (hprofile : ∀s ∈ selected, F.profile s = W)
    (hupper : ∀s ∈ selected, F.upper s = bslot)
    (θ : selected → RayQuotient.Characters M H)
    (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
    (hΦ : ∀z : O, 0 ≤ (Φ (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hkeep : ∀u ∈ F.rows, keep u.val)
    (hone : ∀u ∈ F.rows, Φ (‖eisEmbedding u.val‖ ^ 2 / K) = 1) :
    (∑u ∈ F.rows, ‖HeckeDyadic.polynomial (F.family u F.label) false
      ((HeckeDetectorRowwisePolynomial.logProfile^[j]) HeckeDetectorDyadicProfiles.positiveAnnular)
      (U ^ F.m) σ t *
      HeckeDyadic.polynomial (F.family u F.label) false
      ((HeckeDetectorRowwisePolynomial.logProfile^[k]) HeckeDetectorDyadicProfiles.positiveAnnular)
      (U ^ F.m) σ t * F.physicalProduct selected u‖ ^ 2) ≤
    energy η (fixedBadMask * idealGenerator 1) 1 0
      (twistProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[j]) positiveAnnular))
        σ (orientedFrequency F.reverse t))
      (twistProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[k]) positiveAnnular))
        σ (orientedFrequency F.reverse t))
      (fun s : selected => primePool M H bslot (U ^ (F.widths s.val)))
      (fun s : selected => fun J => idealCoeff (relativeCharacter M H hH η (θ s)) J *
        HeckePrimeAnnular.annularWeight (fun y => conj (W y)) (U ^ (F.widths s.val))
          (1 - (F.external s.val).re) (-(F.external s.val).im) J)
      (fun s : selected => U ^ (F.widths s.val)) (U ^ F.m) (U ^ F.m) keep Φ K := by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  have hdet (u : FreeRow) : detectorPositiveRow F η selected j k σ t u =
      positiveSlotRow η (fixedBadMask * idealGenerator 1) 1 u.val
        (twistProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[j]) positiveAnnular))
          σ (orientedFrequency F.reverse t))
        (twistProfile (orientedProfile F.reverse ((HeckeDetectorRowwisePolynomial.logProfile^[k]) positiveAnnular))
          σ (orientedFrequency F.reverse t))
        (fun s : selected => primePool M H bslot (U ^ (F.widths s.val)))
        (fun s : selected => fun J => idealCoeff (relativeCharacter M H hH η (θ s)) J *
          HeckePrimeAnnular.annularWeight (fun y => conj (W y)) (U ^ (F.widths s.val))
            (1 - (F.external s.val).re) (-(F.external s.val).im) J)
        (fun s : selected => U ^ (F.widths s.val)) 0 (U ^ F.m) (U ^ F.m) := by
    rw [natural_unit_mask_positive (naturalRow η u.val u.property.1)]
    have hslot (s : selected) :
        rowSlot η fixedBadMask 1 u.val
          (primePool M H (F.upper s.val) (U ^ (F.widths s.val)))
          (physicalSlotCoefficient η (F.profile s.val) (U ^ (F.widths s.val)) (F.external s.val)) 0 =
        rowSlot η fixedBadMask 1 u.val (primePool M H bslot (U ^ (F.widths s.val)))
          (fun J => idealCoeff (relativeCharacter M H hH η (θ s)) J *
            HeckePrimeAnnular.annularWeight (fun y => conj (W y)) (U ^ (F.widths s.val))
              (1 - (F.external s.val).re) (-(F.external s.val).im) J) 0 := by
      rw [hupper s.val s.property, hprofile s.val s.property]
      unfold rowSlot
      apply Finset.sum_congr rfl
      intro J hJ
      rw [physicalSlotCoefficient_annular η W _ _ J (Finset.mem_filter.mp hJ).2.1.ne_zero
        (Real.rpow_pos_of_pos hU _)]
      dsimp only
      rw [relative_coefficient_on_actual_primePool M H hH η (θ s) _ _ hJ]
    unfold detectorPositiveRow
    rw [rowMaskElement_eq_fixed]
    unfold positiveSlotRow
    rw [Finset.prod_congr rfl (fun s _ => hslot s)]
  simp_rw [hdet]
  apply finite_positiveSlotRow_le_actual_energy F.rows η _ 1 0 (U ^ F.m) (U ^ F.m)
    _ _ _ _ _ keep Φ K (9 / 4) (9 / 4) hK
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _) _ _ hΦ hkeep hone
  · exact (detector_profile_support F.reverse j σ (orientedFrequency F.reverse t)).trans (fun _ hx => hx.2)
  · exact (detector_profile_support F.reverse k σ (orientedFrequency F.reverse t)).trans (fun _ hx => hx.2)

end OAI.SevenEighths.FiberRelativeEnergyBridge
