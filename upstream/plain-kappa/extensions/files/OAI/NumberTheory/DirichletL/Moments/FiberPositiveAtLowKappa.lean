/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual finite-source admission to the Energy.Bands.PositiveAt estimate.
The actual terminal interface and all admission/cover conditions stay explicit.
No Batch, complete Moments, or final nonvanishing supply is constructed. -/
import OAI.NumberTheory.DirichletL.Moments.FiberRelativeEnergyBridge
import OAI.NumberTheory.DirichletL.Moments.DetectorPairControl
import OAI.NumberTheory.DirichletL.Energy.Bands

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace OAI.SevenEighths.FiberPositiveAtLowKappa
set_option autoImplicit false
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open CenteredMomentDetectorDictionary CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open FiberRelativeEnergyBridge DetectorPairControl
open ConcretePrimeRowBridge ConcreteTraceCRT QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

theorem actual_finite_fiber_bound_of_positiveAt (S : Finset (ℕ × ℕ)) :
    ∃J : ℕ, ∃Cp : ℝ, 0 < Cp ∧
    ∀ {Label Slot : Type*} [Fintype Slot] [DecidableEq Slot],
    ∀ (degree : ℕ) (C : ℝ), 0 ≤ C →
    ∀ (Z d Bmask bΦ L Lslot lo hi Mcap εE κ a ε tstar T allowance height : ℝ)
      (i : ℕ), 1 < Z → 0 ≤ d → 0 ≤ height →
    ∀ (η : Character) (Q : Ideal O) (W : ℝ → ℂ) (bslot : ℝ),
    PositiveAt (α := Slot) M H hH (fun y => conj (W y)) bslot (1/4) (9/4)
      bΦ Bmask L Lslot lo hi Mcap εE κ Z η Q degree S C →
    ∀ (F : Fiber M H Label Slot (Z^d) a ε tstar T allowance i),
    F.rowData = ProbeHighRowFamily.momentData η →
    M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement} →
    ∀ (state : NaturalState Z Bmask bΦ), state.character = η →
    state.puncture = 1 → state.fixedModulus = internalQ Q η → state.width ≤ Mcap →
    ∀ (selected : Finset Slot), selected ⊆ F.slots →
    (∀s ∈ selected, F.profile s = W) → (∀s ∈ selected, F.upper s = bslot) →
    (∀s ∈ selected, ∀P ∈ primePool M H (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((P.absNorm : ℝ) / ((Z^d)^(F.widths s))) ≠ 0 → IsCoprime P η.modulus) →
    (∀s : selected, d * F.widths s.val ≤ Lslot) →
    (∀s : selected, lo ≤ 1 - (F.external s.val).re) →
    (∀s : selected, 1 - (F.external s.val).re ≤ hi) →
    (∀s : selected, |-(F.external s.val).im| ≤ height) →
    ((Z^d)^F.m ≤ Z^L) →
    (length Z ((Z^d)^F.m) + length Z ((Z^d)^F.m) +
      6 * κ * (∑s : selected, d * F.widths s.val) ≤ state.width) →
    (∀u ∈ F.rows, state.radial.keep u.val) →
    (∀u ∈ F.rows, state.radial.profile (‖eisEmbedding u.val‖^2 / state.radial.scale) = 1) →
    ∀ (θ : selected → RayQuotient.Characters M H) (j k : ℕ), j ≤ 2 → k ≤ 2 →
    ∀σ ∈ Set.Icc (0 : ℝ) 1, ∀t : ℝ,
      (∑u ∈ F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t *
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t * F.physicalProduct selected u‖^2) ≤
        C * Cp^4 * diagonalControl state.radial.profile *
          (1 + height)^degree * (1 + ‖t‖)^(4 * J) * Z^(state.width + εE) := by
  obtain ⟨J, Cp, hCp, hpair⟩ := detectorPairProfiles_squared_control_uniform S
  refine ⟨J, Cp, hCp, ?_⟩
  intro Label Slot _ _ degree C hC Z d Bmask bΦ L Lslot lo hi Mcap εE κ
    a ε tstar T allowance height i hZ hd hheight η Q W bslot hpositive
    F hdata hMm state hcharacter hpuncture hQ hwidth selected hselected hprofile hupper
    hη hslotWidth hσlo hσhi hfrequency hcap hcapacity hkeep hone θ j k hj hk σ hσ t
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU : 0 < Z^d := Real.rpow_pos_of_pos hZ0 d
  have hX : 0 < (Z^d)^F.m := Real.rpow_pos_of_pos hU F.m
  have hscale (s : selected) : (Z^d)^(F.widths s.val) = Z^(d * F.widths s.val) :=
    (Real.rpow_mul hZ0.le d (F.widths s.val)).symm
  have hw (s : selected) : 0 ≤ d * F.widths s.val :=
    mul_nonneg hd (F.widths_pos s.val (hselected s.property)).le
  let p := detectorPairProfiles F.reverse j k σ t
  have hp0 : (p.profile 0 : ℝ → ℂ) =
      twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ
        (orientedFrequency F.reverse t) := by
    funext x
    simp [p, detectorPairProfiles, detectorSchwartz_apply]
  have hp1 : (p.profile 1 : ℝ → ℂ) =
      twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ
        (orientedFrequency F.reverse t) := by
    funext x
    simp [p, detectorPairProfiles, detectorSchwartz_apply]
  have hmask : state.mask = fixedBadMask * idealGenerator 1 := by
    simp only [NaturalState.mask, hpuncture]
  have he := hpositive selected θ (fun s => d * F.widths s.val)
    (fun s => 1 - (F.external s.val).re) (fun s => -(F.external s.val).im)
    0 height hw hslotWidth hσlo hσhi hheight hfrequency state hQ hwidth p
    ((Z^d)^F.m) ((Z^d)^F.m) hX hX hcap hcap hcapacity
  rw [hcharacter, hmask, hp0, hp1] at he
  simp_rw [←hscale] at he
  simp only [abs_zero, add_zero] at he
  have hrow := actual_fiber_plain_le_relative_energy (M := M) (H := H) hH F η hdata hMm hU
    selected j k σ t hη W bslot hprofile hupper θ state.radial.keep
    state.radial.profile state.radial.scale state.radial.scale_pos state.radial.nonneg hkeep hone
  have hpbound : (p.control S)^2 ≤ Cp^4 * (1 + ‖t‖)^(4 * J) :=
    hpair F.reverse j k hj hk σ hσ t
  have hdiag : 0 ≤ diagonalControl state.radial.profile := diagonalControl_nonneg _
  calc
    _ ≤ C * diagonalControl state.radial.profile * (p.control S)^2 *
        (1 + height)^degree * Z^(state.width + εE) := hrow.trans he
    _ ≤ C * diagonalControl state.radial.profile * (Cp^4 * (1 + ‖t‖)^(4 * J)) *
        (1 + height)^degree * Z^(state.width + εE) := by gcongr
    _ = _ := by ring

end OAI.SevenEighths.FiberPositiveAtLowKappa
