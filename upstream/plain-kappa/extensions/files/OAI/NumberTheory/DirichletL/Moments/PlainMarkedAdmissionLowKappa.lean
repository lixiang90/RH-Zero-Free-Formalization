/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual plain-marked admission at a moving kappa. This proves the finite-fiber
marked bound from actual PositiveAt and natural-state cover/slot gates.
Complete Moments and the source Batch are supplied separately. -/
import OAI.NumberTheory.DirichletL.Moments.FiberPositiveAtLowKappa
import OAI.NumberTheory.DirichletL.Moments.MarkedHeightBudgetLowKappa
import OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace OAI.SevenEighths.PlainMarkedAdmissionLowKappa
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open CenteredMomentDetectorDictionary CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open FiberPositiveAtLowKappa MarkedHeightBudgetLowKappa
open ConcretePrimeRowBridge ConcreteTraceCRT QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The coefficient in the final moment bound is fixed before the fiber,
selected slots, state, derivative orders, test frequency and height.
The energy admission capacity is proved from the actual plain capacity,
not supplied as another hypothesis. -/
theorem actual_plain_marked_admission (S : Finset (ℕ × ℕ)) :
    ∃J : ℕ, ∃Cp : ℝ, 0 < Cp ∧
    ∀ {Label Slot : Type*} [Fintype Slot] [DecidableEq Slot],
    ∀ (degree : ℕ) (C : ℝ), 0 ≤ C →
    ∀ (Φ : 𝓢(ℝ, ℂ))
      (Z d dmin ρ εE εm h Bmask bΦ L Lslot lo hi Mcap κEnergy κPlain
        a ε tstar T allowance : ℝ) (i : ℕ),
    1 < Z → 0 < dmin → dmin ≤ d → 0 ≤ ρ → 0 ≤ εm → 0 ≤ h →
    0 ≤ κPlain → κEnergy ≤ κPlain → d / 2 ≤ L →
    ρ + εE + h * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm →
    ∀ (η : Character) (Q : Ideal O) (W : ℝ → ℂ) (bslot : ℝ),
    PositiveAt (α := Slot) M H hH (fun y => conj (W y)) bslot (1/4) (9/4)
      bΦ Bmask L Lslot lo hi Mcap εE κEnergy Z η Q degree S C →
    ∀ (F : Fiber M H Label Slot (Z^d) a ε tstar T allowance i),
    F.rowData = ProbeHighRowFamily.momentData η →
    M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement} →
    ∀ (state : NaturalState Z Bmask bΦ), state.character = η →
    state.puncture = 1 → state.fixedModulus = internalQ Q η →
    state.width = d + ρ → state.width ≤ Mcap → state.radial.profile = Φ →
    (∀u ∈ F.rows, state.radial.keep u.val) →
    (∀u ∈ F.rows, state.radial.profile (‖eisEmbedding u.val‖^2 / state.radial.scale) = 1) →
    ∀ (height : ℝ), 0 ≤ height → height ≤ Z^h →
    ∀ (selected : Finset Slot), selected ⊆ F.slots →
    2 * F.m + 6 * κPlain * (∑s ∈ selected, F.widths s) ≤ 1 →
    (∀s ∈ selected, F.profile s = W) → (∀s ∈ selected, F.upper s = bslot) →
    (∀s ∈ selected, ∀P ∈ primePool M H (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((P.absNorm : ℝ) / ((Z^d)^(F.widths s))) ≠ 0 → IsCoprime P η.modulus) →
    (∀s : selected, d * F.widths s.val ≤ Lslot) →
    (∀s : selected, lo ≤ 1 - (F.external s.val).re) →
    (∀s : selected, 1 - (F.external s.val).re ≤ hi) →
    (∀s : selected, |-(F.external s.val).im| ≤ height) →
    ∀ (j k : ℕ), j + k ≤ 2 →
    ∀σ ∈ Set.Icc (0 : ℝ) 1, ∀t ∈ Set.Icc (-height) height,
      (∑u ∈ F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t *
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t * F.physicalProduct selected u‖^2) ≤
        (C * Cp^4 * diagonalControl Φ * (2 : ℝ)^(degree + 4 * J)) *
          (Z^d)^(1 + εm) := by
  obtain ⟨J, Cp, hCp, hbound⟩ := actual_finite_fiber_bound_of_positiveAt M H hH S
  refine ⟨J, Cp, hCp, ?_⟩
  intro Label Slot _ _ degree C hC Φ Z d dmin ρ εE εm h Bmask bΦ L Lslot lo hi Mcap
    κEnergy κPlain a ε tstar T allowance i hZ hdmin hd hρ hεm hh hκPlain hκ hL hbudget
    η Q W bslot hpositive F hdata hMm state hcharacter hpuncture hQ hwidth hMcap hΦ
    hkeep hone height hheight hheight_le selected hselected hcapacity hprofile hupper
    hη hslotWidth hσlo hσhi hfrequency j k hjk σ hσ t ht
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd0 : 0 < d := hdmin.trans_le hd
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hd0
  have hm : 0 ≤ F.m := (F.lengths hU).2.2.2.2
  have hsum : 0 ≤ ∑s ∈ selected, F.widths s :=
    Finset.sum_nonneg (fun s hs => (F.widths_pos s (hselected hs)).le)
  have hlength : length Z ((Z^d)^F.m) = d * F.m := by
    rw [←Real.rpow_mul hZ0.le, length,
      max_eq_right (Real.one_le_rpow hZ.le (mul_nonneg hd0.le hm)),
      Real.logb_rpow hZ0 hZ.ne']
  have hsumScaled : (∑s : selected, d * F.widths s.val) =
      d * (∑s ∈ selected, F.widths s) := by
    simpa only [Finset.mul_sum] using
      (Finset.sum_coe_sort selected (fun s => d * F.widths s))
  have hκsum : 6 * κEnergy * (∑s ∈ selected, F.widths s) ≤
      6 * κPlain * (∑s ∈ selected, F.widths s) := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ (by norm_num)) hsum
  have henergyBase : 2 * F.m + 6 * κEnergy * (∑s ∈ selected, F.widths s) ≤ 1 :=
    (add_le_add_right hκsum _).trans hcapacity
  have hscaled := mul_le_mul_of_nonneg_left henergyBase hd0.le
  have henergyCapacity : length Z ((Z^d)^F.m) + length Z ((Z^d)^F.m) +
      6 * κEnergy * (∑s : selected, d * F.widths s.val) ≤ state.width := by
    rw [hlength, hsumScaled, hwidth]
    nlinarith only [hscaled, hρ]
  have hterm : 0 ≤ 6 * κPlain * (∑s ∈ selected, F.widths s) := by positivity
  have hmUpper : F.m ≤ 1 / 2 := by linarith only [hcapacity, hterm]
  have hXcap : (Z^d)^F.m ≤ Z^L := by
    rw [←Real.rpow_mul hZ0.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have he := mul_le_mul_of_nonneg_left hmUpper hd0.le
    nlinarith only [he, hL]
  have hfinite := hbound degree C hC Z d Bmask bΦ L Lslot lo hi Mcap εE κEnergy
    a ε tstar T allowance height i hZ hd0.le hheight η Q W bslot hpositive
    F hdata hMm state hcharacter hpuncture hQ hMcap selected hselected hprofile hupper
    hη hslotWidth hσlo hσhi hfrequency hXcap henergyCapacity hkeep hone
    (fun _ => 1) j k (by omega) (by omega) σ hσ t
  rw [hwidth, hΦ] at hfinite
  have htHeight : ‖t‖ ≤ height := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ht
  have hdiag : 0 ≤ diagonalControl Φ := diagonalControl_nonneg _
  have hgrowth := actual_growth_absorption (C * Cp^4 * diagonalControl Φ)
    Z d dmin ρ εE εm h height t degree J (by positivity) hZ.le hdmin hd hεm hh
    hheight hheight_le (htHeight.trans hheight_le) hbudget
  exact hfinite.trans hgrowth

end OAI.SevenEighths.PlainMarkedAdmissionLowKappa
