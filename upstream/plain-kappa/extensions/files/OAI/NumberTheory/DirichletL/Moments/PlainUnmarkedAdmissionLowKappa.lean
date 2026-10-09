/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual unmarked admission with natural row width d * max 1 (2*m).
The actual PositiveAt, total state-width cap, polynomial scale cap, and radial
profile cover are retained, with growth absorption for any principal exponent. -/
import OAI.NumberTheory.DirichletL.Moments.FiberPositiveAtLowKappa
import OAI.NumberTheory.DirichletL.Moments.MarkedHeightBudgetLowKappa
import OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace OAI.SevenEighths.PlainUnmarkedAdmissionLowKappa
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open CenteredMomentDetectorDictionary CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open FiberPositiveAtLowKappa MarkedHeightBudgetLowKappa
open ConcretePrimeRowBridge ConcreteTraceCRT QuadraticInitialBound
local notation "O" => HeckeFamily.O

/-- The same absolute loss budget supports any principal exponent p. -/
theorem actual_growth_absorption_principal_exponent
    (C Z d dmin p rho epsE epsm h height t : ℝ) (degree J : ℕ)
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hepsm : 0 ≤ epsm) (hh : 0 ≤ h) (hheight : 0 ≤ height)
    (hheight_le : height ≤ Z^h) (ht : ‖t‖ ≤ Z^h)
    (hbudget : rho + epsE + h * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * epsm) :
    C * (1 + height)^degree * (1 + ‖t‖)^(4 * J) * Z^(d * p + rho + epsE) ≤
      (C * (2 : ℝ)^(degree + 4 * J)) * (Z^d)^(p + epsm) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hg := actual_growth_absorption C Z d dmin rho epsE epsm h height t degree J
    hC hZ hdmin hd hepsm hh hheight hheight_le ht hbudget
  have hsplit : Z^(d * p + rho + epsE) =
      Z^(d + rho + epsE) * Z^(d * (p - 1)) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  have hpower : (Z^d)^(1 + epsm) * Z^(d * (p - 1)) = (Z^d)^(p + epsm) := by
    rw [←Real.rpow_mul hZ0.le, ←Real.rpow_add hZ0, ←Real.rpow_mul hZ0.le]
    congr 1
    ring
  calc
    _ = (C * (1 + height)^degree * (1 + ‖t‖)^(4 * J) * Z^(d + rho + epsE)) *
        Z^(d * (p - 1)) := by
      rw [hsplit]
      ring
    _ ≤ ((C * (2 : ℝ)^(degree + 4 * J)) * (Z^d)^(1 + epsm)) *
        Z^(d * (p - 1)) := mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hZ0.le _)
    _ = (C * (2 : ℝ)^(degree + 4 * J)) *
        ((Z^d)^(1 + epsm) * Z^(d * (p - 1))) := by ring
    _ = _ := by rw [hpower]

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Prove the actual unmarked field from PositiveAt without a marked-capacity
premise. Its polynomial and total natural-state widths retain explicit caps. -/
theorem actual_plain_unmarked_admission (S : Finset (ℕ × ℕ)) :
    ∃J : ℕ, ∃Cp : ℝ, 0 < Cp ∧
    ∀ {Label Slot : Type*} [Fintype Slot] [DecidableEq Slot],
    ∀ (degree : ℕ) (C : ℝ), 0 ≤ C →
    ∀ (Phi : 𝓢(ℝ, ℂ))
      (Z d dmin rho epsE epsm h Bmask bPhi L Lslot lo hi Mcap kappa
        a eps tstar T allowance : ℝ) (i : ℕ),
    1 < Z → 0 < dmin → dmin ≤ d → 0 ≤ rho → 0 ≤ epsm → 0 ≤ h →
    d * (1/2 + 75 * eps) ≤ L →
    rho + epsE + h * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * epsm →
    ∀ (eta : Character) (Q : Ideal O) (W : ℝ → ℂ) (bslot : ℝ),
    PositiveAt (α := Slot) M H hH (fun y => conj (W y)) bslot (1/4) (9/4)
      bPhi Bmask L Lslot lo hi Mcap epsE kappa Z eta Q degree S C →
    ∀ (F : Fiber M H Label Slot (Z^d) a eps tstar T allowance i),
    F.rowData = ProbeHighRowFamily.momentData eta →
    M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement} →
    ∀ (state : NaturalState Z Bmask bPhi), state.character = eta →
    state.puncture = 1 → state.fixedModulus = internalQ Q eta →
    state.width = d * max 1 (2 * F.m) + rho → state.width ≤ Mcap →
    state.radial.profile = Phi →
    (∀u ∈ F.rows, state.radial.keep u.val) →
    (∀u ∈ F.rows, state.radial.profile (‖eisEmbedding u.val‖^2 / state.radial.scale) = 1) →
    ∀ (height : ℝ), 0 ≤ height → height ≤ Z^h →
    ∀ (j k : ℕ), j + k ≤ 2 →
    ∀sigma ∈ Set.Icc (0 : ℝ) 1, ∀t ∈ Set.Icc (-height) height,
      (∑u ∈ F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) sigma t *
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) sigma t‖^2) ≤
        (C * Cp^4 * diagonalControl Phi * (2 : ℝ)^(degree + 4 * J)) *
          (Z^d)^(max 1 (2 * F.m) + epsm) := by
  obtain ⟨J, Cp, hCp, hbound⟩ := actual_finite_fiber_bound_of_positiveAt M H hH S
  refine ⟨J, Cp, hCp, ?_⟩
  intro Label Slot _ _ degree C hC Phi Z d dmin rho epsE epsm h Bmask bPhi L Lslot
    lo hi Mcap kappa a eps tstar T allowance i hZ hdmin hd hrho hepsm hh hL hbudget
    eta Q W bslot hpositive F hdata hMm state hcharacter hpuncture hQ hwidth hMcap
    hPhi hkeep hone height hheight hheight_le j k hjk sigma hsigma t ht
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hd0 : 0 < d := hdmin.trans_le hd
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hd0
  have hm : 0 ≤ F.m := (F.lengths hU).2.2.2.2
  have hmUpper : F.m ≤ 1/2 + 75 * eps := (F.lengths hU).2.2.1
  have hlength : length Z ((Z^d)^F.m) = d * F.m := by
    rw [←Real.rpow_mul hZ0.le, length,
      max_eq_right (Real.one_le_rpow hZ.le (mul_nonneg hd0.le hm)),
      Real.logb_rpow hZ0 hZ.ne']
  have hXcap : (Z^d)^F.m ≤ Z^L := by
    rw [←Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le
      ((mul_le_mul_of_nonneg_left hmUpper hd0.le).trans hL)
  have henergyCapacity : length Z ((Z^d)^F.m) + length Z ((Z^d)^F.m) +
      6 * kappa * (∑s : (∅ : Finset Slot), d * F.widths s.val) ≤ state.width := by
    rw [hlength, hwidth]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]
    have hp := mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) (2 * F.m)) hd0.le
    nlinarith only [hp, hrho]
  have hfinite := hbound degree C hC Z d Bmask bPhi L Lslot lo hi Mcap epsE kappa
    a eps tstar T allowance height i hZ hd0.le hheight eta Q W bslot hpositive F hdata
    hMm state hcharacter hpuncture hQ hMcap (∅ : Finset Slot) (Finset.empty_subset _)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    hXcap henergyCapacity hkeep hone (fun _ => 1) j k (by omega) (by omega)
    sigma hsigma t
  simp only [Fiber.physicalProduct, Finset.prod_empty, mul_one] at hfinite
  rw [hwidth, hPhi] at hfinite
  have htHeight : ‖t‖ ≤ height := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ht
  have hdiag : 0 ≤ diagonalControl Phi := diagonalControl_nonneg _
  have hgrowth := actual_growth_absorption_principal_exponent (C * Cp^4 * diagonalControl Phi)
    Z d dmin (max 1 (2 * F.m)) rho epsE epsm h height t degree J (by positivity)
    hZ.le hdmin hd hepsm hh hheight hheight_le (htHeight.trans hheight_le) hbudget
  exact hfinite.trans hgrowth

end OAI.SevenEighths.PlainUnmarkedAdmissionLowKappa
