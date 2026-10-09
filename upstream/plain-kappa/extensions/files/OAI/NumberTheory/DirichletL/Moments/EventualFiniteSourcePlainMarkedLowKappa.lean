/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual eventual plain-marked supply for one fixed finite character/ideal family.
Native terminal PositiveAt and finite-row NaturalState are constructed in the
proof; actual row, source-slot, prime and height gates remain explicit.
The fixed family is before the terminal degree; no all-character uniform-degree,
complete Moments, count, or final nonvanishing conclusion is asserted. -/
import OAI.NumberTheory.DirichletL.Energy.FiniteLabelPositiveAtLowKappa
import OAI.NumberTheory.DirichletL.Moments.FiniteRowNaturalState
import OAI.NumberTheory.DirichletL.Moments.PlainMarkedAdmissionLowKappa

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open scoped ContDiff
open Filter
namespace OAI.SevenEighths.EventualFiniteSourcePlainMarkedLowKappa
set_option autoImplicit false
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open CenteredMomentDetectorDictionary CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentEnergyWidthRanges
open FiniteLabelPositiveAtLowKappa FiniteRowNaturalState
open MarkedHeightBudgetLowKappa PlainMarkedAdmissionLowKappa
open ConcretePrimeRowBridge ConcreteTraceCRT QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)
include hH

/-- All maps and scalar source geometry are fixed before the witnesses below.
The strictly positive final constant is before Z and every actual fiber.
No caller-supplied PositiveAt, NaturalState, or native energy capacity remains. -/
theorem eventually_finite_source_plain_marked
    {Label Slot : Type*} [Fintype Label] [Fintype Slot] [DecidableEq Slot]
    (η : Label → Character) (Q : Label → Ideal O)
    (hQM : ∀j, Q j ≤ M)
    (hQ0 : ∀j, internalQ (Q j) (η j) ≠ 0)
    (hQt : ∀j, internalQ (Q j) (η j) ≠ ⊤)
    (hQ72 : ∀j, internalQ (Q j) (η j) ≤ Ideal.span {(72 : O)})
    (hMm : M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement})
    (W : ℝ → ℂ) (aslot bslot dmin dmax Mcap L rmin εm τ₀ κEnergy κPlain : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hcapMargin : dmax < Mcap)
    (hL : dmax / 2 ≤ L) (hrmin : 0 < rmin) (hεm : 0 < εm) (hτ₀ : 0 < τ₀)
    (hκ0 : (37/50 : ℝ) ≤ κEnergy) (hκPlain : κEnergy ≤ κPlain)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2 * HeckeZeroSupremum.beta - 1 ≤ κEnergy) :
    ∃ρ εE : ℝ, 0 < ρ ∧ 0 < εE ∧ ρ ≤ Mcap - dmax ∧
    ∃Φ : 𝓢(ℝ, ℂ), (∀x, 0 ≤ (Φ x).re) ∧ (∀x, (Φ x).im = 0) ∧
    ∃degree J : ℕ, ∃τ Ctotal : ℝ,
      0 < τ ∧ τ ≤ τ₀ ∧ 0 < Ctotal ∧
      ρ + εE + 2 * τ * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm ∧
      ∀ᶠZ : ℝ in atTop, 1 < Z ∧
      ∀d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε tstar T allowance : ℝ) (i : ℕ),
      ∀ (F : Fiber M H Label Slot (Z^d) a ε tstar T allowance i),
        F.rowData = ProbeHighRowFamily.momentData (η F.label) →
        (∀u ∈ F.rows, Z^rmin ≤ ((Ideal.span {u.val}).absNorm : ℝ)) →
        (∀s ∈ F.slots, F.profile s = W) → (∀s ∈ F.slots, F.upper s = bslot) →
        (∀s ∈ F.slots, ∀P ∈ primePool M H (F.upper s) ((Z^d)^(F.widths s)),
          F.profile s ((P.absNorm : ℝ) / ((Z^d)^(F.widths s))) ≠ 0 →
            IsCoprime P (η F.label).modulus) →
        (∀s ∈ F.slots, d * F.widths s ≤ fineMesh Mcap 0 L κEnergy εE) →
        (∀s ∈ F.slots, (F.external s).re = 17/50) →
        ∀height : ℝ, 0 ≤ height → height ≤ Z^(2 * τ) →
        (∀s ∈ F.slots, |(F.external s).im| ≤ height) →
        ∀selected : Finset Slot, selected ⊆ F.slots →
        2 * F.m + 6 * κPlain * (∑s ∈ selected, F.widths s) ≤ 1 →
        ∀ (j k : ℕ), j + k ≤ 2 →
        ∀σ ∈ Set.Icc (0 : ℝ) 1, ∀t ∈ Set.Icc (-height) height,
          (∑u ∈ F.rows, ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
              ((Z^d)^F.m) σ t *
            polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
              ((Z^d)^F.m) σ t * F.physicalProduct selected u‖^2) ≤
            Ctotal * (Z^d)^(1 + εm) := by
  obtain ⟨ρ₀, εE, hρ₀, hεE, hheightChoice⟩ :=
    exists_losses_before_height dmin εm hdmin hεm
  let ρ := min ρ₀ ((Mcap - dmax) / 2)
  have hgap : 0 < Mcap - dmax := sub_pos.mpr hcapMargin
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρle : ρ ≤ ρ₀ := min_le_left _ _
  have hρhalf : ρ ≤ (Mcap - dmax) / 2 := min_le_right _ _
  have hρcap : ρ ≤ Mcap - dmax := by linarith only [hρhalf, hgap]
  have hMcap : 0 < Mcap := hdmin.trans_le (hdmax.trans hcapMargin.le)
  have hsconj : Function.support (fun y => conj (W y)) ⊆ Set.Icc aslot bslot := by
    intro y hy
    apply hWs
    intro hz
    exact hy (by simp only [hz, map_zero])
  have hconj : ContDiff ℝ ∞ (fun y => conj (W y)) := Complex.conjCLE.contDiff.comp hW
  obtain ⟨degree, S, C, hC, hpositive⟩ := eventually_finite_label_positiveAt (Slot := Slot)
    M H hH η Q hQM hQ0 hQt hQ72 (fun y => conj (W y))
    aslot bslot (1/4) (9/4) 2 0 L (33/50) (33/50) Mcap κEnergy εE
    haslot hsconj hconj hbslot (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hMcap hκ0 hεE hbeta hκ
  obtain ⟨J, Cp, hCp, hadmission⟩ := actual_plain_marked_admission M H hH S
  obtain ⟨τ, hτ, hτle, hbudget₀⟩ := hheightChoice degree J τ₀ hτ₀
  have hbudget : ρ + εE + 2 * τ * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm := by
    linarith only [hbudget₀, hρle]
  obtain ⟨Φ, hΦnonneg, hΦreal, hstates⟩ := eventually_finite_row_natural_state
    η (fun j => internalQ (Q j) (η j)) hQ0 hQt hQ72 (fun _ => inf_le_right)
    rmin ρ hrmin hρ
  let coefficient := C * Cp^4 * diagonalControl Φ * (2 : ℝ)^(degree + 4 * J)
  let Ctotal := max 1 coefficient
  have hCtotal : 0 < Ctotal := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨ρ, εE, hρ, hεE, hρcap, Φ, hΦnonneg, hΦreal,
    degree, J, τ, Ctotal, hτ, hτle, hCtotal, hbudget, ?_⟩
  filter_upwards [hpositive, hstates] with Z hp hs
  refine ⟨hp.1, ?_⟩
  intro d hd hd' a ε tstar T allowance i F hdata hrowLower hprofile hupper
    hprime hslotMesh hreal height hheight hheight_le hfrequency selected hselected hcapacity
    j k hjk σ hσ t ht
  have hd0 : 0 < d := hdmin.trans_le hd
  obtain ⟨state, hcharacter, hQ, hpuncture, _, _, hwidth, hΦ, hscale, hkeep, hone⟩ :=
    hs.2 F.label d hd0.le F.rows hrowLower F.row_norm
  have hstateCap : state.width ≤ Mcap := by rw [hwidth]; linarith only [hd', hρcap]
  have hkeepRows : ∀u ∈ F.rows, state.radial.keep u.val := by
    intro u hu
    exact (hkeep _).mpr ⟨u, hu, rfl⟩
  have honeRows : ∀u ∈ F.rows,
      state.radial.profile (‖eisEmbedding u.val‖^2 / state.radial.scale) = 1 := by
    intro u hu
    rw [hΦ, hscale]
    exact hone u hu
  have hb := hadmission degree C hC.le Φ Z d dmin ρ εE εm (2 * τ)
    0 2 L (fineMesh Mcap 0 L κEnergy εE) (33/50) (33/50) Mcap κEnergy κPlain
    a ε tstar T allowance i hp.1 hdmin hd hρ.le hεm.le (by positivity)
    (by linarith only [hκ0, hκPlain]) hκPlain (by linarith only [hd', hL]) hbudget
    (η F.label) (Q F.label) W bslot (hp.2 F.label) F hdata hMm state
    hcharacter hpuncture hQ hwidth hstateCap hΦ hkeepRows honeRows
    height hheight hheight_le selected hselected hcapacity
    (fun s hs => hprofile s (hselected hs)) (fun s hs => hupper s (hselected hs))
    (fun s hs => hprime s (hselected hs))
    (fun s => hslotMesh s.val (hselected s.property))
    (fun s => by rw [hreal s.val (hselected s.property)]; norm_num)
    (fun s => by rw [hreal s.val (hselected s.property)]; norm_num)
    (fun s => by simpa only [abs_neg] using hfrequency s.val (hselected s.property))
    j k hjk σ hσ t ht
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (le_max_right 1 coefficient)
    (Real.rpow_nonneg (Real.rpow_nonneg (zero_lt_one.trans hp.1).le _) _)

end OAI.SevenEighths.EventualFiniteSourcePlainMarkedLowKappa
