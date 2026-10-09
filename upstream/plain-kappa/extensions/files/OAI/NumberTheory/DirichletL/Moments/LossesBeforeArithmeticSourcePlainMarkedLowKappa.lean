/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Scalar losses are chosen from scalar geometry before every ideal and ray subgroup.
For each arithmetic source and finite Slot type, native terminal/profile degrees
and a common positive height ceiling precede its finite arithmetic maps. The same
eventual bound holds for every smaller positive height exponent. -/
import OAI.NumberTheory.DirichletL.Energy.UniformDegreePositiveAtLowKappa
import OAI.NumberTheory.DirichletL.Moments.PlainMarkedAdmissionLowKappa
import OAI.NumberTheory.DirichletL.Moments.FiniteRowNaturalState

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate ContDiff
open Filter
namespace OAI.SevenEighths.LossesBeforeArithmeticSourcePlainMarkedLowKappa
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open CenteredMomentDetectorDictionary CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentEnergyWidthRanges UniformDegreePositiveAtLowKappa
open FiniteRowNaturalState MarkedHeightBudgetLowKappa PlainMarkedAdmissionLowKappa
open ConcretePrimeRowBridge ConcreteTraceCRT QuadraticInitialBound
local notation "O" => HeckeFamily.O
local instance {M : Ideal O} [NeZero M] : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Scalar losses precede every ideal, ray subgroup, and finite Slot type.
Their construction uses only `dmin`, `εm`, `dmax`, and `Mcap`. For each arithmetic
source, slots can then be chosen before the native terminal/profile degrees and
common height ceiling, which still precede every finite arithmetic map. -/
theorem exists_losses_before_arithmetic_slots_degrees_height_and_finite_family
    (W : ℝ → ℂ) (aslot bslot dmin dmax Mcap L rmin εm τ₀ κEnergy κPlain : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hcapMargin : dmax < Mcap)
    (hL : dmax / 2 ≤ L) (hrmin : 0 < rmin) (hεm : 0 < εm) (hτ₀ : 0 < τ₀)
    (hκ0 : (37/50 : ℝ) ≤ κEnergy) (hκPlain : κEnergy ≤ κPlain)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2 * HeckeZeroSupremum.beta - 1 ≤ κEnergy) :
    ∃ρ εE : ℝ, 0 < ρ ∧ 0 < εE ∧ ρ ≤ Mcap - dmax ∧
    ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
      (hH : RayOrthogonality.globalUnits M ≤ H),
      M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement} →
    ∀ {Slot : Type*} [Fintype Slot] [DecidableEq Slot],
    ∃degree J : ℕ, ∃τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧
      ρ + εE + 2 * τ * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm ∧
      ∀ {Label : Type*} [Fintype Label],
      ∀ (η : Label → Character) (Q : Label → Ideal O),
        (∀j, Q j ≤ M) → (∀j, internalQ (Q j) (η j) ≠ 0) →
        (∀j, internalQ (Q j) (η j) ≠ ⊤) →
        (∀j, internalQ (Q j) (η j) ≤ Ideal.span {(72 : O)}) →
      ∃Φ : 𝓢(ℝ, ℂ), (∀x, 0 ≤ (Φ x).re) ∧ (∀x, (Φ x).im = 0) ∧
      ∃Ctotal : ℝ, 0 < Ctotal ∧
      ∀ᶠZ : ℝ in atTop, 1 < Z ∧
      ∀τ' : ℝ, 0 < τ' → τ' ≤ τ →
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
        ∀height : ℝ, 0 ≤ height → height ≤ Z^(2 * τ') →
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
  refine ⟨ρ, εE, hρ, hεE, hρcap, ?_⟩
  intro M _ H hH hMm Slot _ _
  obtain ⟨degree, S, hterminal⟩ := exists_degree_before_character_positiveAt (Slot := Slot)
    M H hH (fun y => conj (W y)) aslot bslot (1/4) (9/4) 2 0 L (33/50) (33/50)
    Mcap κEnergy εE haslot hsconj hconj hbslot (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hMcap hκ0 hεE hbeta hκ
  obtain ⟨J, Cp, hCp, hadmission⟩ := actual_plain_marked_admission M H hH S
  obtain ⟨τ, hτ, hτle, hbudget₀⟩ := hheightChoice degree J τ₀ hτ₀
  have hbudget : ρ + εE + 2 * τ * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm := by
    linarith only [hbudget₀, hρle]
  refine ⟨degree, J, τ, hτ, hτle, hbudget, ?_⟩
  intro Label _ η Q hQM hQ0 hQt hQ72
  have hlabel (j : Label) : ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop, 1 < Z ∧
      PositiveAt (α := Slot) M H hH (fun y => conj (W y)) bslot (1/4) (9/4) 2 0 L
        (fineMesh Mcap 0 L κEnergy εE) (33/50) (33/50) Mcap εE κEnergy Z
        (η j) (Q j) degree S C :=
    hterminal (η j) (Q j) (hQM j) (hQ0 j) (hQt j) (hQ72 j)
  choose Cj hCj hj using hlabel
  let constants : Finset ℝ := insert 1 ((Finset.univ : Finset Label).image Cj)
  have hne : constants.Nonempty := Finset.insert_nonempty _ _
  let Cmax : ℝ := constants.max' hne
  have hCbound (j : Label) : Cj j ≤ Cmax := by
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hall : ∀ᶠZ : ℝ in atTop, ∀j : Label, 1 < Z ∧
      PositiveAt (α := Slot) M H hH (fun y => conj (W y)) bslot (1/4) (9/4) 2 0 L
        (fineMesh Mcap 0 L κEnergy εE) (33/50) (33/50) Mcap εE κEnergy Z
        (η j) (Q j) degree S (Cj j) := Filter.eventually_all.mpr hj
  obtain ⟨Φ, hΦnonneg, hΦreal, hstates⟩ := eventually_finite_row_natural_state
    η (fun j => internalQ (Q j) (η j)) hQ0 hQt hQ72 (fun _ => inf_le_right)
    rmin ρ hrmin hρ
  let coefficient := Cmax * Cp^4 * diagonalControl Φ * (2 : ℝ)^(degree + 4 * J)
  let Ctotal := max 1 coefficient
  have hCtotal : 0 < Ctotal := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨Φ, hΦnonneg, hΦreal, Ctotal, hCtotal, ?_⟩
  filter_upwards [hall, hstates] with Z hp hs
  refine ⟨hs.1, ?_⟩
  intro τ' hτ' hτ'le d hd hd' a ε tstar T allowance i F hdata hrowLower hprofile hupper
    hprime hslotMesh hreal height hheight hheight_le hfrequency selected hselected hcapacity
    j k hjk σ hσ t ht
  have hbudget' : ρ + εE + 2 * τ' * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm := by
    have hm := mul_le_mul_of_nonneg_right (show 2 * τ' ≤ 2 * τ by linarith only [hτ'le])
      (show 0 ≤ ((degree + 4 * J : ℕ) : ℝ) by positivity)
    linarith only [hbudget, hm]
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
  have hb := hadmission degree (Cj F.label) (hCj F.label).le Φ Z d dmin ρ εE εm (2 * τ')
    0 2 L (fineMesh Mcap 0 L κEnergy εE) (33/50) (33/50) Mcap κEnergy κPlain
    a ε tstar T allowance i hs.1 hdmin hd hρ.le hεm.le (by positivity)
    (by linarith only [hκ0, hκPlain]) hκPlain (by linarith only [hd', hL]) hbudget'
    (η F.label) (Q F.label) W bslot (hp F.label).2 F hdata hMm state
    hcharacter hpuncture hQ hwidth hstateCap hΦ hkeepRows honeRows
    height hheight hheight_le selected hselected hcapacity
    (fun s hs => hprofile s (hselected hs)) (fun s hs => hupper s (hselected hs))
    (fun s hs => hprime s (hselected hs))
    (fun s => hslotMesh s.val (hselected s.property))
    (fun s => by rw [hreal s.val (hselected s.property)]; norm_num)
    (fun s => by rw [hreal s.val (hselected s.property)]; norm_num)
    (fun s => by simpa only [abs_neg] using hfrequency s.val (hselected s.property))
    j k hjk σ hσ t ht
  have hdiag : 0 ≤ diagonalControl Φ := diagonalControl_nonneg _
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _
    (Real.rpow_nonneg (Real.rpow_nonneg (zero_lt_one.trans hs.1).le _) _)
  calc
    _ ≤ coefficient := by dsimp [coefficient]; gcongr; exact hCbound F.label
    _ ≤ Ctotal := le_max_right _ _

end OAI.SevenEighths.LossesBeforeArithmeticSourcePlainMarkedLowKappa
