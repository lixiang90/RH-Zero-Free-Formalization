/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Choose one fixed radial profile and construct an actual NaturalState for each
retained finite row set, uniformly in a finite fixed character/ideal family.
The fixed-ideal, positive growth and row-band hypotheses remain explicit.
No SourceData slot total or complete moment estimate is assumed. -/
import OAI.NumberTheory.DirichletL.Moments.FiniteFamilyNonexceptional
import OAI.NumberTheory.DirichletL.Energy.FixedRadialSource
import OAI.NumberTheory.DirichletL.Energy.State

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace OAI.SevenEighths.FiniteRowNaturalState
open HeckeFamily HeckeInverseAmplification ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyFixedRadialSource
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open FiniteFamilyNonexceptional
local notation "O" => HeckeFamily.O

theorem eventually_finite_row_natural_state
    {Label : Type*} [Fintype Label] (η : Label → Character) (Q : Label → Ideal O)
    (hQ0 : ∀ j, Q j ≠ 0) (hQ : ∀ j, Q j ≠ ⊤)
    (hQ72 : ∀ j, Q j ≤ Ideal.span {(72 : O)}) (hQη : ∀ j, Q j ≤ (η j).modulus)
    (rmin ρ : ℝ) (hrmin : 0 < rmin) (hρ : 0 < ρ) :
    ∃ Φ : 𝓢(ℝ, ℂ), (∀ x, 0 ≤ (Φ x).re) ∧ (∀ x, (Φ x).im = 0) ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ j : Label, ∀ d : ℝ, 0 ≤ d →
        ∀ rows : Finset FreeRow,
          (∀ u ∈ rows, Z ^ rmin ≤ ((Ideal.span {u.val}).absNorm : ℝ)) →
          (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ Z ^ d) →
          ∃ s : NaturalState Z 0 2,
            s.character = η j ∧ s.fixedModulus = Q j ∧ s.puncture = 1 ∧
            s.rowWidth = d ∧ s.characterWidth = ρ ∧ s.width = d + ρ ∧
            s.radial.profile = Φ ∧ s.radial.scale = Z ^ d ∧
            (∀ z, s.radial.keep z ↔ ∃ u ∈ rows, u.val = z) ∧
            ∀ u ∈ rows, Φ (‖eisEmbedding u.val‖ ^ 2 / Z ^ d) = 1 := by
  obtain ⟨Φ, hs, hn, hi, hone⟩ := exists_fixed_bump 1 (by norm_num)
  refine ⟨Φ, hn, hi, ?_⟩
  have hmod : ∀ᶠ Z : ℝ in atTop, ∀ j : Label,
      ((η j).modulus.absNorm : ℝ) ≤ Z ^ ρ := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop hρ).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hmod,
    eventually_finite_family_no_fixed_inducing η Q hQ0 hQ hQ72 hQη rmin hrmin]
    with Z hZ hmod hno
  refine ⟨hZ, ?_⟩
  intro j d hd rows hlo hupper
  let s : NaturalState Z 0 2 := {
    character := η j
    fixedModulus := Q j
    puncture := 1
    radial := {
      keep := fun z => ∃ u ∈ rows, u.val = z
      profile := Φ
      scale := Z ^ d
      scale_pos := Real.rpow_pos_of_pos (zero_lt_one.trans hZ) d
      nonneg := fun z => hn _ }
    rowWidth := d
    characterWidth := ρ
    base_ge_one := hZ.le
    row_nonneg := hd
    character_nonneg := hρ.le
    scale_eq := rfl
    modulus_bound := hmod j
    puncture_ne_zero := one_ne_zero
    puncture_bound := by simp
    radial_support := by
      intro x hx
      have hx' := (hs hx).2
      change x ≤ 2
      linarith
    row_ne_zero := by
      rintro z ⟨u, hu, rfl⟩
      exact u.property.1
    nonexceptional := by
      rintro z ⟨u, hu, rfl⟩
      exact hno j u (hlo u hu) (fixedBadMask * idealGenerator 1)
        (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero 1 one_ne_zero))
        ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
        ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) }
  refine ⟨s, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun z => Iff.rfl, ?_⟩
  intro u hu
  apply hone
  constructor
  · exact div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) d).le
  · apply (div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) d)).mpr
    rw [one_mul, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact hupper u hu

end OAI.SevenEighths.FiniteRowNaturalState
