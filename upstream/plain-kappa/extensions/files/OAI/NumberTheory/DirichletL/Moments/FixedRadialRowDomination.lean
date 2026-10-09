/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
A single fixed radial profile dominates every retained finite positive row set
inside its geometric radius, uniformly over actual characters, slots and scales.
The row-radius and retention hypotheses remain explicit. -/import OAI.NumberTheory.DirichletL.Moments.FinitePositiveRowDomination
import OAI.NumberTheory.DirichletL.Energy.FixedRadialSource

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.FixedRadialRowDomination
open HeckeFamily HeckeInverseAmplification ConcreteTraceCRT CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentEnergyFixedRadialSource
open FinitePositiveRowDomination
local notation "O" => HeckeFamily.O

theorem exists_fixed_radial_positiveRow_domination (b : ℝ) (hb : 0 < b) :
    ∃ Φ : 𝓢(ℝ, ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Icc (-1) (b + 1) ∧
      (∀ x, 0 ≤ (Φ x).re) ∧ (∀ x, (Φ x).im = 0) ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        (rows : Finset FreeRow) (η : Character) (m A : O)
        (t X₁ X₂ : ℝ) (W₁ W₂ : ℝ → ℂ)
        (pool : ι → Finset (Ideal O)) (coefficient : ι → Ideal O → ℂ)
        (P : ι → ℝ) (keep : O → Prop) (K b₁ b₂ : ℝ),
        0 < K → 0 < X₁ → 0 < X₂ →
        Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
        (∀ u ∈ rows, keep u.val) →
        (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ b * K) →
        (∑ u ∈ rows, ‖positiveSlotRow η m A u.val W₁ W₂ pool coefficient P t X₁ X₂‖ ^ 2) ≤
          energy η m A t W₁ W₂ pool coefficient P X₁ X₂ keep Φ K := by
  obtain ⟨Φ, hs, hn, hi, hone⟩ := exists_fixed_bump b hb
  refine ⟨Φ, hs, hn, hi, ?_⟩
  intro ι _ _ rows η m A t X₁ X₂ W₁ W₂ pool coefficient P keep K b₁ b₂
    hK hX₁ hX₂ hs₁ hs₂ hkeep hrow
  apply finite_positiveSlotRow_le_actual_energy rows η m A t X₁ X₂ W₁ W₂
    pool coefficient P keep Φ K b₁ b₂ hK hX₁ hX₂ hs₁ hs₂ (fun z => hn _) hkeep
  intro u hu
  apply hone
  constructor
  · exact div_nonneg (sq_nonneg _) hK.le
  · apply (div_le_iff₀ hK).mpr
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrow u hu

end OAI.SevenEighths.FixedRadialRowDomination
