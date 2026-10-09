/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Standalone candidate bridge: not an added upstream target or complete Moments
instance. Actual verification status is recorded separately in metadata.json.
This estimates the actual positiveSlotRow and actual energy, without a
raw-moment or final nonvanishing assumption. -/
import OAI.NumberTheory.DirichletL.Moments.InductionEnergy
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.FinitePositiveRowDominationCandidate
open HeckeFamily HeckeInverseAmplification ConcreteTraceCRT
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability
local notation "O" => HeckeFamily.O

theorem finite_positiveSlotRow_le_actual_energy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rows : Finset FreeRow) (η : Character) (m A : O)
    (t X₁ X₂ : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (coefficient : ι → Ideal O → ℂ)
    (P : ι → ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K b₁ b₂ : ℝ)
    (hK : 0 < K) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hΦ : ∀z : O, 0 ≤ (Φ (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hkeep : ∀u ∈ rows, keep u.val)
    (hone : ∀u ∈ rows, Φ (‖eisEmbedding u.val‖ ^ 2 / K) = 1) :
    (∑u ∈ rows, ‖positiveSlotRow η m A u.val W₁ W₂ pool coefficient P t X₁ X₂‖ ^ 2) ≤
      energy η m A t W₁ W₂ pool coefficient P X₁ X₂ keep Φ K := by
  let rowEmbedding : FreeRow ↪ O := ⟨Subtype.val, Subtype.val_injective⟩
  let rowsO : Finset O := rows.map rowEmbedding
  let f : O → ℂ := fun z => positiveSlotRow η m A z W₁ W₂ pool coefficient P t X₁ X₂
  let g : O → ℝ := fun z => if keep z then ‖f z‖ ^ 2 * (Φ (‖eisEmbedding z‖ ^ 2 / K)).re else 0
  have hsum : Summable g := by
    obtain ⟨B, hB⟩ := product_bounded η m A t
      (Real.sqrt (X₁ * X₂ * ∏i, P i) : ℂ)⁻¹
      W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ pool coefficient
    apply bounded_radial_summable f B _ keep Φ K hK
    simpa only [f, positiveSlotRow] using hB
  have hg (z : O) : 0 ≤ g z := by
    dsimp only [g]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hΦ z)
    · exact le_rfl
  have he : (∑u ∈ rows, ‖f u.val‖ ^ 2) = ∑z ∈ rowsO, g z := by
    dsimp only [rowsO]
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [rowEmbedding, Function.Embedding.coeFn_mk, g]
    rw [if_pos (hkeep u hu), hone u hu]
    simp only [Complex.one_re, mul_one]
  calc
    _ = ∑z ∈ rowsO, g z := he
    _ ≤ ∑'z : O, g z := hsum.sum_le_tsum rowsO (fun z _ => hg z)
    _ = _ := rfl

end OAI.SevenEighths.FinitePositiveRowDominationCandidate

set_option pp.all true
set_option pp.maxSteps 1000000
#check @OAI.SevenEighths.FinitePositiveRowDominationCandidate.finite_positiveSlotRow_le_actual_energy
#print axioms OAI.SevenEighths.FinitePositiveRowDominationCandidate.finite_positiveSlotRow_le_actual_energy
