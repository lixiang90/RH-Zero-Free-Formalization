/-
Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
The supremum below is the actual finite-order Hecke family from the pinned
OpenAI/math library. It is not replaced by the single zeta zero supremum.
These parameter lemmas do not assert existence of the arithmetic probe.
-/
import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

set_option autoImplicit false

noncomputable section
namespace LiXiang.LowKappaParameters
open OAI.SevenEighths

def actualKappa : ℝ := 2*HeckeZeroSupremum.beta-1

theorem actualKappa_eq : actualKappa=2*HeckeZeroSupremum.beta-1 := rfl

theorem actualKappa_le_one : actualKappa≤1 := by
  have h := HeckeZeroSupremum.beta_le_one
  unfold actualKappa
  linarith

theorem actual_inputs {sigma : ℝ} (hsigma : 87/100≤sigma)
    (hbad : sigma<HeckeZeroSupremum.beta) :
    37/50<actualKappa ∧ (51/100:ℝ)≤HeckeZeroSupremum.beta ∧
      2*HeckeZeroSupremum.beta-1≤actualKappa := by
  unfold actualKappa
  constructor
  · linarith
  constructor
  · linarith
  · exact le_rfl

theorem actualKappa_reference_increment (sigma : ℝ) :
    actualKappa-(2*sigma-1)=2*(HeckeZeroSupremum.beta-sigma) := by
  unfold actualKappa
  ring

theorem reference_not_admissible {sigma : ℝ}
    (hbad : sigma<HeckeZeroSupremum.beta) :
    ¬(2*HeckeZeroSupremum.beta-1≤2*sigma-1) := by
  linarith

/-- The old 7/8 family bound remains explicit here. -/
theorem actualKappa_le_three_quarters
    (hbootstrap : HeckeZeroSupremum.beta≤7/8) :
    actualKappa≤3/4 := by
  unfold actualKappa
  linarith

theorem moving_range {sigma : ℝ} (hsigma : 87/100≤sigma)
    (hbad : sigma<HeckeZeroSupremum.beta)
    (hbootstrap : HeckeZeroSupremum.beta≤7/8) :
    37/50<actualKappa ∧ actualKappa≤3/4 ∧
      actualKappa-(2*sigma-1)=2*(HeckeZeroSupremum.beta-sigma) :=
  ⟨(actual_inputs hsigma hbad).1, actualKappa_le_three_quarters hbootstrap,
    actualKappa_reference_increment sigma⟩

end LiXiang.LowKappaParameters
