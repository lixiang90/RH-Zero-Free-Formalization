/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual detector Schwartz profile pair and its squared source control.
One degree and constant are chosen after the finite seminorm set and before
all orientations, derivative indices, real shifts and frequencies. The actual
profile-control square retains the C^4 and frequency exponent 4*J. -/
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPair

noncomputable section
open scoped Classical SchwartzMap
namespace OAI.SevenEighths.DetectorPairControl
set_option autoImplicit false
open CenteredMomentDetectorDictionary CenteredMomentFiniteProfileExceptional
open HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles

def detectorPairProfiles (reverse : Bool) (j k : ℕ) (σ t : ℝ) : Profiles (1/4) (9/4) where
  profile q := if q = 0 then detectorSchwartz reverse j σ t else detectorSchwartz reverse k σ t
  support q := by
    have hs (n : ℕ) : Function.support (detectorSchwartz reverse n σ t : ℝ → ℂ) ⊆
        Set.Icc (1/4) (9/4) := by
      intro x hx
      change detectorSchwartz reverse n σ t x ≠ 0 at hx
      rw [detectorSchwartz_apply] at hx
      exact detector_profile_support reverse n σ (orientedFrequency reverse t) hx
    split_ifs
    · exact hs j
    · exact hs k

theorem detectorPairProfiles_squared_control_uniform (S : Finset (ℕ × ℕ)) :
    ∃J : ℕ, ∃C : ℝ, 0 < C ∧ ∀reverse : Bool, ∀j k : ℕ, j ≤ 2 → k ≤ 2 →
      ∀σ ∈ Set.Icc (0 : ℝ) 1, ∀t : ℝ,
        ((detectorPairProfiles reverse j k σ t).control S)^2 ≤
          C^4 * (1 + ‖t‖)^(4 * J) := by
  obtain ⟨J, C, hC, hb⟩ := detectorSchwartz_uniform S
  refine ⟨J, C, hC, ?_⟩
  intro reverse j k hj hk σ hσ t
  let p := detectorPairProfiles reverse j k σ t
  have hj' : sourceControl S (p.profile 0) ≤ C * (1 + ‖t‖)^J := by
    simpa [p, sourceControl, detectorPairProfiles] using hb reverse j hj σ hσ t
  have hk' : sourceControl S (p.profile 1) ≤ C * (1 + ‖t‖)^J := by
    simpa [p, sourceControl, detectorPairProfiles] using hb reverse k hk σ hσ t
  have hprod : p.control S ≤ (C * (1 + ‖t‖)^J)^2 := by
    calc
      _ ≤ (C * (1 + ‖t‖)^J) * (C * (1 + ‖t‖)^J) :=
        mul_le_mul hj' hk' (sourceControl_nonneg S _) (by positivity)
      _ = _ := by ring
  have hsq : (p.control S)^2 ≤ ((C * (1 + ‖t‖)^J)^2)^2 :=
    pow_le_pow_left₀ (Profiles.control_nonneg p S) hprod 2
  apply hsq.trans_eq
  calc
    _ = (C * (1 + ‖t‖)^J)^4 := by ring
    _ = C^4 * ((1 + ‖t‖)^J)^4 := mul_pow _ _ _
    _ = C^4 * (1 + ‖t‖)^(4 * J) := by rw [←pow_mul, Nat.mul_comm J 4]

end OAI.SevenEighths.DetectorPairControl
