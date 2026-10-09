/-
Adapted from OpenAI/math SourceExclusions and ParametersFixedSource under Apache-2.0.
Upstream revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Proof by Li Xiang / lixiang90 (2026-10-09): select one finite excluded set
before every actual Hecke character and every later half-plane threshold.
The correction remains the original arithmetic sourceCorrection, with
w = 1, z = 1/6 and the same summable prime majorant. No zero-free premise.
-/
import OAI.NumberTheory.DirichletL.Detector.GlobalCorrectionLowKappa

namespace OAI
noncomputable section
namespace SevenEighths.PrincipalSignalComparison
open ProbePhysical CanonicalQuadraticSieve
local notation "Id" => Ideal ActualEisensteinCubic.O

/-- One finite set works for the whole actual character family. -/
theorem exists_actual_sourceCorrection_uniform_lowKappa :
    ∃ S : Finset Id, SourceExclusions S ∧
      ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (sourceCorrection eta S) {s : ℂ | 21/25 < s.re} ∧
        ∀ s : ℂ, 21/25 ≤ s.re → ‖sourceCorrection eta S s - 1‖ ≤ (1/2 : ℝ) := by
  have hp : ∀ P ∈ fixedBadPrimes, Prime P := by
    intro P hP
    rcases Finset.mem_insert.mp hP with hP | hP
    · subst P
      exact Ideal.prime_of_isPrime
        (Ideal.span_singleton_eq_bot.not.mpr PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero)
        lambdaIdeal_maximal.isPrime
    · have he := Finset.mem_singleton.mp hP
      subst P
      exact Ideal.prime_of_isPrime
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (2 : ActualEisensteinCubic.O) ≠ 0))
        twoIdeal_maximal.isPrime
  obtain ⟨S, _, hS⟩ := exists_source_exclusions fixedBadPrimes hp (Finset.Subset.refl _)
  refine ⟨S, hS, ?_⟩
  intro eta
  exact ⟨sourceCorrection_analytic_lowKappa eta S hS,
    fun s hs => sourceCorrection_bound_lowKappa eta S hS s hs⟩

/-- The same S supports every later target sigma, including the paper target. -/
theorem exists_actual_sourceCorrection_uniform_halfplanes_lowKappa :
    ∃ S : Finset Id, SourceExclusions S ∧
      ∀ sigma : ℝ, 21/25 ≤ sigma → ∀ eta : HeckeFamily.Character,
        AnalyticOnNhd ℂ (sourceCorrection eta S) {s : ℂ | sigma < s.re} ∧
        ∀ s : ℂ, sigma ≤ s.re → ‖sourceCorrection eta S s - 1‖ ≤ (1/2 : ℝ) := by
  obtain ⟨S, hS, hH⟩ := exists_actual_sourceCorrection_uniform_lowKappa
  refine ⟨S, hS, ?_⟩
  intro sigma hsigma eta
  exact ⟨(hH eta).1.mono (fun _ hs => hsigma.trans_lt hs),
    fun s hs => (hH eta).2 s (hsigma.trans hs)⟩

end SevenEighths.PrincipalSignalComparison
end
end OAI
