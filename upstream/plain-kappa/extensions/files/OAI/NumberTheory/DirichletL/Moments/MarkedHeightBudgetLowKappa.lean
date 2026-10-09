/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.MarkedHeightBudgetLowKappa

/-- The modulus and energy losses are fixed before the terminal/profile
degrees. The height exponent is chosen after those degrees, with any further
positive ceiling. This does not supply the actual source height inequalities. -/
theorem exists_losses_before_height (dmin εm : ℝ) (hdmin : 0 < dmin) (hεm : 0 < εm) :
    ∃ ρ εE : ℝ, 0 < ρ ∧ 0 < εE ∧
      ∀ degree J : ℕ, ∀ τ₀ : ℝ, 0 < τ₀ →
        ∃ τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧
          ρ + εE + 2 * τ * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm := by
  let loss := dmin * εm / 4
  have hloss : 0 < loss := by dsimp [loss]; positivity
  refine ⟨loss, loss, hloss, hloss, ?_⟩
  intro degree J τ₀ hτ₀
  let A : ℝ := (degree + 4 * J : ℕ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let τ := min τ₀ (dmin * εm / (8 * (A + 1)))
  have hτ : 0 < τ := lt_min hτ₀ (by positivity)
  have hmul : τ * (8 * (A + 1)) ≤ dmin * εm :=
    (le_div_iff₀ (by positivity : 0 < 8 * (A + 1))).mp (min_le_right _ _)
  refine ⟨τ, hτ, min_le_left _ _, ?_⟩
  change loss + loss + 2 * τ * A ≤ dmin * εm
  dsimp [loss]
  nlinarith only [hmul, hτ, hA]

private theorem profile_pow_bound (Z h x : ℝ) (n : ℕ)
    (hZ : 1 ≤ Z) (hh : 0 ≤ h) (hx : 0 ≤ x) (hxh : x ≤ Z^h) :
    (1 + x)^n ≤ (2 : ℝ)^n * Z^(h * (n : ℝ)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hbase : 1 ≤ Z^h := Real.one_le_rpow hZ hh
  calc
    (1 + x)^n ≤ (2 * Z^h)^n :=
      pow_le_pow_left₀ (by linarith only [hx]) (by linarith only [hbase, hxh]) n
    _ = (2 : ℝ)^n * Z^(h * (n : ℝ)) := by
      rw [mul_pow, Real.rpow_mul hZ0.le, Real.rpow_natCast]

/-- Absorb the actual finite-fiber bound's two height factors into
U^(1+epsilon_m), for U=Z^d. The squared detector-control exponent is 4J.
The coefficient here is the fixed nonnegative C*Cp^4*diagonalControl Phi. -/
theorem actual_growth_absorption
    (C Z d dmin ρ εE εm h height t : ℝ) (degree J : ℕ)
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hεm : 0 ≤ εm) (hh : 0 ≤ h) (hheight : 0 ≤ height)
    (hheight_le : height ≤ Z^h) (ht : ‖t‖ ≤ Z^h)
    (hbudget : ρ + εE + h * ((degree + 4 * J : ℕ) : ℝ) ≤ dmin * εm) :
    C * (1 + height)^degree * (1 + ‖t‖)^(4 * J) * Z^(d + ρ + εE) ≤
      (C * (2 : ℝ)^(degree + 4 * J)) * (Z^d)^(1 + εm) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hfirst := profile_pow_bound Z h height degree hZ hh hheight hheight_le
  have hsecond := profile_pow_bound Z h ‖t‖ (4 * J) hZ hh (norm_nonneg _) ht
  have hexp : h * (degree : ℝ) + h * ((4 * J : ℕ) : ℝ) + (d + ρ + εE) ≤
      d * (1 + εm) := by
    have hmono : dmin * εm ≤ d * εm := mul_le_mul_of_nonneg_right hd hεm
    push_cast at hbudget ⊢
    nlinarith only [hbudget, hmono]
  calc
    _ ≤ C * ((2 : ℝ)^degree * Z^(h * (degree : ℝ))) *
        ((2 : ℝ)^(4 * J) * Z^(h * ((4 * J : ℕ) : ℝ))) * Z^(d + ρ + εE) := by
      gcongr
    _ = (C * (2 : ℝ)^(degree + 4 * J)) *
        Z^(h * (degree : ℝ) + h * ((4 * J : ℕ) : ℝ) + (d + ρ + εE)) := by
      simp_rw [pow_add, Real.rpow_add hZ0]
      ring
    _ ≤ (C * (2 : ℝ)^(degree + 4 * J)) * Z^(d * (1 + εm)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity)
    _ = _ := by rw [Real.rpow_mul hZ0.le]

end OAI.SevenEighths.MarkedHeightBudgetLowKappa
