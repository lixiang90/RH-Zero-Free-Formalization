import ZeroFree.Signal

/- The height cutoff is chosen before the tail order. All powers in the
   pointwise high estimate have fixed exponents independent of that order. -/
set_option autoImplicit false

noncomputable section
namespace ZeroFree.HeightClosure
open Filter Asymptotics
open scoped Topology

/-- An explicit admissible height exponent, independent of the tail order. -/
def heightExponent (m A τ₀ : ℝ) : ℝ :=
  min τ₀ (min (1 / 10000) (m / (4 * (A + 1))))

theorem heightExponent_spec {m A τ₀ : ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hτ₀ : 0 < τ₀) :
    0 < heightExponent m A τ₀ ∧
    heightExponent m A τ₀ ≤ τ₀ ∧
    heightExponent m A τ₀ ≤ 1 / 10000 ∧
    A * heightExponent m A τ₀ ≤ m / 4 := by
  have hden : 0 < 4 * (A + 1) := by positivity
  have hpos : 0 < heightExponent m A τ₀ := by
    unfold heightExponent
    exact lt_min hτ₀ (lt_min (by norm_num) (div_pos hm hden))
  have hle : heightExponent m A τ₀ ≤ m / (4 * (A + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmul : heightExponent m A τ₀ * (4 * (A + 1)) ≤ m :=
    (le_div_iff₀ hden).mp hle
  refine ⟨hpos, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  nlinarith

/-- The tail order is chosen only after the positive height exponent is fixed. -/
theorem exists_tail_order {τ : ℝ} (hτ : 0 < τ) (B target : ℝ) :
    ∃ N : ℕ, B - (N : ℝ) * τ < target := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((B - target) / τ)
  refine ⟨N, ?_⟩
  have hmul : B - target < (N : ℝ) * τ := (div_lt_iff₀ hτ).mp hN
  linarith

/-- Deterministic power estimate for a legal cutoff T = x^τ. -/
theorem cutoff_terms_bound {x β c m A B τ : ℝ} {N : ℕ}
    (hx : 1 ≤ x) (hm : 0 ≤ m) (hA : 0 ≤ A) (hτ : 0 ≤ τ)
    (hsmall : A * τ ≤ m / 4)
    (htail : B - (N : ℝ) * τ ≤ β + c - m / 2) :
    x ^ (β + c - m) * (1 + x ^ τ) ^ A +
      x ^ B * (x ^ τ) ^ (-(N : ℝ)) ≤
        (2 ^ A + 1) * x ^ (β + c - m / 2) := by
  have hx0 : 0 < x := by linarith
  have hT : 1 ≤ x ^ τ := Real.one_le_rpow hx hτ
  have hgrow : (1 + x ^ τ) ^ A ≤
      (2 : ℝ) ^ A * x ^ (τ * A) := by
    calc
      (1 + x ^ τ) ^ A ≤ (2 * x ^ τ) ^ A :=
        Real.rpow_le_rpow (by positivity) (by linarith) hA
      _ = (2 : ℝ) ^ A * x ^ (τ * A) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hx0.le _),
          ← Real.rpow_mul hx0.le]
  have hfirst : x ^ (β + c - m) * (1 + x ^ τ) ^ A ≤
      (2 : ℝ) ^ A * x ^ (β + c - m / 2) := by
    calc
      x ^ (β + c - m) * (1 + x ^ τ) ^ A ≤
          x ^ (β + c - m) * ((2 : ℝ) ^ A * x ^ (τ * A)) :=
        mul_le_mul_of_nonneg_left hgrow (Real.rpow_nonneg hx0.le _)
      _ = (2 : ℝ) ^ A * x ^ (β + c - m + τ * A) := by
        rw [Real.rpow_add hx0]
        ring
      _ ≤ (2 : ℝ) ^ A * x ^ (β + c - m / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hx (by nlinarith))
          (by positivity)
  have hsecond : x ^ B * (x ^ τ) ^ (-(N : ℝ)) ≤
      x ^ (β + c - m / 2) := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  calc
    _ ≤ (2 : ℝ) ^ A * x ^ (β + c - m / 2) +
        x ^ (β + c - m / 2) := add_le_add hfirst hsecond
    _ = _ := by ring

/-- Raw high-frequency estimates with the height ceiling explicitly quantified.
The constants may depend on N. The exponents A and B cannot depend on N. -/
def HighEstimate (E : ℝ → ℂ) (β c m A B τ₀ : ℝ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ x : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ x ^ τ₀ →
      ‖E x‖ ≤ C * (x ^ (β + c - m) * (1 + T) ^ A +
        x ^ B * T ^ (-(N : ℝ)))

/-- Eliminates the adjustable height and tail order from the raw estimate.
The resulting positive saving is m/2; no asymptotic collapse is assumed. -/
theorem collapse_high_estimate {E : ℝ → ℂ} {β c m A B τ₀ : ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hτ₀ : 0 < τ₀)
    (hhigh : HighEstimate E β c m A B τ₀) :
    E =O[atTop] (fun x : ℝ => x ^ (β + c - m / 2)) := by
  obtain ⟨hτ, hceil, _, hsmall⟩ := heightExponent_spec hm hA hτ₀
  obtain ⟨N, hN⟩ := exists_tail_order hτ B (β + c - m / 2)
  obtain ⟨C, hC, hbound⟩ := hhigh N
  apply IsBigO.of_bound (C * ((2 : ℝ) ^ A + 1))
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hbx hx
  have hT : 1 ≤ x ^ heightExponent m A τ₀ :=
    Real.one_le_rpow hx hτ.le
  have hTceil : x ^ heightExponent m A τ₀ ≤ x ^ τ₀ :=
    Real.rpow_le_rpow_of_exponent_le hx hceil
  have hterms := cutoff_terms_bound (β:=β) (c:=c) (B:=B)
    hx hm.le hA hτ.le hsmall hN.le
  have hb := (hbx _ hT hTceil).trans (mul_le_mul_of_nonneg_left hterms hC)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _), mul_assoc] using hb

/-- Uniform savings across a family; cutoff exponents and constants may depend
on the member, but the same strictly positive m is used in the conclusion. -/
theorem collapse_high_estimate_family {ι : Type*} {E : ι → ℝ → ℂ}
    {β c m : ℝ} {A B τ₀ : ι → ℝ}
    (hm : 0 < m) (hA : ∀ i, 0 ≤ A i) (hτ₀ : ∀ i, 0 < τ₀ i)
    (hhigh : ∀ i, HighEstimate (E i) β c m (A i) (B i) (τ₀ i)) :
    ∀ i, E i =O[atTop] (fun x : ℝ => x ^ (β + c - m / 2)) :=
  fun i => collapse_high_estimate hm (hA i) (hτ₀ i) (hhigh i)

/-- The common analytic signal bound now follows directly from the raw high
estimate and the low-frequency bound. Its margin remains the same for a family. -/
theorem common_signal_bound_of_high_estimate (J f : ℝ → ℂ)
    (σ β ω c m A B τ₀ : ℝ) (hm : 0 < m) (hA : 0 ≤ A) (hτ₀ : 0 < τ₀)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (σ + c + ω)))
    (hhigh : HighEstimate (fun x => J x - f x) β c m A B τ₀) :
    f =O[atTop] (fun x : ℝ =>
      x ^ (β + c - Signal.margin σ β ω (m / 2))) :=
  Signal.common_signal_bound_with_margin J f σ β ω (m / 2) c hJ
    (collapse_high_estimate hm hA hτ₀ hhigh)

end ZeroFree.HeightClosure
