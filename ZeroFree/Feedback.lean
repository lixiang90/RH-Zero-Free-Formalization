import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/- Exact finite parameter feedback for the rational critical-count envelope.
   Arithmetic realization of these count estimates is still a separate proof obligation. -/
noncomputable section
namespace ZeroFree.Feedback

def D (k x : ℝ) : ℝ := 3 - (1 + 2 / (3 * k)) * x
def P (k x : ℝ) : ℝ := (2 - 2 * x / (3 * k)) * (1 - x)
def J (k δ x : ℝ) : ℝ := (5 / 6 - δ) * D k x + δ * P k x
def count (k δ x : ℝ) : ℝ :=
  1 - δ + (5 / 6 - δ) * δ * P k x / (2 * J k δ x)

theorem shape_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ x * (1 - x) ^ 2 ∧ x * (1 - x) ^ 2 ≤ 4 / 27 := by
  constructor
  · positivity
  · have hid : 4 / 27 - x * (1 - x) ^ 2 =
        (x - 1 / 3) ^ 2 * (4 / 3 - x) := by ring
    have hs : 0 ≤ (x - 1 / 3) ^ 2 * (4 / 3 - x) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    linarith

theorem D_ge_two {k x : ℝ} (hk : 37 / 50 ≤ k)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 2 ≤ D k x := by
  have hk0 : 0 < k := by linarith
  have ht0 : 0 ≤ 2 / (3 * k) := by positivity
  have ht1 : 2 / (3 * k) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * k)).2
    linarith
  have hm : (1 + 2 / (3 * k)) * x ≤ 2 * (1 / 2) :=
    mul_le_mul (by linarith) hx1 hx0 (by norm_num)
  unfold D
  linarith

theorem P_nonneg {k x : ℝ} (hk : 37 / 50 ≤ k)
    (_hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 0 ≤ P k x := by
  have hk0 : 0 < k := by linarith
  have ht : 2 * x / (3 * k) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * k)).2
    linarith
  unfold P
  exact mul_nonneg (by linarith) (by linarith)

theorem J_lower {k δ x : ℝ} (hk : 37 / 50 ≤ k)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    2 * (5 / 6 - δ) ≤ J k δ x := by
  have hD := D_ge_two hk hx0 hx1
  have hP := P_nonneg hk hx0 hx1
  have hm := mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ 5 / 6 - δ)
  have hn := mul_nonneg hd0 hP
  unfold J
  linarith

theorem J_pos {k δ x : ℝ} (hk : 37 / 50 ≤ k)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 0 < J k δ x := by
  have h := J_lower hk hd0 hd1 hx0 hx1
  linarith

theorem count_difference {k₁ k₂ δ x : ℝ}
    (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hJ₁ : J k₁ δ x ≠ 0) (hJ₂ : J k₂ δ x ≠ 0) :
    count k₂ δ x - count k₁ δ x =
      (5 / 6 - δ) ^ 2 * δ * (x * (1 - x) ^ 2) * (k₂ - k₁) /
      (3 * k₁ * k₂ * J k₁ δ x * J k₂ δ x) := by
  unfold count
  field_simp
  unfold J D P
  field_simp
  ring


/-- A finite-difference coefficient bound; no differentiability or mean-value
    estimate is imported as a hypothesis. -/
theorem difference_coefficient_bound {k₁ k₂ δ x : ℝ}
    (hk₁ : 37 / 50 ≤ k₁) (hk₂ : 37 / 50 ≤ k₂)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ (5 / 6 - δ) ^ 2 * δ * (x * (1 - x) ^ 2) /
      (3 * k₁ * k₂ * J k₁ δ x * J k₂ δ x) ∧
    (5 / 6 - δ) ^ 2 * δ * (x * (1 - x) ^ 2) /
      (3 * k₁ * k₂ * J k₁ δ x * J k₂ δ x) ≤ 625 / 36963 := by
  have hk₁0 : 0 < k₁ := by linarith
  have hk₂0 : 0 < k₂ := by linarith
  have hJ₁0 := J_pos hk₁ hd0 hd1 hx0 hx1
  have hJ₂0 := J_pos hk₂ hd0 hd1 hx0 hx1
  have hden0 : 0 < 3 * k₁ * k₂ * J k₁ δ x * J k₂ δ x := by positivity
  have hshape := shape_bound hx0 hx1
  have ha : 0 < 5 / 6 - δ := by linarith
  have ha2 : 0 ≤ (5 / 6 - δ) ^ 2 := sq_nonneg _
  have hkp : (37 / 50 : ℝ) * (37 / 50) ≤ k₁ * k₂ :=
    mul_le_mul hk₁ hk₂ (by norm_num) (le_of_lt hk₁0)
  have hJ₁ := J_lower hk₁ hd0 hd1 hx0 hx1
  have hJ₂ := J_lower hk₂ hd0 hd1 hx0 hx1
  have hjjp : 4 * (5 / 6 - δ) ^ 2 ≤ J k₁ δ x * J k₂ δ x := by
    have ht := mul_le_mul hJ₁ hJ₂ (by positivity) (le_of_lt hJ₁0)
    nlinarith only [ht]
  have hprod := mul_le_mul hkp hjjp (by positivity) (by positivity)
  have hden : (4107 / 625 : ℝ) * (5 / 6 - δ) ^ 2 ≤
      3 * k₁ * k₂ * J k₁ δ x * J k₂ δ x := by
    nlinarith only [hprod]
  have hdw : δ * (x * (1 - x) ^ 2) ≤ 1 / 9 := by
    have ht := mul_le_mul hd1 hshape.2 hshape.1 (by norm_num)
    norm_num at ht
    exact ht
  have hnum : (5 / 6 - δ) ^ 2 * δ * (x * (1 - x) ^ 2) ≤
      (5 / 6 - δ) ^ 2 / 9 := by
    have ht := mul_le_mul_of_nonneg_left hdw ha2
    nlinarith only [ht]
  constructor
  · positivity
  · apply (div_le_iff₀ hden0).2
    nlinarith only [hden, hnum]

/-- Both monotonicity and the Lipschitz cost follow from exact rational algebra. -/
theorem count_increment {k₁ k₂ δ x : ℝ}
    (hk₁ : 37 / 50 ≤ k₁) (hk₂ : 37 / 50 ≤ k₂) (hkk : k₁ ≤ k₂)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    0 ≤ count k₂ δ x - count k₁ δ x ∧
      count k₂ δ x - count k₁ δ x ≤ (k₂ - k₁) / 50 := by
  have hk₁0 : 0 < k₁ := by linarith
  have hk₂0 : 0 < k₂ := by linarith
  have hJ₁0 := J_pos hk₁ hd0 hd1 hx0 hx1
  have hJ₂0 := J_pos hk₂ hd0 hd1 hx0 hx1
  have hc := difference_coefficient_bound hk₁ hk₂ hd0 hd1 hx0 hx1
  have hstep : 0 ≤ k₂ - k₁ := by linarith
  have hsmall : (625 / 36963 : ℝ) ≤ 1 / 50 := by norm_num
  have hid := count_difference (ne_of_gt hk₁0) (ne_of_gt hk₂0)
    (ne_of_gt hJ₁0) (ne_of_gt hJ₂0)
  rw [hid]
  have hfactor :
      (5 / 6 - δ) ^ 2 * δ * (x * (1 - x) ^ 2) * (k₂ - k₁) /
        (3 * k₁ * k₂ * J k₁ δ x * J k₂ δ x) =
      ((5 / 6 - δ) ^ 2 * δ * (x * (1 - x) ^ 2) /
        (3 * k₁ * k₂ * J k₁ δ x * J k₂ δ x)) * (k₂ - k₁) := by ring
  rw [hfactor]
  constructor
  · exact mul_nonneg hc.1 hstep
  · have ht := mul_le_mul_of_nonneg_right (le_trans hc.2 hsmall) hstep
    nlinarith only [ht]

/-- Actual-parameter feedback at the reference endpoint. -/
theorem endpoint_saving {k₁ k₂ δ x Δ h Eref : ℝ}
    (hk₁ : 37 / 50 ≤ k₁) (hk₂ : 37 / 50 ≤ k₂)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hΔ : 0 < Δ) (hactual : k₂ - k₁ = 2 * Δ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (href : Eref ≤ 0) :
    Eref - Δ + h * (count k₂ δ x - count k₁ δ x) ≤
      -(24 / 25) * Δ := by
  have hkk : k₁ ≤ k₂ := by linarith
  have hinc := count_increment hk₁ hk₂ hkk hd0 hd1 hx0 hx1
  have hmul := mul_le_mul_of_nonneg_left hinc.2 hh0
  have hmul2 := mul_le_mul_of_nonneg_right hh1 (by linarith : 0 ≤ (k₂ - k₁) / 50)
  nlinarith only [hmul, hmul2, hactual, href]

/-- Extending the physical range by Δ/32 consumes at most Δ/16. -/
theorem extended_saving {Δ h d slope Eendpoint : ℝ}
    (hΔ : 0 < Δ) (hendpoint : Eendpoint ≤ -(24 / 25) * Δ)
    (hs0 : 0 ≤ slope) (hs2 : slope ≤ 2)
    (hd : d ≤ h + Δ / 32) :
    Eendpoint + (d - h) * slope ≤ -(359 / 400) * Δ := by
  have hmul := mul_le_mul_of_nonneg_right (by linarith : d - h ≤ Δ / 32) hs0
  have hmul2 := mul_le_mul_of_nonneg_left hs2 (by linarith : 0 ≤ Δ / 32)
  nlinarith only [hmul, hmul2, hendpoint]

/-- The total strict margin before allocating any further real losses. -/
theorem full_feedback_saving {k₁ k₂ δ x Δ h d slope Eref : ℝ}
    (hk₁ : 37 / 50 ≤ k₁) (hk₂ : 37 / 50 ≤ k₂)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hΔ : 0 < Δ) (hactual : k₂ - k₁ = 2 * Δ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (href : Eref ≤ 0)
    (hs0 : 0 ≤ slope) (hs2 : slope ≤ 2) (hd : d ≤ h + Δ / 32) :
    Eref - Δ + h * (count k₂ δ x - count k₁ δ x) +
      (d - h) * slope ≤ -(359 / 400) * Δ :=
  extended_saving hΔ
    (endpoint_saving hk₁ hk₂ hd0 hd1 hx0 hx1 hΔ hactual hh0 hh1 href)
    hs0 hs2 hd


/-- The count bounds needed for the physical-row slope are derived from J. -/
theorem count_bounds {k δ x : ℝ} (hk : 37 / 50 ≤ k)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 - δ ≤ count k δ x ∧ count k δ x ≤ 1 - δ + (5 / 6 - δ) / 2 := by
  have hD := D_ge_two hk hx0 hx1
  have hP := P_nonneg hk hx0 hx1
  have hJ := J_pos hk hd0 hd1 hx0 hx1
  have ha : 0 ≤ 5 / 6 - δ := by linarith
  have hDP : δ * P k x ≤ J k δ x := by
    unfold J
    have ht := mul_nonneg ha (by linarith : 0 ≤ D k x)
    linarith
  have hr0 : 0 ≤ (5 / 6 - δ) * δ * P k x / (2 * J k δ x) := by positivity
  have hr1 : (5 / 6 - δ) * δ * P k x / (2 * J k δ x) ≤ (5 / 6 - δ) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * J k δ x)).2
    have ht := mul_le_mul_of_nonneg_left hDP ha
    nlinarith only [ht]
  unfold count
  constructor <;> linarith

theorem physical_slope_bounds {k δ x : ℝ} (hk : 37 / 50 ≤ k)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    57 / 200 ≤ count k δ x + δ / 2 - 17 / 50 ∧
      count k δ x + δ / 2 - 17 / 50 ≤ 323 / 300 := by
  have hb := count_bounds hk hd0 hd1 hx0 hx1
  constructor <;> linarith

/-- No physical-row slope assumption is needed when using the derived envelope. -/
theorem physical_feedback_saving {k₁ k₂ δ x Δ h d Eref : ℝ}
    (hk₁ : 37 / 50 ≤ k₁) (hk₂ : 37 / 50 ≤ k₂)
    (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hΔ : 0 < Δ) (hactual : k₂ - k₁ = 2 * Δ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (href : Eref ≤ 0)
    (hd : d ≤ h + Δ / 32) :
    Eref - Δ + h * (count k₂ δ x - count k₁ δ x) +
      (d - h) * (count k₂ δ x + δ / 2 - 17 / 50) ≤ -(359 / 400) * Δ := by
  have hs := physical_slope_bounds hk₂ hd0 hd1 hx0 hx1
  exact full_feedback_saving hk₁ hk₂ hd0 hd1 hx0 hx1 hΔ hactual
    hh0 hh1 href (by linarith) (by linarith) hd

theorem actual_parameter_range {σ β : ℝ}
    (hσ : 87 / 100 ≤ σ) (hσβ : σ ≤ β) (hβ : β ≤ 7 / 8) :
    37 / 50 ≤ 2 * β - 1 ∧ 2 * β - 1 ≤ 3 / 4 ∧
      (2 * β - 1) - (2 * σ - 1) = 2 * (β - σ) := by
  constructor
  · linarith
  constructor
  · linarith
  · ring

end ZeroFree.Feedback


