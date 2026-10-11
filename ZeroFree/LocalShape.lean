import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Finite algebra for local zero-free shape certificates

This file proves rational corner values, positivity on the entire rectangle,
the paired Poisson-kernel identity, and a conditional exclusion implication.
It does not define the Riemann zeta function or certify the external Arb
evaluation or the Hadamard/logarithmic-derivative input.  Those analytic inputs
occur only as explicit hypotheses of the exclusion theorems.
The finite weighted-anchor extension also keeps every kernel budget explicit.
-/

set_option maxHeartbeats 500000

noncomputable section
namespace ZeroFree.LocalShape

def sigmaC : ℝ := 219 / 250
def heightC : ℝ := 4000000000000
def pairC : ℝ := 94 / 125
def energy : ℝ := 29 / 2
def pLo : ℝ := 751 / 1000000
def pHi : ℝ := 3211 / 62500
def zHi : ℝ := 1 / 40000

def pairDen (p z : ℝ) : ℝ := (p - z) ^ 2 + pairC ^ 2 * z
def surplus (p z : ℝ) : ℝ := pairC * (p + z) - energy * pairDen p z
def pairKernel (p z : ℝ) : ℝ := pairC * (p + z) / pairDen p z

theorem corner_lo_zero :
    surplus pLo 0 = 1113147971 / 2000000000000 := by
  norm_num [surplus, pairDen, pairC, energy, pLo]

theorem corner_hi_zero :
    surplus pHi 0 = 2828891 / 7812500000 := by
  norm_num [surplus, pairDen, pairC, energy, pHi]

theorem corner_lo_hi :
    surplus pLo zHi = 185457099 / 500000000000 := by
  norm_num [surplus, pairDen, pairC, energy, pLo, zHi]

theorem corner_hi_hi :
    surplus pHi zHi = 426282771 / 2000000000000 := by
  norm_num [surplus, pairDen, pairC, energy, pHi, zHi]

/-- Endpoint positivity implies positivity inside a concave quadratic segment. -/
theorem concave_quadratic_pos {a b c l u x : ℝ}
    (ha : 0 ≤ a) (hlu : l < u) (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : 0 < -a * l ^ 2 + b * l + c)
    (hu : 0 < -a * u ^ 2 + b * u + c) :
    0 < -a * x ^ 2 + b * x + c := by
  let f : ℝ → ℝ := fun t => -a * t ^ 2 + b * t + c
  have hfl : 0 < f l := hl
  have hfu : 0 < f u := hu
  have hw : 0 < (u - x) * f l + (x - l) * f u := by
    by_cases hxu' : x < u
    · have h1 : 0 < (u - x) * f l := mul_pos (by linarith) hfl
      have h2 : 0 ≤ (x - l) * f u := mul_nonneg (by linarith) (le_of_lt hfu)
      linarith
    · have hxeq : x = u := le_antisymm hxu (le_of_not_gt hxu')
      rw [hxeq]
      simp only [sub_self, zero_mul, zero_add]
      exact mul_pos (by linarith) hfu
  have hs : 0 ≤ a * (x - l) * (u - x) * (u - l) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)) (by linarith)
  have hid : (u - l) * f x =
      (u - x) * f l + (x - l) * f u +
        a * (x - l) * (u - x) * (u - l) := by
    dsimp [f]
    ring
  have hp : 0 < (u - l) * f x := by linarith
  have hfx : 0 < f x := (mul_pos_iff_of_pos_left (by linarith : 0 < u - l)).mp hp
  exact hfx

theorem surplus_pos {p z : ℝ}
    (hpLo : pLo ≤ p) (hpHi : p ≤ pHi)
    (hzLo : 0 ≤ z) (hzHi : z ≤ zHi) : 0 < surplus p z := by
  have hE : 0 ≤ energy := by norm_num [energy]
  have hpRange : pLo < pHi := by norm_num [pLo, pHi]
  have hzRange : (0 : ℝ) < zHi := by norm_num [zHi]
  have hlo0 : 0 < surplus pLo 0 := by rw [corner_lo_zero]; norm_num
  have hhi0 : 0 < surplus pHi 0 := by rw [corner_hi_zero]; norm_num
  have hlo1 : 0 < surplus pLo zHi := by rw [corner_lo_hi]; norm_num
  have hhi1 : 0 < surplus pHi zHi := by rw [corner_hi_hi]; norm_num
  have hform (p z : ℝ) : surplus p z =
      -energy * p ^ 2 + (pairC + 2 * energy * z) * p +
        (pairC * z - energy * z ^ 2 - energy * pairC ^ 2 * z) := by
    unfold surplus pairDen
    ring
  have hz0 : 0 < surplus p 0 := by
    rw [hform]
    apply concave_quadratic_pos hE hpRange hpLo hpHi
    · simpa only [← hform] using hlo0
    · simpa only [← hform] using hhi0
  have hz1 : 0 < surplus p zHi := by
    rw [hform]
    apply concave_quadratic_pos hE hpRange hpLo hpHi
    · simpa only [← hform] using hlo1
    · simpa only [← hform] using hhi1
  have hformZ (p z : ℝ) : surplus p z =
      -energy * z ^ 2 + (pairC + 2 * energy * p - energy * pairC ^ 2) * z +
        (pairC * p - energy * p ^ 2) := by
    unfold surplus pairDen
    ring
  rw [hformZ]
  apply concave_quadratic_pos hE hzRange hzLo hzHi
  · simpa only [← hformZ] using hz0
  · simpa only [← hformZ] using hz1

theorem pair_den_pos {p z : ℝ} (hp : 0 < p) (hz : 0 ≤ z) :
    0 < pairDen p z := by
  unfold pairDen
  by_cases hz0 : z = 0
  · simp only [hz0, sub_zero, mul_zero, add_zero]
    exact sq_pos_of_pos hp
  · have hzPos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hc : 0 < pairC ^ 2 := by norm_num [pairC]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hc hzPos)

theorem pair_kernel_gt_of_surplus {p z : ℝ}
    (hp : 0 < p) (hz : 0 ≤ z) (hs : 0 < surplus p z) :
    energy < pairKernel p z := by
  have hd := pair_den_pos hp hz
  unfold pairKernel
  apply (lt_div_iff₀ hd).2
  unfold surplus at hs
  linarith

theorem pair_kernel_gt_energy {p z : ℝ}
    (hpLo : pLo ≤ p) (hpHi : p ≤ pHi)
    (hzLo : 0 ≤ z) (hzHi : z ≤ zHi) : energy < pairKernel p z := by
  have hp : 0 < p := lt_of_lt_of_le (by norm_num [pLo]) hpLo
  exact pair_kernel_gt_of_surplus hp hzLo (surplus_pos hpLo hpHi hzLo hzHi)

theorem pair_kernel_identity {a b z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z) (hab : a + b = pairC) :
    pairKernel (a * b) z = a / (a ^ 2 + z) + b / (b ^ 2 + z) := by
  have hA : 0 < a ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) hz
  have hB : 0 < b ^ 2 + z := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) hz
  have hD := pair_den_pos (mul_pos ha hb) hz
  unfold pairKernel
  field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hD]
  unfold pairDen
  rw [← hab]
  ring

def zeroProduct (beta : ℝ) : ℝ := (sigmaC - beta) * (sigmaC + beta - 1)
def zeroHeightSquare (t : ℝ) : ℝ := (t - heightC) ^ 2

theorem zero_product_bounds {beta : ℝ} (hLo : 4 / 5 ≤ beta) (hHi : beta ≤ 7 / 8) :
    pLo ≤ zeroProduct beta ∧ zeroProduct beta ≤ pHi := by
  have hlo : zeroProduct beta - pLo = (7 / 8 - beta) * (beta - 1 / 8) := by
    unfold zeroProduct sigmaC pLo
    ring
  have hhi : pHi - zeroProduct beta = (beta - 4 / 5) * (beta - 1 / 5) := by
    unfold zeroProduct sigmaC pHi
    ring
  have h1 : 0 ≤ (7 / 8 - beta) * (beta - 1 / 8) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (beta - 4 / 5) * (beta - 1 / 5) :=
    mul_nonneg (by linarith) (by linarith)
  constructor <;> linarith

theorem zero_height_bounds {t : ℝ} (ht : |t - heightC| ≤ 1 / 200) :
    0 ≤ zeroHeightSquare t ∧ zeroHeightSquare t ≤ zHi := by
  have hb := abs_le.mp ht
  have hm : 0 ≤ (t - heightC + 1 / 200) * (1 / 200 - (t - heightC)) :=
    mul_nonneg (by linarith [hb.1]) (by linarith [hb.2])
  constructor
  · exact sq_nonneg _
  · unfold zeroHeightSquare zHi
    nlinarith only [hm]

/-- Conditional exclusion: `hAnalytic` must be supplied by a separately certified
    analytic theorem and a certified numeric upper bound. -/
theorem rectangle_exclusion {IsZero : ℝ → ℝ → Prop} {beta t : ℝ}
    (hLo : 4 / 5 ≤ beta) (hHi : beta ≤ 7 / 8)
    (ht : |t - heightC| ≤ 1 / 200)
    (hAnalytic : IsZero beta t →
      pairKernel (zeroProduct beta) (zeroHeightSquare t) ≤ energy) :
    ¬ IsZero beta t := by
  have hp := zero_product_bounds hLo hHi
  have hz := zero_height_bounds ht
  have hk := pair_kernel_gt_energy hp.1 hp.2 hz.1 hz.2
  intro hZero
  exact (not_le_of_gt hk) (hAnalytic hZero)

/-- This conditional theorem excludes the full quartic surplus region, with
    no restriction to the smaller rectangle. -/
theorem quartic_shape_exclusion {IsZero : ℝ → ℝ → Prop} {beta t : ℝ}
    (hp : 0 < zeroProduct beta)
    (hShape : 0 < surplus (zeroProduct beta) (zeroHeightSquare t))
    (hAnalytic : IsZero beta t →
      pairKernel (zeroProduct beta) (zeroHeightSquare t) ≤ energy) :
    ¬ IsZero beta t := by
  have hz : 0 ≤ zeroHeightSquare t := sq_nonneg _
  have hk := pair_kernel_gt_of_surplus hp hz hShape
  intro hZero
  exact (not_le_of_gt hk) (hAnalytic hZero)

/-- A convenient rectangle interface when the global strip is an imported
    hypothesis rather than a theorem proved in this file. -/
theorem rectangle_exclusion_of_global_bound
    {IsZero : ℝ → ℝ → Prop} {beta t : ℝ}
    (hGlobal : ∀ beta t, IsZero beta t → beta ≤ 7 / 8)
    (hLo : 4 / 5 ≤ beta) (ht : |t - heightC| ≤ 1 / 200)
    (hAnalytic : IsZero beta t →
      pairKernel (zeroProduct beta) (zeroHeightSquare t) ≤ energy) :
    ¬ IsZero beta t := by
  intro hZero
  exact rectangle_exclusion hLo (hGlobal beta t hZero) ht hAnalytic hZero

def singleKernel (a u : ℝ) : ℝ := a / (a ^ 2 + u ^ 2)

/-- The open disk of radius 1/29 is the strict one-kernel exclusion disk. -/
theorem single_disk_kernel_gt {a u : ℝ}
    (hdisk : (a - 1 / 29) ^ 2 + u ^ 2 < (1 / 29) ^ 2) :
    energy < singleKernel a u := by
  have ha : 0 < a := by nlinarith [sq_nonneg a, sq_nonneg u]
  have hden : 0 < a ^ 2 + u ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg u)
  unfold singleKernel
  apply (lt_div_iff₀ hden).2
  norm_num [energy]
  nlinarith only [hdisk]

theorem single_disk_exclusion {IsZero : ℝ → ℝ → Prop} {beta t : ℝ}
    (hdisk : (beta - (sigmaC - 1 / 29)) ^ 2 + (t - heightC) ^ 2 <
      (1 / 29) ^ 2)
    (hAnalytic : IsZero beta t →
      singleKernel (sigmaC - beta) (t - heightC) ≤ energy) :
    ¬ IsZero beta t := by
  have hdisk' : ((sigmaC - beta) - 1 / 29) ^ 2 + (t - heightC) ^ 2 <
      (1 / 29) ^ 2 := by
    convert hdisk using 1
    ring
  have hk := single_disk_kernel_gt hdisk'
  intro hZero
  exact (not_le_of_gt hk) (hAnalytic hZero)


/-- A reflected pair of kernels at an arbitrary real anchor. -/
def anchoredPairKernel (sigma height beta t : ℝ) : ℝ :=
  singleKernel (sigma - beta) (t - height) +
    singleKernel (sigma + beta - 1) (t - height)

/-- The quartic rational kernel is the reflected pair at the certified anchor. -/
theorem pair_kernel_at_anchor {beta t : ℝ}
    (hLo : 1 / 2 < beta) (hHi : beta ≤ 7 / 8) :
    pairKernel (zeroProduct beta) (zeroHeightSquare t) =
      anchoredPairKernel sigmaC heightC beta t := by
  have ha : 0 < sigmaC - beta := by norm_num [sigmaC] at *; linarith
  have hb : 0 < sigmaC + beta - 1 := by norm_num [sigmaC] at *; linarith
  have hab : (sigmaC - beta) + (sigmaC + beta - 1) = pairC := by
    norm_num [sigmaC, pairC]
    ring
  simpa only [zeroProduct, zeroHeightSquare, anchoredPairKernel, singleKernel] using
    pair_kernel_identity ha hb (sq_nonneg (t - heightC)) hab

/-- Nonnegative rational or real weights preserve every supplied kernel budget.
No analytic summation identity is assumed or proved by this finite inequality. -/
theorem finite_weighted_kernel_bound {ι : Type*} (anchors : Finset ι)
    (weight value budget : ι → ℝ)
    (hWeight : ∀ j ∈ anchors, 0 ≤ weight j)
    (hBudget : ∀ j ∈ anchors, value j ≤ budget j) :
    (∑ j ∈ anchors, weight j * value j) ≤
      ∑ j ∈ anchors, weight j * budget j := by
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (hBudget j hj) (hWeight j hj)

/-- Nonnegative weighting cannot enlarge the union of the separately budgeted
anchor exclusion regions: a strict weighted violation already violates an
individual budget.  This extension is certificate compression only. -/
theorem finite_weighted_superlevel_has_anchor {ι : Type*} (anchors : Finset ι)
    (weight value budget : ι → ℝ)
    (hWeight : ∀ j ∈ anchors, 0 ≤ weight j)
    (hShape : (∑ j ∈ anchors, weight j * budget j) <
      ∑ j ∈ anchors, weight j * value j) :
    ∃ j ∈ anchors, budget j < value j := by
  by_contra hExists
  have hBudget : ∀ j ∈ anchors, value j ≤ budget j := by
    intro j hj
    exact le_of_not_gt (fun hlt => hExists ⟨j, hj, hlt⟩)
  have hBound := finite_weighted_kernel_bound anchors weight value budget hWeight hBudget
  exact (not_le_of_gt hShape) hBound

/-- A strict weighted superlevel condition excludes a hypothetical zero,
provided that every anchor's analytic budget is supplied explicitly. -/
theorem finite_weighted_exclusion {ι : Type*} (anchors : Finset ι)
    (weight budget : ι → ℝ) (kernel : ι → ℝ → ℝ → ℝ)
    {IsZero : ℝ → ℝ → Prop} {beta t : ℝ}
    (hWeight : ∀ j ∈ anchors, 0 ≤ weight j)
    (hShape : (∑ j ∈ anchors, weight j * budget j) <
      ∑ j ∈ anchors, weight j * kernel j beta t)
    (hAnalytic : IsZero beta t → ∀ j ∈ anchors, kernel j beta t ≤ budget j) :
    ¬ IsZero beta t := by
  intro hZero
  have hBound := finite_weighted_kernel_bound anchors weight
    (fun j => kernel j beta t) budget hWeight (hAnalytic hZero)
  exact (not_le_of_gt hShape) hBound

/-- The finite weighted extension specialized to reflected pairs.
This does not enlarge the union of the individually certified anchor regions.
All global, reflection, Hadamard and numeric facts remain behind `hAnalytic`. -/
theorem finite_weighted_pair_exclusion {ι : Type*} (anchors : Finset ι)
    (weight budget sigma height : ι → ℝ)
    {IsZero : ℝ → ℝ → Prop} {beta t : ℝ}
    (hWeight : ∀ j ∈ anchors, 0 ≤ weight j)
    (hShape : (∑ j ∈ anchors, weight j * budget j) <
      ∑ j ∈ anchors, weight j * anchoredPairKernel (sigma j) (height j) beta t)
    (hAnalytic : IsZero beta t → ∀ j ∈ anchors,
      anchoredPairKernel (sigma j) (height j) beta t ≤ budget j) :
    ¬ IsZero beta t := by
  exact finite_weighted_exclusion anchors weight budget
    (fun j beta t => anchoredPairKernel (sigma j) (height j) beta t)
    hWeight hShape hAnalytic

end ZeroFree.LocalShape
