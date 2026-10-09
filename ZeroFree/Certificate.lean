import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

/- Exact algebra of the reference continuous certificate. No analytic estimates are assumed here. -/
noncomputable section

namespace ZeroFree.Certificate

def lower : ℝ := (16683858898627 : ℝ) / 100000000000000
def upper : ℝ := (4170964724657 : ℝ) / 25000000000000
def rootPoly (e : ℝ) : ℝ := 657 * e ^ 3 - 954 * e ^ 2 + 21 * e + 20
def b (e : ℝ) : ℝ := (-5181 + 156335 * e - 387630 * e ^ 2) / 81941
def c (e : ℝ) : ℝ := ((657 : ℝ) / 670) * e ^ 2 + ((141 : ℝ) / 670) * e + ((128 : ℝ) / 335)
def h (e : ℝ) : ℝ := (1 + 3 * e + b e) / 2
def K (e : ℝ) : ℝ := -1/4 + 5 * e / 4 + b e / 6
def W (e y : ℝ) : ℝ := 1/2 + 3 * e / 2 - e * y
def D (e y : ℝ) : ℝ := (5/2 - c e) + (1 + 2 * c e) * y
def P (e y : ℝ) : ℝ := (1 - c e / 2) + 2 * y + 2 * c e * y ^ 2
def A (e y : ℝ) : ℝ := -2 * (P e y - D e y) * (W e y - h e) + h e * P e y
def B (e y : ℝ) : ℝ := 2 * K e * (P e y - D e y) + (5/3) * D e y * (W e y - h e) + (5/6) * h e * P e y
def C (e y : ℝ) : ℝ := -(5/3) * D e y * K e
def Q (e y : ℝ) : ℝ := 4 * A e y * C e y - (B e y) ^ 2

def a0 (e : ℝ) : ℝ := ((22024392 : ℝ) / 27450235) * e ^ 2 + ((-25392303 : ℝ) / 54900470) * e + ((29023387 : ℝ) / 54900470)
def a1 (e : ℝ) : ℝ := ((649584879 : ℝ) / 54900470) * e ^ 2 + ((114089327 : ℝ) / 54900470) * e + ((14691591 : ℝ) / 27450235)
def a2 (e : ℝ) : ℝ := ((-827407842 : ℝ) / 27450235) * e ^ 2 + ((137041024 : ℝ) / 27450235) * e + ((24009804 : ℝ) / 27450235)
def a3 (e : ℝ) : ℝ := ((438 : ℝ) / 67) * e ^ 2 + ((94 : ℝ) / 67) * e + ((-8 : ℝ) / 67)
def b0 (e : ℝ) : ℝ := ((16689698 : ℝ) / 5490047) * e ^ 2 + ((-62414657 : ℝ) / 10980094) * e + ((13527353 : ℝ) / 10980094)
def b1 (e : ℝ) : ℝ := ((185468837 : ℝ) / 10980094) * e ^ 2 + ((-10573322 : ℝ) / 5490047) * e + ((7147234 : ℝ) / 16470141)
def b2 (e : ℝ) : ℝ := ((-44457949 : ℝ) / 5490047) * e ^ 2 + ((7279928 : ℝ) / 5490047) * e + ((237738 : ℝ) / 5490047)
def c0 (e : ℝ) : ℝ := ((233942005 : ℝ) / 65880564) * e ^ 2 + ((-245961465 : ℝ) / 43920376) * e + ((358532815 : ℝ) / 395283384)
def c1 (e : ℝ) : ℝ := ((25770095 : ℝ) / 32940282) * e ^ 2 + ((-295111555 : ℝ) / 65880564) * e + ((156399035 : ℝ) / 197641692)
def q0 (_e : ℝ) : ℝ := (0 : ℝ)
def q1 (e : ℝ) : ℝ := ((1333142883885015 : ℝ) / 60281232124418) * e ^ 2 + ((-5100662787553495 : ℝ) / 542531089119762) * e + ((809726670583070 : ℝ) / 813796633679643)
def q2 (e : ℝ) : ℝ := ((-274436399303309489 : ℝ) / 361687392746508) * e ^ 2 + ((14348670159947407 : ℝ) / 542531089119762) * e + ((13758472255378483 : ℝ) / 813796633679643)
def q3 (e : ℝ) : ℝ := ((81111899732709199 : ℝ) / 90421848186627) * e ^ 2 + ((-2286860800540558 : ℝ) / 90421848186627) * e + ((-16668133986645812 : ℝ) / 813796633679643)
def q4 (e : ℝ) : ℝ := ((-20986353986740589 : ℝ) / 90421848186627) * e ^ 2 + ((3485855804140514 : ℝ) / 271265544559881) * e + ((3574934877543932 : ℝ) / 813796633679643)

theorem interval_squares {e : ℝ} (hlo : lower < e) (hhi : e < upper) :
    lower ^ 2 ≤ e ^ 2 ∧ e ^ 2 ≤ upper ^ 2 := by
  have hl : 0 < lower := by norm_num [lower]
  constructor <;> nlinarith [sq_nonneg (e - lower), sq_nonneg (upper - e)]

theorem a0_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < a0 e := by
  have hs := interval_squares hlo hhi
  dsimp [a0, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem a1_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < a1 e := by
  have hs := interval_squares hlo hhi
  dsimp [a1, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem a2_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < a2 e := by
  have hs := interval_squares hlo hhi
  dsimp [a2, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem a3_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < a3 e := by
  have hs := interval_squares hlo hhi
  dsimp [a3, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem c0_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < c0 e := by
  have hs := interval_squares hlo hhi
  dsimp [c0, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem c1_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < c1 e := by
  have hs := interval_squares hlo hhi
  dsimp [c1, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem q1_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < q1 e := by
  have hs := interval_squares hlo hhi
  dsimp [q1, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem q2_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < q2 e := by
  have hs := interval_squares hlo hhi
  dsimp [q2, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem q3_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < q3 e := by
  have hs := interval_squares hlo hhi
  dsimp [q3, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem q4_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < q4 e := by
  have hs := interval_squares hlo hhi
  dsimp [q4, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem c_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : c e > (0 : ℝ) := by
  have hs := interval_squares hlo hhi
  dsimp [c, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem c_lt_half {e : ℝ} (hlo : lower < e) (hhi : e < upper) : c e < ((1 : ℝ) / 2) := by
  have hs := interval_squares hlo hhi
  dsimp [c, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem a_reduction {e : ℝ} (hp : rootPoly e = 0) (y : ℝ) :
    A e y = a0 e + a1 e * y + a2 e * y ^ 2 + a3 e * y ^ 3 := by
  dsimp [A, P, D, W, h, b, c, K, a0, a1, a2, a3]
  dsimp [rootPoly] at hp
  linear_combination (((-116289 : ℝ) / 5490047) * e * y ^ 2 + ((77526 : ℝ) / 5490047) * e * y + ((-38763 : ℝ) / 21960188) * e + ((2 : ℝ) / 335) * y ^ 3 + ((-775543 : ℝ) / 27450235) * y ^ 2 + ((1061371 : ℝ) / 54900470) * y + ((-367769 : ℝ) / 109800940)) * hp

theorem b_reduction {e : ℝ} (hp : rootPoly e = 0) (y : ℝ) :
    B e y = b0 e + b1 e * y + b2 e * y ^ 2 := by
  dsimp [B, P, D, W, h, b, c, K, b0, b1, b2]
  dsimp [rootPoly] at hp
  linear_combination (((-116289 : ℝ) / 10980094) * e * y ^ 2 + ((90447 : ℝ) / 5490047) * e * y + ((-245499 : ℝ) / 43920376) * e + ((-235891 : ℝ) / 32940282) * y ^ 2 + ((521719 : ℝ) / 32940282) * y + ((-807547 : ℝ) / 131761128)) * hp

theorem c_reduction {e : ℝ} (hp : rootPoly e = 0) (y : ℝ) :
    C e y = c0 e + c1 e * y := by
  dsimp [C, P, D, W, h, b, c, K, c0, c1]
  dsimp [rootPoly] at hp
  linear_combination (((21535 : ℝ) / 5490047) * e * y + ((-21535 : ℝ) / 10980094) * e + ((-249685 : ℝ) / 197641692) * y + ((249685 : ℝ) / 395283384)) * hp

theorem q_reduction {e : ℝ} (hp : rootPoly e = 0) (y : ℝ) :
    Q e y = q1 e * y + q2 e * y ^ 2 + q3 e * y ^ 3 + q4 e * y ^ 4 := by
  rw [Q, a_reduction hp, b_reduction hp, c_reduction hp]
  dsimp [a0, a1, a2, a3, b0, b1, b2, c0, c1, q0, q1, q2, q3, q4]
  dsimp [rootPoly] at hp
  linear_combination (((-6209653158919 : ℝ) / 90421848186627) * e * y ^ 4 + ((112346832578807 : ℝ) / 271265544559881) * e * y ^ 3 + ((-1035839192001917 : ℝ) / 1085062178239524) * e * y ^ 2 + ((56048315405785 : ℝ) / 542531089119762) * e * y + ((54020 : ℝ) / 16470141) * e + ((-194201637000988 : ℝ) / 813796633679643) * y ^ 4 + ((926903629975093 : ℝ) / 813796633679643) * y ^ 3 + ((-501870550854467 : ℝ) / 813796633679643) * y ^ 2 + ((252423814595915 : ℝ) / 3255186534718572) * y + ((29515 : ℝ) / 1474938)) * hp

theorem c_inverse {e : ℝ} (hp : rootPoly e = 0) : (3 * (5/6 - e/2)) * c e = 1 := by
  dsimp [c]
  dsimp [rootPoly] at hp
  linear_combination (((-3 : ℝ) / 1340)) * hp

theorem a_positive {e : ℝ} (hp : rootPoly e = 0)
    (hlo : lower < e) (hhi : e < upper) {y : ℝ} (hy : 0 ≤ y) : 0 < A e y := by
  rw [a_reduction hp]
  have h0 := a0_pos hlo hhi
  have h1 := mul_nonneg (le_of_lt (a1_pos hlo hhi)) hy
  have h2 := mul_nonneg (le_of_lt (a2_pos hlo hhi)) (sq_nonneg y)
  have h3 := mul_nonneg (le_of_lt (a3_pos hlo hhi)) (pow_nonneg hy 3)
  linarith

theorem q_nonnegative {e : ℝ} (hp : rootPoly e = 0)
    (hlo : lower < e) (hhi : e < upper) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Q e y := by
  rw [q_reduction hp]
  have h1 := q1_pos hlo hhi
  have h2 := q2_pos hlo hhi
  have h3 := q3_pos hlo hhi
  have h4 := q4_pos hlo hhi
  positivity

theorem quadratic_nonnegative {a b c d : ℝ} (ha : 0 < a)
    (hq : 0 ≤ 4*a*c-b^2) : 0 ≤ a*d^2-b*d+c := by
  by_contra! hn
  have hneg := mul_neg_of_pos_of_neg ha hn
  nlinarith only [hneg, hq, sq_nonneg (2*a*d-b)]

theorem continuous_certificate {e : ℝ} (hp : rootPoly e = 0)
    (hlo : lower < e) (hhi : e < upper) {y : ℝ} (hy : 0 ≤ y) (δ : ℝ) :
    0 ≤ A e y * δ^2 - B e y * δ + C e y := by
  exact quadratic_nonnegative (a_positive hp hlo hhi hy) (q_nonnegative hp hlo hhi hy)

def J (e y δ : ℝ) : ℝ := (5/6-δ) * D e y + δ * P e y
def R (e y δ : ℝ) : ℝ := 1-δ+(5/6-δ)*δ*P e y/(2*J e y δ)
def endpoint (e y δ : ℝ) : ℝ := K e + W e y * δ - h e * (1-R e y δ)

theorem j_positive {e : ℝ} (hlo : lower < e) (hhi : e < upper)
    {y δ : ℝ} (hy : 0 ≤ y) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3/4) : 0 < J e y δ := by
  have hc0 := c_pos hlo hhi
  have hc1 := c_lt_half hlo hhi
  have hD : 0 < D e y := by unfold D; nlinarith [mul_nonneg (by linarith : 0 ≤ 1+2*c e) hy]
  have hP : 0 < P e y := by unfold P; nlinarith [mul_nonneg (le_of_lt hc0) (sq_nonneg y)]
  unfold J
  exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hD) (mul_nonneg hd0 (le_of_lt hP))

theorem endpoint_identity {e y δ : ℝ} (hJ : J e y δ ≠ 0) :
    -2 * J e y δ * endpoint e y δ = A e y * δ^2 - B e y * δ + C e y := by
  unfold endpoint R
  field_simp
  unfold A B C K W J
  ring

theorem endpoint_nonpositive {e : ℝ} (hp : rootPoly e = 0)
    (hlo : lower < e) (hhi : e < upper) {y δ : ℝ}
    (hy : 0 ≤ y) (hd0 : 0 ≤ δ) (hd1 : δ ≤ 3/4) : endpoint e y δ ≤ 0 := by
  have hJ := j_positive hlo hhi hy hd0 hd1
  have hid := endpoint_identity (ne_of_gt hJ)
  have hf := continuous_certificate hp hlo hhi hy δ
  by_contra! hn
  nlinarith [mul_pos hJ hn]

end ZeroFree.Certificate
