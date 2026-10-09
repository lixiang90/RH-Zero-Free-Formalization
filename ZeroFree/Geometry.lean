import ZeroFree.Certificate

noncomputable section
namespace ZeroFree.Geometry
open ZeroFree.Certificate

/- Positive margins for every physical range displayed in the cubic paper. -/
def minimum_M_prime (e : ℝ) : ℝ := (-3 : ℝ) * e + (1 : ℝ)
theorem minimum_M_prime_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < minimum_M_prime e := by
  have hs := interval_squares hlo hhi
  dsimp [minimum_M_prime, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def minimum_lx_prime (e : ℝ) : ℝ := ((193815 : ℝ) / 81941) * e ^ 2 + ((-201079 : ℝ) / 81941) * e + ((43561 : ℝ) / 81941)
theorem minimum_lx_prime_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < minimum_lx_prime e := by
  have hs := interval_squares hlo hhi
  dsimp [minimum_lx_prime, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def minimum_ly_prime (e : ℝ) : ℝ := ((-193815 : ℝ) / 81941) * e ^ 2 + ((-44744 : ℝ) / 81941) * e + ((38380 : ℝ) / 81941)
theorem minimum_ly_prime_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < minimum_ly_prime e := by
  have hs := interval_squares hlo hhi
  dsimp [minimum_ly_prime, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def principal_w (e : ℝ) : ℝ := ((-38763 : ℝ) / 327764) * e ^ 2 + ((37197 : ℝ) / 1638820) * e + ((1919 : ℝ) / 81941)
theorem principal_w_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < principal_w e := by
  have hs := interval_squares hlo hhi
  dsimp [principal_w, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def principal_z (e : ℝ) : ℝ := ((-12921 : ℝ) / 3277640) * e ^ 2 + ((201079 : ℝ) / 49164600) * e + ((1919 : ℝ) / 2458230)
theorem principal_z_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < principal_z e := by
  have hs := interval_squares hlo hhi
  dsimp [principal_z, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def b_positive (e : ℝ) : ℝ := ((-387630 : ℝ) / 81941) * e ^ 2 + ((156335 : ℝ) / 81941) * e + ((-5181 : ℝ) / 81941)
theorem b_positive_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < b_positive e := by
  have hs := interval_squares hlo hhi
  dsimp [b_positive, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def gram_margin (e : ℝ) : ℝ := ((516840 : ℝ) / 81941) * e ^ 2 + ((-1988149 : ℝ) / 491646) * e + ((2066161 : ℝ) / 4097050)
theorem gram_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < gram_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [gram_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def supply_margin (e : ℝ) : ℝ := ((193815 : ℝ) / 81941) * e ^ 2 + ((208626 : ℝ) / 81941) * e + ((-15367308821 : ℝ) / 31465344000)
theorem supply_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < supply_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [supply_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def outer_ceiling (e : ℝ) : ℝ := ((193815 : ℝ) / 81941) * e ^ 2 + ((-201079 : ℝ) / 81941) * e + ((16727342059 : ℝ) / 31465344000)
theorem outer_ceiling_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < outer_ceiling e := by
  have hs := interval_squares hlo hhi
  dsimp [outer_ceiling, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def floor_margin (e : ℝ) : ℝ := ((64605 : ℝ) / 81941) * e ^ 2 + ((-19641047 : ℝ) / 12291150) * e + ((4023927 : ℝ) / 16388200)
theorem floor_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < floor_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [floor_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def middle_margin (e : ℝ) : ℝ := ((-5439741 : ℝ) / 3277640) * e ^ 2 + ((-3764683 : ℝ) / 24582300) * e + ((7487837 : ℝ) / 98329200)
theorem middle_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < middle_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [middle_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def small_margin (e : ℝ) : ℝ := ((-633129 : ℝ) / 819410) * e ^ 2 + ((-2438279 : ℝ) / 12291150) * e + ((74245951 : ℝ) / 1229115000)
theorem small_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < small_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [small_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def good_euler_margin (e : ℝ) : ℝ := ((-1 : ℝ) / 4) * e + ((7 : ℝ) / 150)
theorem good_euler_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < good_euler_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [good_euler_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def ramified_euler_margin (e : ℝ) : ℝ := ((-1 : ℝ) / 4) * e + ((7 : ℝ) / 150)
theorem ramified_euler_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < ramified_euler_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [ramified_euler_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def small_box_margin (e : ℝ) : ℝ := ((-1 : ℝ) / 4) * e + ((1 : ℝ) / 12)
theorem small_box_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < small_box_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [small_box_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

def zeta_ceiling_margin (e : ℝ) : ℝ := ((-1 : ℝ) / 128) * e + ((167 : ℝ) / 128000)
theorem zeta_ceiling_margin_pos {e : ℝ} (hlo : lower < e) (hhi : e < upper) : 0 < zeta_ceiling_margin e := by
  have hs := interval_squares hlo hhi
  dsimp [zeta_ceiling_margin, lower, upper] at *
  nlinarith only [hlo, hhi, hs.1, hs.2]

theorem plain_terminal_budget {κ M z : ℝ} (_hk : 37/50 ≤ κ)
    (_hz : 0 ≤ z) (hbudget : 6*κ*z ≤ M) : κ*z ≤ M/6 := by linarith

theorem plain_comparison_slack : (1/20 : ℝ) - 25/516 = 1/645 := by norm_num

theorem same_band_slots {κ M z A : ℝ} (hk : 37/50 ≤ κ)
    (hz : 0 ≤ z) (hM : 0 < M) (hA : 5*M/6 < A)
    (hbudget : A+(6*κ-1)*z ≤ M) : z < M/20 := by
  have hmul := mul_nonneg (by linarith : 0 ≤ κ-37/50) hz
  nlinarith

theorem feedback_rational_bound : (625/36963 : ℝ) < 1/50 := by norm_num

theorem central_saving_identity (Δ : ℝ) : (24/25-1/16)*Δ = (359/400)*Δ := by ring

theorem minimum_M_prime_identity (e : ℝ) : minimum_M_prime e = 1-3*e := by
  dsimp [minimum_M_prime, h, b]
  ring

theorem minimum_lx_prime_identity (e : ℝ) : minimum_lx_prime e = (1-e-b e)/2-e := by
  dsimp [minimum_lx_prime, h, b]
  ring

theorem minimum_ly_prime_identity (e : ℝ) : minimum_ly_prime e = (1-e+b e)/2-e := by
  dsimp [minimum_ly_prime, h, b]
  ring

theorem principal_w_identity (e : ℝ) : principal_w e = ((1-e+b e)/2)/20 := by
  dsimp [principal_w, h, b]
  ring

theorem principal_z_identity (e : ℝ) : principal_z e = h e/600 := by
  dsimp [principal_z, h, b]
  ring

theorem b_positive_identity (e : ℝ) : b_positive e = b e := by
  dsimp [b_positive, h, b]
  ring

theorem gram_margin_identity (e : ℝ) : gram_margin e = (1-e+b e)/2-e-11*b e/6-2/25 := by
  dsimp [gram_margin, h, b]
  ring

theorem supply_margin_identity (e : ℝ) : supply_margin e = 5*e-h e-1/384000-1/50 := by
  dsimp [supply_margin, h, b]
  ring

theorem outer_ceiling_identity (e : ℝ) : outer_ceiling e = 1-h e-1/384000 := by
  dsimp [outer_ceiling, h, b]
  ring

theorem floor_margin_identity (e : ℝ) : floor_margin e = -(-6/25+32*e/25+b e/6)-1/200 := by
  dsimp [floor_margin, h, b]
  ring

theorem middle_margin_identity (e : ℝ) : middle_margin e = -(-71/600+329*e/400-421*b e/1200)-1/50 := by
  dsimp [middle_margin, h, b]
  ring

theorem small_margin_identity (e : ℝ) : small_margin e = -(13*h e/75-((1-e+b e)/2)/2+63/5000)-2/25 := by
  dsimp [small_margin, h, b]
  ring

theorem good_euler_margin_identity (e : ℝ) : good_euler_margin e = (11/12-e/4)-3/50-81/100 := by
  dsimp [good_euler_margin, h, b]
  ring

theorem ramified_euler_margin_identity (e : ℝ) : ramified_euler_margin e = (11/12-e/4)-1/20-82/100 := by
  dsimp [ramified_euler_margin, h, b]
  ring

theorem small_box_margin_identity (e : ℝ) : small_box_margin e = (11/12-e/4)+1/2-4/3 := by
  dsimp [small_box_margin, h, b]
  ring

theorem zeta_ceiling_margin_identity (e : ℝ) : zeta_ceiling_margin e = 1/384000-(e-1/6)/128 := by
  dsimp [zeta_ceiling_margin, h, b]
  ring
end ZeroFree.Geometry
