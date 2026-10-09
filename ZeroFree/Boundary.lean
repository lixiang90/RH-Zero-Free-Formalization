import Mathlib

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace ZeroFree

/-- The cubic specifying the feedback boundary. -/
def cubic (e : ℝ) : ℝ := 657 * e ^ 3 - 954 * e ^ 2 + 21 * e + 20

noncomputable def ellLo : ℝ := (16683858898627 : ℝ) / 100000000000000
noncomputable def ellHi : ℝ := (16683858898628 : ℝ) / 100000000000000

theorem ellLo_lt_ellHi : ellLo < ellHi := by norm_num [ellLo, ellHi]
theorem ellLo_coarse : (1 : ℝ) / 6 < ellLo := by norm_num [ellLo]
theorem ellHi_coarse : ellHi < (167 : ℝ) / 1000 := by norm_num [ellHi]
theorem cubic_ellLo_pos : 0 < cubic ellLo := by norm_num [cubic, ellLo]
theorem cubic_ellHi_neg : cubic ellHi < 0 := by norm_num [cubic, ellHi]

theorem cubic_strictAnti : StrictAntiOn cubic (Set.Ioo ((1 : ℝ) / 6) (167 / 1000)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hxU : x ≤ (1 : ℝ) / 5 := by linarith [hx.2]
  have hyU : y ≤ (1 : ℝ) / 5 := by linarith [hy.2]
  have hxSq : x ^ 2 ≤ (1 : ℝ) / 25 := by
    have := mul_nonneg (show 0 ≤ (1 : ℝ) / 5 - x by linarith)
      (show 0 ≤ (1 : ℝ) / 5 + x by linarith)
    nlinarith only [this]
  have hySq : y ^ 2 ≤ (1 : ℝ) / 25 := by
    have := mul_nonneg (show 0 ≤ (1 : ℝ) / 5 - y by linarith)
      (show 0 ≤ (1 : ℝ) / 5 + y by linarith)
    nlinarith only [this]
  have hprod : x * y ≤ (1 : ℝ) / 25 := by
    nlinarith only [sq_nonneg (x - y), hxSq, hySq]
  have hcoef : 657 * (y ^ 2 + y * x + x ^ 2) - 954 * (y + x) + 21 < 0 := by
    nlinarith only [hxSq, hySq, hprod, hx.1, hy.1]
  have hnegative := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hcoef
  have hfactor : cubic y - cubic x =
      (y - x) * (657 * (y ^ 2 + y * x + x ^ 2) - 954 * (y + x) + 21) := by
    dsimp [cubic]
    ring
  linarith only [hnegative, hfactor]

theorem cubic_roots_eq {x y : ℝ}
    (hx : (1 : ℝ) / 6 < x ∧ x < 167 / 1000)
    (hy : (1 : ℝ) / 6 < y ∧ y < 167 / 1000)
    (hpx : cubic x = 0) (hpy : cubic y = 0) : x = y := by
  rcases lt_trichotomy x y with hxy | heq | hyx
  · have h := cubic_strictAnti hx hy hxy
    linarith only [h, hpx, hpy]
  · exact heq
  · have h := cubic_strictAnti hy hx hyx
    linarith only [h, hpx, hpy]

theorem exists_root_isolated : ∃ e : ℝ, cubic e = 0 ∧ ellLo < e ∧ e < ellHi := by
  have hcont : Continuous cubic := by unfold cubic; fun_prop
  obtain ⟨e, he, hpe⟩ := intermediate_value_Icc' ellLo_lt_ellHi.le
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Icc (cubic ellHi) (cubic ellLo) from
      ⟨cubic_ellHi_neg.le, cubic_ellLo_pos.le⟩)
  refine ⟨e, hpe, ?_, ?_⟩
  · have hne : ellLo ≠ e := by
      intro h
      rw [← h] at hpe
      linarith only [cubic_ellLo_pos, hpe]
    exact lt_of_le_of_ne he.1 hne
  · have hne : e ≠ ellHi := by
      intro h
      rw [h] at hpe
      linarith only [cubic_ellHi_neg, hpe]
    exact lt_of_le_of_ne he.2 hne

theorem existsUnique_root_isolated :
    ∃! e : ℝ, cubic e = 0 ∧ ellLo < e ∧ e < ellHi := by
  obtain ⟨e, hp, hlo, hhi⟩ := exists_root_isolated
  refine ⟨e, ⟨hp, hlo, hhi⟩, ?_⟩
  intro y hy
  apply cubic_roots_eq
  · exact ⟨lt_trans ellLo_coarse hy.2.1, lt_trans hy.2.2 ellHi_coarse⟩
  · exact ⟨lt_trans ellLo_coarse hlo, lt_trans hhi ellHi_coarse⟩
  · exact hy.1
  · exact hp

noncomputable def ellStar : ℝ := Classical.choose existsUnique_root_isolated

theorem ellStar_spec : cubic ellStar = 0 ∧ ellLo < ellStar ∧ ellStar < ellHi :=
  (Classical.choose_spec existsUnique_root_isolated).1

theorem ellStar_coarse : (1 : ℝ) / 6 < ellStar ∧ ellStar < 167 / 1000 :=
  ⟨lt_trans ellLo_coarse ellStar_spec.2.1, lt_trans ellStar_spec.2.2 ellHi_coarse⟩

theorem ellStar_unique {e : ℝ} (hlo : (1 : ℝ) / 6 < e) (hhi : e < 167 / 1000)
    (hp : cubic e = 0) : e = ellStar :=
  cubic_roots_eq ⟨hlo, hhi⟩ ellStar_coarse hp ellStar_spec.1

noncomputable def sigmaStar : ℝ := 11 / 12 - ellStar / 4
noncomputable def kappaStar : ℝ := 5 / 6 - ellStar / 2
noncomputable def bStar : ℝ := (-5181 + 156335 * ellStar - 387630 * ellStar ^ 2) / 81941

theorem sigmaStar_cubic :
    7884 * sigmaStar ^ 3 - 18819 * sigmaStar ^ 2 + 14643 * sigmaStar - 3686 = 0 := by
  have hp := ellStar_spec.1
  dsimp [cubic] at hp
  dsimp [sigmaStar]
  nlinarith only [hp]

theorem sigmaStar_isolated :
    (11 : ℝ) / 12 - ellHi / 4 < sigmaStar ∧
      sigmaStar < (11 : ℝ) / 12 - ellLo / 4 := by
  dsimp [sigmaStar]
  constructor <;> linarith only [ellStar_spec.2.1, ellStar_spec.2.2]

theorem sigmaStar_lt_69999_80000 : sigmaStar < (69999 : ℝ) / 80000 := by
  have h := sigmaStar_isolated.2
  norm_num [ellLo] at h ⊢
  linarith only [h]

theorem sigmaStar_lt_seven_eighths : sigmaStar < (7 : ℝ) / 8 := by
  have h := sigmaStar_lt_69999_80000
  linarith only [h]

theorem kappaStar_identity : kappaStar = 2 * sigmaStar - 1 := by
  dsimp [kappaStar, sigmaStar]
  ring

theorem sigmaStar_decimal_isolated :
    (874957019420096 : ℝ) / 1000000000000000 < sigmaStar ∧
      sigmaStar < (874957019420100 : ℝ) / 1000000000000000 := by
  have h := sigmaStar_isolated
  norm_num [ellLo, ellHi] at h
  constructor <;> linarith only [h.1, h.2]

theorem kappaStar_range : (37 : ℝ) / 50 < kappaStar ∧ kappaStar < (3 : ℝ) / 4 := by
  have h := ellStar_coarse
  dsimp [kappaStar]
  constructor <;> linarith only [h.1, h.2]

/-- The previous optimized free-b boundary, included only for exact comparison. -/
noncomputable def sigmaFreeB : ℝ := (1507 - 2 * Real.sqrt 921) / 1653

theorem sqrt921_isolated :
    (303479818 : ℝ) / 10000000 < Real.sqrt 921 ∧
      Real.sqrt 921 < (303479819 : ℝ) / 10000000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 921 by norm_num)
  have hn := Real.sqrt_nonneg (921 : ℝ)
  constructor <;> nlinarith only [hs, hn]

theorem sigmaStar_lt_sigmaFreeB : sigmaStar < sigmaFreeB := by
  have h := sigmaStar_isolated.2
  have hs := sqrt921_isolated.2
  dsimp [ellLo, sigmaFreeB] at *
  linarith only [h, hs]

theorem freeB_improvement_isolated :
    (50 : ℝ) / 1000000000 < sigmaFreeB - sigmaStar ∧
      sigmaFreeB - sigmaStar < (51 : ℝ) / 1000000000 := by
  have h := sigmaStar_isolated
  have hs := sqrt921_isolated
  dsimp [ellLo, ellHi, sigmaFreeB] at *
  constructor <;> linarith only [h.1, h.2, hs.1, hs.2]

theorem bStar_range : (123 : ℝ) / 1000 < bStar ∧ bStar < (124 : ℝ) / 1000 := by
  have hlo := ellStar_spec.2.1
  have hhi := ellStar_spec.2.2
  have hsqlo : ellLo ^ 2 ≤ ellStar ^ 2 := by
    have hmul := mul_nonneg (show 0 ≤ ellStar - ellLo by linarith)
      (show 0 ≤ ellStar + ellLo by
        have h := ellLo_coarse
        linarith)
    nlinarith only [hmul]
  have hsqhi : ellStar ^ 2 ≤ ellHi ^ 2 := by
    have hmul := mul_nonneg (show 0 ≤ ellHi - ellStar by linarith)
      (show 0 ≤ ellHi + ellStar by
        have h := ellStar_coarse.1
        linarith)
    nlinarith only [hmul]
  dsimp [bStar, ellLo, ellHi] at *
  constructor <;> nlinarith only [hlo, hhi, hsqlo, hsqhi]


end ZeroFree
