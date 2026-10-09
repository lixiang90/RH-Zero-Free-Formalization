/-
Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Adapted from the actual LowSourceScales/LowGramScale of OpenAI/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0.
The actual compensated Gram factor is bounded at variable total ell and b.
This supplies its physical scale gate, not the full reflected-energy estimate.
-/
import OAI.NumberTheory.DirichletL.Detector.LowSourceScales

namespace OAI
noncomputable section
namespace SevenEighths.ProbePhysical

def totalSourceLx (ell b : ℝ) : ℝ := (1-ell-b)/2
def totalSourceLy (ell b : ℝ) : ℝ := (1-ell+b)/2
def totalSourceLowExponent (ell b : ℝ) : ℝ := (1-ell)/4-b/6

lemma source_scale_ratio_total (Z ell b : ℝ) (hZ : 0<Z) :
    Z^(totalSourceLy ell b)/Z^(totalSourceLx ell b)=Z^b := by
  rw [←Real.rpow_sub hZ]
  congr 1
  unfold totalSourceLx totalSourceLy
  ring

lemma source_scale_square_total (Z ell b : ℝ) (hZ : 0<Z) :
    Z^((1-ell-3*b)/2)*Z^(totalSourceLy ell b)=(Z^(totalSourceLx ell b))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  unfold totalSourceLx totalSourceLy
  push_cast
  ring

lemma source_compensated_scale_admissible_total (q Z L ell b : ℝ)
    (hq : 1≤q) (hZ : 1≤Z) (hL : 1≤L) (hb : 0≤b)
    (hql : q≤Z^b) (hLl : L≤Z^((1-ell-3*b)/2)) :
    1≤Z^(totalSourceLy ell b)/L ∧
    q*Z^(totalSourceLx ell b)≤Z^(totalSourceLy ell b) ∧
    L*Z^(totalSourceLy ell b)≤q^2*(Z^(totalSourceLx ell b))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ
      (show (1-ell-3*b)/2≤totalSourceLy ell b by unfold totalSourceLy;linarith))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (totalSourceLx ell b))).mp
    rwa [source_scale_ratio_total Z ell b hz]
  · calc
      _≤Z^((1-ell-3*b)/2)*Z^(totalSourceLy ell b) :=
        mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(totalSourceLx ell b))^2 := source_scale_square_total Z ell b hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_gram_power_total (Z ell b δ : ℝ) (hZ : 0<Z) :
    Z^(totalSourceLx ell b)*(Z^b)^(1/6:ℝ)*(Z^(totalSourceLy ell b))^δ =
      Z^(2*totalSourceLowExponent ell b+totalSourceLy ell b*δ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  unfold totalSourceLx totalSourceLowExponent
  ring

lemma source_gram_sqrt_power_total (Z ell b δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^(2*totalSourceLowExponent ell b+totalSourceLy ell b*δ)) =
      Z^(totalSourceLowExponent ell b+totalSourceLy ell b*δ/2) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

lemma source_compensated_gram_scale_total (q Z L ell b δ : ℝ)
    (hq : 1≤q) (hZ : 1≤Z) (hL : 1≤L) (hb : 0≤b)
    (hql : q≤Z^b) (hLl : L≤Z^((1-ell-3*b)/2)) (hδ : 0≤δ) :
    (q*(Z^(totalSourceLx ell b)/L)*(Z^(totalSourceLy ell b)/L)/(Z^(totalSourceLy ell b)/L))*
      (1+((Z^(totalSourceLy ell b)/L)^2/
        (q*(Z^(totalSourceLx ell b)/L)*(Z^(totalSourceLy ell b)/L)))^(1/6:ℝ)+
        ((Z^(totalSourceLy ell b)/L)^2/
          (q*(Z^(totalSourceLx ell b)/L)*(Z^(totalSourceLy ell b)/L)))^2/
            (Z^(totalSourceLy ell b)/L))*(Z^(totalSourceLy ell b)/L)^δ ≤
      (3*q/L)*Z^(2*totalSourceLowExponent ell b+totalSourceLy ell b*δ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible_total q Z L ell b hq hZ hL hb hql hLl
  have hg := compensated_gram_scale_bound q (Z^(totalSourceLx ell b))
    (Z^(totalSourceLy ell b)) L δ hq0 (by positivity) (by positivity) hL hδ hqp ht
  apply hg.trans
  have hratio : Z^(totalSourceLy ell b)/(q*Z^(totalSourceLx ell b))≤Z^b := by
    rw [←source_scale_ratio_total Z ell b hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow
    (by positivity : 0≤Z^(totalSourceLy ell b)/(q*Z^(totalSourceLx ell b))) hratio
    (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(totalSourceLx ell b)/L)*(Z^b)^(1/6:ℝ)*(Z^(totalSourceLy ell b))^δ := by gcongr
    _=(3*q/L)*(Z^(totalSourceLx ell b)*(Z^b)^(1/6:ℝ)*(Z^(totalSourceLy ell b))^δ) := by ring
    _=_ := by rw [source_gram_power_total Z ell b δ hz]

lemma lowGramFactor_source_bound_total (C : CalibrationData) (Z L ell b δ : ℝ)
    (hZ : 1≤Z) (hL : 1≤L) (hb : 0≤b)
    (hql : elementNorm C.generator≤Z^b) (hLl : L≤Z^((1-ell-3*b)/2)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(totalSourceLx ell b)/L) (Z^(totalSourceLy ell b)/L) δ ≤
      Real.sqrt (3*elementNorm C.generator/L)*
        Z^(totalSourceLowExponent ell b+totalSourceLy ell b*δ/2) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale_total _ Z L ell b δ
    (calibration_elementNorm_ge_one C) hZ hL hb hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),
    source_gram_sqrt_power_total Z ell b δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma eventually_compensated_source_scales_total (C : CalibrationData) (B ell b : ℝ)
    (hb : 0<b) (hgeom : 3*ell+3*b<1) :
    ∀ᶠZ : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^b ∧
      ∀L : ℝ,1≤L→L≤B*Z^ell→
        1≤Z^(totalSourceLy ell b)/L ∧
        1≤(Z^(totalSourceLy ell b)/L)^2/
          lowPhysicalScale C (Z^(totalSourceLx ell b)/L) (Z^(totalSourceLy ell b)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(totalSourceLx ell b)/L) (Z^(totalSourceLy ell b)/L) δ ≤
          Real.sqrt (3*elementNorm C.generator/L)*
            Z^(totalSourceLowExponent ell b+totalSourceLy ell b*δ/2) := by
  have hq := (tendsto_rpow_atTop hb).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hgap : 0<(1-3*ell-3*b)/2 := by linarith
  have hB := (tendsto_rpow_atTop hgap).eventually (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hB] with Z hZ hq hB
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^((1-ell-3*b)/2) := calc
    L≤B*Z^ell := hLB
    _≤Z^((1-3*ell-3*b)/2)*Z^ell := mul_le_mul_of_nonneg_right hB (by positivity)
    _=Z^((1-ell-3*b)/2) := by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible_total _ Z L ell b
    (calibration_elementNorm_ge_one C) hZ hL hb.le hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound_total C Z L ell b δ hZ hL hb.le hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr
    (by simpa using hp)

lemma lowPhysicalScale_source_total (C : CalibrationData) (Z L ell b : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(totalSourceLx ell b)/L) (Z^(totalSourceLy ell b)/L) =
      elementNorm C.generator*Z^(1-ell)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(totalSourceLx ell b)*Z^(totalSourceLy ell b)=Z^(1-ell) := by
    rw [←Real.rpow_add hZ]
    congr 1
    unfold totalSourceLx totalSourceLy
    ring
  rw [←he]
  ring

end SevenEighths.ProbePhysical
end
end OAI
