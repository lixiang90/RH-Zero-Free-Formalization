/-
Adapted from OpenAI/math ParametersSlotLengths, Apache-2.0.
Upstream revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream raw SHA-256: e3aeda691b185f261bbac3f2afefb0ebf2d5a6a33bac8d714b323a4397bb7232.
Generalized by Li Xiang / lixiang90: prescribe an arbitrary positive total
slot exponent. Mesh and physical range are fixed before the finite slot
count is selected. The sixfold Mellin pole is not altered.
-/
import OAI.NumberTheory.DirichletL.ParametersSlotLengths

namespace OAI
noncomputable section
open scoped BigOperators
namespace SevenEighths.Parameters

theorem exists_distinct_slot_lengths_total (total mesh : ℝ)
    (htotal : 0<total) (hmesh : 0<mesh) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,Function.Injective ell ∧
      (∀j,0<ell j ∧ ell j<mesh) ∧ (∑j,ell j)=total := by
  have hscale : 0<6*total := by positivity
  obtain ⟨N,hN,old,hinj,hbounds,hsum⟩ :=
    exists_distinct_slot_lengths (mesh/(6*total)) (by positivity)
  let ell : Fin N→ℝ := fun j=>6*total*old j
  refine ⟨N,hN,ell,?_,?_,?_⟩
  · intro j k heq
    apply hinj
    exact mul_left_cancel₀ hscale.ne' heq
  · intro j
    constructor
    · exact mul_pos hscale (hbounds j).1
    · have h := (lt_div_iff₀ hscale).mp (hbounds j).2
      simpa only [ell,mul_comm] using h
  · dsimp only [ell]
    rw [←Finset.mul_sum,hsum]
    ring

theorem exists_physical_slot_lengths_total (total dmin dmax mesh R : ℝ)
    (htotal : 0<total) (hdmin : 0<dmin) (hd : dmin≤dmax)
    (hm : 0<mesh) (hR : 0<R) :
    ∃N : ℕ,0<N ∧ ∃ell : Fin N→ℝ,∃rmin : ℝ,0<rmin ∧
      Function.Injective ell ∧ (∑j,ell j)=total ∧
      (∀j,0<ell j ∧ dmax*rmin≤ell j ∧ ell j≤dmin*mesh ∧ ell j≤dmin*R) ∧
      (∀d : ℝ,dmin≤d → d≤dmax → ∀j,rmin≤ell j/d ∧ ell j/d≤mesh ∧ ell j/d≤R) := by
  obtain ⟨N,hN,ell,hi,he,hS⟩ :=
    exists_distinct_slot_lengths_total total (dmin*min mesh R) htotal
      (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,hj,hjmin⟩ := Finset.exists_min_image Finset.univ ell hne
  have hmax : 0<dmax := hdmin.trans_le hd
  let rmin := ell j/(2*dmax)
  have hr : 0<rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin≤ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin=ell j/2 := by dsimp [rmin];field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : ell k≤dmin*mesh ∧ ell k≤dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N,hN,ell,rmin,hr,hi,hS,
    fun k=>⟨(he k).1,hlo k,(hup k).1,(hup k).2⟩,?_⟩
  intro d hd' hd'' k
  have hd0 : 0<d := hdmin.trans_le hd'
  refine ⟨(le_div_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_,(div_le_iff₀ hd0).mpr ?_⟩
  · exact (by nlinarith : rmin*d≤dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

end SevenEighths.Parameters
end
end OAI
