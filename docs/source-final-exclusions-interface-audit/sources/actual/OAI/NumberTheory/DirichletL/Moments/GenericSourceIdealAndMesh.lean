/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual fixed-ideal gates and arbitrary-total slots satisfying both the physical
and absolute energy mesh bounds, with the exact batch-to-fiber width identity. -/
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource
import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
import OAI.NumberTheory.DirichletL.Hecke.DetectorBatch
import OAI.NumberTheory.DirichletL.ParametersSlotLengthsLowKappa

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.GenericSourceIdealAndMesh
open HeckeFamily CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open HeckeDetectorBatch HeckeDetectorDyadicProfiles HeckeDetectorWitnessRows
local notation "O" => HeckeFamily.O

theorem source_fixed_ideal_gates (M : Ideal O) [NeZero M]
    (S : Finset (Ideal O)) (hS : ∀P ∈ S, Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (hM : M = ∏P ∈ S, P) :
    let Q0 := M ⊓ Ideal.span {(72 : O)}
    Q0 ≤ M ∧ Q0 ≠ 0 ∧ Q0 ≠ ⊤ ∧
      ∀η : Character, internalQ Q0 η ≠ 0 ∧ internalQ Q0 η ≠ ⊤ ∧
        internalQ Q0 η ≤ Ideal.span {(72 : O)} ∧ internalQ Q0 η ≤ η.modulus := by
  dsimp only
  have hQ0 : M ⊓ Ideal.span {(72 : O)} ≠ 0 :=
    Ideal.inf_ne_bot_of_ne_bot (NeZero.ne M)
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72 : O) ≠ 0))
  have hmem : Ideal.span {goodLambda} ∈ S := by
    apply hbad
    change Ideal.span {goodLambda} ∈
      ({Ideal.span {goodLambda}, Ideal.span {(2 : O)}} : Finset (Ideal O))
    simp
  have hle : M ≤ Ideal.span {goodLambda} := by
    rw [hM]
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O => P) hmem
  have hprime := Ideal.isPrime_of_prime (hS _ hmem)
  have hQt : M ⊓ Ideal.span {(72 : O)} ≠ ⊤ := by
    intro h
    exact hprime.ne_top (top_le_iff.mp
      (h ▸ (inf_le_left.trans hle : M ⊓ Ideal.span {(72 : O)} ≤ Ideal.span {goodLambda})))
  refine ⟨inf_le_left, hQ0, hQt, ?_⟩
  intro η
  exact ⟨internalQ_ne_zero _ hQ0 η, internalQ_ne_top _ hQt η,
    inf_le_left.trans inf_le_right, inf_le_right⟩

theorem exists_source_slots_for_both_meshes
    (total dmin dmax batchMesh physicalRange energyMesh : ℝ)
    (htotal : 0 < total) (hdmin : 0 < dmin) (hd : dmin ≤ dmax)
    (hbatchMesh : 0 < batchMesh) (hphysicalRange : 0 < physicalRange)
    (henergyMesh : 0 < energyMesh) :
    ∃N : ℕ, 0 < N ∧ ∃ell : Fin N → ℝ, ∃rmin : ℝ, 0 < rmin ∧
      Function.Injective ell ∧ (∑j, ell j) = total ∧
      (∀j, 0 < ell j ∧ dmax * rmin ≤ ell j ∧ ell j ≤ dmin * batchMesh ∧
        ell j ≤ dmin * physicalRange ∧ ell j ≤ energyMesh) ∧
      (∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀j,
        rmin ≤ ell j / d ∧ ell j / d ≤ batchMesh ∧ ell j / d ≤ physicalRange) := by
  let R := min physicalRange (energyMesh / dmin)
  have hR : 0 < R := lt_min hphysicalRange (div_pos henergyMesh hdmin)
  obtain ⟨N, hN, ell, rmin, hrmin, hinj, hsum, hslots, hphysical⟩ :=
    Parameters.exists_physical_slot_lengths_total total dmin dmax batchMesh R
      htotal hdmin hd hbatchMesh hR
  refine ⟨N, hN, ell, rmin, hrmin, hinj, hsum, ?_, ?_⟩
  · intro j
    have h := hslots j
    refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
    · exact h.2.2.2.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · apply h.2.2.2.trans
      calc
        dmin * R ≤ dmin * (energyMesh / dmin) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le
        _ = energyMesh := mul_div_cancel₀ _ hdmin.ne'
  · intro d hdl hdu j
    have h := hphysical d hdl hdu j
    exact ⟨h.1, h.2.1, h.2.2.trans (min_le_left _ _)⟩

theorem batch_fiber_absolute_slot_width
    {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label : Type*} {N : ℕ}
    {U a ε tstar T allowance : ℝ} {i : ℕ}
    (B : Batch M H Label (Fin N) U a ε tstar T allowance i)
    (ell : Fin N → ℝ) (d : ℝ) (hd : d ≠ 0)
    (hwidths : B.widths = fun s => ell s / d)
    (bin : B.Bin) (label : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin label J K).Nonempty) (s : Fin N) :
    d * (B.fiber bin label J K hne).widths s = ell s := by
  change d * B.widths s = ell s
  rw [hwidths]
  exact mul_div_cancel₀ _ hd

end OAI.SevenEighths.GenericSourceIdealAndMesh
