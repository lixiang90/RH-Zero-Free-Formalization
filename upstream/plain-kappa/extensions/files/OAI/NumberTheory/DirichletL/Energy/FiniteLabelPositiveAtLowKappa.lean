/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Finite fixed-label uniformization of the actual certified PositiveAt supply.
The character/ideal maps are fixed before the atTop source-scale quantifier. -/
import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.FiniteLabelPositiveAtLowKappa
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem eventually_finite_label_positiveAt
    {Label : Type*} [Fintype Label]
    (η : Label → Character) (Q : Label → Ideal O)
    (hQM : ∀j, Q j ≤ M) (hQ0 : ∀j, internalQ (Q j) (η j) ≠ 0)
    (hQt : ∀j, internalQ (Q j) (η j) ≠ ⊤)
    (hQ72 : ∀j, internalQ (Q j) (η j) ≤ Ideal.span {(72 : O)})
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hκ0 : (37/50 : ℝ) ≤ κ)
    (hε : 0 < ε) (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2 * HeckeZeroSupremum.beta - 1 ≤ κ) :
    ∃degree : ℕ, ∃S : Finset (ℕ × ℕ), ∃C : ℝ, 0 < C ∧
      ∀ᶠZ : ℝ in atTop, 1 < Z ∧ ∀j : Label,
        PositiveAt (α := Slot) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z (η j) (Q j) degree S C := by
  have hcert := CenteredMomentEnergyCertifiedExistence.terminal_certificate (α := Slot)
    M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
  obtain ⟨degree, S, hterminal⟩ := certified_terminal (α := Slot) M H hH W bslot a b
    radial Bmask L lo hi Mcap κ ε hmask hMcap.le (by linarith only [hκ0]) hε hcert
  have hlabel (j : Label) : ∃C : ℝ, 0 < C ∧
      ∀ᶠZ : ℝ in atTop, 1 < Z ∧
        PositiveAt (α := Slot) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z (η j) (Q j) degree S C := by
    obtain ⟨Czero, Cpositive, _, hCpositive, hz⟩ :=
      hterminal (η j) (Q j) (hQM j) (hQ0 j) (hQt j) (hQ72 j)
    refine ⟨Cpositive, hCpositive, ?_⟩
    filter_upwards [hz] with Z hZ
    exact ⟨hZ.1, hZ.2.2⟩
  choose Cj hCj hj using hlabel
  let constants : Finset ℝ := insert 1 ((Finset.univ : Finset Label).image Cj)
  have hne : constants.Nonempty := Finset.insert_nonempty _ _
  let C : ℝ := constants.max' hne
  have hOne : (1 : ℝ) ≤ C := by
    exact Finset.le_max' constants 1 (Finset.mem_insert_self _ _)
  have hC : 0 < C := zero_lt_one.trans_le hOne
  have hCbound (j : Label) : Cj j ≤ C := by
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hall : ∀ᶠZ : ℝ in atTop, ∀j : Label, 1 < Z ∧
      PositiveAt (α := Slot) M H hH W bslot a b radial Bmask L
        (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z (η j) (Q j) degree S (Cj j) :=
    Filter.eventually_all.mpr hj
  refine ⟨degree, S, C, hC, ?_⟩
  filter_upwards [hall, eventually_gt_atTop (1 : ℝ)] with Z hZ hZ1
  refine ⟨hZ1, ?_⟩
  intro j
  intro selected θ w σ v t height hw hwL hσlo hσhi hheight hv state hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hh := (hZ j).2 selected θ w σ v t height hw hwL hσlo hσhi hheight hv
    state hQ hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hdiag : 0 ≤ diagonalControl state.radial.profile := diagonalControl_nonneg _
  have hbase : 0 ≤ 1 + |t| + height := by linarith [abs_nonneg t]
  apply hh.trans
  gcongr
  exact hCbound j

end OAI.SevenEighths.FiniteLabelPositiveAtLowKappa
