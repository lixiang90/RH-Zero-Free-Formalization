/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual certified PositiveAt supply with one degree and finite seminorm set
chosen before every character and ideal. The positive constant and eventual
source-scale threshold may depend on those later arithmetic inputs. -/
import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.UniformDegreePositiveAtLowKappa
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound
local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem exists_degree_before_character_positiveAt
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap κ ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hκ0 : (37/50 : ℝ) ≤ κ)
    (hε : 0 < ε) (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2 * HeckeZeroSupremum.beta - 1 ≤ κ) :
    ∃degree : ℕ, ∃S : Finset (ℕ × ℕ),
      ∀η₀ : Character, ∀Q : Ideal O,
        Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
          internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
        ∃C : ℝ, 0 < C ∧ ∀ᶠZ : ℝ in atTop, 1 < Z ∧
          PositiveAt (α := Slot) M H hH W bslot a b radial Bmask L
            (fineMesh Mcap Bmask L κ ε) lo hi Mcap ε κ Z η₀ Q degree S C := by
  have hcert := CenteredMomentEnergyCertifiedExistence.terminal_certificate (α := Slot)
    M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
  obtain ⟨degree, S, hterminal⟩ := certified_terminal (α := Slot) M H hH W bslot a b
    radial Bmask L lo hi Mcap κ ε hmask hMcap.le (by linarith only [hκ0]) hε hcert
  refine ⟨degree, S, ?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Czero, Cpositive, _, hCpositive, hz⟩ :=
    hterminal η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cpositive, hCpositive, ?_⟩
  filter_upwards [hz] with Z hZ
  exact ⟨hZ.1, hZ.2.2⟩

end OAI.SevenEighths.UniformDegreePositiveAtLowKappa
