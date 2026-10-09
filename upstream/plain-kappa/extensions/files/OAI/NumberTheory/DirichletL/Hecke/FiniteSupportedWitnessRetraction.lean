/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Extend an actual SupportedWitness family from a nonempty finite FreeRow set.
A retraction preserves the whole supplied witness structure on every retained
row, without requiring new all-row detector hypotheses. -/
import OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows

noncomputable section
open scoped Classical
namespace OAI.SevenEighths.FiniteSupportedWitnessRetraction
set_option autoImplicit false
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness

theorem finite_supported_witness_retraction
    {Label : Type*} (rows : Finset FreeRow) (hne : rows.Nonempty)
    (χ : rows → Label → Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀u : rows, SupportedWitness (χ u) U a ε tstar T allowance i) :
    ∃r : FreeRow → rows, (∀u : rows, r u.val = u) ∧
      ∃W : ∀u : FreeRow, SupportedWitness (χ (r u)) U a ε tstar T allowance i,
        ∀u : rows, HEq (W u.val) (w u) := by
  obtain ⟨u₀, hu₀⟩ := hne
  let base : rows := ⟨u₀, hu₀⟩
  let r : FreeRow → rows := fun u => if hu : u ∈ rows then ⟨u, hu⟩ else base
  have hr (u : rows) : r u.val = u := by
    dsimp only [r]
    rw [dite_eq_left u.property]
  refine ⟨r, hr, fun u => w (r u), ?_⟩
  intro u
  have hw (v v' : rows) (h : v = v') : HEq (w v) (w v') := by
    cases h
    rfl
  exact hw (r u.val) u (hr u)

end OAI.SevenEighths.FiniteSupportedWitnessRetraction
