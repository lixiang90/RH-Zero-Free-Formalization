/-
Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
For the actual pinned OAI ray quotient, every quotient character has coefficient
one on identityClass ideals. This pointwise arithmetic identity is an input to
the detector finite-row/energy dictionary; it does not assert a moment bound.
-/
import OAI.NumberTheory.DirichletL.RayQuotient

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.RayQuotient
open RayOrthogonality
variable {A : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    (M : Ideal A) [Finite (A ⧸ M)] (H : Subgroup (A ⧸ M)ˣ)
    (hH : globalUnits M ≤ H)

theorem idealCharacter_eq_one_of_identityClass (χ : Characters M H)
    {I : Ideal A} (hI : I ∈ identityClass M H) :
    idealCharacter M H hH χ I = 1 := by
  obtain ⟨hI, a, ha, u, hu, huH⟩ := hI
  change IdealCharacter.ofResidue M χ (character_unitInvariant M H hH χ) I = 1
  rw [IdealCharacter.ofResidue_of_generator M χ _ hI ha, ←hu]
  exact (mem_characters_iff H χ).mp χ.property u huH

end OAI.SevenEighths.RayQuotient
