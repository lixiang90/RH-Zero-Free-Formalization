/-
Adapted from OpenAI/math Hecke/Dirichlet under Apache-2.0.
Upstream revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Generalized by Li Xiang / lixiang90 (2026-10-09): transfer an explicitly
supplied zero-free statement for the actual Hecke family on any positive
half-plane threshold to actual Dirichlet L-functions and riemannZeta.
This module proves the transfer only; it does not supply its family premise.
-/
import OAI.NumberTheory.DirichletL.Hecke.Dirichlet

namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

/-- A conditional transfer for the actual factorization, at an arbitrary sigma > 0. -/
theorem dirichlet_ne_zero_of_hecke_halfplane {sigma : ℝ} (hsigma : 0 < sigma)
    (hH : ∀ (eta : Character) (s : ℂ), sigma < s.re →
      (s ≠ 1 ∨ eta.residue ≠ 1) → LFunction eta s ≠ 0)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : sigma < s.re) (hexc : ¬ (chi = 1 ∧ s = 1)) : chi.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact chi.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    have hpos : 0 < s.re := hsigma.trans hs
    simpa only [h, Complex.zero_re, lt_self_iff_false] using hpos
  have h := hH (character chi) s hs (Or.inl hs1)
  rw [LFunction_eq_dirichlet_product chi hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

/-- The family hypothesis stays explicit; no zero-free conclusion is assumed as an axiom. -/
theorem zeta_ne_zero_of_hecke_halfplane {sigma : ℝ} (hsigma : 0 < sigma)
    (hH : ∀ (eta : Character) (s : ℂ), sigma < s.re →
      (s ≠ 1 ∨ eta.residue ≠ 1) → LFunction eta s ≠ 0)
    (s : ℂ) (hs : sigma < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_ne_zero_of_hecke_halfplane hsigma hH
    (1 : DirichletCharacter ℂ 1) s hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end SevenEighths.HeckeDirichlet
end
end OAI
