/-
Copyright (c) 2026 Li Xiang.
Author: Li Xiang
-/
import OAI.NumberTheory.DirichletL.Detector.ArbitraryTotalSourceBatch
import OAI.NumberTheory.DirichletL.PrimeRows.CubeSupportedWitness

set_option autoImplicit false

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Actual source Batch existence with an arbitrary positive total slot length.
The small witness growth parameter κw and its original budget are preserved. -/
theorem actual_source_batch_total (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀ P ∈ S, P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κw heightCost margin mesh binWidth Λ : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (hΛ : 0 < Λ) (hdtop : dmax ≤ 37 * Λ / 7) (hτ : 0 < τ)
    (hτzero : τ < dmin / 2) (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000)
    (hκw : 0 < κw) (hκw' : κw ≤ 1) (hheightCost : 0 ≤ heightCost)
    (hmargin : 0 < margin) (hm : 0 ≤ mesh) (hb : 0 < binWidth)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κw + 2 * heightCost ≤ ε / 2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    ∀ (U : ℝ) (rows : Finset FreeRow), rows.Nonempty →
      rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) U →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
    ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
      (∀ u ∈ rows, detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows, a ≤ detectorMaximum
        (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3 * i : ℕ) * Z ^ τ)) →
    ∀ tstar : ℝ, 1 ≤ tstar → tstar ≤ 3 / 2 →
    ∀ (N : ℕ) (ell : Fin N → ℝ),
      (∀ j, 0 < ell j) → (∀ j, ell j ≤ dmin * mesh) → (∑ j, ell j) = Λ →
    ∀ (W : Fin N → ℝ → ℂ) (upper : Fin N → ℝ) (z : Fin N → ℂ),
    ∃ B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z ^ d) a ε tstar (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
      B.rows = rows ∧ B.data = sourceMomentData M H hH S hS.prime η ∧
      B.reverse = sourceMomentReverse M H ∧ B.slots = Finset.univ ∧
      B.widths = (fun j => ell j / d) ∧ B.profile = W ∧ B.upper = upper ∧
      B.external = z ∧ B.mesh = mesh ∧ B.binWidth = binWidth ∧
      (∀ u ∈ rows, ∀ j, B.family u j =
        sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κw heightCost margin I hdmin hdmax hτ hτzero hτheight
    hε he he' hκw hκw' hheightCost hmargin hbudget
  filter_upwards [hw, eventually_ge_atTop (1 : ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent
    tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u => hnext u.val u.property) (fun u => hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0, h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u ∈ rows) : rowNorm u ≤ Z ^ d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  let B := retainedSourceBatchTotal M H hH S hS η rows u0 h0
    Z d dmin a ε tstar (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) Λ i
    (fun u hu => w ⟨u, hu⟩) hnorm ell W upper z mesh binWidth hm hb
    hdmin hd hΛ (hd'.trans hdtop) hell hsmall hsum
  refine ⟨B, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro u hu j
  dsimp [B, retainedSourceBatchTotal, retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]

end SevenEighths.ProbeHighRowFamily

end

end OAI
