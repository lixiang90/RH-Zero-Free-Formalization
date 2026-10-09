/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Private universal source-dictionary one-field candidate. The two promoted
ideal/mesh and losses-before-Slot imports are pending canonical installation.
This source has not yet been compiled, freshly audited or independently replayed.
The conclusion covers every matching Batch, not only a constructed witness. -/
import OAI.NumberTheory.DirichletL.Moments.LossesBeforeSlotSourcePlainMarkedLowKappa
import OAI.NumberTheory.DirichletL.Moments.GenericSourceIdealAndMesh
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.SourcePlainMarkedUniversalCandidate
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorBatch HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial HeckeDetectorWitnessRows ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyWidthRanges GenericSourceIdealAndMesh
open LossesBeforeSlotSourcePlainMarkedLowKappa
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The true moving-kappa plain-marked field on the original source dictionary.
Its quantifiers and every matching-Batch condition follow SourceMomentsAt;
the other three Moments fields are deliberately not asserted here. -/
def SourcePlainMarkedAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P ∈ S, Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N → ℝ) (W : ℝ → ℂ)
    (Z d a ε τ dmax bslot slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (κPlain C height εm : ℝ) : Prop :=
  ∀q : ℝ, ∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ)
      ((Z^d)^(τ/(2*dmax))) i,
    B.rows ⊆ rows → B.data = sourceMomentData M H hH S hS η →
    B.reverse = sourceMomentReverse M H → B.slots = Finset.univ →
    B.widths = (fun j => ell j/d) → B.profile = (fun _ => W) →
    B.upper = (fun _ => bslot) → B.external = (fun _ => z) →
    B.mesh = slotMesh → B.binWidth = binWidth →
    (∀u ∈ B.rows, ∀j, B.family u j =
      sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin label J K, ∀hne : (B.fiberRows bin label J K).Nonempty,
      let F := B.fiber bin label J K hne
      ∀selected : Finset (Fin N), selected ⊆ F.slots →
      2*F.m + 6*κPlain*(∑s ∈ selected, F.widths s) ≤ 1 →
      ∀j k : ℕ, j+k ≤ 2 →
      ∀σ ∈ Set.Icc (0 : ℝ) 1, ∀t ∈ Set.Icc (-height) height,
        (∑u ∈ F.rows,
          ‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
              ((Z^d)^F.m) σ t *
            polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
              ((Z^d)^F.m) σ t * F.physicalProduct selected u‖^2) ≤
          C*(Z^d)^(1+εm)

/-- Common losses determine the native energy mesh before constructing N/ell.
After that Slot=Fin N, the actual terminal/profile degrees and a common height
ceiling precede every outer character. Its single positive constant and source
threshold cover all q, all matching Batch records and all nonempty fibers. -/
theorem exists_source_slots_and_universal_plain_marked
    (S : Finset (Ideal O)) (hS : ∀P ∈ S, Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S) (hM : M = ∏P ∈ S, P)
    (W : ℝ → ℂ)
    (aslot bslot total dmin dmax Mcap L rowExponent εm τ₀ κEnergy κPlain
      batchMesh physicalRange : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (htotal : 0 < total) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (hcapMargin : dmax < Mcap) (hL : dmax/2 ≤ L)
    (hrowExponent : 0 < rowExponent) (hεm : 0 < εm) (hτ₀ : 0 < τ₀)
    (hκ0 : (37/50 : ℝ) ≤ κEnergy) (hκPlain : κEnergy ≤ κPlain)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hκ : 2*HeckeZeroSupremum.beta - 1 ≤ κEnergy)
    (hbatchMesh : 0 < batchMesh) (hphysicalRange : 0 < physicalRange) :
    ∃ρ εE : ℝ, 0 < ρ ∧ 0 < εE ∧ ρ ≤ Mcap-dmax ∧
    ∃N : ℕ, 0 < N ∧ ∃ell : Fin N → ℝ, ∃slotLower : ℝ, 0 < slotLower ∧
      Function.Injective ell ∧ (∑s, ell s) = total ∧
      (∀s, 0 < ell s ∧ dmax*slotLower ≤ ell s ∧ ell s ≤ dmin*batchMesh ∧
        ell s ≤ dmin*physicalRange ∧ ell s ≤ fineMesh Mcap 0 L κEnergy εE) ∧
      (∀d : ℝ, dmin ≤ d → d ≤ dmax → ∀s,
        slotLower ≤ ell s/d ∧ ell s/d ≤ batchMesh ∧ ell s/d ≤ physicalRange) ∧
    ∃degree J : ℕ, ∃τ : ℝ, 0 < τ ∧ τ ≤ τ₀ ∧
      ρ + εE + 2*τ*((degree+4*J : ℕ) : ℝ) ≤ dmin*εm ∧
    ∀η : Character, ∃C : ℝ, 0 < C ∧
    ∀ᶠZ : ℝ in atTop, 1 < Z ∧
      ∀τ' : ℝ, 0 < τ' → τ' ≤ τ →
      ∀d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀rows : Finset FreeRow,
        (∀u ∈ rows, Z^rowExponent ≤ ((Ideal.span {u.val}).absNorm : ℝ)) →
      ∀(a ε binWidth : ℝ) (i : ℕ) (z : ℂ), z.re = 17/50 →
      ∀height : ℝ, 0 ≤ height → height ≤ Z^(2*τ') → |z.im| ≤ height →
        SourcePlainMarkedAt M H hH S hS η rows ell W Z d a ε τ' dmax bslot
          batchMesh binWidth i z κPlain C height εm := by
  have hMm : M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement} := by
    rw [hM]
    exact source_product_le_rowMask S hbad
  obtain ⟨ρ, εE, hρ, hεE, hρcap, hslotSupply⟩ :=
    exists_losses_before_slots_degrees_height_and_finite_family M H hH hMm W
      aslot bslot dmin dmax Mcap L rowExponent εm τ₀ κEnergy κPlain
      haslot hWs hW hbslot hdmin hdmax hcapMargin hL hrowExponent hεm hτ₀
      hκ0 hκPlain hbeta hκ
  have hMcap : 0 ≤ Mcap := (hdmin.trans_le (hdmax.trans hcapMargin.le)).le
  have hκEnergy : 0 ≤ κEnergy := by linarith only [hκ0]
  have henergyMesh : 0 < fineMesh Mcap 0 L κEnergy εE :=
    fineMesh_pos Mcap 0 L κEnergy εE hMcap (by norm_num) hκEnergy hεE
  obtain ⟨N, hN, ell, slotLower, hslotLower, hinj, hsum, hslots, hphysical⟩ :=
    exists_source_slots_for_both_meshes total dmin dmax batchMesh physicalRange
      (fineMesh Mcap 0 L κEnergy εE) htotal hdmin hdmax hbatchMesh hphysicalRange henergyMesh
  obtain ⟨degree, J, τ, hτ, hτle, hbudget, hfamily⟩ := hslotSupply (Slot := Fin N)
  refine ⟨ρ, εE, hρ, hεE, hρcap, N, hN, ell, slotLower, hslotLower, hinj,
    hsum, hslots, hphysical, degree, J, τ, hτ, hτle, hbudget, ?_⟩
  intro η
  let ηlabel := sourceMomentBase M H hH S hS η
  let Q0 : Ideal O := M ⊓ Ideal.span {(72 : O)}
  have hQ := source_fixed_ideal_gates M S hS hbad hM
  obtain ⟨Φ, hΦnonneg, hΦreal, C, hC, hbound⟩ :=
    hfamily ηlabel (fun _ => Q0) (fun _ => hQ.1)
      (fun label => (hQ.2.2.2 (ηlabel label)).1)
      (fun label => (hQ.2.2.2 (ηlabel label)).2.1)
      (fun label => (hQ.2.2.2 (ηlabel label)).2.2.1)
  have hcop := eventually_source_slots_coprime M H hH S hS η ell
    (fun s => (hslots s).1) aslot haslot
  have hWsLower : Function.support W ⊆ Set.Ici aslot := by
    intro x hx
    exact (hWs hx).1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hcop] with Z hb hc
  refine ⟨hb.1, ?_⟩
  intro τ' hτ' hτ'le d hd hd' rows hrowLower a ε binWidth i z hz
    height hheight hheight_le hzim
  intro q B hrows hdata hreverse hBslots hwidths hprofile hupper hexternal
    hmesh hbinWidth hfamilySource bin label Ileft Iright hne
  let F := B.fiber bin label Ileft Iright hne
  have hd0 : 0 < d := hdmin.trans_le hd
  have hfdata : F.rowData = ProbeHighRowFamily.momentData (ηlabel F.label) := by
    change B.data label = ProbeHighRowFamily.momentData (ηlabel label)
    rw [hdata]
    exact sourceMomentData_base M H hH S hS η label
  have hfrow : ∀u ∈ F.rows, Z^rowExponent ≤ ((Ideal.span {u.val}).absNorm : ℝ) := by
    intro u hu
    apply hrowLower u
    apply hrows
    exact (Finset.mem_filter.mp hu).1
  have hfprofile : F.profile = fun _ => W := hprofile
  have hfupper : F.upper = fun _ => bslot := hupper
  have hfwidths : F.widths = fun s => ell s/d := hwidths
  have hfexternal : F.external = fun _ => z := hexternal
  have hfprime : ∀s ∈ F.slots,
      ∀P ∈ primePool M H (F.upper s) ((Z^d)^(F.widths s)),
        F.profile s ((P.absNorm : ℝ)/((Z^d)^(F.widths s))) ≠ 0 →
          IsCoprime P (ηlabel F.label).modulus := by
    intro s hs P hP hnonzero
    change IsCoprime P (ηlabel label).modulus
    apply hc label s d hd0.ne' W bslot hWsLower P
    · simpa only [hfupper, hfwidths] using hP
    · simpa only [hfprofile, hfwidths] using hnonzero
  have hfmesh : ∀s ∈ F.slots, d*F.widths s ≤ fineMesh Mcap 0 L κEnergy εE := by
    intro s hs
    rw [batch_fiber_absolute_slot_width B ell d hd0.ne' hwidths bin label Ileft Iright hne s]
    exact (hslots s).2.2.2.2
  have hfreal : ∀s ∈ F.slots, (F.external s).re = 17/50 := by
    intro s hs
    rw [hfexternal]
    exact hz
  have hffrequency : ∀s ∈ F.slots, |(F.external s).im| ≤ height := by
    intro s hs
    rw [hfexternal]
    exact hzim
  exact hb.2 τ' hτ' hτ'le d hd hd' a ε
    (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ') ((Z^d)^(τ'/(2*dmax))) i
    F hfdata hfrow (fun s hs => congrFun hfprofile s) (fun s hs => congrFun hfupper s)
    hfprime hfmesh hfreal height hheight hheight_le hffrequency

end OAI.SevenEighths.SourcePlainMarkedUniversalCandidate
