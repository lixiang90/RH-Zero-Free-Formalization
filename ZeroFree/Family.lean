
import ZeroFree.Signal
import ZeroFree.UpstreamSupremum

/- Quantified family contradiction. The arithmetic signal package is explicit
   input data; its existence for the paper's Hecke family is not proved here. -/
noncomputable section
namespace ZeroFree.Family
open Filter Asymptotics MeasureTheory

def zeroRealParts {ι : Type*} (L : ι → ℂ → ℂ) (Allowed : ι → ℂ → Prop) : Set ℝ :=
  {x | ∃ i ρ, Allowed i ρ ∧ L i ρ = 0 ∧ x = ρ.re}

/-- Concrete analytic signal objects, including every estimate needed for the
conditional continuation. This structure contains no zero-free conclusion. -/
structure SignalData {ι : Type*} (L : ι → ℂ → ℂ) (Allowed : ι → ℂ → Prop)
    (σ β ω high c : ℝ) where
  regular : ι → ℂ → ℂ
  regularizer : ι → ℂ → ℂ
  correction : ι → ℂ → ℂ
  physical : ι → ℝ → ℂ
  principal : ι → ℝ → ℂ
  regular_analytic : ∀ i, AnalyticOnNhd ℂ (regular i)
    {s : ℂ | β-Signal.margin σ β ω high < s.re}
  regularizer_analytic : ∀ i, AnalyticOnNhd ℂ (regularizer i)
    {s : ℂ | β-Signal.margin σ β ω high < s.re}
  correction_analytic : ∀ i, AnalyticOnNhd ℂ (correction i) {s : ℂ | σ < s.re}
  correction_bound : ∀ i s, σ < s.re → ‖correction i s-1‖ ≤ (1/2 : ℝ)
  local_integrability : ∀ i, LocallyIntegrableOn (principal i) (Set.Ioi 0)
  rapid_decay : ∀ i, Continuation.RapidDecayAtZero (principal i)
  low_bound : ∀ i, physical i =O[atTop] (fun x : ℝ => x ^ (σ+c+ω))
  high_bound : ∀ i, (fun x => physical i x-principal i x) =O[atTop]
    (fun x : ℝ => x ^ (β+c-high))
  mellin_identity : ∀ i s, max (β-Signal.margin σ β ω high) 1 < s.re →
    regular i s * Continuation.signalMellin (principal i) c s =
      regularizer i s * Continuation.gaussianMultiplier (correction i) s
  regularization : ∀ i s, Allowed i s →
    β-Signal.margin σ β ω high < s.re → regular i s = regularizer i s * L i s
  regularizer_nonzero : ∀ i s, Allowed i s →
    β-Signal.margin σ β ω high < s.re → regularizer i s ≠ 0

theorem SignalData.nonzero {ι : Type*} {L : ι → ℂ → ℂ} {Allowed : ι → ℂ → Prop}
    {σ β ω high c : ℝ} (data : SignalData L Allowed σ β ω high c) (hω : 0 < ω)
    {i : ι} {ρ : ℂ} (hallowed : Allowed i ρ)
    (hρ : β-Signal.margin σ β ω high < ρ.re) : L i ρ ≠ 0 :=
  Signal.nonzero_of_common_signal σ β ω high c hω
    (L i) (data.regular i) (data.regularizer i) (data.correction i)
    (data.physical i) (data.principal i)
    (data.regular_analytic i) (data.regularizer_analytic i)
    (data.correction_analytic i) (data.correction_bound i)
    (data.local_integrability i) (data.rapid_decay i)
    (data.low_bound i) (data.high_bound i) (data.mellin_identity i) hρ
    (data.regularization i ρ hallowed hρ) (data.regularizer_nonzero i ρ hallowed hρ)

/-- No attainment of the family supremum is assumed. The same positive margin
must work for every family member, while its constants and signal may vary. -/
theorem supremum_le_of_signal_data {ι : Type*}
    (L : ι → ℂ → ℂ) (Allowed : ι → ℂ → Prop) (σ : ℝ) (hσ : 1/2 ≤ σ)
    (hbounded : BddAbove (insert (1/2 : ℝ) (zeroRealParts L Allowed)))
    (hdata : σ < sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed)) →
      ∃ ω high c : ℝ, 0 < ω ∧
        ω < sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed))-σ ∧
        0 < high ∧ Nonempty (SignalData L Allowed σ
          (sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed))) ω high c)) :
    sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed)) ≤ σ := by
  by_contra! hbad
  obtain ⟨ω, high, c, hω0, hω, hh, ⟨data⟩⟩ := hdata hbad
  have hmargin := Signal.margin_pos hω hh
  have hboundary := Signal.continuation_boundary_gt
    (σ:=σ) (β:=sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed))) (high:=high) hω0
  obtain ⟨x, hx, hlt⟩ := UpstreamSupremum.exists_gt_supremum_sub_of_insert
    hbounded hmargin (by linarith : (1/2 : ℝ) ≤
      sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed))-
        Signal.margin σ (sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed))) ω high)
  obtain ⟨i, ρ, ha, hz, heq⟩ := hx
  subst x
  exact data.nonzero hω0 ha hlt hz

theorem no_zero_of_signal_data {ι : Type*}
    (L : ι → ℂ → ℂ) (Allowed : ι → ℂ → Prop) (σ : ℝ) (hσ : 1/2 ≤ σ)
    (hbounded : BddAbove (insert (1/2 : ℝ) (zeroRealParts L Allowed)))
    (hdata : σ < sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed)) →
      ∃ ω high c : ℝ, 0 < ω ∧
        ω < sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed))-σ ∧
        0 < high ∧ Nonempty (SignalData L Allowed σ
          (sSup (insert (1/2 : ℝ) (zeroRealParts L Allowed))) ω high c))
    {i : ι} {ρ : ℂ} (ha : Allowed i ρ) (hρ : σ < ρ.re) : L i ρ ≠ 0 := by
  have hsup := supremum_le_of_signal_data L Allowed σ hσ hbounded hdata
  intro hz
  have hm : ρ.re ∈ insert (1/2 : ℝ) (zeroRealParts L Allowed) :=
    Set.mem_insert_of_mem _ ⟨i, ρ, ha, hz, rfl⟩
  have hle := le_csSup hbounded hm
  linarith

end ZeroFree.Family

