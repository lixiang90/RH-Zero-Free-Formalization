import ZeroFree.Main
import ZeroFree.HeightClosure
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.RemovableSingularity

/- Standard analytic facts about Mathlib's actual zeta function. The arithmetic
   signal construction is still required; none of these lemmas assumes it. -/
set_option autoImplicit false

noncomputable section
namespace ZeroFree.ZetaConcrete
open Filter Asymptotics MeasureTheory
open scoped Topology

/-- Fill the removed pole with the proved residue, rather than the totalized
value of zeta at one. -/
def regularZeta : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s-1)*riemannZeta s) 1 1

theorem regularZeta_one : regularZeta 1 = 1 := by
  simp [regularZeta]

theorem regularZeta_eq {s : ℂ} (hs : s ≠ 1) :
    regularZeta s = (s-1)*riemannZeta s := by
  simp [regularZeta, hs]

theorem regularZeta_differentiableAt_of_ne {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ regularZeta s := by
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => (z-1)*riemannZeta z) s :=
    (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
  apply hdiff.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hs] with z hz
  exact regularZeta_eq hz

theorem regularZeta_continuousAt_one : ContinuousAt regularZeta 1 := by
  exact continuousAt_update_same.mpr riemannZeta_residue_one

theorem regularZeta_analyticAt_one : AnalyticAt ℂ regularZeta 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    ?_ regularZeta_continuousAt_one
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact regularZeta_differentiableAt_of_ne hz

theorem regularZeta_entire : Differentiable ℂ regularZeta := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact regularZeta_analyticAt_one.differentiableAt
  · exact regularZeta_differentiableAt_of_ne hs

theorem regularZeta_analytic (S : Set ℂ) : AnalyticOnNhd ℂ regularZeta S := by
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr regularZeta_entire).mono
    (Set.subset_univ S)

theorem regularizer_analytic (S : Set ℂ) :
    AnalyticOnNhd ℂ (fun s : ℂ => s-1) S := by
  intro s _
  exact analyticAt_id.sub analyticAt_const

theorem regularizer_nonzero {s : ℂ} (hs : s ≠ 1) : s-1 ≠ 0 := sub_ne_zero.mpr hs

def zeroReals : Set ℝ :=
  insert (1/2 : ℝ) (Family.zeroRealParts (fun _ : Unit => riemannZeta) (fun _ s => s ≠ 1))

theorem zeroReals_le_one {x : ℝ} (hx : x ∈ zeroReals) : x ≤ 1 := by
  rcases Set.mem_insert_iff.mp hx with h | h
  · subst x
    norm_num
  · obtain ⟨i, s, ha, hz, heq⟩ := h
    subst x
    by_contra! hlt
    exact riemannZeta_ne_zero_of_one_lt_re hlt hz

theorem zeroReals_bounded : BddAbove zeroReals :=
  ⟨1, fun _ hx => zeroReals_le_one hx⟩

theorem zeroReals_nonempty : zeroReals.Nonempty := ⟨1/2, Set.mem_insert _ _⟩

theorem zero_supremum_bounds : (1/2 : ℝ) ≤ sSup zeroReals ∧ sSup zeroReals ≤ 1 := by
  constructor
  · exact le_csSup zeroReals_bounded (Set.mem_insert _ _)
  · apply csSup_le zeroReals_nonempty
    exact fun _ hx => zeroReals_le_one hx

/-- Only the arithmetic correction and the two actual signals remain as data.
Entire pole removal, regularizer properties, and bounded zeros are proved above. -/
structure SignalData (σ β ω high c : ℝ) where
  correction : ℂ → ℂ
  physical : ℝ → ℂ
  principal : ℝ → ℂ
  correction_analytic : AnalyticOnNhd ℂ correction {s : ℂ | σ < s.re}
  correction_bound : ∀ s, σ < s.re → ‖correction s-1‖ ≤ (1/2 : ℝ)
  local_integrability : LocallyIntegrableOn principal (Set.Ioi 0)
  rapid_decay : Continuation.RapidDecayAtZero principal
  low_bound : physical =O[atTop] (fun x : ℝ => x ^ (σ+c+ω))
  high_bound : (fun x => physical x-principal x) =O[atTop]
    (fun x : ℝ => x ^ (β+c-high))
  mellin_identity : ∀ s, max (β-Signal.margin σ β ω high) 1 < s.re →
    regularZeta s * Continuation.signalMellin principal c s =
      (s-1) * Continuation.gaussianMultiplier correction s

def SignalData.toFamily {σ β ω high c : ℝ} (data : SignalData σ β ω high c) :
    Family.SignalData (fun _ : Unit => riemannZeta) (fun _ s => s ≠ 1) σ β ω high c where
  regular := fun _ => regularZeta
  regularizer := fun _ s => s-1
  correction := fun _ => data.correction
  physical := fun _ => data.physical
  principal := fun _ => data.principal
  regular_analytic := fun _ => regularZeta_analytic _
  regularizer_analytic := fun _ => regularizer_analytic _
  correction_analytic := fun _ => data.correction_analytic
  correction_bound := fun _ => data.correction_bound
  local_integrability := fun _ => data.local_integrability
  rapid_decay := fun _ => data.rapid_decay
  low_bound := fun _ => data.low_bound
  high_bound := fun _ => data.high_bound
  mellin_identity := fun _ => data.mellin_identity
  regularization := fun _ _ hs _ => regularZeta_eq hs
  regularizer_nonzero := fun _ _ hs _ => regularizer_nonzero hs

def ArithmeticSignalObligation : Prop :=
  sigmaStar < sSup zeroReals →
    ∃ ω high c : ℝ, 0 < ω ∧ ω < sSup zeroReals-sigmaStar ∧
      0 < high ∧ Nonempty (SignalData sigmaStar (sSup zeroReals) ω high c)

theorem arithmeticSignalObligation_suffices (h : ArithmeticSignalObligation) :
    ZeroFree.ZetaSignalObligation := by
  refine ⟨zeroReals_bounded, ?_⟩
  intro hb
  obtain ⟨ω, high, c, hω0, hω, hh, ⟨data⟩⟩ := h hb
  exact ⟨ω, high, c, hω0, hω, hh, ⟨data.toFamily⟩⟩

theorem riemannZeta_ne_zero_of_arithmetic_signal (h : ArithmeticSignalObligation)
    {s : ℂ} (hs : sigmaStar < s.re) (hpole : s ≠ 1) : riemannZeta s ≠ 0 :=
  ZeroFree.riemannZeta_ne_zero_of_cubic_signal (arithmeticSignalObligation_suffices h) hs hpole

/-- Before choosing the height exponent or the tail order, the remaining
arithmetic data provide the raw high estimate with N-independent powers. -/
structure RawSignalData (σ β ω c m A B τ₀ : ℝ) where
  correction : ℂ → ℂ
  physical : ℝ → ℂ
  principal : ℝ → ℂ
  correction_analytic : AnalyticOnNhd ℂ correction {s : ℂ | σ < s.re}
  correction_bound : ∀ s, σ < s.re → ‖correction s-1‖ ≤ (1/2 : ℝ)
  local_integrability : LocallyIntegrableOn principal (Set.Ioi 0)
  rapid_decay : Continuation.RapidDecayAtZero principal
  low_bound : physical =O[atTop] (fun x : ℝ => x ^ (σ+c+ω))
  high_estimate : HeightClosure.HighEstimate
    (fun x => physical x-principal x) β c m A B τ₀
  mellin_identity : ∀ s, max (β-Signal.margin σ β ω (m/2)) 1 < s.re →
    regularZeta s * Continuation.signalMellin principal c s =
      (s-1) * Continuation.gaussianMultiplier correction s

def RawSignalData.toSignal {σ β ω c m A B τ₀ : ℝ}
    (data : RawSignalData σ β ω c m A B τ₀)
    (hm : 0 < m) (hA : 0 ≤ A) (hτ₀ : 0 < τ₀) : SignalData σ β ω (m/2) c where
  correction := data.correction
  physical := data.physical
  principal := data.principal
  correction_analytic := data.correction_analytic
  correction_bound := data.correction_bound
  local_integrability := data.local_integrability
  rapid_decay := data.rapid_decay
  low_bound := data.low_bound
  high_bound := HeightClosure.collapse_high_estimate hm hA hτ₀ data.high_estimate
  mellin_identity := data.mellin_identity

def RawArithmeticSignalObligation : Prop :=
  sigmaStar < sSup zeroReals →
    ∃ ω c m A B τ₀ : ℝ, 0 < ω ∧ ω < sSup zeroReals-sigmaStar ∧
      0 < m ∧ 0 ≤ A ∧ 0 < τ₀ ∧
      Nonempty (RawSignalData sigmaStar (sSup zeroReals) ω c m A B τ₀)

theorem rawArithmeticSignalObligation_suffices (h : RawArithmeticSignalObligation) :
    ArithmeticSignalObligation := by
  intro hb
  obtain ⟨ω, c, m, A, B, τ₀, hω0, hω, hm, hA, hτ₀, ⟨data⟩⟩ := h hb
  exact ⟨ω, m/2, c, hω0, hω, by positivity, ⟨data.toSignal hm hA hτ₀⟩⟩

theorem riemannZeta_ne_zero_of_raw_arithmetic_signal (h : RawArithmeticSignalObligation)
    {s : ℂ} (hs : sigmaStar < s.re) (hpole : s ≠ 1) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_arithmetic_signal (rawArithmeticSignalObligation_suffices h) hs hpole

end ZeroFree.ZetaConcrete
