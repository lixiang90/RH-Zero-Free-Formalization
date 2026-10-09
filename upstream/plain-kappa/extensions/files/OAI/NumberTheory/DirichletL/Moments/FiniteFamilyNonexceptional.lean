/- Copyright (c) 2026 Li Xiang. Released under Apache-2.0.
Actual fixed-inducing free-row control for any finite character/ideal family,
independent of a SourceData record or a prescribed total slot length.
The fixed-ideal and positive row-growth hypotheses remain explicit. -/import OAI.NumberTheory.DirichletL.CenteredExceptionalProfile
import OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationRows

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace OAI.SevenEighths.FiniteFamilyNonexceptional
open HeckeFamily HeckeInverseAmplification UniqueFactorizationMonoid
open CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def fixedExceptionalBound (Q : Ideal O) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors Q).toFinset

theorem fixed_inducing_free_norm_le (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hQη : Q ≤ η.modulus) (m : O) (hm : m ≠ 0)
    (hml : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    (Ideal.span {u.val}).absNorm ≤ fixedExceptionalBound Q := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP => prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  obtain ⟨χ, ψ, hprim, hind, hψ, hχ⟩ := hu
  refine ⟨u.property.1, ?_⟩
  intro P hP
  refine ⟨?_, u.property.2 P⟩
  by_contra hout
  have hp : Prime P := prime_of_normalized_factor P hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl, h2, hQP⟩ := outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P := hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz := actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow, one_mul, valuation] at hz
  have hpos := Multiset.count_pos.mpr hP
  have hlt := u.property.2 P
  omega

theorem eventually_finite_family_no_fixed_inducing
    {Label : Type*} [Fintype Label] (η : Label → Character) (Q : Label → Ideal O)
    (hQ0 : ∀ j, Q j ≠ 0) (hQ : ∀ j, Q j ≠ ⊤)
    (hQ72 : ∀ j, Q j ≤ Ideal.span {(72 : O)}) (hQη : ∀ j, Q j ≤ (η j).modulus)
    (rmin : ℝ) (hrmin : 0 < rmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ j : Label, ∀ u : FreeRow,
      Z ^ rmin ≤ ((Ideal.span {u.val}).absNorm : ℝ) →
      ∀ m : O, m ≠ 0 → goodLambda ∣ m → (2 : O) ∣ m →
        ¬FixedInducingRow (η j) (Q j) m 1 u.val := by
  have hbound : ∀ᶠ Z : ℝ in atTop, ∀ j : Label,
      (fixedExceptionalBound (Q j) : ℝ) < Z ^ rmin := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop hrmin).eventually (eventually_gt_atTop _)
  filter_upwards [hbound] with Z hZ
  intro j u hrow m hm hml hm2 hex
  have hb : ((Ideal.span {u.val}).absNorm : ℝ) ≤ fixedExceptionalBound (Q j) := by
    exact_mod_cast fixed_inducing_free_norm_le (η j) (Q j) (hQ0 j) (hQ j)
      (hQ72 j) (hQη j) m hm hml hm2 u hex
  exact (not_lt_of_ge (hrow.trans hb)) (hZ j)

end OAI.SevenEighths.FiniteFamilyNonexceptional
