import ZeroFree.Geometry

/- Exact scalar comparison and clipping-defect repairs extracted from the
modified OpenAI/math reference/reflection proof. They do not formalize
NaturalState, natural character sums, reflected row sums, or moment induction.
See docs/plain-kappa-extension.md for the pending actual upstream chain. -/
set_option autoImplicit false

namespace ZeroFree.PlainComparison


theorem positive_slot_width_drop (M A z xi kappa : ℝ)
    (hM : 0 ≤ M) (hz : 0 ≤ z) (hk : 37/50 ≤ kappa)
    (hA : 5*M/6 ≤ A) (hcap : A+(6*kappa-1)*z ≤ M) :
    3*M/2-A+2*z+xi ≤ 23*M/30+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z ≤ 14*M/15+xi := by
  have hkz : 10/3*z ≤ (6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z ≤ M/20 := by linarith
  constructor <;> nlinarith



theorem slot_budgets (M total ell kappa:ℝ)(_hM:0 ≤ M)(hell:0 ≤ ell)(hk:37/50 ≤ kappa)
    (hlarge:5*M/6 ≤ total+ell)(hcap:total+ell+(6*kappa-1)*ell ≤ M):
    ell ≤ M/20 ∧ (6*kappa-1)*ell ≤ M/6:=by
  have hkell:10/3*ell ≤ (6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0 ≤ M)(_hs:0 ≤ short)(hsM:short ≤ M/4)(_hell:0 ≤ ell)(_hz:0 ≤ z)(hze:z ≤ ell)
    (hk:37/50 ≤ kappa)(he:ell ≤ M/20)(hbudget:(6*kappa-1)*ell ≤ M/6)(hxi:0 ≤ xi)
    (hhigh:5*M/6<short+ max 0 along+z)
    (href:reflected ≤  max 0 (M-along+xi)):
    0<along ∧ reflected+short+z ≤ 23*M/30+xi ∧
      reflected+short+6*kappa*z ≤ 14*M/15+xi:=by
  have haz:0<along:=by
    by_contra hn
    have ha:along ≤ 0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z ≤ M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z ≤ M/20:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0 ≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi ≤ M/15)(ht:reflected+short+z ≤ 23*M/30+xi)
    (hc:reflected+short+6*kappa*z ≤ 14*M/15+xi):
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*kappa*z ≤ M:=by
  constructor <;> linarith



theorem robust_slot_budgets (M total ell kappa defect : ℝ)
    (hell : 0  ≤  ell) (hk : 37/50  ≤  kappa)
    (hlarge : 5*M/6-defect  ≤  total+ell)
    (hcap : total+ell+(6*kappa-1)*ell  ≤  M) :
    ell  ≤  M/20+3*defect/10 ∧ (6*kappa-1)*ell  ≤  M/6+defect := by
  have hkell : 10/3*ell  ≤  (6*kappa-1)*ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem robust_defect_le_width (M xi defect : ℝ) (hM : 0  ≤  M) (hxi : 0  ≤  xi)
    (hreserve : xi+8*defect/5  ≤  M/15) : defect  ≤  M := by
  linarith

theorem robust_balanced_long_nonneg (M total ell kappa xi defect : ℝ)
    (hM : 0  ≤  M) (hell : 0  ≤  ell) (hk : 37/50  ≤  kappa) (hxi : 0  ≤  xi)
    (hlarge : 5*M/6-defect  ≤  total+ell)
    (hcap : total+ell+(6*kappa-1)*ell  ≤  M)
    (hreserve : xi+8*defect/5  ≤  M/15) :
    8*M/15-13*defect/10  ≤  total-M/4 ∧ 0  ≤  total-M/4 := by
  obtain ⟨he, hb⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  constructor <;> linarith

theorem robust_reflected_low (M short along ell z kappa xi defect reflected : ℝ)
    (hM : 0  ≤  M) (_hs : 0  ≤  short) (hsM : short  ≤  M/4)
    (_hell : 0  ≤  ell) (_hz : 0  ≤  z) (hze : z  ≤  ell) (hk : 37/50  ≤  kappa)
    (he : ell  ≤  M/20+3*defect/10)
    (hbudget : (6*kappa-1)*ell  ≤  M/6+defect)
    (hxi : 0  ≤  xi) (hdefect : 0  ≤  defect) (hdefectM : defect  ≤  M)
    (hhigh : 5*M/6 < short+ max 0 along+z)
    (href : reflected  ≤  max 0 (M-along+xi)) :
    0 < along ∧ reflected+short+z  ≤  23*M/30+xi+3*defect/5 ∧
      reflected+short+6*kappa*z  ≤  14*M/15+xi+8*defect/5 := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along  ≤  0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6*kappa-1)*z  ≤  M/6+defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z  ≤  M/20+3*defect/10 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0  ≤  M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem robust_reflected_low_admissible (M xi defect short reflected z kappa : ℝ)
    (hd : 0  ≤  defect) (hreserve : xi+8*defect/5  ≤  M/15)
    (ht : reflected+short+z  ≤  23*M/30+xi+3*defect/5)
    (hc : reflected+short+6*kappa*z  ≤  14*M/15+xi+8*defect/5) :
    reflected+short+z  ≤  5*M/6 ∧ reflected+short+6*kappa*z  ≤  M := by
  constructor <;> linarith

theorem robust_deleted_cases (M total short along ell z kappa xi defect reflected : ℝ)
    (hM : 0  ≤  M) (hs : 0  ≤  short) (hsM : short  ≤  M/4)
    (hell : 0  ≤  ell) (hz : 0  ≤  z) (hze : z  ≤  ell) (hk : 37/50  ≤  kappa)
    (hxi : 0  ≤  xi) (hd : 0  ≤  defect)
    (hreserve : xi+8*defect/5  ≤  M/15)
    (hlarge : 5*M/6-defect  ≤  total+ell)
    (hcap : total+ell+(6*kappa-1)*ell  ≤  M)
    (halong : max 0 along  ≤  total-M/4)
    (href : reflected  ≤  max 0 (M-along+xi)) :
    (short+ max 0 along+z  ≤  5*M/6 ∧ short+ max 0 along+6*kappa*z  ≤  M) ∨
    (0 < along ∧ reflected+short+z  ≤  5*M/6 ∧
      reflected+short+6*kappa*z  ≤  M) := by
  obtain ⟨he,hbudget⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  by_cases hlo : short+ max 0 along+z  ≤  5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0  ≤  6*kappa)
    nlinarith
  · obtain ⟨hapos, ht, hc⟩ := robust_reflected_low M short along ell z kappa xi defect reflected
      hM hs hsM hell hz hze hk he hbudget hxi hd
      (robust_defect_le_width M xi defect hM hxi hreserve) (lt_of_not_ge hlo) href
    exact Or.inr ⟨hapos, robust_reflected_low_admissible M xi defect short reflected z kappa hd hreserve ht hc⟩

theorem robust_fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀M : ℝ, M₀  ≤  M →
      M₀/56+8*(M₀/56)/5  ≤  M/15 := by
  constructor
  · positivity
  · intro M hM
    linarith


end ZeroFree.PlainComparison
