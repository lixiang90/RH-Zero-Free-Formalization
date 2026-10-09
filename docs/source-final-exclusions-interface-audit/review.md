# Final exclusions, product ideal, and source-after-slots review

This is a read-only review, with zero new Lean roots and no Lean/controller/export
run. The new SourceAfterSlots and LossesBeforeArithmetic candidates remain
prepared proofs pending their own canonical compilation and independent replay.

The source-after-slots mathematical type and body are accepted. Their order is

    fixed W/scalar geometry -> rho/epsilonE -> energy mesh -> N/ell/slotLower
      -> any positive detector e and prime seed S0 -> final S
      -> product ideal M / ray subgroup H -> native degree/J/tau
      -> outer eta -> positive constant/eventual range
      -> all smaller allowed heights / all matching Batch records and fibers.

## Exact existing source constructor

`OAI.SevenEighths.Parameters.exists_fixed_source`,
`ParametersFixedSource.lean:26`, has the original pinned signature

```lean
theorem exists_fixed_source (e : ℝ) (he : 0<e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀P∈S₀,Prime P) :
    ∃ S : Finset (Ideal O), S₀⊆S ∧ SourceExclusions S ∧
      FirstTail (4*e) S ∧ (∀P∈S,P.IsMaximal)
```

It internally enlarges the seed by fixedBadPrimes. Thus the caller need only
prove seed primality; it need not already put every bad prime in the seed.
The empty prime seed is also valid. The returned SourceExclusions fields are
`prime`, `bad`, and `tail` (`Detector/SourceExclusions.lean:24`). Therefore
`hS := hExclusions.prime` and `hbad := hExclusions.bad` are the exact source
dictionary gates. The returned maximality is additional genuine information.

The more primitive constructor is
`OAI.SevenEighths.ProbeHighRowFamily.exists_both_source_exclusions`
(`PrimeRows/FirstTail.lean:81`): its positive parameter is eps, and its input
seed must already contain fixedBadPrimes. It returns SourceExclusions S and
FirstTail eps S by taking the maximum of a global prime-norm cutoff and the
eps-dependent first-tail cutoff. `exists_fixed_source` invokes it with eps=4e.

`FirstTail eps S` stores positive eps, norm_four, and the actual excluded-prime
sum of `240*norm(P)^(-1-min eps (1/50))` at most 1/6. Thus the new e parameter
is the actual first-tail/detector parameter, not native energy epsilonE.

## Exact product, row-mask, quotient, and subgroup gates

The actual original lemma is
`OAI.SevenEighths.ProbePhysical.fixedPrimeProduct_ne_zero`
(`Detector/FixedEuler.lean:14`):

```lean
lemma fixedPrimeProduct_ne_zero (S : Finset Id) (hS : ∀P∈S,Prime P) :
    (∏P∈S,P)≠0
```

Its proof uses every factor's `Prime.ne_zero`. This exact signature is identical
in the original pin. No existing `source_product_ne_zero` alias was found in
the inspected actual OAI source or private Lean candidates.

After final S is selected, let M be its product and install
`NeZero M` from that lemma. The product equality is `hM : M=∏P∈S,P`, with proof
`rfl` when M is this definition. It is distinct from the actual native gate
`hMm : M ≤ Ideal.span {ProbeHighRowFamily.rowMaskElement}`.

The latter follows by rewriting hM and calling
`OAI.SevenEighths.CenteredMomentDetectorDictionary.source_product_le_rowMask S hbad`
(`Moments/DetectorDictionarySource.lean:16`). Its only input gate is bad-prime
inclusion; its proof identifies the product of the two fixed bad-prime ideals
with the row-mask ideal and uses divisibility of the finite subproduct.

With `[NeZero M]`, the actual quotient instance is
`Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)`. A concrete subgroup is
`H=⊤`, and the native gate
`hH : RayOrthogonality.globalUnits M ≤ H` follows from `le_top`.

`GenericSourceIdealAndMesh.source_fixed_ideal_gates M S hS hbad hM` then gives
Q0=M inf span{72} nonzero/proper/Q0≤M and, for every actual character, internalQ
nonzero/proper/internalQ≤span{72}/internalQ≤character modulus. It does not need
a supplied HighData or source maximality proof.

In the new second theorem the result quantifies every `[NeZero M]` with hM
equal to the already chosen product. This is a genuine nonvacuous interface:
the theorem also outputs product≠0, so a caller can define this product M,
construct its NeZero instance, and instantiate H=top. An extra existential
M is unnecessary. The same S/hS is retained in SourcePlainMarkedAt.

## W and the final correction

`Parameters.exists_fixed_probe_window` (`ParametersFixedSource.lean:39`) has
no input parameters. It supplies real w, SchwartzMap W, smoothness and compact
support of w, support(w) within (1,2), positive tsupport, 0≤w≤1, w≠0,
complex equality, W≠0, support(W) within [1,2], and real/nonnegative W values.
Thus it can be chosen before losses/slots/e/S. The wrapper takes its coerced
W with aslot=1 and bslot=2. In the actual Mathlib SchwartzSpace/Basic.lean:82,
`W.smooth'` gives the required `ContDiff ℝ ∞ W`; `W.contDiff` is not the
method name used by this structure. Source W differs from Euler correction w=1.

After the final S is selected, the checked
`PrincipalSignalComparison.sourceCorrection_analytic_lowKappa` and
`sourceCorrection_bound_lowKappa` accept its SourceExclusions proof directly.
Their respective domains are Re>21/25 and Re≥21/25; their functions are the
same actual sourceCorrection with this final S. There is no need to keep the
S chosen by an earlier existence theorem or identify correction functions
from different excluded sets.

## New prepared candidate and remaining boundary

The reviewed SourceAfterSlots source has SHA256
`acc66a3ec52d43e0d574d03a2ed97530ae90d6aa1c393ddbfc9062f21c28fecf`.
Its first root obtains scalar losses before all M/H/S and constructs actual
physical slots with both physical mesh and absolute energy mesh bounds. Its
second root (lines173–212) places every positive e and prime seed after these
slots, invokes the original exists_fixed_source, and keeps its actual FirstTail,
SourceExclusions, maximality and product-nonzero evidence before native degrees.
The stronger native candidate chooses rho=min(rho0,(Mcap-dmax)/2) and epsilonE
before introducing M/H; it does not interchange old existential quantifiers.

All mathematical gates remain explicit: positive scalar geometry/loss/slot
mesh, dmax<Mcap, dmax/2≤L, κEnergy≥37/50, κEnergy≤κPlain,
beta≥51/100, 2beta-1≤κEnergy, row-norm lower bounds, source dictionary matching,
external real part17/50, external and test height bounds, absolute slot mesh,
and the actual marked capacity. Mcap is a real width cap; M is an ideal.

The `∀e>0` after-slots interface suffices for this FirstTail integration order:
after choosing a genuine detector e from slot-dependent budgets, specialize it
at that e. It does not choose e or verify its other detector budgets. The
original HighData also stores ε/κ/cost/eps/sigma, detector/phase/count/central/
geometric/principal/window/floor/high-saving/height-choice proofs, and fixed
total ell=1/6. These are not constructed by the new theorem's arbitrary
positive-total slots or by e positivity. Native energy epsilonE, detector e,
detector ε and floor eps remain distinct. No complete HighData, unmarked field,
inverse fields, full Moments/RawMomentInput, moving count or zero-free result
is asserted by this review.
