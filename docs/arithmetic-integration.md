# Arithmetic integration: parameters and remaining interfaces

The primary library checks the cubic algebra, feedback and the constructed
zeta inverse Mellin signal. The separately pinned 4.34.1 development connects
these to actual Hecke arithmetic. An intermediate target pass certifies its
stated mathematical objects and hypotheses; it does not establish the complete
improved zero-free region.

## Distinct quantities

| Quantity | Meaning and required use |
|---|---|
| HeckeZeroSupremum.beta | Supremum for the full actual finite-order Hecke family. The moment certificate uses this object, not the zero supremum of a single zeta function. |
| plain moment kappa | Use 2*beta-1 in the contradiction beta>sigmaStar. kappaStar=2*sigmaStar-1 is the reference for algebra and feedback. |
| Parameters.HighData.kappa | A small detector error scale (the original Lean field is κ). Its phase/error budgets are unrelated to the plain moment parameter. |
| DetectorRawFiber.Moments parameter kappa | The inverse-amplification loss in inverse_raw. The current plain_marked field uses a separately fixed 3/4+2*Delta. It does not inherit this parameter. |
| total slot exponent | The sum of finitely many distinct positive slot lengths; this changes from 1/6 to ellStar. Mesh and physical range are chosen before the slot count. |
| sixfold Mellin pole | The evaluation z=1/6 in the actual source double residue remains fixed. It is not the total slot exponent. |

The new LowKappaParameters module binds the moving parameter to the actual
Hecke supremum. It retains the old family bound beta<=7/8 explicitly wherever
kappa<=3/4 is needed; that bound is not inferred from a zeta-only theorem.

## Principal normalization

Let lx=(1-ell-b)/2, ly=(1-ell+b)/2 and h=(1+3*ell+b)/2.
The actual double residue supplies X^(1/3)*Z^(s-5/6) at X=Z^lx.
The slot normalizer supplies Z^(-ell/6). Their quotient has exponent

    s+c,  c=lx/3-5/6+ell/6=lx/2-1+h/6=-(4+b)/6.

SourceScaling proves the complex-power identity and its equality with the
constructed zeta amplitude. The resulting low exponent at the cubic parameters
is sigmaStar+c=(1-ellStar)/4-bStar/6. The actual PrincipalSignalScalingLowKappa source generalizes sourceMultiplier
and sourceResidueIntegral with this same shift. It uses the existing positive
window theorem and positive actual slot masses to prove the complete scalar
normalizer nonzero. Its five roots passed actual compilation, fresh complete
types/axioms and the strict 49-root independent replay.

## Actual correction and physical probe

GlobalRegionLowKappa and GlobalCorrectionLowKappa prove statements about the original
unramifiedClosed, globalClosedCorrection and sourceCorrection objects.
Their mathematical proof keeps the same CorrectionTail S and the majorant
240*Q^(-17/10), and widens the sufficient x-domain to Re x>21/25.
The other coordinates retain Re w>=9/10 and Re z>=4/25. This is a correction
estimate, not a zero-free region for an L-function. Along with
GlobalSourceCorrectionExistenceLowKappa, these 17 roots passed actual Lean
compilation, fresh complete types and standard-axiom checks, then a strict
independent Nano replay. The latter chooses one finite excluded set before
all characters and all later half-plane thresholds. Exact evidence belongs
in the separate [Euler replay](../upstream/plain-kappa/verification/euler17/strict-replay-result.json).

The verified arbitrary-total slot constructor preserves the required mesh
and physical-range quantifier order. LowSourceScalesLowKappa additionally
derives the actual lowGramFactor exponent (1-ell)/4-b/6, uniformly over L and
delta after an eventual height threshold; its sufficient geometry is b>0 and
3*ell+3*b<1. Its nine roots passed actual compilation, fresh complete
types/axioms and independent Nano replay. This factor estimate still requires
the full reflected-energy sum to obtain the low physical-probe estimate.

CubeNormalizerLowKappa removes the fixed-total specialization of the actual
ray-prime normalizer inverse subpower theorem. The underlying positive mass
and prime distribution theorems are the original arithmetic ones. The new
principal-slot modules likewise retain the original marked and weighted slot
functions, widening their sufficient domain to Re s>=21/25 and changing their
error to 1440 Q^(-21/25). Their stricter smallness condition is retained, and
correction-denominator nonvanishing is not mistaken for a single slot being
nonzero. The 24 principal-slot roots passed actual compilation, fresh
complete types/axioms and the strict 49-root independent replay. The actual
ray-prime inverse has its own verification record, including the PNT leaf
dependencies; neither assertion supplies the missing physical estimates.

The remaining integration must supply these actual interfaces:

1. Complete the low-kappa terminal CertifiedBand induction with moving
   conductors, natural coefficients, masks, row-zero extensions and mesh order.
2. Generalize the physical low probe from the fixed lx=17/48, ly=23/48
   and total slots=1/6 to the paper's parameters, proving the reflected-energy
   and Gram estimates for actual sums.
3. Construct actual marked moments at plain kappa=2*beta-1. The legacy raw
   fiber field uses 3/4+2*Delta and denominators 9/2+12*Delta; the generalized
   capacity denominator is 6*kappa. A bound on an abstract count envelope
   does not supply these marked moments.
4. Assemble detector counts, principal residue/normalizer, low and raw-high
   physical estimates with the quantifier order used by HeightClosure.
5. Instantiate the Hecke-family continuation. The upstream already proves the
   actual Hecke/Dirichlet product factorization; DirichletLowKappa generalizes
   its wrapper threshold with an explicit whole-family nonvanishing premise.
   Supplying that premise is the remaining issue, not a new factorization
   theorem. ArithmeticProbeObligation remains open until this is done.

## The marked-count gate

The existing DetectorPlainFiberCount.plain_fiber_count already accepts an
independent nonnegative kappaPlain. Its raw input is a bound for the actual
squared marked polynomial/physical product sum under

    2*m + 6*kappaPlain*sum(widths) <= 1.

The first integration gate is to derive that actual marked sum from the
terminal energy certificate, with kappaPlain=kappaTerminal plus the explicitly
budgeted padding. The current Moments record takes the sum estimate as a field.
Its kappa parameter enters inverse_raw, while plain_marked fixes kappaPlain
at 3/4+2*Delta. The downstream count-parameter constructors consume a supplied
Moments record.

The dependency order for the improved count is:

1. Supply the actual marked square sum at the moving terminal kappa.
2. Reuse the existing generic plain_fiber_count theorem.
3. Generalize RawBranches and BranchBudget to denominator 6*kappaPlain.
4. Generalize CountFromMoments, RowCountOptimization and RowCountCrossing,
   preserving the same actual row sets and the requested-capacity premises.
5. Assemble the adaptive/batch counts with the actual physical probe estimates.

The legacy downstream chain retains denominator 9/2+12*Delta and a 2/9
reference; its plainExponent also contains 4*x/9 and 8*x/9. All of these must
move together to obtain the paper's improvement. The small detector budget
D.kappa (bounded by 1/16000 in HighData) and the inverse-amplification loss
cannot serve as the terminal growth parameter 2*HeckeZeroSupremum.beta-1.

The generic fiber count requires only kappaPlain>=0. The legacy optimization's
zero-capacity branch additionally uses kappaPlain<=1, obtained from
Delta<=1/8 and kappaPlain=3/4+2*Delta. For the moving terminal parameter,
kappaTerminal<=1 alone does not imply kappaTerminal+padding<=1. This branch
needs an actual bootstrap/margin, or a revised error coefficient with its own
proved upper bound.

The [source-level marked-moment audit](marked-moment-audit/README.md) identifies
an exact finite-row dictionary and a direct radial-energy route. The canonical
central rowBand already supplies rowNorm>=Z^(1/100); its generic Batch
consumers do not construct the required canonical Batch. The new ray
coefficient identity removes the restriction to the trivial ray character.
The remaining bridge must prove the radial domination, source/mask geometry,
full capacity coverage and a uniform height-loss budget before it can supply
plain_marked. The inverse_raw, inverse_marked and plain_unmarked fields also
remain separate requirements of a complete Moments record.
