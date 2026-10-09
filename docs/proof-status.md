# Formalization status and remaining arithmetic obligations

## Completed implications

The root is constructed by the intermediate value theorem. Its uniqueness,
strict isolation and every comparison use exact rational inequalities.

Q0 is exactly zero modulo the cubic. Lean verifies Q1 through Q4 are positive
and proves Q(y) >= 0 for all y >= 0. Square completion proves the continuous
quadratic inequality, and the positive denominator gives the reference endpoint.

Feedback follows an exact finite-difference identity for the rational count,
with positive denominators and a uniform coefficient bound. No derivative or
Lipschitz estimate is assumed. Main connects its parameter to kappaStar and
the certificate's polynomial inverse.

The generic continuation proves convergence and analyticity of an actual
Mellin integral, propagates a product identity, and obtains nonvanishing.
Family.SignalData records actual functions, integrability, decay, estimates,
multiplier control and the identity. No zero-free conclusion is a field.
The family proof uses the supremum with a 1/2 sentinel and does not assume
there is a zero at the supremum.

The standard facts for actual zeta are now proved, rather than supplied as
signal fields: its zero-real-part set is bounded by 1, its removed-pole
function is entire, its value at one is the proved residue, and its
regularizer is nonzero away from one.

HeightClosure chooses tau before N and proves that the raw estimate
C_N [x^(beta+c-m)(1+T)^A + x^B T^(-N)] gives error O(x^(beta+c-m/2)).
A and B are independent of N. The same m/2 works for a family even when
its constants, tau and N differ by member.

ZetaInverse constructs the principal signal explicitly as
x^c * mellinInv(-2, exp((s-5/6)^2) H(s)/zeta(s) reflected in s).
The reciprocal bound in Re(s)>=2 follows from the Moebius Dirichlet series.
Gaussian contour shifting proves arbitrary power decay at zero. Fourier
continuity proves local integrability. Mellin inversion and the identity
theorem prove the initial-half-plane product identity once the signal's
upper growth bound is derived from the low/raw-high probe estimates.

## Open obligation

`ZeroFree.ZetaSignalObligation` is a proposition, not an axiom declaration or
a proved theorem. It requires a bounded zero-real-part set and, under the
contradiction sigmaStar < beta, actual uniform signal data for Mathlib's zeta.
`riemannZeta_ne_zero_of_cubic_signal` takes it explicitly and excludes s = 1.

The sharper remaining input is
`ZeroFree.ZetaInverse.ArithmeticProbeObligation`: under sigmaStar < beta,
construct the analytic correction H close to 1 and an actual physical probe J,
prove its low bound, and prove the raw high estimate against the explicitly
constructed inverse Mellin signal. Integrability, decay, pole removal,
boundedness and the Mellin identity no longer need to be provided as fields.
It remains a proposition with no proved inhabitant. The theorem
`riemannZeta_ne_zero_of_arithmetic_probe` takes it explicitly.

An unconditional improved-region theorem still requires kernel-checked proofs of:

1. The plain-moment induction on 37/50 <= kappa <= 1, with the original moving
conductors, natural row-zero extensions, masks, coefficient classes and
uniform mesh chosen before the slot count. Existing upstream certificates
require kappa >= 3/4.
2. The flexible compensated probe for new lx, ly, h and e, its actual
reflected-energy estimate, and the complete Gram bound. Verified exponent
algebra provides only the numerical part of those estimates.
3. Actual detector counts, strict widths, local Euler convergence, principal
residues, prime normalizer and all physical small/middle/floor/outer estimates.
4. The physical probe and correction with their actual low/raw-high estimates.
For zeta, the principal signal, Mellin identity, and height/tail-order closure
are proved. Extending this construction to the intended Hecke family remains open.
5. Concrete finite-order Hecke-family instantiation, imprimitive factors and
quadratic Dirichlet transfer at the new boundary.

The paper's imported package R supplies the underlying written inputs. This
repository has not formalized its full package or proved
`R -> ZetaSignalObligation`. Conditional analytic theorems and unconditional
real algebra remain separately classified.

## Paper-to-code mapping

| Paper section | Formal coverage |
|---|---|
| Root and comparison | Boundary, complete. |
| Extended plain moment | Numerical budget/slack in Geometry; analytic induction open. |
| Inverse/plain counts | Rational envelope and feedback in Feedback; arithmetic realization open. |
| Probe and low estimate | Normalizer/margin algebra; actual reflected sums and Gram estimates open. |
| Continuous reference certificate | Certificate plus Main, complete for the stated envelope. |
| Actual parameter feedback | Feedback plus Main, complete. |
| Physical admission/Euler/outer rows | Exact margins/identities; convergence and arithmetic estimates open. |
| Uniform continuation | Mellin implication and family contradiction proved; actual zeta inverse signal, identity, origin decay and height closure proved; arithmetic probe estimates and the concrete Hecke family remain open. |

## Verification interpretation

`checked: true` in a build/replay record certifies only its listed declarations
with their complete types. Records leave
`complete_arithmetic_zero_free_proof: false` until the open input is constructed.
Analytic hypotheses are never hidden as global axioms. The historical Python
audit certifies displayed finite algebra and is outside the Lean proof.
