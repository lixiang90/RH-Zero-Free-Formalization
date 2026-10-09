# Concrete zeta signal review — 2026-10-09

A separate read-only review inspected HeightClosure, ZetaConcrete,
ContinuationInversion, ContinuationContour, ZetaInverse and ZetaSignal.
It found no substantive type, normalization, circularity or scope issue.
This internal review is separate from external peer review.

The normalization x^c, reflection s -> -s in mellinInv(-2, amplitude(-s)),
and the contour factor 1/(2*pi) are consistent. The paper's affine prime
normalizer C_b(s)=s-2/3-b/6 has slope one, matching the code's s+c.

The removed-pole function uses the actual residue of Mathlib's zeta.
Its zero-real-part set is bounded independently of the new conjectured
boundary. The principal signal is an explicit integral using actual zeta,
rather than a freely supplied function or an opaque L-function.

HeightClosure fixes A, B and tau0 before all tail orders N, selects a positive
tau from m, A and tau0, then selects N from tau, B and the target exponent.
Constants and eventual thresholds may depend on N. This order matches the
uniform continuation part of the cubic paper. The same m/2 remains valid
for a family even if individual constants and cutoffs vary.

ProbeData.toRawSignal derives the signal growth bound, local integrability,
origin decay and initial product identity. The continuation argument retains
the same correction and probe throughout. There is no nonzero conclusion
among the ProbeData fields and no circular height choice.

The unresolved input is the actual arithmetic construction of H and J,
including their low bound and raw high estimate. Those require the low-kappa
moment induction and new Gram, detector and compensated physical estimates.
The reviewed theorem remains explicitly conditional on ArithmeticProbeObligation.
