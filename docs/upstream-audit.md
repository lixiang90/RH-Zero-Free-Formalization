# Upstream analytic-source audit

The upstream source is [OpenAI/math](https://github.com/openai/math), inspected at
commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its complete library is pinned to
Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

## Actual upstream theorem and static scope

The solution module OAI.NumberTheory.DirichletL.Nonvanishing gives statements
about mathlib's actual riemannZeta and DirichletCharacter.LFunction, with the
principal pole excluded in the Dirichlet statement. It imports Foundation and
Detector.FinalAssemblyUnconditional. The latter derives a CertifiedBand
from actual moment/energy interfaces and assembles the fixed seven-eighths
boundary. Hecke characters are concrete residue characters over the ring of
integers of CyclotomicField 3 Q; their L-functions are not opaque substitutes.

The Nonvanishing module's recursively followed local OAI import closure
contains 2,924 modules and 25,009,201 raw UTF-8 bytes. A line-by-line token scan
found no occurrences of sorry, admit, axiom, unsafe, or native_decide in that
closure. The Comparator challenge files do contain intentional sorry
placeholders, and are not the solution graph.

This is a static source inspection, not a successful compilation, a transitive
kernel axiom audit, or an independent replay of the complete upstream theorem.
The inspected math/lean checkout has no .lake directory. The original paper's
source revision adc7f1241b42e322a6451854ab7e4b4c146bf78a is preserved in the
papers; it must not be silently identified with the newer inspected revision.

## Reused analytic proof

The following modules are ported with provenance and the upstream Apache-2.0 license:

- ZeroFree/UpstreamSupremum.lean adapts the source Supremum.lean.
- ZeroFree/Continuation.lean adapts the source Continuation.lean.
- ZeroFree/ContinuationInversion.lean adapts the actual Mellin/Fourier inversion proof.
- ZeroFree/ContinuationContour.lean adapts the Gaussian contour-shift proof.
- ZeroFree/ZetaInverse.lean specializes Hecke/Signal.lean to actual Mathlib zeta,
  with the reciprocal bound proved from the Moebius Dirichlet series.
- ZeroFree/ZetaSignal.lean specializes Hecke/SignalIdentity.lean, then derives the
  product identity from the constructed signal and the proved height closure.

- ZeroFree/SourceScaling.lean generalizes the actual complex-power identity in
  PrincipalSignalComparison to variable total slot length and scale imbalance,
  retains the sixfold Mellin pole, and matches the constructed zeta amplitude.

Their source hashes, revisions, and exact changes are recorded in
verification/upstream-port-provenance.json. The generic inversion/contour proofs change namespace and imports.
The zeta specialization replaces the character by riemannZeta, proves a
uniform reciprocal bound in Re(s)>=2 from its Moebius series, and changes
the correction domain to sigmaStar. One endpoint rearrangement uses simp
instead of the upstream convert/ring tactic. Half-plane openness is proved
from continuity of real part for compatibility. The originals remain unchanged.
The local build uses Lean 4.33.0-rc2 and mathlib
51e6992efd06126df61a496bebf8f49482a4e129, so it must be compiled here rather than
assumed compatible from the upstream toolchain.

The key theorem is ZeroFree.Continuation.nonzero_of_regularized_signal.
It accepts a variable real boundary a, actual complex functions L, Lregular, R
and W, and an actual real-to-complex signal f. From analyticity on a < Re(s),
local integrability, rapid decay at zero, the power bound on f, an identity
Lregular * signalMellin(f) = R * W on the initial half-plane, and nonzero
regularizer and multiplier, it proves L(rho) != 0. Its proof establishes actual
Mellin convergence and analyticity, propagates the product identity by analytic
uniqueness, and derives the nonvanishing contradiction. It introduces no
analytic axiom. The remaining seven-eighths wrappers keep their original scope.

For zeta the principal signal is now constructed as an actual inverse Mellin
integral. Gaussian contour shifting proves rapid decay at zero; Fourier
continuity proves local integrability. Mellin/Fourier inversion and analytic
uniqueness prove its identity on the initial half-plane. Only the arithmetic
correction and physical probe with their low/raw-high estimates remain as
ZetaInverse.ArithmeticProbeObligation. The analogous concrete Hecke-family
construction at the improved boundary is still pending.

## Why the improved boundary is not an upstream corollary

The improved paper uses kappa at or just above 2 beta - 1. At its proposed
boundary this is about 0.74991403884, below 3/4. The upstream generic plain
terminal certificate, CappedAnalyticSuccessor, CappedLowStage, and
NaturalHighStage each retain the hypothesis 3/4 <= kappa. They cannot simply
be applied at the new value. The proposed range 37/50 <= kappa requires its own
formal derivation from the underlying estimates.

In addition, Parameters.HighData, FinalAssemblyChosenData, Hecke.CommonProbe,
and Hecke.SignalIdentity embed the fixed 7/8 boundary and fixed physical
budgets. The new flexible geometry is not exposed as a generic theorem.
The concrete Hecke transfer/primitive-supremum/signal dependency closures each
contain over 300 modules (about 9.4 MB), while the generic Continuation closure
contains only two OAI modules. Reusing the generic continuation is therefore
practical, but does not by itself complete the improved arithmetic proof.

The repository's public status must distinguish the exact algebra and analytic
continuation proved here from these remaining arithmetic hypotheses.

## Local verification of the port

Every public theorem in these ports is included in the complete fresh library
build and axiom audit, and in the independent serial Nano replay. The current
records are verification/lean-verification.json and
verification/independent-kernel.json. The old analytic-continuation-check.json
records only the initial two-module audit and is preserved as history.

The standalone upstream Lean 4.34.1 workcopy is separate. Its low-kappa patches
are not imported into the checked 4.33.0-rc2 library. Actual upstream moment
compilation and its fresh dependency audit must pass before that range
extension is reported as a proved arithmetic input.
