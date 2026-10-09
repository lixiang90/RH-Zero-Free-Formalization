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

Two small modules were ported with provenance and the upstream Apache-2.0 license:

- ZeroFree/UpstreamSupremum.lean adapts the source Supremum.lean.
- ZeroFree/Continuation.lean adapts the source Continuation.lean.

Their source hashes, revisions, and exact changes are recorded in
verification/upstream-port-provenance.json. The changes are namespace,
import path, provenance notice, and the compatibility replacement of the
newer Complex.isOpen_re_gt helper by its proof from continuity of real part. The originals remain unchanged.
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

This verifies the continuation implication; constructing the arithmetic
signal, proving its estimates, and matching its identity to the intended Hecke
or zeta function remain separate obligations.

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

Both ported modules successfully built with lake build
ZeroFree.UpstreamSupremum ZeroFree.Continuation in the local pinned
environment. A fresh Lean import audited seven exported dependency roots,
including Mellin convergence, Mellin analyticity, product-identity propagation,
and nonzero_of_regularized_signal. It returned exit code 0 in 10.288 seconds
and reported only propext, Quot.sound, and Classical.choice. The records are
verification/analytic-continuation-check.json and
verification/analytic-continuation-axiom-audit.log.
No independent replay of this port was performed in this audit.
