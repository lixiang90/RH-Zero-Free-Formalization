# Actual arithmetic development for the cubic boundary

This directory contains the separately pinned Lean development that connects
our cubic boundary to the actual Hecke arithmetic in OpenAI/math. Author:
**Li Xiang / lixiang90**. It is independent of the primary Lean 4.33.0-rc2
library, and its results are counted separately.

**The complete improved zero-free region is still pending.** The checked slot
constructor below is an actual arithmetic interface. The other new sources
are frozen for review and reproduction while their dependency builds continue.
An intermediate compile or source-preparation pass does not prove the complete
moment certificate or the final zero-free half-plane.

## Mathematical scope

The [41-module patch](reviewed-pending.patch) propagates a plain-moment floor
of kappa >= 37/50 through the original reflected and clipping budgets. It keeps
the actual Hecke polynomials, natural coefficients, masks, prime deletions,
moving conductors and the premise 2*HeckeZeroSupremum.beta-1 <= kappa.
The scalar repairs and their scope are described in
[plain-kappa-extension.md](../../docs/plain-kappa-extension.md).
The patch SHA-256 is
`d18941bdb3a32f42032c5e82c6518baa5dc03968ff8af652ca30d62d6467566e`.

The [authored-source manifest](extensions/manifest.json) records eleven extra
modules separately from those patched upstream sources. Each has an exact
source hash, declaration list and verification status.

| Interface | What the source proves | Current verification |
|---|---|---|
| ParametersSlotLengthsLowKappa | Distinct positive Fin N slot lengths with any positive total, chosen after the mesh and physical range; a uniform positive lower ratio. | 2 roots passed actual compilation, fresh complete types/axioms and independent Nano replay. |
| LowKappaParameters | Bind the moving moment parameter to the actual Hecke-family supremum. The old family bound beta <= 7/8 stays explicit. | 7 roots prepared; actual target verification pending. |
| GlobalRegionLowKappa and GlobalCorrectionLowKappa | Extend the original local/global Euler correction to Re x >= 21/25, retaining the same summable 240 Q^(-17/10) majorant. | 15 roots prepared; actual target verification pending. |
| GlobalSourceCorrectionExistenceLowKappa | Choose one finite excluded set before every character and every later half-plane threshold. No L-function zero-free premise. | 2 roots prepared; actual target verification pending. |
| Hecke.DirichletLowKappa | Apply the existing actual factorization to transfer an explicit whole-family nonvanishing hypothesis to Dirichlet functions and zeta at any positive threshold. | 2 roots prepared; actual target verification pending. |
| PrincipalSignalScalingLowKappa | Normalize the actual Hecke sourceMultiplier and sourceResidueIntegral at variable total ell and imbalance b; derive the nonzero normalizer from positive windows and slot masses. | 5 roots prepared; actual target verification pending. |
| LowSourceScalesLowKappa | Bound the actual compensated lowGramFactor with exponent (1-ell)/4-b/6 and derive the actual physical scale q Z^(1-ell)/L^2. | 9 roots prepared; actual target verification pending. |
| PrimeRows.CubeNormalizerLowKappa | Prove the actual positive ray-prime normalizer nonzero and its inverse bounded by every positive power, using the actual slot sum. | 1 root prepared; actual target verification pending. |
| PrincipalSlotEstimateLowKappa and PrincipalSignalComparisonLowKappa | Bound the original marked slots and weighted slotRatio on Re s >= 21/25, with error 1440 Q^(-21/25); prove correction denominators nonzero and the original slotRatio analytic. | 24 roots prepared, including the explicit bounds structure; actual target verification pending. |

The widened Euler domain is a domain for the **correction factor**, not a
zero-free region for an L-function. The sixfold Mellin pole remains z=1/6,
independently of the variable total slot length. The whole-family hypothesis
in the transfer lemmas and the physical low/high estimates are not supplied by
these identities. See [arithmetic-integration.md](../../docs/arithmetic-integration.md)
for the parameter meanings and remaining interfaces.

## Checked evidence

The slot constructor's fresh audit and serial independent replay checked
**8,647 transitive declarations** from its two roots. The source, configuration,
compiled artifacts and selected build records remained unchanged throughout.
See [slots-total2/strict-replay-result.json](verification/slots-total2/strict-replay-result.json).

All **11 Rellich compatibility patches** also passed real compilation, fresh
types and counted axiom audits, followed by a new independent replay of
**45,863 transitive declarations from 54 roots**. They preserve the mathematical
statements. One original local instance with uninferable proof parameters is
now a same-name lemma, with explicit instances at its two consumers; this
registration change is recorded rather than hidden.
The [compatibility manifest](compat/manifest.json),
[declaration-header comparison](verification/rellich-header-preservation-audit.json)
and [final54 replay](verification/rellich-final54/strict-replay-result.json)
bind the exact sources and checks. The only permitted axioms are `propext`,
`Quot.sound` and `Classical.choice`.

These two replay scopes overlap in foundational declarations and must not be
added together. Neither is a replay of ReflectionRetainedLength,
Energy.CertifiedExistence or the whole improved zero-free theorem.
The [latest frozen build snapshot](verification/latest-actual-module-status.json)
records actual process exits; the two full arithmetic targets remain pending.
Earlier records under verification/ retain their original, narrower scopes.

## Pinned sources and tools

| Component | Pin |
|---|---|
| OpenAI/math | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| Lean | `leanprover/lean4:v4.34.1` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Rellich-Kondrachov | `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` |
| PrimeNumberTheoremAnd | `c39a751132c88b6e8080b74c74023fd95b3d8be0` |
| lean4export | `b18d673bd29b476466a51a3be1012df2ed322b10`, built with Lean 4.34.1 |
| Nano | `418320295890faed83a96fd97907b12a3b6728c2`, serial replay |

The [Lake manifest](template/lake-manifest.json) fixes the full dependency
versions. Original OAI files are read from pinned Git blobs. Authored modules
are explicitly labelled `authored_extension` and have no fabricated upstream
Git baseline. Source preparation checks every patch and rejects unlisted
changes or missing custom imports. The original math checkout is unchanged.

## Reproduction

With Elan, Python 3.10+ and a clone containing the pinned math commit, run from
this directory, choosing a new empty destination:

```sh
python prepare_low_kappa_capsule.py --source /path/to/math --destination /new/empty/plain-project --patch-manifest manifest.json --external-compat-manifest compat/manifest.json --extension-manifest extensions/manifest.json --install --build --jobs 4
```

For a public partial clone at an absent source path, add `--fetch`. Omit
`--install --build` to verify source reconstruction only. The recorded fixtures
under verification/ distinguish this preparation pass from a proof check.

The default `--jobs 1` is serial. Bounds of 2, 4 or 8 run that many Lean child
processes at most, with two Lean threads each. There must be one source-build
controller for a project. It checks source/dependency fingerprints and artifact
hashes, drains current tasks after a failure, and supports
`.serial-build/stop-after-current.flag` for a safe checkpoint. Existing successes
are reused only when their bindings still match.

After a selected target has compiled, the
[kernel replay runner](kernel-tools/run_upstream_nanoda.py) checks its actual
custom dependency closure, freshly prints `#check @` types and transitive
axioms for every selected root, and invokes the pinned exporter and serial
Nano. It requires the Lean 4.34.1 exporter; the primary project's 4.33 exporter
is a different toolchain. Its commands and byte bindings are retained in each
strict replay record and in
[kernel-toolchain-provenance.json](kernel-tools/kernel-toolchain-provenance.json).
All stages must pass for a target to be labelled independently verified.

The upstream OAI Apache-2.0 license is preserved at
[third_party/OAI-LICENSE](../../third_party/OAI-LICENSE); the external package
license is [Rellich-LICENSE](licenses/Rellich-LICENSE).
