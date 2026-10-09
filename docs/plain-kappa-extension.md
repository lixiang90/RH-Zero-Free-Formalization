# Low-kappa plain-moment extension: checked terminal energy and remaining integration

The cubic boundary needs kappaStar < 3/4. Simply replacing a hypothesis
3/4 <= kappa by 37/50 <= kappa in the upstream certificate is invalid.
For example M=1, A=5/6, kappa=37/50 and z=25/516 satisfy
A+(6*kappa-1)*z=M, while z>M/21. Thus the original M/21 comparison
conclusion fails. Its reflected 16M/21 and affine 13M/14 budgets also need
new margins.

## Checked scalar repairs

ZeroFree/PlainComparison.lean contains the exact real comparison, reflected
branch and clipping-defect proofs extracted from the modified upstream chain.
They are checked by the primary Lean audit and independent Nano replay.
Their scope is scalar geometry with explicit budget and reflected-width inputs.
They do not prove the actual reflected-row estimates or the moment induction.

The safe replacements for kappa>=37/50 are:

| Quantity | Old comparison | New comparison |
|---|---|---|
| Slot exponent ell | M/21 | M/20 |
| Reflected total width | 16M/21+xi | 23M/30+xi |
| Reflected affine budget | 13M/14+xi | 14M/15+xi |
| Reserve | xi<=M/14 | xi<=M/15 |

With clipping defect d the new proofs give ell<=M/20+3d/10, total
width<=23M/30+xi+3d/5 and affine budget<=14M/15+xi+8d/5. The reserve
xi+8d/5<=M/15 admits either the original low branch or the reflected low
branch. The original fixed slack d=xi=M0/56 is still sufficient for M>=M0.
No kappa upper bound is needed in these scalar comparison lemmas.

## Actual upstream workcopy

The isolated, ignored workcopy uses the original upstream Lean 4.34.1 and
Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, with pinned external PNTA
and Rellich packages. It copies the exact local OAI import closure from
OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; the original checkout
is unchanged.

The modified chain keeps NaturalState, actual norm/logb reflection, moving
conductors, natural coefficient classes, masks, prime deletion, internalQ
restrictions and the 2*HeckeZeroSupremum.beta-1<=kappa premise. Its arithmetic
low branch bottoms out at the existing CanonicalLowPhysical kappa>=1/6
theorem. The comparison/defect margins above are propagated into actual
reference and reflected-row APIs. The old detector theorem with its fixed
2/27 conclusion is outside this plain extension and is not weakened.

The complete patched chain passed actual compilation. The final controller
record contains 2281 successful custom dependency modules and 37 targets,
with no failed or pending modules. A fresh four-root independent replay checks
actual_successor, certified_bands, terminal_certificate and certified_terminal.
The latter exposes actual ZeroAt/PositiveAt with its terminal CertifiedBand
premise; terminal_certificate constructs that band under the stated inputs.
Their complete printed types and transitive axioms retain the actual family
supremum and arithmetic data. Separate reflection, reference-state and low-branch
geometry scopes bring the independently selected upstream declarations to 22;
21 belong to modified modules and one to an unchanged upstream interface.
These are distinct from the 99 authored roots and from the primary library.
The primary 4.33.0-rc2 proof record does not certify these 4.34.1 targets.

The checked arithmetic low-kappa certificate must now be instantiated
with the actual Hecke-family supremum beta and a moving
kappa satisfying 2*beta-1<=kappa. In the contradiction beta>sigmaStar,
kappaStar=2*sigmaStar-1 cannot satisfy that premise. It is the reference point
for the cubic algebra and feedback; the arithmetic choice is kappa=2*beta-1
(or an explicitly budgeted larger value). The existing 7/8 family bound gives
the required moving range 37/50<=kappa<=3/4, where that bootstrap is supplied.
The new parameter lemma keeps beta<=7/8 explicit; it does not prove the
bootstrap. The original pinned FinalAssemblyUnconditional source does
construct the unconditional 7/8 arithmetic package; the historical source
audit identified an extra 711-module closure. The full bootstrap has not
been compiled or independently checked by this capsule.
The terminal certificate itself needs no kappa upper bound, while
some downstream detector-count branches do. A supremum of the single Riemann
zeta function cannot replace the Hecke-family supremum in this certificate.

The remaining integration must feed the checked terminal energy into the
actual marked moments and improved detector count. The finite-row construction
and its precise outstanding gates are described in
[finite-row-energy-integration.zh.md](finite-row-energy-integration.zh.md).

The current 41-module patch has SHA-256
`58ddc470f93afd26265525e78b951706ccb202839c6768f7ef39006af699dc42`.
Its final four proof-body repairs adapt existing stronger inputs to the
actual weaker API premises; declaration headers and inputs are preserved.
The original d18941bd revision and failed elaborations remain archived as
historical records. Exact source-preparation/build tools, separate
Rellich compatibility patches and local checkpoint records are in
[upstream/plain-kappa](../upstream/plain-kappa/README.md).
