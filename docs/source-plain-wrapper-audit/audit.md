# Minimal actual source-specific moving plain-marked wrapper

This read-only ledger audits the source interface for the next wrapper. It does
not add a source module, build target or proof of complete Moments. Pinned
upstream import nodes and the actual source-state snapshot are bound in
`closures.json`; the newly prepared three-module phase remains separately
pending its canonical checks.

## Exact wrapper scope

Keep the outer generic source parameters M/H/hH, a finite source exclusion set
S/hS, fixed η, positive ell:FinN→R, common actual W/bslot, and scalar geometry.
Define the fixed finite label map

    ηlabel = sourceMomentBase M H hH S hS η
    Label = Sum Bool (RayQuotient.Characters M H).

Use the actual eventual finite-family theorem with this map and fixed Qlabel,
then prove for every q, matching actual source Batch B, bin/label/left/right
and every nonempty-fiber proof the **one actual moving plain-marked field**.
The finite maps are fixed before Z and before B. The current fixed-family root
does not place the degree before every outer η; that requires the separately
prepared native UniformDegreePositiveAt primitive and a genuine new assembly.

The q/cutoff, a/epsilon/tstar/T/allowance/i are already universally variable in
the actual eventual field theorem. There is no new q-specific or witness-zero
estimate. All matching B are covered by rewriting actual fiber fields, not by
selecting one constructor witness and pretending it covers all B.

`SourceMomentsAt` itself, in PrimeRows/NonfloorMoments.lean:15, requires all q,
all matching source B and all nonempty fibers to satisfy the entire four-field
Moments record. A one-field wrapper should introduce a separate explicit
`SourcePlainMarkedAt`/`PlainMarkedAt` interface, retaining the exact actual
polynomial sum and capacity with κPlain. It need not import NonfloorMoments or
its count dependencies merely to state this one field.

## Field-by-field admission dictionary

| Actual gate | Minimal existing source or proof step |
|---|---|
| Fiber.rows⊆B.rows | Batch.fiberRows is DetectorFiberPartition.fiber, a rows.filter; Finset.mem_filter.mp hu gives the original B.rows membership. No special arithmetic lemma is needed. |
| Fiber.label=label, Fiber.rowData=B.data label | Batch.fiber/toFiber definitions, Hecke/DetectorBatch.lean:46 and DetectorFiberPartition.toFiber:62. |
| Fiber.rowData=momentData(ηlabel label) | Rewrite B.data=sourceMomentData, then DetectorDictionarySource.sourceMomentData_base, line43. The exact map is sourceMomentBase at line38. |
| Row lower Z^rmin | Fiber.rows⊆B.rows⊆outer rows and the outer lower condition; rowNorm is exactly the absNorm of the row ideal, PrimeRows/RowPartition.lean:13. |
| Row upper U=Z^d | Actual Fiber.row_norm is inherited from Batch.row_norm. It is already part of a real Batch/Fiber, not a proposed extra numerical envelope. |
| Common profile W | Fiber.profile=B.profile definitionally; rewrite B.profile=(fun _=>W). A common W is needed, not arbitrary profiles varying by slot. |
| Common upper bslot | Fiber.upper=B.upper definitionally; rewrite B.upper=constant bslot. The Fiber type has no equality of upper parameters. |
| Absolute native slot length | Fiber.widths=B.widths; B.widths=(fun s=>ell s/d), d>0. Prove d*(ell/d)=ell. Thus require ell≤fineMesh Mcap0LκEnergyεE. The Batch mesh bound alone is not this native gate. |
| Real external slot exponent | Fiber.external=B.external definitionally; constant external z and z.re=17/50 give native 1-Re=33/50. No conjugate/time sign is changed. |
| External frequency | B.external=constant z and |z.im|≤height give |-Im Fiber.external|≤height by abs_neg. The actual witness.zero is unrelated. |
| Test frequency | t∈[-height,height] gives |t|≤height independently of the external frequency. |
| Actual prime coprimality | DetectorDictionarySource.eventually_source_slots_coprime, line50, for all finite labels/slots, all d≠0 and all W supported in Ici a>0. It uses ell>0 and (Z^d)^(ell/d)=Z^ell, not sum ell=1/6. |
| M≤span rowMaskElement | source_product_le_rowMask, DetectorDictionarySource.lean:16, with bad-prime subset and M=product S. |
| Fixed ideal Qlabel | For old SourceData, NaturalFixedRaySourceFixedIdeal.sourceFixedIdeal=M inf span72, line16, and its nonzero/non-top/modulus/72 lemmas, lines19/23/35/36. For a generic source S, use the same actual ideal but prove the small generic gates without constructing old HighData/SourceData. |

`NaturalFixedRaySourceBatch.eventually_source_batch_plain_sectors`, line20,
already exhibits the rowData rewrite and uniform prime gate for all matching
actual B, all bins/fibers. Its core only needs M=product S, fixed bad primes,
positive ell and source support in Ici1. Its SourceData wrapper at line56 uses
the old data geometry. The new one-field wrapper can use the core lemmas
directly and the new direct actual fiber bridge; it does not need to retain
that older sector inequality as a numerical hypothesis.

The source family equality and source reverse equality in SourceMomentsAt
remain source-identification conditions of that complete interface. The new
one-field proof uses the real Fiber.row_coeff and real F.reverse already
inside F; it need not assume an additional equality of family coefficients.

## Small generic fixed-ideal proof still to write

For a generic source with M=product S and S including the bad prime ideal
span(goodLambda), choose Q0=M inf span72 and Qlabel=constant Q0. Q0≤M and Q0≤72
are lattice inequalities. Nonzero uses NeZero M and
Ideal.span_singleton_eq_bot.not for the actual nonzero numeral72. Properness
uses the actual goodLambda prime in S and Finset.dvd_prod_of_mem, exactly the
argument of sourceFixedIdeal_ne_top. Then internalQ Q0 ηlabel is nonzero and
proper by the compiled NaturalFixedRaySourceInternal.internalQ_ne_zero and
internalQ_ne_top lemmas, and ≤span72 by inf_le_left. The native state also
needs internalQ≤ηlabel.modulus, which follows definitionally from inf_le_right.

These are short real ideal proofs, not a missing family nonvanishing premise.
The existing SourceData-specific lemma cannot be invoked for generic S by
silently synthesizing old HighData; a generic proof/helper is still needed.

## Slot construction and meshes

The actual native energy uses Z as its base and slot powers Z^ell. The source
Batch uses U=Z^d and physical widths ell/d. To construct an actual Batch and
admit its slots simultaneously, select positive ell satisfying both

    ell s ≤ dmin * batchMesh
    ell s ≤ fineMesh Mcap0LκEnergyεE.

Choose a slot ceiling no larger than the minimum of these two positive
numbers, then apply the actual arbitrary-total slot-length construction.
Energy.WidthRanges.fineMesh_pos at line84 supplies positivity with the real
Mcap/mask/κ/epsilon assumptions. The old Parameters.fine_slot_widths bound
controls ell/d in a U-based interface; it must not be substituted for the
new absolute d*F.widths bound without the explicit multiplication proof.

The actual Batch constructor ActualSourceBatchTotal already preserves all
source fields for arbitrary positive total Λ, with dmax≤37Λ/7 and its real
supported-witness/calibration/maximum/rowBand conditions. A source field
wrapper can quantify over matching actual B independently of how B was
constructed; no constructor witness is used to replace those quantifiers.

## Why a new record/consumer path is still necessary

Hecke/DetectorRawFiber.Moments at line62 fixes its plain capacity to
3/4+2Δ at line72. Its c/κ arguments only control inverse_raw RawMoment. A
minimal one-field predicate should therefore carry an explicit κPlain.
A later `MomentsWithPlainKappa` can retain the actual inverse_raw,
inverse_marked and plain_unmarked fields with a separately parameterized
plain_marked field. Δ is not present in those other field types; downstream
endpoint/optimization parameters should remain separate and proved.

DetectorRawBranches.Fiber.plain_marked_count line30, BranchBudget's requested
capacity line60 and CountFromMoments lines76–83 still use 3/4+2Δ and the equal
denominator9/2+12Δ. The actual requested slot range also relies on crossing
bounds and supply≥7/37. None becomes a moving-κ consumer by changing a record
name. `plain_fiber_count` itself has only κPlain≥0; any κPlain≤1 requirement
belongs to a later zero-capacity/optimization branch.

Taking selected=empty in the current marked field only admits 2m≤1. Actual
Fiber.lengths allows m≤1/2+75ε, so this does **not** supply full plain_unmarked
with target U^(max1(2m)+εm). For m>1/2 a new proof needs true native padding or
a separate no-slot API. One viable candidate is actual native PositiveAt with
empty slots and a NaturalState rowWidth=max(d,2dm): native capacity2dm≤rowWidth
and radial domination can then be proved, but X/L/Mcap bounds and height-loss
absorption must be genuinely verified. This is a proposed future proof, not
a checked consequence of the current marked root.

## Actual build boundary of the source interfaces

At the stable source-state snapshot recorded in closures.json:

* DetectorDictionarySource: actual exit0, custom closure1015.
* NaturalFixedRaySourceBatch: actual exit0, custom closure1529.
* NaturalFixedRaySourceFixedIdeal: actual exit0, custom closure1534.
* DetectorBatch: actual exit0, custom closure601.
* SourceExclusions: actual exit0, custom closure467.
* NonfloorMoments: no actual selected-state compile; its import closure has
  48 pinned uncompiled OAI nodes and927 actual custom nodes.

The cached/external import leaves are explicit in the snapshot and are not
counted as new verified proofs. The snapshot binds source hashes and all
existing actual artifacts; it is not a source build plan or fresh/Nano replay.
The 48 uncompiled nodes are listed exactly in closures.json. Avoiding the
whole NonfloorMoments branch is a concrete dependency saving for this single
source-specific plain field, while leaving full Moments/count work explicit.
