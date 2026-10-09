# Marked-moment integration audit

This read-only review traces the actual marked sum, its energy dictionary and
the count consumers in the pinned OAI source. It separates a supplied moment
record from a proof that constructs it. The Chinese review and its 42-file
source snapshot are [audit.zh.md](audit.zh.md) and
[source-snapshot.json](source-snapshot.json). They are a dated source review,
not an axiom audit or a complete moment proof.

The shortest proposed integration starts with the exact
`fiber_plain_energy_eq`, then embeds its finite row sum into the full actual
radial energy. The canonical central rows already have the required lower
norm cutoff. A canonical source Batch and the complete moment estimates
still need to be constructed; see
[canonical-row-domain.zh.md](canonical-row-domain.zh.md).

The pointwise identity in the review has since been promoted to the separate
actual source [RayIdentityClassCoefficient.lean](../../upstream/plain-kappa/extensions/files/OAI/NumberTheory/DirichletL/Moments/RayIdentityClassCoefficient.lean).
Its current actual-module verification is recorded in the capsule manifest.
It does not bound row energies. The earlier standalone prototype bytes are
archived in [IdentityClassCoefficient.lean.raw-source.json](IdentityClassCoefficient.lean.raw-source.json)
so that the review's source binding remains recoverable. This historical
prototype is not a second module in the main or actual arithmetic libraries.
