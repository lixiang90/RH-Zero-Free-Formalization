# Upstream low-kappa development capsule

This frozen development snapshot is pending full actual-module verification. It
does not modify the main Lean 4.33.0-rc2 project and none of its intermediate
results belongs in that project's verified theorem count.

The source is public OpenAI/math commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Source bytes are read from the Git
object at that commit, never trusted from an editable working-tree copy.
The working project uses Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Its exact external imports require
Rellich-Kondrachov `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` and, for larger
roots, PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0`.
`template/lake-manifest.json` fixes their full package dependency graph.

## Source preparation

With an existing clone containing that commit:

```text
python prepare_low_kappa_capsule.py --source /path/to/math --destination /new/empty/plain-project --target OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
```

To fetch the public Git commit without materializing the entire math repository,
add `--fetch` and give an absent source directory. The Git object database is
partial and OAI source blobs are read lazily. Existing source or output data is
never recursively removed or overwritten.

The actual baseline-only preparation was executed successfully on 2026-10-09:
383 OAI modules were copied from pinned Git blobs in 4.27 seconds, with output
status `prepared_pending_compile`. This is a test of the preparation tool,
not a compilation claim.

## Patches remain inputs

Do not freeze the active working-copy changes until the owning agents finish
and a reviewer checks their exact source differences. The tool accepts a frozen
manifest of this shape; values below are placeholders:

```json
{
  "status": "pending",
  "upstream_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
  "patches": [{"file": "reviewed.patch", "sha256": "<patch digest>"}],
  "files": [{
    "path": "OAI/NumberTheory/DirichletL/Moments/ReflectionRetainedLength.lean",
    "baseline_sha256": "<exact pinned source digest>",
    "modified_sha256": "<reviewed modified source digest>"
  }],
  "targets": ["OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength"],
  "declarations": [
    "OAI.SevenEighths.CenteredMomentReflectionRetainedLength.positive_slot_width_drop"
  ]
}
```

Patch paths and hashes are checked; `git apply --check` precedes application.
The tool rejects unlisted modifications, new files and unprepared OAI imports.
Pending is a publication status, not a permission to insert an axiom.

## Actual checks

Add `--patch-manifest /path/to/manifest.json --install --build` to a fresh
preparation command. `--install` runs the pinned Mathlib cache fetch;
`--build` runs `serial_build.py` for the selected target closure and then a fresh
Lean process containing `#check` and `#print axioms` for listed declarations.
An existing prepared project can also run these stages directly:

```text
lake exe cache get
lake env python -B -X utf8 serial_build.py OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
lake env lean -j1 FreshLowKappaAudit.lean
```

The build driver uses one Lean process at a time and two Lean threads. It stores
source and dependency fingerprints, output paths, commands, timings, logs and
exit codes. Fresh types preserve all hypotheses in the report. The status after
successful compilation remains `compiled_locally_pending_independent_replay`.
An independent kernel replay must be added and passed before claiming full
verification. A failure never becomes a successful summary.

The target currently has 383 OAI source dependencies plus 15 actual
Rellich-Kondrachov source dependencies. The complete CertifiedExistence target
has 2,212 OAI modules (21.09 MB). A targeted first gate is considerably smaller
than the final analytic chain, but still substantial. The proof-source edits
must propagate consistently through all callers; compiling an early gate does
not establish the final nonzero strip.

Two pure arithmetic lemmas extracted from the modified ReflectionRetainedLength
working copy separately passed Lean 4.34.1 and fresh transitive axiom printing:
only `propext`, `Classical.choice`, `Quot.sound`. That small capsule contains no
substitution for actual Hecke polynomial or retainedAnnuli definitions and does
not certify an analytic moment bound.

Static inspection of all 383 OAI modules strips nested comments and strings and
finds no lexical `axiom`, `sorry`, `sorryAx`, `admit`, `native_decide`, `unsafe`,
`opaque`, `implemented_by`, `extern`, or `trustLevel`. This inspection is useful
source evidence; it cannot replace a compiled transitive axiom audit or replay.


## Optional bounded scheduler

The default is fully serial. The alternate driver has an explicit maximum of
two Lean child processes, each with two threads; select it with `--jobs 2` in
the preparation tool or run:

```text
lake env python -B -X utf8 serial_build_bounded.py --jobs 2 OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
```

Never run the serial and bounded source builders simultaneously. The bounded
driver drains running tasks after the first failure, writes state through a
single controller, rejects source changes during compilation, and accepts
`.serial-build/stop-after-current.flag` to stop scheduling after current jobs
finish. The actual bounded build has run with these limits and safely drained its
running jobs after a dependency failure.

## Frozen pending snapshot

This bundle contains the currently frozen 41-module LF patch
`reviewed-pending.patch` with SHA-256
`d18941bdb3a32f42032c5e82c6518baa5dc03968ff8af652ca30d62d6467566e`.
Its manifest is explicitly `pending_actual_module_verification`. The full
physical module chain has not passed. One actual first build encountered an
API compatibility error in the fixed Rellich dependency, Euclidean/H1.lean.
That compatibility repair is maintained separately from the 41 mathematical
source edits and must have its own package pin, source hashes and fresh audit.

The preparation tool parses every fresh axiom line, requires exactly the
requested declaration names and count, checks that a fresh type line exists,
and allows only the three standard axioms. It also compares complete source
hash snapshots before and after compilation and fresh audits. Successful
`#print axioms` process exit alone cannot set the axiom-audit flag.

An external compatibility manifest can be supplied with
`--external-compat-manifest`. It names exact package commits, relative files,
baseline Git-blob SHA, modified LF SHA, independent patch SHA, target modules
and declaration names. The tool verifies the package HEAD and canonical
baseline before application, rejects unlisted modifications, and audits these
declarations in a separate fresh process. It remains pending independent replay.

## This checkpoint's exact evidence

`verification/preparation-result.json` records a real successful reconstruction
of all 2,212 OAI modules and application of all 41 frozen source patches from
the public LF Git baseline. This is source preparation, not completion of
either requested analytic target.

`compat/manifest.json` currently contains separate H1 and Translation proof
compatibility patches for the pinned Rellich package. Both keep the original
definitions and statement types. The source-only patch application was tested
on a fresh local clone of the pinned package, and an idempotent second
application verified every final hash. Its record is
`verification/external-compatibility-application.json`.

A new fresh Lean process checked the exact types and permitted transitive
axioms of all 24 listed H1/Translation declarations and preserved both source
hashes; see `verification/rellich-compatibility-strict-audit.json` and its log.
The parser handles wrapped Lean axiom lists and universe annotations; actual
output and deliberately corrupted missing/extra-axiom output tested acceptance
and rejection. These external module checks are not the full OAI moment proof.

The latest completed driver run still had a subsequent Rellich
TranslationEstimateL2 compatibility gate. The owning reviewer is addressing
it separately. `verification/latest-actual-module-status.json` is a snapshot
of completed actual process exits, not a final target-pass declaration.
These dependency fixes and the 41 OAI changes remain outside the main
Lean 4.33 project theorem count.

For full reproduction in a new directory, add all current manifest flags:

```text
python prepare_low_kappa_capsule.py --source /path/to/math --destination /new/empty/plain-project --patch-manifest manifest.json --external-compat-manifest compat/manifest.json --install --build --jobs 2
```

To test only dependency patch application in an already prepared project
containing untouched pinned package checkouts:

```text
python prepare_low_kappa_capsule.py --source /path/to/math --destination /prepared/plain-project --external-compat-manifest compat/manifest.json --apply-external-only
```

No whole-chain certificate is asserted until the requested target compile,
fresh counted axiom audit, source bindings and independent replay all pass.


## Checkpoint on 2026-10-09

The primary 4.33.0-rc2 library separately passes 214 public roots and an
independent replay of 58,109 declarations. None of the pending OAI targets
in this directory is included in those counts.

The actual 4.34.1 dependency build reached 61 successful modules. H1 and
Translation compatibility repairs passed actual module compilation and
fresh checks of 24 declarations, with only the three standard axioms.
These preserve all original definitions and theorem statements. Their
source patches, fixed package commit, raw/canonical hashes, logs and
strict fresh audit are under compat/ and verification/; their independent
replay is pending. The original Rellich Apache-2.0 license is under licenses/.

The frozen snapshot excludes the subsequent TranslationEstimateL2 repair,
which is being checked separately. A fresh full build with only this
snapshot can therefore reach that known dependency compatibility gate.
Neither ReflectionRetainedLength nor CertifiedExistence has completed
its actual compilation/audit here.

The source-preparation tool was actually run on this frozen 41-file LF patch,
rebuilding its 2,212-module source closure directly from the pinned Git blobs
and verifying every baseline and modified hash. Independent fresh-package
fixtures applied both compatibility patches and checked their idempotence.
Compact results are verification/preparation-result.json and
verification/external-compatibility-application.json. These certify source
preparation/application, not the remaining arithmetic moment proof.

The OAI patch uses the upstream Apache-2.0 license preserved at
[third_party/OAI-LICENSE](../../third_party/OAI-LICENSE).
