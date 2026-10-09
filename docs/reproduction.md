# Reproduction details

## Main Lean audit

Run Python 3.10+ and Elan in the checkout:

    lake update
    lake exe cache get
    python scripts/verify.py

The local checked run reused exact-revision dependency caches via ignored
Windows junctions. The committed package file and lock manifest refer to
public Git sources and contain no absolute cache paths.

verify.py checks every public theorem, records source hashes before and after
the actual build/audit, and fails on any nonzero process result, unexpected
axiom, missing audit output or source mutation. The full types of conditional
theorems remain visible in the axiom audit and source.

## Independent Nano kernel

The optional independent driver currently uses a Windows Lean exporter and
WSL Ubuntu Nano. Required tool revisions:

- lean4export: b18d673bd29b476466a51a3be1012df2ed322b10
- nanoda: 418320295890faed83a96fd97907b12a3b6728c2

Build those tools from their public sources, placing repositories and binaries
at the paths in scripts/verify_independent_nanoda.py, or supply a tool root
with the same tmp layout:

    python scripts/run_nanoda.py --tool-root PATH_TO_TOOL_ROOT

This invokes a fresh export of all 146 public theorem roots, followed by the
serial Nano checker. Only propext, Quot.sound and Classical.choice are allowed;
unexpected axioms are hard errors. The wrapper checks all project Lean source
and compiled-module hashes before and after, and binds the complete Lean
audit record. Detailed commands, binary hashes, resources and the observed
checker result are retained in verification/independent-kernel.json.

The proof checker verifies implications with their stated hypotheses.
It does not construct ZetaSignalObligation or certify an unconditional
improved arithmetic zero-free theorem.

## Historical exact audit

    python scripts/hybrid_kappa_feedback_exact_audit.py

This standard-library rational audit is preserved from the parent research
repository and prints its own finite-algebra scope. It provides independent
numerical provenance; its output is not a premise in a Lean proof.
