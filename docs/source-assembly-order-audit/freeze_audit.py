"""Read-only source review: save exact source/Git blobs, never run Lean."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parent
WORK = Path(r"E:\codex-build\RH-Zero-Free-Formalization\tmp\upstream-plain")
ORIGINAL = Path(r"E:\codex-build\math")
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
BASE = "OAI/NumberTheory/DirichletL/"
KEYS = [
    ("Detector/FinalAssemblyData.lean", ["structure SourceData", "exists_source_data"]),
    ("ParametersFixedSource.lean", ["exists_fixed_source", "exists_fixed_probe_window"]),
    ("ParametersHighData.lean", ["exists_high_data"]),
    ("ParametersDetectorScales.lean", ["exists_detector_scales"]),
    ("PrimeRows/FirstTail.lean", ["firstPrimeDefectBound", "structure FirstTail", "exists_first_cutoff", "exists_both_source_exclusions"]),
    ("Detector/SourceExclusions.lean", ["structure SourceExclusions", "exists_source_exclusions"]),
    ("Detector/GlobalCorrection.lean", ["globalPrimeDefectBound", "structure CorrectionTail", "exists_uniform_global_cutoff"]),
    ("Energy/WidthRanges.lean", ["def fineMesh", "fineMesh_pos"]),
]
REFERENCES = [
    "Detector/GlobalSourceCorrectionExistenceLowKappa.lean",
    "Moments/LossesBeforeSlotSourcePlainMarkedLowKappa.lean",
    "Moments/MarkedHeightBudgetLowKappa.lean",
    "PrimeRows/FirstTransport.lean",
    "Detector/CentralCubeNorm.lean",
]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def lf(data):
    return data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")

def git(*args):
    return subprocess.run(["git", "-C", str(ORIGINAL), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout

def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)

assert git("rev-parse", PIN + "^{commit}").decode().strip() == PIN
records = []
quotes = ["# Exact source excerpts for the read-only integration audit", "", "These are source excerpts, not a new Lean verification. Full raw snapshots and original pinned Git blobs are bound in metadata.json.", ""]
live_before = {}
for short, patterns in KEYS:
    rel = BASE + short
    live = WORK / rel
    raw = live.read_bytes()
    live_before[rel] = sha(raw)
    original_rel = "lean/" + rel
    blob_id = git("rev-parse", PIN + ":" + original_rel).decode().strip()
    original = git("show", PIN + ":" + original_rel)
    actual_save = ROOT / "sources" / "actual" / rel
    git_save = ROOT / "sources" / "original-git" / rel
    write(actual_save, raw)
    write(git_save, original)
    records.append({
        "module": rel[:-5].replace("/", "."),
        "actual_source": str(live),
        "actual_snapshot": actual_save.relative_to(ROOT).as_posix(),
        "actual_raw_sha256": sha(raw), "actual_lf_sha256": sha(lf(raw)),
        "actual_raw_bytes": len(raw),
        "original_repository": str(ORIGINAL), "original_commit": PIN,
        "original_git_path": original_rel, "original_git_blob_oid": blob_id,
        "original_snapshot": git_save.relative_to(ROOT).as_posix(),
        "original_git_blob_raw_sha256": sha(original), "original_git_blob_lf_sha256": sha(lf(original)),
        "actual_equals_original_raw": raw == original,
        "actual_equals_original_lf": lf(raw) == lf(original),
        "verification_scope": "read_only_source_review; no new compile or kernel claim",
    })
    lines = lf(raw).decode("utf-8").splitlines()
    quotes += ["## " + rel, "", "Actual raw SHA256: `" + sha(raw) + "`; original Git blob: `" + blob_id + "`.", ""]
    covered = set()
    for pattern in patterns:
        hits = [i for i, line in enumerate(lines) if pattern in line and not line.lstrip().startswith("--")]
        if not hits:
            quotes += ["No exact excerpt selector matched `" + pattern + "`; use the full snapshot.", ""]
            continue
        idx = hits[0]
        start, stop = max(0, idx - 2), min(len(lines), idx + 22)
        if idx in covered:
            continue
        covered.update(range(start, stop))
        quotes += ["### `" + pattern + "` (actual lines " + str(start + 1) + "–" + str(stop) + ")", "", "```lean"]
        quotes += [str(i + 1) + ": " + lines[i] for i in range(start, stop)]
        quotes += ["```", ""]

reference_records = []
for short in REFERENCES:
    rel = BASE + short
    raw = (WORK / rel).read_bytes()
    live_before[rel] = sha(raw)
    reference_records.append({"module": rel[:-5].replace("/", "."), "actual_source": str(WORK / rel), "raw_sha256": sha(raw), "lf_sha256": sha(lf(raw)), "binding_scope": "reference hash only; full eight key snapshots are separate"})

stable = all(sha((WORK / rel).read_bytes()) == digest for rel, digest in live_before.items())
assert stable, "source changed during read-only snapshot"
write(ROOT / "quoted-source.md", ("\n".join(quotes) + "\n").encode())
audit = (ROOT / "audit.md").read_bytes()
quoted = (ROOT / "quoted-source.md").read_bytes()
reviewed_prototype = Path(r"E:\codex-build\RH-Weil\tmp\source-plain-universal-phase-20261009")
meta = {
    "schema": "source-assembly-order-readonly-audit-v1",
    "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "status": "frozen_read_only_review",
    "new_proof_roots": 0,
    "ran_lean": False, "ran_controller": False, "ran_export_or_nanoda": False,
    "modified_formal_or_workcopy_source_or_state": False,
    "scope": "distinguish global prime-norm cutoff from physical slot count; original FirstTail-dependent final S and product M; source window and scalar energy mesh independence; missing true assembly order",
    "audit_file": "audit.md", "audit_raw_sha256": sha(audit), "audit_lf_sha256": sha(lf(audit)),
    "quoted_source_file": "quoted-source.md", "quoted_source_raw_sha256": sha(quoted),
    "original_commit": PIN, "key_source_binding_count": len(records),
    "key_sources": records, "additional_actual_reference_hashes": reference_records,
    "all_bound_actual_sources_before_after_stable": stable,
    "reviewed_universal_prototype_context_only": {
        name: {"path": str(reviewed_prototype / name), "raw_sha256": sha((reviewed_prototype / name).read_bytes())}
        for name in ["SourcePlainMarkedUniversal.candidate.lean", "verification-metadata.json", "verification/fresh.log"]
    },
    "conclusion": "Current fixed-S universal one-field type is valid. Full original source assembly additionally chooses slot-dependent positive detector e before FirstTail(4e) S and product(S). Future true interface must choose scalar losses and physical slots before final S, then native degree/J/tau; no existential exchange is justified by the current type.",
    "unproved_next_interface": "scalar geometry/window -> positive scalar losses -> energy mesh -> physical slots -> actual detector e -> FirstTail-compatible S and product M -> native degree/J/tau -> outer eta constants/eventual universal matching-Batch field",
}
encoded = (json.dumps(meta, ensure_ascii=False, indent=2) + "\n").encode()
write(ROOT / "metadata.json", encoded)
summary = {"folder": str(ROOT), "audit_sha256": sha(audit), "metadata_sha256": sha(encoded), "quoted_source_sha256": sha(quoted), "key_source_bindings": len(records), "sources_before_after_stable": stable, "new_proof_roots": 0}
write(ROOT / "frozen-summary.json", (json.dumps(summary, indent=2) + "\n").encode())
print(json.dumps(summary, ensure_ascii=False, indent=2))
