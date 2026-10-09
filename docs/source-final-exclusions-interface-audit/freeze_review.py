"""Freeze read-only interface review and already existing source bindings."""
from pathlib import Path
import hashlib, json, subprocess, datetime
ROOT = Path(__file__).resolve().parent
WORK = Path(r"E:\codex-build\RH-Zero-Free-Formalization\tmp\upstream-plain")
GIT = Path(r"E:\codex-build\math")
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
BASE = "OAI/NumberTheory/DirichletL/"
FILES = ["ParametersFixedSource.lean", "Detector/FixedEuler.lean", "PrimeRows/FirstTail.lean", "Detector/SourceExclusions.lean", "Moments/DetectorDictionarySource.lean", "Moments/GenericSourceIdealAndMesh.lean"]
PRIVATE = [Path(r"E:\codex-build\RH-Weil\tmp\source-after-slots-phase-20261009\SourceAfterSlotsPlainMarkedLowKappa.lean"), Path(r"E:\codex-build\RH-Weil\tmp\source-after-slots-phase-20261009\contract.json"), Path(r"E:\codex-build\RH-Weil\tmp\losses-before-arithmetic-source-phase-20261009\LossesBeforeArithmeticSourcePlainMarkedLowKappa.lean")]
def sha(b): return hashlib.sha256(b).hexdigest()
def lf(b): return b.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
def git(*args): return subprocess.run(["git", "-C", str(GIT), *args], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout
def save(p,b): p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(b)
state_path = WORK / ".serial-build/state.json"
state = json.loads(state_path.read_text(encoding="utf-8"))
records, checks = [], {}
for short in FILES:
    rel = BASE + short
    src = WORK / rel
    raw = src.read_bytes()
    checks[src] = sha(raw)
    module = rel[:-5].replace("/", ".")
    entry = state[module]
    assert entry["exit_code"] == 0 and entry["source_sha256"] == sha(raw)
    artifacts = entry["artifact_sha256"]
    assert all(sha(Path(p).read_bytes()) == h for p,h in artifacts.items())
    for p,h in artifacts.items(): checks[Path(p)] = h
    target = ROOT / "sources/actual" / rel
    save(target, raw)
    rec = {"module": module, "actual_source": str(src), "actual_snapshot": target.relative_to(ROOT).as_posix(), "raw_sha256": sha(raw), "lf_sha256": sha(lf(raw)), "existing_actual_compile": {"exit_code": 0, "source_sha256": entry["source_sha256"], "fingerprint": entry["fingerprint"], "log_path": entry["log_path"], "artifact_sha256": artifacts, "source_and_artifacts_match_at_review": True}, "new_proof_claim": False}
    if short == "Moments/GenericSourceIdealAndMesh.lean":
        rec["original_git_blob"] = None
        rec["origin"] = "previously checked authored extension, not in original pin"
    else:
        gitrel = "lean/" + rel
        blob = git("show", PIN + ":" + gitrel)
        oid = git("rev-parse", PIN + ":" + gitrel).decode().strip()
        dst = ROOT / "sources/original-git" / rel
        save(dst, blob)
        rec["original_git_blob"] = {"repository": str(GIT), "commit": PIN, "path": gitrel, "oid": oid, "snapshot": dst.relative_to(ROOT).as_posix(), "raw_sha256": sha(blob), "lf_sha256": sha(lf(blob)), "actual_equals_original_raw": raw==blob, "actual_equals_original_lf": lf(raw)==lf(blob)}
    records.append(rec)
private = []
for p in PRIVATE:
    raw = p.read_bytes(); checks[p] = sha(raw)
    dst = ROOT / "prepared-candidate-reference" / p.name
    save(dst, raw)
    private.append({"path": str(p), "snapshot": dst.relative_to(ROOT).as_posix(), "raw_sha256": sha(raw), "lf_sha256": sha(lf(raw)), "scope": "prepared proof or contract reviewed read-only, no compile/replay claim"})
stable = all(sha(p.read_bytes()) == h for p,h in checks.items())
assert stable
review = (ROOT / "review.md").read_bytes()
meta = {"schema": "source-final-exclusions-readonly-interface-review-v1", "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "status": "frozen_read_only_review", "review_sha256": sha(review), "key_actual_source_bindings": records, "prepared_candidate_references": private, "source_and_artifact_before_after_stable": stable, "ran_lean_or_controller_or_export_or_nanoda": False, "modified_formal_sources_or_state": False, "new_proof_roots": 0}
encoded = (json.dumps(meta,ensure_ascii=False,indent=2)+"\n").encode()
save(ROOT / "metadata.json", encoded)
summary = {"folder": str(ROOT), "review_sha256": sha(review), "metadata_sha256": sha(encoded), "actual_sources_exit0_bound": len(records), "pinned_git_blobs": 5, "new_proof_roots": 0, "all_before_after_stable": stable}
save(ROOT / "frozen-summary.json", (json.dumps(summary,indent=2)+"\n").encode())
print(json.dumps(summary,indent=2))
