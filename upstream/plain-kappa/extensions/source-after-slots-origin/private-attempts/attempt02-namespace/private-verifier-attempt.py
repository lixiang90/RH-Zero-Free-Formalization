"""Serial private compile/fresh only. Preserve canonical state and all old sources."""
from pathlib import Path
import datetime, hashlib, importlib.util, json, os, re, subprocess, time

PARENT = Path(r"E:\codex-build\RH-Weil")
FORMAL = Path(r"E:\codex-build\RH-Zero-Free-Formalization")
PROJECT = FORMAL / "tmp/upstream-plain"
PUBLIC = FORMAL / "upstream/plain-kappa"
STRICT = FORMAL / "tmp/upstream-kernel/scripts/run_upstream_nanoda_multitarget_v3.py"
EXPECTED_STATE = "f144fb67f376648f0dd4f3b213e28a709339951a2b08e032e4794fe09f398043"
INPUTS = [
    ("OAI.NumberTheory.DirichletL.Moments.LossesBeforeArithmeticSourcePlainMarkedLowKappa",
     PARENT / "tmp/losses-before-arithmetic-source-phase-20261009/LossesBeforeArithmeticSourcePlainMarkedLowKappa.lean",
     "b793c307ed691f2bb516e8528428fbaefe181e6f5dc74827f8aa320865efbd07",
     ["OAI.SevenEighths.LossesBeforeArithmeticSourcePlainMarkedLowKappa.exists_losses_before_arithmetic_slots_degrees_height_and_finite_family"]),
    ("OAI.NumberTheory.DirichletL.Moments.SourceAfterSlotsPlainMarkedLowKappa",
     PARENT / "tmp/source-after-slots-phase-20261009/SourceAfterSlotsPlainMarkedLowKappa.lean",
     "acc66a3ec52d43e0d574d03a2ed97530ae90d6aa1c393ddbfc9062f21c28fecf",
     ["OAI.SevenEighths.SourceAfterSlotsPlainMarkedLowKappa.exists_slots_before_source_universal_plain_marked",
      "OAI.SevenEighths.SourceAfterSlotsPlainMarkedLowKappa.exists_first_tail_source_after_slots"]),
]

def digest(raw): return hashlib.sha256(raw).hexdigest()
def sha(path): return digest(path.read_bytes())
def save(path, value): path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")

assert sha(STRICT) == "e9cc518136e68b1b8af6f11010d561e6baaa44c1a69847fb344d5acebbd9b714"
spec = importlib.util.spec_from_file_location("frozen_actual_strict", STRICT)
strict = importlib.util.module_from_spec(spec); spec.loader.exec_module(strict)
state_path = PROJECT / ".serial-build/state.json"
state_raw = state_path.read_bytes(); state = json.loads(state_raw)
assert digest(state_raw) == EXPECTED_STATE
assert len(state) == 2279 and all(v["exit_code"] == 0 for v in state.values())
env = os.environ.copy(); env["LEAN_NUM_THREADS"] = "2"
assert "LEAN" in env and "LEAN_SRC_PATH" in env and "LEAN_PATH" in env, "Run via pinned lake env"
lean = Path(env["LEAN"])
version = subprocess.check_output([str(lean), "--version"], text=True, encoding="utf-8").strip()
assert "version 4.34.1" in version
srcroots = list(dict.fromkeys(Path(p) for p in env["LEAN_SRC_PATH"].split(os.pathsep) if p))
libroots = [Path(p) for p in env["LEAN_PATH"].split(os.pathsep) if p]
approved = {}; files = {"strict-tool": STRICT, "private-verifier": Path(__file__).resolve(), "compiler": lean}
for module, source, expected, roots in INPUTS:
    raw = source.read_bytes(); assert digest(raw) == expected
    assert not re.search(r"\b(?:sorry|admit|axiom|unsafe)\b", raw.decode("utf-8"))
    approved[module] = raw; files["approved-source:" + module] = source

def lookup(module, bases, suffix):
    rel = Path(*module.split(".")).with_suffix(suffix)
    for base in bases:
        if (base / rel).is_file(): return base, base / rel
    raise ValueError("Missing dependency " + module + suffix)

plans = {}; selected = {}; known_holes = []; bases = {PROJECT}
roots = [root for item in INPUTS for root in item[3]]
def visit(module):
    if module in approved:
        for dependency in strict.import_names(approved[module]): visit(dependency)
        return
    if module in plans: return
    if module.split(".")[0] in strict.CACHED:
        _, output = lookup(module, libroots, ".olean"); st = output.stat()
        fp = digest((str(output) + ":" + str(st.st_size) + ":" + str(st.st_mtime_ns)).encode())
        plans[module] = {"cached": True, "fingerprint": fp}
        for path in strict.artifacts(output): files["cached:" + path] = Path(path)
        return
    base, source = lookup(module, srcroots, ".lean"); bases.add(base)
    raw = source.read_bytes(); imports = strict.import_names(raw)
    for dependency in imports: visit(dependency)
    fp = digest(json.dumps({"source_sha256": digest(raw), "dependencies": [(m, plans[m]["fingerprint"]) for m in imports],
        "lean_version": "4.34.1", "options": "autoImplicit=false for OAI/PNTA/Rellich only"}).encode())
    entry = state[module]; output = Path(entry["output"])
    assert entry["exit_code"] == 0 and entry["source_sha256"] == digest(raw) and entry["fingerprint"] == fp, module
    assert entry["artifact_sha256"] and strict.artifacts(output) == entry["artifact_sha256"], module
    for dependency, bound in entry.get("direct_dependency_artifact_sha256", {}).items():
        assert bound == state[dependency]["artifact_sha256"], (module, dependency)
    plans[module] = {"cached": False, "fingerprint": fp, "imports": imports}
    selected[module] = entry; files["source:" + module] = source
    for path in entry["artifact_sha256"]: files["artifact:" + path] = Path(path)
    log = Path(entry["log_path"]); files["build-log:" + module] = log
    log_text = log.read_text(encoding="utf-8", errors="replace")
    if re.search(r"declaration uses ['`]?sorry|sorryAx", log_text):
        known_holes.append(strict.actual_pnta_policy(module, base, raw, log_text, roots))

for module in approved: visit(module)
for base in bases:
    for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"):
        path = base / name
        if path.is_file(): files["config:" + str(path)] = path
old32 = json.loads((PUBLIC / "extensions/manifest.json").read_bytes())["files"]
old41 = json.loads((PUBLIC / "manifest.json").read_bytes())["files"]
assert len(old32) == 32 and len(old41) == 41
for item in old32:
    module = item["module"]; source = Path(state[module]["source"])
    assert sha(source) == item.get("raw_actual_source_sha256", state[module]["source_sha256"]), module
    files["old-authored:" + module] = source
for item in old41:
    module = item["path"].removesuffix(".lean").replace("/", "."); source = Path(state[module]["source"])
    assert digest(source.read_bytes().replace(b"\r\n", b"\n")) == item["modified_sha256"], module
    files["old-patched:" + module] = source
for name in ("extensions/manifest.json", "manifest.json", "reviewed-pending.patch"):
    files["public-baseline:" + name] = PUBLIC / name
before = {name: sha(path) for name, path in files.items()}
def stable():
    return state_path.read_bytes() == state_raw and all(sha(files[name]) == value for name, value in before.items())
assert stable()
stage = PARENT / "tmp/source-after-slots-phase-20261009" / ("private-verification-" + datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
stage.mkdir()
source_root = stage / "sources"; library = stage / "lib/lean"
attempt_verifier = stage / "private-verifier-attempt.py"
attempt_verifier.write_bytes(Path(__file__).read_bytes())
save(stage / "dependency-bindings.json", {"state_sha256": EXPECTED_STATE, "selected_actual_records": selected,
    "sha256_before": before, "input_paths": {name: str(path) for name, path in files.items()}, "known_unproved_imported_auxiliaries": known_holes})
# Lean chooses the first library containing a namespace prefix. Merge the old
# OAI artifact namespace into this isolated library using exact read-only aliases;
# placing only two OAI artifacts first would hide the previous OAI library.
runtime_aliases = {}
for module, entry in selected.items():
    if not module.startswith("OAI."): continue
    for original, expected in entry["artifact_sha256"].items():
        original = Path(original)
        relative = original.relative_to(PROJECT / ".lake/build/lib/lean")
        alias = library / relative; alias.parent.mkdir(parents=True, exist_ok=True)
        os.link(original, alias)
        assert sha(alias) == expected
        runtime_aliases[str(alias)] = expected
save(stage / "isolated-runtime-aliases.json", {"method": "Exact hard-linked aliases of already compiled OAI artifacts; no old module recompiled or original written.", "artifact_sha256": runtime_aliases})
env["LEAN_PATH"] = str(library) + os.pathsep + env["LEAN_PATH"]
env["LEAN_SRC_PATH"] = str(source_root) + os.pathsep + env["LEAN_SRC_PATH"]
compile_records = []; candidate_artifacts = {}
for module, original, expected, module_roots in INPUTS:
    rel = Path(*module.split(".")); source = source_root / rel.with_suffix(".lean"); source.parent.mkdir(parents=True, exist_ok=True)
    source.write_bytes(approved[module]); output = library / rel.with_suffix(".olean"); output.parent.mkdir(parents=True, exist_ok=True)
    command = [str(lean), "-j", "2", "-DautoImplicit=false", "--root=" + str(source_root), "-o", str(output), "-i", str(output.with_suffix(".ilean")), str(source)]
    started = time.monotonic(); result = subprocess.run(command, cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = stage / (module + ".compile.log"); log.write_bytes(result.stdout)
    artifacts = strict.artifacts(output); candidate_artifacts.update(artifacts)
    record = {"module": module, "original_source": str(original), "source_sha256": expected, "source_copy": str(source), "source_copy_sha256": sha(source),
        "roots": module_roots, "command": command, "exit_code": result.returncode, "elapsed_seconds": round(time.monotonic() - started, 3),
        "log": str(log), "log_sha256": sha(log), "artifact_sha256": artifacts, "all_old_inputs_and_state_stable": stable(),
        "scope": "Private candidate compilation, not a canonical controller record or independent Nano replay."}
    save(stage / (module + ".compile.json"), record); compile_records.append(record)
    print(json.dumps({"stage": str(stage), "module": module, "exit_code": result.returncode, "elapsed_seconds": record["elapsed_seconds"], "stable": record["all_old_inputs_and_state_stable"]}), flush=True)
    if result.returncode or not stable() or not artifacts or sha(source) != expected or re.search(r"declaration uses ['`]?sorry|sorryAx", result.stdout.decode("utf-8", "replace")):
        print(result.stdout.decode("utf-8", "replace")[-16000:], flush=True)
        raise SystemExit(result.returncode or 1)
audit = stage / "AxiomAudit.lean"
audit.write_text("".join("import " + module + "\n" for module in approved) +
    "set_option pp.all true\nset_option pp.maxSteps 1000000\n" +
    "".join("set_option pp.universes true\n#check @" + root + "\nset_option pp.universes false\n#print axioms " + root + "\n" for root in roots), encoding="utf-8", newline="\n")
command = [str(lean), "-j", "2", "-DautoImplicit=false", str(audit)]
started = time.monotonic(); result = subprocess.run(command, cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
log = stage / "fresh-types-and-axioms.log"; log.write_bytes(result.stdout)
text = result.stdout.decode("utf-8", "replace"); axes = None; error = None
try:
    assert result.returncode == 0, "Fresh Lean exit " + str(result.returncode)
    axes = strict.strict_axes(text, roots)
except Exception as caught: error = str(caught)
artifacts_stable = all(sha(Path(path)) == value for path, value in candidate_artifacts.items())
runtime_aliases_stable = all(sha(Path(path)) == value for path, value in runtime_aliases.items())
passed = result.returncode == 0 and error is None and stable() and artifacts_stable and runtime_aliases_stable
record = {"status": "private_actual_compile_and_full_fresh_pass" if passed else "private_fresh_failure", "stage": str(stage), "roots": roots,
    "private_root_count": len(roots), "compile_records": compile_records, "compiler": version,
    "fresh_command": command, "fresh_exit_code": result.returncode, "fresh_elapsed_seconds": round(time.monotonic() - started, 3),
    "fresh_log_sha256": sha(log), "audit_source_sha256": sha(audit), "fresh_audit": axes, "fresh_error": error,
    "selected_custom_dependency_count": len(selected), "cached_frontier_count": sum(item["cached"] for item in plans.values()),
    "all_old_inputs_and_state_bytes_stable": stable(), "candidate_artifacts_stable": artifacts_stable, "state_sha256_before": EXPECTED_STATE,
    "isolated_runtime_aliases_stable": runtime_aliases_stable, "isolated_runtime_alias_count": len(runtime_aliases),
    "state_sha256_after": sha(state_path), "known_unproved_imported_auxiliaries": known_holes,
    "whole_import_environment_hole_free": not bool(known_holes), "canonical_state_modified": False, "independent_nano_invoked": False,
    "strict_parser_sha256": sha(STRICT), "private_verifier_sha256": sha(Path(__file__))}
save(stage / "fresh-result.json", record)
print(json.dumps(record), flush=True)
if not passed: print(text[-16000:], flush=True)
raise SystemExit(0 if passed else 1)
