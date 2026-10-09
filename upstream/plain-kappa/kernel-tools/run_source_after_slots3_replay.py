from pathlib import Path
import hashlib,subprocess,sys,json
b=Path(r"E:/codex-build/RH-Zero-Free-Formalization");k=b/"tmp/upstream-kernel";w=b/"tmp/upstream-plain"
runner=k/"scripts/run_upstream_nanoda_multitarget_v3.py"
assert hashlib.sha256(runner.read_bytes()).hexdigest()=="e9cc518136e68b1b8af6f11010d561e6baaa44c1a69847fb344d5acebbd9b714"
groups=json.loads((k/"verification/source-after-slots3-groups.json").read_bytes())
assert len(groups)==2 and sum(len(v) for v in groups.values())==3
cmd=[sys.executable,"-B","-X","utf8",str(runner),"--project",str(w)]
for m in groups:cmd += ["--module",m]
for roots in groups.values():
 for root in roots:cmd += ["--root",root]
cmd += ["--exporter-repo",str(k/"lean4export"),"--exporter-bin",str(k/"lean4export/.lake/build/bin/lean4export.exe"),"--nanoda-repo",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/nanoda","--nanoda-bin",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/kernel-tools/nanoda-target/release/nanoda_bin","--label","source-after-slots3-actual","--scope",'Three new canonical actual mathematical roots. Native rho and epsilonE losses are constructed before every ideal M, subgroup H and finite Slot; later degrees/J/common height precede every finite eta/Q family. The source wrapper constructs arbitrary-positive-total physical/energy mesh slots before any arithmetic source. After every positive caller detector e and seed prime set it constructs actual S with SourceExclusions, FirstTail(4*e), maximal primes and nonzero product; the product ideal/subgroup is then followed by degree/J/common height before the outer character and its constant/eventual threshold, which cover all smaller positive heights and matching q/Batch/nonempty fibers. The detector e is distinct from epsilonE. Complete HighData/SourceData assembly, full SourceMomentsAt/RawMomentInput, the other three Moments fields, counts/probe and improved unconditional zero-free assembly remain pending. Older96 selected roots are not replayed. Exact unused imported PNTA holes remain disclosed and absent from selected exports.']
raise SystemExit(subprocess.call(cmd,cwd=w))
