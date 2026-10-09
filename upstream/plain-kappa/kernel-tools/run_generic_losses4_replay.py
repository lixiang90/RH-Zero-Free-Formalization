from pathlib import Path
import hashlib,subprocess,sys,json
b=Path(r"E:/codex-build/RH-Zero-Free-Formalization");k=b/"tmp/upstream-kernel";w=b/"tmp/upstream-plain"
runner=k/"scripts/run_upstream_nanoda_multitarget_v3.py"
assert hashlib.sha256(runner.read_bytes()).hexdigest()=="e9cc518136e68b1b8af6f11010d561e6baaa44c1a69847fb344d5acebbd9b714"
groups=json.loads((k/"verification/generic-losses4-groups.json").read_bytes())
assert len(groups)==2 and sum(len(v) for v in groups.values())==4
cmd=[sys.executable,"-B","-X","utf8",str(runner),"--project",str(w)]
for m in groups:cmd += ["--module",m]
for roots in groups.values():
 for root in roots:cmd += ["--root",root]
cmd += ["--exporter-repo",str(k/"lean4export"),"--exporter-bin",str(k/"lean4export/.lake/build/bin/lean4export.exe"),"--nanoda-repo",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/nanoda","--nanoda-bin",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/kernel-tools/nanoda-target/release/nanoda_bin","--label","generic-losses4-actual","--scope",'Four new canonical source helpers: actual fixed ideal/internalQ gates, arbitrary positive total slot construction meeting batch/physical/energy meshes, exact absolute width for an actual nonempty batch fiber, and a genuine eventual source plain-marked field choosing scalar losses before every finite Slot. Degree/J/common height may depend on Slot but precede finite arithmetic maps; each family has a common positive constant and Z threshold before every smaller positive height. All beta/kappa/source/profile/row/prime/slot/external/height/plain-capacity gates are retained in complete types. Full SourceMomentsAt/RawMomentInput, remaining three fields, counts/probe and improved unconditional zero-free assembly remain pending. Private Candidate evidence and older89 roots are distinct; exact unused imported PNTA holes are disclosed and prohibited in selected exports.']
raise SystemExit(subprocess.call(cmd,cwd=w))
