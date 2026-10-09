from pathlib import Path
import hashlib,subprocess,sys,json
b=Path(r"E:/codex-build/RH-Zero-Free-Formalization");k=b/"tmp/upstream-kernel";w=b/"tmp/upstream-plain"
runner=k/"scripts/run_upstream_nanoda_multitarget_v3.py"
assert hashlib.sha256(runner.read_bytes()).hexdigest()=="e9cc518136e68b1b8af6f11010d561e6baaa44c1a69847fb344d5acebbd9b714"
groups=json.loads((k/"verification/marked-supply3-groups.json").read_bytes())
assert len(groups)==3 and sum(len(v) for v in groups.values())==3
cmd=[sys.executable,"-B","-X","utf8",str(runner),"--project",str(w)]
for m in groups:cmd += ["--module",m]
for roots in groups.values():
 for root in roots:cmd += ["--root",root]
cmd += ["--exporter-repo",str(k/"lean4export"),"--exporter-bin",str(k/"lean4export/.lake/build/bin/lean4export.exe"),"--nanoda-repo",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/nanoda","--nanoda-bin",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/kernel-tools/nanoda-target/release/nanoda_bin","--label","marked-supply3-actual","--scope",'Three new canonical authored declarations: actual finite-fiber plain-marked admission with derived energy capacity and exact degree+4J growth absorption; native terminal degree/S selected before all characters and ideals; and an actual eventual plain-marked field for fixed finite eta/Q maps before degree. The finite-family field imports formal Admission and does not use the separate global-degree primitive to enlarge its quantifiers. Complete real state, row/calibration, character/ideal, profile/prime/window/external/height/plain-capacity/budget and global beta/moving-kappa gates stay visible. This is one moving-capacity Moments field; all-character RawMomentInput uniform profile degree, complete four-field Moments, counts and unconditional improved zero-free assembly remain pending. Historical private Candidate artifacts are separate, and older85 roots are not replayed as an added selected set. Exact unused imported PNTA auxiliaries are disclosed and excluded from the selected export.']
raise SystemExit(subprocess.call(cmd,cwd=w))
