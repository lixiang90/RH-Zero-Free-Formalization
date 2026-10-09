from pathlib import Path
import hashlib,subprocess,sys,json
b=Path(r"E:/codex-build/RH-Zero-Free-Formalization");k=b/"tmp/upstream-kernel";w=b/"tmp/upstream-plain"
runner=k/"scripts/run_upstream_nanoda_multitarget_v3.py"
assert hashlib.sha256(runner.read_bytes()).hexdigest()=="e9cc518136e68b1b8af6f11010d561e6baaa44c1a69847fb344d5acebbd9b714"
groups=json.loads((k/"verification/uniform-height1-groups.json").read_bytes())
assert len(groups)==1 and sum(len(v) for v in groups.values())==1
cmd=[sys.executable,"-B","-X","utf8",str(runner),"--project",str(w)]
for m in groups:cmd += ["--module",m]
for roots in groups.values():
 for root in roots:cmd += ["--root",root]
cmd += ["--exporter-repo",str(k/"lean4export"),"--exporter-bin",str(k/"lean4export/.lake/build/bin/lean4export.exe"),"--nanoda-repo",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/nanoda","--nanoda-bin",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/kernel-tools/nanoda-target/release/nanoda_bin","--label","uniform-height1-actual","--scope",'One new canonical authored source field: terminal degree/S, detector control degree and positive common height exponent chosen before arbitrary finite eta/Q families; for each family the same positive constant and eventual Z threshold work before every smaller positive tauPrime<=tau. All source profile, radial state, arithmetic/calibration, row lower bounds, native beta/kappa, slot mesh, coprime-prime, external Re=17/50, height and moving plain capacity gates remain explicit in full types. Only the actual plain-marked field is supplied; complete SourceMomentsAt/RawMomentInput, the four-field Moments record, counts/probe and improved unconditional zero-free assembly remain pending. Private Candidate records and older88 selected roots are distinct; exact unused imported PNTA holes remain disclosed and absent from the selected kernel export.']
raise SystemExit(subprocess.call(cmd,cwd=w))
