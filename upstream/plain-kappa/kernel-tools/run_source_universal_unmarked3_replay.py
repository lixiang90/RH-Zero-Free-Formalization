from pathlib import Path
import hashlib,subprocess,sys,json
b=Path(r"E:/codex-build/RH-Zero-Free-Formalization");k=b/"tmp/upstream-kernel";w=b/"tmp/upstream-plain"
runner=k/"scripts/run_upstream_nanoda_multitarget_v3.py"
assert hashlib.sha256(runner.read_bytes()).hexdigest()=="e9cc518136e68b1b8af6f11010d561e6baaa44c1a69847fb344d5acebbd9b714"
groups=json.loads((k/"verification/source-universal-unmarked3-groups.json").read_bytes())
assert len(groups)==2 and sum(len(v) for v in groups.values())==3
cmd=[sys.executable,"-B","-X","utf8",str(runner),"--project",str(w)]
for m in groups:cmd += ["--module",m]
for roots in groups.values():
 for root in roots:cmd += ["--root",root]
cmd += ["--exporter-repo",str(k/"lean4export"),"--exporter-bin",str(k/"lean4export/.lake/build/bin/lean4export.exe"),"--nanoda-repo",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/nanoda","--nanoda-bin",r"E:/codex-build/RH-Zero-Proportion-Formalization/tmp/kernel-tools/nanoda-target/release/nanoda_bin","--label","source-universal-unmarked3-actual","--scope",'Three new canonical mathematical roots: a universal actual source-dictionary plain-marked field for every matching q/Batch and nonempty fiber, plus principal-exponent growth absorption and actual empty-selected unmarked admission. For the universal field, fixed prime S/product M precedes scalar losses, N/ell/slotLower, then terminal/profile degrees and common positive height ceiling; these precede every outer character. Each character has a positive constant and eventual threshold before all smaller positive heights, source rows and all matching batches/fibers. The exact SourcePlainMarkedAt predicate is not an extra selected root. The unmarked admission uses natural row width d*max(1,2*m)+rho without marked capacity, retaining actual PositiveAt, state-width and polynomial-scale caps, radial keep/profile cover and the height/loss budget. All arithmetic, beta/kappa, source-data/family/profile/window, prime/mesh/external/height/plain-capacity gates in the full types remain explicit. Complete SourceData/SourceMomentsAt/RawMomentInput, remaining fields, counts/probe and improved unconditional zero-free assembly remain pending. Older93 roots and private prototypes are not replayed; exact unused imported PNTA holes remain disclosed and absent from selected exports.']
raise SystemExit(subprocess.call(cmd,cwd=w))
