
"""Replay every public theorem with the independently pinned serial Nano kernel."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--tool-root',type=Path,default=ROOT)
 a=p.parse_args();tool=a.tool_root.resolve()
 roots=json.loads((ROOT/'verification/roots.json').read_text())
 prior=json.loads((ROOT/'verification/lean-verification.json').read_text())
 if not prior['checked']:raise RuntimeError('A successful full Lean audit is required first')
 files=list((ROOT/'ZeroFree').glob('*.lean'))+[ROOT/'ZeroFree.lean']+list((ROOT/'.lake/build/lib/lean/ZeroFree').glob('*.olean'))+[ROOT/'.lake/build/lib/lean/ZeroFree.olean']
 before={str(f.relative_to(ROOT)).replace('\\','/'):sha(f) for f in files}
 for name,expected in prior['source_hashes_after'].items():
  if name.endswith('.lean') and (ROOT/name).exists() and sha(ROOT/name)!=expected:raise RuntimeError('Source changed after Lean audit: '+name)
 cmd=[sys.executable,'-B','-X','utf8',str(ROOT/'scripts/verify_independent_nanoda.py'),'ZeroFree',
 '--olean','.lake/build/lib/lean/ZeroFree.olean','--source','ZeroFree.lean',
 '--lean-path','.lake/build/lib/lean',
 '--exporter-repo',str(tool/'tmp/lean4export'),
 '--exporter-bin',str(tool/'tmp/lean4export/.lake/build/bin/lean4export.exe'),
 '--nanoda-repo',str(tool/'tmp/nanoda'),
 '--nanoda-bin',str(tool/'tmp/kernel-tools/nanoda-target/release/nanoda_bin'),
 '--threads','1','--output','verification/independent-kernel.json',
 '--scope','Every public theorem including exact cubic algebra, feedback, real Mellin continuation, quantified family reduction and conditional actual-zeta theorem. Explicit arithmetic hypotheses remain unproved; no official website acceptance.']
 for root in roots:cmd+=['--root',root]
 process=subprocess.run(cmd,cwd=ROOT)
 after={str(f.relative_to(ROOT)).replace('\\','/'):sha(f) for f in files}
 record=json.loads((ROOT/'verification/independent-kernel.json').read_text())
 record.update({'all_project_source_and_olean_hashes_before':before,'all_project_source_and_olean_hashes_after':after,
 'all_project_inputs_unchanged':before==after,'complete_arithmetic_zero_free_proof':False,
 'requires_explicit_signal_hypotheses':True,'lean_audit_record_sha256':sha(ROOT/'verification/lean-verification.json')})
 record['nano_check_passed']=record['nano_check_passed'] and before==after
 (ROOT/'verification/independent-kernel.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
 return 0 if process.returncode==0 and record['nano_check_passed'] else 1
if __name__=='__main__':sys.exit(main())

