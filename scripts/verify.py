
"""Build every formal module, then freshly audit every public theorem.

The successful audit proves the declarations with their stated hypotheses.
It does not prove the existence of the arithmetic signal package.
"""
from pathlib import Path
import hashlib, json, re, subprocess, sys, time
ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Quot.sound','Classical.choice'}
SCOPES={
'Boundary':'ZeroFree',
'Certificate':'ZeroFree.Certificate',
'Geometry':'ZeroFree.Geometry',
'Feedback':'ZeroFree.Feedback',
'UpstreamSupremum':'ZeroFree.UpstreamSupremum',
'Continuation':'ZeroFree.Continuation',
'Signal':'ZeroFree.Signal',
'Family':'ZeroFree.Family',
'Main':'ZeroFree',
'HeightClosure':'ZeroFree.HeightClosure',
'ZetaConcrete':'ZeroFree.ZetaConcrete',
'ContinuationInversion':'ZeroFree.Continuation',
'ContinuationContour':'ZeroFree.Continuation',
'ZetaInverse':'ZeroFree.ZetaInverse',
'ZetaSignal':'ZeroFree.ZetaInverse',
'PlainComparison':'ZeroFree.PlainComparison',
'SourceScaling':'ZeroFree.SourceScaling',
}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    out=ROOT/'verification';out.mkdir(exist_ok=True)
    roots=[]
    for module,ns in SCOPES.items():
        text=(ROOT/'ZeroFree'/f'{module}.lean').read_text(encoding='utf-8-sig')
        for name in re.findall(r'^theorem\s+([A-Za-z_][A-Za-z_0-9.]*)',text,re.M):
            roots.append(ns+'.'+name)
        forbidden=re.findall(r'^\s*(?:axiom|opaque)\s|(?<![A-Za-z_])(?:sorry|admit|native_decide|unsafe)(?![A-Za-z_])',re.sub(r'/-[\s\S]*?-/', '',text))
        if forbidden: raise RuntimeError(f'Proof gap or unchecked declaration token in {module}')
    roots=list(dict.fromkeys(roots))
    (out/'roots.json').write_text(json.dumps(roots,indent=2)+'\n',encoding='utf8')
    audit=out/'AxiomAudit.lean'
    audit.write_text('import ZeroFree\n\n'+'\n'.join('#print axioms '+n for n in roots)+'\n',encoding='utf8')
    files=[ROOT/'ZeroFree.lean',ROOT/'lakefile.toml',ROOT/'lake-manifest.json',ROOT/'lean-toolchain']+list((ROOT/'ZeroFree').glob('*.lean'))+[audit,Path(__file__)]
    before={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in files}
    start=time.monotonic()
    build=subprocess.run(['lake','build'],cwd=ROOT,capture_output=True,encoding='utf8',errors='replace')
    (out/'build.log').write_text(build.stdout+build.stderr,encoding='utf8')
    elapsed=round(time.monotonic()-start,3)
    ax=None; ax_elapsed=None; observed=[]; count=0
    if build.returncode==0:
        start=time.monotonic()
        ax=subprocess.run(['lake','env','lean',str(audit.relative_to(ROOT))],cwd=ROOT,capture_output=True,encoding='utf8',errors='replace')
        ax_elapsed=round(time.monotonic()-start,3)
        text=ax.stdout+ax.stderr
        (out/'axioms.log').write_text(text,encoding='utf8')
        blocks=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text)
        independent=re.findall(r'does not depend on any axioms',text)
        count=len(blocks)+len(independent)
        observed=sorted(set(n.strip() for b in blocks for n in b.split(',') if n.strip()))
    after={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in files}
    passed=build.returncode==0 and ax is not None and ax.returncode==0 and count==len(roots) and set(observed)<=ALLOWED and before==after
    result={
        'scope':'Full library build plus fresh transitive audit of all public theorems. Conditional analytic assumptions remain hypotheses.',
        'lean':subprocess.check_output(['lean','--version'],cwd=ROOT,text=True).strip(),
        'mathlib_commit':'51e6992efd06126df61a496bebf8f49482a4e129',
        'build_exit_code':build.returncode,'build_elapsed_seconds':elapsed,
        'audit_exit_code':None if ax is None else ax.returncode,'audit_elapsed_seconds':ax_elapsed,
        'root_count':len(roots),'audited_count':count,'observed_axioms':observed,
        'source_hashes_before':before,'source_hashes_after':after,'inputs_unchanged':before==after,
        'checked':passed,'complete_arithmetic_zero_free_proof':False,
        'open_input':'ZetaInverse.ArithmeticProbeObligation: construct the arithmetic correction and physical probe with low/raw-high estimates; the low-kappa arithmetic induction is pending. The analytic zeta signal, Mellin identity and height closure are proved implications.',
        'independent_kernel_replay':'Separate record; not implied by this build.',
        'logs':{'build':'verification/build.log','axioms':'verification/axioms.log'}
    }
    (out/'lean-verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['checked','build_exit_code','audit_exit_code','root_count','audited_count','observed_axioms','build_elapsed_seconds','audit_elapsed_seconds']},indent=2))
    return 0 if passed else 1
if __name__=='__main__':sys.exit(main())

