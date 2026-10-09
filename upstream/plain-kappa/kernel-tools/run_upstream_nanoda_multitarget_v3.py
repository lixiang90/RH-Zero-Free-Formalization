"""Fresh types/axioms and serial independent Nano for already-built upstream roots.

This tool does not build or mutate OAI source or build state. It requires every
custom imported module to have an actual successful build record with matching
source/dependency fingerprints and artifact hashes. It reports complete types
without discarding hypotheses. Full analytic conclusions are never inferred
from checks of smaller root sets.
"""
from pathlib import Path
import argparse,subprocess,json,hashlib,os,sys,time,re,importlib.util
CACHED=('Mathlib','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Lean','Init','Std','Lake')
AXIOMS={'propext','Quot.sound','Classical.choice'}
NAME=re.compile(r"(?:[^\W\d]|_)[\w']*(?:\.(?:[^\W\d]|_)[\w']*)*",re.UNICODE)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def encode(v):return json.dumps(v,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()
def save(p,v):p.write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def import_names(raw):return [n for line in raw.decode('utf-8-sig').splitlines() if (m:=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$',line)) for n in m.group(1).split('--')[0].split()]
def artifacts(out):return {str(p):sha(p) for p in (out,Path(str(out)+'.private'),Path(str(out)+'.server'),out.with_suffix('.ilean')) if p.is_file()}
def strict_axes(text,roots):
 found=[]
 for m in re.finditer(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",text,re.M):
  found.append({'declaration':m[1],'axioms':[n.strip() for n in (m[2] or '').split(',') if n.strip()]})
 if len(found)!=len(roots) or {v['declaration'] for v in found}!=set(roots):raise ValueError('Fresh audit names/count mismatch')
 for v in found:
  if not set(v['axioms'])<=AXIOMS:raise ValueError('Unpermitted transitive axioms: '+str(v))
  if not re.search(r'^@?'+re.escape(v['declaration'])+r'(?:\.\{|\s|:)',text,re.M):raise ValueError('Fresh full type output missing: '+v['declaration'])
 if re.search(r"declaration uses ['`]?sorry|sorryAx|unknown constant",text):raise ValueError('Fresh output contains a failed proof or declaration')
 return {'declaration_count':len(found),'checks':found,'only_standard_axioms':True}

PNTA_MODULE='PrimeNumberTheoremAnd.Wiener'
PNTA_PIN='c39a751132c88b6e8080b74c74023fd95b3d8be0'
PNTA_RAW='963151c22caeb12f5c203ae944961629bfe7840915519255d79220f415ca0fbf'
PNTA_LF='7bd40c9cffedc1d9a0f675ea971c6719e490b1b106807459d549145f30d70f05'
PNTA_HOLES=('prelim_decay_2','prelim_decay_3')
PNTA_WARNING_LINES=['PrimeNumberTheoremAnd/Wiener.lean:325:8: warning: declaration uses `sorry`','PrimeNumberTheoremAnd/Wiener.lean:344:8: warning: declaration uses `sorry`']
def validate_pnta_policy(module,raw,log_text,roots,pin,public_blob):
 if module!=PNTA_MODULE:raise ValueError('Unpermitted proof warning module')
 raw_sha=hashlib.sha256(raw).hexdigest();lf=raw.replace(b'\r\n',b'\n')
 if pin!=PNTA_PIN:raise ValueError('PNTA fixed pin changed')
 if raw_sha not in (PNTA_RAW,PNTA_LF) or hashlib.sha256(lf).hexdigest()!=PNTA_LF:raise ValueError('PNTA exact source changed')
 if public_blob!=lf or hashlib.sha256(public_blob).hexdigest()!=PNTA_LF:raise ValueError('PNTA public Git blob mismatch')
 if set(roots)&set(PNTA_HOLES):raise ValueError('Known unproved auxiliary was selected')
 lines=log_text.replace('\\','/').splitlines()
 if lines!=PNTA_WARNING_LINES:raise ValueError('PNTA exact warning declarations/positions/count changed')
 src_lines=lf.decode('utf8').splitlines()
 for name,line,proof_line in [('prelim_decay_2',325,327),('prelim_decay_3',344,347)]:
  if not re.match(r'^theorem '+name+r'\b',src_lines[line-1]) or 'sorry' not in src_lines[proof_line-1]:raise ValueError('PNTA exact declaration proof positions changed')
 return {'module':module,'package_url':'https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git','package_pin':pin,'raw_actual_source_sha256':raw_sha,'canonical_lf_sha256':PNTA_LF,'unproved_auxiliary_declarations':list(PNTA_HOLES),'allowed_exact_warning_lines':lines,'only_unselected_imported_auxiliary_warnings_allowed':True,'whole_import_environment_hole_free':False}
def actual_pnta_policy(module,base,raw,log_text,roots):
 pin=subprocess.check_output(['git','-C',str(base),'rev-parse','HEAD'],text=True,encoding='utf8').strip()
 blob=subprocess.check_output(['git','-C',str(base),'cat-file','blob',PNTA_PIN+':PrimeNumberTheoremAnd/Wiener.lean'])
 return validate_pnta_policy(module,raw,log_text,roots,pin,blob)
def check_export_hole_absence(export_path,expected_sha):
 if sha(export_path)!=expected_sha:raise ValueError('Export artifact digest mismatch')
 hits=[];blocked=set(PNTA_HOLES)|{'sorryAx'}
 with export_path.open('rb') as f:
  for line_number,line in enumerate(f,1):
   if not any(n.encode() in line for n in blocked):continue
   node=json.loads(line);name=node.get('str')
   if 'in' in node and isinstance(name,dict) and name.get('pre')==0 and name.get('str') in blocked:hits.append({'line':line_number,'name':name['str'],'name_id':node['in']})
 if hits:raise ValueError('Unproved declaration or sorryAx occurs in selected kernel export: '+str(hits))
 return {'export_sha256':expected_sha,'blocked_global_names':sorted(blocked),'blocked_name_occurrences':hits,'selected_export_contains_neither_unproved_auxiliaries_nor_sorryAx':True}

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--project',required=True,type=Path);ap.add_argument('--module',action='append',required=True);ap.add_argument('--root',action='append',required=True)
 ap.add_argument('--exporter-repo',required=True,type=Path);ap.add_argument('--exporter-bin',required=True,type=Path)
 ap.add_argument('--nanoda-repo',required=True,type=Path);ap.add_argument('--nanoda-bin',required=True,type=Path)
 ap.add_argument('--driver',type=Path,default=Path(__file__).with_name('verify_independent_nanoda_34.py'))
 ap.add_argument('--scope',required=True);ap.add_argument('--label',default='upstream-target')
 a=ap.parse_args();project=a.project.resolve();roots=a.root;modules=a.module
 if not all(NAME.fullmatch(n) for n in modules+roots) or len(set(roots))!=len(roots) or len(set(modules))!=len(modules):ap.error('Need distinct valid declaration names')
 if not re.fullmatch(r'[A-Za-z0-9_-]+',a.label):ap.error('Invalid output label')
 if not project.is_dir():ap.error('Project missing')
 os.chdir(project)
 stage=project/'tmp/verification'/(a.label+'-'+time.strftime('%Y%m%d-%H%M%S'));stage.mkdir(parents=True,exist_ok=False)
 version=subprocess.check_output(['lean','--version'],cwd=project,text=True,encoding='utf-8').strip()
 if 'version 4.34.1' not in version:raise ValueError('Pinned Lean 4.34.1 required')
 query=subprocess.run(['lake','--no-cache','env',sys.executable,'-c','import os,json;print(json.dumps(dict(os.environ)))'],cwd=project,capture_output=True,text=True,encoding='utf-8')
 if query.returncode:raise ValueError('Pinned Lake environment unavailable')
 env=json.loads(query.stdout)
 srcroots=list(dict.fromkeys(Path(p) for p in env['LEAN_SRC_PATH'].split(os.pathsep) if p));libroots=[Path(p) for p in env['LEAN_PATH'].split(os.pathsep) if p]
 statepath=project/'.serial-build/state.json';state=json.loads(statepath.read_text(encoding='utf-8'));plans={};order=[];visiting=set();files={};known_import_holes=[]
 def lookup(mod,bases,suffix):
  rel=Path(*mod.split('.')).with_suffix(suffix)
  for base in bases:
   if (base/rel).is_file():return base,base/rel
  raise ValueError('Missing '+suffix+' for '+mod)
 def visit(mod):
  if mod in plans:return
  if mod in visiting:raise ValueError('Import cycle')
  visiting.add(mod)
  if mod.split('.')[0] in CACHED:
   base,out=lookup(mod,libroots,'.olean');st=out.stat();fp=hashlib.sha256((str(out)+':'+str(st.st_size)+':'+str(st.st_mtime_ns)).encode()).hexdigest()
   plans[mod]={'cached':True,'fingerprint':fp,'artifact':str(out)}
   for p in artifacts(out):files['cached:'+p]=Path(p)
  else:
   base,p=lookup(mod,srcroots,'.lean');raw=p.read_bytes();ims=import_names(raw)
   for im in ims:visit(im)
   digest=hashlib.sha256(raw).hexdigest();deps=[(im,plans[im]['fingerprint']) for im in ims]
   fp=hashlib.sha256(json.dumps({'source_sha256':digest,'dependencies':deps,'lean_version':'4.34.1','options':'autoImplicit=false for OAI/PNTA/Rellich only'}).encode()).hexdigest()
   out=base/'.lake/build/lib/lean'/Path(*mod.split('.')).with_suffix('.olean');actual=artifacts(out);entry=state.get(mod,{})
   if entry.get('exit_code')!=0 or entry.get('source_sha256')!=digest or entry.get('fingerprint')!=fp:raise ValueError('Actual successful source/dependency build record missing or stale: '+mod)
   if not actual or entry.get('artifact_sha256')!=actual:raise ValueError('Actual compiled artifact binding missing or changed: '+mod)
   if Path(entry['source']).resolve()!=p.resolve() or Path(entry['output']).resolve()!=out.resolve():raise ValueError('Compiled source/artifact path mismatch: '+mod)
   for im,bound in entry.get('direct_dependency_artifact_sha256',{}).items():
    if im not in ims or plans[im]['cached']:raise ValueError('Invalid direct dependency binding: '+mod)
    if bound!=artifacts(Path(plans[im]['output'])):raise ValueError('Direct compiled dependency binding changed: '+mod)
   files['custom-source:'+mod]=p
   for art in actual:files['custom-artifact:'+art]=Path(art)
   if entry.get('log_path'):
    log=Path(entry['log_path']);files['build-log:'+mod]=log
    log_text=log.read_text(encoding='utf-8',errors='replace')
    if re.search(r"declaration uses ['`]?sorry|sorryAx",log_text):
     policy=actual_pnta_policy(mod,base,raw,log_text,roots);policy.update({'source_path':str(p),'actual_build_log_path':str(log),'actual_build_log_sha256':sha(log)});known_import_holes.append(policy)
   plans[mod]={'cached':False,'source':str(p),'source_sha256':digest,'fingerprint':fp,'imports':ims,'output':str(out),'base':str(base),'artifact_sha256':actual,'build_record':entry};order.append(mod)
  visiting.remove(mod)
 for module in modules:visit(module)
 selected={m:state[m] for m in order};extract=stage/'actual-build-state-extract.json'
 save(extract,{'state_path':str(statepath),'observed_full_state_sha256':sha(statepath),'selected_records':selected,'note':'Other controller records may advance; selected records must remain exact.'});files['actual-build-state-extract']=extract
 bases={project}|{Path(plans[m]['base']) for m in order}
 for base in bases:
  for n in ('lean-toolchain','lakefile.lean','lakefile.toml','lake-manifest.json'):
   p=base/n
   if p.is_file():files['config:'+str(p)]=p
 files['audit-runner']=Path(__file__).resolve();files['nano-driver']=a.driver.resolve()
 save(stage/'closure-plan.json',{'modules':modules,'custom_count':len(order),'cached_frontier_count':sum(p['cached'] for p in plans.values()),'plans':plans})
 files['closure-plan']=stage/'closure-plan.json'
 def snap():return {k:sha(p) for k,p in files.items()}
 before=snap()
 def guard(label):
  after=snap()
  if before!=after:raise ValueError('Closure sources/configuration/artifacts changed at '+label)
  current=json.loads(statepath.read_text(encoding='utf-8'))
  if selected!={m:current.get(m) for m in order}:raise ValueError('Selected actual build records changed at '+label)
  for hole in known_import_holes:
   plan=plans[hole['module']];actual_pnta_policy(hole['module'],Path(plan['base']),Path(plan['source']).read_bytes(),Path(hole['actual_build_log_path']).read_text(encoding='utf8'),roots)
  return after
 aggregate='UpstreamNano_'+time.strftime('%Y%m%d_%H%M%S');aggregate_source=project/(aggregate+'.lean');aggregate_olean=project/'.lake/build/lib/lean'/(aggregate+'.olean')
 aggregate_source.write_text(''.join('import '+m+'\n' for m in modules),encoding='utf-8',newline='\n')
 start=time.monotonic();compile_log=stage/'aggregate-compile.log'
 with compile_log.open('wb') as out:p=subprocess.run(['lake','env','lean','-j1','-o',str(aggregate_olean),aggregate_source.name],cwd=project,stdout=out,stderr=subprocess.STDOUT)
 if p.returncode:raise ValueError('Fresh aggregate real compilation failed; see '+str(compile_log))
 guard('fresh aggregate compile')
 files['aggregate-source']=aggregate_source;files['aggregate-olean']=aggregate_olean;files['aggregate-log']=compile_log;before=snap()
 audit=project/(aggregate+'Audit.lean');audit.write_text('import '+aggregate+'\nset_option pp.universes true\nset_option pp.fullNames true\nset_option pp.explicit true\nset_option pp.all true\nset_option pp.maxSteps 1000000\n\n'+'\n'.join('set_option pp.universes true\n#check @'+n+'\nset_option pp.universes false\n#print axioms '+n for n in roots)+'\n',encoding='utf-8',newline='\n')
 auditlog=stage/'fresh-types-and-axioms.log'
 with auditlog.open('wb') as out:p=subprocess.run(['lake','env','lean','-j1',audit.name],cwd=project,stdout=out,stderr=subprocess.STDOUT)
 if p.returncode:raise ValueError('Fresh #check/#print real process failed; see '+str(auditlog))
 audited=strict_axes(auditlog.read_text(encoding='utf-8'),roots);guard('fresh type/axiom audit')
 files['audit-source']=audit;files['audit-log']=auditlog;before=snap()
 output=Path('verification')/(a.label+'-'+stage.name.rsplit('-',2)[-2]+'-'+stage.name.rsplit('-',1)[-1]+'-nano.json')
 command=[sys.executable,'-B','-X','utf8',str(a.driver),'--project',str(project),aggregate]
 for n in roots:command.extend(['--root',n])
 command.extend(['--source',str(aggregate_source),'--olean',str(aggregate_olean),'--lean-path',str(project/'.lake/build/lib/lean'),'--exporter-repo',str(a.exporter_repo),'--exporter-bin',str(a.exporter_bin),'--nanoda-repo',str(a.nanoda_repo),'--nanoda-bin',str(a.nanoda_bin),'--threads','1','--output',str(output),'--scope',a.scope])
 print(json.dumps({'fresh_root_count':len(roots),'custom_closure_count':len(order),'phase':'actual serial independent Nano','stage':str(stage)},ensure_ascii=False),flush=True)
 p=subprocess.run(command,cwd=project);after=guard('serial independent replay')
 nano=json.loads((project/output).read_text(encoding='utf-8')) if (project/output).is_file() else {}
 passed=p.returncode==0 and nano.get('nano_check_passed') is True
 export_hole_audit=None
 if passed:
  if set(nano.get('observed_axioms',[]))-AXIOMS:raise ValueError('Nano observed unpermitted axiom')
  export_path=Path(nano['input_paths']['export']);export_hole_audit=check_export_hole_absence(export_path,nano['sha256_after']['export'])
 record={'runner_version':'v3_exact_unused_PNTA_auxiliary_exception','known_unproved_imported_auxiliaries':known_import_holes,'whole_import_environment_hole_free':not bool(known_import_holes),'selected_export_unproved_auxiliary_absence_audit':export_hole_audit,'scope':a.scope,'target_module':modules[0] if len(modules)==1 else None,'target_modules':modules,'selected_roots':roots,'compiler':version,'custom_closure_count':len(order),'cached_frontier_count':sum(v['cached'] for v in plans.values()),'fresh_types_include_all_hypotheses':True,'fresh_audit':audited,'fresh_aggregate_recompiled':True,'all_selected_actual_build_records_unchanged':True,'actual_build_record_kinds':{m:state[m].get('artifact_binding_kind') for m in order},'sha256_before':before,'sha256_after':after,'input_paths':{k:str(v) for k,v in files.items()},'all_inputs_unchanged':True,'actual_nano_driver_command':command,'actual_nano_driver_exit_code':p.returncode,'nano_record_path':str(output),'nano_record_sha256':sha(project/output) if (project/output).is_file() else None,'independent_replay_passed':passed,'elapsed_seconds':round(time.monotonic()-start,3),'full_analytic_chain_verified':False}
 save(stage/'strict-replay-result.json',record)
 print(json.dumps({'result':str(stage/'strict-replay-result.json'),'independent_replay_passed':passed},ensure_ascii=False),flush=True)
 raise SystemExit(0 if passed else 1)
if __name__=='__main__':main()
