from pathlib import Path
import argparse, datetime, hashlib, json
p=argparse.ArgumentParser()
p.add_argument('--session',type=int)
p.add_argument('--driver',default='serial_build_bounded8_v2.py')
p.add_argument('--source-freeze',default='plain-kappa-source-freeze.json')
p.add_argument('--targets-file',required=True)
a=p.parse_args()
root=Path(__file__).resolve().parent
build=root/'.serial-build'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
raw=(build/'state.json').read_bytes()
state=json.loads(raw)
targets_path=Path(a.targets_file).resolve(strict=True)
targets_raw=targets_path.read_bytes()
try:
    targets=json.loads(targets_raw)
except (ValueError, UnicodeError) as error:
    raise SystemExit('Invalid targets JSON: '+str(error))
if not isinstance(targets,list) or not targets:
    raise SystemExit('Targets must be a nonempty JSON list')
if any(not isinstance(target,str) or not target.strip() for target in targets):
    raise SystemExit('Targets must be nonempty strings')
if len(set(targets))!=len(targets):
    raise SystemExit('Duplicate targets are not allowed')
passed=[]; failed=[]
for mod,entry in sorted(state.items()):
    item={'module':mod,'source':entry['source'],'source_sha256':entry['source_sha256'],'imports':entry['imports'],'dependency_fingerprint':entry['fingerprint'],'exit_code':entry['exit_code'],'output':entry['output'],'log_path':entry.get('log_path'),'wall_seconds':entry.get('wall_seconds'),'artifact_sha256':entry.get('artifact_sha256',{}),'artifact_binding_epoch':entry.get('artifact_binding_epoch'),'artifact_binding_kind':entry.get('artifact_binding_kind')}
    if entry['exit_code']==0:
        src=Path(entry['source'])
        item['current_source_matches_record']=src.is_file() and sha(src)==entry['source_sha256']
        artifacts=entry.get('artifact_sha256',{})
        item['current_artifacts_match_record']=bool(artifacts) and all(Path(path).is_file() and sha(Path(path))==digest for path,digest in artifacts.items())
        passed.append(item)
    else: failed.append(item)
freeze_path=root/a.source_freeze
freeze=json.loads(freeze_path.read_text(encoding='utf-8'))
frozen=all(hashlib.sha256((root/Path(*m['module'].split('.')).with_suffix('.lean')).read_text(encoding='utf-8-sig').replace('\r\n','\n').encode()).hexdigest()==m['modified_lf_sha256'] for m in freeze['modules'])
summary_paths=sorted(build.glob('*-bounded*/summary.json'))
latest=summary_paths[-1] if summary_paths else None
summary=json.loads(latest.read_text(encoding='utf-8')) if latest else None
if summary: summary['pending_module_count']=len(summary.pop('pending',[]))
manifest=build/'successful-module-hashes.json'
manifest_raw=(json.dumps(passed,indent=2)+'\n').encode()
matched={v['module']:v for v in passed if v['current_source_matches_record'] and v['current_artifacts_match_record']}
command="& 'C:\\Users\\A\\.elan\\bin\\lake.exe' env 'C:\\Python312\\python.exe' -B -X utf8 "+a.driver+' --jobs 8 '+' '.join(targets)
checkpoint={'captured_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'pending_actual_module_verification','baseline_git_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','lean_version':'4.34.1','mathlib_commit':'d13f23b723b8a846827a245b89c10fc7d3f11612','frozen_oai_source_manifest_path':str(freeze_path),'frozen_oai_source_manifest_sha256':sha(freeze_path),'frozen_oai_patch_sha256':freeze['patch_sha256'],'prior_historical_patch_sha256':freeze.get('prior_historical_patch_sha256'),'frozen_oai_module_count':len(freeze['modules']),'frozen_oai_hashes_match':frozen,'successful_module_count':len(passed),'failed_module_count':len(failed),'successful_current_sources_match':all(v['current_source_matches_record'] for v in passed),'successful_current_artifacts_match':all(v['current_artifacts_match_record'] for v in passed),'build_state_path':str(build/'state.json'),'build_state_sha256':hashlib.sha256(raw).hexdigest(),'successful_module_manifest_path':str(manifest),'successful_module_manifest_sha256':hashlib.sha256(manifest_raw).hexdigest(),'bounded_driver_path':str(root/a.driver),'bounded_driver_sha256':sha(root/a.driver),'latest_summary_path':str(latest) if latest else None,'latest_summary':summary,'targets':targets,'targets_file_absolute_path':str(targets_path),'targets_file_sha256':hashlib.sha256(targets_raw).hexdigest(),'targets_file_before_after_bytes_match':True,'targets_file_validation':'nonempty list of unique nonempty strings','actual_target_compile_record_current':{t:t in matched for t in targets},'certified_existence_compiled':'OAI.NumberTheory.DirichletL.Energy.CertifiedExistence' in matched,'terminal_certificate_checked':False,'independent_replay_completed':False,'last_controller_session':a.session,'controller_status':'stopped_after_first_failure' if failed else 'stopped_at_clean_resumable_boundary','stop_flag_exists':(build/'stop-after-current.flag').exists(),'resume_cwd':str(root),'resume_command':command,'failed_modules':failed,'scope_note':'These records bind actual custom-module source and artifacts. Target full types/axioms and independent replay remain separate required checks; older legacy entries explicitly retain their current-local-state binding epoch.'}
if (build/'state.json').read_bytes()!=raw: raise SystemExit('State changed during capture; retry at stable boundary')
if targets_path.read_bytes()!=targets_raw: raise SystemExit('Targets bytes changed during capture; retry at stable boundary')
manifest.write_bytes(manifest_raw)
out=build/'current-checkpoint.json'
out.write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:checkpoint[k] for k in ['captured_at_utc','successful_module_count','failed_module_count','frozen_oai_hashes_match','successful_current_sources_match','successful_current_artifacts_match','actual_target_compile_record_current','build_state_sha256','bounded_driver_sha256']}))
print(out)
