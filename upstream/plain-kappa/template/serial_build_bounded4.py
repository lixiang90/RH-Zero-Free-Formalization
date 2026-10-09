from pathlib import Path
import os,sys,json,hashlib,re,subprocess,time,argparse,datetime
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
root=Path(__file__).resolve().parent
if not os.environ.get("LEAN"):raise SystemExit("Run through lake env python serial_build.py ROOT_MODULE")
tool=Path(os.environ["LEAN"]); env=os.environ.copy();env["LEAN_NUM_THREADS"]="2"
srcroots=list(dict.fromkeys(Path(p) for p in env["LEAN_SRC_PATH"].split(os.pathsep) if p))
libroots=[Path(p) for p in env["LEAN_PATH"].split(os.pathsep) if p]
statepath=root/".serial-build"/"state.json";statepath.parent.mkdir(parents=True,exist_ok=True)
state=json.loads(statepath.read_text(encoding="utf-8")) if statepath.exists() else {}
visiting=set(); built={}; plans={}; order=[]
cachedprefixes=("Mathlib","Batteries","Aesop","Qq","ProofWidgets","ImportGraph","LeanSearchClient","Plausible","Lean","Init","Std","Lake")
def source(mod):
    rel=Path(*mod.split(".")).with_suffix(".lean")
    for base in srcroots:
        if (base/rel).is_file():return base,base/rel
    raise RuntimeError("No source for "+mod)
def olean(mod):
    rel=Path(*mod.split(".")).with_suffix(".olean")
    for base in libroots:
        if (base/rel).is_file():return base/rel
    return None
def imports(txt):
    return [im for line in txt.splitlines() if (m:=re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$",line)) for im in m.group(1).split("--")[0].split()]
def plan(mod):
    if mod in plans:return
    if mod in visiting:raise RuntimeError("Import cycle "+mod)
    visiting.add(mod)
    if mod.split(".")[0] in cachedprefixes:
        art=olean(mod)
        if not art:raise RuntimeError("Pinned dependency cache incomplete: "+mod)
        # Trusted downloaded cache at the pinned package version; artifact recorded.
        st=art.stat();plans[mod]={"cached":True,"fingerprint":hashlib.sha256((str(art)+":"+str(st.st_size)+":"+str(st.st_mtime_ns)).encode()).hexdigest(),"artifact":str(art)}
    else:
        base,path=source(mod);raw=path.read_bytes();ims=imports(raw.decode("utf-8-sig"))
        for im in ims:plan(im)
        digest=hashlib.sha256(raw).hexdigest()
        dep=[(im,plans[im]["fingerprint"]) for im in ims]
        fingerprint=hashlib.sha256(json.dumps({"source_sha256":digest,"dependencies":dep,"lean_version":"4.34.1","options":"autoImplicit=false for OAI/PNTA/Rellich only"}).encode()).hexdigest()
        out=base/".lake"/"build"/"lib"/"lean"/Path(*mod.split(".")).with_suffix(".olean")
        plans[mod]={"cached":False,"source":str(path),"base":str(base),"source_sha256":digest,"imports":ims,"fingerprint":fingerprint,"output":str(out)}
        order.append(mod)
    visiting.remove(mod)
parser=argparse.ArgumentParser(description="Bounded topological Lean build. Never run concurrently with another source builder.")
parser.add_argument("--jobs",type=int,choices=(1,2,4),default=4)
parser.add_argument("targets",nargs="+")
args=parser.parse_args();targets=args.targets
for mod in targets:plan(mod)
stamp=time.strftime("%Y%m%d-%H%M%S")+"-bounded4";logdir=statepath.parent/stamp;logdir.mkdir()
(logdir/"plan.json").write_text(json.dumps({"targets":targets,"modules":plans,"order":order,"max_parallel_processes":args.jobs},indent=2),encoding="utf-8")
print(json.dumps({"targets":targets,"compile_plan_modules":len(order),"cached_imports":sum(p["cached"] for p in plans.values()),"threads_per_lean":2,"max_parallel_processes":args.jobs,"log_directory":str(logdir)}),flush=True)
start=time.monotonic();compiled=0;reused=0;done=set();pending=[];active={};failed=[];stopped=False
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def artifacts(output):
    # Include all emitted environment parts, not just the primary olean.
    p=Path(output)
    return {str(q):sha(q) for q in [p,Path(str(p)+".private"),Path(str(p)+".server"),p.with_suffix(".ilean")] if q.is_file()}
def artifact_binding_matches(entry):
    recorded=entry.get("artifact_sha256",{})
    return bool(recorded) and recorded==artifacts(entry["output"])
# Pre-guard legacy state at this stopped, explicit migration epoch.
migration=[]
epoch=datetime.datetime.now(datetime.timezone.utc).isoformat()
for m,entry in state.items():
    if entry.get("exit_code")==0 and not entry.get("artifact_sha256"):
        src=Path(entry["source"]);out=Path(entry["output"])
        if not out.is_file() or sha(src)!=entry["source_sha256"]:
            raise RuntimeError("Cannot bind legacy module: "+m)
        entry["artifact_sha256"]=artifacts(out)
        entry["artifact_binding_epoch"]=epoch
        entry["artifact_binding_kind"]="captured_current_local_state_not_historical_compile"
        migration.append(m)
if migration:
    migration_record={"captured_at_utc":epoch,"modules":migration,"statement":"Current legacy source/output pairs captured now; not hashes recorded at historical compilation.","state_sha256_before":sha(statepath)}
    (logdir/"legacy-artifact-binding.json").write_text(json.dumps(migration_record,indent=2)+"\n",encoding="utf-8")
    replacement=statepath.with_suffix(".json.new")
    replacement.write_text(json.dumps(state,indent=2),encoding="utf-8")
    os.replace(replacement,statepath)
for mod in order:
    p=plans[mod];prior=state.get(mod,{})
    if prior.get("fingerprint")==p["fingerprint"] and Path(p["output"]).exists() and prior.get("exit_code")==0 and artifact_binding_matches(prior) and all(plans[d]["cached"] or d in done for d in p["imports"]):
        done.add(mod);reused+=1
    else:pending.append(mod)
custom=set(order)
deps={m:[d for d in plans[m]["imports"] if d in custom] for m in order}
def build_one(mod):
    p=plans[mod];path=Path(p["source"]);out=Path(p["output"]);logfile=logdir/(mod+".log")
    if hashlib.sha256(path.read_bytes()).hexdigest()!=p["source_sha256"]:
        return dict(p,exit_code=90,wall_seconds=0.0,error="Source changed after planning",log_path=str(logfile))
    direct_artifacts={d:artifacts(plans[d]["output"]) for d in p["imports"] if not plans[d]["cached"]}
    out.parent.mkdir(parents=True,exist_ok=True)
    argv=[str(tool),"-j","2","-o",str(out),"-i",str(out.with_suffix(".ilean"))]
    if mod.split(".")[0] in ("OAI","PrimeNumberTheoremAnd","RellichKondrachov","MathlibExtensions"):argv.append("-DautoImplicit=false")
    argv.append(str(path.relative_to(p["base"])))
    t=time.monotonic()
    with logfile.open("w",encoding="utf-8") as log:
        proc=subprocess.run(argv,cwd=p["base"],env=env,stdout=log,stderr=subprocess.STDOUT)
    entry=dict(p,exit_code=proc.returncode,wall_seconds=round(time.monotonic()-t,6),log_path=str(logfile),command=argv)
    if hashlib.sha256(path.read_bytes()).hexdigest()!=p["source_sha256"]:
        entry["exit_code"]=90;entry["error"]="Source changed during compilation"
    if any(artifacts(plans[d]["output"])!=a for d,a in direct_artifacts.items()):
        entry["exit_code"]=90;entry["error"]="Direct dependency artifact changed during compilation"
    if entry["exit_code"]==0:
        entry["artifact_sha256"]=artifacts(out)
        entry["artifact_binding_kind"]="captured_after_this_compilation"
        entry["direct_dependency_artifact_sha256"]=direct_artifacts
        if not out.is_file():
            entry["exit_code"]=90;entry["error"]="Compiler exit zero without olean"
    return entry
with ThreadPoolExecutor(max_workers=args.jobs) as pool:
    while pending or active:
        if (statepath.parent/"stop-after-current.flag").exists():stopped=True
        if not failed and not stopped:
            available=[m for m in pending if all(d in done for d in deps[m])]
            for mod in available[:max(0,args.jobs-len(active))]:
                pending.remove(mod)
                print(json.dumps({"building":mod,"completed":len(done),"total":len(order),"active_before":len(active)}),flush=True)
                active[pool.submit(build_one,mod)]=mod
        if not active:
            if failed or stopped:break
            raise RuntimeError("No eligible target in an acyclic graph")
        finished,_=wait(active,timeout=5,return_when=FIRST_COMPLETED)
        for future in finished:
            mod=active.pop(future)
            try:entry=future.result()
            except Exception as e:entry=dict(plans[mod],exit_code=91,error=repr(e))
            state[mod]=entry
            replacement=statepath.with_suffix(".json.new")
            replacement.write_text(json.dumps(state,indent=2),encoding="utf-8")
            os.replace(replacement,statepath)
            if entry["exit_code"]==0:
                done.add(mod);compiled+=1
                print(json.dumps({"built":mod,"wall_seconds":entry["wall_seconds"]}),flush=True)
            else:
                failed.append({"module":mod,**entry})
                print(json.dumps({"failed":mod,"exit_code":entry["exit_code"],"log_path":entry.get("log_path"),"error":entry.get("error")}),flush=True)
                log=Path(entry.get("log_path",""))
                if log.is_file():print(log.read_text(encoding="utf-8")[-5000:],flush=True)
summary={"targets":targets,"compiled":compiled,"reused":reused,"wall_seconds":round(time.monotonic()-start,6),"exit_code":failed[0]["exit_code"] if failed else (130 if stopped else 0),"status":"failed" if failed else ("interrupted_pending_resume" if stopped else "compiled_locally_pending_independent_replay"),"failed":[{"module":f["module"],"exit_code":f["exit_code"]} for f in failed],"pending":pending,"all_target_oleans_exist":all(Path(plans[m]["output"]).exists() for m in targets),"lean":"4.34.1","threads_per_lean":2,"max_parallel_processes":args.jobs,"axiom_audit_completed":False,"independent_replay_completed":False}
(logdir/"summary.json").write_text(json.dumps(summary,indent=2)+"\n",encoding="utf-8")
print(json.dumps(summary),flush=True)
raise SystemExit(summary["exit_code"])
