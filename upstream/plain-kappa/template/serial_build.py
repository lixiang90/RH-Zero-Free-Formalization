from pathlib import Path
import os,sys,json,hashlib,re,subprocess,time
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
    return [im for line in txt.splitlines() if line.startswith("import ") for im in line[7:].split("--")[0].split()]
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
targets=sys.argv[1:]
if not targets:raise SystemExit("Need at least one root module")
for mod in targets:plan(mod)
stamp=time.strftime("%Y%m%d-%H%M%S");logdir=statepath.parent/stamp;logdir.mkdir()
(logdir/"plan.json").write_text(json.dumps({"targets":targets,"modules":plans,"order":order},indent=2),encoding="utf-8")
print(json.dumps({"targets":targets,"compile_plan_modules":len(order),"cached_imports":sum(p["cached"] for p in plans.values()),"threads_per_lean":2,"log_directory":str(logdir)}),flush=True)
start=time.monotonic();compiled=0;reused=0
for n,mod in enumerate(order,1):
    p=plans[mod];out=Path(p["output"])
    prior=state.get(mod,{})
    if prior.get("fingerprint")==p["fingerprint"] and out.exists() and prior.get("exit_code")==0:
        reused+=1;continue
    out.parent.mkdir(parents=True,exist_ok=True)
    logfile=logdir/(mod+".log")
    args=[str(tool),"-j","2","-o",str(out),"-i",str(out.with_suffix(".ilean"))]
    if mod.split(".")[0] in ("OAI","PrimeNumberTheoremAnd","RellichKondrachov","MathlibExtensions"):args.append("-DautoImplicit=false")
    args.append(str(Path(p["source"]).relative_to(p["base"])))
    print(json.dumps({"index":n,"total":len(order),"building":mod}),flush=True)
    t=time.monotonic()
    with logfile.open("w",encoding="utf-8") as log:
        proc=subprocess.run(args,cwd=p["base"],env=env,stdout=log,stderr=subprocess.STDOUT)
    seconds=time.monotonic()-t
    entry=dict(p,exit_code=proc.returncode,wall_seconds=round(seconds,6),log_path=str(logfile),command=args)
    state[mod]=entry
    statepath.write_text(json.dumps(state,indent=2),encoding="utf-8")
    if proc.returncode:
        print(json.dumps({"failed":mod,"exit_code":proc.returncode,"wall_seconds":round(seconds,3),"log_path":str(logfile)}),flush=True)
        print(logfile.read_text(encoding="utf-8"),flush=True)
        raise SystemExit(proc.returncode)
    compiled+=1
    print(json.dumps({"built":mod,"wall_seconds":round(seconds,3)}),flush=True)
summary={"targets":targets,"compiled":compiled,"reused":reused,"wall_seconds":round(time.monotonic()-start,6),"exit_code":0,"all_target_oleans_exist":all(Path(plans[m]["output"]).exists() for m in targets),"lean":"4.34.1","threads_per_lean":2,"axiom_audit_completed":False,"independent_replay_completed":False}
(logdir/"summary.json").write_text(json.dumps(summary,indent=2)+"\n",encoding="utf-8")
print(json.dumps(summary),flush=True)
