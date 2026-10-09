"""Prepare a pinned, isolated upstream low-kappa development.

All patches are inputs from an explicitly frozen manifest. This tool does not
declare them proved. Run targeted compilation and fresh type/axiom audits with
--install --build; independent replay is still a separate required check.
"""
from pathlib import Path
import argparse,subprocess,json,hashlib,shutil,time,os,sys,re
COMMIT="fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
REPO="https://github.com/openai/math"
TEMPLATE=Path(__file__).resolve().parent/"template"
def sha(raw):return hashlib.sha256(raw).hexdigest()
def run(args,cwd,log=None):
    started=time.monotonic()
    if log:
        with Path(log).open("w",encoding="utf-8") as f:p=subprocess.run(args,cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
    else:p=subprocess.run(args,cwd=cwd)
    r={"command":args,"exit_code":p.returncode,"wall_seconds":round(time.monotonic()-started,6)}
    if log:r["log_path"]=str(log);r["log_sha256"]=sha(Path(log).read_bytes())
    if p.returncode:raise RuntimeError(json.dumps(r))
    return r
def imports(txt):
    # All pinned OAI imports occur on one line, before the namespace.
    return [i for line in txt.splitlines() if line.startswith("import ") for i in line[7:].split("--")[0].split()]
def contained(path,base):
    p=path.resolve();b=base.resolve()
    if p!=b and b not in p.parents:raise ValueError("Path outside intended directory: "+str(p))
    return p
def validate_lean_path(path):
    p=Path(path)
    if p.is_absolute() or ".." in p.parts or not p.parts or p.parts[0]!="OAI" or p.suffix!=".lean":
        raise ValueError("Expected a relative OAI .lean file: "+str(path))
    return p
ALLOWED_AXIOMS={"propext","Classical.choice","Quot.sound"}
def validate_axiom_log(text,declarations):
    if not declarations or len(set(declarations))!=len(declarations):
        raise ValueError("Need distinct declarations for a fresh axiom audit")
    found=[]
    pattern=r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$"
    for m in re.finditer(pattern,text,re.M):
        axes=[x.strip() for x in (m.group(2) or "").split(",") if x.strip()]
        found.append({"declaration":m.group(1),"axioms":axes})
    if len(found)!=len(declarations) or {x["declaration"] for x in found}!=set(declarations):
        raise ValueError("Fresh axiom output declaration count or names mismatch: expected="+repr(declarations)+" found="+repr(found))
    for check in found:
        if not set(check["axioms"])<=ALLOWED_AXIOMS:
            raise ValueError("Unapproved transitive axioms: "+str(check))
        if not re.search(r"^"+re.escape(check["declaration"])+r"(?:\.\{|\s|:)",text,re.M):
            raise ValueError("Fresh #check type output missing: "+check["declaration"])
    return {"declaration_count":len(found),"checks":found,"only_standard_axioms":True}
def fresh_audit(lake,out,targets,declarations,label):
    for name in declarations:
        if not all(p.isidentifier() for p in name.split(".")):raise ValueError("Invalid declaration name")
    audit="\n".join("import "+m for m in targets)+"\n\n"+"\n".join("#check "+n+"\n#print axioms "+n for n in declarations)+"\n"
    file=out/(label+".lean");file.write_text(audit,encoding="utf-8")
    log=out/(label+".log")
    stage=run([lake,"env","lean","-j1",file.name],out,log)
    result=validate_axiom_log(log.read_text(encoding="utf-8"),declarations)
    result["audit_source_sha256"]=sha(file.read_bytes());result["log_sha256"]=sha(log.read_bytes())
    return stage,result
def apply_external_compatibility(manifest_path,out):
    data=json.loads(manifest_path.read_text(encoding="utf-8"))
    checked=[]
    for package in data.get("packages",[]):
        pkgname=package["name"]
        if not pkgname.replace("-","").isidentifier():raise ValueError("Invalid package name")
        pkg=contained(out/".lake"/"packages"/pkgname,out)
        pin=package["commit"]
        if not re.fullmatch(r"[0-9a-f]{40}",pin):raise ValueError("Expected exact package Git commit")
        actual=subprocess.check_output(["git","rev-parse","HEAD"],cwd=pkg,text=True).strip()
        if actual!=pin:raise ValueError("External dependency commit mismatch")
        already=[]
        for f in package["files"]:
            rel=Path(f["path"])
            if rel.is_absolute() or ".." in rel.parts:raise ValueError("Unsafe dependency file path")
            file=contained(pkg/rel,pkg)
            baseline=subprocess.check_output(["git","show",pin+":"+rel.as_posix()],cwd=pkg)
            if sha(baseline)!=f["baseline_sha256"]:raise ValueError("Dependency Git baseline digest mismatch")
            raw=file.read_bytes().replace(b"\r\n",b"\n")
            if sha(raw)==f["baseline_sha256"]:already.append(False)
            elif sha(raw)==f["modified_sha256"]:already.append(True)
            else:raise ValueError("Unexpected dependency working-copy source")
            file.write_bytes(raw)
        if any(already) and not all(already):raise ValueError("Partially applied compatibility patch")
        for patch in package["patches"]:
            path=contained(manifest_path.parent/patch["file"],manifest_path.parent)
            if sha(path.read_bytes())!=patch["sha256"]:raise ValueError("Dependency patch digest mismatch")
            if not all(already):
                run(["git","-c","core.autocrlf=false","apply","--check",str(path)],pkg);run(["git","-c","core.autocrlf=false","apply",str(path)],pkg)
        for f in package["files"]:
            if sha((pkg/f["path"]).read_bytes())!=f["modified_sha256"]:raise ValueError("Patched dependency digest mismatch")
        changed=subprocess.check_output(["git","diff","--name-only",pin],cwd=pkg,text=True).splitlines()
        if not set(changed)<={f["path"] for f in package["files"]}:raise ValueError("Unlisted dependency modification")
        checked.append(package)
    return {"status":"source_patches_applied_pending_kernel_audit","manifest_sha256":sha(manifest_path.read_bytes()),"packages":checked}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source",required=True,type=Path,help="Existing OpenAI/math Git checkout, or new fetch directory")
    parser.add_argument("--fetch",action="store_true",help="Fetch the exact public Git commit into an absent source directory")
    parser.add_argument("--destination",required=True,type=Path,help="New empty build directory")
    parser.add_argument("--patch-manifest",type=Path,help="Frozen reviewed manifest; omission prepares baseline only")
    parser.add_argument("--external-compat-manifest",type=Path)
    parser.add_argument("--apply-external-only",action="store_true",help="Apply exact dependency patches to an existing prepared project, without source preparation or compilation")
    parser.add_argument("--target",action="append",default=[])
    parser.add_argument("--declaration",action="append",default=[])
    parser.add_argument("--install",action="store_true")
    parser.add_argument("--build",action="store_true")
    parser.add_argument("--lake",default="lake")
    parser.add_argument("--jobs",type=int,choices=(1,2),default=1)
    a=parser.parse_args()
    src=a.source.resolve();out=a.destination.resolve()
    if src==out or src in out.parents or out in src.parents:
        raise ValueError("Source and destination must be disjoint")
    if a.fetch:
        if src.exists():raise ValueError("--fetch requires an absent directory; existing data is preserved")
        src.mkdir(parents=True)
        run(["git","init"],src)
        run(["git","remote","add","origin",REPO],src)
        run(["git","config","remote.origin.promisor","true"],src)
        run(["git","config","remote.origin.partialclonefilter","blob:none"],src)
        run(["git","fetch","--depth","1","--filter=blob:none","origin",COMMIT],src)
    # Objects are read from COMMIT rather than trusting source working-tree files.
    verified=subprocess.check_output(["git","rev-parse",COMMIT+"^{commit}"],cwd=src,text=True).strip()
    if verified!=COMMIT:raise ValueError("Pinned commit does not resolve")
    if a.apply_external_only:
        if not a.external_compat_manifest:raise ValueError("Need --external-compat-manifest")
        result=apply_external_compatibility(a.external_compat_manifest,out)
        result["tool_source_sha256"]=sha(Path(__file__).read_bytes())
        (out/"external-compatibility-application.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
        print(json.dumps({"directory":str(out),"status":result["status"],"package_count":len(result["packages"])},indent=2))
        return
    if out.exists() and any(out.iterdir()):
        raise ValueError("Use a new empty destination; existing files are preserved")
    out.mkdir(parents=True,exist_ok=True)
    run(["git","init"],out) # isolate git apply from a surrounding repository
    run(["git","config","core.autocrlf","false"],out)
    for name in ("lakefile.lean","lake-manifest.json","lean-toolchain","serial_build.py","serial_build_bounded.py"):
        shutil.copyfile(TEMPLATE/name,out/name)
    manifest=json.loads(a.patch_manifest.read_text(encoding="utf-8")) if a.patch_manifest else None
    if manifest and manifest.get("upstream_commit")!=COMMIT:raise ValueError("Patch manifest baseline mismatch")
    targets=a.target or (manifest.get("targets",[]) if manifest else []) or ["OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength"]
    declarations=a.declaration or (manifest.get("declarations",[]) if manifest else [])
    tracked={}
    cat=subprocess.Popen(["git","cat-file","--batch"],cwd=src,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def blob(mod):
        rel=Path(*mod.split(".")).with_suffix(".lean").as_posix()
        if not rel.startswith("OAI/"):raise ValueError("Only OAI modules are copied: "+mod)
        cat.stdin.write((COMMIT+":lean/"+rel+"\n").encode());cat.stdin.flush()
        header=cat.stdout.readline().decode().strip().split()
        if len(header)!=3 or header[1]!="blob":raise RuntimeError("Missing pinned source: "+rel)
        size=int(header[2]);raw=cat.stdout.read(size)
        if cat.stdout.read(1)!=b"\n":raise RuntimeError("Invalid git cat-file stream")
        return rel,raw,header[0]
    pending=list(targets)
    if manifest:
        for f in manifest.get("files",[]):
            rel=validate_lean_path(f["path"]);pending.append(".".join(rel.with_suffix("").parts))
    while pending:
        mod=pending.pop()
        if mod in tracked:continue
        rel,raw,oid=blob(mod);dst=contained(out/rel,out);dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(raw)
        ims=imports(raw.decode("utf-8-sig"))
        tracked[mod]={"path":rel,"git_blob":oid,"baseline_sha256":sha(raw),"baseline_imports":ims}
        pending.extend(i for i in ims if i.startswith("OAI."))
    cat.stdin.close();cat.wait()
    applied=[]
    if manifest:
        for f in manifest.get("files",[]):
            rel=validate_lean_path(f["path"])
            if sha((out/rel).read_bytes())!=f["baseline_sha256"]:raise ValueError("Unexpected baseline "+str(rel))
        for entry in manifest.get("patches",[]):
            path=contained(a.patch_manifest.parent/entry["file"],a.patch_manifest.parent)
            if sha(path.read_bytes())!=entry["sha256"]:raise ValueError("Patch hash mismatch")
            run(["git","apply","--check",str(path)],out)
            run(["git","apply",str(path)],out);applied.append(entry)
        for f in manifest.get("files",[]):
            rel=validate_lean_path(f["path"])
            if sha((out/rel).read_bytes())!=f["modified_sha256"]:raise ValueError("Unexpected patched source "+str(rel))
        listed={f["path"] for f in manifest.get("files",[])}
        expected_files={t["path"] for t in tracked.values()}
        actual_files={p.relative_to(out).as_posix() for p in (out/"OAI").rglob("*.lean")}
        if actual_files!=expected_files:
            raise ValueError("Patch creates or removes unmanifested OAI files")
        for mod,t in tracked.items():
            new_imports=imports((out/t["path"]).read_text(encoding="utf-8-sig"))
            if any(i.startswith("OAI.") and i not in tracked for i in new_imports):
                raise ValueError("Patch introduces an unprepared OAI import: "+mod)
        for mod,t in tracked.items():
            modified=sha((out/t["path"]).read_bytes())!=t["baseline_sha256"]
            if modified and t["path"] not in listed:raise ValueError("Unlisted modified file "+t["path"])
    for mod,t in tracked.items():t["modified_sha256"]=sha((out/t["path"]).read_bytes())
    record={"upstream_repo":REPO,"upstream_commit":COMMIT,"sources":tracked,"targets":targets,"patches":applied,"status":"prepared_pending_compile","independent_kernel_replay_completed":False,"axiom_audit_completed":False,"stages":[]}
    recordfile=out/"capsule-reproduction.json"
    def save():recordfile.write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
    save()
    def snapshot():
        paths={t["path"] for t in tracked.values()}
        if {p.relative_to(out).as_posix() for p in (out/"OAI").rglob("*.lean")}!=paths:
            raise ValueError("Source file set changed")
        result={name:sha((out/name).read_bytes()) for name in sorted(paths)}
        for name in ("lakefile.lean","lake-manifest.json","lean-toolchain"):result[name]=sha((out/name).read_bytes())
        if a.external_compat_manifest:
            ext=json.loads(a.external_compat_manifest.read_text(encoding="utf-8"))
            for pkg in ext["packages"]:
                for f in pkg["files"]:
                    rel=Path(".lake/packages")/pkg["name"]/f["path"]
                    result[rel.as_posix()]=sha((out/rel).read_bytes())
        return result
    if a.install:
        record["stages"].append(run([a.lake,"exe","cache","get"],out,out/"dependency-cache.log"));save()
    if a.external_compat_manifest:
        record["external_compatibility"]={"status":"pending_install","manifest_sha256":sha(a.external_compat_manifest.read_bytes())}
        if a.install or a.build:
            record["external_compatibility"]=apply_external_compatibility(a.external_compat_manifest,out)
        save()
    if a.build:
        before=snapshot();record["build_source_snapshot"]=before;save()
        buildargv=[a.lake,"env",sys.executable,"-B","-X","utf8"]+ (["serial_build_bounded.py","--jobs","2"] if a.jobs==2 else ["serial_build.py"])+targets
        record["stages"].append(run(buildargv,out,out/"targeted-serial-build.log"));save()
        if snapshot()!=before:raise ValueError("Source hashes changed during build")
        if declarations:
            stage,audit=fresh_audit(a.lake,out,targets,declarations,"FreshLowKappaAudit")
            record["stages"].append(stage)
            if snapshot()!=before:raise ValueError("Source hashes changed during fresh audit")
            record["axiom_audit"]=audit;record["axiom_audit_completed"]=True
            record["audit_source_snapshot"]=snapshot()
            record["status"]="compiled_locally_pending_independent_replay"
        else:record["status"]="compiled_pending_fresh_axiom_audit_and_independent_replay"
        if a.external_compat_manifest:
            ext=json.loads(a.external_compat_manifest.read_text(encoding="utf-8"))
            extdecls=[n for pkg in ext["packages"] for n in pkg.get("declarations",[])]
            exttargets=[n for pkg in ext["packages"] for n in pkg.get("targets",[])]
            if extdecls:
                stage,audit=fresh_audit(a.lake,out,exttargets,extdecls,"FreshExternalCompatibilityAudit")
                record["stages"].append(stage)
                if snapshot()!=before:raise ValueError("Source hashes changed during dependency audit")
                record["external_compatibility"]["fresh_axiom_audit"]=audit
                record["external_compatibility"]["status"]="compiled_locally_pending_independent_replay"
        save()
    print(json.dumps({"directory":str(out),"modules":len(tracked),"targets":targets,"status":record["status"],"record":str(recordfile)},indent=2))
if __name__=="__main__":main()
