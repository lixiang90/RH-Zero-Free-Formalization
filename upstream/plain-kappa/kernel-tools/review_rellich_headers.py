from pathlib import Path
import re,json,hashlib,subprocess
BASE=Path(r'E:\codex-build\RH-Zero-Free-Formalization\tmp');WORK=BASE/'upstream-plain';PKG=WORK/'.lake/packages/rellich-kondrachov';OUT=BASE/'upstream-kernel'
DIRS=['rellich-h1-compat','rellich-translation-compat','rellich-translation-l2-compat','rellich-translation-h1-compat','rellich-restrict-compat','rellich-approximation-compat','rellich-compactness-compat','rellich-kernels-compat','rellich-arzela-ascoli-compat','rellich-transfer-compat','rellich-euclidean-compat']
def strip_comments(text):
 out=[];i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif text.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif string:
   out.append(text[i])
   if text[i]=='\\' and i+1<len(text):out.append(text[i+1]);i+=2
   else:
    if text[i]=='"':string=False
    i+=1
  elif text.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif text.startswith('--',i):
   j=text.find('\n',i);j=len(text) if j<0 else j;out.extend(' '*(j-i));i=j
  else:
   if text[i]=='"':string=True
   out.append(text[i]);i+=1
 return ''.join(out)
HEAD=re.compile(r'^(?:(?:private|protected|noncomputable|local)\s+)*(?:def|abbrev|theorem|lemma|instance|structure|class|inductive)\b',re.M)
def headers(t):
 t=strip_comments(t);matches=list(HEAD.finditer(t));out=[]
 for ix,m in enumerate(matches):
  piece=t[m.start():matches[ix+1].start() if ix+1<len(matches) else len(t)]
  end=re.search(r':=|\bwhere\b',piece)
  if not end:raise ValueError('No declaration boundary: '+piece[:80])
  out.append(' '.join(piece[:end.start()].split()))
 return out
def context(t):
 lines=strip_comments(t).splitlines();out=[]
 for i,line in enumerate(lines):
  if re.match(r'^(?:variable|namespace|section\b|end\b|open\b|omit\b|include\b|attribute\b|noncomputable section\b)',line):
   piece=[line];j=i+1
   while j<len(lines) and (not lines[j].strip() or lines[j][0].isspace()):
    piece.append(lines[j]);j+=1
   out.append(' '.join(' '.join(piece).split()))
 return out
records=[]
for dirname in DIRS:
 d=WORK/'tmp'/dirname
 if not (d/'metadata.json').is_file():continue
 m=json.loads((d/'metadata.json').read_text());rel=m['relative_source'];baseline=subprocess.check_output(['git','show',m['package_pin']+':'+rel],cwd=PKG).decode();modified=(PKG/rel).read_text(encoding='utf-8')
 b=headers(baseline);a=headers(modified);assert len(b)==len(a),rel
 differences=[]
 for i,(x,y) in enumerate(zip(b,a)):
  if x!=y:
   if dirname=='rellich-approximation-compat' and x.startswith('local instance instIsProbabilityMeasure_kernelMeasure') and y=='lemma '+x[len('local instance '):]:differences.append({'index':i,'baseline_header':x,'modified_header':y,'kind':'registration_only_complete_mathematical_type_identical'})
   else:raise ValueError('Mathematical declaration header changed: '+rel+' '+str((x,y)))
 assert context(baseline)==context(modified),rel+' namespace/context changed'
 records.append({'path':rel,'baseline_lf_sha256':m['baseline_lf_sha256'],'modified_lf_sha256':m['after_lf_sha256'],'top_level_declaration_header_count':len(b),'context_commands_equal':True,'all_mathematical_headers_equal':True,'registration_changes':differences,'baseline_headers':b,'modified_headers':a})
report={'method':'Compare comment-stripped top-level declaration headers before :=/where and namespace/variable/include/omit/open/attribute commands against pinned public Git blobs; exact complete mathematical headers match. Fresh compiled #check types and independent Nano are separate evidence. This is a source-structure comparison, not a Lean parser certificate.','source_package_pin':'70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23','files':records,'file_count':len(records),'all_mathematical_headers_equal':True}
(OUT/'rellich-header-preservation-audit.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'file_count':len(records),'declaration_header_count':sum(v['top_level_declaration_header_count'] for v in records),'changes':sum(len(v['registration_changes']) for v in records)}))
