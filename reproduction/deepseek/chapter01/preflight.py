#!/usr/bin/env python3
"""Operator-side validation only: no model calls, no supplied mathematical targets."""
from pathlib import Path
import subprocess,json,hashlib,os
from datetime import datetime
from zoneinfo import ZoneInfo
BASE=Path(__file__).resolve().parent; W=BASE/'workspace'; PROJECT=BASE.parents[1]
CONFIG=json.loads((W/'run/experiment.json').read_text()); checks=[]
def run(args,isolated=False):
 p=subprocess.run(([str(BASE/'isolated-command.sh')] if isolated else [])+[str(x) for x in args],cwd=W,text=True,capture_output=True,timeout=300)
 return p
def check(name,action):
 try:
  evidence=action(); checks.append(dict(name=name,status='PASS',evidence=evidence))
 except Exception as e: checks.append(dict(name=name,status='FAIL',error=str(e)))
def eq(a,b):
 if a!=b: raise ValueError(f'expected {b!r}, got {a!r}')
 return a
def source(): return eq(hashlib.sha256((W/CONFIG['source_pdf']).read_bytes()).hexdigest(),CONFIG['source_sha256'])
def baseline():
 authored=[]
 for root,dirs,files in os.walk(W):
  dirs[:]=[d for d in dirs if d not in ['.lake','.git']]
  for name in files:
   f=Path(root)/name
   if f.is_symlink(): raise ValueError('Unexpected input symlink outside dependency cache')
   if name.endswith('.lean'): authored.append(str(f.relative_to(W)))
 eq(sorted(authored),['lean/HDP.lean']); eq((W/'lean/HDP.lean').read_text(),'import Mathlib\n')
 if (W/'workflow').exists() or (W/'.dsh').exists(): raise ValueError('Unexpected workflow/skill input')
 return {'initial_lean_files':authored,'no_chapter_declarations':True}
def deps():
 eq((W/'lean/lean-toolchain').read_text().strip(),CONFIG['lean_toolchain']); rows=[]
 for x in json.loads((W/'lean/lake-manifest.json').read_text())['packages']:
  d=W/'lean/.lake/packages'/x['name']
  q=run(['git','-C',d,'rev-parse','HEAD']); eq(q.returncode,0); eq(q.stdout.strip(),x['rev'])
  q=run(['git','-C',d,'status','--porcelain','--untracked-files=normal']); eq(q.returncode,0); eq(q.stdout.strip(),'')
  rows.append({'package':x['name'],'revision':x['rev'],'source_worktree_clean':True})
 return rows
def proof_environment():
 q=run([W/'tools/lake.sh','build','HDP'],True); eq(q.returncode,0)
 return 'The initial HDP project containing only import Mathlib builds inside the outer sandbox.'
def read_fence():
 node='/Users/gspyrou/.nvm/versions/node/v24.19.0/bin/node'
 # openSync tests the permission without reading or printing credential contents.
 code='const fs=require("fs"); let denied=false; try {const f=fs.openSync(process.argv[1],"r");fs.closeSync(f)}catch(e){denied=["EPERM","EACCES"].includes(e.code)};process.exit(denied?0:1)'
 for f in [PROJECT/'README.md',PROJECT/'output/deepseek-appetizer-api/workspace/lean/ComputationalMathematics/Source/Vershynin/Chapter01.lean',PROJECT/'.tools/deepseek-appetizer/home/.credentials.yaml']:
  q=run([node,'-e',code,str(f)],True); eq(q.returncode,0)
 return 'Old project, old Chapter 1 product file and actual upstream credential file cannot be opened.'
def frozen_inputs():
 node='/Users/gspyrou/.nvm/versions/node/v24.19.0/bin/node'
 code='const fs=require("fs");let denied=false;try {const fd=fs.openSync(process.argv[1],"r+");fs.closeSync(fd)}catch(e){denied=["EPERM","EACCES"].includes(e.code)};process.exit(denied?0:1)'
 for f in [W/'source/Chapter01.pdf',W/'AGENTS.md',W/'run/PROTOCOL.txt',W/'lean/.lake/packages/mathlib/Mathlib.lean',W/'lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean']:
  q=run([node,'-e',code,str(f)],True); eq(q.returncode,0)
 return 'PDF/protocol and Mathlib source/proof objects are read-only; only Lake hash/trace bookkeeping may update.'
def network():
 for url,allowed in [('http://127.0.0.1:3085/health',True),('http://127.0.0.1:3083/health',False)]:
  q=run(['/usr/bin/curl','--noproxy','*','--max-time','3','-fsS',url],True); eq(q.returncode==0,allowed)
 return 'Local meter health works; another localhost port is blocked.'
def startup():
 s=(BASE/'logs/launch-smoke.log').read_text()
 eq('dsh web: http://127.0.0.1:3084/' in s,True); eq('did not activate' in s,False); eq('startup failed' in s,False)
 return 'Isolated Harness starts without plugin activation warnings.'
def preset_packages():
 config=(PROJECT/'.tools/deepseek-chapter01-clean/home/profiles/web/cordis.patch.yml').read_text()
 section=config.split('- id: preset-standard\n',1)[1].split('\n- id:',1)[0]
 preset=json.loads(section.strip().removeprefix('config:').strip())
 names=[]
 def walk(rows):
  for row in rows:
   name=row.get('name','')
   if name.startswith('@deepseek-ai/'):
    eq((PROJECT/'.tools/deepseek-harness/node_modules'/name/'package.json').is_file(),True); names.append(name)
   if row.get('group'): walk(row.get('config',[]))
 walk(preset['plugins'])
 return {'installed_preset_packages':names}
def actual_shell_route():
 node='/Users/gspyrou/.nvm/versions/node/v24.19.0/bin/node'
 script=PROJECT/'.tools/deepseek-chapter01-clean/home/tmp/harness-shell-check.mjs'
 q=run([node,script],True); eq(q.returncode,0)
 r=json.loads(q.stdout); eq(all(x['status']=='PASS' for x in r['checks']),True)
 return {'service':'actual DSH sandbox-bash executor inside outer isolation','checks':[x['name'] for x in r['checks']]}
def observer():
 eq((PROJECT/'.tools/deepseek-chapter01-clean/metrics/current.json').exists(),False)
 return 'No measurement has been started. The meter refuses unarmed inference calls.'
check('source_hash',source)
check('empty_chapter_baseline',baseline)
check('pinned_clean_dependency_sources',deps)
check('lean_mathlib_compilation_inside_isolation',proof_environment)
check('old_code_and_real_credential_read_denials',read_fence)
check('frozen_source_protocol_and_library_proofs',frozen_inputs)
check('network_boundary',network)
check('isolated_harness_startup',startup)
check('all_preset_plugin_packages_installed',preset_packages)
check('actual_harness_shell_route',actual_shell_route)
check('no_experiment_started',observer)
r=dict(checked_at=datetime.now(ZoneInfo('Europe/Athens')).isoformat(),status='READY_FOR_CLEAN_RUN' if all(c['status']=='PASS' for c in checks) else 'NOT_READY',checks=checks,model_requests_made=0,chapter_formalization_started=False)
(BASE/'preflight.json').write_text(json.dumps(r,indent=2)+'\n'); print(json.dumps(r,indent=2)); raise SystemExit(0 if r['status']=='READY_FOR_CLEAN_RUN' else 1)
