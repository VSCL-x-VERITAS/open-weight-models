#!/usr/bin/env python3
"""Verify exported source hashes, pinned builds and all local axiom dependencies."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[1]
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--project',choices=('all','appetizer','chapter01'),default='all')
    parser.add_argument('--lake',default='lake')
    parser.add_argument('--fetch-cache',action='store_true')
    args=parser.parse_args()
    files=json.loads((ROOT/'provenance/source-files.json').read_text())['files']
    verification=ROOT/'.verification';verification.mkdir(exist_ok=True)
    projects=('appetizer','chapter01') if args.project=='all' else (args.project,)
    results=[]
    for name in projects:
        for entry in files:
            if entry['path'].startswith(name+'/'):
                digest=hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest()
                if digest!=entry['original_sha256'] or digest!=entry['exported_sha256']:raise ValueError('Source hash mismatch: '+entry['path'])
        for suffix,cmd in ([('cache',[args.lake,'exe','cache','get'])] if args.fetch_cache else []) + [('build',[args.lake,'build','HDP']),('axioms',[args.lake,'env','lean','checks/AuditKernel.lean'])]:
            log=verification/f'{name}-{suffix}.log'
            with log.open('w') as f:p=subprocess.run(cmd,cwd=ROOT/name,stdout=f,stderr=subprocess.STDOUT)
            if p.returncode:raise RuntimeError(f'{name} {suffix} failed; see {log}')
        text=(verification/f'{name}-axioms.log').read_text()
        total=[line for line in text.splitlines() if 'AUDIT_TOTAL ' in line]
        if not total:raise RuntimeError(name+': missing axiom-check completion count')
        result={'project':name,'build':'PASS','source_hashes':'PASS','all_local_constant_axioms':'PASS','kernel_constant_count':int(total[-1].split('AUDIT_TOTAL ')[1]),'source_correspondence':'Qualified independent operator judgment, see audit/audit-and-comparison.json'}
        results.append(result);print(json.dumps(result))
    (verification/'results.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
