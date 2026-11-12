#!/usr/bin/env python3
"""Build the pinned release and inspect axiom dependencies; no model access."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
TOOLCHAIN = 'leanprover/lean4:v4.29.0-rc3'
MATHLIB = 'e8ea1afc32790ce1d4e1a4e45cc412ba9388716b'


def run(args, project, logfile):
    with logfile.open('w', encoding='utf-8') as stream:
        result = subprocess.run(args, cwd=ROOT / project, stdout=stream,
                                stderr=subprocess.STDOUT, check=False)
    if result.returncode:
        print(logfile.read_text(), file=sys.stderr)
        raise RuntimeError(f'{project}: command failed ({result.returncode}); {logfile}')
    return logfile.read_text()


def verify(project, lake, fetch_cache):
    work = ROOT / project
    if (work / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise RuntimeError(f'{project}: toolchain differs from the experiment pin')
    manifest = json.loads((work / 'lake-manifest.json').read_text())
    pins = [p for p in manifest['packages'] if p['name'] == 'mathlib']
    if len(pins) != 1 or pins[0]['rev'] != MATHLIB:
        raise RuntimeError(f'{project}: Mathlib revision differs from the experiment pin')
    sources = json.loads((ROOT / 'provenance/source-files.json').read_text())['files']
    for entry in sources:
        if not entry['path'].startswith(project + '/'):
            continue
        actual = hashlib.sha256((ROOT / entry['path']).read_bytes()).hexdigest()
        if actual != entry['original_sha256'] or actual != entry['exported_sha256']:
            raise RuntimeError(f'Source differs from saved model output: {entry["path"]}')
    logs = ROOT / '.verification'
    logs.mkdir(exist_ok=True)
    if fetch_cache:
        print(f'{project}: fetching pinned Mathlib cache', flush=True)
        run([lake, 'exe', 'cache', 'get'], project, logs / f'{project}-cache.log')
    print(f'{project}: building HDP', flush=True)
    run([lake, 'build', 'HDP'], project, logs / f'{project}-build.log')
    print(f'{project}: checking declaration axioms', flush=True)
    text = run([lake, 'env', 'lean', 'checks/Axioms.lean'], project,
               logs / f'{project}-axioms.log')
    expected = re.findall(r'^#print axioms (\S+)', (work / 'checks/Axioms.lean').read_text(), re.M)
    # Declaration identifiers can end in an apostrophe. Split on the fixed
    # phrase rather than treating the first apostrophe as a closing delimiter.
    rows = []
    for line in text.splitlines():
        if ' depends on axioms: [' not in line:
            continue
        name, values = line.split(' depends on axioms: [', 1)
        rows.append((name[1:-1], values.rsplit(']', 1)[0]))
    observed = [name for name, _ in rows]
    if observed != expected:
        raise RuntimeError(f'{project}: axiom output does not match the declaration list')
    for name, values in rows:
        axioms = {v.strip() for v in values.split(',') if v.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise RuntimeError(f'{project}: unexpected axioms for {name}: {sorted(axioms)}')
    print(f'{project}: PASS, {len(rows)} declarations inspected', flush=True)
    return {'project': project, 'build': 'PASS', 'axiom_check': 'PASS',
            'declarations_checked': len(rows), 'source_hash_check': 'PASS',
            'source_semantic_audit': 'Not performed by this script'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', choices=['all', 'appetizer', 'chapter01'], default='all')
    parser.add_argument('--lake', default='lake', help='Lake executable (default: PATH)')
    parser.add_argument('--fetch-cache', action='store_true', help='Download the pinned Mathlib build cache first')
    args = parser.parse_args()
    projects = ['appetizer', 'chapter01'] if args.project == 'all' else [args.project]
    results = [verify(project, args.lake, args.fetch_cache) for project in projects]
    (ROOT / '.verification/results.json').write_text(json.dumps(results, indent=2) + '\n')
    print('All requested checks passed. Source fidelity requires a separate semantic audit.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
