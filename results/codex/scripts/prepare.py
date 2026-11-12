#!/usr/bin/env python3
"""Prepare independent PDF-only Codex trials. Never copies product Lean code."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
OPERATOR = ROOT / '.tools/codex-hdp-operator'
WORKFLOW = OPERATOR / 'workflow-latest'
TRIALS = ROOT / 'output/codex-hdp-clean'
CODEX = Path('/Applications/ChatGPT.app/Contents/Resources/codex-cli/CodexCLI.app/Contents/MacOS/codex')
MODEL = 'gpt-6.1-sol'
CASES = {
    'appetizer': ('deepseek-appetizer-clean-api', 'Appetizer.pdf', '164189f2c6e5d39c6b8aa96f3a3c18d02f42194b890be3610aaa44d7c487ca7f'),
    'chapter01': ('deepseek-chapter01-clean-api', 'Chapter01.pdf', '855fdaf6870f664f1e470d47641b6d72758afdb9b87649a6494b027cecc02b17'),
}
SKILLS = ('book-formalization', 'book-formalization-migration', 'formalization-faithfulness-audit', 'formalization-code-review')

def dump(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2) + '\n')

def tomlstr(value):
    return json.dumps(str(value))

def prepare(name):
    old, pdf, digest = CASES[name]
    case = TRIALS / name
    work = case / 'workspace'
    home = OPERATOR / 'trials' / name / 'codex-home'
    if (case / 'prepared.json').exists():
        return
    for p in (work / 'source', work / 'lean/HDP', work / 'run', work / 'reports', work / 'tools', case / 'observer', case / 'tmp', home / 'skills'):
        p.mkdir(parents=True, exist_ok=True)
    original = ROOT / 'output' / old / 'workspace'
    payload = (original / 'source' / pdf).read_bytes()
    assert hashlib.sha256(payload).hexdigest() == digest
    (work / 'source' / pdf).write_bytes(payload)
    # Only official mathematical dependencies, not the previous project's build or HDP tree.
    packages = work / 'lean/.lake/packages'
    if not packages.exists():
        packages.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['/bin/cp', '-cR', str(original / 'lean/.lake/packages'), str(packages)], check=True)
    manifest = json.loads((original / 'lean/lake-manifest.json').read_text())
    for package in manifest['packages']:
        path = packages / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        assert actual == package['rev'], (path, actual)
        changes = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
        assert not changes, (path, changes)
    for filename in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'):
        shutil.copyfile(original / 'lean' / filename, work / 'lean' / filename)
    (work / 'lean/HDP.lean').write_text('import Mathlib\n')
    (work / '.gitignore').write_text('lean/.lake/\nsource/*.pdf\n.formalization/\nreports/native/\n')
    for skill in SKILLS:
        installed = OPERATOR / 'skill-packages' / skill
        assert (installed / 'SKILL.md').is_file()
        # The canonical checkout preserves relative runtime references. Tests and
        # all book packages/history remain outside the permissions allowlist.
        link = home / 'skills' / skill
        if not link.exists():
            link.symlink_to(WORKFLOW / 'skills' / skill, target_is_directory=True)
    # Native Codex reads this sign-in itself; model tools cannot read this home.
    # A symlink avoids making another credential-bearing file.
    auth = home / 'auth.json'
    if not auth.exists():
        auth.symlink_to(Path('/Users/gspyrou/.codex/auth.json'))
    shutil.copyfile('/Users/gspyrou/.codex/models_cache.json', home / 'models_cache.json')
    path = f"{ROOT / '.tools/elan/bin'}:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin"
    env = {'PATH': path, 'ELAN_HOME': str(ROOT / '.tools/elan'), 'CODEX_HOME': str(home),
           'TMPDIR': str(case / 'tmp'), 'PYTHONNOUSERSITE': '1', 'PYTHONDONTWRITEBYTECODE': '1'}
    reads = [Path('/opt/homebrew'), CODEX.parent, ROOT / '.tools/elan', WORKFLOW / 'skills',
             WORKFLOW / 'project-development/current', home / 'skills', OPERATOR / 'runtime-python']
    fs = {':root': 'deny', ':minimal': 'read', ':tmpdir': 'deny', ':slash_tmp': 'deny', str(work): 'write', str(case / 'tmp'): 'write'}
    fs.update({str(p): 'read' for p in reads})
    fs.update({str(work / p): 'read' for p in ('AGENTS.md', 'run', 'source', 'tools', 'lean/lean-toolchain', 'lean/lake-manifest.json', 'lean/.lake/packages')})
    # No theorem fixtures, historical sessions, tests or book-specific source packages.
    fs[str(WORKFLOW / 'skills/**/tests/**')] = 'deny'
    config = [f'model = "{MODEL}"', 'model_reasoning_effort = "high"', 'model_provider = "openai"',
              'approval_policy = "never"', 'default_permissions = "clean-trial"', 'web_search = "disabled"',
              'project_doc_max_bytes = 0', 'cli_auth_credentials_store = "file"',
              '[features]', 'apps = false', 'in_app_browser = false', 'hooks = false', 'multi_agent = true',
              '[agents]', 'max_threads = 4', 'max_depth = 1',
              '[permissions.clean-trial.filesystem]']
    config += [f'{tomlstr(k)} = {tomlstr(v)}' for k, v in fs.items()]
    config += ['[permissions.clean-trial.network]', 'enabled = false', '[shell_environment_policy]', 'inherit = "none"', '[shell_environment_policy.set]']
    config += [f'{tomlstr(k)} = {tomlstr(v)}' for k, v in env.items()]
    config += [f'[projects.{tomlstr(work)}]', 'trust_level = "trusted"']
    (home / 'config.toml').write_text('\n'.join(config) + '\n')
    dump(home / 'trial-policy.json', {'claude_consultation': 'disabled', 'model': MODEL, 'effort': 'high'})
    dump(case / 'launch.json', {'case': name, 'workspace': str(work), 'codex_home': str(home), 'env': env, 'codex': str(CODEX)})
    subprocess.run(['git', 'init', '-b', 'codex/clean-trial', str(work)], check=True, stdout=subprocess.DEVNULL)
    dump(case / 'prepared.json', {
        'case': name, 'created_unix': time.time(), 'source_pdf': pdf, 'source_sha256': digest,
        'initial_lean': 'import Mathlib\n', 'initial_product_modules': [],
        'lean_toolchain': (work / 'lean/lean-toolchain').read_text().strip(),
        'dependencies': [{k: p[k] for k in ('name', 'url', 'rev')} for p in manifest['packages']],
        'workflow_version': '8.1.70', 'workflow_commit': '1fb46504020649465d98ef2533a926e8c1e4dbf4',
        'model': MODEL, 'reasoning_effort': 'high', 'auth_mode': 'native ChatGPT sign-in; credentials denied to tools',
        'claude_consultation': 'disabled by explicit user choice',
        'deviations': ['Canonical Claude source-admission receipt unavailable in Codex-only protocol.',
                       'Full POSIX installer failed on macOS xattr API; exact tagged skill packages installed with the standard Codex installer.'],
    })

if __name__ == '__main__':
    for name in CASES:
        prepare(name)
        print(f'Prepared {name}')
