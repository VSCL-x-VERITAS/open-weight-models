#!/usr/bin/env python3
"""Write frozen neutral instructions, never prior proof or audit findings."""
import json
from pathlib import Path
from prepare import ROOT, OPERATOR, TRIALS, WORKFLOW, CASES

CHECK = '''import errno, json, socket
from pathlib import Path
forbidden = FORBIDDEN
results = []
for label, path in forbidden.items():
    try:
        with Path(path).open('rb') as stream:
            stream.read(1)
    except PermissionError:
        results.append({'check': label, 'denied': True})
    except OSError as error:
        results.append({'check': label, 'denied': error.errno in (errno.EPERM, errno.EACCES), 'errno': error.errno})
    else:
        results.append({'check': label, 'denied': False})
sock = socket.socket()
sock.settimeout(2)
try:
    sock.connect(('127.0.0.1', 3084))
except OSError as error:
    results.append({'check': 'other_harness_network', 'denied': error.errno in (errno.EPERM, errno.EACCES), 'errno': error.errno})
else:
    results.append({'check': 'other_harness_network', 'denied': False})
finally:
    sock.close()
assert Path('source/PDFNAME').read_bytes().startswith(b'%PDF')
assert Path('lean/.lake/packages/mathlib/Mathlib.lean').is_file()
assert Path('lean/HDP.lean').read_text() == 'import Mathlib\\n'
print(json.dumps({'checks': results, 'positive_source_and_mathlib': True}))
assert all(item['denied'] for item in results), 'ISOLATION FAILED: do not begin formalization'
'''

for name, (_, pdf, _) in CASES.items():
    work = TRIALS / name / 'workspace'
    other = 'chapter01' if name == 'appetizer' else 'appetizer'
    forbidden = {
        'prior_product': str(ROOT / 'output/hdp-deepseek-formalization/appetizer/HDP.lean'),
        'prior_attempt': str(ROOT / 'output/deepseek-appetizer-clean-api/workspace/lean/HDP.lean'),
        'prior_audit': str(ROOT / 'output/hdp-independent-correspondence-audit/audit.json'),
        'other_new_case': str(TRIALS / other / 'workspace/lean/HDP.lean'),
        'global_credentials': '/Users/gspyrou/.codex/auth.json',
        'native_credentials': str(OPERATOR / 'trials' / name / 'codex-home/auth.json'),
        'skill_book_package': str(WORKFLOW / 'books/vershynin-hdp/book.json'),
        'root_repository': str(ROOT / '.git/config'),
    }
    # Book metadata filenames may vary by release; use an existing file, not a
    # nonexistent-path failure as evidence of isolation.
    book_files = list((WORKFLOW / 'books/vershynin-hdp').rglob('*.json'))
    assert book_files
    forbidden['skill_book_package'] = str(book_files[0])
    assert all(Path(path).is_file() for path in forbidden.values())
    check = CHECK.replace('FORBIDDEN', repr(forbidden)).replace('PDFNAME', pdf)
    (work / 'tools/isolation_check.py').write_text(check)
    skill = OPERATOR / 'trials' / name / 'codex-home/skills/book-formalization/SKILL.md'
    agents = f'''This is an independent, clean PDF-to-Lean experiment.

Source: source/{pdf}. Formalize the complete supplied PDF, including its operative
definitions, numbered and unnumbered mathematical statements and exercises. Read
the entire source, its proofs and notes to determine scope. Source correspondence
is as important as successful compilation. Derive the inventory yourself.

Use the book-formalization skill at {skill} and its four roles.
No previous book-specific Lean code, inventories, reports, statement corrections
or prior experiment sessions are available. The only mathematical software input
is the pinned Lean compiler and official Mathlib dependency tree in lean/.lake.
The tool filesystem permission profile enforces this boundary. Do not bypass it,
request wider access, inspect credentials, use the internet or import solutions.

USER-APPROVED PROTOCOL OVERRIDES:
* Codex only, GPT-6.1 Sol at High. No Claude, external model, model fallback, remote
  source consultation or paid API key. Independent Codex reviewers are required.
* The current skill unconditionally requires a Claude receipt for canonical source
  admission even when its installation choice disables advice. Never invent or
  relabel such a receipt. Record Codex-only independent source review as an explicit
  adaptation. Do not claim canonical Claude admission or canonical Chapter PASS
  if unavailable. Continue the mathematical work and real independent reviews.
* Start a fresh source package and mathematical target inventory from this PDF.
  Never load an existing workflow book package or stable theorem-library base.
  Lean project is lean/; its starting HDP.lean contains only import Mathlib.
* Skill helper frontdoors may assume a pre-admitted published source module or a
  platform runtime unavailable here. Attempt the applicable existing route once,
  retain the concrete blocker and proceed using the four roles. Do not build new
  controllers, fake gate acceptance, change upstream skill code or spend the
  experiment authoring new workflow infrastructure. Preserve exact target reviews,
  native independent reviewer identities, kernel checks and source coverage.
* Native fresh subagents may perform the skill's independent roles. Give reviewers
  complete source passages/context, exact proof-free target and effective
  definitions. No generator proof/conclusions; no inherited generator transcript.
  Keep roles distinct and preserve actual evidence. Never self-certify independence.
* Manual operator publication only. No GitHub access or remote mutation by worker.
  Work locally. Do not change Lean/Mathlib pins, dependency source or frozen inputs.

Keep an explicit source-to-declaration inventory with page/label, exact source
meaning, definitions, target, assumptions, review outcome, proof status and any
remaining source mismatch. Preserve every scope exclusion with a reason; no
silent omissions or weakened targets to get a green build. Until the inventory
is independently reviewed, completeness percentages are N/A.

Use no sorry/admit, custom axioms, unsafe proofs, circular definitions or opaque
mathematical placeholders in accepted results. Allowed logical axioms are the
ordinary Lean/Mathlib propext, Classical.choice and Quot.sound. Use real Lean
compilation and #print axioms evidence. Claim-contract canonical proof receipts
are preferred where supported; identify any missing receipt honestly.

Persist work, inventory, decisions and review evidence as you go. Continue all
actionable rows without asking the operator to choose conventions. Justify source
interpretations, and make unresolved mismatches visible. A turn ending, a partial
proof or a checkpoint is not source completion. Do not stop merely after the first
increment. Resume from persisted work; do not reset completed evidence.

Before ending, write reports/STATUS.json with state in:
  working: actionable work remains; next_action explains it;
  blocked: genuine nonlocal blocker, concrete evidence and action needed;
  claimed_complete_pending_audit: all source items resolved, independent source
    coverage and statement reviews retained, actual build and axiom checks pass.
This last state is a completion CLAIM requiring a separate operator audit; it is
not canonical Chapter PASS. Never report a blocker just because a proof is hard.
'''
    (work / 'AGENTS.md').write_text(agents)
    setup = f'''Setup phase only. Do not read or formalize the PDF yet.
Read AGENTS.md and the installed book-formalization SKILL.md plus its short
four-role workflow. Run tools/isolation_check.py from this workspace with python3;
all forbidden reads and the network check must be denied. Preserve its output in
reports/setup-isolation.json. Check pdftotext/pdfinfo availability without reading
PDF contents; check the pinned Lean version and run the initial empty-project
lake build in lean/. Use login=false for shell commands. You have no approval or
network access and must not bypass the profile. Record any narrow tool/runtime
problem with actual evidence and solve only within the profile.
Write reports/SETUP_READY.json with ready true only if isolation and the initial
Lean build really pass. Record model gpt-6.1-sol, effort high, skill 8.1.70,
Codex-only deviations and commands. Do not write mathematical inventory or proofs.
End this setup turn. A separately logged next turn starts formalization.
'''
    (work / 'run/SETUP_PROMPT.txt').write_text(setup)
    (work / 'run/START_PROMPT.txt').write_text('''Formalization phase starts now. Read AGENTS.md and apply the installed
book-formalization skill to the whole source PDF. Independently derive the source
inventory, formalization steps, exact Lean statements and proofs from scratch.
Use fresh native Codex reviewers for the skill's independent roles as specified.
Continue through all actionable work until the whole PDF is resolved or a genuine
typed nonlocal blocker exists. Follow the explicit protocol overrides and retain
all real evidence. Do not stop after a first increment or confuse compile success
with source completeness. Persist reports/STATUS.json before ending.
''')
    (work / 'run/CONTINUE_PROMPT.txt').write_text('''Continue the same clean formalization experiment from persisted files and
review evidence. Read AGENTS.md, reports/STATUS.json and the source inventory.
Continue every actionable source, target, proof, independent review, build and
coverage item. Do not repeat valid completed reviews, weaken source targets or
stop at another checkpoint. No new mathematical hint is supplied by this
automatic continuation. Write reports/STATUS.json with the honest final state.
''')
    print(f'Wrote frozen protocol for {name}')
