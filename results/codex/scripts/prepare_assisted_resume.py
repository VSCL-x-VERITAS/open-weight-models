#!/usr/bin/env python3
"""Retain original stopping evidence and supply independently researched contracts."""
import datetime as dt
import hashlib
import json
from pathlib import Path
import shutil

from prepare import ROOT, TRIALS
from observe import summary

INTERVENTION = 'operator-clarification-001'

APP_CONTRACT = '''Operator clarification 001 — Appetizer Notes U17

Authority: the user explicitly asked the operator to independently review the
blocker, provide the needed clarification as appropriate, and resume the run.
This is an operator-supplied mathematical target backed by primary literature.
It changes this continuation to an assisted experiment. It does not add Lean
solutions, permit access to any prior project, or remove any source item.

INDEPENDENT REVIEW
I visually checked the original PDF page 4, the precise Exercise 0.0.6 bound,
the final Notes sentence and your blocker. A uniform matching lower bound over
every polytope and every positive radius would be false. The cited sharpness is
worst-case and up to absolute constants in a nontrivial entropy range. Your
request for explicit quantifiers and range was justified.

PRIMARY-SOURCE SUPPORT (paraphrase, not a copied proof)
The book's reference [50] is Carl–Pajor (1988), pp. 479–504. On pp. 491–492,
Corollary 2.4 and the following discussion identify the sharp entropy scale for
the identity from finite-dimensional l1 to l2. Equation (2.14) supplies a positive
universal lower constant multiplying min(1,sqrt(log(1+n/k)/k)), for 1<=k<=n.
The image of the l1 unit ball is the symmetric convex hull of the coordinate
unit vectors. Scaling this body by 1/2 makes its diameter at most one.
Source URL: https://www.math.uci.edu/~rvershyn/teaching/hdp/carl-pajor.pdf
Paper: B. Carl and A. Pajor, Gelfand numbers of operators with values in a Hilbert
space, Inventiones mathematicae 94 (1988), 479–504; equation (2.14), printed p.492.
Bibliographic binding: author-hosted first-edition book, bibliography [49–50],
https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf (printed p.286).
Only the bibliography was used from the additional book, not later proofs.

PRECISE TARGET TO INDEPENDENTLY REVIEW AND THEN PROVE
For every natural n>=1, in Euclidean real n-space let
  V_n = { +(1/2)e_i, -(1/2)e_i : i=1,...,n },
  K_n = convexHull(V_n).
Verify V_n has exactly 2n elements and diameter at most 1.
There exists a real absolute constant c with 0<c<1, independent of n,k, such that
for every n>=1, integer 1<=k<=n, and real epsilon>0 with
  epsilon < c * min(1, sqrt(log(1 + (n:real)/(k:real)) / (k:real))),
EVERY finite set C of centers in the ambient Euclidean n-space whose closed
epsilon-balls cover K_n satisfies
  2^(k-1) < card(C).
Log is natural logarithm. Exponents and divisions have their indicated real or
natural meanings. The conclusion concerns arbitrary centers, not just centers
chosen in V_n or empirical averages. No assumption granting the desired packing
or entropy lower bound may be inserted into the final theorem.

WHY THIS ADDRESSES THE BOOK
This is a dyadic entropy formulation of a worst-case matching lower bound. It
selects a concrete family of polytopes with N=2n vertices in the book's diameter
normalization, with a single universal constant and a stated intermediate
entropy range. Explain the connection to Exercise 0.0.6's upper bound and the
limitations of the range; do not claim equality of constants or sharpness at
arbitrarily small radii in fixed dimension. An isolated vertex-separation bound,
a theorem about empirical centers only, or optimality of approximate convex
combinations is not enough to establish this covering-number sharpness target.

ACCEPTANCE AND SCOPE
Record this source supplementation as an intervention, retain the original
unresolved row and original reports, and obtain a fresh independent Codex review
of this proof-free target and its literature correspondence. If a reviewer finds
a substantive mismatch, repair the target transparently and retain both versions.
Then prove the reviewed target from Lean/Mathlib and this trial's own code. The
paper's mathematical assertion is source material, not an axiom or a supplied
Lean theorem. No sorry, custom axiom or assumed lower-bound hypothesis is allowed.
Keep all previously completed work/reviews unless a concrete defect is found.
Continue independently through proof, review, integration, build and axiom checks.
If this remaining proof is difficult, persist with mathematical work rather than
reporting the now-specified source as a nonlocal blocker. Do not silently defer it
or mark the whole source complete from the upper bound alone.
'''

CHAPTER_CONTRACT = '''Operator clarification 001 — Chapter 1 signed raw moments

Authority: the user explicitly asked the operator to independently review the
blocker, provide the needed clarification as appropriate, and resume the run.
This is an explicit operator semantic amendment. It changes this continuation
to an assisted experiment. The original PDF remains unchanged.

INDEPENDENT REVIEW
I visually checked the original PDF's printed page 5, your discrepancy record
and Basic.lean's definitions. The displayed signed real raw moment at arbitrary
positive real order is underspecified. The real square root of a negative value
already makes the unrestricted wording untenable. Mathlib's total Real.rpow
does not determine the author's intended meaning. Your refusal to silently adopt
that extension was correct. Existing supported-domain definitions may be reused.

ADOPT THIS EXPLICIT DOMAIN CORRECTION
1. For an arbitrary signed real random variable, raw moments in this experiment
   mean integer orders n in the positive naturals: E[X^n], with ordinary signed
   integer powers. Keep the existing optional extended expectation treatment:
   one-sided infinities are allowed where defined, and infinity-minus-infinity
   stays undefined. Finite real statements retain their integrability conditions.
2. For nonnegative real random variables, raw moments E[X^p] are allowed for every
   real p>0, with ordinary nonnegative-base real powers and extended nonnegative
   expectations; keep finite-real bridges with their actual finiteness hypotheses.
3. For arbitrary signed real variables, absolute moments E[|X|^p] remain defined
   for every real p>0. Retain infinite values and the Lp material already proved.
4. No semantics are asserted here for a general signed variable at a noninteger
   raw order. This is a documented correction of the PDF's domain, not a theorem
   proving the printed unrestricted wording. Do not relabel absolute moments as
   signed raw moments, use complex moments, or silently use negative-base rpow.
   Special rational-power conventions outside these domains are not part of the
   amended specification; they are not universally impossible, just not adopted.

SOURCE SUPPORT
NIST's tutorial defines moments of a real variable using positive integer orders
(Possolo–Toman, Tutorial for Metrologists, printed p.17, Section 4.8).
https://www.nist.gov/system/files/documents/2017/04/28/TutorialMetrologists2011Nov22.pdf
This supports the standard signed integer convention. It does not prove that the
book intended this exact correction; that choice is explicitly operator-authorized.
Nonnegative and absolute real-power domains follow the original PDF and ordinary
real analysis, not a newly supplied negative-base extension.

REMAINING WORK
Obtain a fresh independent Codex statement/source review of this proof-free
amendment. Preserve original unresolved-source evidence and mark its disposition
as resolved_by_operator_domain_amendment, with the exact retained limitation.
Make the correction explicit in the module documentation, source inventory,
final crosswalk and report. Check that accepted public raw-moment declarations
only assert these meaningful domains. Reuse valid existing proofs and reviews;
add only missing bridges or counterexample evidence that materially verifies the
correction. In particular check agreement on the common nonnegative integer
domain and the finite expectation bridges, rather than only renaming definitions.
Recheck affected source coverage, actual integrated Lean build and allowed axioms.

When all mathematical and review work is complete, completion must be described
as the supplied Chapter 1 with this explicit domain correction, not verbatim
formalization of its unrestricted signed/noninteger wording. Do not silently
waive unrelated scope items. Canonical Claude admission remains unavailable under
the Codex-only protocol, so retain its separate limitation without fake receipts.
'''

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def prepare(name, contract):
    case = TRIALS / name
    work = case / 'workspace'
    archive = case / 'observer/interventions' / INTERVENTION
    if archive.exists():
        raise RuntimeError(f'Intervention already prepared: {name}; do not overwrite original evidence')
    archive.mkdir(parents=True)
    baseline = summary(case)
    (archive / 'unassisted-measurement-baseline.json').write_text(json.dumps(baseline, indent=2) + '\n')
    (archive / 'source-contract.txt').write_text(contract)
    original_files = {}
    for path in sorted(work.rglob('*')):
        rel = path.relative_to(work)
        if '.lake' in rel.parts or '.git' in rel.parts or not path.is_file():
            continue
        # Immutable original stopping record: hashes cover all evidence, while
        # retained copies cover generated Lean and source/accounting JSON.
        original_files[str(rel)] = sha(path)
        if path.suffix == '.lean' or (path.suffix == '.json' and str(rel).startswith('reports/')):
            copy = archive / 'original-state' / rel
            copy.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, copy)
    (archive / 'original-workspace-hashes.json').write_text(json.dumps(original_files, indent=2) + '\n')
    supplied = work / 'source' / INTERVENTION
    supplied.mkdir()
    clarification = supplied / 'CLARIFICATION.txt'
    clarification.write_text(contract)
    prompt = work / 'run/RESUME_AFTER_OPERATOR_001.txt'
    prompt.write_text(f'''Resume this SAME {name} experiment from its persisted proofs and reviews.
The user has explicitly authorized an independent operator review, narrowly
justified source clarification and resumption. Read AGENTS.md, current STATUS,
and source/{INTERVENTION}/CLARIFICATION.txt in full.

The clarification is a source-only operator intervention: its explicit amended
contract supersedes the old unresolved-source blocker. It does not change Lean,
Mathlib, skill, model, effort, filesystem permissions, no-network policy, or the
prohibition on prior project/experiment solutions. Continue with GPT-6.1 Sol/High.
The operator researched cited mathematics outside this sandbox; you receive only
the retained clarification, no Lean solution, prior library or external access.

Mark reports/STATUS.json working while actionable work remains. Preserve original
evidence; it has also been archived outside your accessible workspace. Record
assisted_continuation_001 explicitly in your inventory and final report. Obtain
a fresh independent Codex review of the new proof-free contract, then complete
its proof and affected source/structure/axiom/build checks. Existing valid work
must be reused. Continue all actionable mathematical work; do not create new
workflow infrastructure or repeat unrelated completed reviews. Never introduce
unsupported proof assumptions or weaken this contract just to close the row.

The original skill's canonical Claude/receipt limitations remain recorded; they
do not themselves block the authorized adapted mathematical workflow. Never
claim canonical Chapter PASS or unassisted completion. On completion use
claimed_complete_pending_audit with explicit amended-source scope and links to
actual independent review and kernel evidence. A newly found genuine nonlocal
blocker must be precise and evidence-backed. A hard proof is not such a blocker.
''')
    receipt = {'id': INTERVENTION, 'case': name,
        'prepared_at_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
        'authorization': 'User: independently review what they need, provide it as you see fit, then resume their runs.',
        'experiment_classification_before': 'unassisted clean Codex trial with adapted skill',
        'experiment_classification_after': 'operator-assisted continuation of the same clean Codex trial',
        'source_contract': str(clarification.relative_to(work)), 'source_contract_sha256': sha(clarification),
        'resume_prompt': str(prompt.relative_to(work)), 'resume_prompt_sha256': sha(prompt),
        'provided_lean_proofs': False, 'provided_prior_library_or_experiment_solutions': False,
        'operator_review_scope': 'The two reported source blockers, their primary references and relevant existing moment/covering definitions; not a new full independent source audit.',
        'operator_research_duration_seconds': None,
        'operator_research_tokens': None,
        'operator_research_note': 'This coordinating chat/research is outside the native trial meter. No missing duration, tokens or API-equivalent charge is fabricated.',
        'baseline': {k: baseline[k] for k in ('state','response_usage_records','tokens','api_equivalent_usd','active_seconds_excluding_between_turn_idle','setup_active_seconds','formalization_active_seconds')},
        'original_workspace_hashes_sha256': sha(archive / 'original-workspace-hashes.json')}
    (archive / 'intervention-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (supplied / 'INTERVENTION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(name, 'prepared;', baseline['response_usage_records'], 'original usage records retained')

if __name__ == '__main__':
    prepare('appetizer', APP_CONTRACT)
    prepare('chapter01', CHAPTER_CONTRACT)
