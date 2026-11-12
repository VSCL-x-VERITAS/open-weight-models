#!/usr/bin/env python3
"""Regenerate the combined PDF from exact exported metrics (requires ReportLab)."""
from pathlib import Path
import json
from xml.sax.saxutils import escape
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.pagesizes import A4
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak

ROOT = Path(__file__).resolve().parents[1]
S = json.loads((ROOT / 'metrics/summary.json').read_text())
RUNS = [json.loads(p.read_text()) for p in sorted((ROOT / 'metrics/runs').glob('*.json'))]
DEST = ROOT / 'reports/combined-experiment-report.pdf'
DEST.parent.mkdir(exist_ok=True)
BLUE = colors.HexColor('#163A53')
TEAL = colors.HexColor('#167D8D')
GRAY = colors.HexColor('#53616B')
LIGHT = colors.HexColor('#EFF4F7')
styles = getSampleStyleSheet()
styles.add(ParagraphStyle(name='TitleHDP', fontName='Helvetica-Bold', fontSize=24,
                         leading=29, textColor=BLUE, spaceAfter=12))
styles.add(ParagraphStyle(name='SubHDP', fontName='Helvetica', fontSize=11,
                         leading=15, textColor=GRAY, spaceAfter=18))
styles.add(ParagraphStyle(name='HeadHDP', fontName='Helvetica-Bold', fontSize=13,
                         leading=17, textColor=BLUE, spaceBefore=14, spaceAfter=8))
styles.add(ParagraphStyle(name='BodyHDP', fontName='Helvetica', fontSize=9.5,
                         leading=13.8, textColor=colors.HexColor('#21323D'), spaceAfter=9))
styles.add(ParagraphStyle(name='SmallHDP', fontName='Helvetica', fontSize=8,
                         leading=11, textColor=GRAY, spaceAfter=7))
styles.add(ParagraphStyle(name='TableHDP', fontName='Helvetica', fontSize=8.3,
                         leading=11.3, textColor=colors.HexColor('#21323D')))
styles.add(ParagraphStyle(name='TableHeadHDP', fontName='Helvetica-Bold', fontSize=8.2,
                         leading=11, textColor=colors.white))

story = []
WIDTH = A4[0]-96

def p(text, style='BodyHDP'):
    story.append(Paragraph(text, styles[style]))

def head(text):
    p(text, 'HeadHDP')

def duration(seconds):
    ms = round(seconds * 1000)
    h, ms = divmod(ms, 3600000)
    m, ms = divmod(ms, 60000)
    sec = ms / 1000
    return (f'{h}h ' if h else '') + (f'{m}m ' if m or h else '') + f'{sec:06.3f}s'

def usd(value): return f'${value:.9f}'
def num(value): return f'{value:,}'

def table(rows, widths, numeric_from=1):
    cooked = []
    for i, row in enumerate(rows):
        cooked.append([Paragraph(escape(str(x)), styles['TableHeadHDP' if i==0 else 'TableHDP']) for x in row])
    t = Table(cooked, colWidths=widths, repeatRows=1, hAlign='LEFT')
    t.setStyle(TableStyle([
        ('BACKGROUND',(0,0),(-1,0),BLUE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white,LIGHT]),
        ('VALIGN',(0,0),(-1,-1),'TOP'),
        ('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),
        ('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),7),
        ('LINEBELOW',(0,-1),(-1,-1),0.5,colors.HexColor('#CBD8E0')),
    ]))
    story.append(t)
    story.append(Spacer(1,9))

app = S['appetizer']['all_measured_phases']
ch = S['chapter01']['main_attempt_and_continuations']

p('PDF-to-Lean formalization<br/>Appetizer and Chapter 1', 'TitleHDP')
p('Roman Vershynin - High-Dimensional Probability<br/>Clean DeepSeek API experiments | Report date: 2 November 2026 (Athens)', 'SubHDP')
p('<b>Outcome:</b> both final outputs build in Lean, and the model reports complete mathematical coverage of the assigned extracts. '
  'Independent source-to-statement semantic review remains pending. Chapter 1 required four human-prompted continuations; it is not a one-shot success.')
head('Final reconciled metrics')
table([
 ['Metric','Clean Appetizer','Chapter 1'],
 ['Assigned source','4 PDF pages','7 PDF pages (book pp. 5-11)'],
 ['Active time, including warm setup',duration(app['measured_elapsed_seconds']),duration(ch['measured_elapsed_seconds'])],
 ['API requests',num(app['request_count']),num(ch['request_count'])],
 ['Input tokens',num(app['input_tokens']),num(ch['input_tokens'])],
 ['Output tokens',num(app['output_tokens']),num(ch['output_tokens'])],
 ['Cached input (subset)',num(app['reported_cached_input_tokens']),num(ch['reported_cached_input_tokens'])],
 ['Reasoning output (subset)',num(app['reported_reasoning_tokens']),num(ch['reported_reasoning_tokens'])],
 ['Actual API cost (USD)',usd(app['cost_usd']),usd(ch['cost_usd'])],
 ['Formalization attempts','1; no rescue continuation','5; initial + 4 continuations'],
 ['Final HDP modules','8 + entry point','13 + entry point'],
], [WIDTH*.40,WIDTH*.30,WIDTH*.30])
p('These are finalized, reconciled OpenRouter usage charges, not price estimates. All billing records have input, output and cost data. '
  'Repeated context is counted on every request. Cached-input and reasoning-output counts are subsets, not extra tokens.', 'SmallHDP')
head('Scope and quality status')
p('The Appetizer covers the Caratheodory and approximate Caratheodory results, variance exercises, covering bounds, binomial estimates and sharpness. '
  'Chapter 1 covers its inventoried mathematical content in Sections 1.1-1.3, including the strong law, CLT, de Moivre-Laplace and Poisson limit theorem. '
  'Illustrative and historical narrative is excluded explicitly in the inventories.')
p('The original Appetizer pilot had access to an existing formalization library and is excluded from these clean results. '
  'No Leanstral API run or NERSC GPU comparison is claimed here.', 'SmallHDP')

story.append(PageBreak())
p('Time, phases and continuations', 'TitleHDP')
p('Primary time is observed agent/tool/API active elapsed time, with recorded idle and blocking human waits excluded. '
  'It is neither raw wall time nor GPU/CPU time. Local compiler work during active turns counts.')
head('Warm setup versus mathematical formalization')
rows=[['Phase','Active time','Calls','Input tokens','Output tokens','USD']]
for title, values in [
 ('Appetizer setup',S['appetizer']['setup']),('Appetizer formalization',S['appetizer']['formalization']),
 ('Chapter 1 setup',S['chapter01']['setup']),('Chapter 1 formalization',S['chapter01']['formalization']),
 ('Separate calibration',S['chapter01']['separate_setup_calibration'])]:
    rows.append([title,duration(values['measured_elapsed_seconds']),values['request_count'],num(values['input_tokens']),num(values['output_tokens']),f"{values['cost_usd']:.9f}"])
table(rows,[95,88,34,88,77,WIDTH-382])
p('Setup means warm model protocol/environment checks. It does not measure downloading/installing Lean, Mathlib or the full released book-formalization skill. '
  'The earlier Chapter 1 calibration is outside the Chapter 1 total on page 1 and is shown separately.', 'SmallHDP')
head('Chapter 1 attempt history')
chapter_runs=[r for r in RUNS if r['project']=='chapter01' and r['classification']!='SETUP_CALIBRATION_ONLY']
rows=[['Attempt','Active time','Calls','Input tokens','Output tokens','USD']]
for n,r in enumerate(chapter_runs,1):
    rows.append([f'{n:02}'+(' (incl. setup)' if n==1 else ''),duration(r['measured_elapsed_seconds']),r['request_count'],num(r['input_tokens']),num(r['output_tokens']),f"{r['cost_usd']:.9f}"])
table(rows,[95,88,34,88,77,WIDTH-382])
p('<b>01:</b> incomplete; four main obligations remained. <b>02:</b> CLT, de Moivre-Laplace and a special-case norm counterexample added; Poisson remained open. '
  '<b>03:</b> broader source correspondence and general counterexample added; Poisson and further gaps remained. '
  '<b>04:</b> Poisson proved; three source-correspondence gaps remained. <b>05:</b> model reported those gaps closed and full inventoried mathematical coverage.')
p('Incomplete attempts are retained as part of the experimental result. They ended with normal final responses despite open work; '
  'the harness turn status "completed" did not establish mathematical completion. Continuation prompts requested persistence and self-review without supplying a proof strategy.', 'SmallHDP')

story.append(PageBreak())
p('Protocol, verification and limits', 'TitleHDP')
head('Inputs and isolation')
p('The model received an assigned PDF and a generic PDF-to-Lean protocol. It derived its own inventory, statements, proof plan and code. '
  'Lean core, the pinned Mathlib and ordinary dependencies were the supplied mathematical libraries; generic shell, PDF and compiler tools were allowed. '
  'The clean processes were isolated from previous product formalizations and prior Appetizer attempts. Pretraining exposure is not assessed.')
p('<b>Model:</b> deepseek/deepseek-v4.1-flash-1017, High reasoning, OpenRouter.<br/>'
  '<b>Harness:</b> @deepseek-ai/dsh@0.2.1-rc.5.<br/>'
  '<b>Lean:</b> leanprover/lean4:v4.29.0-rc3.<br/>'
  '<b>Mathlib:</b> e8ea1afc32790ce1d4e1a4e45cc412ba9388716b.', 'SmallHDP')
head('What was checked')
p('The operator reran both final project builds and selected declaration axiom checks after model completion. '
  'The release additionally rebuilds the exported projects from fresh project build directories and checks the axioms of 37 Appetizer and 113 Chapter 1 '
  'public named definitions, lemmas and theorems. Only the standard axioms propext, Classical.choice and Quot.sound are accepted; empty axiom sets are also accepted. '
  'Historical Prop-valued drafts are excluded from the release declaration list and do not count as proofs.')
p('Release verification reuses the same pinned Mathlib dependency build cache but does not copy either experiment\'s HDP build output. '
  'The final Lean source files are exported byte for byte; hashes identify them. This is reproducibility checking, not independent mathematical proof discovery.')
head('Limits that affect interpretation')
p('<b>Source fidelity:</b> complete coverage is the model\'s self-review. A full independent comparison of hypotheses, quantifiers, constants and conclusions with the PDF is pending. '
  'Kernel checking proves the stated propositions, not that they are the intended book propositions.')
p('<b>Correspondence choices:</b> the final Chapter 1 binomial distribution is defined as a Bernoulli-sum law; equivalence with the separately retained PMF construction is not claimed. '
  'The real-exponent moment definition inherits Mathlib\'s convention for negative bases. The Appetizer uses positive sample size and the explicit improved-covering constant 4. '
  'Reviewers should inspect these choices against the source.')
p('<b>Operational differences:</b> the clean Appetizer\'s image attachment viewer failed, so the model continued via text and bounding-box extraction. '
  'Chapter 1 had an operational viewer fix before the main attempt. A later idle browser/login recovery used the existing harness API to resume the same session. '
  'These interventions, installation work and post-run verification time are not included as model formalization activity.')
p('<b>Protocol scope:</b> this is a custom generic protocol, not the full upstream book-formalization skill. '
  'The Appetizer had no mathematical rescue continuation. Chapter 1 had four operator-requested continuations and must not be presented as an uninterrupted autonomous one-shot experiment.')

story.append(PageBreak())
p('Assessment and independent checking', 'TitleHDP')
head('Assessment based on the measurements')
p('The clean Appetizer and Chapter 1 together required <b>'+duration(S['both_main_experiments']['measured_elapsed_seconds'])+'</b> of observed active time and <b>'+usd(S['both_main_experiments']['cost_usd'])+'</b> '
  'in API charges, including their warm setup phases. Including the separate calibration raises those totals to '+duration(S['both_including_separate_calibration']['measured_elapsed_seconds'])+' and '+usd(S['both_including_separate_calibration']['cost_usd'])+'. '
  'These runs show that obtaining buildable candidate formalizations at low inference cost was feasible in this configuration. The clean Appetizer reached reported completion in one formalization attempt, '
  'whereas Chapter 1 needed four continuations: proof-search persistence and source-correspondence coverage were the principal observed limitations. '
  'The large input totals include repeated, mostly cached context and should not be read as unique source content. '
  'The evidence supports reporting kernel-checked candidate outputs with disclosed interventions; it does not yet support an unqualified independently verified chapter-completeness claim, '
  'a success-rate estimate, or a comparative claim about Leanstral or NERSC GPU runs.')
head('Reproducibility release')
p('<link href="https://github.com/gspyrou1/hdp-formalization-deepseek" color="#167D8D">github.com/gspyrou1/hdp-formalization-deepseek</link>')
p('The repository supplies two independent Lake projects, pinned manifests, theorem/axiom inspection files, a verification script, exact finalized per-run JSON/CSV metrics, '
  'the generic protocol and continuation prompts, coverage inventories, original attempt reports and earlier Chapter 1 source snapshots. '
  'An independent checker does not need an API key or the model harness.')
p('<font face="Courier" size="8">git clone https://github.com/gspyrou1/hdp-formalization-deepseek.git<br/>'
  'cd hdp-formalization-deepseek<br/>'
  'python3 scripts/verify.py --fetch-cache</font>')
p('Install Git, Python 3 and Lean\'s Elan manager first. The first check downloads the pinned Lean/Mathlib dependencies; cache availability and machine speed affect verification time. '
  'The script checks source hashes and pins, builds both projects, and rejects unexpected axiom dependencies. '
  'Inspect actual signatures with <font face="Courier" size="8">lake env lean checks/Statements.lean</font> inside either project, then compare every source inventory row with the book.')
head('Evidence and traceability')
p('Exact figures: metrics/summary.json, metrics/runs.csv and metrics/runs/*.json. '
  'Checks performed on this exported release: reports/release-verification.json and its build/axiom logs. '
  'Original model reports can contain stale provisional metric snapshots; finalized exported metrics take precedence. '
  'Source identifiers and PDF checksums are in SOURCE.md. Book PDFs/extracted text, private credentials, raw session replay and hidden reasoning are not redistributed.', 'SmallHDP')
p('Documentation references: '
  '<link href="https://leanprover-community.github.io/install/project" color="#167D8D">Lean community project guide</link>; '
  '<link href="https://docs.github.com/en/migrations/importing-source-code/using-the-command-line-to-import-source-code/adding-locally-hosted-code-to-github" color="#167D8D">GitHub: adding locally hosted code</link>.', 'SmallHDP')

def page(canvas, doc):
    canvas.saveState()
    canvas.setStrokeColor(TEAL)
    canvas.setLineWidth(2)
    canvas.line(48,A4[1]-31,A4[0]-48,A4[1]-31)
    canvas.setFont('Helvetica',8)
    canvas.setFillColor(GRAY)
    canvas.drawString(48,25,'Clean DeepSeek HDP experiments | 2 November 2026')
    canvas.drawRightString(A4[0]-48,25,f'{doc.page} / 4')
    canvas.restoreState()

doc=SimpleDocTemplate(str(DEST),pagesize=A4,rightMargin=48,leftMargin=48,
    topMargin=48,bottomMargin=43,title='Clean DeepSeek HDP formalization: Appetizer and Chapter 1',
    author='HDP formalization experiment',pageCompression=1)
doc.build(story,onFirstPage=page,onLaterPages=page)
print(DEST)
