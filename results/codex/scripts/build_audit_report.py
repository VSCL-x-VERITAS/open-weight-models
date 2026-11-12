#!/usr/bin/env python3
"""Render the independently audited Codex experiment and DeepSeek comparison."""
from pathlib import Path
import json
from decimal import Decimal
from xml.sax.saxutils import escape
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak, Preformatted

ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / 'audit'
D = json.loads((AUDIT/'audit-and-comparison.json').read_text())
C = D['codex_cases']; DS = D['deepseek']; TOTAL = D['codex_totals']
DEST = ROOT/'reports/codex-independent-audit-comparison.pdf'
DEST.parent.mkdir(parents=True,exist_ok=True)
BLUE=colors.HexColor('#163A53'); TEAL=colors.HexColor('#167D8D'); LIGHT=colors.HexColor('#EFF4F7'); GRAY=colors.HexColor('#53616B')
W=A4[0]-96
styles=getSampleStyleSheet()
styles.add(ParagraphStyle(name='TitleHDP',fontName='Helvetica-Bold',fontSize=23,leading=28,textColor=BLUE,spaceAfter=13))
styles.add(ParagraphStyle(name='SubHDP',fontName='Helvetica',fontSize=10.5,leading=15,textColor=GRAY,spaceAfter=16))
styles.add(ParagraphStyle(name='HeadHDP',fontName='Helvetica-Bold',fontSize=12.5,leading=16,textColor=BLUE,spaceBefore=12,spaceAfter=7))
styles.add(ParagraphStyle(name='BodyHDP',fontName='Helvetica',fontSize=9.2,leading=13,textColor=colors.HexColor('#21323D'),spaceAfter=8))
styles.add(ParagraphStyle(name='SmallHDP',fontName='Helvetica',fontSize=8,leading=11,textColor=GRAY,spaceAfter=6))
styles.add(ParagraphStyle(name='CellHDP',fontName='Helvetica',fontSize=8.2,leading=10.9,textColor=colors.HexColor('#21323D')))
styles.add(ParagraphStyle(name='CellHeadHDP',fontName='Helvetica-Bold',fontSize=8.1,leading=10.8,textColor=colors.white))
styles.add(ParagraphStyle(name='CodeHDP',fontName='Courier',fontSize=8.1,leading=11,textColor=BLUE,spaceAfter=8))
story=[]
def p(text,style='BodyHDP'):story.append(Paragraph(text,styles[style]))
def head(text):p(text,'HeadHDP')
def page(title):story.append(PageBreak());p(title,'TitleHDP')
def duration(s):
    s=round(s);h,s=divmod(s,3600);m,s=divmod(s,60)
    return (f'{h}h ' if h else '')+f'{m}m {s:02d}s'
def money(x,digits=4):return f'${Decimal(str(x)):,.{digits}f}'
def integer(x):return f'{x:,}'
def table(rows,widths):
    cells=[[Paragraph(escape(str(x)),styles['CellHeadHDP' if i==0 else 'CellHDP']) for x in row] for i,row in enumerate(rows)]
    t=Table(cells,colWidths=widths,repeatRows=1,hAlign='LEFT')
    t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),BLUE),('ROWBACKGROUNDS',(0,1),(-1,-1),[colors.white,LIGHT]),('VALIGN',(0,0),(-1,-1),'TOP'),('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),6),('BOTTOMPADDING',(0,0),(-1,-1),6),('LINEBELOW',(0,0),(-1,0),.6,BLUE),('LINEBELOW',(0,-1),(-1,-1),.4,colors.HexColor('#C9D6DF'))]))
    story.append(t);story.append(Spacer(1,8))
def link(url,label):return f'<link href="{escape(url)}" color="#167D8D">{escape(label)}</link>'

p('Codex HDP formalization<br/>Independent audit and DeepSeek comparison','TitleHDP')
p('Appetizer and Chapter 1 | 3 November 2026 | Clean inputs, preserved interventions','SubHDP')
head('Verdict: qualified completion')
p('<b>Both Codex projects rebuild successfully, and no blocking source-statement mismatch was found within their recorded amended mathematical scope.</b> The audit mapped all 11 supplied PDF pages into 31 Appetizer and 47 Chapter 1 comparison units. A fresh kernel audit accepted all 447 local product constants with only propext, Classical.choice and Quot.sound.')
p('This supports completion <b>with explicit source-domain conventions and the two operator amendments</b>. It does not establish a verbatim, unrestricted extended-valued formalization of every possible reading of the original PDFs. In particular, variance exercises and Chebyshev remain finite-second-moment results. The original signed/noninteger moment wording is corrected, and the Notes sharpness sentence is replaced by a precise literature-supported contract.')
table([['Codex case','Active time incl. native setup','API-equivalent estimate','Audit disposition'],['Appetizer',duration(C['appetizer']['active_seconds_excluding_between_turn_idle']),money(C['appetizer']['api_equivalent_usd'],2),'Qualified amended-scope completion'],['Chapter 1',duration(C['chapter01']['active_seconds_excluding_between_turn_idle']),money(C['chapter01']['api_equivalent_usd'],2),'Qualified amended-scope completion']],[77,140,119,W-336])
head('What the experiment demonstrates')
p('The clean Codex workflow produced kernel-checked source-level results, meaningful probability/limit constructions, and a substantial new covering lower bound. Both initial runs stopped at genuine specification questions; the operator then supplied source-only clarifications and resumed the same sessions. These are <b>assisted completions</b>, with the original unassisted outcomes preserved.')
head('Decision for reporting')
p('No routine formalization restart is required for the recorded finite-quantity amended scope. A claim covering general infinite-variance versions would require further mathematical work and review. Use the qualified wording in this report rather than an unqualified claim that the original PDF was formalized autonomously from beginning to end.')
p('The audit is an independent model review with machine-checked proof evidence, not a blinded human review or a canonical workflow Chapter PASS certificate. Original experiment files were left unchanged.','SmallHDP')

page('Protocol and interventions')
table([['Item','Recorded configuration'],['Model / effort','GPT-6.1 Sol / High; native Codex 0.165.0-alpha.1.2; native ChatGPT sign-in'],['Generic skill','formalization-collaboration v8.1.70; commit 1fb46504020649465d98ef2533a926e8c1e4dbf4'],['Lean / Mathlib','leanprover/lean4:v4.29.0-rc3; Mathlib e8ea1afc32790ce1d4e1a4e45cc412ba9388716b'],['Starting mathematical input','Separate 4-page Appetizer and 7-page Chapter 1 PDFs; each project initially only import Mathlib'],['Isolation','Native restricted-read permission profile; prior library, prior attempts, audits, credentials and the other case denied to tools; tool networking disabled'],['Roles','Generator plus fresh independent source/statement, verification and structure reviews; all native trial worker token usage included'],['Completion policy','Persisted same-session continuation; completion claims required a separate operator audit; manual publication']],[105,W-105])
head('Unassisted outcomes retained')
p('Appetizer stopped after '+duration(C['appetizer']['assistance']['unassisted_baseline']['active_seconds_excluding_between_turn_idle'])+' at an estimated '+money(C['appetizer']['assistance']['unassisted_baseline']['api_equivalent_usd'])+'; Chapter 1 stopped after '+duration(C['chapter01']['assistance']['unassisted_baseline']['active_seconds_excluding_between_turn_idle'])+' at '+money(C['chapter01']['assistance']['unassisted_baseline']['api_equivalent_usd'])+'. These include native setup. Neither original run claimed whole-source completion.')
head('Operator clarification 001')
p('<b>Appetizer:</b> the Notes assertion of sharpness was made precise using Carl-Pajor (1988), equation (2.14): a worst-case dyadic covering lower bound for diameter-one coordinate cross-polytopes, with a universal positive constant, an explicit range and arbitrary ambient covering centers. The model supplied the Lean proof; no prior Lean solution was supplied.')
p('<b>Chapter 1:</b> signed raw moments use positive integer orders; nonnegative raw moments and signed absolute moments use positive real orders. Undefined signed infinity-minus-infinity remains undefined. This is an explicit domain amendment, not a proof of the unrestricted original wording.')
head('Execution qualifications')
p('The four tagged skill packages were installed with the standard Codex installer. The full POSIX installer doctor failed on the unavailable macOS Python xattr API. Canonical Claude source admission and canonical proof/gate receipts were unavailable under the Codex-only adaptation and are not claimed. The actual isolated compiler and independent local checks were verified separately. The two assisted continuations ran in parallel, using their original session identities.')

page('Codex measurements')
rows=[['Case / phase','Active turn time','Input tokens','Output tokens','API-equivalent USD']]
for name,label in [('appetizer','Appetizer'),('chapter01','Chapter 1')]:
    m=C[name];a=m['assistance'];b=a['unassisted_baseline'];setup=m['phase_usage']['setup']
    rows += [[label+' setup',duration(m['setup_active_seconds']),integer(setup['input_tokens']),integer(setup['output_tokens']),money(m['phase_api_equivalent_usd']['setup'],6)],
      [label+' unassisted math',duration(m['unassisted_formalization_seconds']),integer(b['tokens']['input_tokens']-setup['input_tokens']),integer(b['tokens']['output_tokens']-setup['output_tokens']),money(m['unassisted_formalization_cost_usd'],6)],
      [label+' assisted math',duration(a['assisted_active_seconds']),integer(a['assisted_tokens']['input_tokens']),integer(a['assisted_tokens']['output_tokens']),money(a['assisted_api_equivalent_usd'],6)]]
table(rows,[127,87,103,88,W-405])
rows=[['All phases','Input','Cached input','Output','Reasoning subset']]
for name,label in [('appetizer','Appetizer'),('chapter01','Chapter 1')]:
    t=C[name]['tokens'];rows.append([label,integer(t['input_tokens']),integer(t['cached_input_tokens']),integer(t['output_tokens']),integer(t['reasoning_output_tokens'])])
table(rows,[80,110,110,95,W-395])
p('Appetizer: 655 native usage-bearing responses across 18 sessions; Chapter 1: 742 across 11 sessions. Every session\'s distinct response counters reconcile with its final cumulative counters; no usage anomalies were recorded. Cached input is a subset of input. Reasoning is a subset of output and is not added twice.')
head('Time boundaries')
p('The sum of case active budgets is <b>'+duration(TOTAL['sum_task_active_seconds'])+'</b>. Because assisted cases overlapped, the union of active intervals is <b>'+duration(TOTAL['union_active_seconds_across_both_cases'])+'</b>. Between-turn/operator waiting is excluded; live model/tool work and provider backoff inside a turn count. These are observed turn intervals, not GPU compute time.')
p('<b>Setup means model-side skill/environment checks, not the complete operator installation effort.</b> Operator preparation, specification research and this post-run audit are outside the native trial meter; their missing durations/tokens/cost are unknown, not zero.')
head('Pricing interpretation')
p('The total is <b>'+money(TOTAL['api_equivalent_usd'],7)+'</b>, a hypothetical standard API estimate, not a subscription charge or invoice. Rates per million: input $2, cached input $0.10, output $10. Requests above 272,000 input tokens use $4 / $0.20 / $15 for the full request; 32 Chapter 1 responses crossed that tier, versus none for Appetizer. Separate cache-write fees are not inferred from unreported fields.')
p('The estimate assumes observed Codex cache reads carry over to API use. Under a no-cache-read scenario at the same request tiers it becomes '+money(TOTAL['no_cache_read_sensitivity_usd'],2)+'; this is a sensitivity scenario, not an upper bound. Pricing verified 3 November 2026: '+link('https://developers.openai.com/api/docs/models/gpt-6.1-sol','official GPT-6.1 Sol model page')+'.','SmallHDP')

page('Appetizer: source audit')
table([['Source content','Independent disposition'],['Convex combinations; Caratheodory; n+1 sharpness','Finite-support coefficients, convex-hull membership, affine-independent simplex witness; no omitted mathematical statement found.'],['Approximate Caratheodory, Theorem 0.0.2','Euclidean source wrapper with positive sample count, repetitions and 1/sqrt(k) bound. A more general Hilbert-space theorem is proved.'],['Probabilistic construction and operative proof claims','Indexed finite PMFs, independent copies, expectation/variance identities, empirical SLLN and favorable-realization statements exist separately.'],['Exercise 0.0.3(a,b)','Both identities proved with finite-second-moment hypotheses. Bounded finite empirical sampling satisfies them.'],['Corollary 0.0.4 and Exercise 0.0.6','Actual extreme-vertex count, epsilon-balls, multiset count and improved bound; fixed absolute constant exp(1).'],['Exercise 0.0.5','The binomial coefficient chain and its stated positive integer range are represented.'],['Notes sharpness, amended U17','HDP.Sharpness.entropy_lower_bound matches the supplied dyadic contract, using c=1/1000000 and arbitrary covering centers.']],[153,W-153])
head('Sharpness is substantive and nonvacuous')
p('The witness is the convex hull of the 2n signed half-coordinate vectors in real Euclidean n-space. The code identifies its vertices and unit-diameter normalization and proves a packing/covering lower bound for every n >= 1 and 1 <= k <= n. At radii below c * min(1, sqrt(log(1+n/k)/k)), any finite ambient-center cover has more than 2^(k-1) balls. The target does not assume its own lower bound or restrict centers to empirical averages.')
head('Qualifications to retain')
p('<b>Finite moments:</b> the variance exercise versions assume L2. They do not establish every meaningful infinite-second-moment extension of the unqualified source prose. <b>Proof route:</b> the exported approximation theorem uses a deterministic greedy argument; separate probability results cover the source construction, but the main theorem does not depend on that probabilistic route.')
p('<b>Source precision:</b> k must be positive; repeated outcome values aggregate their PMF masses; closed balls retain the source\'s non-strict distance bound. The short Notes sentence alone did not determine the quantitative lower-bound contract. The amended result does not claim exact constants or all small-radius asymptotics at fixed dimension.')
p('Fresh independent review: 31 grouped source units, all four pages and operative mathematical Notes examined. No blocking mismatch found under these qualifications. The larger generator inventory and this independent grouping are not competing completeness percentages.','SmallHDP')

page('Chapter 1: source audit')
table([['Source content','Independent disposition'],['Expectations, MGF and moments','Finite-real statements carry domain hypotheses; nonnegative expectations and MGF have ENNReal representations and finite bridges; signed expectations track undefined cases.'],['Lp, Banach/Hilbert, norm inequalities','Mathlib a.e. quotient spaces and actual norm inequalities; finite and infinite norm endpoints retained. The printed p=0 endpoint is corrected to p>0.'],['Jensen and classical inequalities','Operative convexity/integrability conditions are explicit. Markov has extended nonnegative coverage; Chebyshev is finite variance.'],['CDF and tails, Proposition 1.2.1 / Exercises 1.2.2-3','Distribution determination; nonnegative and absolute layer-cake preserve infinity; signed tails use Option EReal and include one-sided infinite cases.'],['Variance sums, sample mean and rate','Finite-second-moment additivity and IID sample-mean statements are proved. Broader extended-variance identities are not asserted.'],['Law of large numbers','Genuine almost-sure convergence of empirical means, not a definition that assumes the conclusion.'],['CLT and de Moivre-Laplace','Joint IID, finite L2 and positive variance; actual normalization and Gaussian weak/CDF/tail conclusions.'],['Binomial law and Poisson limit','Independent Bernoulli-sum law linked to the standard binomial PMF; real recoding and full triangular-array weak limit, including rate zero.'],['Operator moment amendment','Nine new bridge/consistency theorems, including nonnegative integer agreement and finite/infinite domain handling; original ambiguous wording remains explicitly corrected.']],[143,W-143])
head('Scope judgment')
p('The independent reviewer mapped 47 source items across all seven pages and found no missing numbered result/exercise within the recorded amended finite-quantity scope. Positive CLT variance is necessary for standard Gaussian normalization; the zero-variance limit is not silently treated as standard Gaussian. The Lp quotient and p>0 conventions are explicit.')
p('<b>Material qualification:</b> variance additivity and Chebyshev assume MemLp 2, while their source wording does not always say finite variance. The restriction is recorded in the development and inherited by the final scoped report; the raw-moment amendment alone is not a newly issued variance amendment. An unrestricted extended-variance completion is not established.')
head('Documentation advisory')
p('The helper weighted_tail_toReal is a valid Lean conversion under totalized real-integral/toReal semantics, but its docstring overstates unrestricted literal real-integral meaning at divergent inputs. The source-facing finite real theorem requires hfinite and the ENNReal theorem retains infinity, so this is a documentation advisory, not a false accepted source theorem or a reason to restart proof search.')

page('How the Lean outputs differ')
table([['Area','Codex output','DeepSeek output'],['Approximation proof','General Hilbert-space deterministic proof; separate empirical probability infrastructure.','Finite product probability, variance computation and a favorable realization directly prove the main approximation.'],['Vertices and covering constant','Actual extreme-point count wrappers; retains multiset bound; explicit C=exp(1).','Valid finite-generator bounds; exports C=4. The actual-extreme-vertex bridge is absent.'],['Covering sharpness','Assisted dyadic entropy lower bound with concrete cross-polytopes and arbitrary centers.','Sharpness.lean proves n+1 Caratheodory sharpness, not the final Notes entropy claim.'],['Basic quantities and raw powers','Extended nonnegative/optional signed values; explicit raw-moment domain correction and bridges.','Basic expectation/MGF/moment wrappers are totalized real integrals; signed real powers inherit Real.rpow conventions.'],['Tail identities','Nonnegative/absolute infinity cases plus defined signed infinite/undefined cases.','Also has genuine ENNReal nonnegative/absolute layer-cake and Markov; signed tail identity requires Integrable.'],['Independence and SLLN','Source IID package is jointly independent; compact CLT normalizes by actual moments.','Final CLT/Poisson also jointly independent. SLLN has weaker pairwise hypotheses; historical unproved pairwise-only Prop records remain imported.'],['Binomial identification','Standard PMF law linked to arbitrary independent Bernoulli sums and real-valued recoding.','Uses canonical product-sum binomial law; separate PMF definition is retained without an exported identification theorem.'],['Organization','Explicit source wrappers and richer semantic APIs; Chapter 1 includes two large modules of 700+ lines.','Chapter 1 separates WeakConvergence/CLT/Poisson/SourceWrappers; easier topic navigation, with some historical naming clutter.']],[94,(W-94)/2,(W-94)/2])
head('Quality judgment')
p('Codex\'s artifact has broader explicit source-domain coverage and closes concrete bridges missing from DeepSeek. DeepSeek has a direct probabilistic dependency path for the appetizer and a more general SLLN entry point. Both have substantial proved analytic limit theorems; historical Prop records must not be counted as proved results. There is no uniform winner on every interface, hypothesis set or proof-design criterion.')
p('These are source/code observations, not measured claims about upgrade robustness or proof-search efficiency. Exact references for all 14 comparison points are retained in reviews/code-comparison.json.','SmallHDP')

page('Measured comparison and assessment')
table([['Case','DeepSeek active','Actual API USD','Codex active','API-equivalent USD'],['Appetizer',duration(DS['appetizer']['all_measured_phases']['measured_elapsed_seconds']),money(DS['appetizer']['all_measured_phases']['cost_usd'],4),duration(C['appetizer']['active_seconds_excluding_between_turn_idle']),money(C['appetizer']['api_equivalent_usd'],4)],['Chapter 1',duration(DS['chapter01']['main_attempt_and_continuations']['measured_elapsed_seconds']),money(DS['chapter01']['main_attempt_and_continuations']['cost_usd'],4),duration(C['chapter01']['active_seconds_excluding_between_turn_idle']),money(C['chapter01']['api_equivalent_usd'],4)]],[70,109,100,109,W-388])
p('Both columns include native/warm setup and counted model activity, excluding between-turn waiting. DeepSeek ran deepseek/deepseek-v4.1-flash-1017 through its harness/OpenRouter; Codex ran GPT-6.1 Sol/High through ChatGPT sign-in. The DeepSeek nonclean pilot and separate calibration are excluded here.')
table([['Meter total','DeepSeek main experiments','Codex incl. assisted continuation'],['Input tokens',integer(DS['both_main_experiments']['input_tokens']),integer(TOTAL['tokens']['input_tokens'])],['Cached input',integer(DS['both_main_experiments']['reported_cached_input_tokens']),integer(TOTAL['tokens']['cached_input_tokens'])],['Output tokens',integer(DS['both_main_experiments']['output_tokens']),integer(TOTAL['tokens']['output_tokens'])],['Recorded cost',money(DS['both_main_experiments']['cost_usd'],7)+' actual',money(TOTAL['api_equivalent_usd'],7)+' hypothetical']],[133,(W-133)/2,(W-133)/2])
table([['Product source size','Codex files / lines','DeepSeek files / lines'],['Appetizer','14 / 1,691','9 / 999'],['Chapter 1','6 / 2,129','14 / 2,380']],[159,(W-159)/2,(W-159)/2])
p('Files include each umbrella HDP.lean; physical lines include comments, blanks and imports, but exclude dependency code, build output and audit checks. Size and generated-constant counts are not theorem-quality or completeness scores.','SmallHDP')
head('Assessment based on the metrics and audit')
p('In this configuration, Codex reached a more explicitly scoped and semantically broader final artifact with lower observed active time per case and a higher API-equivalent spend. Its original attempts correctly exposed two source specification problems, and the added review/assistance closed them with checked mathematics. DeepSeek produced useful, lower-cost candidate developments, but its final artifacts retain the documented Notes omission and domain/bridge limitations. This supports reporting the strengths and costs of the two complete workflows. It does not isolate intrinsic model ability: the skills, independent reviewers, intervention content, caching, meter events and billing channels differed, and there is only one trial per case.')
p('DeepSeek\'s 1,066 proxied requests and Codex\'s 1,397 usage-bearing responses are different measurement units. Provider reasoning-token labels are also not directly interchangeable. Codex totals exclude this operator audit and specification-research effort; neither trial provides complete human/operator end-to-end labor cost.','SmallHDP')

page('Evidence and reproducibility')
head('Independent audit evidence')
p('Original product source was frozen by SHA-256, copied into disposable audit projects and rebuilt from fresh project build outputs. Only official pinned dependency caches were APFS-cloned. Every constant originating in all product modules, including private/generated dependencies, was checked for nonstandard axioms, custom local axioms, unsafe/partial definitions and opaque placeholders. Appetizer: 186 constants; Chapter 1: 261. Both checks passed; original product hashes remained unchanged.')
p('Fresh source reviewers worked without generator histories or completion verdicts before forming their source judgments. A separate reviewer compared the actual code. The coordinator had earlier experiment context and authored the two amendments, so this is independent of proof generation but not blinded or human certification. No canonical versioned audit, Claude admission, or Chapter PASS receipt was fabricated.')
head('Download and check')
p(link('https://github.com/gspyrou1/hdp-formalization-codex','github.com/gspyrou1/hdp-formalization-codex'))
story.append(Preformatted('git clone https://github.com/gspyrou1/hdp-formalization-codex.git\ncd hdp-formalization-codex/appetizer\nlake exe cache get\nlake build HDP\nlake env lean checks/AuditKernel.lean',styles['CodeHDP']))
p('Repeat the project commands in chapter01. Lean toolchain and dependency manifests are pinned. Product Lean source is exported byte for byte. Reports, amendments, public numeric metrics and independent review evidence accompany it; PDFs, credentials, raw native sessions and build caches are excluded.')
head('Evidence files')
p('audit-and-comparison.json: combined verdict and exact metrics. reviews/: independent source matrices and 14-point comparison. kernel-verification.json and evidence/: fresh-build logs, kernel checkers and hashes. metrics/phase-summary.csv: setup, unassisted and assisted totals. These are operator audit records, not canonical workflow receipts.')
head('Source identity and references')
for name,title in [('appetizer','Appetizer PDF'),('chapter01','Chapter 1 PDF')]:
    digest=D['frozen_inputs_sha256'][name+'/source/'+('Appetizer.pdf' if name=='appetizer' else 'Chapter01.pdf')]
    p(title+' SHA-256: <font face="Courier" size="7">'+digest[:32]+'<br/>'+digest[32:]+'</font>','SmallHDP')
p('Primary book: '+link('https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf','Vershynin, first edition, author-hosted text')+'. Sharpness source: '+link('https://www.math.uci.edu/~rvershyn/teaching/hdp/carl-pajor.pdf','Carl-Pajor (1988), pp.480, 491-492, equation (2.14)')+'. Moment convention: '+link('https://www.nist.gov/system/files/documents/2017/04/28/TutorialMetrologists2011Nov22.pdf','Possolo-Toman/NIST (2011), Section 4.8, p.17')+'.','SmallHDP')
p('Comparison release: '+link('https://github.com/gspyrou1/hdp-formalization-deepseek','DeepSeek repository')+', commit 11c5bcf20f1e91b501c96fce3038ba4ad39dafc6. This report\'s model/code comparison is independently source-based; it retains the earlier DeepSeek audit\'s distinction between valid kernel proofs and full-source correspondence.','SmallHDP')

def footer(canvas,doc):
    canvas.saveState();canvas.setStrokeColor(colors.HexColor('#D8E1E7'));canvas.line(48,39,A4[0]-48,39)
    canvas.setFont('Helvetica',7.5);canvas.setFillColor(GRAY);canvas.drawString(48,26,'HDP | Codex independent audit and DeepSeek comparison | 3 November 2026');canvas.drawRightString(A4[0]-48,26,str(doc.page));canvas.restoreState()

doc=SimpleDocTemplate(str(DEST),pagesize=A4,leftMargin=48,rightMargin=48,topMargin=43,bottomMargin=53,title='Codex HDP: independent audit and DeepSeek comparison',author='Codex independent operator audit')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print(DEST)
