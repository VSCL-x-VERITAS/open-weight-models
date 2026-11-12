# Setup Readiness Report

Phase: warm setup only. No mathematical PDF content was read, no inventory or
theorem targets were constructed, and nothing was proved.

## Checks performed

| Check | Result |
|---|---|
| `run/SETUP_PROMPT.txt`, `run/PROTOCOL.txt`, `AGENTS.md` read | OK |
| Lean toolchain | `leanprover/lean4:v4.29.0-rc3` (pinned via `lean/lean-toolchain`) |
| Lean binary | 4.29.0-rc3, arm64-apple-darwin24.6.0, commit 5d86aa4032284a5242470e95fbe25f1ff506763d |
| Lake binary | 5.0.0-src+5d86aa4, resolves pinned toolchain through `lean-toolchain` |
| Mathlib pin in `lakefile.toml` | `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b` |
| Mathlib checkout HEAD | matches pin exactly (`git rev-parse HEAD`) |
| Mathlib build cache | present, ~5.8 GB under `lean/.lake/packages/mathlib/.lake/build` |
| Focused compiler check | `import Mathlib`, `#check Nat.add_comm`, `#check MeasureTheory.Measure`, `#print axioms Nat.add_comm` succeeded; no axioms reported for the sample theorem |
| Project build | `tools/lake.sh build HDP` completed successfully (8050 jobs) |
| `lean/HDP.lean` | unchanged initial content: `import Mathlib` |
| Source PDF | `source/Appetizer.pdf`, 4 pages, PDF 1.6, unencrypted, parses via poppler |
| Source checksum | sha256 `164189f2c6e5d39c6b8aa96f3a3c18d02f42194b890be3610aaa44d7c487ca7f`, matches run manifest |
| PDF tooling | `pdfinfo`, `pdftotext`, `pdftoppm`, `pdfimages`, `python3` available; `mutool`/`qpdf` absent, not required |
| Resources | ~215 GB free disk, 24 GB RAM |
| Git state | no commits; all workspace files untracked (expected clean-initial state) |

## Notes / limitations

- `bash` executed `/tmp` writes were refused by the session sandbox despite the
  configured full-access file policy; the compiler check was therefore run from
  a temporary file in the workspace and removed afterwards. No workspace state
  changes remain from that check.
- `reports/metrics/` is operator-owned observational metadata and was not read
  as mathematical input (only `latest-summary.json` was inspected to confirm the
  run manifest and pins).
- No changes were made to the model, tools, pins, access policy, or measurement
  controls. No web access or external mathematical material was used.
- `python3` has neither PyMuPDF nor pypdf installed; poppler command-line tools
  are sufficient for text/rendering if needed.

## Readiness

Lean compiler, pinned Mathlib, project build, and generic PDF tooling all check
out. Ready to stop and await the fixed formalization launch.
