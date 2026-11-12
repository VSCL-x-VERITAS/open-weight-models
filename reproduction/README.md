# Rerun the experiments

The original experiments ran on macOS. Use a separate private directory for
each rerun and a dedicated elan installation. Keep the checkout, reports,
credentials, and any previous attempts outside the model's working directory.
Install Python 3.10+, Git, Poppler (`pdftotext`, `pdfinfo`, `pdftoppm`), and elan.
Set the shell variables in the commands below to absolute paths. The preparation
command verifies the PDF hash, copies the pinned Lake configuration, writes only
`import Mathlib` to the initial Lean file, fetches the official dependencies,
and checks their revisions before starting a model. Use `--stage-only` to inspect
the clean inputs without downloading or launching anything.

For both models set `CASE` to `appetizer` or `chapter01`, `PDF` to the exact
extract, `SCRATCH` to a new private directory under `/Users` outside this checkout,
and `LEAN_HOME` to the dedicated elan directory containing `bin/lake`.
Keep the Appetizer and Chapter 1 sessions separate. The source files and their
hashes are listed in [SOURCE.md](../results/deepseek/SOURCE.md).

## DeepSeek

The experiment used Node 24.19.0, DSH `0.2.1-rc.5`, and OpenRouter model
`deepseek/deepseek-v4.1-flash-1017` with high reasoning. Install the pinned DSH
package and its dependency lock into a separate directory `DSH_INSTALL`:

```sh
mkdir -p "$DSH_INSTALL"
cp reproduction/deepseek/package.json reproduction/deepseek/package-lock.json "$DSH_INSTALL/"
(cd "$DSH_INSTALL" && npm ci)
```

Set `NODE_BIN` to the versioned Node installation's `bin/node`. Create a private
file (`chmod 600`) under `/Users` outside the repository and scratch directory,
and set `UPSTREAM_CREDENTIALS` to its path. The file uses the DSH credentials
schema shown below. Enter your own key directly in your editor.

```yaml
version: 1
refs:
  OPENROUTER_API_KEY: YOUR_OPENROUTER_KEY
```

```sh
python3 reproduction/prepare.py deepseek "$CASE" "$PDF" "$SCRATCH" \
  --elan "$LEAN_HOME" --node "$NODE_BIN" --harness "$DSH_INSTALL" \
  --upstream-credentials "$UPSTREAM_CREDENTIALS"
```

The script relocates the recorded macOS Seatbelt profile and launch scripts,
sets up a separate random local proxy credential, checks the read fence and
runs an empty Lean build inside the sandbox. `danger-full-access` is the inner
DSH setting and relies on the outer Seatbelt wrapper. Use the generated
`start-harness.sh` to keep that outer wrapper active.

1. Go to `$SCRATCH/output/deepseek-$CASE-clean-api` and run
   `./start-harness.sh`. Open its loopback UI in a browser. Appetizer uses
   UI/meter ports 3086/3087 and Chapter 1 uses 3084/3085.
2. From another terminal in the same directory run
   `./experiment.sh start "hdp-$CASE" --phase setup`.
   Create a fresh session in the generated workspace and submit the exact text
   in `workspace/run/SETUP_PROMPT.txt`.
3. After setup readiness and once the turn has stopped, run
   `./experiment.sh phase formalization` and submit
   `workspace/run/START_PROMPT.txt` in the same session.
4. If work stops before completion, keep the same workspace and review the
   checkpoint. For Chapter 1 the archived continuation prompts are
   `RESUME_02_PROMPT.txt` through `RESUME_05_PROMPT.txt`. Use them only when
   their prerequisites match the checkpoint. Record the prompt and intervention,
   and stop and export the current meter run before arming the next one with
   `--phase formalization`. The historical continuations share evolving Lean
   sources. The separate Chapter 1 setup calibration is excluded from the main
   totals.
5. Use `./experiment.sh status` and `./experiment.sh idle` to inspect a run.
   After the turn ends use `./experiment.sh stop`, then
   `./experiment.sh reconcile` to recover usage and costs missing from responses.
   `./experiment.sh export RUN_ID` exports the archived meter totals. The idle
   observer uses native session events. Keep accounting gaps visible in the
   resulting coverage fields. Exported phase data lands under
   `workspace/reports/metrics/`.

The files under [deepseek/](deepseek/) preserve original meter, watcher, harness,
and monitoring source. The original preflight and snapshot scripts are
historical operator tools with original paths and run IDs. New setups use the
checks in `prepare.py`. The receipt evidence contains allowlisted numeric fields
and phase labels from the original exports. It omits provider identifiers and
request/response bodies. Reconciliation, billing deduplication and timing
definitions are implemented in `metrics.mjs` and `idle-accounting.mjs`.

```sh
node --test reproduction/deepseek/appetizer/*.test.mjs
```

The tests use loopback mock servers and require permission to bind locally.
They do not call OpenRouter.

## Codex

The original client was Codex `0.165.0-alpha.1.2` with native ChatGPT sign-in,
GPT-6.1 Sol, and High reasoning. The driver depends on that version's app-server
interface and restricted-read permission profiles. Set `CODEX_BIN` to a
compatible binary, `CODEX_AUTH_FILE` to an existing file-backed native sign-in
file, and `WORKFLOW_DIR` to a clean checkout of the generic workflow:

```sh
git clone https://github.com/VSCL-x-VERITAS/formalization-collaboration.git "$WORKFLOW_DIR"
git -C "$WORKFLOW_DIR" checkout --detach 1fb46504020649465d98ef2533a926e8c1e4dbf4
python3 reproduction/prepare.py codex "$CASE" "$PDF" "$SCRATCH" \
  --elan "$LEAN_HOME" --codex "$CODEX_BIN" \
  --workflow "$WORKFLOW_DIR" --auth "$CODEX_AUTH_FILE"
```

Use `--tool-bin` if the generic tools are not in `/opt/homebrew/bin`, and
`--models-cache` if the pinned client needs its existing native model cache.
The setup exposes the four generic workflow skills at the pinned release
(v8.1.70). It leaves the upstream book packages and credential store outside the
tool read boundary. The original macOS install used the exact tagged skills
after the full POSIX installer's xattr check failed. The run uses independent
Codex roles and a documented source-admission adaptation for Codex-only review.

```sh
RUN="$SCRATCH/output/codex-$CASE-clean-api"
python3 results/codex/scripts/run_trial.py "$RUN"
```

The driver submits the setup and formalization prompts as separate turns. The
setup turn checks restricted access and the clean Lean project. The driver
records neutral continuations until a declared completion or a source blocker.
Inspect `workspace/reports/STATUS.json` and
`observer/measurement-summary.json`. Original prompts are in each frozen
project's `experiment/` directory.

To replay the documented assistance, first preserve and audit the unassisted
checkpoint. If it has the same source blocker, copy the case's
`operator-clarification-001/CLARIFICATION.txt` to
`$RUN/workspace/source/operator-clarification-001/CLARIFICATION.txt` and its
`RESUME_PROMPT.txt` to `$RUN/workspace/run/RESUME_AFTER_OPERATOR_001.txt`.
Record this as an assisted continuation. Resume the same native thread with
`python3 results/codex/scripts/run_trial.py --resume "$RUN"`. If the blocker
differs, report it rather than applying the historical amendment blindly.

```sh
python3 results/codex/scripts/check_metrics.py
```

The observer records per-response usage from native sessions and timestamps
from the driver. Export sanitized metrics with
`python3 reproduction/codex/export_metrics.py "$RUN" /path/to/private-export`.
The dated pricing file and phase summaries are under
[Codex metrics](../results/codex/metrics/). The Codex amounts estimate API
charges using the measured counters. DeepSeek amounts use observed OpenRouter
charges. Both exclude between-turn operator waiting and the independent
post-run audits. Keep raw native sessions and sign-in data private.
