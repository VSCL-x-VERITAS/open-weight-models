#!/bin/bash
set -euo pipefail
umask 077
EXPERIMENT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
unset OPENROUTER_API_KEY
exec /Users/gspyrou/.nvm/versions/node/v24.19.0/bin/node "$EXPERIMENT_DIR/experiment.mjs" "$@"
