#!/bin/bash
set -euo pipefail
umask 077
EXPERIMENT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$EXPERIMENT_DIR/inside-env.sh"
unset OPENROUTER_API_KEY
"$CLEAN_NODE" "$EXPERIMENT_DIR/experiment.mjs" ensure
if "$CLEAN_NODE" "$EXPERIMENT_DIR/reuse-running-harness.mjs" "$EXPERIMENT_DIR"; then
 exit 0
else
 status=$?
 [[ "$status" == 10 ]] || exit "$status"
fi
cd -- "$CLEAN_WORKSPACE"
: > "$EXPERIMENT_DIR/logs/server.log"
exec /usr/bin/sandbox-exec -f "$EXPERIMENT_DIR/isolation.sb" /usr/bin/env -i  PATH="$(dirname -- "$CLEAN_NODE"):$CLEAN_ELAN/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin"  USER="gspyrou" LOGNAME="gspyrou" LANG="en_US.UTF-8"  DSH_HOME="$CLEAN_DSH_HOME" DSH_AGENTS_HOME="$CLEAN_DSH_HOME/agents"  ELAN_HOME="$CLEAN_ELAN" XDG_CACHE_HOME="$CLEAN_DSH_HOME/cache" TMPDIR="$CLEAN_DSH_HOME/tmp"  "$CLEAN_NODE" "$CLEAN_HARNESS" web --host 127.0.0.1 --port 3086 --no-open  > >(tee -a "$EXPERIMENT_DIR/logs/server.log") 2>&1
