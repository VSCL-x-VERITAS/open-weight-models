#!/bin/bash
set -euo pipefail
EXPERIMENT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
source "$EXPERIMENT_DIR/inside-env.sh"
cd -- "$CLEAN_WORKSPACE"
exec /usr/bin/sandbox-exec -f "$EXPERIMENT_DIR/isolation.sb" /usr/bin/env -i  PATH="$(dirname -- "$CLEAN_NODE"):$CLEAN_ELAN/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin"  USER="gspyrou" LOGNAME="gspyrou" LANG="en_US.UTF-8"  DSH_HOME="$CLEAN_DSH_HOME" DSH_AGENTS_HOME="$CLEAN_DSH_HOME/agents"  ELAN_HOME="$CLEAN_ELAN" XDG_CACHE_HOME="$CLEAN_DSH_HOME/cache" TMPDIR="$CLEAN_DSH_HOME/tmp" "$@"
