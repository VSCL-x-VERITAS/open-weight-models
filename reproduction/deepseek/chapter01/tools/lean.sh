#!/bin/bash
set -euo pipefail
TASK_WORKSPACE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
args=()
for arg in "$@"; do
 if [[ "$arg" == *.lean && "$arg" != /* && -f "$arg" ]]; then
  arg="$(cd -- "$(dirname -- "$arg")" && pwd -P)/$(basename -- "$arg")"
 fi
 args+=("$arg")
done
cd -- "$TASK_WORKSPACE/lean"
exec "/Users/gspyrou/Documents/ChatGPT/George S/.tools/elan/bin/lake" env lean "${args[@]}"
