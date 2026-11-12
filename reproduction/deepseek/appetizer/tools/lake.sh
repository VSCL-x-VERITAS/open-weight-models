#!/bin/bash
set -euo pipefail
TASK_WORKSPACE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd -- "$TASK_WORKSPACE/lean"
exec "/Users/gspyrou/Documents/ChatGPT/George S/.tools/elan/bin/lake" "$@"
