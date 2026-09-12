#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if ! command -v lake >/dev/null 2>&1; then
  export ELAN_HOME="$PWD/.tooling/elan"
  export PATH="$ELAN_HOME/bin:$PATH"
fi

python3 scripts/check_sources.py
lake build LectureNotes
lake env lean Audit.lean
