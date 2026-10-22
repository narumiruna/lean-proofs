#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
uv run --no-project python scripts/check_exercises.py "$@"
lake build
lake env lean scripts/check_axioms.lean
uv run --no-project python -m unittest discover -s scripts/tests -v
