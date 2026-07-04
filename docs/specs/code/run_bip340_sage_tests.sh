#!/usr/bin/env bash
# Run all Sage BIP-340 tests.  Requires Sage (importable via sage.all).
# Usage: ./run_bip340_sage_tests.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

export PYTHONPATH="$SCRIPT_DIR"

# Find a Python that can import sage.all.
SAGE_PYTHON=""
for cand in python3 sage; do
  if command -v "$cand" &>/dev/null; then
    if "$cand" -c "import sage.all" 2>/dev/null; then
      SAGE_PYTHON="$cand"
      break
    fi
  fi
done

if [ -z "$SAGE_PYTHON" ]; then
  echo "ERROR: No Python with 'sage.all' found." >&2
  echo "Try: /home/jrml/miniforge3/bin/python or install SageMath." >&2
  exit 1
fi

echo "Using Sage Python: $(command -v "$SAGE_PYTHON")"

echo "=== Sage BIP-340 reference tests ==="
"$SAGE_PYTHON" -m pytest tests/test_bip340.py -v --tb=short

echo ""
echo "=== Sage BIP-340 circuit parity tests ==="
"$SAGE_PYTHON" -m pytest tests/test_bip340_circuit.py -v --tb=short

echo ""
echo "=== All Sage BIP-340 tests complete ==="
