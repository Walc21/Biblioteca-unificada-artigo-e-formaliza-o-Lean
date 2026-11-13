#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 scripts/verificar.py
if [[ -n "${TECTONIC_BIN:-}" ]]; then
  "$TECTONIC_BIN" --keep-logs artigo.tex
elif command -v tectonic >/dev/null 2>&1; then
  tectonic --keep-logs artigo.tex
else
  latexmk -xelatex -interaction=nonstopmode -halt-on-error -file-line-error artigo.tex
fi
echo "PDF composto: $(pwd)/artigo.pdf"
