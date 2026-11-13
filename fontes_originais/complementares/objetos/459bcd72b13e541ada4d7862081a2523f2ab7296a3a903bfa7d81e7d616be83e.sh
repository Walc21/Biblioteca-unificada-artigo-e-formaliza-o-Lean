#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 scripts/figuras.py
python3 scripts/codigos.py
python3 scripts/verificar.py
latexmk -xelatex -interaction=nonstopmode -halt-on-error -file-line-error artigo.tex
echo "PDF composto: $(pwd)/artigo.pdf"
