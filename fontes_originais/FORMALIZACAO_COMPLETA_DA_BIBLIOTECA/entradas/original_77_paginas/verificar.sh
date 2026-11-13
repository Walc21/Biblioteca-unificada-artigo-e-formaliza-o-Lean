#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$PROJECT_ROOT"
sha256sum -c SHA256SUMS.txt
python3 auditoria/auditar_fontes.py
python3 auditoria/auditar_pdfs.py \
  Biblioteca_Deterministica_Artigo_Unificado_Revisado.pdf

echo "Manifesto, fontes e PDFs verificados."
