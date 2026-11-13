#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
export PYTHONDONTWRITEBYTECODE=1
export MPLCONFIGDIR="${TMPDIR:-/tmp}/biblioteca-unificada-mpl"

python3 "$PROJECT_ROOT/reproducibility/biblioteca/reproduzir_curvas.py" \
  --language pt \
  --output-root "$PROJECT_ROOT/reproducibility/biblioteca"

for script in \
  seletor_dinamico_exato.py \
  constante_diadica.py \
  espacos_aproximacao.py \
  restricoes_rede.py \
  reversibilidade_regularizada.py
do
  python3 "$PROJECT_ROOT/reproducibility/selecao/$script" \
    --output-root "$PROJECT_ROOT"
done

python3 "$PROJECT_ROOT/auditoria/auditar_fontes.py"

(
  cd "$PROJECT_ROOT/artigo"
  latexmk -C artigo_nacional.tex
  latexmk -pdf -interaction=nonstopmode -halt-on-error artigo_nacional.tex
  for log in artigo_nacional.log
  do
    if rg -n \
      'Overfull \\hbox|Overfull \\vbox|There were undefined references|Citation .+ undefined|multiply defined' \
      "$log"
    then
      echo "Falha de composição registrada em $log." >&2
      exit 1
    fi
  done
  cp artigo_nacional.pdf "$PROJECT_ROOT/Biblioteca_Deterministica_Artigo_Unificado_Revisado.pdf"
)

python3 "$PROJECT_ROOT/auditoria/auditar_pdfs.py" \
  "$PROJECT_ROOT/Biblioteca_Deterministica_Artigo_Unificado_Revisado.pdf"

(
  cd "$PROJECT_ROOT/artigo"
  latexmk -C artigo_nacional.tex
  LATEX_CLEAN_DIR="$(mktemp -d "${TMPDIR:-/tmp}/biblioteca-unificada-latex.XXXXXX")"
  for stem in artigo_nacional
  do
    for suffix in aux bbl blg fdb_latexmk fls log out pdf toc
    do
      if [[ -e "${stem}.${suffix}" ]]
      then
        mv "${stem}.${suffix}" "$LATEX_CLEAN_DIR/"
      fi
    done
  done
)

(
  cd "$PROJECT_ROOT"
  find . -type f \
    ! -name 'SHA256SUMS.txt' \
    ! -name '*.zip' \
    ! -name '*.aux' \
    ! -name '*.blg' \
    ! -name '*.bbl' \
    ! -name '*.fdb_latexmk' \
    ! -name '*.fls' \
    ! -name '*.log' \
    ! -name '*.out' \
    ! -name '*.toc' \
    ! -name '*.pyc' \
    -print0 | sort -z | xargs -0 sha256sum > SHA256SUMS.txt
)

echo "Compilação do documento-sistema corrigido concluída."
