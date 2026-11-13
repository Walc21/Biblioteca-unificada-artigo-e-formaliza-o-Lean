#!/usr/bin/env bash
# Compila e verifica o pacote: Lean (3 ambientes), LaTeX e relatório de pendências.
#
# Uso: ./compilar_tudo.sh [opções]
#   --sem-lean           pula o Lean
#   --sem-latex          pula o LaTeX
#   --so-status          só o relatório de pendências (nada é compilado)
#   --axiomas            roda a auditoria de axiomas (só propext, Classical.choice, Quot.sound)
#   --cache-de DIR       reaproveita .lake (Mathlib) de DIR/<ambiente>/.lake por link simbólico,
#                        em vez de baixar o cache. Ex.: ~/Projetos/Biblioteca_ALPHAGOD/Biblioteca_Reconstruida/lean4/ambientes
#   --atualizar-pdf      copia tex/principal.pdf para ../Biblioteca_Unificada.pdf ao final
# Logs em compilar_pendencias/logs/<data-hora>/. Código de saída 0 só se tudo passar.
set -uo pipefail
AQUI="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RAIZ="$(cd "$AQUI/.." && pwd)"
ENVS="$RAIZ/lean4/ambientes"
export PATH="$HOME/.elan/bin:$PATH"

DO_LEAN=1; DO_LATEX=1; DO_AXIOMS=0; CACHE_DE=""; UPDATE_PDF=0
while [ $# -gt 0 ]; do
  case "$1" in
    --sem-lean) DO_LEAN=0;;
    --sem-latex) DO_LATEX=0;;
    --so-status) DO_LEAN=0; DO_LATEX=0;;
    --axiomas) DO_AXIOMS=1;;
    --cache-de) CACHE_DE="${2:?falta o diretório}"; shift;;
    --atualizar-pdf) UPDATE_PDF=1;;
    -h|--help) sed -n '2,14p' "$0"; exit 0;;
    *) echo "opção desconhecida: $1" >&2; exit 2;;
  esac
  shift
done

LOGS="$AQUI/logs/$(date +%Y%m%d-%H%M%S)"; mkdir -p "$LOGS"
RESUMO=(); FALHAS=0
reg() { RESUMO+=("$(printf '%-30s %-8s %s' "$1" "$2" "$3")"); [ "$2" = FALHOU ] && FALHAS=$((FALHAS+1)); return 0; }

# ---------------------------------------------------------------- Lean
if [ $DO_LEAN -eq 1 ]; then
  if ! command -v lake >/dev/null; then
    echo "lake não encontrado. Instale o elan: https://github.com/leanprover/elan" >&2; exit 3
  fi
  for spec in "artigo_2:Pendencias:AuditoriaPendencias.lean" \
              "base_integrada:PendenciasParte1:AuditoriaPendenciasParte1.lean" \
              "parte_1::"; do
    IFS=: read -r nome alvo audit <<<"$spec"
    dir="$ENVS/$nome"; log="$LOGS/lean-$nome.log"
    echo ">>> Lean: $nome ${alvo:+(lake build $alvo)}"
    if [ ! -d "$dir" ]; then reg "lean $nome" FALHOU "pasta ausente"; continue; fi
    if [ -n "$CACHE_DE" ] && [ ! -e "$dir/.lake" ]; then
      if [ -d "$CACHE_DE/$nome/.lake" ]; then ln -s "$CACHE_DE/$nome/.lake" "$dir/.lake"
      else echo "    aviso: $CACHE_DE/$nome/.lake não existe"; fi
    fi
    if [ ! -d "$dir/.lake/packages/mathlib" ]; then
      echo "    baixando Mathlib e cache (precisa de rede; pode levar bastante tempo e espaço)..."
      ( cd "$dir" && lake exe cache get ) >"$LOGS/lean-$nome-cache.log" 2>&1 \
        || echo "    aviso: 'lake exe cache get' falhou; veja $LOGS/lean-$nome-cache.log"
    fi
    ( cd "$dir" && lake build $alvo ) >"$log" 2>&1; rc=$?
    sorries=$(grep -c "declaration uses 'sorry'" "$log"); errs=$(grep -c '^error' "$log")
    jobs=$(grep -o 'Build completed successfully ([0-9]* jobs)' "$log" | tail -1)
    if [ $rc -ne 0 ] || [ "$errs" -gt 0 ]; then reg "lean $nome" FALHOU "rc=$rc, $errs erro(s); veja $log"
    elif [ "$sorries" -gt 0 ]; then reg "lean $nome" FALHOU "compila, mas $sorries declaração(ões) com sorry"
    else reg "lean $nome" OK "${jobs:-compilou}, sem sorry"; fi

    if [ $DO_AXIOMS -eq 1 ] && [ -n "$audit" ] && [ -f "$dir/$audit" ]; then
      alog="$LOGS/axiomas-$nome.log"
      ( cd "$dir" && lake env lean "$audit" ) >"$alog" 2>&1
      n=$(grep -c 'depends on axioms' "$alog")
      extras=$(grep -o 'depends on axioms: \[[^]]*\]' "$alog" | sed 's/.*\[//; s/\]//' | tr ',' '\n' \
               | sed 's/^ *//; s/ *$//' | sort -u | grep -v -x -e '' -e propext -e Classical.choice -e Quot.sound || true)
      if [ "$n" -eq 0 ]; then reg "axiomas $nome" AVISO "nenhuma linha 'depends on axioms' em $alog"
      elif [ -n "$extras" ]; then reg "axiomas $nome" FALHOU "axiomas extras: $(echo $extras)"
      else reg "axiomas $nome" OK "$n teoremas, só propext/Classical.choice/Quot.sound"; fi
    fi
  done
fi

# ---------------------------------------------------------------- LaTeX
if [ $DO_LATEX -eq 1 ]; then
  echo ">>> LaTeX: tex/principal.tex"
  if ! command -v latexmk >/dev/null; then
    TEXENV="${TEX_ENV_SH:-$HOME/Projetos/Arquivos_Extraidos_2026-11-13/tex-env.sh}"
    [ -f "$TEXENV" ] && source "$TEXENV"
  fi
  if ! command -v latexmk >/dev/null; then
    reg "latex" FALHOU "latexmk ausente (instale latexmk, texlive-latex-extra, texlive-lang-portuguese)"
  else
    ( cd "$RAIZ/tex" && { [ -f principal.aux ] || pdflatex -interaction=nonstopmode -halt-on-error principal.tex; \
        latexmk -pdf -interaction=nonstopmode -halt-on-error principal.tex; } ) >"$LOGS/latex.log" 2>&1; rc=$?
    pags=$(grep -o 'Output written on principal.pdf ([0-9]* pages' "$RAIZ/tex/principal.log" | grep -o '[0-9]* pages')
    probs=$(grep -c 'undefined\|Missing character\|Overfull' "$RAIZ/tex/principal.log")
    if [ $rc -ne 0 ]; then reg "latex" FALHOU "rc=$rc; veja $LOGS/latex.log"
    elif [ "$probs" -gt 0 ]; then reg "latex" FALHOU "$pags, mas $probs aviso(s) (undefined/Missing/Overfull)"
    else reg "latex" OK "${pags:-ok}, sem referências indefinidas"; fi
    if [ $UPDATE_PDF -eq 1 ] && [ $rc -eq 0 ]; then
      cp "$RAIZ/tex/principal.pdf" "$RAIZ/Biblioteca_Unificada.pdf" && reg "pdf raiz" OK "atualizado (SHA256SUMS.txt ficou desatualizado)"
    fi
  fi
fi

# ---------------------------------------------------------------- pendências
echo ">>> Pendências"
python3 -I "$AQUI/status_pendencias.py" | tee "$LOGS/status_pendencias.txt"

echo; echo "================= RESUMO ================="
for l in "${RESUMO[@]:-}"; do [ -n "$l" ] && echo "$l"; done
echo "Logs: $LOGS"
[ $FALHAS -eq 0 ] && echo "Resultado: tudo o que foi executado passou." || echo "Resultado: $FALHAS falha(s)."
exit $([ $FALHAS -eq 0 ] && echo 0 || echo 1)
