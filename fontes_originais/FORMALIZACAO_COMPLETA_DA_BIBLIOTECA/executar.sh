#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

mode="${1:---completo}"
if [[ $# -gt 1 || ( "$mode" != "--completo" && "$mode" != "--estatico" ) ]]; then
  echo 'Uso: ./executar.sh [--completo|--estatico]' >&2
  exit 2
fi

mkdir -p evidencias/validacoes
run_dir="$(mktemp -d "evidencias/validacoes/$(TZ=America/Sao_Paulo date +%Y-%m-%d_%H-%M-%S)_XXXXXX")"
trap 'echo "Execução interrompida ou com erro; consulte os registros em $run_dir" >&2' ERR

python3 verificar_imports.py 2>&1 | tee "$run_dir/imports.log"
python3 verificar_v2.py 2>&1 | tee "$run_dir/estrutura_v2.log"
python3 verificar_pontes.py 2>&1 | tee "$run_dir/pontes.log"

if [[ "$mode" == "--completo" ]]; then
  lake --version | tee "$run_dir/ambiente.log"
  lake build SemanticAudit > "$run_dir/build.log" 2>&1
  tail -n 6 "$run_dir/build.log"
  echo "Auditoria de axiomas em execução; pode levar vários minutos. Registro: $run_dir/axiomas.log"
  lake env lean AuditoriaAxiomasPontes.lean > "$run_dir/axiomas.log" 2>&1
  echo 'Compilação e execução da auditoria de axiomas concluídas.'
fi

printf 'SUCESSO %s\n' "$mode" > "$run_dir/resultado.txt"
echo "Registros: $run_dir"
