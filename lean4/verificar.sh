#!/usr/bin/env bash
set -euo pipefail

ambientes="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/ambientes" && pwd)"

auditar() {
  local arquivo
  for arquivo in "$@"; do
    printf '\n== %s/%s ==\n' "${PWD##*/}" "$arquivo"
    # As auditorias com #print axioms só exibem as dependências.
    # pipefail também preserva falhas do próprio Lean.
    lake env lean "$arquivo" | awk '
      { print }
      / depends on axioms: \[/ {
        axiomas = $0
        sub(/^.* depends on axioms: \[/, "", axiomas)
        coletando = 1
      }
      coletando && !/ depends on axioms: \[/ { axiomas = axiomas " " $0 }
      coletando && /\][[:space:]]*$/ {
        coletando = 0
        sub(/\][[:space:]]*$/, "", axiomas)
        gsub(/[[:space:]]/, "", axiomas)
        total = split(axiomas, nomes, ",")
        for (i = 1; i <= total; i++) {
          if (nomes[i] != "propext" && nomes[i] != "Classical.choice" &&
              nomes[i] != "Quot.sound") {
            fflush()
            printf "Axioma fora da lista permitida: %s\n", nomes[i] > "/dev/stderr"
            falhou = 1
          }
        }
      }
      END {
        if (coletando) {
          fflush()
          print "Lista de axiomas incompleta." > "/dev/stderr"
        }
        exit (falhou || coletando)
      }
    '
  done
}

cd "$ambientes/artigo_2"
lake build ValidationAll Pendencias
auditar AuditoriaPacote.lean AuditoriaPendencias.lean CorrespondenciasAudit.lean

cd "$ambientes/base_integrada"
lake build Unified SemanticAudit PendenciasParte1 RequestProject.Main
auditar AuditoriaIntegracao.lean AuditoriaAxiomasPontes.lean AuditoriaAxiomas.lean AuditoriaPendenciasParte1.lean

cd "$ambientes/parte_1"
lake build ValidationAll
auditar AuditoriaPacote.lean CorrespondenciasAudit.lean
