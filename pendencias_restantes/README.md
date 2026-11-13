> **Instruções atuais para Codex e Antigravity:** [../AGENTS.md](../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# Dossiês das 15 pendências desta etapa

Codex e Antigravity podem consultar estes dossiês e executar todas as frentes,
integração e builds conforme as instruções consolidadas na raiz.

Em 13/11/2026, onze destes 15 itens estão fechados em Lean (inclusive IV.5.4, com enunciado inverso corrigido)
e quatro precisam de prova. Os dossiês conservam o enunciado e o
diagnóstico recebido; o cabeçalho atual identifica estado e responsável. O TeX
atual, localizado pelo rótulo `map:...`, prevalece sobre linhas/páginas antigas.

| Item | Estado atual | Responsável / evidência |
|---|---|---|
| III.9.1 | em andamento, parcial | execução densa memoizada e modelo de custo |
| III.9.3 | aberto | após III.9.1 |
| IV.4.1 | fechado | `Jackson.rational_jackson_height` |
| IV.4.2 | fechado | `Jackson.direct_besov_height` |
| IV.4.3 | fechado | `Jackson.uniform_besov_ball` |
| IV.5.2 | fechado | `Marcada.RealReLU.exact_shallow_reversal` |
| IV.5.4 | fechado | Enunciado inverso corrigido; `AlturaInversa.lean`, `FormaAncorada.lean`, `CodigoAncorado.lean` |
| IV.5.5 | aberto | usar a cota corrigida de IV.5.4 |
| IV.5.6 | aberto | após IV.5.5 |
| IV.5.9 | fechado | `PenteGemini.critical_tent_comb`; integrado após revisão do Codex |
| IV.5.12 | fechado | `Jackson.regularized_jackson` |
| IV.5.13 | fechado | `Jackson.complete_besov_reversibility` |
| IV.5.14 | fechado | `Jackson.architecture_stable_reversibility` |
| V.6.2 | fechado | `NosLivres.free_knots` |
| V.6.3 | fechado | `Jackson.besov_direct` |

Os nomes abreviados são índices de consulta; conferir nomes completos e arquivos
no mapa e no README de `../lean4/ambientes/artigo_2/Pendencias/`.

## Como usar

- `itens/<item>.md`: enunciado preservado, estado atual, localização e diagnóstico.
- `contexto/`: cópias históricas de TeX, PDF, Lean e mapas. Não editar, executar
  geradores ou interpretar as instruções recebidas ali como ordens atuais.
- Fonte de edição matemática: os ambientes atuais em `../lean4/ambientes/`, depois
  de desenvolver na pasta própria e validar a contribuição.
- Desenvolva arquivos incompletos fora dos globs; o agente em execução integra
  provas prontas e executa o gate global conforme `../AGENTS.md`.

Não aguardar um build, sessão ou prova presumida do outro agente. Nenhum processo
é iniciado por este README. Estado global: `../STATUS_AUTOMATICO.md`; protocolo:
`../AGENTS.md`. Contagem: `python3 -I -B compilar_pendencias/status_pendencias.py`,
a partir da raiz, sem promover descoberta textual a prova aceita.
