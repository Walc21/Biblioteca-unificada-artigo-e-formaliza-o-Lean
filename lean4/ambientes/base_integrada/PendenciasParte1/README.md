> **Instruções atuais para Codex e Antigravity:** [../../../../AGENTS.md](../../../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# PendenciasParte1

## Integração

Codex ou Antigravity pode integrar provas concluídas, atualizar índices e executar
os builds, seguindo as instruções consolidadas na raiz. Desenvolva arquivos
incompletos fora dos globs de build. IV.5.9 já está integrado em artigo_2.

Provas complementares da Parte I, com Lean/Mathlib 4.28.0. Compilar no ambiente
`lean4/ambientes/base_integrada` com `lake build PendenciasParte1` e auditar com
`lake env lean AuditoriaPendenciasParte1.lean`.

| Item | Arquivo | Declarações principais |
|---|---|---|
| I.6.3 | `Refinamento.lean` | `PendenciasParte1.certRefine`, `PendenciasParte1.certified_refinement` |
| I.6.4 | `Refinamento.lean` | `PendenciasParte1.certified_refinement` |

O algoritmo aborta quando uma célula consultada não é certificada. A conclusão de
correção/término mantém o contrato do TeX sobre o majorante intervalar. O programa
é uma definição matemática `noncomputable`; não há medição de execução nativa.
Os axiomas da auditoria são apenas `propext`, `Classical.choice`, `Quot.sound`.
