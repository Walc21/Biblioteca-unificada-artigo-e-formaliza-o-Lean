# PendenciasParte1

Provas complementares da Parte I, com Lean/Mathlib 4.28.0. Compilar no ambiente
`lean4/ambientes/base_integrada` com `lake build PendenciasParte1` e auditar com
`lake env lean AuditoriaPendenciasParte1.lean`.

| Item | Arquivo | Declarações principais |
|---|---|---|
| I.6.3 | `Refinamento.lean` | `PendenciasParte1.certRefine`, `PendenciasParte1.certified_refinement` (raízes contidas em `[α,β]`) |
| I.6.3 | `RefinamentoCobertura.lean` | `CoberturaExterna.certRefineProjected`, `projected_certificate_sound` (certificado da extensão por caixa projetada) |
| I.6.4 | `Refinamento.lean` | `PendenciasParte1.certified_refinement` (raízes contidas em `[α,β]`) |
| I.6.4 | `RefinamentoCobertura.lean` | `CoberturaExterna.refinement_contract_external`, `certified_refinement_external` (cobertura diádica externa, sem `hsub`), `thirds_success` (exemplo `[1/3, 2/3]`) |

`Refinamento.lean` exige as raízes contidas em `[α,β]`, o que exclui intervalos como `[1/3, 2/3]`. `RefinamentoCobertura.lean` remove essa hipótese: o certificado de cada célula é calculado numa caixa racional que envolve a projeção da célula sobre `[α,β]`, e a extensão quadrática satisfaz `F'' x = f''(clamp x)`. A caixa pode incluir pontos fora de `[α,β]`; nesse caso a rotina pode falhar, mas uma falha nunca é usada como certificado.

O algoritmo aborta quando uma célula consultada não é certificada. A conclusão de
correção/término mantém o contrato do TeX sobre o majorante intervalar. O programa
é uma definição matemática `noncomputable`; não há medição de execução nativa.
Os axiomas da auditoria são apenas `propext`, `Classical.choice`, `Quot.sound`.
