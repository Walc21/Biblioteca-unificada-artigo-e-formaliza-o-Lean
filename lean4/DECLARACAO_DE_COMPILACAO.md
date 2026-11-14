# Declaração de compilação da formalização em Lean 4

**Victor Gabriel de Oliveira** · recompilação de 13 e 14 de novembro de 2026

Declaro que os três ambientes Lean deste repositório (`artigo_2`, `base_integrada` e `parte_1`) foram
recompilados do zero com **Lean 4.28.0** e **Mathlib v4.28.0**, a partir dos fontes versionados na árvore
`lean4/` do commit `bda95cf`, sem erros e sem `sorry`. As ressalvas abaixo fazem parte desta declaração e
delimitam o que ela afirma.

## O que foi feito

A compilação usou uma cópia de trabalho contendo apenas os arquivos versionados. Dos ambientes locais, foi
reaproveitado somente o cache já compilado do Mathlib, ligado por link simbólico. Os módulos do projeto
foram compilados com `lake build`:

| Ambiente | Alvos compilados | Tarefas | Resultado |
|---|---|---|---|
| `artigo_2` | `ValidationAll`, `Pendencias` | 8095 | sucesso, 0 erros |
| `base_integrada` | `Unified`, `SemanticAudit`, `PendenciasParte1`, `RequestProject.Main` | 8093 e 8034 | sucesso, 0 erros |
| `parte_1` | `ValidationAll` | 8036 | sucesso, 0 erros |

Nenhum log contém o aviso «declaration uses 'sorry'». Foram compilados 144 módulos e executados 9 scripts
de auditoria, o que cobre os 153 arquivos `.lean` versionados.

## Auditoria de axiomas

Foram executadas, com `lake env lean`, as nove auditorias do repositório. Todas terminaram com código de
saída 0. Em nenhuma aparece `sorryAx`, e todas as declarações dependem somente de `propext`,
`Classical.choice` e `Quot.sound`:

| Ambiente | Auditoria | Declarações |
|---|---|---|
| `artigo_2` | `AuditoriaPacote` | 2199 |
| `artigo_2` | `AuditoriaPendencias` | 110 |
| `base_integrada` | `AuditoriaIntegracao` | 3265 |
| `base_integrada` | `AuditoriaAxiomasPontes` | 2755 (2196 teoremas) |
| `base_integrada` | `AuditoriaAxiomas` | 2597 (2056 teoremas) |
| `base_integrada` | `AuditoriaPendenciasParte1` | 2 |
| `parte_1` | `AuditoriaPacote` | 509 |

`CorrespondenciasAudit` (em `artigo_2` e em `parte_1`) confere que os nomes citados existem e têm o tipo
esperado. Uma busca textual nos 153 arquivos, ignorando comentários, não encontrou `sorry`, `admit` nem
declarações `axiom`. As contagens incluem declarações auxiliares geradas pelo Lean e não devem ser somadas
entre auditorias, porque há sobreposição de módulos importados.

## Como reproduzir

```bash
cd lean4/ambientes/artigo_2
lake exe cache get
lake build ValidationAll Pendencias
lake env lean AuditoriaPendencias.lean

cd ../base_integrada && lake exe cache get
lake build Unified SemanticAudit PendenciasParte1 RequestProject.Main
lake env lean AuditoriaIntegracao.lean

cd ../parte_1 && lake exe cache get && lake build ValidationAll
```

## Ressalvas

1. **O Mathlib não foi recompilado.** Foi usado o cache já compilado na máquina de trabalho.
2. **Compilar não é o mesmo que corresponder ao artigo.** A compilação mostra que cada teorema vale como
   está enunciado em Lean. Ela não mostra que o enunciado em Lean diz o mesmo que o teorema do texto.
   Das 151 correspondências do mapa, 77 foram apenas *inspecionadas* e 20 *integradas à base*; elas não
   foram reauditadas semanticamente uma a uma. Não se afirma formalização integral do artigo.
3. **III.9.1** usa um modelo de custo unitário explícito e não implementa o desempate canônico por κ
   (formalizado no seletor funcional de III.7.4). **III.9.3** toma como hipótese do modelo (`BitModel`) o
   custo das operações aritméticas em bits; não há modelo de máquina em Lean.
4. **IV.5.4** foi fechada com o enunciado **corrigido**: a cota impressa originalmente era falsa
   (contraexemplo `R(x)=x`, provado em Lean). Na parte direta, a forma reduzida é a estrutura `Anchored`,
   sem ponte formal para `RealReLU`.
5. **Os programas Python de `verificacao/` não fazem parte das provas** e não foram reexecutados
   integralmente nesta recompilação.
6. **Documentos herdados.** `documentacao/INTEGRACAO_NORMALIZACAO.md` cita registros em `evidencias/` e um
   `executar.sh` que não estão neste repositório.
