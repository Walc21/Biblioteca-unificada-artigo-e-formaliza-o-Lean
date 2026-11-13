# Índice: o que NÃO bate com o Lean e ainda precisa ser provado

Método: para cada um dos 151 resultados numerados, o enunciado TeX (hipóteses, quantificadores, conclusão) foi lido contra a assinatura Lean das declarações associadas em `mapas/correspondencia_completa.json`. **É julgamento por leitura; o Lean não foi recompilado.** Os pares lado a lado estão em `pares_tex_lean.json`.

## Resumo

| Parte | Total | Bate | Observação (sem Lean) | **Não bate / a provar** |
|---|---:|---:|---:|---:|
| I | 24 | 22 | 0 | **2** |
| II | 40 | 40 | 0 | **0** |
| III | 59 | 37 | 7 | **15** |
| IV | 24 | 0 | 3 | **21** |
| V | 4 | 0 | 0 | **4** |
| **Total** | 151 | 99 | 10 | **42** |

A Parte II (normalização) bate integralmente com o Lean (`Montagens` e `SemanticBridge`): 40 resultados, nenhum pendente.

## Categorias

- **H** (8): Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo
- **P** (3): Cobertura parcial: o Lean prova algo mais fraco ou diferente do enunciado
- **A** (3): Algoritmo sem implementação certificada: há prova da recorrência, falta o programa e a prova de que ele a calcula
- **C** (2): Contrato abstrato: o Lean prova sob um majorante genérico; falta ligar ao avaliador concreto
- **S** (1): Prova textual e prova Lean fora de sincronia (o enunciado bate; a demonstração em TeX precisa ser atualizada)
- **N** (24): Sem Lean: nenhuma declaração localizada para este enunciado
- **T** (1): Corolário a transportar: existe o resultado-base em Lean, falta instanciá-lo nas definições deste artigo

## Lista dos itens que não batem

`pág.` é a página do PDF unificado; `linha` é a linha em `tex/partes/*.tex`; o detalhe de cada caso está em `../03_lacunas/LACUNAS_parte_*.md`.

| Nº | Tipo | Título | Pág. | Linha | Cat. | Lean mais próximo |
|---|---|---|---:|---:|:--:|---|
| I.6.3 | algoritmo | refinamento certificado | 16 | 434 | C | `Fase3.refineCell` |
| I.6.4 | teorema | correção, término e tamanho | 17 | 449 | C | `Fase3.refine_terminates` |
| III.2.3 | proposicao | densidade, interpolação e forma ReLU | 37 | 54 | H | `Artigo.assemblies_dense` |
| III.3.12 | teorema | comparação rigorosa dos formatos | 43 | 436 | P | `Artigo.coding_formats_decoders` |
| III.3.15 | lema | controle uniforme da primeira derivada | 44 | 578 | H | `Artigo.derivative_control` |
| III.3.16 | teorema | controle simultâneo de erro, folhas, altura e bits | 44 | 600 | H | `Artigo.joint_budget` |
| III.3.17 | corolario | altura suficiente para precisão prescrita | 46 | 715 | H | `Artigo.height_for_epsilon` |
| III.3.18 | teorema | entropia e codebook explícito | 47 | 794 | H | `Artigo.entropy_codebook` |
| III.3.25 | algoritmo | enumeração exata do catálogo | 51 | 1138 | A | `Artigo.finite_catalog_minimizer` |
| III.6.3 | algoritmo | rotulação exata de uma árvore fixa | 57 | 1675 | A | `Artigo.Setup.fixed_correctness` |
| III.7.4 | algoritmo | seletor exato por programação dinâmica | 58 | 1801 | A | `Artigo.Setup.variable_correctness` |
| III.9.1 | teorema | complexidade em número de estados | 60 | 1996 | P | `Artigo.Setup.state_complexity` |
| III.9.3 | teorema | cota grosseira de complexidade de bits | 61 | 2083 | P | `Artigo.Setup.bit_complexity` |
| III.11.2 | lema | expansão local uniforme | 68 | 2581 | H | `Artigo.local_asymptotic_error` |
| III.11.3 | teorema | envelope diádico universal e agudo | 68 | 2608 | H | `Artigo.general_dyadic_envelope` |
| III.12.1 | teorema | lei exata e intervalo de acumulação | 69 | 2705 | H | `Artigo.quadratic_dyadic_constant` |
| III.12.3 | corolario | fases sincronizadas | 71 | 2860 | S | `Artigo.synchronized_phases` |
| IV.3.1 | proposicao | aninhamento da agenda | 80 | 81 | N | — |
| IV.3.2 | teorema | redução exata às escalas diádicas | 80 | 133 | N | — |
| IV.3.3 | proposicao | falha exata de homogeneidade | 80 | 166 | N | — |
| IV.4.1 | lema | Jackson racional com altura explícita | 82 | 277 | N | — |
| IV.4.2 | teorema | direção direta com altura aritmética | 83 | 398 | N | — |
| IV.4.3 | corolario | imersões quantitativas uniformes sobre bolas | 84 | 453 | N | — |
| IV.4.5 | corolario | endpoint $C^2$ | 84 | 518 | T | `Dyadic.Lib.simultaneous_control` |
| IV.4.6 | proposicao | piso aritmético uniforme | 85 | 555 | N | — |
| IV.5.1 | definicao | biblioteca marcada completa | 87 | 756 | N | — |
| IV.5.2 | teorema | reversibilidade rasa exata | 88 | 793 | N | — |
| IV.5.3 | definicao | altura canônica de rede | 88 | 845 | N | — |
| IV.5.4 | proposicao | forma ancorada e comprimento estrutural | 88 | 863 | N | — |
| IV.5.5 | teorema | reversão aproximada quantizada | 89 | 922 | N | — |
| IV.5.6 | corolario | redes profundas medidas pela função realizada | 90 | 984 | N | — |
| IV.5.7 | teorema | imersão inversa sob crescimento de Lipschitz | 91 | 1087 | N | — |
| IV.5.8 | corolario | aplicação às agendas diretas | 92 | 1142 | N | — |
| IV.5.9 | teorema | agudeza por um pente de tendas | 92 | 1178 | N | — |
| IV.5.10 | lema | desigualdade inversa universal | 93 | 1287 | N | — |
| IV.5.12 | teorema | Jackson racional para o funcional de realização | 93 | 1314 | N | — |
| IV.5.13 | teorema | caracterização pelo funcional de realização | 94 | 1362 | N | — |
| IV.5.14 | teorema | reversibilidade estável por inclusão de redes | 95 | 1448 | N | — |
| V.6.1 | teorema | taxa garantida em árvores | 97 | 27 | N | — |
| V.6.2 | teorema | cota assintótica com nós livres | 98 | 57 | N | — |
| V.6.3 | teorema | estimativa direta | 98 | 109 | N | — |
| V.21.1 | lema | majorante local da função de Runge | 99 | 152 | N | — |

## Ordem sugerida de ataque

1. **Ponte de regularidade** (8 itens da Parte III + IV.4.5): uma única prova de extensão C² de [0,1] à reta destrava III.2.3, III.3.15–3.18, III.11.2, III.11.3, III.12.1 e IV.4.5.
2. **III.3.12**: formalizar a árvore em raiz única com N = 2^r folhas.
3. **Fecho do refinamento certificado** (I.6.3, I.6.4): ligar `refine_correct` ao `boundSecondDerivative`.
4. **Algoritmos** (III.3.25, III.6.3, III.7.4) e depois **complexidade** (III.9.1, III.9.3), que depende de um modelo de custo.
5. **Parte V** (V.21.1 é o mais curto) e **Parte IV** (20 resultados novos; antes, as definições de agenda, erro e Besov).
6. **III.12.3** é só texto: reescrever a demonstração.

## Conferidos que batem, com observação

- **I.4.3**: Conferido nesta rodada: `assembly_eq_relu` escreve `(a 0).line (a 0).left`, isto é, o valor da primeira peça em t₀; é a leitura do texto. A direção inversa (`relu_mem_Asm`) exige menos hipóteses que o texto (não pede nós distintos). Sugere-se mudar o status de `divergencia_documentada` para `correspondencia_inspecionada`.
- **III.12.2**: O Lean dispensa a hipótese C¹ (basta a igualdade com quadráticas nas células fechadas). O texto mantém C¹, que é mais forte: o enunciado do texto segue verdadeiro. Não é lacuna.

## Observações do volume (sem Lean autônomo, não entram na contagem de pendências)

III.3.5, III.3.8, III.3.10, III.4.6, III.8.3, III.9.2, III.12.4, IV.3.4, IV.4.4, IV.5.11.
