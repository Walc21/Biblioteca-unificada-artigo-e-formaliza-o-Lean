# Parte I — Biblioteca, endereçamento e refinamento

Os módulos executáveis ficam em `../../ambientes/`. Este diretório contém o índice da parte, sem mover os módulos e quebrar imports.

## I.2.1 — lema pareamento e cota

Original de 77 páginas: 2.1.

Fonte editável: [tex/partes/artigo_1.tex:40](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.cpair_bijective`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 93.
- [`Fase3.cdiag_eq_floor`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 103.
- [`Fase3.cpair_le`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 126.

## I.2.2 — lema 

Original de 77 páginas: 2.2.

Fonte editável: [tex/partes/artigo_1.tex:53](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.zEnum_bijective`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 148.
- [`Fase3.zInv_le`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 151.

## I.2.3 — lema contagem por altura

Original de 77 páginas: 2.3.

Fonte editável: [tex/partes/artigo_1.tex:67](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.3`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.card_QH_le`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 44.
- [`Fase3.card_QH_ge`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 118.

## I.2.4 — lema posto por altura

Original de 77 páginas: 2.4.

Fonte editável: [tex/partes/artigo_1.tex:85](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.4`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.Qenum_bijective`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 254.
- [`Fase3.QstarEnum_bijective`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 257.
- [`Fase3.rankQ_lt`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 268.
- [`Fase3.rankQstar_lt`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 282.

## I.2.5 — lema 

Original de 77 páginas: 2.5.

Fonte editável: [tex/partes/artigo_1.tex:97](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.5`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.calkinWilf_two_pow`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 333.

## I.3.1 — lema estrutura diádica

Original de 77 páginas: 3.1.

Fonte editável: [tex/partes/artigo_1.tex:125](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.cellOwn_partition`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 58.
- [`Fase3.cell_refine`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 62.
- [`Fase3.cell_length`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 76.
- [`Fase3.center_bijOn`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 134.
- [`Fase3.dyadicMid_dense`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 140.

## I.3.2 — lema 

Original de 77 páginas: 3.2.

Fonte editável: [tex/partes/artigo_1.tex:145](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.decode4_bijective`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 169.

## I.3.3 — definicao gerador e biblioteca

Original de 77 páginas: 3.3.

Fonte editável: [tex/partes/artigo_1.tex:162](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.3`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.gen`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 212.
- [`Fase3.library`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 215.

## I.3.4 — lema validade espacial exata

Original de 77 páginas: 3.4.

Fonte editável: [tex/partes/artigo_1.tex:175](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.4`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.preimageInterval_eq`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 237.

## I.3.5 — teorema unicidade do endereço

Original de 77 páginas: 3.5.

Fonte editável: [tex/partes/artigo_1.tex:185](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.5`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.gen_injective`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 320.

## I.3.6 — teorema dicionário de jatos racionais

Original de 77 páginas: 3.6.

Fonte editável: [tex/partes/artigo_1.tex:195](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.6`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.jet_bijective`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 292.
- [`Fase3.jet_dense`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 303.

## I.4.1 — definicao montagem contínua

Original de 77 páginas: 4.1.

Fonte editável: [tex/partes/artigo_1.tex:213](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.1`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Fase3.IsAssembly`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Assembly.lean) — linha 53.
- [`Dyadic.Lib.IsAssemblyRep`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Lib/Assembly.lean) — linha 19.
- [`Dyadic.Lib.Asm`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Lib/Assembly.lean) — linha 26.
- [`SemanticBridge.fase3_assembly_iff_consolidated`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 105.
- [`SemanticBridge.fase2_restriction_eq_consolidated`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 142.

## I.4.2 — teorema densidade das montagens

Original de 77 páginas: 4.2.

Fonte editável: [tex/partes/artigo_1.tex:226](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.assembly_dense`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Assembly.lean) — linha 386.

## I.4.3 — teorema equivalência montagem--ReLU racional

Original de 77 páginas: 4.3.

Fonte editável: [tex/partes/artigo_1.tex:253](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.3`.

Estado: **Divergência documentada**. O operador de extensao normalizado foi integrado a classe concreta da Fase 2. O enunciado TeX deste volume le g(t0) como o valor em t0 da primeira peca (t0 pode estar fora de K); essa leitura nao foi reverificada contra o enunciado Lean.

- [`Dyadic.Lib.assembly_eq_relu`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean) — linha 92.
- [`Dyadic.Lib.relu_mem_Asm`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean) — linha 183.

## I.4.4 — proposicao parâmetros e altura

Original de 77 páginas: 4.4.

Fonte editável: [tex/partes/artigo_1.tex:272](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.4`.

Estado: **Correspondência inspecionada**. 

- [`Dyadic.Lib.relu_parameters_height`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean) — linha 360.

## I.4.5 — proposicao pertencimento e aderência

Original de 77 páginas: 4.5.

Fonte editável: [tex/partes/artigo_1.tex:294](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.5`.

Estado: **Correspondência inspecionada**. 

- [`Dyadic.Lib.taylor_jet`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/Taylor.lean) — linha 55.

## I.5.1 — teorema cota aguda e limite

Original de 77 páginas: 5.1.

Fonte editável: [tex/partes/artigo_1.tex:320](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:5.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.errP_le`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 148.
- [`Fase3.tendsto_errP`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 269.
- [`Fase3.exists_assembly_rate`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 304.

## I.5.2 — corolario preservação da constante

Original de 77 páginas: 5.2.

Fonte editável: [tex/partes/artigo_1.tex:347](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:5.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.exists_assembly_seq_constant`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 319.

## I.6.1 — lema restos transcendentais com extremos racionais

Original de 77 páginas: 7.1.

Fonte editável: [tex/partes/artigo_1.tex:401](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.exp_sub_expPoly_bounds`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Transcendental.lean) — linha 61.
- [`Fase3.sin_cos_lagrange`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Transcendental.lean) — linha 225.

## I.6.2 — proposicao correção do majorante intervalar

Original de 77 páginas: 7.2.

Fonte editável: [tex/partes/artigo_1.tex:422](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.boundSecondDerivative_correct`](../../../lean4/ambientes/base_integrada/Unified/Fase3/IntervalArith.lean) — linha 619.
- [`Fase3.Mint_ge_supNorm`](../../../lean4/ambientes/base_integrada/Unified/Fase3/IntervalArith.lean) — linha 629.

## I.6.3 — algoritmo refinamento certificado

Original de 77 páginas: 7.3.

Fonte editável: [tex/partes/artigo_1.tex:434](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.3`.

Estado: **Formalizado e compilado**. Refinamento recursivo certificado sob hipoteses sobre os majorantes; composicao executavel com avaliacao intervalar e escolha racional ainda requer fechamento. [11/11/2026] Algoritmo `certRefine` com M(J) = M_int(J) de `boundSecondDerivative`; devolve `none` (aborta) exatamente quando alguma célula consultada falha. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Fase3.refineCell`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 29.
- [`Fase3.refineAll`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 35.
- [`Fase3.rStar`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 39.
- [`PendenciasParte1.certRefine`](../../../lean4/ambientes/base_integrada/PendenciasParte1/Refinamento.lean) — linha 55.
- [`PendenciasParte1.certified_refinement`](../../../lean4/ambientes/base_integrada/PendenciasParte1/Refinamento.lean) — linha 135.

## I.6.4 — teorema correção, término e tamanho

Original de 77 páginas: 7.4.

Fonte editável: [tex/partes/artigo_1.tex:449](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.4`.

Estado: **Formalizado e compilado**. Termino e correcao sob os contratos formais; nao equivale a certificar uma implementacao completa ligada ao avaliador intervalar. [11/11/2026] Em caso de sucesso: f = E é C² em [α,β], η_cert ≤ ε_I, profundidade ≤ r*, ≤ R₀2^{r*} folhas e ‖f−g‖ ≤ ε_I+ε_R (instancia `refine_terminates`/`refine_correct`); contrato M_int ≤ M* nas células certificadas. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Fase3.refine_terminates`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 222.
- [`Fase3.refine_correct`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 292.
- [`PendenciasParte1.certified_refinement`](../../../lean4/ambientes/base_integrada/PendenciasParte1/Refinamento.lean) — linha 135.

## I.6.5 — proposicao calibração exata para curvatura constante

Original de 77 páginas: 7.5.

Fonte editável: [tex/partes/artigo_1.tex:476](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.5`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.calibration`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Calibration.lean) — linha 94.

## I.6.6 — observacao diferença segunda e erro no centro

Original de 77 páginas: 7.6.

Fonte editável: [tex/partes/artigo_1.tex:502](../../../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.6`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.center_error_eq`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Observation.lean) — linha 16.
- [`Fase3.cube_example`](../../../lean4/ambientes/base_integrada/Unified/Fase3/Observation.lean) — linha 27.


## Cópias para leitura

`fontes_referenciados/` reúne cópias byte a byte dos módulos associados. Para compilar, use os ambientes completos em `../../ambientes/`, que preservam imports e dependências.
