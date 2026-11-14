# Correspondência do volume com Lean 4

As ligações abaixo são derivadas da matriz recebida, com caminhos locais conferidos. A compilação histórica não é uma nova validação semântica.

## Parte I

## I.2.1 — lema pareamento e cota

Original de 77 páginas: 2.1.

Fonte editável: [tex/partes/artigo_1.tex:40](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.cpair_bijective`](../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 93.
- [`Fase3.cdiag_eq_floor`](../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 103.
- [`Fase3.cpair_le`](../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 126.

## I.2.2 — lema

Original de 77 páginas: 2.2.

Fonte editável: [tex/partes/artigo_1.tex:53](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.zEnum_bijective`](../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 148.
- [`Fase3.zInv_le`](../lean4/ambientes/base_integrada/Unified/Fase3/Indexing.lean) — linha 151.

## I.2.3 — lema contagem por altura

Original de 77 páginas: 2.3.

Fonte editável: [tex/partes/artigo_1.tex:67](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.3`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.card_QH_le`](../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 44.
- [`Fase3.card_QH_ge`](../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 118.

## I.2.4 — lema posto por altura

Original de 77 páginas: 2.4.

Fonte editável: [tex/partes/artigo_1.tex:85](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.4`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.Qenum_bijective`](../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 254.
- [`Fase3.QstarEnum_bijective`](../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 257.
- [`Fase3.rankQ_lt`](../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 268.
- [`Fase3.rankQstar_lt`](../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 282.

## I.2.5 — lema

Original de 77 páginas: 2.5.

Fonte editável: [tex/partes/artigo_1.tex:97](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:2.5`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.calkinWilf_two_pow`](../lean4/ambientes/base_integrada/Unified/Fase3/Heights.lean) — linha 333.

## I.3.1 — lema estrutura diádica

Original de 77 páginas: 3.1.

Fonte editável: [tex/partes/artigo_1.tex:125](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.cellOwn_partition`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 58.
- [`Fase3.cell_refine`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 62.
- [`Fase3.cell_length`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 76.
- [`Fase3.center_bijOn`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 134.
- [`Fase3.dyadicMid_dense`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 140.

## I.3.2 — lema

Original de 77 páginas: 3.2.

Fonte editável: [tex/partes/artigo_1.tex:145](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.decode4_bijective`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 169.

## I.3.3 — definição gerador e biblioteca

Original de 77 páginas: 3.3.

Fonte editável: [tex/partes/artigo_1.tex:162](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.3`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.gen`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 212.
- [`Fase3.library`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 215.

## I.3.4 — lema validade espacial exata

Original de 77 páginas: 3.4.

Fonte editável: [tex/partes/artigo_1.tex:175](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.4`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.preimageInterval_eq`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 237.

## I.3.5 — teorema unicidade do endereço

Original de 77 páginas: 3.5.

Fonte editável: [tex/partes/artigo_1.tex:185](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.5`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.gen_injective`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 320.

## I.3.6 — teorema dicionário de jatos racionais

Original de 77 páginas: 3.6.

Fonte editável: [tex/partes/artigo_1.tex:195](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:3.6`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.jet_bijective`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 292.
- [`Fase3.jet_dense`](../lean4/ambientes/base_integrada/Unified/Fase3/Cells.lean) — linha 303.

## I.4.1 — definição montagem contínua

Original de 77 páginas: 4.1.

Fonte editável: [tex/partes/artigo_1.tex:213](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.1`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Fase3.IsAssembly`](../lean4/ambientes/base_integrada/Unified/Fase3/Assembly.lean) — linha 53.
- [`Dyadic.Lib.IsAssemblyRep`](../lean4/ambientes/base_integrada/Unified/Consolidado/Lib/Assembly.lean) — linha 19.
- [`Dyadic.Lib.Asm`](../lean4/ambientes/base_integrada/Unified/Consolidado/Lib/Assembly.lean) — linha 26.
- [`SemanticBridge.fase3_assembly_iff_consolidated`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 105.
- [`SemanticBridge.fase2_restriction_eq_consolidated`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 142.

## I.4.2 — teorema densidade das montagens

Original de 77 páginas: 4.2.

Fonte editável: [tex/partes/artigo_1.tex:226](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.assembly_dense`](../lean4/ambientes/base_integrada/Unified/Fase3/Assembly.lean) — linha 386.

## I.4.3 — teorema equivalência montagem--ReLU racional

Original de 77 páginas: 4.3.

Fonte editável: [tex/partes/artigo_1.tex:253](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.3`.

Estado: **Divergência documentada**. O operador de extensão normalizado foi integrado à classe concreta da Fase 2. O enunciado TeX deste volume le g(t0) como o valor em t0 da primeira peça (t0 pode estar fora de K); essa leitura não foi reverificada contra o enunciado Lean.

- [`Dyadic.Lib.assembly_eq_relu`](../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean) — linha 92.
- [`Dyadic.Lib.relu_mem_Asm`](../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean) — linha 183.

## I.4.4 — proposição parâmetros e altura

Original de 77 páginas: 4.4.

Fonte editável: [tex/partes/artigo_1.tex:272](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.4`.

Estado: **Correspondência inspecionada**. 

- [`Dyadic.Lib.relu_parameters_height`](../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean) — linha 360.

## I.4.5 — proposição pertencimento e aderência

Original de 77 páginas: 4.5.

Fonte editável: [tex/partes/artigo_1.tex:294](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:4.5`.

Estado: **Correspondência inspecionada**. 

- [`Dyadic.Lib.taylor_jet`](../lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/Taylor.lean) — linha 55.

## I.5.1 — teorema cota aguda e limite

Original de 77 páginas: 5.1.

Fonte editável: [tex/partes/artigo_1.tex:320](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:5.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.errP_le`](../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 148.
- [`Fase3.tendsto_errP`](../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 269.
- [`Fase3.exists_assembly_rate`](../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 304.

## I.5.2 — corolário preservação da constante

Original de 77 páginas: 5.2.

Fonte editável: [tex/partes/artigo_1.tex:347](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:5.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.exists_assembly_seq_constant`](../lean4/ambientes/base_integrada/Unified/Fase3/Rates.lean) — linha 319.

## I.6.1 — lema restos transcendentais com extremos racionais

Original de 77 páginas: 7.1.

Fonte editável: [tex/partes/artigo_1.tex:401](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.1`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.exp_sub_expPoly_bounds`](../lean4/ambientes/base_integrada/Unified/Fase3/Transcendental.lean) — linha 61.
- [`Fase3.sin_cos_lagrange`](../lean4/ambientes/base_integrada/Unified/Fase3/Transcendental.lean) — linha 225.

## I.6.2 — proposição correção do majorante intervalar

Original de 77 páginas: 7.2.

Fonte editável: [tex/partes/artigo_1.tex:422](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.2`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.boundSecondDerivative_correct`](../lean4/ambientes/base_integrada/Unified/Fase3/IntervalArith.lean) — linha 619.
- [`Fase3.Mint_ge_supNorm`](../lean4/ambientes/base_integrada/Unified/Fase3/IntervalArith.lean) — linha 629.

## I.6.3 — algoritmo refinamento certificado

Original de 77 páginas: 7.3.

Fonte editável: [tex/partes/artigo_1.tex:434](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.3`.

Estado: **Formalizado e compilado**. Refinamento recursivo certificado sob hipóteses sobre os majorantes; composição executável com avaliação intervalar e escolha racional ainda requer fechamento. [11/11/2026] Algoritmo `certRefine` com M(J) = M_int(J) de `boundSecondDerivative`; devolve `none` (aborta) exatamente quando alguma célula consultada falha. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Fase3.refineCell`](../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 29.
- [`Fase3.refineAll`](../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 35.
- [`Fase3.rStar`](../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 39.
- [`PendenciasParte1.certRefine`](../lean4/ambientes/base_integrada/PendenciasParte1/Refinamento.lean) — linha 55.
- [`PendenciasParte1.certified_refinement`](../lean4/ambientes/base_integrada/PendenciasParte1/Refinamento.lean) — linha 135.

## I.6.4 — teorema correção, término e tamanho

Original de 77 páginas: 7.4.

Fonte editável: [tex/partes/artigo_1.tex:449](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.4`.

Estado: **Formalizado e compilado**. Término e correção sob os contratos formais; não equivale a certificar uma implementação completa ligada ao avaliador intervalar. [11/11/2026] Em caso de sucesso: f = E é C² em [α,β], η_cert ≤ ε_I, profundidade ≤ r*, ≤ R₀2^{r*} folhas e ‖f−g‖ ≤ ε_I+ε_R (instancia `refine_terminates`/`refine_correct`); contrato M_int ≤ M* nas células certificadas. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Fase3.refine_terminates`](../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 222.
- [`Fase3.refine_correct`](../lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean) — linha 292.
- [`PendenciasParte1.certified_refinement`](../lean4/ambientes/base_integrada/PendenciasParte1/Refinamento.lean) — linha 135.

## I.6.5 — proposição calibração exata para curvatura constante

Original de 77 páginas: 7.5.

Fonte editável: [tex/partes/artigo_1.tex:476](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.5`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.calibration`](../lean4/ambientes/base_integrada/Unified/Fase3/Calibration.lean) — linha 94.

## I.6.6 — observação diferença segunda e erro no centro

Original de 77 páginas: 7.6.

Fonte editável: [tex/partes/artigo_1.tex:502](../tex/partes/artigo_1.tex); rótulo `map:artigo_1:6.6`.

Estado: **Correspondência inspecionada**. 

- [`Fase3.center_error_eq`](../lean4/ambientes/base_integrada/Unified/Fase3/Observation.lean) — linha 16.
- [`Fase3.cube_example`](../lean4/ambientes/base_integrada/Unified/Fase3/Observation.lean) — linha 27.


## Parte II

## II.2.1 — definição racional reduzido e altura

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:89](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.ht`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 39.
- [`Montagens.ht_props`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 44.

## II.2.2 — definição célula e funções de seus extremos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:106](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.Cell`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 51.
- [`Montagens.LQ`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 54.
- [`Montagens.RQ`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 56.
- [`Montagens.XQ`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 58.
- [`Montagens.J`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 68.
- [`Montagens.O`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 70.
- [`Montagens.P`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 72.
- [`Montagens.Dy`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 75.

## II.2.3 — lema geometria elementar

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:129](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.geometry`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 81.

## II.2.4 — definição átomo e suas projeções

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:149](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.4`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.Atom`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 131.
- [`Montagens.Atom.height`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 159.
- [`SemanticBridge.normalizationAtomEquiv`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationAtoms.lean) — linha 22.
- [`SemanticBridge.normalization_atom_height`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationAtoms.lean) — linha 40.

## II.2.5 — lema formas da reta

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:170](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.5`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.line_forms`](../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 168.
- [`SemanticBridge.normalization_atom_line`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationAtoms.lean) — linha 37.

## II.3.1 — definição campos dos contratos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:191](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.1`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.Sep`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 25.
- [`Montagens.Cover`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 29.
- [`Montagens.MatchK`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 33.
- [`Montagens.Agree`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 41.
- [`Montagens.LocalRep`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 45.
- [`Montagens.StrongRep`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 49.
- [`SemanticBridge.normalization_local_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 17.
- [`SemanticBridge.normalization_strong_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 29.

## II.3.2 — definição atividade e filtro

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:228](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.Active`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 69.
- [`Montagens.NormK`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 72.

## II.3.3 — lema critério exato de atividade

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:241](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.active_iff`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 78.

## II.3.4 — lema intervalos separados

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:262](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.separated_of_disjoint`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 92.
- [`Montagens.separated_inter`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 103.

## II.3.5 — teorema normalização

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:275](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.5`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.normalization`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 176.
- [`Montagens.normalizationG`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 198.
- [`SemanticBridge.normalizeAtoms_strong`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 79.
- [`SemanticBridge.normalizeAtoms_subset`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 64.
- [`SemanticBridge.normalizeAtoms_card_le`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 70.
- [`SemanticBridge.normalizeAtoms_idem`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 74.

## II.3.6 — corolário equivalência local e consolidada

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:314](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.6`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.Aloc_eq_Astr`](../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 219.
- [`SemanticBridge.local_asm_eq_strong`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 87.

## II.4.1 — definição pareamento e descompactação

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:329](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.T`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 23.
- [`Montagens.pair`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 28.
- [`Montagens.unpair`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 45.
- [`Montagens.pack`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 48.
- [`Montagens.unpack`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 53.

## II.4.2 — lema inversas do pareamento

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:354](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.2`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.pair_props`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 92.
- [`SemanticBridge.normalization_pair`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 22.
- [`SemanticBridge.normalization_unpack2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 37.
- [`SemanticBridge.normalization_unpack3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 34.

## II.4.3 — definição enumeração dos inteiros

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:382](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.3`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.Zenc`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 136.
- [`Montagens.Zinv`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 139.
- [`Montagens.Zenc_Zinv`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 153.
- [`Montagens.Zinv_Zenc`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 160.
- [`SemanticBridge.normalization_Z2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 50.
- [`SemanticBridge.normalization_Z3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 41.

## II.4.4 — definição ordens e postos dos racionais

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:393](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.QH`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 169.
- [`Montagens.prec`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 222.
- [`Montagens.Pred`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 228.
- [`Montagens.rank`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 231.
- [`Montagens.rankStar`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 238.

## II.4.5 — lema postos e enumerações inversas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:430](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.5`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.prec_coincide`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 291.
- [`Montagens.rank_bijective`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 372.
- [`Montagens.rankStar_bijective`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 376.
- [`SemanticBridge.normalization_rank2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 82.
- [`SemanticBridge.normalization_rank3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 54.
- [`SemanticBridge.normalization_Q2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 101.
- [`SemanticBridge.normalization_Q3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 69.
- [`SemanticBridge.normalization_Qstar2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 107.
- [`SemanticBridge.normalization_Qstar3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 75.

## II.4.6 — definição codificadores concretos de átomos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:468](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.6`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.enc`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 401.
- [`Montagens.dec`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 406.
- [`Montagens.tau`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 420.

## II.4.7 — lema contrato completo de endereçamento

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:491](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.7`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.codec`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 430.
- [`Montagens.tau_props`](../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 449.
- [`SemanticBridge.normalization_ofFase2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 129.
- [`SemanticBridge.normalization_ofFase3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 115.
- [`SemanticBridge.normalization_C2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 40.
- [`SemanticBridge.normalization_C3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 35.
- [`SemanticBridge.normalization_lam2`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 59.
- [`SemanticBridge.normalization_lam3`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 53.

## II.5.1 — definição testemunha por células endereçadas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:517](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.CellRep`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 26.
- [`Montagens.CellRepG`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 33.

## II.5.2 — definição continuidade no domínio e restrição

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:537](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.2`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.ContOn`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 42.
- [`Montagens.Res`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 55.
- [`Montagens.ResImage`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 59.
- [`SemanticBridge.normalization_contOn_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 66.

## II.5.3 — definição as três classes tipadas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:558](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.3`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.B2`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 65.
- [`Montagens.B3`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 69.
- [`Montagens.Bcon`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 73.
- [`SemanticBridge.normalization_B2_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 109.
- [`SemanticBridge.normalization_B3_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 83.
- [`SemanticBridge.normalization_Bcon_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 93.

## II.5.4 — lema conversões explícitas das testemunhas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:575](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.cellsToAtoms_spec`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 176.
- [`Montagens.cellsToAtoms_specG`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 189.
- [`Montagens.atomsToCells_spec`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 202.
- [`Montagens.atomsToCells_specG`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 216.

## II.5.5 — definição extensão contínua por projeção

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:629](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.5`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.projK`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 232.
- [`Montagens.E0`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 239.
- [`Montagens.Res_E0`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 260.

## II.5.6 — teorema equivalência extensional tipada

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:644](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.6`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.bridge`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 318.
- [`Montagens.B3_eq_Bcon`](../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 309.
- [`SemanticBridge.fase3_assembly_iff_consolidated`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 105.
- [`SemanticBridge.fase2_restriction_eq_consolidated`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 142.

## II.6.1 — definição orçamento da testemunha

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:676](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.1`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.Budget`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 23.
- [`Montagens.AlocNH`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 27.
- [`Montagens.AstrNH`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 31.
- [`SemanticBridge.normalization_budget_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 37.

## II.6.2 — teorema igualdade sob os mesmos recursos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:693](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.2`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.AlocNH_eq_AstrNH`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 37.
- [`SemanticBridge.local_budgeted_eq_strong`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 103.
- [`SemanticBridge.normalization_typed_budget_iff`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 17.

## II.6.3 — definição distância uniforme e ínfimo

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:705](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.3`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.dK`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 46.
- [`Montagens.Err`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 65.
- [`Montagens.dK_isMax`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 49.
- [`Montagens.Err_empty`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 74.
- [`SemanticBridge.normalization_distance`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 35.

## II.6.4 — corolário igualdade dos erros e de suas condições de altura

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:731](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.4`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.errors_eq`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 78.
- [`Montagens.heights_eq`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 82.
- [`SemanticBridge.normalization_Econ_eq_jointError`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 54.
- [`SemanticBridge.normalization_Eloc_eq_jointError`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 86.
- [`SemanticBridge.local_height_conditions_eq`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 125.

## II.6.5 — proposição testemunhas já ativas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:749](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.5`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.norm_fixed_of_active`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 91.
- [`Montagens.norm_fixed_of_subset`](../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 95.

## II.7.1 — definição ordem auxiliar total dos átomos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:769](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.zeta`](../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 25.
- [`Montagens.sortAtoms`](../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 40.

## II.7.2 — lema propriedades da lista ordenada

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:800](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.sortAtoms_props`](../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 55.

## II.7.3 — definição tipo dos dados de cadeia

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:820](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain`](../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 110.

## II.7.4 — teorema construção determinada da cadeia

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:844](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.chainOf`](../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 344.
- [`Montagens.chainOf_nodes_dyadic`](../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 360.

## II.8.1 — definição parâmetros e funções parciais

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:890](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain.Fpart`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 52.
- [`Montagens.NormChain.Rext`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 59.

## II.8.2 — lema expansão da recursão

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:920](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain.Rext_sum`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 88.
- [`Montagens.NormChain.Rext_anchor`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 103.
- [`Montagens.NormChain.Rext_of_M_eq_one`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 111.

## II.8.3 — lema identidade de duas retas incidentes

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:948](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain.incident`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 120.

## II.8.4 — teorema correção da extensão

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:965](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.4`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.NormChain.extension`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 211.
- [`SemanticBridge.fase2_relu_extension_agrees`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 27.
- [`SemanticBridge.fase2_relu_extension_is_consolidated`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 34.

## II.8.5 — lema unicidade de uma reta a partir de dois pontos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:1013](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.5`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificação dos tipos de átomos, endereços, classes e erros com a v2 está provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.affine_eq_of_two_points`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 283.

## II.8.6 — teorema independência da testemunha

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:1025](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.6`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.Rext_unique`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 331.
- [`SemanticBridge.fase2_relu_extension_eq`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 47.

## II.8.7 — definição operador de extensão das montagens

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:1060](../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.7`.

Estado: **Integrado à base**. Identificação com os tipos concretos da v2 provada nos módulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipóteses, domínio, função e orçamentos preservados.

- [`Montagens.extOp`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 359.
- [`Montagens.Res_extOp`](../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 370.
- [`SemanticBridge.fase2ReLUExtension`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 23.
- [`SemanticBridge.fase2_relu_extension_agrees`](../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 27.


## Parte III

## III.2.1 — lema indexação elementar

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/artigo_2.tex:26](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:2.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.cantorPair_bijective`](../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 77.
- [`Artigo.cantorPair_le`](../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 81.
- [`Artigo.Zenum_bijective`](../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 111.
- [`Artigo.Zinv_le`](../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 118.
- [`Artigo.card_QH_le`](../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 191.
- [`Artigo.card_QH_ge`](../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 320.
- [`Artigo.rank_lt_three_sq`](../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 536.

## III.2.2 — definição átomos e montagens

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/artigo_2.tex:43](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:2.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Atom`](../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 17.
- [`Artigo.Atom.interface_injective`](../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 115.
- [`Artigo.Atom.addr_injective`](../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 178.
- [`Artigo.LTree.WF`](../lean4/ambientes/artigo_2/RequestProject/Trees.lean) — linha 98.

## III.2.3 — proposição densidade, interpolação e forma ReLU

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/artigo_2.tex:54](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:2.3`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] Cota de interpolação provada com `ContDiffOn ℝ 2 f (Icc a b)` e `derivWithin`, via extensão C² portada da Fase 3 (`Pendencias/Extensao.lean`). Densidade e forma ReLU já batiam. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.assemblies_dense`](../lean4/ambientes/artigo_2/RequestProject/Uniform.lean) — linha 231.
- [`Artigo.interp_remainder_C2`](../lean4/ambientes/artigo_2/RequestProject/Interp.lean) — linha 126.
- [`Artigo.LTree.eval_relu_form`](../lean4/ambientes/artigo_2/RequestProject/Trees.lean) — linha 392.
- [`Pendencias.interp_remainder_C2On`](../lean4/ambientes/artigo_2/Pendencias/Interpolacao.lean) — linha 20.

## III.3.1 — teorema cota polinomial do endereço

Original de 77 páginas: 8.1.

Fonte editável: [tex/partes/artigo_2.tex:97](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.index_bound`](../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 48.

## III.3.2 — lema cardinalidade das cascas de altura

Original de 77 páginas: 8.2.

Fonte editável: [tex/partes/artigo_2.tex:123](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.card_LH_le`](../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 239.
- [`Artigo.card_LH_ge`](../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 264.
- [`Artigo.card_LH_theta`](../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 272.

## III.3.3 — proposição ordem exata do pior endereço aritmético

Original de 77 páginas: 8.3.

Fonte editável: [tex/partes/artigo_2.tex:175](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.3`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.MGamma_theta`](../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 137.
- [`Artigo.MGamma_bits`](../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 148.

## III.3.4 — teorema cota minimax relativa ao calibre

Original de 77 páginas: 8.4.

Fonte editável: [tex/partes/artigo_2.tex:216](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.address_lower`](../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 203.

## III.3.5 — observação

Original de 77 páginas: 8.5.

Fonte editável: [tex/partes/artigo_2.tex:245](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.5`.

Estado: **Observação editorial**. Observação ou diagnostico do texto; não é um teorema Lean autônomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.3.6 — definição enumeração por altura da biblioteca

Original de 77 páginas: 8.6.

Fonte editável: [tex/partes/artigo_2.tex:252](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.6`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.nSharp`](../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 245.
- [`Artigo.GammaSharp`](../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 279.

## III.3.7 — teorema endereço minimax exato para a exaustão

Original de 77 páginas: 8.7.

Fonte editável: [tex/partes/artigo_2.tex:257](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.7`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.sharp_optimal`](../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 293.

## III.3.8 — observação qual endereço usar

Original de 77 páginas: 8.8.

Fonte editável: [tex/partes/artigo_2.tex:279](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.8`.

Estado: **Observação editorial**. Observação ou diagnostico do texto; não é um teorema Lean autônomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.3.9 — teorema serialização condicionada de montagens

Original de 77 páginas: 8.9.

Fonte editável: [tex/partes/artigo_2.tex:306](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.9`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.assembly_serialization`](../lean4/ambientes/artigo_2/RequestProject/Serialization.lean) — linha 184.
- [`Artigo.assembly_serialization_Gamma`](../lean4/ambientes/artigo_2/RequestProject/Serialization.lean) — linha 207.

## III.3.10 — observação

Original de 77 páginas: 8.10.

Fonte editável: [tex/partes/artigo_2.tex:341](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.10`.

Estado: **Observação editorial**. Observação ou diagnostico do texto; não é um teorema Lean autônomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.3.11 — lema cálculo elementar de alturas

Original de 77 páginas: 8.11.

Fonte editável: [tex/partes/artigo_2.tex:379](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.11`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.assembly_height_arith`](../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 160.

## III.3.12 — teorema comparação rigorosa dos formatos

Original de 77 páginas: 8.12.

Fonte editável: [tex/partes/artigo_2.tex:436](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.12`.

Estado: **Formalizado e compilado**. coding_gap_family prova uma cadeia para todo N par. O enunciado deste volume usa N=2^r e raiz J(H-1-r,0); a árvore em raiz única para N=2^r continua não formalizada em Lean (H=N=6 produz suporte [0,3/16], que não é uma célula diádica única). [11/11/2026] Montagem cheia `famTree` em J_{H-1-r,0} (WF, folhas J_{H-1,j}, altura H), N = 2^r; caso geral com N′ = 2^{⌊log₂N⌋}: NH ≤ 4 L_rat; inclui decodificadores e ordens. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.coding_formats_decoders`](../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 270.
- [`Artigo.coding_format_orders`](../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 421.
- [`Artigo.coding_gap_family`](../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 526.
- [`Pendencias.coding_formats_comparison`](../lean4/ambientes/artigo_2/Pendencias/Formatos.lean) — linha 71.

## III.3.13 — definição erro conjunto número--altura

Original de 77 páginas: 8.13.

Fonte editável: [tex/partes/artigo_2.tex:514](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.13`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.jointErr`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 30.
- [`Artigo.heightFor`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 38.

## III.3.14 — proposição monotonicidade dos dois orçamentos

Original de 77 páginas: 8.14.

Fonte editável: [tex/partes/artigo_2.tex:541](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.14`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.jointErr_succ_N_le`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 55.
- [`Artigo.jointErr_succ_H_le`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 59.
- [`Artigo.jointErr_tendsto`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 72.

## III.3.15 — lema controle uniforme da primeira derivada

Original de 77 páginas: 8.15.

Fonte editável: [tex/partes/artigo_2.tex:578](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.15`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; |f′| ≤ 4R+M/2 com f′ unilateral. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.derivative_control`](../lean4/ambientes/artigo_2/RequestProject/Interp.lean) — linha 231.
- [`Pendencias.derivative_control_Icc`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 129.
- [`Pendencias.FRM_subset_FRMIcc`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 56.
- [`Pendencias.extF_mem_FRM`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 59.

## III.3.16 — teorema controle simultâneo de erro, folhas, altura e bits

Original de 77 páginas: 8.16.

Fonte editável: [tex/partes/artigo_2.tex:600](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.16`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; mesma árvore determinística `uniformTree (jvals f r)` (só amostra f em [0,1]) e consequência para todo N ≥ 2. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.joint_budget`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 424.
- [`Artigo.joint_all_N`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 509.
- [`Pendencias.joint_budget_Icc`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 137.
- [`Pendencias.joint_all_N_Icc`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 153.

## III.3.17 — corolário altura suficiente para precisão prescrita

Original de 77 páginas: 8.17.

Fonte editável: [tex/partes/artigo_2.tex:715](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.17`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; n_ε, H_ε inalterados; `jointErr`, `heightFor` e `supDist` só dependem de f em [0,1]. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.height_for_epsilon`](../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 663.
- [`Pendencias.height_for_epsilon_Icc`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 159.

## III.3.18 — teorema entropia e codebook explícito

Original de 77 páginas: 8.18.

Fonte editável: [tex/partes/artigo_2.tex:794](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.18`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; coberturas de FRMIcc e FRM coincidem (`isCover_iff`), logo `entropyH ε (FRMIcc R M) = entropyH ε (FRM R M)`; codebook transportado. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.entropy_codebook`](../lean4/ambientes/artigo_2/RequestProject/Entropy.lean) — linha 46.
- [`Pendencias.entropy_codebook_Icc`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 178.

## III.3.19 — definição recursos de um codec

Original de 77 páginas: 8.19.

Fonte editável: [tex/partes/artigo_2.tex:905](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.19`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.EpsCodec`](../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 21.
- [`Artigo.Ldec`](../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 35.
- [`Artigo.Lglobal`](../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 39.
- [`Artigo.Lfolhas`](../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 43.

## III.3.20 — proposição limite informacional para representação decodificável

Original de 77 páginas: 8.20.

Fonte editável: [tex/partes/artigo_2.tex:949](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.20`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.description_lower`](../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 118.
- [`Artigo.complexity_chain`](../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 180.

## III.3.21 — proposição

Original de 77 páginas: 8.21.

Fonte editável: [tex/partes/artigo_2.tex:1011](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.21`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.no_minimizer`](../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 22.

## III.3.22 — definição catálogo truncado

Original de 77 páginas: 8.22.

Fonte editável: [tex/partes/artigo_2.tex:1040](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.22`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.RepCat`](../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 92.
- [`Artigo.SigmaCat`](../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 107.

## III.3.23 — teorema finitude, existência e desempate canônico

Original de 77 páginas: 8.23.

Fonte editável: [tex/partes/artigo_2.tex:1071](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.23`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.finite_catalog_minimizer`](../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 329.

## III.3.24 — proposição consistência sob truncagem

Original de 77 páginas: 8.24.

Fonte editável: [tex/partes/artigo_2.tex:1113](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.24`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.catalog_consistency`](../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 360.

## III.3.25 — algoritmo enumeração exata do catálogo

Original de 77 páginas: 8.25.

Fonte editável: [tex/partes/artigo_2.tex:1138](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.25`.

Estado: **Formalizado e compilado**. A recorrência ou existência matemática tem prova; falta implementar e certificar a execução e a reconstrução com comparação exata. [11/11/2026] Programa computável `gen`/`select`/`enumSelect`; = `RepCat` e devolve `canon` quando J é avaliado exatamente em ℚ. Testado com `#eval` (|𝓛₂| = 252; 42 e 102 representações para D = 0, 1, H = 2). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.finite_catalog_minimizer`](../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 329.
- [`Pendencias.gen_eq_RepCat`](../lean4/ambientes/artigo_2/Pendencias/Enumeracao.lean) — linha 56.
- [`Pendencias.enumSelect_eq_canon`](../lean4/ambientes/artigo_2/Pendencias/Enumeracao.lean) — linha 136.

## III.4.1 — definição pares de fronteira admissíveis

Original de 77 páginas: 9.1.

Fonte editável: [tex/partes/artigo_2.tex:1241](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.IsAdmPair`](../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 19.
- [`Artigo.PH`](../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 27.

## III.4.2 — proposição dicionário exato de fronteiras

Original de 77 páginas: 9.2.

Fonte editável: [tex/partes/artigo_2.tex:1254](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.endpoint_dictionary`](../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 63.

## III.4.3 — definição alfabeto de fronteira

Original de 77 páginas: 9.3.

Fonte editável: [tex/partes/artigo_2.tex:1296](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.3`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Valphabet`](../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 102.

## III.4.4 — lema finitude e suficiência

Original de 77 páginas: 9.4.

Fonte editável: [tex/partes/artigo_2.tex:1308](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.value_alphabet`](../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 122.

## III.4.5 — proposição células vazias e refinamento uniforme máximo

Original de 77 páginas: 9.5.

Fonte editável: [tex/partes/artigo_2.tex:1344](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.5`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.translation_obstruction`](../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 230.

## III.4.6 — observação assimetria espacial do catálogo

Original de 77 páginas: 9.6.

Fonte editável: [tex/partes/artigo_2.tex:1395](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.6`.

Estado: **Observação editorial**. Observação ou diagnostico do texto; não é um teorema Lean autônomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.5.1 — lema decodificação e aditividade

Original de 77 páginas: 10.1.

Fonte editável: [tex/partes/artigo_2.tex:1481](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:5.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.recursive_stream`](../lean4/ambientes/artigo_2/RequestProject/Functional.lean) — linha 57.

## III.5.2 — lema compatibilidade do desempate com a colagem

Original de 77 páginas: 10.2.

Fonte editável: [tex/partes/artigo_2.tex:1552](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:5.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.tie_concatenation`](../lean4/ambientes/artigo_2/RequestProject/Functional.lean) — linha 178.

## III.6.1 — definição recorrência para árvore fixa

Original de 77 páginas: 11.1.

Fonte editável: [tex/partes/artigo_2.tex:1592](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:6.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.Cfix`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 114.

## III.6.2 — teorema correção para árvore fixa

Original de 77 páginas: 11.2.

Fonte editável: [tex/partes/artigo_2.tex:1625](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:6.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.fixed_correctness`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 164.
- [`Artigo.Setup.fixed_global`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 189.

## III.6.3 — algoritmo rotulação exata de uma árvore fixa

Original de 77 páginas: 11.3.

Fonte editável: [tex/partes/artigo_2.tex:1675](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:6.3`.

Estado: **Formalizado e compilado**. A recorrência ou existência matemática tem prova; falta implementar e certificar a execução e a reconstrução com comparação exata. [11/11/2026] Tabela em pós-ordem com o κ-mínimo por estado (`fixTable`, colagem por w), custo = `Cfix`, raiz = rotulação κ-mínima de `fixed_global` (via Lema 5.2 `tie_concatenation`). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.Setup.fixed_correctness`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 164.
- [`Artigo.Setup.fixed_global`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 189.
- [`Pendencias.DPprog.fixTable_cost`](../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 190.
- [`Pendencias.DPprog.fixRoot_spec`](../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 244.

## III.7.1 — definição recorrência de Bellman com árvore variável

Original de 77 páginas: 12.1.

Fonte editável: [tex/partes/artigo_2.tex:1706](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.Cvar`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 24.

## III.7.2 — teorema exatidão, existência e determinismo

Original de 77 páginas: 12.2.

Fonte editável: [tex/partes/artigo_2.tex:1732](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.variable_correctness`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 43.
- [`Artigo.Setup.variable_global`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 67.

## III.7.3 — corolário compatibilidade com a enumeração de formas

Original de 77 páginas: 12.3.

Fonte editável: [tex/partes/artigo_2.tex:1780](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.3`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.shape_enumeration`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 235.

## III.7.4 — algoritmo seletor exato por programação dinâmica

Original de 77 páginas: 12.4.

Fonte editável: [tex/partes/artigo_2.tex:1801](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.4`.

Estado: **Formalizado e compilado**. A recorrência ou existência matemática tem prova; falta implementar e certificar a execução e a reconstrução com comparação exata. [11/11/2026] Tabela `varTable` (candidato folha + colagens, troca só se κ diminui), custo = `Cvar`, raiz = ótimo `Cstar` e representação κ-mínima de `variable_global`. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.Setup.variable_correctness`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 43.
- [`Artigo.Setup.variable_global`](../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 67.
- [`Pendencias.DPprog.varTable_cost`](../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 316.
- [`Pendencias.DPprog.varRoot_spec`](../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 339.

## III.8.1 — teorema correção sob orçamento de folhas

Original de 77 páginas: 13.1.

Fonte editável: [tex/partes/artigo_2.tex:1835](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.leaf_budget`](../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 181.
- [`Artigo.Setup.leaf_budget_atMost`](../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 208.

## III.8.2 — teorema cálculo exato do melhor erro truncado

Original de 77 páginas: 13.2.

Fonte editável: [tex/partes/artigo_2.tex:1895](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.bottleneck_correctness`](../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 327.
- [`Artigo.Setup.bottleneck`](../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 361.

## III.8.3 — observação interação entre profundidade e translação

Original de 77 páginas: 13.3.

Fonte editável: [tex/partes/artigo_2.tex:1929](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.3`.

Estado: **Observação editorial**. Observação ou diagnostico do texto; não é um teorema Lean autônomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.8.4 — corolário convergência para funções contínuas

Original de 77 páginas: 13.4.

Fonte editável: [tex/partes/artigo_2.tex:1944](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.uniform_convergence`](../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 387.

## III.9.1 — teorema complexidade em número de estados

Original de 77 páginas: 14.1.

Fonte editável: [tex/partes/artigo_2.tex:1996](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.1`.

Estado: **Formalizado e compilado**. Prova cardinalidades das tabelas e transições; não certifica tempo e memória de um programa com execução ligada a essas cardinalidades. [13/11/2026] III.9.1 formalizado com modelo de custo explícito: monad de contagem Tm, memória densa Mem com domínio explícito e motor genérico de preenchimento por níveis (runFrom_spec). Implementação densa da recorrência Cvar (denseRun: tabela (r,j,u,v) -> custo+apontador, níveis D..0, cada candidato w custa 2 leituras+1 soma+1 comparação) e da recorrência com orçamento Cb (denseRunB: chaves (r,j,u,v,n), pares (n_L,w)). Provado: (a) a tabela guarda exatamente Cvar/Cb (specE_cost, specEB_cost); (b) memória exatamente S_D M^2 (resp. S_D N M^2) entradas; (c) operações <= 8 S_D M^3 (resp. <= 7 S_D N^2 M^3) com custos de folha pre-computados; (d) apontadores reconstroem uma representação ótima em Rset/RsetN (rebuild_spec, rebuildB_spec); (e) custo local calculado sobre P observações (leafInit, 4P+3 operações, valor exatamente Phi): inicialização acrescenta 4 S_D P M^2 (variável) e S_D M^2 (4P+3) (orçamento). Compilado e auditado (propext, Classical.choice, Quot.sound). Ressalvas: (1) a comparação na tabela densa e feita sobre o custo; o desempate pela chave completa kappa (fluxo shortlex) não está no programa denso — o TeX conta comparações de chave como unitárias, de modo que a contagem coincide, e o seletor kappa-canônico continua sendo o de III.7.4 (varRoot_spec); a tabela densa devolve UMA representação ótima, não necessariamente a kappa-mínima; (2) o tempo de reconstrução não é contado (não faz parte do enunciado); (3) modelo: leitura/escrita da tabela, soma e comparação no corpo ordenado dos custos são operações unitárias, conforme a seção do TeX; (4) as constantes explícitas 8 e 7 materializam O(.) para M>=1.

- [`Artigo.Setup.state_complexity`](../lean4/ambientes/artigo_2/RequestProject/Complexity.lean) — linha 89.
- [`Pendencias.DenseDP.state_complexity_dense`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1813.
- [`Pendencias.DenseDP.dense_variable_complexity`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 866.
- [`Pendencias.DenseDP.dense_budget_complexity`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1459.
- [`Pendencias.DenseDP.dense_variable_init`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1614.
- [`Pendencias.DenseDP.dense_budget_init`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1762.

## III.9.2 — observação tabelas esparsas

Original de 77 páginas: 14.2.

Fonte editável: [tex/partes/artigo_2.tex:2033](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.2`.

Estado: **Observação editorial**. Observação ou diagnostico do texto; não é um teorema Lean autônomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.9.3 — teorema cota grosseira de complexidade de bits

Original de 77 páginas: 14.3.

Fonte editável: [tex/partes/artigo_2.tex:2083](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.3`.

Estado: **Formalizado e compilado**. bit_complexity limita o tamanho dos custos racionais. As cotas de tempo e memória em bits do artigo exigem semântica de execução e custo de operações/desempate. [13/11/2026] III.9.3 formalizado sobre a implementação densa de III.9.1 (leafInit agora testa admissibilidade antes de somar a perda; estado não admissível cobra 4P+3 como cota superior sem aritmética sobre os dados). Provado: (1) crescimento — todo custo finito Cvar/Cb da recorrência (entradas da tabela), toda soma de candidatos c_L+c_R (<= 4 B_cost+5 bits), todo candidato com penalidade (<= 16 B_cost+25 bits) e todo acumulador parcial da perda local (lossTm) tem comprimento em bits <= B_cost = Bcost S B L, a cota explícita de Setup.bit_complexity (2(P(5B+6clog H+2(k0+D)+9)+2B+2clog L+2)+3); (2) tempo em bits — número de operações de III.9.1 (S_D M^2 (4M+6)+4 S_D P M^2 sem orçamento; S_D M^2 (4P+3)+S_D M^2 N (4NM+2) com orçamento) multiplicado por opBits = arith(b)+L+entryBits, com opBits <= cA MZ(b) clog(2b)+2L+b+idx, b=16 B_cost+25; (3) memória em bits — dom.card * (B_cost+L+idx) exatamente S_D M^2 (resp. S_D N M^2) vezes. Multiplicação escolar: schoolModel (MZ b = b^2). Compilado e auditado (propext, Classical.choice, Quot.sound). Ressalvas: (a) o custo de uma soma/comparação/redução de frações com operandos de b bits, <= cA MZ(b) log(2b), e Hipótese do modelo (BitModel.arith_le), como no TeX ("algoritmos inteiros usuais"); não ha modelo de maquina em Lean; (b) o tempo em bits é o número de operações unitárias vezes o custo-limite de uma operação (argumento do TeX), não uma simulação bit a bit; (c) BitHyp assume B (bl dos dados/penalidades) e L (comprimento de fluxo das representações do catalogo, eq. stream-length) como no teorema bit_complexity; (d) os índices (idxBits = clog(S_D M+1)) aparecem explicitamente em vez de absorvidos; (e) vale a ressalva de III.9.1 sobre o desempate kappa (comparações de chave unitárias; empate shortlex custa L).

- [`Artigo.Setup.bit_complexity`](../lean4/ambientes/artigo_2/RequestProject/BitComplexity.lean) — linha 266.
- [`Pendencias.DenseDP.bit_complexity_dense`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 178.
- [`Pendencias.DenseDP.Cvar_bits`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 60.
- [`Pendencias.DenseDP.Cb_bits`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 68.
- [`Pendencias.DenseDP.candidate_bits`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 86.
- [`Pendencias.DenseDP.lossTm_acc_bits`](../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 124.

## III.9.4 — proposição convergência dos mínimos penalizados

Original de 77 páginas: 14.4.

Fonte editável: [tex/partes/artigo_2.tex:2160](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.truncation_convergence`](../lean4/ambientes/artigo_2/RequestProject/Complexity.lean) — linha 200.

## III.9.5 — proposição um seletor exato pode ser descontínuo

Original de 77 páginas: 14.5.

Fonte editável: [tex/partes/artigo_2.tex:2195](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.5`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.instability`](../lean4/ambientes/artigo_2/RequestProject/Complexity.lean) — linha 288.

## III.11.1 — teorema minimalidade exata do limiar

Original de 77 páginas: 16.1.

Fonte editável: [tex/partes/artigo_2.tex:2521](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:11.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.threshold_optimality`](../lean4/ambientes/artigo_2/RequestProject/Dyadic.lean) — linha 337.
- [`Artigo.Edia_eq_sInf_nThr`](../lean4/ambientes/artigo_2/RequestProject/Dyadic.lean) — linha 363.

## III.11.2 — lema expansão local uniforme

Original de 77 páginas: 16.2.

Fonte editável: [tex/partes/artigo_2.tex:2581](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:11.2`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] f ∈ C²(K) via `ContDiffOn`; e_f(J), f″ e ω_{f″} unilaterais em K, por `extF` e lemas de congruência. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.local_asymptotic_error`](../lean4/ambientes/artigo_2/RequestProject/Dyadic.lean) — linha 455.
- [`Pendencias.local_asymptotic_error_on`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 229.

## III.11.3 — teorema envelope diádico universal e agudo

Original de 77 páginas: 16.3.

Fonte editável: [tex/partes/artigo_2.tex:2608](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:11.3`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] f ∈ C²(K) via `ContDiffOn`, com `curvIOn` (I(f) com f″ unilateral); as três formas (eventual, liminf/limsup, caso I(f)=0). Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.general_dyadic_envelope`](../lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean) — linha 519.
- [`Artigo.general_dyadic_envelope_zero`](../lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean) — linha 544.
- [`Artigo.general_dyadic_envelope_liminf`](../lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean) — linha 597.
- [`Pendencias.general_dyadic_envelope_on`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 240.
- [`Pendencias.general_dyadic_envelope_liminf_on`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 255.
- [`Pendencias.general_dyadic_envelope_zero_on`](../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 270.

## III.12.1 — teorema lei exata e intervalo de acumulação

Original de 77 páginas: 17.1.

Fonte editável: [tex/partes/artigo_2.tex:2705](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.1`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensão Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipóteses dos componentes citados. [11/11/2026] Mesmas seis conclusões de `quadratic_dyadic_constant` com `q ∈ C²(K)` (`ContDiffOn`) e `q″ ≡ κ` unilateral em K; usa `extF` e lemas de congruência (`Edia_congr`, `nThr_congr`). Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.quadratic_dyadic_constant`](../lean4/ambientes/artigo_2/RequestProject/DyadicExact.lean) — linha 58.
- [`Pendencias.quadratic_dyadic_constant_on`](../lean4/ambientes/artigo_2/Pendencias/LeiExata.lean) — linha 74.

## III.12.2 — teorema contagem exata em uma malha diádica base

Original de 77 páginas: 17.2.

Fonte editável: [tex/partes/artigo_2.tex:2813](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.2`.

Estado: **Generalização documentada**. O Lean dispensa C1: a igualdade com quadráticas nas células fechadas conserva compatibilidade nos extremos. O texto mantém C1; não foi modificado.

- [`Artigo.piecewise_quadratic_count`](../lean4/ambientes/artigo_2/RequestProject/DyadicPhase.lean) — linha 238.

## III.12.3 — corolário fases sincronizadas

Original de 77 páginas: 17.3.

Fonte editável: [tex/partes/artigo_2.tex:2860](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.3`.

Estado: **Prova textual sincronizada**. A demonstração Lean evita aplicar o envelope C2 global a uma função quadrática por partes que pode não ser C2. Manter o enunciado e atualizar a demonstração textual em etapa posterior. [13/11/2026] Demonstração textual sincronizada com Artigo.synchronized_phases, preservando o enunciado e sem invocar o envelope C2 global para a função quadrática por partes. PDF recompilado nesta rodada.

- [`Artigo.synchronized_phases`](../lean4/ambientes/artigo_2/RequestProject/DyadicSync.lean) — linha 99.

## III.12.4 — observação agudeza uniforme e comportamento pontual

Original de 77 páginas: 17.4.

Fonte editável: [tex/partes/artigo_2.tex:2967](../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.4`.

Estado: **Observação editorial**. Observação ou diagnostico do texto; não é um teorema Lean autônomo.

Nenhuma declaração Lean associada na matriz recebida.


## Parte IV

## IV.3.1 — proposição aninhamento da agenda

Original de 77 páginas: 18.1.

Fonte editável: [tex/partes/artigo_3.tex:81](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.1`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] Definições `Sigma`, `pErr` formalizadas sobre K=[0,1] (domínio de `jointErr`); inclusão, monotonia, cota por ‖f‖ e atingimento do ínfimo (catálogo finito), além da fórmula min{‖f‖, E_{N,H(N)}}. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Agenda.schedule_nesting`](../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 67.
- [`Pendencias.Agenda.pErr_eq_min`](../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 44.

## IV.3.2 — teorema redução exata às escalas diádicas

Original de 77 páginas: 18.2.

Fonte editável: [tex/partes/artigo_3.tex:133](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.2`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] Funcional `rateQ` (q<∞) e `rateInf` (q=∞); constantes `C = 2^α` e `K = (1+2·(2^α)^q)^{1/q}` só dependem de α, q. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.dyadic_reduction`](../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 142.
- [`Pendencias.Agenda.dyadic_reduction_inf`](../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 181.

## IV.3.3 — proposição falha exata de homogeneidade

Original de 77 páginas: 18.3.

Fonte editável: [tex/partes/artigo_3.tex:166](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.3`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] Com H(1) ≥ 2: 𝔞(x) = 0 e 𝔞(√2 x) > 0, para 0<q<∞ e q=∞ (irracionalidade de √2). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.homogeneity_failure`](../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 253.
- [`Pendencias.Agenda.homogeneity_failure_inf`](../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 269.

## IV.3.4 — observação estrutura aritmética do funcional

Original de 77 páginas: 18.4.

Fonte editável: [tex/partes/artigo_3.tex:197](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.4`.

Estado: **Observação editorial**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.4.1 — lema Jackson racional com altura explícita

Original de 77 páginas: 19.1.

Fonte editável: [tex/partes/artigo_3.tex:277](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.1`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Jackson racional em raiz diádica geral, constante absoluta 8 e versão uniforme sobre bolas; Whitney demonstrada, sem hipótese adicional não provada. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.rational_jackson_height`](../lean4/ambientes/artigo_2/Pendencias/Jackson.lean) — linha 508.
- [`Pendencias.Jackson.rational_jackson_uniform`](../lean4/ambientes/artigo_2/Pendencias/Jackson.lean) — linha 678.

## IV.4.2 — teorema direção direta com altura aritmética

Original de 77 páginas: 19.2.

Fonte editável: [tex/partes/artigo_3.tex:398](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.2`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Inclusões diretas de Besov para os regimes do enunciado, inclusive agenda com folga polinomial, em raiz diádica geral. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.direct_besov_height`](../lean4/ambientes/artigo_2/Pendencias/Direta.lean) — linha 594.

## IV.4.3 — corolário imersões quantitativas uniformes sobre bolas

Original de 77 páginas: 19.3.

Fonte editável: [tex/partes/artigo_3.tex:453](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.3`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Cotas quantitativas uniformes sobre bolas nos três regimes, com constantes independentes da função e do raio. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.uniform_besov_ball`](../lean4/ambientes/artigo_2/Pendencias/Direta.lean) — linha 718.

## IV.4.4 — observação o papel do índice $q$

Original de 77 páginas: 19.4.

Fonte editável: [tex/partes/artigo_3.tex:501](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.4`.

Estado: **Observação editorial**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.4.5 — corolário endpoint $C^2$

Original de 77 páginas: 19.5.

Fonte editável: [tex/partes/artigo_3.tex:518](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.5`.

Estado: **Formalizado e compilado**. A estimativa C2 de base existe. Falta transportá-la para as definições de agenda, erro e classe do atual Artigo 3; não contado como teorema integralmente formalizado. [11/11/2026] Funcional `rateInf` (𝔞_{α,∞}) e agenda `H2 R M N = ⌈C_H N²⌉` definidos; sup sobre `FRMIcc R M` (C² só em [0,1]) de 𝔞_{2,∞} ≤ max{R,(M+4)/2}; para N ≥ 2, montagem admissível com códigos ≤ C_b N log₂(2N). Base: `joint_all_N_Icc`, `joint_budget_Icc`, `pErr_eq_min`. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Dyadic.Lib.simultaneous_control`](../lean4/ambientes/base_integrada/Unified/Consolidado/Sec7/Simultaneous.lean) — linha 477.
- [`Dyadic.Lib.precision_height`](../lean4/ambientes/base_integrada/Unified/Consolidado/Sec7/Precision.lean) — linha 71.
- [`Pendencias.Agenda.c2_endpoint`](../lean4/ambientes/artigo_2/Pendencias/Endpoint.lean) — linha 31.
- [`Pendencias.Agenda.c2_endpoint_bits`](../lean4/ambientes/artigo_2/Pendencias/Endpoint.lean) — linha 56.

## IV.4.6 — proposição piso aritmético uniforme

Original de 77 páginas: 19.6.

Fonte editável: [tex/partes/artigo_3.tex:555](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.6`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] Piso e_N ≥ 1/(2H(N)), dist(1/(2H), 𝒬_H) = 1/(2H) e a consequência H(N) ≥ (2C)⁻¹N^s (para N ≥ 1), sobre K=[0,1]. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Agenda.arithmetic_floor`](../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 125.
- [`Pendencias.Agenda.infDist_QH`](../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 111.
- [`Pendencias.Agenda.height_lower_bound`](../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 160.

## IV.5.1 — definição biblioteca marcada completa

Original de 77 páginas: 20.1.

Fonte editável: [tex/partes/artigo_3.tex:756](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.1`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] Definições `MAtom` (s ∈ ℚ qualquer), `MTree`, `MWF`, `MAsm`, `MAsmNH`; inclusões 𝓛 ⊂ 𝓛^□, 𝒜 ⊂ 𝒜^□, 𝒜_{N,H} ⊂ 𝒜^□_{N,H}. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Marcada.marked_extends`](../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 157.
- [`Pendencias.Marcada.Atom.toM_injective`](../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 52.

## IV.5.2 — teorema reversibilidade rasa exata

Original de 77 páginas: 20.2.

Fonte editável: [tex/partes/artigo_3.tex:793](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.2`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Teorema completo exact_shallow_reversal para parâmetros reais: equivalência marcada e aritmética, construção canônica, minimalidade e unicidade inclusive dos rótulos atômicos, M+1 <= N_can <= 1+sum d_j e equivalência com a biblioteca original quando todas as inclinações são não nulas. Igualdade de funções em [0,1], como no TeX; inclui M=0. Build Pendencias e auditoria de axiomas aprovados, apenas propext, Classical.choice, Quot.sound.

- [`Pendencias.Marcada.RealReLU.exact_shallow_reversal`](../lean4/ambientes/artigo_2/Pendencias/ReversaoOriginal.lean) — linha 219.

## IV.5.3 — definição altura canônica de rede

Original de 77 páginas: 20.3.

Fonte editável: [tex/partes/artigo_3.tex:845](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.3`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] Definições `canonShape` (𝒯(S)), `RedReLU`, `Hcan`; H_can = maior altura dos átomos da montagem canônica; folhas de 𝒯(S) sem quebras no interior. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Marcada.RedReLU.Hcan`](../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 265.
- [`Pendencias.Marcada.RedReLU.Hcan_eq_maxHeight`](../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 274.
- [`Pendencias.Marcada.canonShape_no_interior`](../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 203.
- [`Pendencias.Marcada.RedReLU.canon_leaves_free`](../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 280.

## IV.5.4 — proposição forma ancorada e comprimento estrutural

Original de 77 páginas: 20.4.

Fonte editável: [tex/partes/artigo_3.tex:863](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.4`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] IV.5.4 fechado nas duas direções, com a cota inversa CORRIGIDA aprovada pelo usuário (a cota impressa é falsa: R(x)=x, M=0, D=0, W=1). Volta: H_can(R) <= 2^(D+1)(M+2)W^(M+3) e log2 H_can <= 5[(M+1)log2(2W)+D+log2(M+1)] (AlturaInversa.lean); no_additive_constant_fix mostra que nenhum termo aditivo conserta a versão antiga. Ida: forma ancorada reduzida e código prefix-free de comprimento <= 40 N floor(log2 2H) (FormaAncorada.lean, CodigoAncorado.lean). Ressalva: a forma reduzida é a estrutura Anchored, sem ponte explícita para RealReLU. Enunciado corrigido e formalizado (sem sorry) em verificacao/IV_5_4/IV_5_4_trecho_corrigido.tex.

- [`Pendencias.Marcada.AlturaInversa.Hcan_le`](../lean4/ambientes/artigo_2/Pendencias/AlturaInversa.lean) — linha 365.
- [`Pendencias.Marcada.AlturaInversa.reverse_height_bit_bound`](../lean4/ambientes/artigo_2/Pendencias/AlturaInversa.lean) — linha 376.
- [`Pendencias.Marcada.AlturaInversa.no_additive_constant_fix`](../lean4/ambientes/artigo_2/Pendencias/AlturaInversa.lean) — linha 442.
- [`Pendencias.Marcada.Ancorada.anchored_form`](../lean4/ambientes/artigo_2/Pendencias/FormaAncorada.lean) — linha 465.
- [`Pendencias.Marcada.Ancorada.direct_part`](../lean4/ambientes/artigo_2/Pendencias/CodigoAncorado.lean) — linha 175.

## IV.5.5 — teorema reversão aproximada quantizada

Original de 77 páginas: 20.5.

Fonte editável: [tex/partes/artigo_3.tex:950](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.5`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] IV.5.5 formalizado: quantized_approximate_reverse com C universal = 320 (mesma constante em D_eps e na cota de altura). Para forma ReLU reduzida real com |c|,|q|,|a_j| <= W, W >= 1, e 0<eps<=1, existe montagem U da biblioteca original (LTree.WF, inclinação não nula) com erro uniforme <= eps em [0,1], número de folhas <= 1+M*ceil(log2(C(M+1)(W+1)/eps)) e altura atômica máxima <= C(M+1)^3(W+1)^3/eps^2; vale com regiões planas. Prova: arredondamento de c,q,a_j a múltiplos de 1/Q, quebras a j/2^D (1<=j<=2^D-1), perturbação t/Q da inclinação global com t em [1,M+2] escolhido por gavetas, montagem canônica de IV.5.2 transportada para LTree. A cota de altura e provada diretamente com denominador comum (Hcan_leQ); não usa a cota impressa antiga de IV.5.4. Compilado e auditado (apenas propext, Classical.choice, Quot.sound). Ressalvas: D_eps usa Nat.ceil (o argumento do log e >= 1, logo coincide com o teto inteiro); a cota de folhas usa a profundidade de quantização D <= D_eps. A prova textual do TeX permanece como esboço (usa Q ~ delta^-1 com delta=eps/(16(M+1)(W+1)); a formalização usa Q = ceil(4(M+2)/eps) e 2^D >= 2(M+1)(W+1)/eps, que dão as mesmas ordens).

- [`Pendencias.Marcada.QuantIV55.quantized_approximate_reverse`](../lean4/ambientes/artigo_2/Pendencias/ReversaoQuantizada.lean) — linha 666.
- [`Pendencias.Marcada.QuantIV55.construct`](../lean4/ambientes/artigo_2/Pendencias/ReversaoQuantizada.lean) — linha 558.
- [`Pendencias.Marcada.QuantIV55.Hcan_leQ`](../lean4/ambientes/artigo_2/Pendencias/ReversaoQuantizada.lean) — linha 187.

## IV.5.6 — corolário redes profundas medidas pela função realizada

Original de 77 páginas: 20.6.

Fonte editável: [tex/partes/artigo_3.tex:1012](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.6`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] IV.5.6 formalizado: deep_functional_reverse. Redes ReLU univariadas feedforward arbitrarias (NetFun: camadas afins e ReLU alternadas, qualquer profundidade/largura) realizam funções contínuas lineares por partes (fecho por combinações afins e por max 0, via colagem e remoção da ultima quebra). Para F com norma uniforme <= B e Lipschitz <= L em [0,1], F coincide em [0,1] com uma forma ReLU reduzida real (quebras estritas em (0,1), saltos não nulos) com M+1 = R(F) hinges+1, onde R(F) = regionCount F é o menor número de peças afins de [0,1] (regiões afins máximas); |c|<=B, |q|<=L, |a_j|<=2L, todos <= W = 2 max{1,B,L}; e IV.5.5 (quantized_approximate_reverse) vale com esses M e W. Compilado e auditado (propext, Classical.choice, Quot.sound). Escolhas de formalização: B e Lipschitz medidos em [0,1] (domínio do enunciado); R(F) definido como mínimo de peças afins, equivalente a regiões afins máximas para F continua (regionCount_eq prova R(F)=M+1 para a forma reduzida). A prova do TeX permanece valida; a formalização explícita a derivada via inclinações locais sigma_n.

- [`Pendencias.Marcada.DeepIV56.deep_functional_reverse`](../lean4/ambientes/artigo_2/Pendencias/ReversaoProfunda.lean) — linha 583.
- [`Pendencias.Marcada.DeepIV56.regionCount_eq`](../lean4/ambientes/artigo_2/Pendencias/ReversaoProfunda.lean) — linha 499.

## IV.5.7 — teorema imersão inversa sob crescimento de Lipschitz

Original de 77 páginas: 20.7.

Fonte editável: [tex/partes/artigo_3.tex:1115](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.7`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] ω₂ e Besov pela norma diádica do texto em [0,1]; C = 4 + 2^{γ+1}; hipótese A_α(f) ≤ A na forma e_N ≤ A N^{-α}; conclusões B^{θ*}_{∞,∞} e B^θ_{∞,p} (θ<θ*, 0<p<∞). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.inverse_modulus`](../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 167.
- [`Pendencias.Agenda.inverse_besov`](../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 262.

## IV.5.8 — corolário aplicação às agendas diretas

Original de 77 páginas: 20.8.

Fonte editável: [tex/partes/artigo_3.tex:1170](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.8`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] H(N) ≤ C N^γ ⟹ 𝒜^α_q ⊂ B^{α/(α+γ)}_{∞,∞} (q<∞ via IV.3.2 e q=∞); agendas `Hsk` = H_{s,κ} em [0,1] (C_K = 8): ϑ_s e ordens < ϑ_s com fator logarítmico. Montagens H(N)-Lipschitz (`Sigma_lipschitz`). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.raw_library_inverse_inf`](../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 419.
- [`Pendencias.Agenda.raw_library_inverse`](../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 430.
- [`Pendencias.Agenda.schedule_raw_inverse`](../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 536.
- [`Pendencias.Agenda.vartheta_eq`](../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 526.

## IV.5.9 — teorema agudeza por um pente de tendas

Original de 77 páginas: 20.9.

Fonte editável: [tex/partes/artigo_3.tex:1206](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.9`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Teorema do pente de tendas IV.5.9 concluído em Pendencias.PenteGemini.critical_tent_comb: continuidade, aproximação para todo N >= 1 na biblioteca original e não pertencimento às classes Besov acima e no expoente critico para todo r finito. Build Pendencias e auditoria agregada passaram; axiomas permitidos.

- [`Pendencias.PenteGemini.critical_tent_comb`](../lean4/ambientes/artigo_2/Pendencias/Pente.lean) — linha 1194.

## IV.5.10 — lema desigualdade inversa universal

Original de 77 páginas: 20.10.

Fonte editável: [tex/partes/artigo_3.tex:1315](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.10`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [11/11/2026] ω₂(f,1/N) ≤ 4 𝓡_N(f) para toda agenda, toda f e todo N (`realN`). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.universal_inverse`](../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 109.

## IV.5.11 — observação o que o funcional mede

Original de 77 páginas: 20.11.

Fonte editável: [tex/partes/artigo_3.tex:1336](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.11`.

Estado: **Observação editorial**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.5.12 — teorema Jackson racional para o funcional de realização

Original de 77 páginas: 20.12.

Fonte editável: [tex/partes/artigo_3.tex:1342](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.12`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Jackson para o funcional de realização em [0,1], cota bilateral e versão uniforme; constantes universais explícitas. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.regularized_jackson`](../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 87.
- [`Pendencias.Jackson.regularized_jackson_uniform`](../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 119.

## IV.5.13 — teorema caracterização pelo funcional de realização

Original de 77 páginas: 20.13.

Fonte editável: [tex/partes/artigo_3.tex:1390](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.13`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Igualdades de classes de Besov e realização em todos os regimes declarados, incluindo folga polinomial. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.complete_besov_reversibility`](../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 393.

## IV.5.14 — teorema reversibilidade estável por inclusão de redes

Original de 77 páginas: 20.14.

Fonte editável: [tex/partes/artigo_3.tex:1476](../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.14`.

Estado: **Formalizado e compilado**. Não foi localizado resultado Lean que certifique este enunciado. Fase3 é uma etapa da formalização do Artigo 1, não o atual Artigo 3. [13/11/2026] Estabilidade das igualdades para famílias aninhadas que contêm zero e as montagens na escala linear declarada. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.architecture_stable_reversibility`](../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 448.


## Parte V

## V.6.1 — teorema taxa garantida em árvores

Original de 77 páginas: 6.1.

Fonte editável: [tex/partes/complemento_original.tex:27](../tex/partes/complemento_original.tex); rótulo `map:complemento_original:6.1`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondência editorial não afirma prova Lean. [11/11/2026] σ_N^dia = `Edia`; f ∈ C²(K) via `ContDiffOn`; taxas M L²/(8N²) (N = 2^r) e M L²/(2N²); montagem racional na mesma árvore (qualquer `DShape`) com erro < ‖f − P_Λ f‖ + δ. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.tree_rate_pow`](../lean4/ambientes/artigo_2/Pendencias/Arvores.lean) — linha 54.
- [`Pendencias.tree_rate`](../lean4/ambientes/artigo_2/Pendencias/Arvores.lean) — linha 62.
- [`Pendencias.tree_rationalization`](../lean4/ambientes/artigo_2/Pendencias/Arvores.lean) — linha 255.

## V.6.2 — teorema cota assintótica com nós livres

Original de 77 páginas: 6.2.

Fonte editável: [tex/partes/complemento_original.tex:57](../tex/partes/complemento_original.tex); rótulo `map:complemento_original:6.2`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondência editorial não afirma prova Lean. [13/11/2026] Cota assintótica com nós livres e derivadas unilaterais para funções C2 no intervalo fechado. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.NosLivres.free_knots`](../lean4/ambientes/artigo_2/Pendencias/NosLivres.lean) — linha 123.

## V.6.3 — teorema estimativa direta

Original de 77 páginas: 6.3.

Fonte editável: [tex/partes/complemento_original.tex:109](../tex/partes/complemento_original.tex); rótulo `map:complemento_original:6.3`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondência editorial não afirma prova Lean. [13/11/2026] Estimativa direta em raiz diádica geral, constante de Whitney explícita e montagem racional com erro adicional arbitrário. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.besov_direct`](../lean4/ambientes/artigo_2/Pendencias/BesovDireta.lean) — linha 129.
- [`Pendencias.Jackson.besov_direct_whitney`](../lean4/ambientes/artigo_2/Pendencias/BesovDireta.lean) — linha 109.

## V.21.1 — lema majorante local da função de Runge

Original de 77 páginas: 21.1.

Fonte editável: [tex/partes/complemento_original.tex:152](../tex/partes/complemento_original.tex); rótulo `map:complemento_original:21.1`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondência editorial não afirma prova Lean. [11/11/2026] Provado; a forma `runge_majorant` dispensa J ⊆ [-1,1]. Inclui `deriv2_runge`. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Runge.runge_majorant_sub`](../lean4/ambientes/artigo_2/Pendencias/Runge.lean) — linha 118.
- [`Pendencias.Runge.runge_majorant`](../lean4/ambientes/artigo_2/Pendencias/Runge.lean) — linha 84.


