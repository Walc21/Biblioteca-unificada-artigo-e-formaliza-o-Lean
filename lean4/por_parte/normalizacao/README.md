# Parte II — Normalização e equivalência das montagens

Os módulos executáveis ficam em `../../ambientes/`. Este diretório contém o índice da parte, sem mover os módulos e quebrar imports.

## II.2.1 — definicao racional reduzido e altura

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:89](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.ht`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 39.
- [`Montagens.ht_props`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 44.

## II.2.2 — definicao célula e funções de seus extremos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:106](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.Cell`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 51.
- [`Montagens.LQ`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 54.
- [`Montagens.RQ`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 56.
- [`Montagens.XQ`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 58.
- [`Montagens.J`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 68.
- [`Montagens.O`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 70.
- [`Montagens.P`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 72.
- [`Montagens.Dy`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 75.

## II.2.3 — lema geometria elementar

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:129](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.geometry`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 81.

## II.2.4 — definicao átomo e suas projeções

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:149](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.4`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.Atom`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 131.
- [`Montagens.Atom.height`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 159.
- [`SemanticBridge.normalizationAtomEquiv`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationAtoms.lean) — linha 22.
- [`SemanticBridge.normalization_atom_height`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationAtoms.lean) — linha 40.

## II.2.5 — lema formas da reta

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:170](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:2.5`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.line_forms`](../../../lean4/ambientes/parte_1/RequestProject/Basic.lean) — linha 168.
- [`SemanticBridge.normalization_atom_line`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationAtoms.lean) — linha 37.

## II.3.1 — definicao campos dos contratos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:191](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.1`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.Sep`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 25.
- [`Montagens.Cover`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 29.
- [`Montagens.MatchK`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 33.
- [`Montagens.Agree`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 41.
- [`Montagens.LocalRep`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 45.
- [`Montagens.StrongRep`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 49.
- [`SemanticBridge.normalization_local_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 17.
- [`SemanticBridge.normalization_strong_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 29.

## II.3.2 — definicao atividade e filtro

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:228](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.Active`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 69.
- [`Montagens.NormK`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 72.

## II.3.3 — lema critério exato de atividade

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:241](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.active_iff`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 78.

## II.3.4 — lema intervalos separados

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:262](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.separated_of_disjoint`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 92.
- [`Montagens.separated_inter`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 103.

## II.3.5 — teorema normalização

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:275](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.5`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.normalization`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 176.
- [`Montagens.normalizationG`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 198.
- [`SemanticBridge.normalizeAtoms_strong`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 79.
- [`SemanticBridge.normalizeAtoms_subset`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 64.
- [`SemanticBridge.normalizeAtoms_card_le`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 70.
- [`SemanticBridge.normalizeAtoms_idem`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 74.

## II.3.6 — corolario equivalência local e consolidada

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:314](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:3.6`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.Aloc_eq_Astr`](../../../lean4/ambientes/parte_1/RequestProject/Normalization.lean) — linha 219.
- [`SemanticBridge.local_asm_eq_strong`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 87.

## II.4.1 — definicao pareamento e descompactação

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:329](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.T`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 23.
- [`Montagens.pair`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 28.
- [`Montagens.unpair`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 45.
- [`Montagens.pack`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 48.
- [`Montagens.unpack`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 53.

## II.4.2 — lema inversas do pareamento

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:354](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.2`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.pair_props`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 92.
- [`SemanticBridge.normalization_pair`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 22.
- [`SemanticBridge.normalization_unpack2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 37.
- [`SemanticBridge.normalization_unpack3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 34.

## II.4.3 — definicao enumeração dos inteiros

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:382](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.3`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.Zenc`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 136.
- [`Montagens.Zinv`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 139.
- [`Montagens.Zenc_Zinv`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 153.
- [`Montagens.Zinv_Zenc`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 160.
- [`SemanticBridge.normalization_Z2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 50.
- [`SemanticBridge.normalization_Z3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 41.

## II.4.4 — definicao ordens e postos dos racionais

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:393](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.QH`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 169.
- [`Montagens.prec`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 222.
- [`Montagens.Pred`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 228.
- [`Montagens.rank`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 231.
- [`Montagens.rankStar`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 238.

## II.4.5 — lema postos e enumerações inversas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:430](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.5`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.prec_coincide`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 291.
- [`Montagens.rank_bijective`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 372.
- [`Montagens.rankStar_bijective`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 376.
- [`SemanticBridge.normalization_rank2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 82.
- [`SemanticBridge.normalization_rank3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 54.
- [`SemanticBridge.normalization_Q2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 101.
- [`SemanticBridge.normalization_Q3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 69.
- [`SemanticBridge.normalization_Qstar2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 107.
- [`SemanticBridge.normalization_Qstar3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 75.

## II.4.6 — definicao codificadores concretos de átomos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:468](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.6`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.enc`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 401.
- [`Montagens.dec`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 406.
- [`Montagens.tau`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 420.

## II.4.7 — lema contrato completo de endereçamento

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:491](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:4.7`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.codec`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 430.
- [`Montagens.tau_props`](../../../lean4/ambientes/parte_1/RequestProject/Enumeration.lean) — linha 449.
- [`SemanticBridge.normalization_ofFase2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 129.
- [`SemanticBridge.normalization_ofFase3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationEnumerations.lean) — linha 115.
- [`SemanticBridge.normalization_C2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 40.
- [`SemanticBridge.normalization_C3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 35.
- [`SemanticBridge.normalization_lam2`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 59.
- [`SemanticBridge.normalization_lam3`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 53.

## II.5.1 — definicao testemunha por células endereçadas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:517](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.CellRep`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 26.
- [`Montagens.CellRepG`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 33.

## II.5.2 — definicao continuidade no domínio e restrição

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:537](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.2`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.ContOn`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 42.
- [`Montagens.Res`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 55.
- [`Montagens.ResImage`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 59.
- [`SemanticBridge.normalization_contOn_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 66.

## II.5.3 — definicao as três classes tipadas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:558](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.3`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.B2`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 65.
- [`Montagens.B3`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 69.
- [`Montagens.Bcon`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 73.
- [`SemanticBridge.normalization_B2_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 109.
- [`SemanticBridge.normalization_B3_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 83.
- [`SemanticBridge.normalization_Bcon_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 93.

## II.5.4 — lema conversões explícitas das testemunhas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:575](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.cellsToAtoms_spec`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 176.
- [`Montagens.cellsToAtoms_specG`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 189.
- [`Montagens.atomsToCells_spec`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 202.
- [`Montagens.atomsToCells_specG`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 216.

## II.5.5 — definicao extensão contínua por projeção

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:629](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.5`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.projK`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 232.
- [`Montagens.E0`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 239.
- [`Montagens.Res_E0`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 260.

## II.5.6 — teorema equivalência extensional tipada

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:644](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:5.6`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.bridge`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 318.
- [`Montagens.B3_eq_Bcon`](../../../lean4/ambientes/parte_1/RequestProject/Bridge.lean) — linha 309.
- [`SemanticBridge.fase3_assembly_iff_consolidated`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 105.
- [`SemanticBridge.fase2_restriction_eq_consolidated`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationClasses.lean) — linha 142.

## II.6.1 — definicao orçamento da testemunha

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:676](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.1`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.Budget`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 23.
- [`Montagens.AlocNH`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 27.
- [`Montagens.AstrNH`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 31.
- [`SemanticBridge.normalization_budget_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 37.

## II.6.2 — teorema igualdade sob os mesmos recursos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:693](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.2`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.AlocNH_eq_AstrNH`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 37.
- [`SemanticBridge.local_budgeted_eq_strong`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 103.
- [`SemanticBridge.normalization_typed_budget_iff`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 17.

## II.6.3 — definicao distância uniforme e ínfimo

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:705](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.3`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.dK`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 46.
- [`Montagens.Err`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 65.
- [`Montagens.dK_isMax`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 49.
- [`Montagens.Err_empty`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 74.
- [`SemanticBridge.normalization_distance`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 35.

## II.6.4 — corolario igualdade dos erros e de suas condições de altura

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:731](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.4`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.errors_eq`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 78.
- [`Montagens.heights_eq`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 82.
- [`SemanticBridge.normalization_Econ_eq_jointError`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 54.
- [`SemanticBridge.normalization_Eloc_eq_jointError`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationErrors.lean) — linha 86.
- [`SemanticBridge.local_height_conditions_eq`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationContracts.lean) — linha 125.

## II.6.5 — proposicao testemunhas já ativas

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:749](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:6.5`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.norm_fixed_of_active`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 91.
- [`Montagens.norm_fixed_of_subset`](../../../lean4/ambientes/parte_1/RequestProject/Error.lean) — linha 95.

## II.7.1 — definicao ordem auxiliar total dos átomos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:769](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.zeta`](../../../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 25.
- [`Montagens.sortAtoms`](../../../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 40.

## II.7.2 — lema propriedades da lista ordenada

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:800](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.sortAtoms_props`](../../../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 55.

## II.7.3 — definicao tipo dos dados de cadeia

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:820](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain`](../../../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 110.

## II.7.4 — teorema construção determinada da cadeia

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:844](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:7.4`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.chainOf`](../../../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 344.
- [`Montagens.chainOf_nodes_dyadic`](../../../lean4/ambientes/parte_1/RequestProject/Chain.lean) — linha 360.

## II.8.1 — definicao parâmetros e funções parciais

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:890](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.1`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain.Fpart`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 52.
- [`Montagens.NormChain.Rext`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 59.

## II.8.2 — lema expansão da recursão

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:920](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.2`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain.Rext_sum`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 88.
- [`Montagens.NormChain.Rext_anchor`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 103.
- [`Montagens.NormChain.Rext_of_M_eq_one`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 111.

## II.8.3 — lema identidade de duas retas incidentes

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:948](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.3`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.NormChain.incident`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 120.

## II.8.4 — teorema correção da extensão

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:965](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.4`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.NormChain.extension`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 211.
- [`SemanticBridge.fase2_relu_extension_agrees`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 27.
- [`SemanticBridge.fase2_relu_extension_is_consolidated`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 34.

## II.8.5 — lema unicidade de uma reta a partir de dois pontos

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:1013](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.5`.

Estado: **Correspondência inspecionada**. Resultado recebido preservado. A identificacao dos tipos de atomos, enderecos, classes e erros com a v2 esta provada nas pontes Normalization; consultar INTEGRACAO_NORMALIZACAO.md.

- [`Montagens.affine_eq_of_two_points`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 283.

## II.8.6 — teorema independência da testemunha

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:1025](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.6`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.Rext_unique`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 331.
- [`SemanticBridge.fase2_relu_extension_eq`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 47.

## II.8.7 — definicao operador de extensão das montagens

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/normalizacao.tex:1060](../../../tex/partes/normalizacao.tex); rótulo `map:normalizacao:8.7`.

Estado: **Integrado à base**. Identificacao com os tipos concretos da v2 provada nos modulos NormalizationAtoms, Contracts, Enumerations, Classes, Errors e ReLU. Hipoteses, dominio, funcao e orcamentos preservados.

- [`Montagens.extOp`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 359.
- [`Montagens.Res_extOp`](../../../lean4/ambientes/parte_1/RequestProject/ReLU.lean) — linha 370.
- [`SemanticBridge.fase2ReLUExtension`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 23.
- [`SemanticBridge.fase2_relu_extension_agrees`](../../../lean4/ambientes/base_integrada/Unified/SemanticBridge/NormalizationReLU.lean) — linha 27.


## Cópias para leitura

`fontes_referenciados/` reúne cópias byte a byte dos módulos associados. Para compilar, use os ambientes completos em `../../ambientes/`, que preservam imports e dependências.
