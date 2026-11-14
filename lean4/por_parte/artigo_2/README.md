# Parte III — Custo, entropia e seleção exata

Os módulos executáveis ficam em `../../ambientes/`. Este diretório contém o índice da parte, sem mover os módulos e quebrar imports.

## III.2.1 — lema indexação elementar

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/artigo_2.tex:26](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:2.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.cantorPair_bijective`](../../../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 77.
- [`Artigo.cantorPair_le`](../../../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 81.
- [`Artigo.Zenum_bijective`](../../../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 111.
- [`Artigo.Zinv_le`](../../../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 118.
- [`Artigo.card_QH_le`](../../../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 191.
- [`Artigo.card_QH_ge`](../../../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 320.
- [`Artigo.rank_lt_three_sq`](../../../lean4/ambientes/artigo_2/RequestProject/Indexing.lean) — linha 536.

## III.2.2 — definicao átomos e montagens

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/artigo_2.tex:43](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:2.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Atom`](../../../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 17.
- [`Artigo.Atom.interface_injective`](../../../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 115.
- [`Artigo.Atom.addr_injective`](../../../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 178.
- [`Artigo.LTree.WF`](../../../lean4/ambientes/artigo_2/RequestProject/Trees.lean) — linha 98.

## III.2.3 — proposicao densidade, interpolação e forma ReLU

Original de 77 páginas: sem correspondência direta; desenvolvimento da edição atual.

Fonte editável: [tex/partes/artigo_2.tex:54](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:2.3`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] Cota de interpolação provada com `ContDiffOn ℝ 2 f (Icc a b)` e `derivWithin`, via extensão C² portada da Fase 3 (`Pendencias/Extensao.lean`). Densidade e forma ReLU já batiam. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.assemblies_dense`](../../../lean4/ambientes/artigo_2/RequestProject/Uniform.lean) — linha 231.
- [`Artigo.interp_remainder_C2`](../../../lean4/ambientes/artigo_2/RequestProject/Interp.lean) — linha 126.
- [`Artigo.LTree.eval_relu_form`](../../../lean4/ambientes/artigo_2/RequestProject/Trees.lean) — linha 392.
- [`Pendencias.interp_remainder_C2On`](../../../lean4/ambientes/artigo_2/Pendencias/Interpolacao.lean) — linha 20.

## III.3.1 — teorema cota polinomial do endereço

Original de 77 páginas: 8.1.

Fonte editável: [tex/partes/artigo_2.tex:97](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.index_bound`](../../../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 48.

## III.3.2 — lema cardinalidade das cascas de altura

Original de 77 páginas: 8.2.

Fonte editável: [tex/partes/artigo_2.tex:123](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.card_LH_le`](../../../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 239.
- [`Artigo.card_LH_ge`](../../../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 264.
- [`Artigo.card_LH_theta`](../../../lean4/ambientes/artigo_2/RequestProject/Atoms.lean) — linha 272.

## III.3.3 — proposicao ordem exata do pior endereço aritmético

Original de 77 páginas: 8.3.

Fonte editável: [tex/partes/artigo_2.tex:175](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.3`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.MGamma_theta`](../../../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 137.
- [`Artigo.MGamma_bits`](../../../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 148.

## III.3.4 — teorema cota minimax relativa ao calibre

Original de 77 páginas: 8.4.

Fonte editável: [tex/partes/artigo_2.tex:216](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.address_lower`](../../../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 203.

## III.3.5 — observacao 

Original de 77 páginas: 8.5.

Fonte editável: [tex/partes/artigo_2.tex:245](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.5`.

Estado: **Observação editorial**. Observacao ou diagnostico do texto; nao e um teorema Lean autonomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.3.6 — definicao enumeração por altura da biblioteca

Original de 77 páginas: 8.6.

Fonte editável: [tex/partes/artigo_2.tex:252](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.6`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.nSharp`](../../../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 245.
- [`Artigo.GammaSharp`](../../../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 279.

## III.3.7 — teorema endereço minimax exato para a exaustão

Original de 77 páginas: 8.7.

Fonte editável: [tex/partes/artigo_2.tex:257](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.7`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.sharp_optimal`](../../../lean4/ambientes/artigo_2/RequestProject/Addresses.lean) — linha 293.

## III.3.8 — observacao qual endereço usar

Original de 77 páginas: 8.8.

Fonte editável: [tex/partes/artigo_2.tex:279](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.8`.

Estado: **Observação editorial**. Observacao ou diagnostico do texto; nao e um teorema Lean autonomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.3.9 — teorema serialização condicionada de montagens

Original de 77 páginas: 8.9.

Fonte editável: [tex/partes/artigo_2.tex:306](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.9`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.assembly_serialization`](../../../lean4/ambientes/artigo_2/RequestProject/Serialization.lean) — linha 184.
- [`Artigo.assembly_serialization_Gamma`](../../../lean4/ambientes/artigo_2/RequestProject/Serialization.lean) — linha 207.

## III.3.10 — observacao 

Original de 77 páginas: 8.10.

Fonte editável: [tex/partes/artigo_2.tex:341](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.10`.

Estado: **Observação editorial**. Observacao ou diagnostico do texto; nao e um teorema Lean autonomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.3.11 — lema cálculo elementar de alturas

Original de 77 páginas: 8.11.

Fonte editável: [tex/partes/artigo_2.tex:379](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.11`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.assembly_height_arith`](../../../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 160.

## III.3.12 — teorema comparação rigorosa dos formatos

Original de 77 páginas: 8.12.

Fonte editável: [tex/partes/artigo_2.tex:436](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.12`.

Estado: **Formalizado e compilado**. coding_gap_family prova uma cadeia para todo N par. O enunciado deste volume usa N=2^r e raiz J(H-1-r,0); a arvore em raiz unica para N=2^r continua nao formalizada em Lean (H=N=6 produz suporte [0,3/16], que nao e uma celula diadica unica). [11/11/2026] Montagem cheia `famTree` em J_{H-1-r,0} (WF, folhas J_{H-1,j}, altura H), N = 2^r; caso geral com N′ = 2^{⌊log₂N⌋}: NH ≤ 4 L_rat; inclui decodificadores e ordens. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.coding_formats_decoders`](../../../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 270.
- [`Artigo.coding_format_orders`](../../../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 421.
- [`Artigo.coding_gap_family`](../../../lean4/ambientes/artigo_2/RequestProject/Formats.lean) — linha 526.
- [`Pendencias.coding_formats_comparison`](../../../lean4/ambientes/artigo_2/Pendencias/Formatos.lean) — linha 71.

## III.3.13 — definicao erro conjunto número--altura

Original de 77 páginas: 8.13.

Fonte editável: [tex/partes/artigo_2.tex:514](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.13`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.jointErr`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 30.
- [`Artigo.heightFor`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 38.

## III.3.14 — proposicao monotonicidade dos dois orçamentos

Original de 77 páginas: 8.14.

Fonte editável: [tex/partes/artigo_2.tex:541](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.14`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.jointErr_succ_N_le`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 55.
- [`Artigo.jointErr_succ_H_le`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 59.
- [`Artigo.jointErr_tendsto`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 72.

## III.3.15 — lema controle uniforme da primeira derivada

Original de 77 páginas: 8.15.

Fonte editável: [tex/partes/artigo_2.tex:578](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.15`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; |f′| ≤ 4R+M/2 com f′ unilateral. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.derivative_control`](../../../lean4/ambientes/artigo_2/RequestProject/Interp.lean) — linha 231.
- [`Pendencias.derivative_control_Icc`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 129.
- [`Pendencias.FRM_subset_FRMIcc`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 56.
- [`Pendencias.extF_mem_FRM`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 59.

## III.3.16 — teorema controle simultâneo de erro, folhas, altura e bits

Original de 77 páginas: 8.16.

Fonte editável: [tex/partes/artigo_2.tex:600](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.16`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; mesma árvore determinística `uniformTree (jvals f r)` (só amostra f em [0,1]) e consequência para todo N ≥ 2. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.joint_budget`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 424.
- [`Artigo.joint_all_N`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 509.
- [`Pendencias.joint_budget_Icc`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 137.
- [`Pendencias.joint_all_N_Icc`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 153.

## III.3.17 — corolario altura suficiente para precisão prescrita

Original de 77 páginas: 8.17.

Fonte editável: [tex/partes/artigo_2.tex:715](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.17`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; n_ε, H_ε inalterados; `jointErr`, `heightFor` e `supDist` só dependem de f em [0,1]. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.height_for_epsilon`](../../../lean4/ambientes/artigo_2/RequestProject/JointBudget.lean) — linha 663.
- [`Pendencias.height_for_epsilon_Icc`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 159.

## III.3.18 — teorema entropia e codebook explícito

Original de 77 páginas: 8.18.

Fonte editável: [tex/partes/artigo_2.tex:794](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.18`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; coberturas de FRMIcc e FRM coincidem (`isCover_iff`), logo `entropyH ε (FRMIcc R M) = entropyH ε (FRM R M)`; codebook transportado. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.entropy_codebook`](../../../lean4/ambientes/artigo_2/RequestProject/Entropy.lean) — linha 46.
- [`Pendencias.entropy_codebook_Icc`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 178.

## III.3.19 — definicao recursos de um codec

Original de 77 páginas: 8.19.

Fonte editável: [tex/partes/artigo_2.tex:905](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.19`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.EpsCodec`](../../../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 21.
- [`Artigo.Ldec`](../../../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 35.
- [`Artigo.Lglobal`](../../../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 39.
- [`Artigo.Lfolhas`](../../../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 43.

## III.3.20 — proposicao limite informacional para representação decodificável

Original de 77 páginas: 8.20.

Fonte editável: [tex/partes/artigo_2.tex:949](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.20`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.description_lower`](../../../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 118.
- [`Artigo.complexity_chain`](../../../lean4/ambientes/artigo_2/RequestProject/Codecs.lean) — linha 180.

## III.3.21 — proposicao 

Original de 77 páginas: 8.21.

Fonte editável: [tex/partes/artigo_2.tex:1011](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.21`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.no_minimizer`](../../../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 22.

## III.3.22 — definicao catálogo truncado

Original de 77 páginas: 8.22.

Fonte editável: [tex/partes/artigo_2.tex:1040](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.22`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.RepCat`](../../../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 92.
- [`Artigo.SigmaCat`](../../../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 107.

## III.3.23 — teorema finitude, existência e desempate canônico

Original de 77 páginas: 8.23.

Fonte editável: [tex/partes/artigo_2.tex:1071](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.23`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.finite_catalog_minimizer`](../../../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 329.

## III.3.24 — proposicao consistência sob truncagem

Original de 77 páginas: 8.24.

Fonte editável: [tex/partes/artigo_2.tex:1113](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.24`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.catalog_consistency`](../../../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 360.

## III.3.25 — algoritmo enumeração exata do catálogo

Original de 77 páginas: 8.25.

Fonte editável: [tex/partes/artigo_2.tex:1138](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:3.25`.

Estado: **Formalizado e compilado**. A recorrencia ou existencia matematica tem prova; falta implementar e certificar a execucao e a reconstrucao com comparacao exata. [11/11/2026] Programa computável `gen`/`select`/`enumSelect`; = `RepCat` e devolve `canon` quando J é avaliado exatamente em ℚ. Testado com `#eval` (|𝓛₂| = 252; 42 e 102 representações para D = 0, 1, H = 2). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.finite_catalog_minimizer`](../../../lean4/ambientes/artigo_2/RequestProject/Catalog.lean) — linha 329.
- [`Pendencias.gen_eq_RepCat`](../../../lean4/ambientes/artigo_2/Pendencias/Enumeracao.lean) — linha 56.
- [`Pendencias.enumSelect_eq_canon`](../../../lean4/ambientes/artigo_2/Pendencias/Enumeracao.lean) — linha 136.

## III.4.1 — definicao pares de fronteira admissíveis

Original de 77 páginas: 9.1.

Fonte editável: [tex/partes/artigo_2.tex:1241](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.IsAdmPair`](../../../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 19.
- [`Artigo.PH`](../../../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 27.

## III.4.2 — proposicao dicionário exato de fronteiras

Original de 77 páginas: 9.2.

Fonte editável: [tex/partes/artigo_2.tex:1254](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.endpoint_dictionary`](../../../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 63.

## III.4.3 — definicao alfabeto de fronteira

Original de 77 páginas: 9.3.

Fonte editável: [tex/partes/artigo_2.tex:1296](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.3`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Valphabet`](../../../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 102.

## III.4.4 — lema finitude e suficiência

Original de 77 páginas: 9.4.

Fonte editável: [tex/partes/artigo_2.tex:1308](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.value_alphabet`](../../../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 122.

## III.4.5 — proposicao células vazias e refinamento uniforme máximo

Original de 77 páginas: 9.5.

Fonte editável: [tex/partes/artigo_2.tex:1344](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.5`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.translation_obstruction`](../../../lean4/ambientes/artigo_2/RequestProject/Interface.lean) — linha 230.

## III.4.6 — observacao assimetria espacial do catálogo

Original de 77 páginas: 9.6.

Fonte editável: [tex/partes/artigo_2.tex:1395](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:4.6`.

Estado: **Observação editorial**. Observacao ou diagnostico do texto; nao e um teorema Lean autonomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.5.1 — lema decodificação e aditividade

Original de 77 páginas: 10.1.

Fonte editável: [tex/partes/artigo_2.tex:1481](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:5.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.recursive_stream`](../../../lean4/ambientes/artigo_2/RequestProject/Functional.lean) — linha 57.

## III.5.2 — lema compatibilidade do desempate com a colagem

Original de 77 páginas: 10.2.

Fonte editável: [tex/partes/artigo_2.tex:1552](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:5.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.tie_concatenation`](../../../lean4/ambientes/artigo_2/RequestProject/Functional.lean) — linha 178.

## III.6.1 — definicao recorrência para árvore fixa

Original de 77 páginas: 11.1.

Fonte editável: [tex/partes/artigo_2.tex:1592](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:6.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.Cfix`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 114.

## III.6.2 — teorema correção para árvore fixa

Original de 77 páginas: 11.2.

Fonte editável: [tex/partes/artigo_2.tex:1625](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:6.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.fixed_correctness`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 164.
- [`Artigo.Setup.fixed_global`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 189.

## III.6.3 — algoritmo rotulação exata de uma árvore fixa

Original de 77 páginas: 11.3.

Fonte editável: [tex/partes/artigo_2.tex:1675](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:6.3`.

Estado: **Formalizado e compilado**. A recorrencia ou existencia matematica tem prova; falta implementar e certificar a execucao e a reconstrucao com comparacao exata. [11/11/2026] Tabela em pós-ordem com o κ-mínimo por estado (`fixTable`, colagem por w), custo = `Cfix`, raiz = rotulação κ-mínima de `fixed_global` (via Lema 5.2 `tie_concatenation`). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.Setup.fixed_correctness`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 164.
- [`Artigo.Setup.fixed_global`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 189.
- [`Pendencias.DPprog.fixTable_cost`](../../../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 190.
- [`Pendencias.DPprog.fixRoot_spec`](../../../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 244.

## III.7.1 — definicao recorrência de Bellman com árvore variável

Original de 77 páginas: 12.1.

Fonte editável: [tex/partes/artigo_2.tex:1706](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.Cvar`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 24.

## III.7.2 — teorema exatidão, existência e determinismo

Original de 77 páginas: 12.2.

Fonte editável: [tex/partes/artigo_2.tex:1732](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.variable_correctness`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 43.
- [`Artigo.Setup.variable_global`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 67.

## III.7.3 — corolario compatibilidade com a enumeração de formas

Original de 77 páginas: 12.3.

Fonte editável: [tex/partes/artigo_2.tex:1780](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.3`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.shape_enumeration`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 235.

## III.7.4 — algoritmo seletor exato por programação dinâmica

Original de 77 páginas: 12.4.

Fonte editável: [tex/partes/artigo_2.tex:1801](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:7.4`.

Estado: **Formalizado e compilado**. A recorrencia ou existencia matematica tem prova; falta implementar e certificar a execucao e a reconstrucao com comparacao exata. [11/11/2026] Tabela `varTable` (candidato folha + colagens, troca só se κ diminui), custo = `Cvar`, raiz = ótimo `Cstar` e representação κ-mínima de `variable_global`. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Artigo.Setup.variable_correctness`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 43.
- [`Artigo.Setup.variable_global`](../../../lean4/ambientes/artigo_2/RequestProject/DP.lean) — linha 67.
- [`Pendencias.DPprog.varTable_cost`](../../../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 316.
- [`Pendencias.DPprog.varRoot_spec`](../../../lean4/ambientes/artigo_2/Pendencias/ProgDin.lean) — linha 339.

## III.8.1 — teorema correção sob orçamento de folhas

Original de 77 páginas: 13.1.

Fonte editável: [tex/partes/artigo_2.tex:1835](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.leaf_budget`](../../../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 181.
- [`Artigo.Setup.leaf_budget_atMost`](../../../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 208.

## III.8.2 — teorema cálculo exato do melhor erro truncado

Original de 77 páginas: 13.2.

Fonte editável: [tex/partes/artigo_2.tex:1895](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.2`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.bottleneck_correctness`](../../../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 327.
- [`Artigo.Setup.bottleneck`](../../../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 361.

## III.8.3 — observacao interação entre profundidade e translação

Original de 77 páginas: 13.3.

Fonte editável: [tex/partes/artigo_2.tex:1929](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.3`.

Estado: **Observação editorial**. Observacao ou diagnostico do texto; nao e um teorema Lean autonomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.8.4 — corolario convergência para funções contínuas

Original de 77 páginas: 13.4.

Fonte editável: [tex/partes/artigo_2.tex:1944](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:8.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.uniform_convergence`](../../../lean4/ambientes/artigo_2/RequestProject/Budgets.lean) — linha 387.

## III.9.1 — teorema complexidade em número de estados

Original de 77 páginas: 14.1.

Fonte editável: [tex/partes/artigo_2.tex:1996](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.1`.

Estado: **Formalizado e compilado**. Prova cardinalidades das tabelas e transicoes; nao certifica tempo e memoria de um programa com execucao ligada a essas cardinalidades. [13/11/2026] III.9.1 formalizado com modelo de custo explicito: monad de contagem Tm, memoria densa Mem com dominio explicito e motor generico de preenchimento por niveis (runFrom_spec). Implementacao densa da recorrencia Cvar (denseRun: tabela (r,j,u,v) -> custo+apontador, niveis D..0, cada candidato w custa 2 leituras+1 soma+1 comparacao) e da recorrencia com orcamento Cb (denseRunB: chaves (r,j,u,v,n), pares (n_L,w)). Provado: (a) a tabela guarda exatamente Cvar/Cb (specE_cost, specEB_cost); (b) memoria exatamente S_D M^2 (resp. S_D N M^2) entradas; (c) operacoes <= 8 S_D M^3 (resp. <= 7 S_D N^2 M^3) com custos de folha pre-computados; (d) apontadores reconstroem uma representacao otima em Rset/RsetN (rebuild_spec, rebuildB_spec); (e) custo local calculado sobre P observacoes (leafInit, 4P+3 operacoes, valor exatamente Phi): inicializacao acrescenta 4 S_D P M^2 (variavel) e S_D M^2 (4P+3) (orcamento). Compilado e auditado (propext, Classical.choice, Quot.sound). Ressalvas: (1) a comparacao na tabela densa e feita sobre o custo; o desempate pela chave completa kappa (fluxo shortlex) nao esta no programa denso — o TeX conta comparacoes de chave como unitarias, de modo que a contagem coincide, e o seletor kappa-canonico continua sendo o de III.7.4 (varRoot_spec); a tabela densa devolve UMA representacao otima, nao necessariamente a kappa-minima; (2) o tempo de reconstrucao nao e contado (nao faz parte do enunciado); (3) modelo: leitura/escrita da tabela, soma e comparacao no corpo ordenado dos custos sao operacoes unitarias, conforme a secao do TeX; (4) as constantes explicitas 8 e 7 materializam O(.) para M>=1.

- [`Artigo.Setup.state_complexity`](../../../lean4/ambientes/artigo_2/RequestProject/Complexity.lean) — linha 89.
- [`Pendencias.DenseDP.state_complexity_dense`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1813.
- [`Pendencias.DenseDP.dense_variable_complexity`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 866.
- [`Pendencias.DenseDP.dense_budget_complexity`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1459.
- [`Pendencias.DenseDP.dense_variable_init`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1614.
- [`Pendencias.DenseDP.dense_budget_init`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean) — linha 1762.

## III.9.2 — observacao tabelas esparsas

Original de 77 páginas: 14.2.

Fonte editável: [tex/partes/artigo_2.tex:2033](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.2`.

Estado: **Observação editorial**. Observacao ou diagnostico do texto; nao e um teorema Lean autonomo.

Nenhuma declaração Lean associada na matriz recebida.

## III.9.3 — teorema cota grosseira de complexidade de bits

Original de 77 páginas: 14.3.

Fonte editável: [tex/partes/artigo_2.tex:2083](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.3`.

Estado: **Formalizado e compilado**. bit_complexity limita o tamanho dos custos racionais. As cotas de tempo e memoria em bits do artigo exigem semantica de execucao e custo de operacoes/desempate. [13/11/2026] III.9.3 formalizado sobre a implementacao densa de III.9.1 (leafInit agora testa admissibilidade antes de somar a perda; estado nao admissivel cobra 4P+3 como cota superior sem aritmetica sobre os dados). Provado: (1) crescimento — todo custo finito Cvar/Cb da recorrencia (entradas da tabela), toda soma de candidatos c_L+c_R (<= 4 B_cost+5 bits), todo candidato com penalidade (<= 16 B_cost+25 bits) e todo acumulador parcial da perda local (lossTm) tem comprimento em bits <= B_cost = Bcost S B L, a cota explicita de Setup.bit_complexity (2(P(5B+6clog H+2(k0+D)+9)+2B+2clog L+2)+3); (2) tempo em bits — numero de operacoes de III.9.1 (S_D M^2 (4M+6)+4 S_D P M^2 sem orcamento; S_D M^2 (4P+3)+S_D M^2 N (4NM+2) com orcamento) multiplicado por opBits = arith(b)+L+entryBits, com opBits <= cA MZ(b) clog(2b)+2L+b+idx, b=16 B_cost+25; (3) memoria em bits — dom.card * (B_cost+L+idx) exatamente S_D M^2 (resp. S_D N M^2) vezes. Multiplicacao escolar: schoolModel (MZ b = b^2). Compilado e auditado (propext, Classical.choice, Quot.sound). Ressalvas: (a) o custo de uma soma/comparacao/reducao de fracoes com operandos de b bits, <= cA MZ(b) log(2b), e HIPOTESE do modelo (BitModel.arith_le), como no TeX ("algoritmos inteiros usuais"); nao ha modelo de maquina em Lean; (b) o tempo em bits e o numero de operacoes unitarias vezes o custo-limite de uma operacao (argumento do TeX), nao uma simulacao bit a bit; (c) BitHyp assume B (bl dos dados/penalidades) e L (comprimento de fluxo das representacoes do catalogo, eq. stream-length) como no teorema bit_complexity; (d) os indices (idxBits = clog(S_D M+1)) aparecem explicitamente em vez de absorvidos; (e) vale a ressalva de III.9.1 sobre o desempate kappa (comparacoes de chave unitarias; empate shortlex custa L).

- [`Artigo.Setup.bit_complexity`](../../../lean4/ambientes/artigo_2/RequestProject/BitComplexity.lean) — linha 266.
- [`Pendencias.DenseDP.bit_complexity_dense`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 178.
- [`Pendencias.DenseDP.Cvar_bits`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 60.
- [`Pendencias.DenseDP.Cb_bits`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 68.
- [`Pendencias.DenseDP.candidate_bits`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 86.
- [`Pendencias.DenseDP.lossTm_acc_bits`](../../../lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean) — linha 124.

## III.9.4 — proposicao convergência dos mínimos penalizados

Original de 77 páginas: 14.4.

Fonte editável: [tex/partes/artigo_2.tex:2160](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.4`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.Setup.truncation_convergence`](../../../lean4/ambientes/artigo_2/RequestProject/Complexity.lean) — linha 200.

## III.9.5 — proposicao um seletor exato pode ser descontínuo

Original de 77 páginas: 14.5.

Fonte editável: [tex/partes/artigo_2.tex:2195](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:9.5`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.instability`](../../../lean4/ambientes/artigo_2/RequestProject/Complexity.lean) — linha 288.

## III.11.1 — teorema minimalidade exata do limiar

Original de 77 páginas: 16.1.

Fonte editável: [tex/partes/artigo_2.tex:2521](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:11.1`.

Estado: **Correspondência inspecionada**. 

- [`Artigo.threshold_optimality`](../../../lean4/ambientes/artigo_2/RequestProject/Dyadic.lean) — linha 337.
- [`Artigo.Edia_eq_sInf_nThr`](../../../lean4/ambientes/artigo_2/RequestProject/Dyadic.lean) — linha 363.

## III.11.2 — lema expansão local uniforme

Original de 77 páginas: 16.2.

Fonte editável: [tex/partes/artigo_2.tex:2581](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:11.2`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] f ∈ C²(K) via `ContDiffOn`; e_f(J), f″ e ω_{f″} unilaterais em K, por `extF` e lemas de congruência. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.local_asymptotic_error`](../../../lean4/ambientes/artigo_2/RequestProject/Dyadic.lean) — linha 455.
- [`Pendencias.local_asymptotic_error_on`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 229.

## III.11.3 — teorema envelope diádico universal e agudo

Original de 77 páginas: 16.3.

Fonte editável: [tex/partes/artigo_2.tex:2608](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:11.3`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] f ∈ C²(K) via `ContDiffOn`, com `curvIOn` (I(f) com f″ unilateral); as três formas (eventual, liminf/limsup, caso I(f)=0). Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.general_dyadic_envelope`](../../../lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean) — linha 519.
- [`Artigo.general_dyadic_envelope_zero`](../../../lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean) — linha 544.
- [`Artigo.general_dyadic_envelope_liminf`](../../../lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean) — linha 597.
- [`Pendencias.general_dyadic_envelope_on`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 240.
- [`Pendencias.general_dyadic_envelope_liminf_on`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 255.
- [`Pendencias.general_dyadic_envelope_zero_on`](../../../lean4/ambientes/artigo_2/Pendencias/Ponte.lean) — linha 270.

## III.12.1 — teorema lei exata e intervalo de acumulação

Original de 77 páginas: 17.1.

Fonte editável: [tex/partes/artigo_2.tex:2705](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.1`.

Estado: **Formalizado e compilado**. Resultados globais ou classe FRM usam regularidade C2 na reta. O artigo admite C2 no intervalo; transportar a extensao Fase3.extF e preservar valores, erros e curvatura. Conferir individualmente as hipoteses dos componentes citados. [11/11/2026] Mesmas seis conclusões de `quadratic_dyadic_constant` com `q ∈ C²(K)` (`ContDiffOn`) e `q″ ≡ κ` unilateral em K; usa `extF` e lemas de congruência (`Edia_congr`, `nThr_congr`). Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Artigo.quadratic_dyadic_constant`](../../../lean4/ambientes/artigo_2/RequestProject/DyadicExact.lean) — linha 58.
- [`Pendencias.quadratic_dyadic_constant_on`](../../../lean4/ambientes/artigo_2/Pendencias/LeiExata.lean) — linha 74.

## III.12.2 — teorema contagem exata em uma malha diádica base

Original de 77 páginas: 17.2.

Fonte editável: [tex/partes/artigo_2.tex:2813](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.2`.

Estado: **Generalização documentada**. O Lean dispensa C1: a igualdade com quadraticas nas celulas fechadas conserva compatibilidade nos extremos. O texto mantem C1; nao foi modificado.

- [`Artigo.piecewise_quadratic_count`](../../../lean4/ambientes/artigo_2/RequestProject/DyadicPhase.lean) — linha 238.

## III.12.3 — corolario fases sincronizadas

Original de 77 páginas: 17.3.

Fonte editável: [tex/partes/artigo_2.tex:2860](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.3`.

Estado: **Prova textual sincronizada**. A demonstracao Lean evita aplicar o envelope C2 global a uma funcao quadratica por partes que pode nao ser C2. Manter o enunciado e atualizar a demonstracao textual em etapa posterior. [13/11/2026] Demonstracao textual sincronizada com Artigo.synchronized_phases, preservando o enunciado e sem invocar o envelope C2 global para a funcao quadratica por partes. PDF recompilado nesta rodada.

- [`Artigo.synchronized_phases`](../../../lean4/ambientes/artigo_2/RequestProject/DyadicSync.lean) — linha 99.

## III.12.4 — observacao agudeza uniforme e comportamento pontual

Original de 77 páginas: 17.4.

Fonte editável: [tex/partes/artigo_2.tex:2967](../../../tex/partes/artigo_2.tex); rótulo `map:artigo_2:12.4`.

Estado: **Observação editorial**. Observacao ou diagnostico do texto; nao e um teorema Lean autonomo.

Nenhuma declaração Lean associada na matriz recebida.


## Cópias para leitura

`fontes_referenciados/` reúne cópias byte a byte dos módulos associados. Para compilar, use os ambientes completos em `../../ambientes/`, que preservam imports e dependências.
