# Reauditoria semântica das correspondências herdadas

Escopo: as 97 entradas do mapa `mapas/MAPA_TEX_LEAN.md` marcadas como **Correspondência inspecionada** (77) ou **Integrado à base** (20). Para cada uma, comparei o enunciado do texto (na linha indicada pelo mapa, em `tex/partes/`) com a assinatura da declaração Lean apontada.

## Método e limites (leia antes da tabela)

- **Quem avaliou:** uma IA (Claude), sem revisão humana. Por seu pedido de sigilo, nenhum enunciado foi enviado a outro serviço nem a revisores. Os vereditos são leitura da IA e devem ser tratados como tais.
- **O que foi comparado:** hipóteses, conclusões e objetos definidos, pelas assinaturas Lean lidas no código. As **demonstrações** Lean não foram relidas, só os enunciados.
- **Entradas «Integrado à base» (20):** o enunciado Lean está na base integrada e a ponte com `Montagens`/`Artigo` é uma equivalência (`normalization_*`, `SemanticBridge.*`). Verifiquei que a equivalência existe e tem o enunciado certo, mas **não** li as provas dessas equivalências.
- **Compilação:** nesta rodada compilei `lean4/ambientes/artigo_2` (`lake build Pendencias`). Os ambientes `parte_1` e `base_integrada` não foram recompilados aqui.
- **Fiel com ressalva:** a conclusão do texto está em Lean, mas falta algo (uma cláusula, uma forma explícita, uma hipótese que aparece só no tipo). Não é divergência de conteúdo.
- **Divergência:** nenhuma foi encontrada nas 97 entradas.

## Resumo

- Fiel: **84**
- Fiel com ressalva: **13**
- Divergência: **0**
- Total: **97** (77 inspecionadas + 20 integradas)

## Ressalvas que valem para o artigo

- **III.3.2:** a constante `288/π⁴` foi **verificada numericamente**: `|Library_H|/H⁶` converge para `288/π⁴ ≈ 2,9566` (razão 1,0033 em H = 512; script `verificacao/constante_iii32.py`), e a contagem bate com o Lean para H = 2..5. A **prova formal** da assintótica (que exige a contagem de pares coprimos) **não foi feita**.
- **III.3.7:** as funções `GammaSharp` e `nSharp` são executáveis (compiladas sem `noncomputable`; testadas para n < 40, com `nSharp(GammaSharp n) = n`), mas a prova formal de `Computable` nos dois sentidos **não foi feita**.
- **I.6.1:** formalizado depois (`lemma61_exp_rational`, `lemma61_enclosures`): as rotinas racionais de exp, sin e cos contêm as funções, com as cotas (37) e (38).
- **I.6.2:** a regra de falha foi formalizada depois (`boundSecondDerivative_fail_iff`): a rotina devolve `none` exatamente quando algum pedaço após `d` bissecções tem um denominador cujo intervalo contém 0.
- **Cláusulas de forma** (I.2.1, I.2.2, I.3.3, I.4.1, I.4.2, II.2.5, II.7.1, III.2.2, III.3.4, III.3.20): são formulações equivalentes ou mais gerais, mas algumas cláusulas do texto (inversas explícitas, não degenerescência do intervalo, injetividade de uma chave, invariante `ℓ ≥ H − O(1)`) não aparecem como teoremas separados.
- **Hipóteses mais gerais no Lean** (por exemplo, `H ≥ 2` não exigido em II.6.2; `m₀ ∈ ℕ` em vez de `m₀ ≥ 0` em III.4.5; `∀ (u,v) ∈ ℚ²` em III.7.2): implicam o enunciado do texto.

## Tabela

| Item | Enunciado (título) | Tipo original | Veredito | Declarações Lean | Observação |
|---|---|---|---|---|---|
| I.2.1 | lema pareamento e cota | inspecionado | Fiel com ressalva | `Fase3.cpair_bijective`, `Fase3.cdiag_eq_floor`, `Fase3.cpair_le` | inversa explícita só parcialmente (w via cdiag_eq_floor; v,u não enunciados) |
| I.2.2 | lema | inspecionado | Fiel com ressalva | `Fase3.zEnum_bijective`, `Fase3.zInv_le` | bijetividade e cota ok; fórmula da inversa Z^{-1} não enunciada |
| I.2.3 | lema contagem por altura | inspecionado | Fiel | `Fase3.card_QH_le`, `Fase3.card_QH_ge` | Lean dá cota inferior sem H0 (mais forte); c1=1/4 coerente |
| I.2.4 | lema posto por altura | inspecionado | Fiel | `Fase3.Qenum_bijective`, `Fase3.QstarEnum_bijective`, `Fase3.rankQ_lt` | rankQ = card(predQ) é a posição na enumeração; Qenum é a inversa (lidas nesta rodada) |
| I.2.5 | lema | inspecionado | Fiel | `Fase3.calkinWilf_two_pow` | calkinWilf_two_pow com 1≤q |
| I.3.1 | lema estrutura diádica | inspecionado | Fiel | `Fase3.cellOwn_partition`, `Fase3.cell_refine`, `Fase3.cell_length` | partição, refinamento, comprimento, bijeção sobre D_mid e densidade |
| I.3.2 | lema | inspecionado | Fiel | `Fase3.decode4_bijective` | decode4 é a inversa explícita (cunpair), conferida nesta rodada |
| I.3.3 | definição gerador e biblioteca | inspecionado | Fiel com ressalva | `Fase3.gen`, `Fase3.library` | nao-degenerescência do intervalo fora do tipo de Γ |
| I.3.4 | lema validade espacial exata | inspecionado | Fiel | `Fase3.preimageInterval_eq` | preimageInterval_eq |
| I.3.5 | teorema unicidade do endereço | inspecionado | Fiel | `Fase3.gen_injective` | gen_injective |
| I.3.6 | teorema dicionário de jatos racionais | inspecionado | Fiel | `Fase3.jet_bijective`, `Fase3.jet_dense` | jet_bijective (injetiva e imagem exata) e jet_dense |
| I.4.1 | definição montagem contínua | integrado | Fiel com ressalva | `Fase3.IsAssembly`, `Dyadic.Lib.IsAssemblyRep`, `Dyadic.Lib.Asm` | IsAssembly exige ContinuousOn, cobertura, endereços; «inclinação não nula» vem do tipo do endereço (ℕ), não é enunciado; equivalência com Asm provada (fase3_assembly_iff_consolidated) |
| I.4.2 | teorema densidade das montagens | inspecionado | Fiel com ressalva | `Fase3.assembly_dense` | assembly_dense não enuncia «peças em L com inclinação não nula» (implícito no tipo do endereço) |
| I.4.4 | proposição parâmetros e altura | inspecionado | Fiel | `Dyadic.Lib.relu_parameters_height` | relu_parameters_height: 2N racionais e cotas 2^{H+1}H²; Lean com H geral (mais forte) |
| I.4.5 | proposição pertencimento e aderência | inspecionado | Fiel | `Dyadic.Lib.taylor_jet` | taylor_jet: átomo exato e aproximação com cotas (28)-(29) |
| I.5.1 | teorema cota aguda e limite | inspecionado | Fiel | `Fase3.errP_le`, `Fase3.tendsto_errP`, `Fase3.exists_assembly_rate` | errP_le, tendsto_errP, exists_assembly_rate |
| I.5.2 | corolário preservação da constante | inspecionado | Fiel | `Fase3.exists_assembly_seq_constant` | exists_assembly_seq_constant |
| I.6.1 | restos transcendentais com extremos racionais | inspecionado | Fiel | `Fase3.lemma61_exp_rational`, `Fase3.lemma61_enclosures`, `Fase3.expQ_sound`, `Fase3.expEncl_mem`, `Fase3.sinEncl_mem`, `Fase3.cosEncl_mem`, `Fase3.exp_sub_expPoly_bounds`, `Fase3.sin_cos_lagrange` | rotinas racionais de exp, sin e cos com inclusão e cotas (37)-(38) (`Unified/Fase3/IntervalArith.lean`, `Unified/Fase3/Lemma61.lean`, acrescentado nesta rodada) |
| I.6.2 | proposição correção do majorante intervalar | inspecionado | Fiel | `Fase3.boundSecondDerivative_correct`, `Fase3.Mint_ge_supNorm`, `Fase3.boundSecondDerivative_fail_iff` | correção sob sucesso e regra de falha exata (`Unified/Fase3/IntervalFailure.lean`, acrescentada nesta rodada) |
| I.6.5 | proposição calibração exata para curvatura constante | inspecionado | Fiel | `Fase3.calibration` | calibration: N=2^{rcal}, patamar, liminf 1/√8 e limsup 1/√2 (rcal = max(0,⌈log₄(A/ε)⌉)) |
| I.6.6 | observação diferença segunda e erro no centro | inspecionado | Fiel | `Fase3.center_error_eq`, `Fase3.cube_example` | center_error_eq e cube_example (P_J x^3 = x, norma 2/(3√3)) |
| II.2.1 | definição racional reduzido e altura | inspecionado | Fiel | `Montagens.ht`, `Montagens.ht_props` | ht = max(|num|,den) e ht_props |
| II.2.2 | definição célula e funções de seus extremos | inspecionado | Fiel | `Montagens.Cell`, `Montagens.LQ`, `Montagens.RQ` | Cell, LQ/RQ/XQ, J, O, P, Dy |
| II.2.3 | lema geometria elementar | inspecionado | Fiel | `Montagens.geometry` | geometry (inclui J(c)=J(d) ⇒ c=d) |
| II.2.4 | definição átomo e suas projeções | integrado | Fiel com ressalva | `Montagens.Atom`, `Montagens.Atom.height`, `SemanticBridge.normalizationAtomEquiv` | estrutura Atom e equivalência com Dyadic.Lib.Atom (integrado); campos conferidos só na equivalência |
| II.2.5 | lema formas da reta | integrado | Fiel com ressalva | `Montagens.line_forms`, `SemanticBridge.normalization_atom_line` | line_forms cobre ℓ_a, ℓ_a(X_a)=y, continuidade, b≠0; a unicidade por dados (C,y,s) é a igualdade por campos, não enunciada |
| II.3.1 | definição campos dos contratos | integrado | Fiel | `Montagens.Sep`, `Montagens.Cover`, `Montagens.MatchK` | definições Sep, Cover, MatchK, Agree, LocalRep, StrongRep; equivalências em NormalizationContracts |
| II.3.2 | definição atividade e filtro | inspecionado | Fiel | `Montagens.Active`, `Montagens.NormK` | Active = O_a ∩ K° ≠ ∅; NormK = filter |
| II.3.3 | lema critério exato de atividade | inspecionado | Fiel | `Montagens.active_iff` | active_iff |
| II.3.4 | lema intervalos separados | inspecionado | Fiel | `Montagens.separated_of_disjoint`, `Montagens.separated_inter` | separated_of_disjoint e separated_inter (com ponto comum único) |
| II.3.5 | teorema normalização | integrado | Fiel | `Montagens.normalization`, `Montagens.normalizationG`, `SemanticBridge.normalizeAtoms_strong` | normalization e normalizationG (cinco conclusões); versão tipada normalizeAtoms_* |
| II.3.6 | corolário equivalência local e consolidada | integrado | Fiel | `Montagens.Aloc_eq_Astr`, `SemanticBridge.local_asm_eq_strong` | Aloc_eq_Astr |
| II.4.1 | definição pareamento e descompactação | inspecionado | Fiel | `Montagens.T`, `Montagens.pair`, `Montagens.unpair` | T, pair, unpair |
| II.4.2 | lema inversas do pareamento | integrado | Fiel | `Montagens.pair_props`, `SemanticBridge.normalization_pair`, `SemanticBridge.normalization_unpack2` | pair_props (todas as identidades e a fórmula de w) |
| II.4.3 | definição enumeração dos inteiros | integrado | Fiel | `Montagens.Zenc`, `Montagens.Zinv`, `Montagens.Zenc_Zinv` | Zenc, Zinv e inversas |
| II.4.4 | definição ordens e postos dos racionais | inspecionado | Fiel | `Montagens.QH`, `Montagens.prec`, `Montagens.Pred` | QH, mem_QH (= {ht ≤ H}), rank = card Pred |
| II.4.5 | lema postos e enumerações inversas | integrado | Fiel | `Montagens.prec_coincide`, `Montagens.rank_bijective`, `Montagens.rankStar_bijective` | prec_coincide, rank_bijective, rankStar_bijective (Q_i = inversa, consequência da bijetividade) |
| II.4.6 | definição codificadores concretos de átomos | inspecionado | Fiel | `Montagens.enc`, `Montagens.dec`, `Montagens.tau` | enc, dec, tau (definições; coerência verificada em II.4.7) |
| II.4.7 | lema contrato completo de endereçamento | integrado | Fiel | `Montagens.codec`, `Montagens.tau_props`, `SemanticBridge.normalization_ofFase2` | codec e tau_props |
| II.5.1 | definição testemunha por células endereçadas | inspecionado | Fiel | `Montagens.CellRep`, `Montagens.CellRepG` | CellRep/CellRepG (definições; ligação com StrongRep via base integrada) |
| II.5.2 | definição continuidade no domínio e restrição | integrado | Fiel | `Montagens.ContOn`, `Montagens.Res`, `Montagens.ResImage` | ContOn, Res, ResImage; normalization_contOn_iff ⇔ ContinuousOn |
| II.5.3 | definição as três classes tipadas | integrado | Fiel | `Montagens.B2`, `Montagens.B3`, `Montagens.Bcon` | B2, B3, Bcon e equivalências (normalization_B2/B3/Bcon_iff) |
| II.5.4 | lema conversões explícitas das testemunhas | inspecionado | Fiel | `Montagens.cellsToAtoms_spec`, `Montagens.cellsToAtoms_specG`, `Montagens.atomsToCells_spec` | cellsToAtoms_spec(G), atomsToCells_spec(G) (cardinalidade, peças, endereços) |
| II.5.5 | definição extensão contínua por projeção | inspecionado | Fiel | `Montagens.projK`, `Montagens.E0`, `Montagens.Res_E0` | projK, E0, Res_E0 |
| II.5.6 | teorema equivalência extensional tipada | integrado | Fiel | `Montagens.bridge`, `Montagens.B3_eq_Bcon`, `SemanticBridge.fase3_assembly_iff_consolidated` | bridge (quatro igualdades), B3_eq_Bcon |
| II.6.1 | definição orçamento da testemunha | integrado | Fiel | `Montagens.Budget`, `Montagens.AlocNH`, `Montagens.AstrNH` | Budget e AlocNH/AstrNH (Lean sem a hipótese H≥2 do texto: mais geral) |
| II.6.2 | teorema igualdade sob os mesmos recursos | integrado | Fiel | `Montagens.AlocNH_eq_AstrNH`, `SemanticBridge.local_budgeted_eq_strong`, `SemanticBridge.normalization_typed_budget_iff` | AlocNH_eq_AstrNH e local_budgeted_eq_strong (Lean sem H≥2: mais geral) |
| II.6.3 | definição distância uniforme e ínfimo | integrado | Fiel | `Montagens.dK`, `Montagens.Err`, `Montagens.dK_isMax` | dK (sup = max em compacto), dK_isMax, Err, Err_empty, normalization_distance |
| II.6.4 | corolário igualdade dos erros e de suas condições de altura | integrado | Fiel | `Montagens.errors_eq`, `Montagens.heights_eq`, `SemanticBridge.normalization_Econ_eq_jointError` | errors_eq, heights_eq (conjuntos e ínfimos), local_height_conditions_eq |
| II.6.5 | proposição testemunhas já ativas | inspecionado | Fiel | `Montagens.norm_fixed_of_active`, `Montagens.norm_fixed_of_subset` | norm_fixed_of_active, norm_fixed_of_subset |
| II.7.1 | definição ordem auxiliar total dos átomos | inspecionado | Fiel com ressalva | `Montagens.zeta`, `Montagens.sortAtoms` | zeta (chave lexicográfica dos 5 campos) e sortAtoms; a injetividade da chave não é enunciada separadamente |
| II.7.2 | lema propriedades da lista ordenada | inspecionado | Fiel | `Montagens.sortAtoms_props` | sortAtoms_props e sortAtoms_left_strict (sob Sep) |
| II.7.3 | definição tipo dos dados de cadeia | inspecionado | Fiel | `Montagens.NormChain` | NormChain: campos (injetiva, imagem, t crescente, extremos LQ/RQ) e extras de fronteira |
| II.7.4 | teorema construção determinada da cadeia | inspecionado | Fiel | `Montagens.chainOf`, `Montagens.chainOf_nodes_dyadic` | chainOf (t por chainNodes; t0 = L(a0), t_{j+1} = R(a_j)) |
| II.8.1 | definição parâmetros e funções parciais | inspecionado | Fiel | `Montagens.NormChain.Fpart`, `Montagens.NormChain.Rext` | Fpart (recursão F_0, F_{r+1}) e Rext; ρ = relu |
| II.8.2 | lema expansão da recursão | inspecionado | Fiel | `Montagens.NormChain.Rext_sum`, `Montagens.NormChain.Rext_anchor`, `Montagens.NormChain.Rext_of_M_eq_one` | Rext_sum e Rext_anchor |
| II.8.3 | lema identidade de duas retas incidentes | inspecionado | Fiel | `Montagens.NormChain.incident` | incident |
| II.8.4 | teorema correção da extensão | integrado | Fiel | `Montagens.NormChain.extension`, `SemanticBridge.fase2_relu_extension_agrees`, `SemanticBridge.fase2_relu_extension_is_consolidated` | extension: contínua, peças em [t_j,t_{j+1}], agrega K, caudas, nós em K°∩D (Lean inclui cláusula extra em t_1) |
| II.8.5 | lema unicidade de uma reta a partir de dois pontos | inspecionado | Fiel | `Montagens.affine_eq_of_two_points` | affine_eq_of_two_points |
| II.8.6 | teorema independência da testemunha | integrado | Fiel | `Montagens.Rext_unique`, `SemanticBridge.fase2_relu_extension_eq` | Rext_unique |
| II.8.7 | definição operador de extensão das montagens | integrado | Fiel | `Montagens.extOp`, `Montagens.Res_extOp`, `SemanticBridge.fase2ReLUExtension` | extOp, Res_extOp (e fase2ReLUExtension na base integrada) |
| III.2.1 | lema indexação elementar | inspecionado | Fiel | `Artigo.cantorPair_bijective`, `Artigo.cantorPair_le`, `Artigo.Zenum_bijective` | cantorPair, Zenum, Zinv_le, card_QH_le/ge, rank_lt_three_sq |
| III.2.2 | definição átomos e montagens | inspecionado | Fiel com ressalva | `Artigo.Atom`, `Artigo.Atom.interface_injective`, `Artigo.Atom.addr_injective` | Atom, interface_injective, addr_injective; endereço explícito π(...) e convenção semiaberta de posse não aparecem como teoremas |
| III.3.1 | teorema cota polinomial do endereço | inspecionado | Fiel | `Artigo.index_bound` | index_bound (H^8 e log2) |
| III.3.2 | lema cardinalidade das cascas de altura | inspecionado | Fiel com ressalva | `Artigo.card_LH_le`, `Artigo.card_LH_ge`, `Artigo.card_LH_theta` | card_LH_le, card_LH_ge, card_LH_theta (Θ(H⁶)); a assintótica ∼(288/π⁴)H⁶ NÃO está formalizada |
| III.3.3 | proposição ordem exata do pior endereço aritmético | inspecionado | Fiel | `Artigo.MGamma_theta`, `Artigo.MGamma_bits` | MGamma_theta e MGamma_bits |
| III.3.4 | teorema cota minimax relativa ao calibre | inspecionado | Fiel com ressalva | `Artigo.address_lower` | address_lower (forma assintótica); o pigeonhole exato max A ≥ |Library_H|−1 não é enunciado separadamente |
| III.3.6 | definição enumeração por altura da biblioteca | inspecionado | Fiel | `Artigo.nSharp`, `Artigo.GammaSharp` | nSharp, GammaSharp; atomKey = [k, Z⁻¹(m), rankQ y, rankQs s] com injetividade |
| III.3.7 | teorema endereço minimax exato para a exaustão | inspecionado | Fiel com ressalva | `Artigo.sharp_optimal` | sharp_optimal (bijeção, inversas, max = |L_H|−1 ≤ 18H⁶−1, minimax); a computabilidade nos dois sentidos NÃO está formalizada (sem Computable/Primrec) |
| III.3.9 | teorema serialização condicionada de montagens | inspecionado | Fiel | `Artigo.assembly_serialization`, `Artigo.assembly_serialization_Gamma` | assembly_serialization (decodificável, comprimento com clog) e a versão Γ (8 log₂H + O(1)) |
| III.3.11 | lema cálculo elementar de alturas | inspecionado | Fiel | `Artigo.assembly_height_arith` | ht_add_le, ht_sub_le, ht_mul_le e assembly_height_arith (2H², H2^H, 2^{H+1}H²) |
| III.3.13 | definição erro conjunto número--altura | inspecionado | Fiel | `Artigo.jointErr`, `Artigo.heightFor` | jointErr e heightFor (definições) |
| III.3.14 | proposição monotonicidade dos dois orçamentos | inspecionado | Fiel | `Artigo.jointErr_succ_N_le`, `Artigo.jointErr_succ_H_le`, `Artigo.jointErr_tendsto` | jointErr_succ_N_le, jointErr_succ_H_le, jointErr_tendsto (antitone, limite leafErr); leafErr não lido |
| III.3.19 | definição recursos de um codec | inspecionado | Fiel | `Artigo.EpsCodec`, `Artigo.Ldec`, `Artigo.Lglobal` | EpsCodec, Ldec, Lglobal (clog₂ do cardinal), Lfolhas |
| III.3.20 | proposição limite informacional para representação decodificável | inspecionado | Fiel com ressalva | `Artigo.description_lower`, `Artigo.complexity_chain` | description_lower (comprimento fixo, prefix-free, Ldec ≥ ⌈H⌉); a forma invariante ℓ ≥ H − O(1) não formalizada |
| III.3.21 | proposição | inspecionado | Fiel | `Artigo.no_minimizer` | no_minimizer: ínfimo 0 e nenhum átomo o realiza (Lean com «∀ átomo» e cellIcc no lugar de x∈I_n^x, equivalente por III.3.4) |
| III.3.22 | definição catálogo truncado | inspecionado | Fiel | `Artigo.RepCat`, `Artigo.SigmaCat` | RepCat/SigmaCat via allTrees H D (folhas em LH H, profundidade D) e WF |
| III.3.23 | teorema finitude, existência e desempate canônico | inspecionado | Fiel | `Artigo.finite_catalog_minimizer` | finite_catalog_minimizer (cotas com Tshape: T_0=1, T_{d+1}=1+T_d²; canKey injetiva) |
| III.3.24 | proposição consistência sob truncagem | inspecionado | Fiel | `Artigo.catalog_consistency` | catalog_consistency (aninhamento, minVal monótono, estabilização canônica) |
| III.4.1 | definição pares de fronteira admissíveis | inspecionado | Fiel | `Artigo.IsAdmPair`, `Artigo.PH` | IsAdmPair: u≠v, ht((u+v)/2)≤H, ht(2^k(v−u))≤H, k+1≤H, |m|+1≤H (idêntico) |
| III.4.2 | proposição dicionário exato de fronteiras | inspecionado | Fiel | `Artigo.endpoint_dictionary` | endpoint_dictionary (BijOn e contagem q_H(q_H−1) ou 0) |
| III.4.3 | definição alfabeto de fronteira | inspecionado | Fiel | `Artigo.Valphabet` | Valphabet (definição) |
| III.4.4 | lema finitude e suficiência | inspecionado | Fiel | `Artigo.value_alphabet` | value_alphabet: finitude, suficiência e as quatro cotas (2S_D q(q−1), 2|L_H|, 18 S_D H⁴, 36 H⁶) |
| III.4.5 | proposição células vazias e refinamento uniforme máximo | inspecionado | Fiel | `Artigo.translation_obstruction` | translation_obstruction: não vazio ⇔ (k0+r+1≤H ∧ 2^r m0+j+1≤H); N_r com max{0,·} via ℕ; uniforme; equivalência logarítmica (m0 ∈ ℕ em vez de m0≥0) |
| III.5.1 | lema decodificação e aditividade | inspecionado | Fiel | `Artigo.recursive_stream` | recursive_stream: prefix-free, injetiva, comprimentos (folha e nó) |
| III.5.2 | lema compatibilidade do desempate com a colagem | inspecionado | Fiel | `Artigo.tie_concatenation` | tie_concatenation (monotonia da chave na colagem) |
| III.6.1 | definição recorrência para árvore fixa | inspecionado | Fiel | `Artigo.Setup.Cfix` | Cfix (folha Φ; nó com λbits+λsplit+min_w) |
| III.6.2 | teorema correção para árvore fixa | inspecionado | Fiel | `Artigo.Setup.fixed_correctness`, `Artigo.Setup.fixed_global` | fixed_correctness e fixed_global (com unicidade canônica) |
| III.7.1 | definição recorrência de Bellman com árvore variável | inspecionado | Fiel | `Artigo.Setup.Cvar` | Cvar (base d=0; min(Φ, …) para d+1) |
| III.7.2 | teorema exatidão, existência e determinismo | inspecionado | Fiel | `Artigo.Setup.variable_correctness`, `Artigo.Setup.variable_global` | variable_correctness (Lean para todo (u,v)∈ℚ², mais geral) e variable_global (finitude e unicidade canônica sob HK ≤ H) |
| III.7.3 | corolário compatibilidade com a enumeração de formas | inspecionado | Fiel | `Artigo.Setup.shape_enumeration` | shape_enumeration |
| III.8.1 | teorema correção sob orçamento de folhas | inspecionado | Fiel | `Artigo.Setup.leaf_budget`, `Artigo.Setup.leaf_budget_atMost` | leaf_budget e leaf_budget_atMost |
| III.8.2 | teorema cálculo exato do melhor erro truncado | inspecionado | Fiel | `Artigo.Setup.bottleneck_correctness`, `Artigo.Setup.bottleneck` | bottleneck (min sobre n ≤ min(N,2^D)) e a cláusula de profundidade inativa |
| III.8.4 | corolário convergência para funções contínuas | inspecionado | Fiel | `Artigo.uniform_convergence` | uniform_convergence (Lean para toda sequência → ∞, mais geral) |
| III.9.4 | proposição convergência dos mínimos penalizados | inspecionado | Fiel | `Artigo.Setup.truncation_convergence` | truncation_convergence (monotonia, ínfimo, convergência e estabilização do seletor) |
| III.9.5 | proposição um seletor exato pode ser descontínuo | inspecionado | Fiel | `Artigo.instability` | instability: qualquer seletor de custo mínimo é descontínuo em 0 na norma uniforme |
| III.11.1 | teorema minimalidade exata do limiar | inspecionado | Fiel | `Artigo.threshold_optimality`, `Artigo.Edia_eq_sInf_nThr` | threshold_optimality e Edia_eq_sInf_nThr (texto já corrigido para N ≥ 1) |

## Efeito sobre o mapa

O mapa mantém o estado original de cada entrada; esta reauditoria acrescenta o veredito acima. Ela **não** muda o número de provas formais nem fecha as ressalvas listadas.
