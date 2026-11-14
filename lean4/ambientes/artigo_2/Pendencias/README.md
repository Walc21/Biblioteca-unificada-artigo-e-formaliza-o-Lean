# Pendencias — provas Lean que fecham lacunas do volume

Biblioteca `Pendencias` do ambiente `lean4/ambientes/artigo_2` (Lean/Mathlib 4.28.0), criada em 11/11/2026 (rodada 1: 12 itens; rodada 2: 12 itens aqui, mais I.6.3/I.6.4 em `base_integrada/PendenciasParte1/` e III.12.3 no TeX).
Não altera nenhum arquivo de `RequestProject/`; só importa dele.

```bash
cd lean4/ambientes/artigo_2
lake build Pendencias                         # compila tudo
lake env lean AuditoriaPendencias.lean        # imprime os axiomas (saída em axiomas_pendencias.log)
```

As declarações auditadas abaixo dependem apenas de `propext`, `Classical.choice`, `Quot.sound`. Nenhum `sorry`.

| Item | Arquivo | Declarações principais |
|---|---|---|
| V.21.1 | `Runge.lean` | `Runge.runge_majorant_sub`, `Runge.runge_majorant` (sem J ⊆ [-1,1]) |
| III.2.3 | `Interpolacao.lean` | `interp_remainder_C2On` |
| III.12.1 | `LeiExata.lean` | `quadratic_dyadic_constant_on` |
| III.3.15 | `Ponte.lean` | `derivative_control_Icc` |
| III.3.16 | `Ponte.lean` | `joint_budget_Icc`, `joint_all_N_Icc` |
| III.3.17 | `Ponte.lean` | `height_for_epsilon_Icc` |
| III.3.18 | `Ponte.lean` | `entropy_codebook_Icc` |
| III.11.2 | `Ponte.lean` | `local_asymptotic_error_on` |
| III.11.3 | `Ponte.lean` | `general_dyadic_envelope_on`, `_liminf_on`, `_zero_on` |
| IV.3.1 | `Agenda.lean` | `Agenda.schedule_nesting`, `Agenda.pErr_eq_min` |
| IV.4.5 | `Endpoint.lean` | `Agenda.c2_endpoint`, `Agenda.c2_endpoint_bits` |
| IV.4.6 | `Agenda.lean` | `Agenda.arithmetic_floor`, `Agenda.infDist_QH`, `Agenda.height_lower_bound` |
| IV.3.2 | `Taxa.lean` | `Agenda.dyadic_reduction`, `Agenda.dyadic_reduction_inf` |
| IV.3.3 | `Taxa.lean` | `Agenda.homogeneity_failure`, `Agenda.homogeneity_failure_inf` |
| IV.5.1 | `Marcada.lean` | `Marcada.marked_extends` (definições `MAtom`, `MTree`, `MAsm`, `MAsmNH`) |
| IV.5.3 | `Marcada.lean` | `Marcada.RedReLU.Hcan`, `Hcan_eq_maxHeight`, `canonShape_no_interior` |
| IV.5.7 | `Inversa.lean` | `Agenda.inverse_modulus`, `Agenda.inverse_besov` |
| IV.5.8 | `Inversa.lean` | `Agenda.raw_library_inverse(_inf)`, `Agenda.schedule_raw_inverse` |
| IV.5.9 | `Pente.lean` | `PenteGemini.critical_tent_comb` |
| IV.5.10 | `Inversa.lean` | `Agenda.universal_inverse` |
| III.3.12 | `Formatos.lean` | `coding_formats_comparison` |
| III.3.25 | `Enumeracao.lean` | `gen_eq_RepCat`, `enumSelect_eq_canon` (programa executável) |
| III.6.3 | `ProgDin.lean` | `DPprog.fixTable_cost`, `DPprog.fixRoot_spec` |
| III.7.4 | `ProgDin.lean` | `DPprog.varTable_cost`, `DPprog.varRoot_spec` |
| V.6.1 | `Arvores.lean` | `tree_rate_pow`, `tree_rate`, `tree_rationalization` |
| I.6.3, I.6.4 | `../../base_integrada/PendenciasParte1/Refinamento.lean` | `PendenciasParte1.certRefine`, `certified_refinement` (`lake build PendenciasParte1` em `base_integrada`) |
| III.12.3 | `tex/partes/artigo_2.tex` | demonstração textual reescrita seguindo `Artigo.synchronized_phases` |
| IV.4.1 | `Jackson.lean` | `Jackson.rational_jackson_height`, `Jackson.rational_jackson_uniform` |
| IV.4.2 | `Direta.lean` | `Jackson.direct_besov_height` |
| IV.4.3 | `Direta.lean` | `Jackson.uniform_besov_ball` |
| IV.5.12 | `Realizacao.lean` | `Jackson.regularized_jackson`, `Jackson.regularized_jackson_uniform` |
| IV.5.13 | `Realizacao.lean` | `Jackson.complete_besov_reversibility` |
| IV.5.14 | `Realizacao.lean` | `Jackson.architecture_stable_reversibility` |
| V.6.2 | `NosLivres.lean` | `NosLivres.free_knots` |
| V.6.3 | `BesovDireta.lean` | `Jackson.besov_direct`, `Jackson.besov_direct_whitney` |
| IV.5.4 (volta, enunciado corrigido) | `AlturaInversa.lean` | `AlturaInversa.Hcan_le`, `reverse_height_bit_bound`, `no_additive_constant_fix` |
| IV.5.4 (ida) | `FormaAncorada.lean`, `CodigoAncorado.lean` | `Ancorada.anchored_form`, `anchoredCodec_RT`, `anchored_length`, `direct_part` |
| IV.5.5 | `ReversaoQuantizada.lean` | `QuantIV55.quantized_approximate_reverse` (C = 320), `construct`, `Hcan_leQ`, `exists_nonflat`, `Rq_err` |
| IV.5.6 | `ReversaoProfunda.lean` | `DeepIV56.deep_functional_reverse`, `IsReLUNetwork.isPL`, `IsPL.relu`, `reduced_of_PL`, `regionCount_eq`, `sigma_abs_le` |
| III.9.1 | `ComplexidadeDensa.lean` | `DenseDP.state_complexity_dense`, `dense_variable_complexity`, `dense_budget_complexity`, `dense_variable_init`, `dense_budget_init`, `runFrom_spec`, `specE_cost`, `specEB_cost`, `rebuild_spec`, `rebuildB_spec` |
| III.9.3 | `ComplexidadeBits.lean` | `DenseDP.bit_complexity_dense`, `Cvar_bits`, `Cb_bits`, `candidate_bits`, `partial_loss_bits`, `lossTm_acc_bits` (usa `Setup.bit_complexity`) |
| IV.5.2 | `ReversaoOriginal.lean` | `Marcada.RealReLU.exact_shallow_reversal`, `original_realizable_iff` |
| auxiliar de IV.5.2 | `Canonica.lean` | `Marcada.canonShape_least`, `canonShape_unique_least`, `canonShape_independent_depth`, `canonShape_min_leaves` |
| auxiliar de IV.5.2 | `CanonicaContagem.lean` | `Marcada.canonShape_leaf_bounds` (cotas explicitas inferior e superior) |
| auxiliar de IV.5.2 | `ReversaoRacional.lean` | `Marcada.RedReLU.canonTree_representation_bounds` |
| auxiliar de IV.5.2 | `ReLUReal.lean` | `Marcada.RealReLU.not_differentiableAt_break` |
| auxiliar de IV.5.2 | `ReversaoNecessidade.lean` | `Marcada.RealReLU.parameters_necessary` |
| auxiliar de IV.5.2 | `MarcadaParticao.lean` | `Marcada.MTree.leavesAvoid_cuts`, `RedReLU.canonTree_shape` |
| auxiliar de IV.5.2 | `ReversaoExata.lean` | `Marcada.RealReLU.marked_realizable_iff`, `canonicalTree_spec`, `canonicalTree_unique_least` |
| auxiliar | `Extensao.lean` | `extF`, extensão C² e lemas de congruência usados nas provas acima |

## Ideia comum

`Extensao.lean` é um porte, sem mudança matemática, da extensão C² da Fase 3 (`Unified/Fase3/Extension.lean`):
para `f` com `ContDiffOn ℝ 2 f [α,β]`, `extF f α β` é C² na reta, coincide com `f` em `[α,β]` e tem segunda
derivada igual à unilateral de `f` lá. Os teoremas globais do `RequestProject` são aplicados a `extF f` e
transportados por lemas de congruência (as grandezas só olham valores no intervalo).

## Definições novas (escolhas de formalização)

* `FRMIcc R M` (`Ponte.lean`): a classe 𝓕_{R,M} do texto, C² só em [0,1], f″ unilateral nos extremos.
* `curvIOn` (`Ponte.lean`): I(f) com f″ unilateral em K.
* `Agenda.Sigma`, `Agenda.pErr`, `Agenda.QH`, `Agenda.rateInf`, `Agenda.H2`: objetos do Artigo 3, sobre
  K = [0,1] (o domínio de `Artigo.jointErr`), com erros em `ENNReal` como `jointErr`.
* IV.4.6, consequência: enunciada para N ≥ 1.
* `rateQ`, `dterm`, `dyadQ`, `dyadInf` (`Taxa.lean`): funcional de taxa para q < ∞ e normas diádicas.
* `omega2`, `BesovInf`, `BesovQ`, `realN`, `eG`, `LipGrowth`, `Hsk` (`Inversa.lean`): ω₂ e Besov pela norma diádica do texto em [0,1]; `Hsk s κ` é H_{s,κ} com C_K = 8.
* `MAtom`, `MTree`, `canonShape`, `RedReLU`, `Hcan` (`Marcada.lean`).
* `tentTree`, `combFun`, `combFrom` (`Pente.lean`, pente de tendas na biblioteca original).
* `famTree` (`Formatos.lean`); `gen`, `select`, `enumSelect` (`Enumeracao.lean`, computáveis); `fixTable`, `varTable`, `kselect` (`ProgDin.lean`); `realize`, `qv`, `shapeL` (`Arvores.lean`).
* σ_N^dia do complemento é o `Edia` existente (ínfimo de `treeErr`).
* Teste executável de III.3.25 registrado em `axiomas_pendencias.log` (`#eval`).

## IV.5.4 — volta corrigida e ida formalizada

A cota impressa `log₂ H_can ≤ C[M log(2W)+D+log(M+1)]` é falsa (`R(x)=x`: `H_can=2`, lado direito 0;
`R(x)=Wx`: `H_can ≥ W`). `AlturaInversa.lean` demonstra a forma correta, sem `sorry` e só com
`propext`, `Classical.choice`, `Quot.sound`:
`H_can(R) ≤ 2^(D+1)(M+2)W^(M+3)` (`Hcan_le`) e
`log₂ H_can ≤ 5[(M+1)log₂(2W)+D+log₂(M+1)]` (`reverse_height_bit_bound`),
sob as hipóteses do TeX (`Hip`: alturas `≤ W`, quebras diádicas em `(0,1)`, profundidade `≤ D`).
`no_additive_constant_fix` mostra que nenhum termo aditivo conserta o enunciado antigo.
Auditoria de axiomas: `AuditoriaPendencias.lean` (em `lean4/ambientes/artigo_2`).

**Ida (forma ancorada e comprimento).** `FormaAncorada.lean` prova `anchored_form`: toda
`g ∈ MAsmNH N H` se escreve em `[0,1]` como `ys + s0 (x - xs) + ∑ a_j ρ(x - t_j)` com
`xs = 2^-(k+1)` (centro da folha mais à esquerda, `g xs = ys`), `M ≤ N-1` hinges,
`t_j` estritamente crescentes em `(0,1)` e `a_j ≠ 0`; `ht ys ≤ H`, `ht s0 ≤ H`,
toda inclinação parcial `σ_i` tem altura `≤ H`, cada salto `ht a_j ≤ 2H²`, e cada `t_j = m/2^k`
com `k+1 ≤ H`, `|m|+1 ≤ H`. A base é a forma ReLU `eval_relu_form` sobre folhas contíguas de
`MTree` (a inclinação pode ser nula; hinges de salto zero são descartados em `redPairs`).
`CodigoAncorado.lean` define `anchoredCodec` (`γ(M+1)` + campos; `dyadCodec` para `xs` e `t_j`,
`ratCodec` para os demais), prova decodificação exata `anchoredCodec_RT` (logo prefix-free,
`anchored_prefix_free`) e `anchored_length`: `|C(A)| ≤ 40 · N · ⌊log₂ 2H⌋`. O teorema `direct_part`
junta tudo (também com `logb`). Auditoria de axiomas: `AuditoriaPendencias.lean` (somente `propext`, `Classical.choice`, `Quot.sound`).
Ressalva: a "forma reduzida" é a estrutura `Anchored` (não o tipo `RealReLU`); não há ponte
explícita `Anchored → RealReLU`.

## Correspondencia semantica de IV.5.2

`RealReLU M` admite parametros reais, inclusive `M=0`; `Reduced` reproduz
as quebras estritamente crescentes em `(0,1)` e os saltos nao nulos do TeX.
`MarkedRealizable` e `OriginalRealizable` comparam funcoes em `[0,1]`, sem impor
valores externos ao dominio do enunciado. `Arithmetic` e a conclusao de racionalidade
dos coeficientes e de diadicidade das quebras. O teorema combinado inclui a
minimalidade e unicidade da forma da arvore, as duas cotas explicitas de folhas e
a equivalencia com todas as inclinacoes locais nao nulas para a biblioteca original.
