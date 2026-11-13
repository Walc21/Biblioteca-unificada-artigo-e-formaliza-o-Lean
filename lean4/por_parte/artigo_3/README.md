# Parte IV — Agendas de altura e teoria direta--inversa

Os módulos executáveis ficam em `../../ambientes/`. Este diretório contém o índice da parte, sem mover os módulos e quebrar imports.

## IV.3.1 — proposicao aninhamento da agenda

Original de 77 páginas: 18.1.

Fonte editável: [tex/partes/artigo_3.tex:81](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.1`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] Definições `Sigma`, `pErr` formalizadas sobre K=[0,1] (domínio de `jointErr`); inclusão, monotonia, cota por ‖f‖ e atingimento do ínfimo (catálogo finito), além da fórmula min{‖f‖, E_{N,H(N)}}. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Agenda.schedule_nesting`](../../../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 67.
- [`Pendencias.Agenda.pErr_eq_min`](../../../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 44.

## IV.3.2 — teorema redução exata às escalas diádicas

Original de 77 páginas: 18.2.

Fonte editável: [tex/partes/artigo_3.tex:133](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.2`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] Funcional `rateQ` (q<∞) e `rateInf` (q=∞); constantes `C = 2^α` e `K = (1+2·(2^α)^q)^{1/q}` só dependem de α, q. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.dyadic_reduction`](../../../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 142.
- [`Pendencias.Agenda.dyadic_reduction_inf`](../../../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 181.

## IV.3.3 — proposicao falha exata de homogeneidade

Original de 77 páginas: 18.3.

Fonte editável: [tex/partes/artigo_3.tex:166](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.3`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] Com H(1) ≥ 2: 𝔞(x) = 0 e 𝔞(√2 x) > 0, para 0<q<∞ e q=∞ (irracionalidade de √2). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.homogeneity_failure`](../../../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 253.
- [`Pendencias.Agenda.homogeneity_failure_inf`](../../../lean4/ambientes/artigo_2/Pendencias/Taxa.lean) — linha 269.

## IV.3.4 — observacao estrutura aritmética do funcional

Original de 77 páginas: 18.4.

Fonte editável: [tex/partes/artigo_3.tex:197](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:3.4`.

Estado: **Observação editorial**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.4.1 — lema Jackson racional com altura explícita

Original de 77 páginas: 19.1.

Fonte editável: [tex/partes/artigo_3.tex:277](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.1`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Jackson racional em raiz diadica geral, constante absoluta 8 e versao uniforme sobre bolas; Whitney demonstrada, sem hipotese adicional nao provada. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.rational_jackson_height`](../../../lean4/ambientes/artigo_2/Pendencias/Jackson.lean) — linha 508.
- [`Pendencias.Jackson.rational_jackson_uniform`](../../../lean4/ambientes/artigo_2/Pendencias/Jackson.lean) — linha 678.

## IV.4.2 — teorema direção direta com altura aritmética

Original de 77 páginas: 19.2.

Fonte editável: [tex/partes/artigo_3.tex:398](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.2`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Inclusoes diretas de Besov para os regimes do enunciado, inclusive agenda com folga polinomial, em raiz diadica geral. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.direct_besov_height`](../../../lean4/ambientes/artigo_2/Pendencias/Direta.lean) — linha 594.

## IV.4.3 — corolario imersões quantitativas uniformes sobre bolas

Original de 77 páginas: 19.3.

Fonte editável: [tex/partes/artigo_3.tex:453](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.3`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Cotas quantitativas uniformes sobre bolas nos tres regimes, com constantes independentes da funcao e do raio. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.uniform_besov_ball`](../../../lean4/ambientes/artigo_2/Pendencias/Direta.lean) — linha 718.

## IV.4.4 — observacao o papel do índice $q$

Original de 77 páginas: 19.4.

Fonte editável: [tex/partes/artigo_3.tex:501](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.4`.

Estado: **Observação editorial**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.4.5 — corolario endpoint $C^2$

Original de 77 páginas: 19.5.

Fonte editável: [tex/partes/artigo_3.tex:518](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.5`.

Estado: **Formalizado e compilado**. A estimativa C2 de base existe. Falta transporta-la para as definicoes de agenda, erro e classe do atual Artigo 3; nao contado como teorema integralmente formalizado. [11/11/2026] Funcional `rateInf` (𝔞_{α,∞}) e agenda `H2 R M N = ⌈C_H N²⌉` definidos; sup sobre `FRMIcc R M` (C² só em [0,1]) de 𝔞_{2,∞} ≤ max{R,(M+4)/2}; para N ≥ 2, montagem admissível com códigos ≤ C_b N log₂(2N). Base: `joint_all_N_Icc`, `joint_budget_Icc`, `pErr_eq_min`. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Dyadic.Lib.simultaneous_control`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Sec7/Simultaneous.lean) — linha 477.
- [`Dyadic.Lib.precision_height`](../../../lean4/ambientes/base_integrada/Unified/Consolidado/Sec7/Precision.lean) — linha 71.
- [`Pendencias.Agenda.c2_endpoint`](../../../lean4/ambientes/artigo_2/Pendencias/Endpoint.lean) — linha 31.
- [`Pendencias.Agenda.c2_endpoint_bits`](../../../lean4/ambientes/artigo_2/Pendencias/Endpoint.lean) — linha 56.

## IV.4.6 — proposicao piso aritmético uniforme

Original de 77 páginas: 19.6.

Fonte editável: [tex/partes/artigo_3.tex:555](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:4.6`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] Piso e_N ≥ 1/(2H(N)), dist(1/(2H), 𝒬_H) = 1/(2H) e a consequência H(N) ≥ (2C)⁻¹N^s (para N ≥ 1), sobre K=[0,1]. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Agenda.arithmetic_floor`](../../../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 125.
- [`Pendencias.Agenda.infDist_QH`](../../../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 111.
- [`Pendencias.Agenda.height_lower_bound`](../../../lean4/ambientes/artigo_2/Pendencias/Agenda.lean) — linha 160.

## IV.5.1 — definicao biblioteca marcada completa

Original de 77 páginas: 20.1.

Fonte editável: [tex/partes/artigo_3.tex:756](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.1`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] Definições `MAtom` (s ∈ ℚ qualquer), `MTree`, `MWF`, `MAsm`, `MAsmNH`; inclusões 𝓛 ⊂ 𝓛^□, 𝒜 ⊂ 𝒜^□, 𝒜_{N,H} ⊂ 𝒜^□_{N,H}. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Marcada.marked_extends`](../../../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 157.
- [`Pendencias.Marcada.Atom.toM_injective`](../../../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 52.

## IV.5.2 — teorema reversibilidade rasa exata

Original de 77 páginas: 20.2.

Fonte editável: [tex/partes/artigo_3.tex:793](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.2`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Teorema completo exact_shallow_reversal para parametros reais: equivalencia marcada e aritmetica, construcao canonica, minimalidade e unicidade inclusive dos rotulos atomicos, M+1 <= N_can <= 1+sum d_j e equivalencia com a biblioteca original quando todas as inclinacoes sao nao nulas. Igualdade de funcoes em [0,1], como no TeX; inclui M=0. Build Pendencias e auditoria de axiomas aprovados, apenas propext, Classical.choice, Quot.sound.

- [`Pendencias.Marcada.RealReLU.exact_shallow_reversal`](../../../lean4/ambientes/artigo_2/Pendencias/ReversaoOriginal.lean) — linha 219.

## IV.5.3 — definicao altura canônica de rede

Original de 77 páginas: 20.3.

Fonte editável: [tex/partes/artigo_3.tex:845](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.3`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] Definições `canonShape` (𝒯(S)), `RedReLU`, `Hcan`; H_can = maior altura dos átomos da montagem canônica; folhas de 𝒯(S) sem quebras no interior. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Marcada.RedReLU.Hcan`](../../../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 265.
- [`Pendencias.Marcada.RedReLU.Hcan_eq_maxHeight`](../../../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 274.
- [`Pendencias.Marcada.canonShape_no_interior`](../../../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 203.
- [`Pendencias.Marcada.RedReLU.canon_leaves_free`](../../../lean4/ambientes/artigo_2/Pendencias/Marcada.lean) — linha 280.

## IV.5.4 — proposicao forma ancorada e comprimento estrutural

Original de 77 páginas: 20.4.

Fonte editável: [tex/partes/artigo_3.tex:863](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.4`.

Estado: **Não formalizado no acervo**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.5.5 — teorema reversão aproximada quantizada

Original de 77 páginas: 20.5.

Fonte editável: [tex/partes/artigo_3.tex:922](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.5`.

Estado: **Não formalizado no acervo**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.5.6 — corolario redes profundas medidas pela função realizada

Original de 77 páginas: 20.6.

Fonte editável: [tex/partes/artigo_3.tex:984](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.6`.

Estado: **Não formalizado no acervo**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.5.7 — teorema imersão inversa sob crescimento de Lipschitz

Original de 77 páginas: 20.7.

Fonte editável: [tex/partes/artigo_3.tex:1087](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.7`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] ω₂ e Besov pela norma diádica do texto em [0,1]; C = 4 + 2^{γ+1}; hipótese A_α(f) ≤ A na forma e_N ≤ A N^{-α}; conclusões B^{θ*}_{∞,∞} e B^θ_{∞,p} (θ<θ*, 0<p<∞). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.inverse_modulus`](../../../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 167.
- [`Pendencias.Agenda.inverse_besov`](../../../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 262.

## IV.5.8 — corolario aplicação às agendas diretas

Original de 77 páginas: 20.8.

Fonte editável: [tex/partes/artigo_3.tex:1142](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.8`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] H(N) ≤ C N^γ ⟹ 𝒜^α_q ⊂ B^{α/(α+γ)}_{∞,∞} (q<∞ via IV.3.2 e q=∞); agendas `Hsk` = H_{s,κ} em [0,1] (C_K = 8): ϑ_s e ordens < ϑ_s com fator logarítmico. Montagens H(N)-Lipschitz (`Sigma_lipschitz`). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.raw_library_inverse_inf`](../../../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 419.
- [`Pendencias.Agenda.raw_library_inverse`](../../../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 430.
- [`Pendencias.Agenda.schedule_raw_inverse`](../../../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 536.
- [`Pendencias.Agenda.vartheta_eq`](../../../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 526.

## IV.5.9 — teorema agudeza por um pente de tendas

Original de 77 páginas: 20.9.

Fonte editável: [tex/partes/artigo_3.tex:1178](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.9`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Teorema do pente de tendas IV.5.9 concluido em Pendencias.PenteGemini.critical_tent_comb: continuidade, aproximacao para todo N >= 1 na biblioteca original e nao pertencimento as classes Besov acima e no expoente critico para todo r finito. Build Pendencias e auditoria agregada passaram; axiomas permitidos.

- [`Pendencias.PenteGemini.critical_tent_comb`](../../../lean4/ambientes/artigo_2/Pendencias/Pente.lean) — linha 1194.

## IV.5.10 — lema desigualdade inversa universal

Original de 77 páginas: 20.10.

Fonte editável: [tex/partes/artigo_3.tex:1287](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.10`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [11/11/2026] ω₂(f,1/N) ≤ 4 𝓡_N(f) para toda agenda, toda f e todo N (`realN`). Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.Agenda.universal_inverse`](../../../lean4/ambientes/artigo_2/Pendencias/Inversa.lean) — linha 109.

## IV.5.11 — observacao o que o funcional mede

Original de 77 páginas: 20.11.

Fonte editável: [tex/partes/artigo_3.tex:1308](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.11`.

Estado: **Observação editorial**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Nenhuma declaração Lean associada na matriz recebida.

## IV.5.12 — teorema Jackson racional para o funcional de realização

Original de 77 páginas: 20.12.

Fonte editável: [tex/partes/artigo_3.tex:1314](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.12`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Jackson para o funcional de realizacao em [0,1], cota bilateral e versao uniforme; constantes universais explicitas. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.regularized_jackson`](../../../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 87.
- [`Pendencias.Jackson.regularized_jackson_uniform`](../../../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 119.

## IV.5.13 — teorema caracterização pelo funcional de realização

Original de 77 páginas: 20.13.

Fonte editável: [tex/partes/artigo_3.tex:1362](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.13`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Igualdades de classes de Besov e realizacao em todos os regimes declarados, incluindo folga polinomial. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.complete_besov_reversibility`](../../../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 393.

## IV.5.14 — teorema reversibilidade estável por inclusão de redes

Original de 77 páginas: 20.14.

Fonte editável: [tex/partes/artigo_3.tex:1448](../../../tex/partes/artigo_3.tex); rótulo `map:artigo_3:5.14`.

Estado: **Formalizado e compilado**. Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3. [13/11/2026] Estabilidade das igualdades para familias aninhadas que contem zero e as montagens na escala linear declarada. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.architecture_stable_reversibility`](../../../lean4/ambientes/artigo_2/Pendencias/Realizacao.lean) — linha 448.


## Cópias para leitura

`fontes_referenciados/` reúne cópias byte a byte dos módulos associados. Para compilar, use os ambientes completos em `../../ambientes/`, que preservam imports e dependências.
