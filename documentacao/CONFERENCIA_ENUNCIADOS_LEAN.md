# Conferência de fidelidade dos enunciados Lean

Folha de conferência entre os enunciados de `tex/partes/artigo_2.tex` e os teoremas Lean
correspondentes em `lean4/ambientes/artigo_2/` (Lean 4.28.0, Mathlib v4.28.0).

Esta folha foi refeita do zero nesta rodada: a branch `conferencia-enunciados-lean` (commit
`fc5f1c0`) não existia no computador de trabalho. O conteúdo abaixo foi conferido contra o
código atual da `main` (após o PR #14, lei de fase formalizada).

## Legenda

- **provado**: verificado pelo compilador Lean (`lake build Pendencias`), com axiomas apenas
  `propext`, `Classical.choice`, `Quot.sound` (ver `AuditoriaPendencias.lean`).
- **testado numericamente**: verificação numérica; não é prova formal. Não usado nesta folha.
- **conjectura**: afirmação não provada.

Cada item tem: (1) enunciado do texto, em paráfrase; (2) enunciado Lean, com arquivo e linha;
(3) correspondência das conclusões; (4) divergências e ressalvas; (5) edições propostas
(**não aplicadas**: aguardam aprovação).

Status usados: **Fiel** (mesmas hipóteses e conclusões), **Fiel com ressalva** (correspondência
completa, com diferença de forma ou de hipótese que deve ser explicitada), **Divergência**.

---

## Tabela de definições

| Texto | Lean | Arquivo |
|---|---|---|
| `e_f(J)`, erro local de `f` em `J` | `locErr f k m` | `RequestProject/Dyadic.lean:35` |
| `n_f(ε)`, número de folhas do limiar | `nThr f ε k m` | `RequestProject/Dyadic.lean:259` |
| `E_N^dia(f)_∞`, erro diádico ótimo com `N` folhas | `Edia f k m N` | `RequestProject/Dyadic.lean:215` |
| `I(f) = ∫_K |f''|^{1/2}` (unilateral em `K`) | `curvI f k m`; `curvIOn f k m` para `C²(K)` | `RequestProject/DyadicEnvelope.lean:15`; `Pendencias/Ponte.lean:206` |
| `g(u) = 2^{⌈u⌉-u}`, `g⁺(u) = 2^{⌊u⌋+1-u}` | `gC`, `gP` | `Pendencias/FaseNucleo.lean:14-15` |
| `w_f(x) = √(|f''(x)|/8)` | `wPh f x` | `Pendencias/FaseFuncao.lean:22` |
| `a_f(x) = log₄(L²|f''(x)|/8)` | `aPh f k₀ m₀ x` | `Pendencias/FaseFuncao.lean:25` |
| `Ψ_f(t) = ∫_K w_f g(t+a_f)` | `PsiF f k₀ m₀ t` | `Pendencias/FaseFuncao.lean:29` |
| `Ψ_f⁺` | `PsiP f k₀ m₀ t` | `Pendencias/FaseFuncao.lean` |
| `μ_f` (medida de fase em 𝕋) | `muCirc f k₀ m₀` = `μ̃_f`, com `μ_f = √8·μ̃_f` | `Pendencias/FaseMedida.lean` |
| `𝕋` | `AddCircle (1:ℝ)` | Mathlib |
| versões em `C²(K)` | sufixo `_on`, via `extF f (cL k₀ m₀) (cR k₀ m₀)` | `Pendencias/Ponte.lean`, `Pendencias/FaseOn.lean` |

---

## III.11.1 — minimalidade exata do limiar

**Texto** (`artigo_2.tex:2541`, rótulo `artigo_2:thm:threshold-optimality`). Para `f ∈ C(K)`, a
árvore de limiar `T_ε(f)` é finita e é a única árvore mais grossa cuja interpolação tem erro
≤ ε; tem o menor número de folhas entre as árvores viáveis; e
`E_N ≤ ε ⇔ n_f(ε) ≤ N`, com `E_N = inf{ε > 0 : n_f(ε) ≤ N}`.

**Lean.** `Artigo.threshold_optimality` (`RequestProject/Dyadic.lean:337`) e
`Artigo.Edia_eq_sInf_nThr` (`RequestProject/Dyadic.lean:363`, com `hN : 1 ≤ N`).

**Correspondência.**

| Conclusão do texto | Lean |
|---|---|
| `T_ε(f)` finita e única árvore mais grossa | `(∃! T, IsThr f ε k m T)` |
| erro de `T_ε(f)` ≤ ε | `(thrTree f ε k m).treeErr f k m ≤ ε` |
| coarsest: refina toda árvore viável | `∀ T, T.treeErr ≤ ε → T.Refines (thrTree …)` |
| menor número de folhas | `∀ T, T.treeErr ≤ ε → nThr f ε k m ≤ T.numLeaves` |
| `E_N ≤ ε ⇔ n_f(ε) ≤ N` | `∀ N, 1 ≤ N → (Edia f k m N ≤ ε ↔ nThr f ε k m ≤ N)` |
| `E_N = inf{…}` | `Edia_eq_sInf_nThr` (requer `1 ≤ N`) |

**Status: Fiel com ressalva.** **provado**.

**Divergências e ressalvas.**
- O enunciado do texto não diz `N ≥ 1`; o Lean exige `1 ≤ N` em ambas as formas (a forma com
  ínfimo `Edia_eq_sInf_nThr` tem `hN : 1 ≤ N` explícito). Ressalva de redação: o texto deve dizer
  a faixa de `N` em que vale a equivalência.

**Edição (aprovada e aplicada em `tex/partes/artigo_2.tex`).** No enunciado, acrescentar «para todo inteiro `N ≥ 1`» antes
de `E_N^{dia}(f)_∞ ≤ ε`, e «(para `N ≥ 1`)» antes da identidade do ínfimo.

---

## III.11.2 — expansão local uniforme

**Texto** (`artigo_2.tex:2601`, rótulo `artigo_2:lem:local-asymptotic-error`). Para `f ∈ C²(K)`,
toda célula `J ⊆ K` e todo `x ∈ J`:
`|e_f(J) − |f''(x)||J|²/8| ≤ ω_{f''}(|J|)|J|²/8`.

**Lean.** `Pendencias.local_asymptotic_error_on` (`Pendencias/Ponte.lean:229`), com
`hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)`, `hJ : cellIcc k m ⊆ cellIcc k₀ m₀`,
`hx : x ∈ cellIcc k m`; `modCont` no lugar de `ω_{f''}`.

**Correspondência.** Mesma desigualdade, com `|f''(x)|` e `ω` calculados com a derivada
unilateral em `K` (`derivWithin (derivWithin f K) K`).

**Status: Fiel.** **provado**.

**Divergências e ressalvas.** Nenhuma substantiva. `modCont` é a definição Lean do módulo de
continuidade; a identidade com `ω_{f''}` é a definição usada no texto.

---

## III.11.3 — envelope diádico universal e agudo

**Texto** (`artigo_2.tex:2628`, rótulo `artigo_2:thm:general-dyadic-envelope`). Para `f ∈ C²(K)`
com `I(f) > 0`: `I/√8 ≤ liminf √ε n_f(ε) ≤ limsup √ε n_f(ε) ≤ I/√2` e
`I²/8 ≤ liminf N²E_N ≤ limsup N²E_N ≤ I²/2`. As afirmações valem também se `f''` tem zeros.
Se `I(f) = 0`, então `f` é afim e os dois erros são identicamente nulos.

**Lean.**
- `Pendencias.general_dyadic_envelope_on` (`Pendencias/Ponte.lean:240`): forma "eventual"
  (`∀ δ > 0, ∀ᶠ ε …` e `∀ᶠ N …`).
- `Pendencias.general_dyadic_envelope_liminf_on` (`Pendencias/Ponte.lean:255`): forma
  `liminf`/`limsup`.
- `Pendencias.general_dyadic_envelope_zero_on` (`Pendencias/Ponte.lean:270`): caso `I(f) = 0`.
- Formas globais (`C²(ℝ)`): `Artigo.general_dyadic_envelope` (`RequestProject/DyadicEnvelope.lean:519`),
  `general_dyadic_envelope_zero` (linha 544), `general_dyadic_envelope_liminf` (linha 597).

**Correspondência.**

| Conclusão do texto | Lean |
|---|---|
| `I/√8 ≤ liminf √ε n_f(ε)` e `limsup ≤ I/√2` | `…_liminf_on`: `curvIOn/√8 ≤ liminf …`, `limsup … ≤ curvIOn/√2` |
| `I²/8 ≤ liminf N²E_N`, `limsup N²E_N ≤ I²/2` | `…_liminf_on`: `curvIOn²/8 ≤ liminf …`, `limsup … ≤ curvIOn²/2` |
| formas eventuais (`±δ`) | `general_dyadic_envelope_on` |
| `I(f) = 0` ⇒ `f` afim em `K` | `∃ α β, ∀ x ∈ cellIcc k₀ m₀, f x = α + β x` |
| `I(f) = 0` ⇒ erros nulos | `∀ ε > 0, nThr f ε k₀ m₀ = 1` e `∀ N ≥ 1, Edia f k₀ m₀ N = 0` |
| afirmações válidas com zeros de `f''` | hipótese `hI : 0 < curvIOn` é a única; nenhuma exige `f'' ≠ 0` |

**Status: Fiel com ressalva.** **provado**.

**Divergências e ressalvas.**
- Caso `I(f) = 0`: o texto diz apenas «os dois erros são identicamente nulos», sem a conclusão
  «f é afim» explícita no enunciado (a conclusão está em forma de prosa). O Lean tem as três
  partes. Ressalva de redação, conforme pedido.
- O Lean exige `1 ≤ N` para `Edia`, como em III.11.1.

**Edições propostas (não aplicadas).**
1. (aplicada) No enunciado, acrescentar: «Se `I(f) = 0`, então `f` é afim em `K`, `n_f(ε) = 1` para todo
   `ε > 0` e `E_N^{dia}(f)_∞ = 0` para todo `N ≥ 1`.»
2. Trocar «os dois erros são identicamente nulos» por essa lista, e explicitar `N ≥ 1` nas
   igualdades com `E_N`.

---

## III.12.1 — lei exata e intervalo de acumulação

**Texto** (`artigo_2.tex:2725`, rótulo `artigo_2:thm:quadratic-dyadic-constant`). Se `K` é uma
célula diádica de comprimento `L` e `q'' ≡ κ ≠ 0` em `K`, com `A = |κ|L²/8`, então para `N ≥ 1`:
`E_N(q) = A·4^{−⌊log₂N⌋}`; os valores de acumulação de `N²E_N` formam `[A, 4A]`; `liminf = A`;
`limsup = 4A`; o limite não existe; e `n_f(ε) = 2^{⌈log₄(A/ε)⌉}`.

**Lean.** `Pendencias.quadratic_dyadic_constant_on` (`Pendencias/LeiExata.lean:74`), com
`hq : ContDiffOn ℝ 2 q (cellIcc k₀ m₀)`, `hκ : κ ≠ 0`, `hκq` (derivada unilateral igual a `κ`
em `K`), `hA : A = |κ|·(cR − cL)²/8`. Versão global: `Artigo.quadratic_dyadic_constant`
(`RequestProject/DyadicExact.lean:58`).

**Correspondência.**

| Conclusão do texto | Lean |
|---|---|
| `E_N(q) = A/4^{⌊log₂N⌋}` (`N ≥ 1`) | `∀ N, 1 ≤ N → Edia q k₀ m₀ N = A / 4 ^ Nat.log 2 N` |
| acumulação = `[A, 4A]` | `{x \| MapClusterPt x atTop (N²·Edia)} = Icc A (4A)` |
| `liminf = A`, `limsup = 4A` | `liminf … = A` e `limsup … = 4 * A` |
| sem limite | `¬ ∃ c, Tendsto (N²·Edia) atTop (𝓝 c)` |
| `n_f(ε) = 2^{⌈log₄(A/ε)⌉}` | `∀ ε > 0, nThr q ε k₀ m₀ = 2 ^ (⌈logb 4 (A/ε)⌉).toNat` |

**Status: Fiel.** **provado** (as seis conclusões).

**Divergências e ressalvas.** Nenhuma. A forma `⌈·⌉.toNat` no Lean é a forma inteira do
expoente, equivalente ao texto para `A/ε > 0`.

---

## III.12.2 — contagem exata em uma malha diádica base

**Texto** (`artigo_2.tex:2833`, rótulo `artigo_2:thm:piecewise-quadratic-count`). `f ∈ C(K)`,
`K = [0,1]`, quadrática em cada célula `Q_i` da malha `2^{−q₀}`, com `f''|_{int Q_i} = κ_i ≠ 0`
e `A_i = |κ_i||Q_i|²/8`. Existe `ε₀ > 0` tal que, para `0 < ε < ε₀`,
`n_f(ε) = Σ_i 2^{⌈log₄(A_i/ε)⌉}` e `√ε n_f(ε) = Φ(−log₄ε)`, com `Φ` 1-periódica e não constante.

**Lean.** `Artigo.piecewise_quadratic_count` (`RequestProject/DyadicPhase.lean:238`). Hipóteses:
`hκ : ∀ i < 2^q₀, κ i ≠ 0` e `hquad : ∀ i < 2^q₀, ∃ b c, ∀ x ∈ cellIcc q₀ i, f x = κ i/2·x² + b x + c`;
`hA : A i = |κ i|·(cR − cL)²/8`.

**Correspondência.**

| Conclusão do texto | Lean |
|---|---|
| existe `ε₀`, para `ε < ε₀`: `n_f(ε) = Σ 2^{⌈log₄(A_i/ε)⌉}` | `∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → nThr f ε 0 0 = Σ …` |
| `√ε n_f(ε) = Φ(−log₄ε)` | `Real.sqrt ε * nThr f ε 0 0 = phaseFn A (2^q₀) (−logb 4 ε)` |
| `Φ` 1-periódica | `Function.Periodic (phaseFn A (2^q₀)) 1` |
| `Φ` não constante | `∃ s t, phaseFn … s ≠ phaseFn … t` |

**Status: Fiel com ressalva.** **provado**.

**Divergências e ressalvas.**
- Forma das hipóteses: o Lean usa `κ_i/2·x² + bx + c` em cada célula **fechada**, o que tem
  `f'' = κ_i` no interior, e a continuidade de `f` em `K` segue do lema de colagem (finitas
  células fechadas). Equivalente ao texto, mas a continuidade não aparece como hipótese.
- O texto não define `Φ`; o Lean usa `phaseFn A (2^q₀)`. Ressalva de notação.

---

## III.12.3 — fases sincronizadas

**Texto** (`artigo_2.tex:2880`, rótulo `artigo_2:cor:synchronized-phases`). Nas hipóteses de
III.12.2, com `A_i/A_j ∈ 4^ℤ` para todos `i, j`:
`liminf N²E_N = I(f)²/8` e `limsup N²E_N = I(f)²/2`.

**Lean.** `Artigo.synchronized_phases` (`RequestProject/DyadicSync.lean:99`), com
`hsync : ∀ i < 2^q₀, ∀ j < 2^q₀, ∃ z : ℤ, A i / A j = 4^z`.

**Correspondência.** `liminf (N²·Edia f 0 0 N) atTop = (∫₀¹ √|f''|)²/8` e
`limsup … = (∫₀¹ √|f''|)²/2`. O Lean escreve `I(f)` como a integral `∫₀¹ √|deriv (deriv f)|`.

**Status: Fiel.** **provado**.

**Divergências e ressalvas.** Notação de `I(f)`. A demonstração textual foi sincronizada e
não usa o envelope global para a função por partes (ver `MAPA_TEX_LEAN.md`).

---

## III.12.5 — lema das propriedades da função de fase

**Texto** (`artigo_2.tex:3146`, rótulo `map:artigo_2:12.5`). Para `f ∈ C²(K)` com `I(f) > 0`:
(i) `Ψ_f` e `Ψ_f⁺` são 1-periódicas, `I/√8 ≤ Ψ_f ≤ Ψ_f⁺ ≤ I/√2`; `Ψ_f(t) = 8^{−1/2}∫ g(t+θ) dμ_f(θ)`;
`Ψ_f⁺(t) − Ψ_f(t) = 8^{−1/2} μ_f({−t})`.
(ii) `Ψ_f` contínua à esquerda, `Ψ_f⁺` à direita, limites laterais, semicontinuidade,
extremos `m_f`, `M_f`; `Ψ_f` contínua em `t` ⇔ `−t` não é átomo.
(iii) `∫₀¹ Ψ_f(t) e^{−2πimt} dt = (√8(ln2 + 2πim))^{−1} ∫_𝕋 e^{2πimθ} dμ_f(θ)`; em particular
`∫₀¹ Ψ_f = I/(√8 ln 2)`.

**Lean.** Módulos `Pendencias/Fase*.lean`, principais declarações:

| Conclusão | Lean (arquivo) |
|---|---|
| periodicidade | `psiF_periodic`, `psiP_periodic` (`FaseFuncao`) |
| cotas `I/√8 ≤ Ψ_f`, `Ψ_f ≤ Ψ_f⁺ ≤ 2I/√8` | `psiF_ge`, `psiF_le_psiP`, `psiP_le` (`FaseFuncao`) |
| limites laterais | `psiF_tendsto_left/right`, `psiP_tendsto_left/right` (`FaseFuncao`) |
| semicontinuidade, extremos | `psiF_lsc`, `psiP_usc`, `exists_min_psiF`, `exists_max_psiP` |
| `Ψ⁺ − Ψ` | `psiP_sub_psiF` (`FaseSalto.lean:32`): `= ∫_K 1_{S(t)} w_f`, com `S(t) = {x : t + a(x) ∈ ℤ}` |
| `Ψ` contínua ⇔ sem átomo | `continuousAt_psiF_iff` (`FaseSalto.lean:83`), `isAtomPhase_iff_gap` (`FaseSalto.lean:54`) |
| `∫₀¹ Ψ_f` | `integral_psiF` (`FaseMedia.lean:50`) |
| coeficientes de Fourier | `fourier_psiF` (`FaseFourier.lean:117`) |
| `Ψ_f = ∫ g(t+θ) dμ̃_f` | `PsiF_eq_circ` (`FaseMedida.lean`), com `μ̃_f = μ_f/√8` |
| massa de `μ̃_f` = `I/√8` | `muCirc_mass` (`FaseMedida.lean`) |
| versões `C²(K)` | `psiFOn_ge`, `psiPOn_le`, `integral_psiFOn`, `continuousAt_psiFOn_iff` (`FaseOn.lean`) |

**Status: Fiel com ressalva** (**provado**). As ressalvas que existiam sobre `μ_f` foram
resolvidas nesta rodada (ver abaixo).

**Divergências e ressalvas.**
1. **Resolvida:** `μ_f` não era construída como medida em `𝕋`. Agora `muCirc f k₀ m₀` é a
   imagem de `√(|f''|/8) dx` em `K` pela fase `x ↦ a(x) mod 1`; por `PsiF_eq_circ`,
   `Ψ_f(t) = ∫ gCirc(t+θ) dμ̃_f(θ)`, e `μ_f = √8 μ̃_f` (a massa total é `I/√8`).
   A identidade de (i) com `μ_f({−t})` vale com `μ̃_f({−t}) = ∫ 1_{S(t)} w_f`, e a versão
   formal é a integral de `psiP_sub_psiF`, não uma igualdade de medidas.
2. **Resolvida em `C²(K)` e `ℝ`:** o cálculo de (iii) está formalizado; `fourier_muCirc` dá
   `∫ e_m dμ̃_f = ∫_K w_f e^{2πima}`, e `fourier_psiF` a relação com `Ψ_f`.
3. Tipo de `μ_f` no texto versus `μ̃_f`: o texto usa `μ_f`; o Lean usa `μ̃_f`. Relação
   `μ_f = √8 μ̃_f` (ver 1).

**Edição proposta (não aplicada).** Escrever (i) como
«`Ψ_f(t) = ∫_𝕋 g(t+θ) dμ̃_f(θ)`, com `μ̃_f = 8^{−1/2} μ_f`», ou manter `μ_f` e acrescentar a
definição de `μ̃_f` como imagem.

---

## III.12.6 — lema contagem por células

**Texto** (`artigo_2.tex:3200`, rótulo `map:artigo_2:12.6`). Para `f ∈ C²(K)`, malha uniforme
`𝒬_q` de `2^q` células, `m_Q = min_Q c`, `M_Q = max_Q c`, `t = −log₄ε`:
(a) `√ε n_f(ε) ≤ 2^q√ε + Σ_{M_Q>0} ℓ_Q √(M_Q/8) g(t + log₄(L²M_Q/8))`;
(b) existe `ε_q > 0` tal que, para `ε < ε_q`, `√ε n_f(ε) ≥ Σ_{m_Q>0} ℓ_Q √(m_Q/8) g(t + log₄(L²m_Q/8))`.

**Lean.** Versões com teto `⌈log₄(·)⌉`, sobre `f ∈ C²(ℝ)`:
`Pendencias.upper_count_pow` (a) e `Pendencias.lower_count_pow` (b) (`Pendencias/FaseContagem.lean:31`
e `:72`). **Versões `C²(K)` (acrescentadas nesta rodada):** `Pendencias.upper_count_pow_on` e
`Pendencias.lower_count_pow_on` (`Pendencias/FaseOn.lean`), obtidas de `extF` com
`nThr_congr`, `treeErr_congr`, `locErr_congr` e `d2On_eq` (`eqOn_cell_d2`).

**Correspondência.** Os tetos `⌈·⌉` do Lean são os do texto. A passagem à forma com `g(t+α)`
do texto está nos módulos `FaseLei2` (`upper_integral_bound`, `lower_integral_bound`) e
`FaseLei3` (`phase_lower`, `phase_upper`); **esta correspondência não foi reconferida linha a
linha nesta rodada**.

**Status: Fiel com ressalva** (**provado**). A ponte para a forma com `g(t+α)` foi verificada, mas
só na forma de passo com `η`, não na forma literal do texto.

**Verificação da ponte.** As somas de (a) e (b) não são formalizadas literalmente. O Lean usa `Gl`/`Gu`
(`FaseLei2.lean:109-115`): `Gl(n,ε,j) = sLow_j/√8 · gC(−log₄ε + log₄((2^{k₀})⁻² sLow_j²/8))`, análogo a `Gu`
com `sUp_j`. É a parcela `w·g(t+log₄(L²M/8))` do texto com `M` trocado por `sLow²` (ou `sUp²`), onde
`sLow/sUp = sqrt(|f''|) ∓ η_n` nas células de nível `k₀+d_n`. A soma vira `∫_K Gl(cidx x) dx`
(`lower_integral_bound`; `upper_integral_bound` para a cota superior), e `η_n → 0` é feito por Fatou em
`FaseLei3` (`phase_lower`, `phase_upper`). O conteúdo está provado, mas com `η_n` e profundidade `d_n`
escolhidas por oscilação; (a) e (b) com `M_Q`, `m_Q` e `ε_q` literais **não** aparecem como enunciados Lean.
Ressalva mantida.

**Divergências e ressalvas.**
- A versão `C²(K)` do texto estava pendente (ressalva do mapa, agora resolvida).
- Hipótese (b): o texto usa `ε_q` (mínimo dos erros dos ancestrais próprios das células com
  `m_Q > 0`); o Lean usa a hipótese `hanc` com a mesma condição, por ancestral.

---

## III.12.7 — teorema lei de fase para curvatura variável

**Texto** (`artigo_2.tex:3271`, rótulo `map:artigo_2:12.7`). Para `f ∈ C²(K)`, `I > 0`,
`ε_j ↓ 0` com `−log₄ε_j mod 1 → τ`: `Ψ_f(τ) ≤ liminf √ε_j n_f(ε_j) ≤ limsup ≤ Ψ_f⁺(τ)`.
(i) se `−τ` não é átomo, `√ε_j n_f(ε_j) → Ψ_f(τ)`;
(ii) se `μ_f` não tem átomos, `Ψ_f` é contínua e `√ε n_f(ε) − Ψ_f(−log₄ε) → 0`;
(iii) `liminf_{ε↓0} √ε n_f(ε) = m_f` e `limsup = M_f`.

**Lean.**
- Cotas por fases convergentes: `phase_lower` (`Pendencias/FaseLei3.lean:57`),
  `phase_upper` (`FaseLei3.lean:92`).
- (i): `phase_law_nonatom` (`Pendencias/FaseLei4.lean:54`), hipótese
  `Tendsto (−logb 4 (ε j) − z j) atTop (𝓝 τ)` com `z j ∈ ℤ` (equivalente a `mod 1`).
- (ii): `phase_law_uniform` (`FaseLei4.lean:69`); a parte de convergência uniforme de
  `√ε n_f(ε) − Ψ_f(−log₄ε)` **não foi conferida nesta rodada**.
- (iii): `phase_seq_min` (`FaseLei5.lean:20`), `phase_seq_max` (`FaseLei5.lean:34`),
  `phase_liminf_ge` e `phase_limsup_le` (`FaseLei4.lean:94`, `:107`).
- Versões `C²(K)`: `phase_law_nonatom_on`, `phase_law_uniform_on`, `phase_liminf_ge_on`,
  `phase_limsup_le_on` (`Pendencias/FaseOn.lean`).

**Status: Fiel.** **provado** em (i), (ii) e (iii).

**Verificação de (ii).** `phase_law_uniform` (`FaseLei4.lean:69`) afirma
`∀ δ>0, ∀ᶠ ε in 𝓝[>]0, |√ε·n_f(ε) − Ψ_f(−log₄ε)| < δ`, a convergência uniforme do texto, sob
`∀ t, ¬IsAtomPhase`. Prova por contradição com extração de subsequência (`exists_phase_subseq`), usando (i) e a
continuidade de `Ψ_f` nas fases não atômicas. Compilada, sem `sorry`, axiomas padrão.

**Divergências e ressalvas.**
- `τ` é tratado por sequências de inteiros `z_j`, o que é a forma `mod 1` do texto.
- (ii) verificado: a convergência uniforme está no enunciado Lean.

---

## III.12.8 — acumulação, critério de uniformidade e limite

**Texto** (`artigo_2.tex:3366`, rótulo `map:artigo_2:12.8`). Para `f ∈ C²(K)` com `I > 0`:
(a) os valores de acumulação de `N²E_N` formam `[m_f², M_f²]`;
(b) `lim N²E_N` existe ⇔ `Ψ_f` constante ⇔ `μ_f` uniforme; nesse caso `Ψ_f ≡ I/(√8 ln2)`,
`lim N²E_N = I²/(8 ln²2)` e `lim √ε n_f(ε) = I/(√8 ln2)`;
(c) média universal: `lim_T ∫_T^{T+1} 2^{−t} n_f(4^{−t}) dt = I/(√8 ln2)`;
(d) `m_f = I/√8` ⇔ `μ_f` é massa pontual (`|f''| ∈ c₀ 4^ℤ` q.t.p. em `{f'' ≠ 0}`), e o mesmo
para `M_f = I/√2`.

**Lean.**
- (a) `phase_cluster_set_on` (`Pendencias/FaseLei5.lean:289` na forma ℝ, `_on` em `FaseOn.lean`).
- (b) `limit_iff_const_on` e `limit_iff_const` (`FaseCoro.lean:74`): limite ⇔ `Ψ` constante;
  `limit_of_const_on`: valores `c = I/(√8 ln2)`, `lim √ε n = c`, `lim N²E = c²`.
  **Nova:** `psi_const_iff_muCirc` (`FaseMedida.lean`): `Ψ` constante ⇔
  `muCirc = (ofReal(I/√8)) • haarAddCircle`, ou seja, `μ̃_f = (I/√8)·haar`; `psiOn_const_iff_muCirc`
  e `limit_iff_muCirc_on` (`C²(K)`); `limit_iff_muCirc` (`ℝ`).
- (c) `phase_average` (`FaseMediaFase.lean:77`), e `phase_average_on` (`FaseOn.lean`).
- (d) `min_attained_iff_fourPowers`, `max_attained_iff_fourPowers`, `extremes_iff_fourPowers`
  (`FaseExtremos.lean:183`, `:191`, `:199`), e as versões `_on`.

**Status: Fiel** (**provado**; (b) completa com as formas `_muCirc`). A ressalva que restava
(equivalência com `μ_f` uniforme) está resolvida.

**Divergências e ressalvas.**
1. **Resolvida:** a equivalência `Ψ_f constante ⇔ μ_f uniforme` (b). Prova: unicidade de
   Fourier para medidas finitas no círculo (`circ_fourier_uniqueness`, via `span_fourier_closure_eq_top`
   e `ext_of_forall_integral_eq_of_IsFiniteMeasure`) e os coeficientes `fourier_muCirc`.
2. **Naming**: «massa pontual» no Lean é `FourPowers`: `|f''| ∈ c₀·4^ℤ` q.t.p. em `{f'' ≠ 0}`,
   que é a definição parentética do próprio texto. Não é uma medida pontual formal em `𝕋`
   (`μ_f` não tem átomo formal no Lean; a forma formal é a condição sobre `|f''|`).
   Ressalva de redação, não de conteúdo.
3. Em (d) o Lean prova a equivalência para `m_f` e para `M_f` separadamente.

**Edição proposta (não aplicada).** Em (b), trocar «ocorre se, e somente se, `μ_f` é uniforme»
por «ocorre se, e somente se, `μ_f` é uniforme (ou seja, `μ_f = (I/√8)·μ_{Haar}` no círculo)»,
com a nota de que a prova formal está em `FaseMedida.lean`.

---

## Divergências já conhecidas (estado após esta rodada)

| Item | Estado |
|---|---|
| `μ_f` não construída como medida em `𝕋` | **Resolvida**: `muCirc` (`FaseMedida.lean`), `μ_f = √8·μ̃_f` |
| «massa pontual» virou `FourPowers` | **Mantida** como ressalva de redação (definição do próprio texto) |
| III.12.6 só tinha versão `C²(ℝ)` | **Resolvida**: `upper_count_pow_on`, `lower_count_pow_on` |
| III.12.8(b) sem equivalência com `μ_f` uniforme | **Resolvida**: `psi_const_iff_muCirc` e `limit_iff_muCirc_on` |

## Observações de redação (aprovadas e aplicadas)

1. III.11.1: `N ≥ 1` explicitado na equivalência e na identidade do ínfimo.
2. III.11.3: caso `I(f) = 0` com as três conclusões.
