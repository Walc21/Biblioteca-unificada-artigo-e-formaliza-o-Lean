# Lacunas de prova em Lean: Parte IV (artigo_3)

21 caso(s) cujo enunciado do volume não está integralmente provado por uma declaração Lean existente. Marque `[x]` quando o caso for fechado e atualize o `status` em `mapas/correspondencia_completa.json`.

## [x] IV.3.1. proposicao — aninhamento da agenda

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 81, rótulo `map:artigo_3:3.1`; PDF unificado, p. 80.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Definições de agenda `H`, classe `Σ_N^{L,H}(K)` e erro `e_N^{L,H}`.

**Enunciado no volume (TeX):**

```latex
\begin{proposition}[aninhamento da agenda]

Se $H$ é não decrescente, então
\begin{equation}
 \Sigma_N^{\Library,H}(K)
 \subseteq\Sigma_{N+1}^{\Library,H}(K)
 \quad\text{e}\quad
 e_{N+1}^{\Library,H}(f)\le e_N^{\Library,H}(f)\le\|f\|_\infty.
 
\end{equation}
Para cada $N$, o ínfimo em \eqref{artigo_3:eq:pointed-error} é atingido.
\end{proposition}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): Aninhamento segue de `jointErr_succ_N_le` (III.3.14) com `H` não decrescente; atingimento do ínfimo por finitude do catálogo (III.3.23).


**Fechado em 11/11/2026.** Definições `Sigma`, `pErr` formalizadas sobre K=[0,1] (domínio de `jointErr`); inclusão, monotonia, cota por ‖f‖ e atingimento do ínfimo (catálogo finito), além da fórmula min{‖f‖, E_{N,H(N)}}. Declarações: `Pendencias.Agenda.schedule_nesting` (`lean4/ambientes/artigo_2/Pendencias/Agenda.lean`), `Pendencias.Agenda.pErr_eq_min` (`lean4/ambientes/artigo_2/Pendencias/Agenda.lean`). Compilado com `lake build Pendencias` em `lean4/ambientes/artigo_2`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound` (`axiomas_pendencias.log`).
---

## [ ] IV.3.2. teorema — redução exata às escalas diádicas

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 133, rótulo `map:artigo_3:3.2`; PDF unificado, p. 80.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.3.1; definição de `a_{α,q}` (norma de ℓ^q com pesos 2^{rα}).

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[redução exata às escalas diádicas]

Para toda agenda não decrescente, $\alpha>0$ e $0<q\le\infty$,
\begin{equation}
 \mathfrak a_{\alpha,q}^{\Library,H}(f)
 \asymp_{\alpha,q}
 \left\|\bigl(2^{r\alpha}
 e_{2^r}^{\Library,H}(f)\bigr)_{r\ge0}\right\|_{\ell^q},
 
\end{equation}
com a interpretação usual por supremo quando $q=\infty$. As constantes não
dependem de $f$ nem de $H$.
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): Monotonia em N (IV.3.1) e comparação entre somas diádicas e somas em N.

---

## [ ] IV.3.3. proposicao — falha exata de homogeneidade

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 166, rótulo `map:artigo_3:3.3`; PDF unificado, p. 80.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.3.1; definição de `a_{α,q}`.

**Enunciado no volume (TeX):**

```latex
\begin{proposition}[falha exata de homogeneidade]

Suponha $K=[0,1]$ e $H(1)\ge2$. O funcional
$\|f\|_\infty+\mathfrak a_{\alpha,q}^{\Library,H}(f)$ não é homogêneo sobre
$C(K)$ e, portanto, não é uma quase-norma. Mais precisamente, para
$f(x)=x$ e $c=\sqrt2$,
\begin{equation}
 \mathfrak a_{\alpha,q}^{\Library,H}(f)=0,
 \qquad
 \mathfrak a_{\alpha,q}^{\Library,H}(cf)>0.
 
\end{equation}
\end{proposition}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): III.3.21 (`no_minimizer`: √2 não é realizado por átomo racional) é o ingrediente aritmético.

---

## [ ] IV.4.1. lema — Jackson racional com altura explícita

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 277, rótulo `map:artigo_3:4.1`; PDF unificado, p. 82.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Espaços de Besov B^s_{∞,∞}(K), expoente ν_s, constantes C_K.

**Enunciado no volume (TeX):**

```latex
\begin{lemma}[Jackson racional com altura explícita]

Seja $f\in B^s_{\infty,\infty}(K)$, $R=\|f\|_\infty$. Existe
$n_0=n_0(f,K,s)$ tal que, para toda potência de dois $n=2^r\ge n_0$ e todo
inteiro
\[
 H\ge\max\{C_Kn^{\nu_s},16(R+1)\}
\]
que satisfaça
\begin{equation}
 H\ge\max\{2,k_0+r+1,
      \max_{0\le j<n}|2^rm_0+j|+1\},
 
\end{equation}
existe $g_{n,H}\in\Aclass_{n,H}(K)$ tal que
\begin{equation}
 \|f-g_{n,H}\|_\infty
 \le 2C_W\omega_2(f,L/n)_{\infty,K}
      +\frac{C(R+1)}{H},
 
\end{equation}
onde $C$ é absoluto e $C_W$ é a constante de Whitney.

Além disso, existe $A_{K,s}\ge1$, independente de $f$, com a seguinte versão
uniforme. Se $B\ge1$, $\|f\|_{B^s_{\infty,\infty}(K)}^*\le B$, $n=2^r\ge2$
e
\begin{equation}
 H\ge A_{K,s}(B+1)n^{\nu_s},
 
\end{equation}
então todas as conclusões anteriores valem sem limiar dependente de $f$ e com
o último termo de \eqref{artigo_3:eq:rational-jackson-height} igual a
$8(B+1)/H$. A constante $A_{K,s}$ também torna automática a condição
geométrica \eqref{artigo_3:eq:height-geometry-condition}.
\end{lemma}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): III.3.16 (controle simultâneo) é o caso C² com s = 2.

---

## [ ] IV.4.2. teorema — direção direta com altura aritmética

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 398, rótulo `map:artigo_3:4.2`; PDF unificado, p. 83.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.4.1; IV.3.2.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[direção direta com altura aritmética]

Se $0<s<2$, então as seguintes inclusões de conjuntos valem:
\begin{align}
 B^s_{\infty,\infty}(K)
 &\subset
 \mathscr A^s_\infty(\Library,H_{s,0}),
 \\
 B^s_{\infty,q}(K)
 &\subset
 \mathscr A^s_q(\Library,H_{s,0}),
 &&0<q<\infty,\qquad 0<s<1,
 \\
 B^s_{\infty,q}(K)
 &\subset
 \mathscr A^s_q(\Library,H_{s,\kappa}),
 &&0<q<\infty,\qquad 1\le s<2,\qquad\kappa>1/q.
 
\end{align}
Em particular, para $s\ge1$, o endpoint $q=\infty$ admite
$H(N)=O_K(N^s)$; para $q<\infty$, basta acrescentar um fator logarítmico
crítico. Como
alternativa sem logaritmo, para qualquer $\eta>0$ pode-se substituir
$H_{s,\kappa}$ em \eqref{artigo_3:eq:direct-critical-log} por
\begin{equation}
 \widetilde H_{s,\eta}(N)
 =\left\lceil C_K(N+1)^{\max\{1,s+\eta\}}\right\rceil.
 
\end{equation}
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.4.3. corolario — imersões quantitativas uniformes sobre bolas

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 453, rótulo `map:artigo_3:4.3`; PDF unificado, p. 84.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.4.1, IV.4.2.

**Enunciado no volume (TeX):**

```latex
\begin{corollary}[imersões quantitativas uniformes sobre bolas]

Para $B\ge1$ e $\kappa\ge0$, defina
\begin{equation}
 \widehat H_{s,\kappa}^{[B]}(N)
 =\left\lceil A_{K,s}(B+1)(N+1)^{\nu_s}
        [\log(eN)]^\kappa\right\rceil .
 
\end{equation}
Existem constantes independentes de $B$ e de $f$ tais que
\begin{align}
 \sup_{\|f\|_{B^s_{\infty,\infty}(K)}^*\le B}
 \mathfrak a_{s,\infty}^{\Library,
       \widehat H_{s,0}^{[B]}}(f)
 &\le C_{K,s}(B+1), &&0<s<2,\\
 \sup_{\|f\|_{B^s_{\infty,q}(K)}^*\le B}
 \mathfrak a_{s,q}^{\Library,
       \widehat H_{s,0}^{[B]}}(f)
 &\le C_{K,s,q}(B+1), &&0<s<1,\quad0<q<\infty,
 \\
 \sup_{\|f\|_{B^s_{\infty,q}(K)}^*\le B}
 \mathfrak a_{s,q}^{\Library,
       \widehat H_{s,\kappa}^{[B]}}(f)
 &\le C_{K,s,q,\kappa}(B+1),
 &&1\le s<2,\quad0<q<\infty,\quad\kappa>1/q.
 
\end{align}
Assim, cada bola de Besov é enviada uniformemente a uma bola do funcional de
taxa sob uma única agenda, sem qualquer limiar dependente da função.
\end{corollary}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [x] IV.4.5. corolario — endpoint $C^2$

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 518, rótulo `map:artigo_3:4.5`; PDF unificado, p. 84.
- **Categoria T:** Corolário a transportar: existe o resultado-base em Lean, falta instanciá-lo nas definições deste artigo.
- **Status no mapa:** `corolario_a_transportar`.
- **Dependências / ordem:** Ponte de regularidade; IV.3.1; IV.3.2.

**Enunciado no volume (TeX):**

```latex
\begin{corollary}[endpoint $C^2$]

Na raiz $K=[0,1]$, seja
$\mathcal F_{R,M}=\{f\in C^2[0,1]:\|f\|_\infty\le R,
\|f''\|_\infty\le M\}$ e
\[
 C_H=\max\{4(R+1),\,2(4R+M/2+1)\}.
\]
Com $H_2(N)=\lceil C_HN^2\rceil$,
\begin{equation}
 \sup_{f\in\mathcal F_{R,M}}
 \mathfrak a_{2,\infty}^{\Library,H_2}(f)
 \le\max\left\{R,\frac{M+4}{2}\right\}.
 
\end{equation}
As montagens que realizam a cota para $N\ge2$ usam
$O_{R,M}(N\log(2N))$ bits nos três formatos prefix-free do
segundo artigo \citep{artigo_2-oliveiraII}.
\end{corollary}
```

**Declarações Lean associadas (assinatura):**

`Dyadic.Lib.simultaneous_control` — `lean4/ambientes/base_integrada/Unified/Consolidado/Sec7/Simultaneous.lean`, linha 477

```lean
fixed and `C_H = max{4(R+1), 2(C₀+1)}`.  For every dyadic power `n = 2^r ≥ 2` and every
`f ∈ 𝓕_{R,M}`, the assembly `g_n` (dyadic interpolant of the nodal values `v_j ∈ G_j^{(n)}`
nearest to `f(j/n)`, ties broken towards the smaller grid point) has exactly `n` leaves and
satisfies (72) `‖f - g_n‖ ≤ (M+4)/(8n²)` and (73) `ht_max(g_n) ≤ C_H n²`; in the three formats
of Theorem 7.12 its length is `O_{R,M}(n log(2n))` (74); and for every `N ≥ 2`,
`E_{N,⌈C_H N²⌉}(f) < (M+4)/(2N²)` (75). -/
theorem simultaneous_control (R M : ℝ) :
    (∀ f ∈ FRM R M, ∀ r : ℕ, 1 ≤ r →
      IsAssemblyRep (Icc 0 1) (gN f r) (leavesN f r) ∧ (leavesN f r).card = 2 ^ r ∧
      gN f r ∈ Asm (Icc 0 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |f x - gN f r x| ≤ (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2)) ∧
      (∀ a ∈ leavesN f r, (a.height : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2) ∧
      (∀ j : ℕ, ((vNode f r j : ℚ) : ℝ) ∈ altGrid r j ∧
        ∀ w ∈ altGrid r j, |((vNode f r j : ℚ) : ℝ) - f (j / 2 ^ r)| ≤ |w - f (j / 2 ^ r)| ∧
          (|((vNode f r j : ℚ) : ℝ) - f (j / 2 ^ r)| = |w - f (j / 2 ^ r)| →
            ((vNode f r j : ℚ) : ℝ) ≤ w))) ∧
    (∃ C : ℝ, ∀ f ∈ FRM R M, ∀ r : ℕ, 1 ≤ r →
      ((streamAtom (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        C * 2 ^ r * Real.logb 2 (2 * 2 ^ r) ∧
      ((streamStr (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        C * 2 ^ r * Real.logb 2 (2 * 2 ^ r) ∧
      ((streamRat (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        C * 2 ^ r * Real.logb 2 (2 * 2 ^ r)) ∧
    (∀ f ∈ FRM R M, ∀ N : ℕ, 2 ≤ N →
      jointError (Icc 0 1) N ⌈CH R M * (N : ℝ) ^ 2⌉₊ f <
        ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2)))
```

`Dyadic.Lib.precision_height` — `lean4/ambientes/base_integrada/Unified/Consolidado/Sec7/Precision.lean`, linha 71

```lean
/-- **Corollary 7.17** (sufficient height for a prescribed precision).  With
`n_ε = 2^{⌈log₂ max{2, √((M+4)/(8ε))}⌉}` and `H_ε = ⌈C_H n_ε²⌉`, uniformly for `f ∈ 𝓕_{R,M}`:
(83) `E_{n_ε, H_ε}(f) ≤ ε` and in particular `H_{ε,n_ε}(f) ≤ H_ε`;
(84) `n_ε = O_{R,M}(ε^{-1/2})`, `H_ε = O_{R,M}(ε^{-1})`;
(85) the three formats of the assembly `g_{n_ε}` of Theorem 7.16 have length
`O_{R,M}(ε^{-1/2} log(2/ε))`.  The asymptotic bounds are stated for `0 < ε ≤ 1`. -/
theorem precision_height (R M : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∀ f ∈ FRM R M,
      jointError (Icc 0 1) (nEps M ε) (HEps R M ε) f ≤ ENNReal.ofReal ε ∧
      minHeight (Icc 0 1) ε (nEps M ε) f ≤ HEps R M ε) ∧
    (∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (nEps M ε : ℝ) ≤ C / Real.sqrt ε ∧ (HEps R M ε : ℝ) ≤ C / ε) ∧
    (∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ f ∈ FRM R M,
      ((streamAtom (leafAtom f (rEps M ε)) (nEps M ε)).length : ℝ) ≤
        C / Real.sqrt ε * Real.logb 2 (2 / ε) ∧
      ((streamStr (leafAtom f (rEps M ε)) (nEps M ε)).length : ℝ) ≤
        C / Real.sqrt ε * Real.logb 2 (2 / ε) ∧
      ((streamRat (leafAtom f (rEps M ε)) (nEps M ε)).length : ℝ) ≤
        C / Real.sqrt ε * Real.logb 2 (2 / ε))
```

**O que difere:** O resultado-base existe: `Dyadic.Lib.simultaneous_control` e `Dyadic.Lib.precision_height` (que é o caso C² com `FRM`). Falta transportá-lo para as definições de agenda `H₂(N) = ⌈C_H N²⌉`, erro `a_{2,∞}` e classe do Artigo 3, e herda a ponte de regularidade (a classe `FRM` é C² na reta).

**O que provar:** Depois de IV.3.1–IV.3.2 e da ponte de regularidade: provar `sup_{f∈𝓕_{R,M}} a_{2,∞}^{L,H₂}(f) ≤ max{R, (M+4)/2}` a partir de `precision_height`; a cota `N log N` de bits vem de III.3.16.


**Fechado em 11/11/2026.** Funcional `rateInf` (𝔞_{α,∞}) e agenda `H2 R M N = ⌈C_H N²⌉` definidos; sup sobre `FRMIcc R M` (C² só em [0,1]) de 𝔞_{2,∞} ≤ max{R,(M+4)/2}; para N ≥ 2, montagem admissível com códigos ≤ C_b N log₂(2N). Base: `joint_all_N_Icc`, `joint_budget_Icc`, `pErr_eq_min`. Declarações: `Pendencias.Agenda.c2_endpoint`, `Pendencias.Agenda.c2_endpoint_bits` (`lean4/ambientes/artigo_2/Pendencias/Endpoint.lean`). `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.
---

## [x] IV.4.6. proposicao — piso aritmético uniforme

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 555, rótulo `map:artigo_3:4.6`; PDF unificado, p. 85.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Definição de `dist(a_H, 𝒬_H)`; IV.3.1.

**Enunciado no volume (TeX):**

```latex
\begin{proposition}[piso aritmético uniforme]

Para cada $H\ge2$, seja $a_H=1/(2H)$ e $f_H\equiv a_H$ em $K$. Então, para
todo $N$,
\begin{equation}
 e_N^{\Library,H}(f_H)
 \ge\operatorname{dist}(a_H,\mathcal Q_H)
 =\frac1{2H}.
 
\end{equation}
Consequentemente, se uma classe contém todas as constantes
$f\equiv a$, $|a|\le1/4$, e satisfaz
$\sup_f e_N^{\Library,H}(f)\le C N^{-s}$, então
$H(N)\ge(2C)^{-1}N^s$ para todo $N$ com $H(N)\ge2$.
\end{proposition}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): `QH` e `card_QH_le` (Fase3/Artigo); distância de 1/(2H) a 𝒬_H é cálculo com alturas.


**Fechado em 11/11/2026.** Piso e_N ≥ 1/(2H(N)), dist(1/(2H), 𝒬_H) = 1/(2H) e a consequência H(N) ≥ (2C)⁻¹N^s (para N ≥ 1), sobre K=[0,1]. Declarações: `Pendencias.Agenda.arithmetic_floor` (`lean4/ambientes/artigo_2/Pendencias/Agenda.lean`), `Pendencias.Agenda.infDist_QH` (`lean4/ambientes/artigo_2/Pendencias/Agenda.lean`), `Pendencias.Agenda.height_lower_bound` (`lean4/ambientes/artigo_2/Pendencias/Agenda.lean`). Compilado com `lake build Pendencias` em `lean4/ambientes/artigo_2`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound` (`axiomas_pendencias.log`).
---

## [ ] IV.5.1. definicao — biblioteca marcada completa

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 756, rótulo `map:artigo_3:5.1`; PDF unificado, p. 87.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Definição de átomos marcados (quádruplas com s = 0 permitido).

**Enunciado no volume (TeX):**

```latex
\begin{definition}[biblioteca marcada completa]

A biblioteca $\Library^\square$ é formada pelas quádruplas marcadas
\begin{equation}
 (k,m,y_0,s)\in\Nzero\times\mathbb Z\times\mathbb Q\times\mathbb Q,
 
\end{equation}
com o mesmo segmento \eqref{artigo_3:eq:inherited-atom} e a mesma altura
\eqref{artigo_3:eq:inherited-height}. A marca $(k,m)$ é conservada na decodificação,
inclusive quando $s=0$. Denote por $\Aclass^\square(K)$ suas montagens
contínuas e por $\Aclass^\square_{N,H}(K)$ aquelas com no máximo $N$
folhas e altura atômica no máximo $H$.
\end{definition}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): `Artigo.Atom`/`Dyadic.Lib.Atom` como base; é preciso um tipo novo com marca.

---

## [ ] IV.5.2. teorema — reversibilidade rasa exata

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 793, rótulo `map:artigo_3:5.2`; PDF unificado, p. 88.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.5.1.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[reversibilidade rasa exata]

Uma função na forma reduzida \eqref{artigo_3:eq:reduced-relu-reverse} pertence a
$\Aclass^\square([0,1])$ se e somente se
\begin{equation}
 c,q,a_1,\ldots,a_M\in\mathbb Q,
 \qquad
 \tau_1,\ldots,\tau_M\in\mathbb D.
 
\end{equation}
Nessas condições, $\mathcal T(\{\tau_1,\ldots,\tau_M\})$ é a única árvore
menos refinada que realiza $R$. Se $N_{\rm can}(R)$ é seu número de folhas e
$d_j$ é a profundidade diádica reduzida de $\tau_j$, então
\begin{equation}
 M+1\le N_{\rm can}(R)
 \le 1+\sum_{j=1}^{M}d_j.
 
\end{equation}
A função pertence à biblioteca original $\Aclass([0,1])$ exatamente quando,
além de \eqref{artigo_3:eq:marked-reversal-conditions},
\begin{equation}
 \sigma_i\ne0\qquad(0\le i\le M).
 
\end{equation}
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): `Dyadic.Lib.relu_mem_Asm` e `assembly_eq_relu` (I.4.3) cobrem a direção sem marca; a marca e a unicidade da árvore menos refinada são novas.

---

## [ ] IV.5.3. definicao — altura canônica de rede

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 845, rótulo `map:artigo_3:5.3`; PDF unificado, p. 88.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.5.2.

**Enunciado no volume (TeX):**

```latex
\begin{definition}[altura canônica de rede]

Para uma rede que satisfaz \eqref{artigo_3:eq:marked-reversal-conditions}, defina
\begin{equation}
 H_{\rm can}(R)=
 \max_{J_{k,m}\in\operatorname{leaf}(\mathcal T(S))}
 \max\{2,k+1,|m|+1,\height(R(x_{k,m})),\height(R'|_{J_{k,m}})\}.
 
\end{equation}
\end{definition}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.5.4. proposicao — forma ancorada e comprimento estrutural

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 863, rótulo `map:artigo_3:5.4`; PDF unificado, p. 88.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.5.1–IV.5.3.

**Enunciado no volume (TeX):**

```latex
\begin{proposition}[forma ancorada e comprimento estrutural]

Se $g\in\Aclass^\square_{N,H}([0,1])$, sua forma reduzida possui
$M\le N-1$ hinges e pode ser escrita, tomando o centro $x_*$ da folha mais à
esquerda, como
\begin{equation}
 g(x)=g(x_*)+\sigma_0(x-x_*)
      +\sum_{j=1}^{M}(\sigma_j-\sigma_{j-1})\rho(x-\tau_j).
 
\end{equation}
Os valores $g(x_*)$ e $\sigma_i$ têm altura no máximo $H$, os saltos têm
altura no máximo $2H^2$, e os pontos diádicos são transmitidos por seus pares
estruturais. Consequentemente, existe uma codificação prefix-free da forma
ancorada com
\begin{equation}
 L_{\rm ReLU}^{\rm anc}(g)=O(N\log(2H)).
 
\end{equation}

Na direção contrária, se os coeficientes de
\eqref{artigo_3:eq:reduced-relu-reverse} têm altura no máximo $W$ e as quebras têm
profundidade no máximo $D$, então
\begin{equation}
 \log_2 H_{\rm can}(R)
 \le C\bigl[M\log(2W)+D+\log(M+1)\bigr]
 
\end{equation}
para uma constante universal $C$.
\end{proposition}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): `relu_parameters_height` (I.4.4) dá as alturas dos parâmetros.

---

## [ ] IV.5.5. teorema — reversão aproximada quantizada

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 922, rótulo `map:artigo_3:5.5`; PDF unificado, p. 89.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.5.1–IV.5.4.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[reversão aproximada quantizada]

Seja $R$ como em \eqref{artigo_3:eq:reduced-relu-reverse}, agora com parâmetros reais,
e suponha
\begin{equation}
 |c|,|q|,|a_1|,\ldots,|a_M|\le W,
 \qquad W\ge1.
 
\end{equation}
Para todo $0<\varepsilon\le1$, existe uma montagem da biblioteca original
$g_\varepsilon\in\Aclass([0,1])$ tal que
\begin{align}
 \|R-g_\varepsilon\|_\infty&\le\varepsilon,
 \\
 |\Lambda(g_\varepsilon)|&\le1+MD_\varepsilon,
 \qquad
 D_\varepsilon=
 \left\lceil\log_2\frac{C(M+1)(W+1)}{\varepsilon}\right\rceil,
 \\
 \height_{\max}(g_\varepsilon)
 &\le
 C(M+1)^3(W+1)^3\varepsilon^{-2},
 
\end{align}
onde $C$ é universal. A conclusão permanece válida quando $R$ possui regiões
planas.
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): `Fase3.assembly_dense` / `errP_le` para a aproximação; quantização racional é nova.

---

## [ ] IV.5.6. corolario — redes profundas medidas pela função realizada

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 984, rótulo `map:artigo_3:5.6`; PDF unificado, p. 90.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.5.5; noção de região afim máxima de uma rede ReLU.

**Enunciado no volume (TeX):**

```latex
\begin{corollary}[redes profundas medidas pela função realizada]

Se uma rede ReLU univariada arbitrária realiza uma função $F$ com $R(F)$
regiões afins máximas, norma uniforme no máximo $B$ e constante de Lipschitz
no máximo $L_F$, então o \cref{artigo_3:thm:quantized-approximate-reverse} vale com
\begin{equation}
 M=R(F)-1,
 \qquad
 W\le2\max\{1,B,L_F\}.
 
\end{equation}
\end{corollary}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.5.7. teorema — imersão inversa sob crescimento de Lipschitz

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1087, rótulo `map:artigo_3:5.7`; PDF unificado, p. 91.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Definição de Lipschitz para a família 𝒢_N; ω₂.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[imersão inversa sob crescimento de Lipschitz]

Sejam $\mathcal G_N\subset C([0,1])$ famílias de aproximantes tais que
\begin{equation}
 \operatorname{Lip}(g)\le C_LN^\gamma
 \qquad(g\in\mathcal G_N),
 \qquad \gamma\ge0,
 
\end{equation}
e defina
$e_N^{\mathcal G}(f)=\inf_{g\in\mathcal G_N}\|f-g\|_\infty$. Se
\begin{equation}
 A_\alpha(f):=\sup_{N\ge1}N^\alpha e_N^{\mathcal G}(f)<\infty,
 \qquad \alpha>0,
 
\end{equation}
então, com
\begin{equation}
 \theta_* = \frac{\alpha}{\alpha+\gamma},
 
\end{equation}
vale
\begin{equation}
 \omega_2(f,t)_\infty
 \le C_{\alpha,\gamma}(A_\alpha(f)+C_L)t^{\theta_*},
 \qquad 0<t\le\frac12.
 
\end{equation}
Consequentemente,
\begin{equation}
 f\in B^{\theta_*}_{\infty,\infty}([0,1])
 \quad\text{e}\quad
 f\in B^\theta_{\infty,r}([0,1])
 \quad(0<\theta<\theta_*,\ 0<r\le\infty).
 
\end{equation}
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.5.8. corolario — aplicação às agendas diretas

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1142, rótulo `map:artigo_3:5.8`; PDF unificado, p. 92.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.5.7, IV.4.2.

**Enunciado no volume (TeX):**

```latex
\begin{corollary}[aplicação às agendas diretas]

Se $H(N)\le C N^\gamma$, então
\begin{equation}
 \mathscr A_q^\alpha(\Library,H)
 \subset B^{\alpha/(\alpha+\gamma)}_{\infty,\infty}([0,1]),
 \qquad 0<q\le\infty.
 
\end{equation}
Para as agendas $H_{s,0}$ da \cref{artigo_3:sec:direct-height}, isso dá
\begin{equation}
 \mathscr A_q^s(\Library,H_{s,0})
 \subset B^{\vartheta_s}_{\infty,\infty},
 \qquad
 \vartheta_s=
 \begin{cases}
 s/(s+1),&0<s<1,\\
 1/2,&1\le s<2.
 \end{cases}
 
\end{equation}
Se a agenda possui ainda um fator logarítmico, a mesma conclusão vale para
toda ordem estritamente menor que $\vartheta_s$.
\end{corollary}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.5.9. teorema — agudeza por um pente de tendas

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1178, rótulo `map:artigo_3:5.9`; PDF unificado, p. 92.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Construção do pente de tendas; definição de B^θ_{∞,r}.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[agudeza por um pente de tendas]

Fixe $0<\alpha\le\gamma$ e ponha
$\theta_*=\alpha/(\alpha+\gamma)$. Existe
$f\in C([0,1])$ e uma constante $C$ tais que, para a biblioteca original sob
$H(N)=\lceil CN^\gamma\rceil$,
\begin{equation}
 e_N^{\Library,H}(f)\le CN^{-\alpha},
 
\end{equation}
mas
\begin{equation}
 f\notin B^\theta_{\infty,\infty}\quad(\theta>\theta_*),
 \qquad
 f\notin B^{\theta_*}_{\infty,r}\quad(0<r<\infty).
 
\end{equation}
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.5.10. lema — desigualdade inversa universal

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1287, rótulo `map:artigo_3:5.10`; PDF unificado, p. 93.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Definição de ω₂ e do funcional `R_N^{L,H}`.

**Enunciado no volume (TeX):**

```latex
\begin{lemma}[desigualdade inversa universal]

Para toda agenda, toda $f\in C([0,1])$ e todo $N\ge2$,
\begin{equation}
 \frac14\omega_2(f,N^{-1})_\infty
 \le \mathcal R_N^{\Library,H}(f).
 
\end{equation}
\end{lemma}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): Desigualdade triangular para segundas diferenças (elementar).

---

## [ ] IV.5.12. teorema — Jackson racional para o funcional de realização

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1314, rótulo `map:artigo_3:5.12`; PDF unificado, p. 93.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.4.1, IV.5.10.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[Jackson racional para o funcional de realização]

Se $0<s<2$ e $f\in B^s_{\infty,\infty}([0,1])$, então, para toda potência de
dois $N$ suficientemente grande e toda altura que satisfaz as hipóteses do
\cref{artigo_3:lem:rational-jackson-height},
\begin{equation}
 \frac14\omega_2(f,N^{-1})_\infty
 \le \mathcal R_N^{\Library,H}(f)
 \le C_0\omega_2(f,N^{-1})_\infty+\frac{C_f}{H(N)},
 
\end{equation}
onde $C_0$ é universal e $C_f$ depende apenas de $\|f\|_\infty$ e das
constantes fixadas na racionalização.
Se $\|f\|_{B^s_{\infty,\infty}}^*\le B$, $B\ge1$, e
$H(N)\ge\widehat H_{s,0}^{[B]}(N)$, a mesma estimativa vale para toda potência
diádica $N\ge2$, com $C_f/H(N)$ substituído por $C(B+1)/H(N)$ e constantes
independentes de $f$.
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.5.13. teorema — caracterização pelo funcional de realização

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1362, rótulo `map:artigo_3:5.13`; PDF unificado, p. 94.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.4.2, IV.5.8, IV.5.12.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[caracterização pelo funcional de realização]

Para $0<s<2$, valem as igualdades de conjuntos
\begin{align}
 B^s_{\infty,\infty}([0,1])
 &=\mathscr R_\infty^s(\Library,H_{s,0}),
 \\
 B^s_{\infty,q}([0,1])
 &=\mathscr R_q^s(\Library,H_{s,0}),
 &&0<q<\infty,\quad0<s<1,
 \\
 B^s_{\infty,q}([0,1])
 &=\mathscr R_q^s(\Library,H_{s,\kappa}),
 &&0<q<\infty,\quad1\le s<2,\quad\kappa>1/q.
 
\end{align}
Pode-se substituir a agenda logarítmica da última linha por qualquer agenda
com folga polinomial \eqref{artigo_3:eq:polynomial-slack-schedule}.
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---

## [ ] IV.5.14. teorema — reversibilidade estável por inclusão de redes

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1448, rótulo `map:artigo_3:5.14`; PDF unificado, p. 95.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Definição de famílias aninhadas de redes ReLU 𝒩_N.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[reversibilidade estável por inclusão de redes]

Seja $(\mathcal N_N)$ qualquer família de funções realizadas por redes ReLU
aninhada no orçamento, isto é,
\begin{equation}
 0\in\mathcal N_N,
 \qquad \mathcal N_N\subseteq\mathcal N_{N+1}
 \qquad(N\ge1),
 
\end{equation}
e suponha que, para alguma constante $c\ge1$,
\begin{equation}
 \Sigma_N^{\Library,H}([0,1])\subseteq\mathcal N_{\lceil cN\rceil}
 \qquad(N\ge1).
 
\end{equation}
Defina
\begin{equation}
 \mathcal R_N^{\mathcal N}(f)
 =\inf_{R\in\mathcal N_N}
 \left\{\|f-R\|_\infty+\omega_2(R,N^{-1})_\infty\right\}.
 
\end{equation}
Sob cada uma das agendas do
\cref{artigo_3:thm:complete-besov-reversibility}, substituir
$\mathcal R_N^{\Library,H}$ por $\mathcal R_N^{\mathcal N}$ preserva as
igualdades \eqref{artigo_3:eq:complete-reverse-endpoint}--
\eqref{artigo_3:eq:complete-reverse-critical}.
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Nenhuma declaração Lean localizada (a Fase3 do acervo é do Artigo 1, não do atual Artigo 3). Os enunciados dependem de definições (agenda, erro por agenda, Besov, ω₂) que também não existem em Lean.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —

---
