# Lacunas de prova em Lean: Parte V (complemento)

4 caso(s) cujo enunciado do volume não está integralmente provado por uma declaração Lean existente. Marque `[x]` quando o caso for fechado e atualize o `status` em `mapas/correspondencia_completa.json`.

## [ ] V.6.1. teorema — taxa garantida em árvores

- **Onde no TeX:** `tex/partes/complemento_original.tex`, linha 27, rótulo `map:complemento_original:6.1`; PDF unificado, p. 97.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `sem_formalizacao_localizada`.
- **Dependências / ordem:** I.5.1; III.3.14.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[taxa garantida em árvores]
Se $f\in C^2(K)$, $L=|K|$, $M=\|f''\|_{\infty,K}$ e $N\ge2$, então
\begin{equation}
 \sigma_N^{\mathrm{dia}}(f)_\infty\le\frac{ML^2}{2N^2}.
 
\end{equation}
Se $N=2^r$, a constante melhora para
\begin{equation}
 \sigma_N^{\mathrm{dia}}(f)_\infty\le\frac{ML^2}{8N^2}.
 
\end{equation}
Para qualquer árvore finita $\Lambda$ e $\delta>0$, há uma montagem racional na mesma árvore cujo erro é menor que $\|f-P_\Lambda f\|_\infty+\delta$.
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Resultado original preservado no complemento; sem formalização localizada.

**O que provar:** Provar a taxa `M L²/(2N²)` (e `M L²/(8N²)` para `N = 2^r`) para erros em árvores diádicas e a existência de montagem racional na mesma árvore a custo `δ`. Possível reaproveitamento: `Fase3.errP_le` (cota `h²M/8` de interpolação em ContDiffOn) e `Dyadic.Lib.jointError`.

---

## [ ] V.6.2. teorema — cota assintótica com nós livres

- **Onde no TeX:** `tex/partes/complemento_original.tex`, linha 57, rótulo `map:complemento_original:6.2`; PDF unificado, p. 98.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `sem_formalizacao_localizada`.
- **Dependências / ordem:** Integral de |f″|^{1/2}; partições por quantis; I.5.1.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[cota assintótica com nós livres]
Para $f\in C^2[\alpha,\beta]$,
\begin{equation}
 \limsup_{N\to\infty}N^2E_N^{\mathrm{lv}}(f)
 \le\frac18\left(\int_\alpha^\beta |f''(x)|^{1/2}\dd x\right)^2.
 
\end{equation}
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Sem formalização localizada.

**O que provar:** Provar `limsup N²E_N^lv(f) ≤ (1/8)(∫|f″|^{1/2})²` para `f ∈ C²[α,β]` com nós livres (equidistribuição pela densidade |f″|^{1/2}).

---

## [ ] V.6.3. teorema — estimativa direta

- **Onde no TeX:** `tex/partes/complemento_original.tex`, linha 109, rótulo `map:complemento_original:6.3`; PDF unificado, p. 98.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `sem_formalizacao_localizada`.
- **Dependências / ordem:** Definição de B^s_{∞,∞}; V.6.1.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[estimativa direta]
Se $0<s<2$, $|K|=L$ e o seminorma em \eqref{complemento_original:eq:besov-seminorm} é finito, então, para $N\ge2$,
\begin{equation}
 \sigma_N^{\mathrm{dia}}(f)_\infty
 \le C_sL^s|f|_{B^s_{\infty,\infty}(K)}N^{-s},
 
\end{equation}
onde $C_s$ independe de $f$ e $N$. Para todo $\delta>0$, uma montagem racional com no máximo $N$ folhas alcança o lado direito de \eqref{complemento_original:eq:besov-rate} acrescido de $\delta$.
\end{theorem}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Sem formalização localizada.

**O que provar:** Provar `σ_N^dia(f) ≤ C_s L^s |f|_{B^s_{∞,∞}} N^{-s}` (0<s<2) e o refinamento racional com δ > 0. Requer a definição do seminorma de Besov.

---

## [x] V.21.1. lema — majorante local da função de Runge

- **Onde no TeX:** `tex/partes/complemento_original.tex`, linha 152, rótulo `map:complemento_original:21.1`; PDF unificado, p. 99.
- **Categoria N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `sem_formalizacao_localizada`.
- **Dependências / ordem:** Definição de f e cálculo de f″.

**Enunciado no volume (TeX):**

```latex
\begin{lemma}[majorante local da função de Runge]
Em todo intervalo fechado $J\subset[-1,1]$, o máximo de $|f''|$ é atingido em um extremo de $J$ ou em um ponto de $\{0,-0{,}2,0{,}2\}\cap J$.
\end{lemma}
```

**Declarações Lean associadas:** nenhuma.

**O que difere:** Sem formalização localizada.

**O que provar:** Provar que o máximo de |f″| da função de Runge em todo intervalo fechado J ⊂ [−1,1] ocorre num extremo de J ou em um ponto de {0, ±0,2} ∩ J. É cálculo elementar de uma função racional explícita; viável direto em Lean com `Polynomial`/`deriv`.


**Fechado em 11/11/2026.** Provado; a forma `runge_majorant` dispensa J ⊆ [-1,1]. Inclui `deriv2_runge`. Declarações: `Pendencias.Runge.runge_majorant_sub` (`lean4/ambientes/artigo_2/Pendencias/Runge.lean`), `Pendencias.Runge.runge_majorant` (`lean4/ambientes/artigo_2/Pendencias/Runge.lean`). Compilado com `lake build Pendencias` em `lean4/ambientes/artigo_2`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound` (`axiomas_pendencias.log`).
---
