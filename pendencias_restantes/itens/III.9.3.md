> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# III.9.3. teorema — cota grosseira de complexidade de bits

## Estado atual — 13/11/2026

- Estado: **formalizado (13/11/2026)** em `lean4/ambientes/artigo_2/Pendencias/ComplexidadeBits.lean`, teorema `DenseDP.bit_complexity_dense`; compilado e auditado (propext, Classical.choice, Quot.sound). Ressalva: custo de aritmética racional em bits é hipótese do modelo (`BitModel`).
- Responsável: agente em execução.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/artigo_2.tex`, rótulo `map:artigo_2:9.3`,
  linha 2083, página 61 neste ponto de controle.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 2083, rótulo `map:artigo_2:9.3`; PDF unificado, p. 61.
- **Categoria de origem (histórica) P:** Cobertura parcial: o Lean prova algo mais fraco ou diferente do enunciado.
- **Status no mapa:** `cobertura_parcial`.
- **Dependências / ordem:** III.9.1.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[cota grosseira de complexidade de bits]

Todos os custos racionais que aparecem na recorrência possuem numeradores e
denominadores de comprimento no máximo
\begin{equation}
 B_{\rm cost}
 =O\!\left(
 P\bigl(B_{\mathcal Z}+D+|k_0|+\log(2H)\bigr)
 +B_{\mathcal Z}+D+\log(2L)
 \right).
 
\end{equation}
Consequentemente, a versão densa sem orçamento de folhas pode ser executada em
\begin{equation}
 O\!\left(
 (S_DM^3+S_DPM^2)
 \bigl[\mathsf M_{\mathbb Z}(B_{\rm cost})
       \log(2B_{\rm cost})+L\bigr]
 \right)
 
\end{equation}
operações de bit e
\begin{equation}
 O\!\left(S_DM^2(B_{\rm cost}+L)\right)
 
\end{equation}
bits de memória quando todos os estados e fluxos são armazenados. Na versão
com até $N$ folhas, substituem-se $S_DM^3$ e $S_DM^2$ por
$S_DN^2M^3$ e $S_DNM^2$, respectivamente. Com multiplicação escolar,
$\mathsf M_{\mathbb Z}(b)=O(b^2)$.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.Setup.bit_complexity` — `lean4/ambientes/artigo_2/RequestProject/BitComplexity.lean`, linha 266

```lean
Let `B` bound the bit length `bl` of all abscissae, responses, weights and penalties, let
`P = |𝒵|` be the number of observations and `L` a bound on the stream lengths. Then every cost
`cost_𝒵(R)` occurring in the recursion — of a representation `R` rooted at a descendant `J` of
`K` within the depth budget, with atoms in `𝓛_H` and `|ser_rec(R)| ≤ L` — satisfies
`bl(cost_𝒵(R)) ≤ 2 (P (5B + 6⌈log₂H⌉ + 2(k₀+D) + 9) + 2B + 2⌈log₂L⌉ + 2) + 3`,
i.e. `bl = O(P (B_𝒵 + D + k₀ + log(2H)) + B_𝒵 + log(2L))`. -/
theorem bit_complexity {B L : ℕ}
    (hdata : ∀ p ∈ S.data, bl p.1 ≤ B ∧ bl p.2.1 ≤ B ∧ bl p.2.2 ≤ B) (hlb : bl S.lb ≤ B)
    (hls : bl S.ls ≤ B) {k r : ℕ} {m : ℤ} (hd : IsDesc S.k₀ S.m₀ k m r) {R : LTree}
    (hR : WF k m R) (hdep : r + R.depth ≤ S.D) (hh : R.maxHeight ≤ S.H) (hL : (serRec R).length ≤ L) :
    bl (S.costT R) ≤ 2 * (S.data.length * (5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 9) +
      2 * B + 2 * Nat.clog 2 L + 2) + 3
```

**O que difere:** `Setup.bit_complexity` limita o tamanho em bits dos custos racionais `B_cost`. As cotas de TEMPO e MEMÓRIA em bits do texto (produto `M_ℤ(B_cost)·log(2B_cost)` etc.) dependem de custo de multiplicação e comparação de racionais, que o Lean não modela.

**O que provar:** Estender o modelo de custo de III.9.1 com custo de operações em ℚ (multiplicação, soma, comparação, desempate shortlex) e provar a cota do enunciado.


## Contexto e reaproveitamento

Depende de III.9.1; custo de operações em ℚ.
