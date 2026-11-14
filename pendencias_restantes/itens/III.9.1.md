> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# III.9.1. teorema — complexidade em número de estados

## Estado atual — 13/11/2026

- Estado: **formalizado (13/11/2026)** em `lean4/ambientes/artigo_2/Pendencias/ComplexidadeDensa.lean`, teorema `DenseDP.state_complexity_dense` (e `dense_variable_complexity`, `dense_budget_complexity`, `dense_variable_init`, `dense_budget_init`); compilado e auditado (propext, Classical.choice, Quot.sound). Ressalva: desempate pela chave κ não está no programa denso (ver mapa).
- Responsável: agente em execução.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/artigo_2.tex`, rótulo `map:artigo_2:9.1`,
  linha 1996, página 60 neste ponto de controle.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 1996, rótulo `map:artigo_2:9.1`; PDF unificado, p. 60.
- **Categoria de origem (histórica) P:** Cobertura parcial: o Lean prova algo mais fraco ou diferente do enunciado.
- **Status no mapa:** `cobertura_parcial`.
- **Dependências / ordem:** III.7.4 (implementação).

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[complexidade em número de estados]

Suponha os custos de folha pré-computados. Uma implementação densa do
\cref{artigo_2:alg:variable-tree} usa
\begin{equation}
 O(S_DM^3)
 
\end{equation}
operações e
\begin{equation}
 O(S_DM^2)
 
\end{equation}
entradas de memória quando preserva todos os apontadores de reconstrução.
A versão com orçamento de até $N$ folhas usa
\begin{equation}
 O(S_DN^2M^3)
 
\end{equation}
operações e $O(S_DNM^2)$ entradas. Se cada custo local
\eqref{artigo_2:eq:local-loss} for calculado diretamente sobre $P$ observações, a
inicialização densa acrescenta $O(S_DPM^2)$ operações.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.Setup.state_complexity` — `lean4/ambientes/artigo_2/RequestProject/Complexity.lean`, linha 89

```lean
`S_D M³`;
(iii) with a budget of up to `N` leaves, the table has `S_D N M²` entries and the transitions
(one per internal node, triple `(u,w,v)` and budget pair `n_L + n_R = n ≤ N`) number at most
`S_D N² M³`;
(iv) computing every local loss directly over the `P` observations costs `S_D P M²` operations;
(v) with `M ≤ 36 H⁶` (Lemma 4.4), the transitions number at most `36³ S_D H¹⁸`. -/
theorem state_complexity (hH : 2 ≤ S.H) (N : ℕ) :
    (cellsD S.D ×ˢ (S.V ×ˢ S.V)).card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V)).card ≤ (2 ^ (S.D + 1) - 1) * S.V.card ^ 3 ∧
    (cellsD S.D ×ˢ (S.V ×ˢ S.V) ×ˢ Finset.Icc 1 N).card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V) ×ˢ budgetPairs N).card ≤
      (2 ^ (S.D + 1) - 1) * N ^ 2 * S.V.card ^ 3 ∧
    (cellsD S.D ×ˢ (S.V ×ˢ S.V) ×ˢ Finset.range S.data.length).card =
      (2 ^ (S.D + 1) - 1) * S.data.length * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V)).card ≤ (2 ^ (S.D + 1) - 1) * (36 ^ 3 * S.H ^ 18)
```

**O que difere:** `Setup.state_complexity` prova as cardinalidades (tabelas `O(S_D M²)`, transições `O(S_D M³)`, com orçamento `S_D N M²` e `S_D N² M³`). O texto afirma número de OPERAÇÕES e de entradas de memória de uma implementação densa; não há semântica de execução nem modelo de custo no Lean.

**O que provar:** Definir um modelo de custo (por exemplo, uma mônada de contagem de passos `TimeM`) para a implementação densa de III.7.4 e provar que ela faz `O(S_D M³)` operações e usa `O(S_D M²)` células.


## Contexto e reaproveitamento

Depende de III.7.4 (programa). Precisa de modelo de custo (mônada de contagem).
