> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# IV.5.2. teorema — reversibilidade rasa exata

## Estado atual — 13/11/2026

- Estado: **fechado em Lean; não reabrir a prova por este diagnóstico recebido**.
- Manutenção: agente em execução.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.2`,
  linha 793, página 89 neste ponto de controle.
- Declarações integradas (conferir hipóteses no fonte):
  - `Pendencias.Marcada.RealReLU.exact_shallow_reversal` em `lean4/ambientes/artigo_2/Pendencias/ReversaoOriginal.lean`.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 793, rótulo `map:artigo_3:5.2`; PDF unificado, p. 89.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `formalizado_compilado`.
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

**Declarações Lean integradas:** `Pendencias.Marcada.RealReLU.exact_shallow_reversal`.

**Diferença atual:** O diagnóstico de ausência foi superado pela prova integrada indicada no cabeçalho. As definições e o enunciado foram formalizados; não há nova tarefa de prova para este item.

**Trabalho atual:** Nenhuma prova nova solicitada para este item fechado; preservar a correspondência documentada no cabeçalho.


## Contexto e reaproveitamento

Definições prontas em `Pendencias/Marcada.lean` (`MAtom`, `MTree`, `MAsm`, `canonShape`, `RedReLU`, `canonTree`). Falta: R ∈ 𝒜^□ ⟺ dados racionais e quebras diádicas; unicidade da árvore menos refinada; M+1 ≤ N_can ≤ 1+∑d_j; condição σ_i ≠ 0 para 𝒜.
