> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# IV.5.14. teorema — reversibilidade estável por inclusão de redes

## Estado atual — 13/11/2026

- Estado: **fechado em Lean; não reabrir a prova por este diagnóstico recebido**.
- Manutenção: agente em execução.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.14`,
  linha 1448, página 96 neste ponto de controle.
- Declarações integradas (conferir hipóteses no fonte):
  - `Pendencias.Jackson.architecture_stable_reversibility` em `lean4/ambientes/artigo_2/Pendencias/Realizacao.lean`.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1448, rótulo `map:artigo_3:5.14`; PDF unificado, p. 96.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `formalizado_compilado`.
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

**Declarações Lean integradas:** `Pendencias.Jackson.architecture_stable_reversibility`.

**Diferença atual:** O diagnóstico de ausência foi superado pela prova integrada indicada no cabeçalho. As definições e o enunciado foram formalizados; não há nova tarefa de prova para este item.

**Trabalho atual:** Nenhuma prova nova solicitada para este item fechado; preservar a correspondência documentada no cabeçalho.


## Contexto e reaproveitamento

Depende de IV.5.13.
