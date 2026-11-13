> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# IV.5.13. teorema — caracterização pelo funcional de realização

## Estado atual — 13/11/2026

- Estado: **fechado em Lean; não reabrir a prova por este diagnóstico recebido**.
- Manutenção: agente em execução.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.13`,
  linha 1362, página 95 neste ponto de controle.
- Declarações integradas (conferir hipóteses no fonte):
  - `Pendencias.Jackson.complete_besov_reversibility` em `lean4/ambientes/artigo_2/Pendencias/Realizacao.lean`.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1362, rótulo `map:artigo_3:5.13`; PDF unificado, p. 95.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `formalizado_compilado`.
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

**Declarações Lean integradas:** `Pendencias.Jackson.complete_besov_reversibility`.

**Diferença atual:** O diagnóstico de ausência foi superado pela prova integrada indicada no cabeçalho. As definições e o enunciado foram formalizados; não há nova tarefa de prova para este item.

**Trabalho atual:** Nenhuma prova nova solicitada para este item fechado; preservar a correspondência documentada no cabeçalho.


## Contexto e reaproveitamento

Depende de IV.4.2, IV.5.8 (feito), IV.5.12.
