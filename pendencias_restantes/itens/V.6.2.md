> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# V.6.2. teorema — cota assintótica com nós livres

## Estado atual — 13/11/2026

- Estado: **fechado em Lean; não reabrir a prova por este diagnóstico recebido**.
- Manutenção: agente em execução.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/complemento_original.tex`, rótulo `map:complemento_original:6.2`,
  linha 57, página 99 neste ponto de controle.
- Declarações integradas (conferir hipóteses no fonte):
  - `Pendencias.NosLivres.free_knots` em `lean4/ambientes/artigo_2/Pendencias/NosLivres.lean`.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/complemento_original.tex`, linha 57, rótulo `map:complemento_original:6.2`; PDF unificado, p. 99.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `formalizado_compilado`.
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

**Declarações Lean integradas:** `Pendencias.NosLivres.free_knots`.

**O que difere:** Sem formalização localizada.

**Trabalho atual:** Nenhuma prova nova solicitada para este item fechado; preservar a correspondência documentada no cabeçalho.


## Contexto e reaproveitamento

Nós livres; equidistribuição pela densidade |f″|^{1/2}. `curvIOn` em `Pendencias/Ponte.lean` pode ajudar.
