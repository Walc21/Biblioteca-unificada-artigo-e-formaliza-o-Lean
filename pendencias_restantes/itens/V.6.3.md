> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# V.6.3. teorema — estimativa direta

## Estado atual — 13/11/2026

- Estado: **fechado em Lean; não reabrir a prova por este diagnóstico recebido**.
- Manutenção: agente em execução.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/complemento_original.tex`, rótulo `map:complemento_original:6.3`,
  linha 109, página 99 neste ponto de controle.
- Declarações integradas (conferir hipóteses no fonte):
  - `Pendencias.Jackson.besov_direct` em `lean4/ambientes/artigo_2/Pendencias/BesovDireta.lean`.
  - `Pendencias.Jackson.besov_direct_whitney` em `lean4/ambientes/artigo_2/Pendencias/BesovDireta.lean`.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/complemento_original.tex`, linha 109, rótulo `map:complemento_original:6.3`; PDF unificado, p. 99.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `formalizado_compilado`.
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

**Declarações Lean integradas:** `Pendencias.Jackson.besov_direct`, `Pendencias.Jackson.besov_direct_whitney`.

**O que difere:** Sem formalização localizada.

**Trabalho atual:** Nenhuma prova nova solicitada para este item fechado; preservar a correspondência documentada no cabeçalho.


## Contexto e reaproveitamento

Besov B^s_{∞,∞} e Whitney; V.6.1.
