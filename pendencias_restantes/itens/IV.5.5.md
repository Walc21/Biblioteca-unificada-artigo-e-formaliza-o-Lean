> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# IV.5.5. teorema — reversão aproximada quantizada

## Estado atual — 13/11/2026

- Estado: **aberto; não há prova nova declarada**.
- Responsável: agente em execução.
- Status no mapa atual: `nao_formalizado_no_acervo`.
- TeX atual: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.5`,
  linha 922, página 90 neste ponto de controle.

Não usar a cota inversa refutada de IV.5.4. Buscar uma prova independente; se indispensável, registrar a dependência falsa como bloqueio.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 922, rótulo `map:artigo_3:5.5`; PDF unificado, p. 90.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
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

**Diferença atual:** O teorema completo ainda não foi formalizado. As definições de agenda, erro, Besov e módulo já existem em Pendencias; falta provar este enunciado, não aguardar a criação dessas definições.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): `Fase3.assembly_dense` / `errP_le` para a aproximação; quantização racional é nova.


## Contexto e reaproveitamento

Depende de IV.5.1–5.4; quantização racional nova.
