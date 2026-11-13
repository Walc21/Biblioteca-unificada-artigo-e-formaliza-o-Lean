> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# IV.5.6. corolario — redes profundas medidas pela função realizada

## Estado atual — 13/11/2026

- Estado: **aberto; não há prova nova declarada**.
- Responsável: agente em execução.
- Status no mapa atual: `nao_formalizado_no_acervo`.
- TeX atual: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.6`,
  linha 984, página 91 neste ponto de controle.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 984, rótulo `map:artigo_3:5.6`; PDF unificado, p. 91.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
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

**Diferença atual:** O teorema completo ainda não foi formalizado. As definições de agenda, erro, Besov e módulo já existem em Pendencias; falta provar este enunciado, não aguardar a criação dessas definições.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): —


## Contexto e reaproveitamento

Depende de IV.5.5; precisa de "regiões afins máximas" de rede ReLU.
