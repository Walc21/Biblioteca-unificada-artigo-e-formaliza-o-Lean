> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# IV.5.4. proposicao — forma ancorada e comprimento estrutural

## Estado atual — 13/11/2026

- Estado: **FECHADO com enunciado inverso corrigido** (a cota abaixo, impressa originalmente, é falsa para R(x)=x, M=0, D=0, W=1; versão correta: log₂ H_can ≤ 5[(M+1)log₂(2W)+D+log₂(M+1)]).
- Provas: `Pendencias/AlturaInversa.lean`, `FormaAncorada.lean`, `CodigoAncorado.lean`. O texto abaixo é o enunciado ORIGINAL, histórico.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.4`,
  linha 863, página 89 neste ponto de controle.

Evidência: `verificacao/lean/ContraexemploAltura.lean`. O diagnóstico não fecha o item.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 863, rótulo `map:artigo_3:5.4`; PDF unificado, p. 89.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** IV.5.1–IV.5.3.

**Enunciado no volume (TeX):**

```latex
\begin{proposition}[forma ancorada e comprimento estrutural]

Se $g\in\Aclass^\square_{N,H}([0,1])$, sua forma reduzida possui
$M\le N-1$ hinges e pode ser escrita, tomando o centro $x_*$ da folha mais à
esquerda, como
\begin{equation}
 g(x)=g(x_*)+\sigma_0(x-x_*)
      +\sum_{j=1}^{M}(\sigma_j-\sigma_{j-1})\rho(x-\tau_j).
 
\end{equation}
Os valores $g(x_*)$ e $\sigma_i$ têm altura no máximo $H$, os saltos têm
altura no máximo $2H^2$, e os pontos diádicos são transmitidos por seus pares
estruturais. Consequentemente, existe uma codificação prefix-free da forma
ancorada com
\begin{equation}
 L_{\rm ReLU}^{\rm anc}(g)=O(N\log(2H)).
 
\end{equation}

Na direção contrária, se os coeficientes de
\eqref{artigo_3:eq:reduced-relu-reverse} têm altura no máximo $W$ e as quebras têm
profundidade no máximo $D$, então
\begin{equation}
 \log_2 H_{\rm can}(R)
 \le C\bigl[M\log(2W)+D+\log(M+1)\bigr]
 
\end{equation}
para uma constante universal $C$.
\end{proposition}
```

**Declarações Lean associadas:** nenhuma.

**Diferença atual:** As definições de agenda, erro, Besov e módulo existem. A cota inversa deste item foi refutada pelo contraexemplo certificado indicado no cabeçalho; o enunciado permanece preservado.

**O que provar:** Formalizar as definições necessárias e o enunciado. Possível reaproveitamento (a verificar): `relu_parameters_height` (I.4.4) dá as alturas dos parâmetros.


## Contexto e reaproveitamento

Depende de IV.5.1–5.3 (5.1 e 5.3 feitos em `Marcada.lean`); códigos prefix-free como em `Formats.lean`.
