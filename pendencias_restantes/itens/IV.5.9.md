> **Instruções atuais para Codex e Antigravity:** [../../AGENTS.md](../../AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# IV.5.9. teorema — agudeza por um pente de tendas

## Estado atual — 13/11/2026

- Estado: **formalizado, revisado, integrado e compilado**.
- Autoria da contribuição: Gemini; integração e revisão: Codex.
- Status no mapa atual: `formalizado_compilado`.
- TeX atual: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.9`, linha 1178.
- Fonte integrado: `lean4/ambientes/artigo_2/Pendencias/Pente.lean`, declaração
  `Pendencias.PenteGemini.critical_tent_comb` (linha 1194).
- Evidência: `colaboracao/codex/REVISAO_IV_5_9.md`, `lake build Pendencias`,
  auditoria agregada e gate dos três ambientes em
  `compilar_pendencias/logs/20261113-142704/`.

`omega2`, `BesovInf` e `BesovQ` já existem em `Pendencias/Inversa.lean`;
`Sigma`/`pErr` em `Agenda.lean`, `rateInf` em `Endpoint.lean` e `rateQ` em
`Taxa.lean`. Não aguardar essas definições ou qualquer processo do Codex.
A atribuição anterior do Gemini está concluída; o agente atual pode trabalhar em todas as frentes.

## Dossiê recebido — referência matemática, não ordens atuais

O enunciado abaixo foi preservado. Estados, declarações ausentes, dependências,
linhas e páginas do diagnóstico original podem estar superados; valem o cabeçalho
atual e os fontes atuais. Instruções de desenvolvimento seguem o AGENTS.md da raiz.

- **Onde no TeX:** `tex/partes/artigo_3.tex`, linha 1178, rótulo `map:artigo_3:5.9`; PDF unificado, p. 93.
- **Categoria de origem (histórica) N:** Sem Lean: nenhuma declaração localizada para este enunciado.
- **Status no mapa:** `nao_formalizado_no_acervo`.
- **Dependências / ordem:** Construção do pente de tendas; definição de B^θ_{∞,r}.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[agudeza por um pente de tendas]

Fixe $0<\alpha\le\gamma$ e ponha
$\theta_*=\alpha/(\alpha+\gamma)$. Existe
$f\in C([0,1])$ e uma constante $C$ tais que, para a biblioteca original sob
$H(N)=\lceil CN^\gamma\rceil$,
\begin{equation}
 e_N^{\Library,H}(f)\le CN^{-\alpha},
 
\end{equation}
mas
\begin{equation}
 f\notin B^\theta_{\infty,\infty}\quad(\theta>\theta_*),
 \qquad
 f\notin B^{\theta_*}_{\infty,r}\quad(0<r<\infty).
 
\end{equation}
\end{theorem}
```

**Declaração Lean principal:**
`Pendencias.PenteGemini.critical_tent_comb` em `Pendencias/Pente.lean`.

**Correspondência verificada:** o teorema completo prova continuidade em `[0,1]`, taxa
para todo `N ≥ 1` sob a agenda indicada, não pertencimento a `BesovInf θ` para
`θ > α/(α+γ)` e não pertencimento a `BesovQ` no expoente crítico para todo
`0 < r < ∞`. A construção usa a biblioteca original com inclinações locais não
nulas.

**Revisão de fidelidade:** reutiliza `pErr`, `Sigma`, `AdmNH`, `omega2`, `BesovInf` e
`BesovQ` existentes. Hipóteses, domínio e conclusões coincidem com o TeX atual;
nenhum enunciado matemático foi alterado. A cópia integrada foi apenas reformatada
em linhas Lean de até 100 colunas; seu conteúdo sem espaços coincide com a entrega.


## Contexto e reaproveitamento

Pente de tendas; usar `omega2`, `BesovInf/BesovQ`, `rateQ/rateInf` de `Pendencias/`. Cotas inferiores de ω₂.
