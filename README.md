<div align="center">

# Biblioteca determinística de segmentos afins racionais

### Construção, seleção exata, aproximação e normalização — com formalização em Lean 4

*Um volume de 122 páginas, 151 resultados matemáticos e mais de 40 mil linhas de Lean 4 verificadas pelo kernel.*

**Victor Gabriel de Oliveira** · edição consolidada de 13 de novembro de 2026

[**📄 Ler o artigo (PDF)**](Biblioteca_Unificada.pdf) &nbsp;·&nbsp; [**🧮 Mapa TeX → Lean**](mapas/MAPA_TEX_LEAN.md) &nbsp;·&nbsp; [**⚙️ Fontes Lean 4**](lean4/ambientes) &nbsp;·&nbsp; [**✍️ Fontes LaTeX**](tex)

`Lean 4.28.0` · `Mathlib 4.28.0` · `axiomas: propext, Classical.choice, Quot.sound` · `0 sorry`

</div>

---

## A ideia em um parágrafo

Como aproximar *qualquer* função contínua por pedaços de reta **de forma totalmente determinística,
enumerável e sem nenhum número real escondido nos parâmetros**? Este trabalho constrói uma biblioteca
de segmentos afins de inclinação racional ancorados em células diádicas, em que **cada endereço
recupera exatamente a célula e a função**, e mostra que ela é, ao mesmo tempo, densa em $C(K)$,
equivalente a redes ReLU rasas racionais, otimizável **exatamente** por programação dinâmica, e capaz
de caracterizar espaços de Besov por taxas de aproximação com custo aritmético controlado. Tudo isso
vem com uma formalização em Lean 4 que liga cada enunciado do texto a uma prova verificada por máquina.

## O volume em números

| | |
|---|---|
| Páginas do PDF | **122** |
| Ambientes matemáticos (teoremas, lemas, definições, algoritmos…) | **151** |
| Ambientes do manuscrito original de 77 páginas cobertos | **108** |
| Figuras (PDF, PNG e SVG) | **17** |
| Referências bibliográficas | **49** |
| Código Lean 4 | **~40 mil linhas**, mais de 2 mil teoremas e lemas, em 3 ambientes |
| Casos do dossiê de pendências fechados | **42 de 42** (41 provas Lean + 1 prova textual) |
| Base de confiança do Lean | apenas `propext`, `Classical.choice`, `Quot.sound` |

## As cinco partes

### Parte I — Biblioteca, endereçamento e refinamento
Uma biblioteca **enumerável e sem repetições** de segmentos afins de inclinação racional não nula, presos
a células diádicas. Montagens contínuas finitas são **densas em $C(K)$** e admitem **representação exata
por redes ReLU rasas racionais** com quebras diádicas. Para funções $C^2$, a racionalização preserva a
constante $1/8$ do erro de interpolação uniforme. O refinamento adaptativo combina majorantes intervalares
racionais da segunda derivada com racionalização nodal, com correção, término e tamanho controlados.

### Parte II — Normalização e equivalência das montagens
Os tipos e as dependências de todas as construções: representações por átomos e por células endereçadas,
conversões entre elas e a equivalência das classes de funções que definem.

### Parte III — Custo, entropia e seleção exata
- Sob um calibre explícito a biblioteca contém $\Theta(H^6)$ átomos; o gerador aritmético tem pior índice
  $\Theta(H^8)$ e a enumeração por altura realiza o mínimo exato do maior índice.
- Três formatos *prefix-free* distinguem endereços, estrutura ReLU e expansão racional.
- Em classes limitadas de $C^2$, a curvatura fornece um *codebook* com entropia de ordem $\varepsilon^{-1/2}$.
- **Pares racionais de fronteira são estados suficientes** para selecionar simultaneamente árvore e átomos,
  com penalidades de descrição ou orçamentos de folhas: seleção **exata** por programação dinâmica, com
  desempate canônico e cotas de complexidade (inclusive em bits).
- Para interpolação real em árvores estritamente diádicas: envelope assintótico $[\,I(f)^2/8,\ I(f)^2/2\,]$,
  realizado por curvatura constante; quadráticas por partes têm uma lei periódica de fases.

### Parte IV — Agendas de altura e teoria direta–inversa
- O funcional de melhor erro define estratos, mas **falha em ser homogêneo** por escalares reais.
- Aproximantes em malhas diádicas com altura de ordem $N^{\max\{1,s\}}$ (com fator logarítmico no caso crítico)
  e **cotas uniformes sobre bolas de Besov**.
- Erro bruto $N^{-\alpha}$ com crescimento de Lipschitz $N^{\gamma}$ ⟹ regularidade inversa de ordem
  $\alpha/(\alpha+\gamma)$; um **pente de tendas** mostra que a cota é aguda quando $0<\alpha\le\gamma$.
- **Extensão marcada** e reversibilidade exata de redes ReLU rasas; **reversão aproximada quantizada** para
  parâmetros reais; **redes profundas** medidas pela função que realizam (a tenda iterada tem $2^L$ regiões).
- Caracterização direta e inversa das classes de Besov somando ao erro a segunda diferença do aproximante.

### Parte V — Complementos do manuscrito original
Os resultados das seções 6 e 21 do documento original (resto de interpolação, taxas uniformes,
comparação com nós livres), conservando a numeração original para cruzamento.

## Resultados em destaque (e onde estão no Lean)

| Resultado | Declaração Lean | Arquivo |
|---|---|---|
| Reversibilidade rasa exata de redes ReLU (IV.5.2) | `Marcada.RealReLU.exact_shallow_reversal` | `artigo_2/Pendencias/ReversaoOriginal.lean` |
| Cota de altura inversa **corrigida** (IV.5.4) | `AlturaInversa.Hcan_le`, `reverse_height_bit_bound`, `no_additive_constant_fix` | `artigo_2/Pendencias/AlturaInversa.lean` |
| Reversão aproximada quantizada, $C=320$ (IV.5.5) | `Marcada.QuantIV55.quantized_approximate_reverse` | `artigo_2/Pendencias/ReversaoQuantizada.lean` |
| Redes profundas pela função realizada (IV.5.6) | `Marcada.DeepIV56.deep_functional_reverse` | `artigo_2/Pendencias/ReversaoProfunda.lean` |
| Pente de tendas, agudeza crítica (IV.5.9) | `PenteGemini.critical_tent_comb` | `artigo_2/Pendencias/Pente.lean` |
| Cotas diretas de Jackson/Besov (IV.4.x) | `Jackson.rational_jackson_uniform`, `direct_besov_height`, `uniform_besov_ball` | `artigo_2/Pendencias/Jackson.lean`, `Direta.lean` |
| Reversibilidade de Besov completa e estável (IV.5.13–14) | `Jackson.complete_besov_reversibility`, `architecture_stable_reversibility` | `artigo_2/Pendencias/Realizacao.lean` |
| Seleção exata por programação dinâmica (III.6–7) | `DPprog.varRoot_spec`, `fixRoot_spec` | `artigo_2/Pendencias/ProgDin.lean` |
| **Complexidade densa em número de estados (III.9.1)** | `DenseDP.state_complexity_dense` | `artigo_2/Pendencias/ComplexidadeDensa.lean` |
| **Complexidade de bits (III.9.3)** | `DenseDP.bit_complexity_dense` | `artigo_2/Pendencias/ComplexidadeBits.lean` |

A tabela completa — cada um dos 151 ambientes do PDF com o rótulo no TeX, a linha e a(s) declaração(ões) Lean —
está em [`mapas/MAPA_TEX_LEAN.md`](mapas/MAPA_TEX_LEAN.md).

### Um destaque honesto: a formalização corrigiu o artigo

Ao formalizar IV.5.4 descobriu-se que a cota impressa para a altura canônica,
$\log_2 H_{\mathrm{can}}(R)\le C[M\log(2W)+D+\log(M+1)]$, **é falsa**: para $R(x)=x$ ($M=0$, $D=0$, $W=1$)
tem-se $H_{\mathrm{can}}=2$ e o lado direito é $0$. O texto agora traz a versão correta, com fator $M+1$
(`Hcan_le`, `reverse_height_bit_bound`) e o contraexemplo está provado em Lean (`no_additive_constant_fix`).
É esse tipo de coisa que uma prova verificada por máquina encontra e uma leitura cuidadosa deixa passar.

### Complexidade com modelo de custo explícito (III.9.1 e III.9.3)

A implementação densa da recorrência é um programa dentro do Lean, com um **monad de contagem de operações**,
memória densa de domínio explícito e um motor genérico de preenchimento por níveis. Provou-se que a tabela
guarda exatamente `Cvar`/`Cb`, que a memória é exatamente $S_D M^2$ (resp. $S_D N M^2$) entradas, que o
tempo é $\le 8\,S_D M^3$ (resp. $\le 7\,S_D N^2 M^3$) e que os apontadores reconstroem uma representação
ótima; em bits, todo operando tem comprimento $\le B_{\mathrm{cost}}$.

## Estrutura do repositório

```
.
├── Biblioteca_Unificada.pdf        # o artigo (122 páginas)
├── tex/                            # fontes LaTeX
│   ├── principal.tex               #   documento principal (compilar com latexmk)
│   ├── documento_completo.tex      #   versão em arquivo único, com bibliografia incorporada
│   ├── partes/                     #   as cinco partes
│   ├── figuras/                    #   17 figuras em PDF, PNG e SVG
│   └── referencias.bib
├── lean4/ambientes/
│   ├── artigo_2/                   # Partes III–V: RequestProject/ e a biblioteca Pendencias/
│   ├── base_integrada/             # Parte I e II: Unified/ e PendenciasParte1/
│   └── parte_1/                    # núcleo da Parte I (RequestProject/) e auditorias
└── mapas/MAPA_TEX_LEAN.md          # correspondência enunciado TeX ↔ declaração Lean
```

## Como reproduzir

**Artigo (LaTeX).**

```bash
cd tex
latexmk -pdf -interaction=nonstopmode principal.tex      # gera tex/principal.pdf
```

**Formalização (Lean).** Instale o [`elan`](https://github.com/leanprover/elan); cada ambiente fixa a
versão do Lean e do Mathlib (4.28.0). O cache do Mathlib não é versionado.

```bash
cd lean4/ambientes/artigo_2
lake exe cache get          # baixa o Mathlib já compilado
lake build Pendencias       # provas das Partes III–V
lake env lean AuditoriaPendencias.lean     # imprime os axiomas de cada resultado

cd ../base_integrada && lake exe cache get && lake build PendenciasParte1
cd ../parte_1        && lake exe cache get && lake build
```

Os ambientes `artigo_2`, `base_integrada` e `parte_1` compilam de forma independente. Em cada auditoria,
todas as declarações dependem **somente** de `propext`, `Classical.choice` e `Quot.sound`, sem `sorry`.

## Escopo e honestidade

Este repositório prefere afirmar menos a afirmar demais:

- **Prova compilada ≠ correspondência herdada.** Dos 151 ambientes, os 42 casos do dossiê de pendências
  têm prova Lean nova (41) ou prova textual sincronizada (1). Outras 77 correspondências foram *inspecionadas*
  e 20 *integradas à base* a partir de formalizações anteriores; elas apontam declarações Lean relevantes,
  mas **não** foram reauditadas semanticamente uma a uma. Não se afirma formalização integral.
- **III.9.1** usa um modelo de custo unitário explícito; a tabela densa compara custos e **não** implementa o
  desempate canônico por $\kappa$ (que está formalizado no seletor funcional de III.7.4).
- **III.9.3** toma como *hipótese do modelo* (`BitModel`) que somar, comparar e reduzir frações de $b$ bits
  custa $O(\mathsf M_{\mathbb Z}(b)\log 2b)$, como no texto — não há modelo de máquina em Lean.
- **IV.5.4** foi fechado com o enunciado corrigido (ver acima).

## Autor

**Victor Gabriel de Oliveira.** A formalização em Lean 4 foi desenvolvida com assistência de
ferramentas de IA e verificada pelo kernel do Lean.
