# Correspondência semântica — IV.5.2

Fonte normativa: `tex/partes/artigo_3.tex`, rótulo `map:artigo_3:5.2` e fórmulas
`reduced-relu-reverse`, `marked-reversal-conditions`, `canonical-tree-leaf-bounds`,
`original-nonflat-condition`. O enunciado TeX foi preservado.

Declaração que reúne as conclusões: `Pendencias.Marcada.RealReLU.exact_shallow_reversal`,
em `lean4/ambientes/artigo_2/Pendencias/ReversaoOriginal.lean`.

| Conteúdo do TeX | Declaração / representação Lean |
|---|---|
| Parâmetros reais, M hinges | `RealReLU M`, com M natural arbitrário, incluindo zero |
| 0 < τ₁ < … < τ_M < 1 e a_j ≠ 0 | `RealReLU.Reduced`: `StrictMono τ`, interior e saltos não nulos |
| Função c+qx+∑a_jρ(x−τ_j) | `RealReLU.eval`, soma sobre `Fin M` |
| Pertinência a 𝒜^□([0,1]) | `MarkedRealizable`: árvore marcada bem formada e igualdade no intervalo |
| Coeficientes racionais e quebras diádicas | `Arithmetic`, conclusões de `parameters_necessary` |
| Se e somente se | `marked_realizable_iff`, ambas as direções |
| Árvore menos refinada que realiza R | `realizes_refines_canonical`; toda realização refina a canônica |
| Unicidade da árvore mínima | `canonicalTree_unique_least_labeled`, igualdade da árvore inteira, inclusive rótulos |
| M+1 ≤ N_can ≤ 1+∑d_j | `canonicalTree_spec`, usando as contagens de `CanonicaContagem.lean` |
| d_j é a profundidade reduzida | `dyadicDepth`, `dyadicDepth_spec`: denominador reduzido = 2^d_j |
| Biblioteca original iff todas as σ_i ≠ 0 | `original_realizable_iff`, com índices n=0,…,M |

## Hipóteses e domínio

As hipóteses da declaração principal são somente os dados reais da fórmula e as
condições de redução impressas antes do teorema. Não se presume a racionalidade
nem a diadicidade para provar a direção necessária. Para construir a árvore,
a hipótese `Arithmetic` está sob o quantificador que exprime “nessas condições”.

O TeX trata de funções em `[0,1]`. As avaliações das árvores são funções em `ℝ`
por conveniência do acervo; `EqOn` compara exatamente suas restrições ao intervalo,
sem exigir uma extensão externa que o TeX não especifica. O uso de M=0 é preservado.

As quebras são distintas por `StrictMono`, portanto a cardinalidade do conjunto
racionalizado é exatamente M (`rationalData_card`). A inclusão `ℚ → ℝ` é injetiva:
as testemunhas racionais não mudam os dados da rede. A identidade funcional da
conversão é provada em `rationalData_eval`.

## Estratégia certificada

A árvore canônica separa as quebras; em cada folha, `atomAt_eval` identifica a
fórmula hinge com o átomo determinado por valor central e inclinação. A prova de
`canonTree_realizes` verifica a continuidade nas fronteiras. A contagem superior
consome uma unidade da carga de profundidades a cada subdivisão; a inferior
conta as quebras que cada nó pode separar.

Para a necessidade, cada hinge reduzido é um ponto de não diferenciabilidade.
Fora das fronteiras diádicas finitas, uma montagem tem derivada racional, a
inclinação do átomo alcançado. Isso força as quebras a serem fronteiras diádicas.
Cada região afim tem um ponto fora dessas fronteiras: sua inclinação é racional,
e as diferenças entre inclinações fornecem os saltos racionais. O intercepto vem
da avaliação no extremo zero.

A biblioteca original só usa átomos de inclinação não nula. A necessidade passa
pela derivada em cada região; a suficiência retira as marcas da montagem canônica
quando todas as inclinações são não nulas. A igualdade entre árvores mínimas foi
provada também para os rótulos, por unicidade dos parâmetros afins em cada célula.

## Reprodução

```bash
cd lean4/ambientes/artigo_2
lake build Pendencias
lake env lean AuditoriaPendencias.lean
```

As saídas da rodada específica ficam em `verificacao/build_reversao_exata.log`
e `verificacao/axiomas_reversao_exata.log`. O fechamento só é registrado no mapa
depois de ambos terminarem sem erros e sem axiomas fora da lista permitida.
