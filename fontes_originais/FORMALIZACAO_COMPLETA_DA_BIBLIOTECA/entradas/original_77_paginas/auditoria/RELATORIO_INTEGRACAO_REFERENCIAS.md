# Relatório histórico de integração das referências

> Registro da versão anterior à revisão de 8 de agosto de 2026. Menções às
> duas composições tipográficas descrevem o pacote auditado originalmente e
> não a entrega corrigida atual. Consulte `RELATORIO_DE_CORRECOES_2026.pdf`.

## Escopo

As edições nacional e IEEE usam a mesma sequência de 22 seções LaTeX. A
auditoria foi feita sobre esses fontes compartilhados, os dois mestres, os dois
PDFs originais e as 36 entradas de `references.bib`.

Antes da revisão, 24 das 36 chaves bibliográficas eram citadas. Depois da
revisão, todas as 36 são chamadas no texto e aparecem nas bibliografias das duas
edições. Nenhuma chave citada ficou sem entrada no arquivo `.bib`.

## Referências integradas

| Núcleo temático | Chaves incorporadas | Local principal |
|---|---|---|
| Programação dinâmica e aproximação por segmentos | `bellman1957`, `bellman1961`, `stone1961` | introdução e seção 12 |
| CART e partições diádicas recursivas | `breiman1984`, `donoho1997`, `blanchard2007` | introdução e seções 9--10 |
| Aproximação por partes, splines e Besov | `birman1967`, `petrushev1988`, `schumaker2007` | seções 4--6 e 19 |
| Aproximação por funções racionais | `petrushevpopov1987` | seção 19, com distinção explícita entre quocientes de polinômios e coeficientes racionais |
| Cotas e profundidade em redes ReLU | `yarotsky2017`, `telgarsky2016` | seções 4 e 20 |

Outras referências já usadas foram reposicionadas ou repetidas quando
sustentavam diretamente o contexto local. Em particular, as fontes sobre redes
ReLU que estavam anexadas a uma frase sobre codificação prefix-free foram
movidas para a identidade em hinges que efetivamente documentam.

## Critério de atribuição

As citações foram usadas para antecedentes, métodos e resultados clássicos. Os
teoremas, constantes, recorrências com estados aritméticos e limites específicos
da biblioteca continuam apresentados como resultados do artigo. Não se atribuiu
a uma fonte externa uma prova ou uma restrição que ela não contém.

Os registros sobre programação dinâmica, árvores diádicas, splines/Besov e
redes ReLU foram confrontados por busca acadêmica. A constante local de
interpolação e a contagem de regiões da tenda iterada também foram verificadas
simbolicamente: o máximo do erro quadrático em uma célula é
`|kappa| h^2 / 8`, e as quatro primeiras iteradas têm respectivamente
`2, 4, 8, 16` regiões, com inclinações `±2, ±4, ±8, ±16`.

## Verificações finais

- cobertura bibliográfica nos fontes: 36/36;
- referências internas: 247, todas definidas;
- ambientes matemáticos: 95, todos balanceados;
- PDF nacional: 71 páginas;
- PDF IEEE: 59 páginas;
- ausência de citações indefinidas, referências indefinidas e caixas excedentes;
- presença, nas duas seções bibliográficas, dos autores que cobrem as 12 entradas integradas;
- inspeção visual de todas as páginas das duas edições.
