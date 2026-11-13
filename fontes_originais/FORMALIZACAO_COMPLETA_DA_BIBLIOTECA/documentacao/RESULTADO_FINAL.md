# Resultado do recorte, da integração e das duas etapas iniciais

Conferência final de 22/10/2026.

## Edição e preservação do escopo

O Artigo 1 foi reduzido de 49 para 24 ambientes numerados, com 20 resultados
matemáticos. Os 24 enunciados retidos permanecem exatamente iguais.
O bloco de 25 ambientes transferidos está no Artigo 2, seção 3. Resumo,
introdução, conclusão e notação passaram a refletir o recorte. O calibre
necessário à proposição 4.4 foi preservado nas preliminares.

Os três resultados da seção 6 original e o lema 21.1 de Runge receberam
destino integral no complemento. Foram preservados seus enunciados e
demonstrações matemáticas; somente remissões externas foram ajustadas.
O complemento conserva a numeração do original.

Os 108 ambientes do original de 77 páginas têm destino explícito: 24 no
Artigo 1, 56 no Artigo 2, 24 no Artigo 3 e quatro no complemento. Não há
enunciado original sem destino documental nem duplicação ativa do bloco
transferido. O original completo continua preservado com seu manifesto.

Foram recompostos e revisados os PDFs do Artigo 1, com 17 páginas, e do
complemento, com três páginas. As remissões estão resolvidas; a composição
final não apresenta caracteres ausentes ou caixas excedendo a largura.

Dos 130 arquivos do retrato anterior, 120 permanecem byte a byte iguais.
As dez alterações registradas correspondem ao recorte, à composição e às
importações do agregador; todas têm o original preservado fora da raiz ativa.
Nenhum fonte Lean recebido ou declaração Lean original foi reescrito.
Cinco materiais inativos foram retirados da pasta do Artigo 1 após comparação
com as cópias históricas, sem apagar os originais.

## Correspondência entre TeX e Lean

A matriz atual contém 151 ambientes: 24 do Artigo 1, 59 do Artigo 2, 24 do
Artigo 3, 40 da normalização e quatro do complemento. São 104 teoremas,
lemas, proposições ou corolários. O original tem seu inventário separado,
evitando somar duas vezes o conteúdo de origem.

Cada entrada conserva texto, posição, rótulos, hash, resultados Lean
identificados e ressalvas. Os 275 nomes Lean citados passaram pelo compilador:
94 da base, 97 da Parte I e 84 do Artigo 2. As entradas sem prova localizada
continuam explícitas; uma correspondência editorial não é apresentada como
formalização integral.

O fechamento matemático da normalização foi integrado aos tipos concretos
da biblioteca em seis módulos, com sete definições e 67 teoremas públicos
novos. As identidades de endereços, classes, recursos, erros e extensão ReLU
estão detalhadas em `INTEGRACAO_NORMALIZACAO.md`.

O arquivo histórico auxiliar chamado
`Fechamento_Parte_2_Formalizacao_Aristotle.tex` continua parcialmente
recuperado. Ele é distinto do original de 77 páginas fornecido pelo autor
e não foi apresentado como recuperado integralmente ou substituído por
uma reconstrução presumida. O fechamento matemático entregue nesta etapa
está nos novos módulos Lean e tem seus próprios registros de verificação.

## Validação integral dos dois pacotes recebidos

| Pacote | Módulos compilados | Declarações auditadas | Teoremas auditados | Axiomas inesperados |
| --- | ---: | ---: | ---: | ---: |
| Parte I | 9 | 509 | 348 | 0 |
| Artigo 2 | 31 | 2.199 | 1.700 | 0 |

Os ambientes de validação mantêm diretórios de build separados. O agregador
do Artigo 2 importa os 31 módulos, corrigindo a insuficiência do Main
recebido, que importa apenas Mathlib. Os 40 fontes recebidos permanecem
inalterados, com zero ocorrências de `sorry` no código verificado.

A execução completa da base integrada também passou. Sua auditoria própria
conferiu 2.755 declarações e 2.196 teoremas. Uma auditoria adicional incluindo
as dependências recebidas da Parte I conferiu 3.265 declarações e 2.544
teoremas. Só foram encontrados `propext`, `Classical.choice` e `Quot.sound`.
Essas contagens se sobrepõem e não representam resultados matemáticos distintos.

O ambiente de compatibilidade local está fixado em Lean/Mathlib 4.28.0.
As configurações originais Aristotle não vieram nos pacotes; não se afirma
reprodução retroativa de um ambiente desconhecido.

## Próxima frente matemática

O próximo passo é resolver as diferenças semânticas ainda registradas para
o Artigo 2: regularidade C², passagem para árvores em raiz única e execução
das recorrências com seus custos. A divergência textual g(t₀) também precisa
ser sincronizada com a extensão certificada. O Artigo 3 e os quatro resultados
do complemento permanecem frentes próprias de formalização.

## Registros principais

- `CORRESPONDENCIA_ARTIGOS.md` e `enunciados.json`: matriz TeX–Lean atual.
- `CONFERENCIA_ORIGINAL_77.md`: origem e destino de todos os ambientes do original.
- `evidencias/integracao_normalizacao_2026-10-22/resultado.json`: integração e auditoria.
- `validacao/resultados.json`: compilação e auditoria dos dois pacotes separados.
- `evidencias/recebimento_2026-10-22/recorte_editorial.json`: alterações autorizadas e originais preservados.
- `evidencias/validacoes/2026-10-22_19-20-19_L5Io81/`: execução completa da base.
