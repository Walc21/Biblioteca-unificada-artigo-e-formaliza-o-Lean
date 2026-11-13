# Formalização da biblioteca — estado atual

Raiz única de trabalho, atualizada em 22/10/2026. Lean/Mathlib 4.28.0.

O [resultado final](documentacao/RESULTADO_FINAL.md) reúne o recorte editorial,
a integração da normalização e a validação integral dos dois pacotes recebidos.

## Artigos e correspondências

- Artigo 1 reduzido: 24 ambientes numerados, com os enunciados retidos preservados.
- Artigo 2: 59 ambientes, incluindo os 25 transferidos do primeiro artigo.
- Artigo 3: 24 ambientes; sua formalização integral continua como frente própria.
- Complemento: os quatro resultados restantes do original, com enunciados e provas.
- Normalização da Parte I: 40 ambientes e pacote Lean integrado à base.

A [matriz TeX–Lean](documentacao/CORRESPONDENCIA_ARTIGOS.md) cobre os 151 ambientes
atuais, com 275 identificadores Lean conferidos pelo compilador. Os enunciados
sem formalização localizada e as diferenças semânticas permanecem explícitos.
O [cruzamento do original](documentacao/CONFERENCIA_ORIGINAL_77.md) dá destino aos
108 ambientes do documento de 77 páginas, sem duplicação ativa do bloco transferido.
O original integral está preservado em `entradas/original_77_paginas/`.

Os PDFs recompostos são `artigos/artigo_1/artigo.pdf` (17 páginas) e
`artigos/complemento_original_77/complemento.pdf` (três páginas).

## Integração verificada

As seis [pontes da normalização](documentacao/INTEGRACAO_NORMALIZACAO.md) provam
as identidades de átomos, endereços, classes, recursos, erros e extensão ReLU
nas definições concretas da biblioteca. São sete definições e 67 teoremas públicos
novos, sem reescrever os enunciados Lean recebidos. A base tem 53 módulos em
`Unified/`, dos quais 41 são os fontes de origem preservados.

A execução completa da base passou: 2.755 declarações e 2.196 teoremas auditados.
A auditoria adicional que inclui a Parte I verificou 3.265 declarações e 2.544
teoremas. As contagens se sobrepõem. Só aparecem `propext`, `Classical.choice`
e `Quot.sound`; nenhum axioma fora da lista foi encontrado.

Os pacotes também passaram novamente em ambientes separados:

| Pacote | Arquivos Lean | Declarações | Teoremas |
| --- | ---: | ---: | ---: |
| Parte I | 9 | 509 | 348 |
| Artigo 2 | 31 | 2.199 | 1.700 |

O agregador do Artigo 2 importa todos os 31 módulos. Seu Main original importa
apenas Mathlib. Os 40 fontes recebidos permanecem inalterados. As configurações
originais Aristotle não vieram nos pacotes; a validação certifica compatibilidade
local explícita com Lean/Mathlib 4.28.0.

## Verificações reproduzíveis

```bash
./executar.sh
lake env lean AuditoriaIntegracao.lean
python3 scripts/validar_pacotes.py
python3 scripts/mapear_corpus.py
python3 scripts/conferir_original_77.py
python3 scripts/documentar_estado.py
python3 scripts/verificar_preservacao.py
```

Para resumir os logs existentes dos pacotes: `python3 scripts/validar_pacotes.py --resumir`.
Para conferir apenas a estrutura da base: `./executar.sh --estatico`.

## Preservação e organização

As dez alterações autorizadas do retrato de 130 arquivos estão registradas em
`evidencias/recebimento_2026-10-22/recorte_editorial.json`; os outros 120 arquivos
permanecem byte a byte iguais. Os originais anteriores ao recorte estão em
`/home/victor/Projetos/Arquivo_Biblioteca_2026-10-22/antes_do_recorte_editorial/`.
Cinco materiais inativos saíram da raiz do Artigo 1 após comparação com esse arquivo.
Nenhum fonte Lean recebido ou declaração Lean original foi reescrito.

Os registros finais estão em `evidencias/integracao_normalizacao_2026-10-22/`,
`evidencias/validacoes/2026-10-22_19-20-19_L5Io81/` e `validacao/resultados.json`.
O Artigo 2 conserva seu ambiente independente até as próximas pontes semânticas.
O documento auxiliar histórico de fechamento continua parcialmente recuperado;
não foi confundido com o original integral nem apresentado como fonte completo.
