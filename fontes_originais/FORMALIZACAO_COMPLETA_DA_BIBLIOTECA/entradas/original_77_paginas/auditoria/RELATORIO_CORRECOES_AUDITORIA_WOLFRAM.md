# Registro histórico dos achados da auditoria matemática Wolfram

> Este arquivo documenta uma etapa anterior. Nomes e paginações das antigas
> composições são mantidos apenas para rastreabilidade. Consulte
> `RELATORIO_DE_CORRECOES_2026.pdf` para o estado atual.

## Correspondência da versão auditada

O laudo `Relatorio_Auditoria_Matematica_Wolfram.pdf` identifica como objeto a
versão `REFERENCIADO(1)`, com SHA-256
`5c63188368b6fb0cb31f55de065ead171807383b9d2e319ad7ebc97d8e51b4bf`.
O arquivo `REFERENCIADO(2)` recebido para esta revisão possui exatamente o mesmo
SHA-256 e é idêntico byte a byte. Assim, os locais e os diagnósticos do laudo
aplicam-se diretamente à base corrigida.

## Resultado da conferência dos achados

| ID | Conferência independente | Solução implementada |
|---|---|---|
| M-01 | Confirmado. A hipótese publicada não relacionava classes neurais em orçamentos distintos e o contraexemplo com múltiplos de 3 invalida o teorema original. | Exigido `N_N subset N_{N+1}`; prova reescrita com reindexação diádica; resumo, abstract, introdução e conclusão qualificados. |
| L-01 | Confirmado. A direção inversa da caracterização citava uma cota dentro de um teorema que já pressupunha pertencimento a Besov. | A prova agora usa diretamente o lema universal, válido para toda função contínua. |
| R-01 | Confirmado. O caminho publicado não existia no pacote. | Corrigido para `reproducibility/selecao/seletor_dinamico_exato.py`. |
| R-02 | Confirmado. `compilar.sh` executa um programa da biblioteca e cinco da seleção. | A Seção 21 registra seis programas coordenados por `compilar.sh` e distingue seus arquivos JSON. |
| E-01 | Confirmado. Havia duas vírgulas no índice da célula. | Corrigido para `J_{k_0+r,2^r m_0+j}`. |

## Reparo matemático de M-01

O contraexemplo do laudo é válido. Para `c=3`, defina a classe neural de
orçamento `m` como a classe da biblioteca de orçamento `m/3` quando `3` divide
`m`, e como `{0}` nos demais casos. Cada classe contém funções ReLU e a inclusão
da biblioteca no orçamento `3N` vale, mas nenhuma potência de dois é divisível
por 3. Logo, para `f=1`, todos os certificados neurais nos orçamentos diádicos
valem 1, contradizendo a caracterização Besov alegada.

A solução inserida exige aninhamento das classes neurais no orçamento. Para
preservar explicitamente a hipótese diádica do lema de Jackson, a prova usa

`d = 2^{ceil(log_2 c)}`, `M = 2^r` e `n = M/d`.

Então `n` continua sendo potência de dois, `ceil(cn) <= M` e

`Sigma_n subset N_{ceil(cn)} subset N_M`.

O módulo de segunda ordem é monótono na escala, `M=dn` altera as taxas apenas
pelo fator constante `d^s`, e a passagem de `M` a `n` é um deslocamento fixo da
sequência diádica. Isso fecha simultaneamente os casos `q=infinito` e
`0<q<infinito`, sem usar um orçamento não diádico no lema de Jackson.

## Proteção contra regressões

`auditoria/auditar_fontes.py` passou a verificar especificamente os cinco
achados: caminho do seletor, contagem dos programas, índice da célula, citação
do lema universal, aninhamento da família neural, reindexação diádica e as
qualificações do resumo, abstract e conclusão.

## Validação final

- seis suítes determinísticas executadas integralmente;
- 4.096 conversões exatas montagem--ReLU e 2.952 roundtrips de reversibilidade;
- 84 redes quantizadas e 1.260 certificados triangulares verificados;
- auditoria estática aprovada: 399 rótulos, 247 referências internas resolvidas,
  36 chaves bibliográficas e 95 ambientes matemáticos;
- edição Nacional: 71 páginas A4;
- edição IEEE: 59 páginas Letter;
- nenhuma citação ou referência indefinida e nenhuma caixa excedente;
- inspeção visual integral das 130 páginas, com revisão ampliada de todas as
  páginas alteradas;
- manifesto SHA-256 e `verificar.sh` aprovados após o fechamento do pacote.

Todos os cinco problemas apontados no laudo foram, portanto, confirmados e
resolvidos. O restante do núcleo matemático e dos resultados reprodutíveis
permaneceu inalterado.
