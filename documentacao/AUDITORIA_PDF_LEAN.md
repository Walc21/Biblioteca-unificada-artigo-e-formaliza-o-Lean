# Auditoria dos enunciados e da reprodução

A revisão parte de `c67268b9510696cdcf08b22f89842cf5bd54a49d`, o mesmo commit no
checkout local e no repositório GitHub. Foram examinadas a edição unificada e
a edição ABNT. A comparação usou os rótulos do [mapa](../mapas/MAPA_TEX_LEAN.md)
para ligar o PDF, suas fontes e as assinaturas Lean de cada resultado
revisitado. A [reauditoria das 97 correspondências herdadas](REAUDITORIA_CORRESPONDENCIAS.md)
e a [conferência da fase](CONFERENCIA_ENUNCIADOS_LEAN.md) registram a cobertura
anterior. Esta rodada não é uma certificação semântica integral dos 156 ambientes.

| Item | Correspondência verificada |
|---|---|
| I.4.3 | A expressão na ida usa a reta do primeiro átomo em `t₀`, mesmo quando `t₀ ∉ K`. A hipótese de compatibilidade nas fronteiras compartilhadas vem da definição de montagem. A divergência que constava do mapa correspondia à redação anterior. |
| I.6.3–I.6.4 | Para coberturas que se estendem além de `K`, a declaração correspondente é `certified_refinement_external`. As raízes têm interiores disjuntos e a estimativa de profundidade usa o contrato sobre o majorante. As escolhas nodais são existenciais. |
| III.3.2 e III.3.7 | `card_LH` dá a contagem exata e `card_LH_theta` dá a ordem. A assintótica com constante `288/π⁴` usa a soma dos totientes na prova textual. As duas funções de endereçamento são executáveis e têm inversão provada. A computabilidade no sentido do predicado `Computable` permanece sem teorema. |
| III.9.1 e III.9.3 | A tabela instrumentada recupera um minimizador de custo e sua largura agora contabiliza a coordenada de orçamento. O seletor de III.7.4 certifica a escolha canônica. A estimativa de custo para o desempate por fluxos da tabela densa continua textual. |
| III.12.5 e III.12.8 | A medida formal no círculo é `μ̃_f = μ_f/√8`. O salto é a massa do singleton `{-t}` para essa medida. A equivalência de uniformidade já estava em `FaseMedida.lean` e a edição não ABNT ainda a descrevia como pendente. |
| IV.3.1, IV.3.2 e IV.4.6 | Os enunciados impressos usam uma raiz diádica qualquer. As declarações citadas no mapa usavam apenas `[0,1]`. `AgendaRaiz.lean` prova as versões gerais, incluindo o atingimento do ínfimo, ambos os sentidos da redução de escala e o piso na altura `H(N)`. |
| IV.3.3 e IV.4.5 | A hipótese de agenda não decrescente vem da definição de agenda e passou a constar no enunciado de IV.3.3. Em IV.4.5, `c2_endpoint` e `c2_endpoint_bits` já usam a agenda `H2` e a classe `C²([0,1])` da edição atual. |
| IV.5.2–IV.5.6 | A reversão trabalha com igualdade em `[0,1]`. Em IV.5.4, `Anchored.toRealReLU` preserva avaliação, número e ordem das quebras, com saltos não nulos. A cota inversa já corrigida nos dois PDFs é a de `Hcan_le`. |
| IV.5.13–IV.5.14 e Parte V | A inclusão de arquiteturas usa a classe apontada e o orçamento reescalado. O lema de Runge do complemento permite um intervalo maior no Lean. As demais declarações da Parte V foram conferidas quanto à raiz, ao interpolante e à regularidade exigida. |

## Reprodução

- O gerador original das seis figuras da Parte I foi recuperado do acervo local.
  Os seis PDFs gerados coincidiram pixel a pixel com os publicados quando renderizados a
  130 dpi. O refinamento de `[1+64(x-5/8)^2]⁻¹` gera 27 folhas e um certificado de
  erro `51/5000`. O circuito recompilou a partir da fonte TikZ do repositório.
  As 17 figuras tiveram arquivos PDF gerados com as dimensões originais.
  Oito coincidiram pixel a pixel e nas demais houve diferenças em menos de
  3% dos pixels da renderização a 130 dpi.
- A reprodução passou a emitir as tabelas do interpolante exponencial e do codebook
  em TeX. As linhas das 15 tabelas geradas coincidiram nas duas edições, considerando
  os separadores de milhares, decimais e intervalos usados na apresentação.
- As razões para as alturas 50, 800 e 12800 de III.3.2 e as janelas de III.12.9
  agora têm comandos documentados. A floresta de quadráticas por partes reproduziu
  33, 18 e 119 limiares, com a igualdade entre o menor valor de `N²E_N` e o
  extremo inferior de fase verificada em frações exatas.
- Os seis JSON versionados foram reproduzidos. As diferenças ficaram nos
  metadados e nos últimos dígitos de três expoentes ajustados em ponto flutuante.

Os [comandos de reprodução](../verificacao/README.md) registram os parâmetros e
os arquivos de saída.
