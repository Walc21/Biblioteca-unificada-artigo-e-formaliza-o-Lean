# Lacunas e diferenças semânticas localizadas

Este inventário deriva das ressalvas já presentes na entrega recebida. Não cria novas provas ou obrigações presumidas. O número original identifica o manuscrito de 77 páginas; o número do volume identifica a presente edição.

## I.4.3 — equivalência montagem--ReLU racional

Original: **4.3**. Página do volume: **11**. Estado: `divergencia_documentada`.

O operador de extensao normalizado foi integrado a classe concreta da Fase 2. O enunciado TeX deste volume le g(t0) como o valor em t0 da primeira peca (t0 pode estar fora de K); essa leitura nao foi reverificada contra o enunciado Lean.

Fonte: `tex/partes/artigo_1.tex:253`; rótulo `map:artigo_1:4.3`.

- `Dyadic.Lib.assembly_eq_relu` — `lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean:92`.
- `Dyadic.Lib.relu_mem_Asm` — `lean4/ambientes/base_integrada/Unified/Consolidado/Sec4/ReLU.lean:183`.

## III.9.1 — complexidade em número de estados

Original: **14.1**. Página do volume: **60**. Estado: `cobertura_parcial`.

Prova cardinalidades das tabelas e transicoes; nao certifica tempo e memoria de um programa com execucao ligada a essas cardinalidades.

Fonte: `tex/partes/artigo_2.tex:1996`; rótulo `map:artigo_2:9.1`.

- `Artigo.Setup.state_complexity` — `lean4/ambientes/artigo_2/RequestProject/Complexity.lean:89`.

## III.9.3 — cota grosseira de complexidade de bits

Original: **14.3**. Página do volume: **61**. Estado: `cobertura_parcial`.

bit_complexity limita o tamanho dos custos racionais. As cotas de tempo e memoria em bits do artigo exigem semantica de execucao e custo de operacoes/desempate.

Fonte: `tex/partes/artigo_2.tex:2083`; rótulo `map:artigo_2:9.3`.

- `Artigo.Setup.bit_complexity` — `lean4/ambientes/artigo_2/RequestProject/BitComplexity.lean:266`.

## III.12.3 — fases sincronizadas

Original: **17.3**. Página do volume: **71**. Estado: `prova_textual_sincronizada`.

A demonstracao Lean evita aplicar o envelope C2 global a uma funcao quadratica por partes que pode nao ser C2. Manter o enunciado e atualizar a demonstracao textual em etapa posterior. [13/11/2026] Demonstracao textual sincronizada com Artigo.synchronized_phases, preservando o enunciado e sem invocar o envelope C2 global para a funcao quadratica por partes. PDF recompilado nesta rodada.

Fonte: `tex/partes/artigo_2.tex:2860`; rótulo `map:artigo_2:12.3`.

- `Artigo.synchronized_phases` — `lean4/ambientes/artigo_2/RequestProject/DyadicSync.lean:99`.

## IV.5.5 — reversão aproximada quantizada

Original: **20.5**. Página do volume: **90**. Estado: `nao_formalizado_no_acervo`.

Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Fonte: `tex/partes/artigo_3.tex:950`; rótulo `map:artigo_3:5.5`.

Nenhuma declaração Lean localizada para este ambiente.

## IV.5.6 — redes profundas medidas pela função realizada

Original: **20.6**. Página do volume: **91**. Estado: `nao_formalizado_no_acervo`.

Nao foi localizado resultado Lean que certifique este enunciado. Fase3 e uma etapa da formalizacao do Artigo 1, nao o atual Artigo 3.

Fonte: `tex/partes/artigo_3.tex:1012`; rótulo `map:artigo_3:5.6`.

Nenhuma declaração Lean localizada para este ambiente.

