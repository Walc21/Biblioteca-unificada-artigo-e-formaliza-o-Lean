# Biblioteca determinística de segmentos afins em células diádicas

Pacote reproduzível da versão unificada corrigida.

- `Biblioteca_Deterministica_Artigo_Unificado_Revisado.pdf`: documento-sistema em português, A4 e uma coluna;
- `artigo/artigo_nacional.tex`: fonte mestre;
- `artigo/secoes/`: seções independentes;
- `reproducibility/biblioteca/`: indexação, gerador, aproximação, codificação e figuras;
- `reproducibility/selecao/`: seleção exata, constantes diádicas, espaços de aproximação e reversibilidade;
- `auditoria/RELATORIO_DE_CORRECOES_2026.pdf`: relatório detalhado desta revisão;
- `publicacao/`: mapas de desmembramento editorial A/B/C e do apêndice residual R;
- `SHA256SUMS.txt`: manifesto de integridade.

## Decisão sobre a antiga composição IEEE

A composição `IEEEtran` em português foi retirada: ela não era uma edição submissível e manter o nome “IEEE” induziria a uma qualificação editorial incorreta. O documento unificado continua integralmente preservado na edição nacional. Os mapas em `publicacao/` definem as três peças editoriais recomendadas; traduções integrais e submissões devem ser produzidas apenas quando cada manuscrito independente estiver estabilizado e revisado pelo autor.

## Recompilação completa

Requisitos: Python 3.10+, NumPy, Matplotlib, `latexmk`, pdfLaTeX, BibTeX, Poppler e `pypdf`.

```bash
./compilar.sh
```

O comando regenera resultados, tabelas e figuras, executa a auditoria estática, compila o PDF, verifica referências e metadados e atualiza o manifesto SHA-256.

## Verificação

```bash
./verificar.sh
```

O comando confere o manifesto, fontes, rótulos, citações, correções matemáticas exigidas, chamadas de figuras e tabelas e o PDF final.

## Identificadores externos

ORCID, arXiv e DOI de repositório não foram fornecidos. Nenhum identificador foi inventado. Após o depósito público, esses campos devem ser atualizados nas declarações editoriais e no relatório.
