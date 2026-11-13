# Relatório histórico de reprodutibilidade

> Registro da versão anterior à revisão de 8 de agosto de 2026. A composição
> IEEE em português foi retirada da entrega corrigida; consulte
> `RELATORIO_DE_CORRECOES_2026.pdf` para o protocolo vigente.

O artigo possui um único núcleo matemático compartilhado pelas edições nacional e IEEE. A compilação executa seis suítes determinísticas: biblioteca e codificação; seleção dinâmica; constante diádica; espaços de aproximação; restrições ReLU; reversibilidade regularizada.

A auditoria estática verifica:

- unicidade de rótulos e resolução de referências internas;
- resolução de todas as chaves bibliográficas;
- identidade da ordem das seções entre as duas edições;
- equilíbrio dos ambientes matemáticos;
- ausência de linguagem editorial de versionamento no corpo ativo.

A auditoria dos PDFs verifica metadados, extensão mínima e presença textual dos três resultados centrais: a lei do conjunto de acumulação, a obstrução à quase-norma e a reversibilidade regularizada.

O arquivo `SHA256SUMS.txt` cobre todos os arquivos de distribuição, exceto o próprio manifesto e resíduos temporários de compilação.

## Resultado da construção de referência

- edição nacional: 71 páginas em A4;
- edição IEEE: 59 páginas em papel Carta, classe oficial `IEEEtran`;
- 4.096 conversões exatas entre montagens e redes na auditoria da biblioteca;
- 2.952 idas e voltas exatas na auditoria de reversibilidade;
- 84 reversões aproximadas e 1.260 certificados triangulares;
- fontes sem rótulos ou citações indefinidos e sem marcas editoriais de versionamento;
- composição sem caixas excedentes e com todas as fontes incorporadas;
- inspeção visual integral das 130 páginas.
