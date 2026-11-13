# Biblioteca matemática consolidada

Consolidação de 31/10/2026 de todo o conteúdo autoral disponível em `/home/victor/Projetos`, incluindo o interior dos nove pacotes ZIP/TAR.GZ. Os originais permanecem nos seus lugares. A raiz corrente é [FORMALIZACAO_COMPLETA_DA_BIBLIOTECA](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/README.md); versões antigas não substituem essa edição.

## Leitura por divisão matemática

| Divisão | PDF e fontes | Formalização e estado |
|---|---|---|
| Artigo 1 | [PDF, 17 páginas](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_1/artigo.pdf); [LaTeX](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_1/artigo.tex) | 24 ambientes; base `Unified/Fase1`, `Fase2`, `Fase3` e pontes semânticas. |
| Artigo 2 | [PDF, 42 páginas](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_2/Artigo_2.pdf); [LaTeX](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_2/Artigo_2.tex) | 59 ambientes; 31 módulos em `entradas/artigo_2/RequestProject`, ambiente próprio em `validacao/artigo_2`. Revisão semântica pendente. |
| Artigo 3 | [PDF, 20 páginas](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_3/Artigo_3.pdf); [LaTeX](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_3/Artigo_3.tex) | 24 ambientes; formalização integral permanece aberta. `Fase3` é uma fase do Artigo 1, não a formalização do Artigo 3. |
| Normalização da Parte I | [LaTeX](<FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/entradas/parte_1/Solucao_Equivalencia_Montagens_Parte_1%20(1).tex>) | 40 ambientes; nove módulos recebidos e seis pontes `Unified/SemanticBridge/Normalization*`. |
| Complemento | [PDF, 3 páginas](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/complemento_original_77/complemento.pdf); [LaTeX](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/complemento_original_77/complemento.tex) | Quatro resultados do original, com demonstrações matemáticas; provas Lean ainda não localizadas. |
| Original integral | [PDF, 77 páginas](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/entradas/original_77_paginas/Biblioteca_Deterministica_Artigo_Unificado_Revisado.pdf) | Preservado com fontes, reprodução e auditorias. Seus 108 ambientes têm destino na divisão editorial; não somar novamente aos 151 ambientes atuais. |

Consultar a [matriz de correspondência](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/documentacao/CORRESPONDENCIA_ARTIGOS.md), o [destino do original](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/documentacao/CONFERENCIA_ORIGINAL_77.md) e o [relatório matemático](FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/documentacao/RESULTADO_FINAL.md). Os links absolutos de documentos históricos registram o local de origem; a navegação desta página usa caminhos internos ao pacote.

## O que foi refinado nesta entrega

Foram inventariadas 1.071 ocorrências de arquivos, com 489 conteúdos distintos por SHA-256, incluindo 139 conteúdos Lean distintos. O conteúdo corrente foi preservado byte a byte e os links internos foram convertidos em arquivos/diretórios comuns para facilitar a extração. Os nove contêineres antigos foram substituídos pelos seus membros, evitando ZIP dentro de ZIP. Setenta e nove conteúdos únicos exteriores à raiz corrente estão no [índice complementar](COMPLEMENTARES.md), com procedência e acesso direto.

`CATALOGO.json` relaciona cada caminho de origem ao conteúdo preservado. `RESTAURAR_HISTORICO.py DESTINO_NOVO` recompõe todas as árvores autorais, incluindo pacotes expandidos, em uma pasta nova. O arquivo antigo comprimido não é reconstruído byte a byte; seus membros são preservados sem alteração. Não se executaram scripts históricos nem se incorporaram variantes antigas como novas provas.

Foram omitidos somente dependências, ambientes virtuais e caches regeneráveis (`.lake`, `.venv` etc.), relacionados no catálogo. Figuras, PDFs, bibliografias, dados, scripts, evidências, fontes de origem e frentes incompletas permanecem preservados. As cópias necessárias para executar os ambientes atuais foram mantidas; o acervo complementar é deduplicado por conteúdo.

## Verificação e reprodução

A compactação compara DEFLATE, BZIP2, LZMA e armazenamento direto por arquivo, escolhendo o menor conteúdo comprimido. Usar um extrator com suporte a ZIP BZIP2/LZMA; Python 3 também extrai com `python3 -m zipfile -e Biblioteca_Consolidada_2026-10-31.zip DESTINO`.

Execute `python3 VERIFICAR_ENTREGA.py` na pasta extraída para verificar o manifesto e todas as correspondências do catálogo. O manifesto protege todos os arquivos da entrega, exceto ele próprio.

As provas usam Lean/Mathlib 4.28.0, com a revisão das dependências fixada nos arquivos `lake-manifest.json`. Para reconstruir, instalar a versão indicada por `lean-toolchain` e, em cada ambiente, obter as dependências/cache com `lake exe cache get`. Será necessário acesso à rede e espaço para recriar os artefatos omitidos.

Na raiz corrente, executar `bash executar.sh` e `lake env lean AuditoriaIntegracao.lean`. Para os pacotes isolados, executar `python3 scripts/validar_pacotes.py`. Os diretórios `validacao/parte_1/RequestProject` e `validacao/artigo_2/RequestProject` já contêm os fontes necessários, sem links simbólicos.

Os registros desta conferência estão em `verificacao_2026-10-31/`. A compilação atual foi executada na raiz de origem; o ZIP foi verificado separadamente quanto a conteúdo e extração. Evidências de 22/10 permanecem como registros históricos com suas datas originais. Alguns verificadores históricos de preservação consultam caminhos absolutos da máquina de origem; para integridade desta entrega, usar `VERIFICAR_ENTREGA.py`.

## Limites matemáticos preservados

A entrega consolida o progresso existente; não declara concluída a formalização integral dos artigos. Permanecem as pontes C², árvores em raiz única, execução de recorrências e custos do Artigo 2, a divergência textual `g(t₀)`, a formalização integral do Artigo 3 e do complemento. O documento auxiliar histórico de fechamento continua parcialmente recuperado. Compilação e auditoria de axiomas não eliminam essas diferenças semânticas. As contagens de declarações de auditorias diferentes se sobrepõem.
