> **Instruções atuais para Codex e Antigravity:** [AGENTS.md](AGENTS.md).
> Registros anteriores de divisão de tarefas são históricos.

# Biblioteca unificada — estado verificado em 13/11/2026

O pacote foi auditado, mas ainda há pendências de formalização (quatro casos sem
fechamento, já consistente entre PDF e mapa). O PDF tem
**122 páginas**; `Biblioteca_Unificada.pdf` e `tex/principal.pdf` são idênticos.
Os enunciados matemáticos numerados e a prova reescrita de III.12.3 foram
preservados byte a byte em relação ao início desta sessão.

Dos **151 ambientes**, **140 são formalizáveis** e 11 são observações. O mapa registra:

| Estado | Quantidade |
|---|---:|
| Prova Lean formalizada e compilada | 37 |
| Correspondência inspecionada, herdada | 77 |
| Integrado à base, herdado | 20 |
| Não formalizado no acervo | 2 |
| Cobertura parcial | 2 |
| Observação editorial | 10 |
| Divergência documentada | 1 |
| Generalização documentada | 1 |
| Prova textual sincronizada | 1 |

No dossiê dos **42 casos originais**, são **37 fechados em Lean e 1 sincronizado
textualmente**, totalizando 38 casos tratados, com **4 ainda sem fechamento**.
São III.9.1, III.9.3, IV.5.5 e IV.5.6. As correspondências herdadas não
são contadas como novas provas semanticamente auditadas.

**IV.5.4 foi fechado nas duas direções com a cota inversa corrigida.** A cota impressa
era falsa (`R(x)=x`, `M=0`, `D=0`, `W=1`); o texto agora traz
`log₂ H_can ≤ 5[(M+1)log₂(2W)+D+log₂(M+1)]` (fator `M+1`, constante explícita), provada em
`Pendencias/AlturaInversa.lean`. A ida (forma ancorada, código prefix-free de
`≤ 40·N·⌊log₂ 2H⌋` bits) está em `FormaAncorada.lean` e `CodigoAncorado.lean`
(`Ancorada.direct_part`). Ressalva: a forma reduzida é a estrutura `Anchored`, sem ponte
formal para `RealReLU`. Enunciado original, contraexemplo e auditorias:
`verificacao/IV_5_4/` e `verificacao/lean/ContraexemploAltura.lean`.

**IV.5.2 foi fechado nesta rodada**, com o teorema completo
`RealReLU.exact_shallow_reversal`: equivalência para parâmetros reais, árvore
canônica mínima única inclusive dos rótulos, ambas as cotas explícitas de folhas
e condição sem regiões planas para a biblioteca original. A correspondência de
cada conclusão está em `verificacao/fidelidade_IV_5_2.md`.

**IV.5.9 também foi fechado nesta rodada:** `Pendencias.PenteGemini.critical_tent_comb`
formaliza continuidade, taxa de aproximação para todo `N ≥ 1` na biblioteca
original e as duas exclusões Besov. Codex compilou o módulo, verificou a
correspondência com o TeX e integrou a cópia em `Pendencias/Pente.lean`.
Evidência: `colaboracao/codex/REVISAO_IV_5_9.md` e
`compilar_pendencias/logs/20261113-142704/`.

## Orientação de execução

Codex e Antigravity podem trabalhar em todas as pendências, integrar provas prontas
e executar o gate global. As instruções operacionais consolidadas estão em
`AGENTS.md` e `gemini.md`; a divisão anterior por agente foi encerrada.

## Onde começar

| Conteúdo | Caminho |
|---|---|
| Instruções consolidadas para os agentes | `AGENTS.md`, `gemini.md` |
| Material obsoleto | enviado à lixeira do sistema em 13/11/2026 (inclui a pasta IV.5.4 antiga) |
| PDF unificado | `Biblioteca_Unificada.pdf` |
| LaTeX modular, fonte de edição | `tex/principal.tex`, `tex/partes/` |
| Fonte único gerado | `tex/documento_completo.tex` |
| Correspondência resultado → Lean → estado | `mapas/MAPA_TEX_LEAN.md` |
| Matriz com páginas e linhas | `mapas/correspondencia_completa.json` e `.csv` |
| Registro persistente de 37 casos tratados | `mapas/formalizacoes_pendencias.json` |
| Ambientes Lean compiláveis | `lean4/ambientes/` |
| Cópias Lean para leitura, geradas | `lean4/por_parte/` |
| Provas das rodadas recentes | `lean4/ambientes/artigo_2/Pendencias/README.md` |
| Provas complementares da Parte I | `lean4/ambientes/base_integrada/PendenciasParte1/README.md` |
| Dossiês | `pendencias_restantes/` (os antigos foram para a lixeira) |
| Figuras PDF/SVG/PNG a 600 dpi | `tex/figuras/`, `mapas/FIGURAS_E_USOS.md` |
| Auditoria atual | `verificacao/auditoria_final.json`, `verificacao/resultado_editorial.json` |
| Último gate global Lean/axiomas | `verificacao/compilacao_atual.json`, logs em `compilar_pendencias/logs/20261113-142704/` |
| Histórico desta execução | `LOG_TRABALHO.md` |

`fontes_originais/` e `historico/` são preservados, somente para leitura. Os dossiês
`pendencias_restantes/contexto/` são fotografias antigas para consulta; o estado atual
vem do mapa e de `STATUS_AUTOMATICO.md`. O PDF de 114 páginas é histórico; as edições
intermediárias de 116 e 117 páginas não representam o pacote sincronizado atual.

## Partes e numeração

| Parte | Conteúdo | Ambientes |
|---|---|---:|
| I | Biblioteca, endereçamento, aproximação e refinamento | 24 |
| II | Normalização e equivalência das montagens | 40 |
| III | Custos, entropia, programação dinâmica e interpolação | 59 |
| IV | Agendas de altura, teoria direta–inversa e ReLU | 24 |
| V | Complementos das seções 6 e 21 originais | 4 |

Os 108 ambientes do manuscrito original de 77 páginas estão contidos nos 151, não
são somados a eles. `III.3.12` identifica Parte III, seção 3, ambiente 12; os rótulos
`map:...` permanecem estáveis. A pasta Lean `Fase3` pertence à base do Artigo 1.

## Compilar e verificar

Lean/Mathlib estão fixados em **4.28.0**. Os caches `.lake` existem nesta cópia de
trabalho; são grandes e devem ser excluídos de qualquer arquivo de distribuição.
Não apague os caches nem os logs. Para uma cópia sem cache, execute `lake exe cache get`
em cada ambiente antes do primeiro build; esse download precisa de rede e espaço.

O ambiente TeX/Python local já instalado pode ser ativado assim:

```bash
export PATH="$HOME/.elan/bin:$PATH"
source /home/victor/Projetos/Arquivos_Extraidos_2026-11-13/tex-env.sh
source /home/victor/Projetos/Arquivos_Extraidos_2026-11-13/.venv/bin/activate
./compilar_pendencias/compilar_tudo.sh --so-status
./compilar_pendencias/compilar_tudo.sh --axiomas
python3 -I scripts/verificar_entrega.py
python3 -I verificacao/auditar_pacote.py final
sha256sum -c SHA256SUMS.txt --quiet
```

A compilação usa `lean4/ambientes/`, não as cópias por parte. O alvo de `artigo_2` é
`Pendencias`; o de `base_integrada` é `PendenciasParte1`; o de `parte_1` é
`ValidationAll`. A auditoria suplementar de toda a Parte I usa
`lake env lean AuditoriaPacote.lean` nesse último ambiente.

## Reconstruir sem perder as provas

O patch de reconstrução foi autorizado e aplicado nesta sessão. O registro persistente
inclui as duas rodadas anteriores, os oito resultados iniciais de 13/11, IV.5.2
e III.12.3. Os trechos
editoriais reaplicam a prova textual já existente e tornam os identificadores dos
apêndices únicos no PDF. A reconstrução foi testada em cópia isolada antes de rodar
neste pacote.

Faça backup antes de reconstruir, conforme `AGENTS.md`. Ordem:

```bash
python3 -I -B scripts/reconstruir.py
# Restaurar o bloco PendenciasParte1 de base_integrada/lakefile.toml;
# reconstruir.py ainda repõe o lakefile original desse ambiente.
(cd tex && pdflatex -interaction=nonstopmode -halt-on-error principal.tex)
(cd tex && latexmk -pdf -interaction=nonstopmode -halt-on-error principal.tex)
python3 -I scripts/preencher_linha_lean.py .
python3 -I scripts/verificar_entrega.py
python3 -I scripts/finalizar.py
./compilar_pendencias/compilar_tudo.sh --axiomas
python3 -I verificacao/auditar_pacote.py final
```

`finalizar.py` roda depois do último `latexmk`. Ele gera o fonte único, as cópias por
parte e o PDF da raiz; não edite esses derivados à mão. Rode a reconstrução antes de
repetir `finalizar.py`, pois o finalizador acrescenta uma nota aos índices por parte.
Exporte figuras novamente apenas se elas mudarem. Recalcule `SHA256SUMS.txt` após a
última alteração; `.lake` e `compilar_pendencias/logs/` ficam fora do manifesto.

## Evidências e limites

A auditoria estrutural confere os 151 ambientes, 108 originais e 348 associações a
Lean após a integração de IV.5.9; 108 ocorrências de fontes recebidos foram
comparadas byte a byte. A auditoria
do PDF confere 108 entradas visíveis de sumário, seus destinos e títulos, 17 figuras
em cada formato, fontes incorporadas e ausência de páginas vazias, referências
quebradas e avisos LaTeX proibidos. Foram inspecionadas visualmente páginas de
abertura, apêndices, texto matemático, tabelas longas e bibliografia.

A bibliografia conserva 49 entradas, 48 citadas nos corpos das partes. A entrada
recebida `artigo_2-stern1858`, sem citação no corpo, foi preservada; nenhuma referência
nova foi acrescentada.

Compilação Lean, correspondência editorial e equivalência semântica são evidências
distintas. O pacote não declara formalização integral nem transforma o contraexemplo
de IV.5.4 em prova da proposição.
