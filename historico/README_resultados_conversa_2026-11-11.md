# Resultados da conversa — Biblioteca ALPHAGOD (11/11/2026)

Estado: **27 de 42** casos pendentes do volume foram fechados; **15** continuam em aberto.

## Estrutura

- `1_formalizadas_lean/` — provas Lean compiladas (Lean/Mathlib 4.28.0), sem `sorry`.
  - `artigo_2/` — biblioteca `Pendencias` (`lake build Pendencias`).
  - `base_integrada/` — biblioteca `PendenciasParte1` (`lake build PendenciasParte1`), Parte I.
  - Cada pasta traz `lakefile.toml`, o módulo raiz, o arquivo de auditoria e o log de `#print axioms`.
  - O `README.md` dentro de `artigo_2/Pendencias/` tem a tabela item → arquivo → teorema.
- `2_latex/` — fontes LaTeX do volume.
  - `tex/` — todas as partes (modular e documento único), inclusive a alteração de III.12.3.
  - `alteracoes/III12.3_alteracao.diff` — diff exato da demonstração reescrita de III.12.3.
  - `alteracoes/artigo_2_copia_pendencias.tex` — cópia do `artigo_2.tex` alterado.
- `3_documentacao/` — lacunas, mapa TeX↔Lean, índices, `LEIA_PRIMEIRO.md`, `SHA256SUMS.txt`
  e a pasta `pendencias_restantes/` com as 15 que faltam.

## Itens fechados (27)

| Rodada | Itens | Onde |
|---|---|---|
| 1 | III.2.3, III.3.15, III.3.16, III.3.17, III.3.18, III.11.2, III.11.3, III.12.1, IV.3.1, IV.4.5, IV.4.6, V.21.1 | `artigo_2/Pendencias/` |
| 2 | I.6.3, I.6.4 | `base_integrada/PendenciasParte1/` |
| 2 | III.3.12, III.3.25, III.6.3, III.7.4 | `artigo_2/Pendencias/` |
| 2 | IV.3.2, IV.3.3, IV.5.1, IV.5.3, IV.5.7, IV.5.8, IV.5.10, V.6.1 | `artigo_2/Pendencias/` |
| 2 | III.12.3 (demonstração textual reescrita) | `2_latex/tex/partes/artigo_2.tex` |

## Pendências (15)

Veja `3_documentacao/pendencias_restantes/README.md` (um arquivo por item, com enunciado, contexto e
reaproveitamento).

## Ressalvas

- **O PDF não foi recompilado.** `Biblioteca_Unificada.pdf` continua sendo a versão anterior à
  reescrita de III.12.3, porque não há TeX instalado nesta máquina. Para recompilar:
  ```bash
  latexmk -cd -pdf -interaction=nonstopmode -halt-on-error tex/principal.tex
  ```
- **Definições de escolha.** Algumas definições foram feitas por mim (por exemplo `FRMIcc`,
  `curvIOn`, `Sigma`, `pErr`, `omega2`, `MAtom`, `DPprog`); estão documentadas nos READMEs.
- **Itens de definição.** IV.5.1 e IV.5.3 foram fechados com definições e propriedades básicas,
  não com a reversibilidade (IV.5.2, ainda aberto).
- **Contrato do I.6.4.** A cota M_int ≤ M* nas células certificadas é hipótese, como no contrato (40) do texto.
- **Teste executável.** O programa de III.3.25 foi testado com `#eval` em parâmetros pequenos
  (ver `axiomas_pendencias.log`); H = 3 ficou pesado demais para testar.

## Como reproduzir

Os ambientes Lean completos (`RequestProject`, `Unified`, `.lake`) estão na biblioteca
`~/Projetos/Biblioteca_ALPHAGOD/Biblioteca_Reconstruida/lean4/ambientes/`, não neste zip, por tamanho.
Para compilar a partir daqui, copie as pastas `Pendencias` e `PendenciasParte1` para os ambientes correspondentes.
