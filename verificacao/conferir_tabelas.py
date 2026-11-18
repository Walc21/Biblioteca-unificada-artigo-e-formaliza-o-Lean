#!/usr/bin/env python3
"""Compara as linhas das tabelas geradas com as duas edições TeX."""

import argparse
from difflib import unified_diff
from pathlib import Path
import re


TABLES = {
    "artigo_1:tab:interpolante-exp": ("reproduzir_curvas", "interpolante_exp"),
    "artigo_2:tab:joint-budget-pt": ("reproduzir_curvas", "orcamento_conjunto"),
    "artigo_2:tab:dp-audit": ("seletor_dinamico_exato", "auditoria_selecao"),
    "artigo_2:tab:selector-comparison": ("seletor_dinamico_exato", "comparacao_seletores"),
    "artigo_2:tab:quadratic-exact": ("constante_diadica", "constante_quadratica"),
    "artigo_2:tab:smooth-diagnostics": ("constante_diadica", "diagnosticos_assintoticos"),
    "artigo_2:tab:dyadic-constants-audit": ("constante_diadica", "auditoria_constante"),
    "artigo_2:tab:codificacoes-pt": ("reproduzir_curvas", "codificacoes"),
    "artigo_2:tab:codebook-pt": ("reproduzir_curvas", "codebook"),
    "artigo_2:tab:enderecos-pt": ("reproduzir_curvas", "enderecos"),
    "artigo_3:tab:height-schedules": ("espacos_aproximacao", "agendas_altura"),
    "artigo_3:tab:height-audit": ("espacos_aproximacao", "auditoria_altura"),
    "artigo_3:tab:deep-tent-network": ("restricoes_rede", "tenda_rede"),
    "artigo_3:tab:approximate-reverse-audit": ("reversibilidade_regularizada", "reversao_aproximada"),
    "artigo_3:tab:kink-regularized-certificate": ("reversibilidade_regularizada", "certificado_quina"),
}
REPO = Path(__file__).resolve().parent.parent


def table_rows(tex: str, source: Path) -> list[str]:
    match = re.search(r"\\midrule(.*?)\\bottomrule", tex, re.DOTALL)
    if match is None:
        raise ValueError(f"Corpo da tabela ausente em {source}")
    body = match[1].replace("{,}", ".")
    body = re.sub(r"(?<=\d)\\,(?=\d{3}\b)", "", body)  # separador de milhar
    body = re.sub(r"(?<=\d);(?=\s+\d)", ",", body)     # separador de intervalo
    return [re.sub(r"\s+", "", row) for row in body.split(r"\\") if row.strip()]


def published_tables(edition: Path) -> dict[str, str]:
    result = {}
    for part in edition.glob("partes/artigo_*.tex"):
        for match in re.finditer(r"\\begin\{table\}.*?\\end\{table\}", part.read_text(encoding="utf-8"), re.DOTALL):
            label = re.search(r"\\label\{([^}]+)\}", match[0])
            if label is not None and label[1] in TABLES:
                if label[1] in result:
                    raise ValueError(f"Rótulo duplicado em {edition}: {label[1]}")
                result[label[1]] = match[0]
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", type=Path, required=True, help="saída de reproduzir_tudo.py")
    args = parser.parse_args()
    success = True
    for name in ("tex", "tex_abnt"):
        edition = REPO / name
        published = published_tables(edition)
        for label, (program, table) in TABLES.items():
            generated = args.output_root / program / "artigo" / "secoes" / f"tab_{table}.tex"
            if label not in published or not generated.is_file():
                print(f"{name}, {label}: falta o rótulo publicado ou o arquivo {generated}")
                success = False
                continue
            original_rows = table_rows(published[label], edition)
            generated_rows = table_rows(generated.read_text(encoding="utf-8"), generated)
            if original_rows != generated_rows:
                print("\n".join(unified_diff(original_rows, generated_rows, f"{name}/{label}", str(generated), lineterm="")))
                success = False
    if not success:
        raise SystemExit(1)
    print(f"{len(TABLES)} tabelas conferidas em cada edição.")


if __name__ == "__main__":
    main()
