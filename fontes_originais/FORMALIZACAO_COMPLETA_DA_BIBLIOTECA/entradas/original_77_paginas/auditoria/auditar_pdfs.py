#!/usr/bin/env python3
"""Verificações estruturais e textuais dos PDFs finais."""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

from pypdf import PdfReader


REQUIRED_PHRASES = (
    "conjunto de acumulação",
    "não é uma quase-norma",
    "funcional de realização",
    "uniformes sobre bolas",
    "complexidade de bits",
)

# Sobrenomes que cobrem as 12 entradas antes presentes no .bib, mas ausentes
# das chamadas bibliográficas. A busca é feita somente depois do cabeçalho da
# bibliografia, para não confundir uma citação no corpo com uma entrada final.
INTEGRATED_REFERENCE_ANCHORS = (
    "Bellman",
    "Birman",
    "Blanchard",
    "Breiman",
    "Donoho",
    "Petrushev",
    "Schumaker",
    "Stone",
    "Telgarsky",
    "Yarotsky",
    "Hristov",
    "Gühring",
    "Burchard",
    "Elbrächter",
    "Petersen",
    "Elias",
    "Cover",
    "Pérez",
    "Kesseböhmer",
)


def bibliography_text(text: str) -> str | None:
    heading = re.compile(
        r"(?im)^\s*(?:referências|r\s*e\s*f\s*e\s*r\s*e\s*n\s*c\s*e\s*s)\s*$"
    )
    matches = list(heading.finditer(text))
    if not matches:
        return None
    return text[matches[-1].end() :]


def pdf_text(path: Path) -> str:
    proc = subprocess.run(
        ["pdftotext", str(path), "-"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return proc.stdout


def main(paths: list[str]) -> int:
    errors: list[str] = []
    for raw in paths:
        path = Path(raw).resolve()
        if not path.exists() or path.stat().st_size == 0:
            errors.append(f"PDF ausente ou vazio: {path}")
            continue
        reader = PdfReader(path)
        if len(reader.pages) < 20:
            errors.append(f"PDF inesperadamente curto ({len(reader.pages)} pp.): {path.name}")
        text = pdf_text(path)
        for phrase in REQUIRED_PHRASES:
            if phrase.lower() not in text.lower():
                errors.append(f"Expressão central ausente em {path.name}: {phrase}")
        bibliography = bibliography_text(text)
        if bibliography is None:
            errors.append(f"Seção bibliográfica ausente em {path.name}")
        else:
            missing_anchors = [
                anchor
                for anchor in INTEGRATED_REFERENCE_ANCHORS
                if anchor.lower() not in bibliography.lower()
            ]
            if missing_anchors:
                errors.append(
                    f"Entradas integradas ausentes da bibliografia de {path.name}: "
                    f"{missing_anchors}"
                )
        if re.search(r"(undefined references|citation.+undefined)", text, re.I):
            errors.append(f"Marcador de referência indefinida em {path.name}")
        metadata = reader.metadata or {}
        if "Victor Gabriel de Oliveira" not in str(metadata.get("/Author", "")):
            errors.append(f"Autor ausente dos metadados de {path.name}")
        if not str(metadata.get("/Keywords", "")).strip():
            errors.append(f"Palavras-chave ausentes dos metadados de {path.name}")

        # L-01: nenhum rótulo de referência cruzada pode sair em inglês no corpo
        # em português. O abstract inglês é excluído da varredura.
        corpo = text
        marca = "All computational identities are audited"
        if marca in corpo:
            corpo = corpo[corpo.index(marca) + len(marca):]
        vazamentos = sorted(
            {
                match.group(0).lower()
                for match in re.finditer(
                    r"\b(?:sections?|figures?|tables?|equations?|appendices)\b",
                    corpo,
                )
            }
        )
        if vazamentos:
            errors.append(
                f"L-01: rótulos de referência cruzada em inglês em {path.name}: "
                f"{vazamentos}"
            )
        print(f"{path.name}: {len(reader.pages)} páginas, {path.stat().st_size} bytes")

    if errors:
        for error in errors:
            print(f"ERRO: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
