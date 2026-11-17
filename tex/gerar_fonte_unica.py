#!/usr/bin/env python3
"""Gera documento_completo.tex a partir de principal.tex e principal.bbl."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent


def expandir(path: Path, pilha: tuple[Path, ...] = ()) -> str:
    path = path.resolve()
    if path in pilha:
        raise ValueError(f"Inclusão recursiva: {path}")
    texto = path.read_text(encoding="utf-8")

    def incluir(match: re.Match[str]) -> str:
        arquivo = path.parent / match.group(1)
        if not arquivo.suffix:
            arquivo = arquivo.with_suffix(".tex")
        return expandir(arquivo, (*pilha, path))

    return re.sub(r"\\input\{([^}]+)\}", incluir, texto)


def main() -> None:
    bbl = ROOT / "principal.bbl"
    if not bbl.is_file():
        raise SystemExit("Compile principal.tex com latexmk antes de gerar a fonte única.")
    texto = expandir(ROOT / "principal.tex")
    texto = re.sub(r"\\bibliographystyle\{[^}]+\}", "", texto)
    texto, substituicoes = re.subn(
        r"\\bibliography\{[^}]+\}",
        lambda _: bbl.read_text(encoding="utf-8"),
        texto,
    )
    if substituicoes != 1:
        raise ValueError("Era esperada exatamente uma bibliografia.")
    destino = ROOT / "documento_completo.tex"
    destino.write_text(
        "% Gerado por gerar_fonte_unica.py; editar principal.tex e seus arquivos incluídos.\n"
        "% Bibliografia incorporada; figuras externas relativas a esta pasta.\n" + texto,
        encoding="utf-8",
    )
    print(destino)


if __name__ == "__main__":
    main()
