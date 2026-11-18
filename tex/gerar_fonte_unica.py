#!/usr/bin/env python3
"""Gera documento_completo.tex expandindo as inclusões de principal.tex."""

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
    texto = expandir(ROOT / "principal.tex")
    destino = ROOT / "documento_completo.tex"
    destino.write_text(
        "% Gerado por gerar_fonte_unica.py; editar principal.tex e seus arquivos incluídos.\n"
        "% Bibliografia incorporada; figuras compartilhadas de ../tex/figuras/.\n" + texto,
        encoding="utf-8",
    )
    print(destino)


if __name__ == "__main__":
    main()
