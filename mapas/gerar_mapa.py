#!/usr/bin/env python3
"""Gera mapas/MAPA_TEX_LEAN.md a partir de mapas/dados/mapa.json.

O JSON é a fonte da correspondência. As linhas do TeX são calculadas a partir
dos rótulos `\\label{map:...}` em tex/partes/, de modo que o mapa nunca aponta
para uma linha velha. A verificação dos nomes Lean fica em verificar_mapa.py.

Uso:
    python3 mapas/gerar_mapa.py                 # escreve mapas/MAPA_TEX_LEAN.md
    python3 mapas/gerar_mapa.py --verificar     # falha se o arquivo estiver desatualizado
    python3 mapas/gerar_mapa.py --tex OUTRA/tex --saida /tmp/mapa.md   # para testes
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

RAIZ = Path(__file__).resolve().parent.parent
DADOS = RAIZ / "mapas" / "dados" / "mapa.json"
SAIDA_PADRAO = RAIZ / "mapas" / "MAPA_TEX_LEAN.md"
TEX_PADRAO = RAIZ / "tex"


def linha_do_rotulo(tex: Path, arquivo: str, rotulo: str) -> int:
    """Número (1-based) da única linha que define `\\label{rotulo}` no arquivo indicado."""
    caminho = tex / "partes" / arquivo
    if not caminho.is_file():
        raise ValueError(f"arquivo inexistente para o rótulo {rotulo!r}: {caminho}")
    alvo = "\\label{" + rotulo + "}"
    linhas = [
        n for n, texto in enumerate(caminho.read_text(encoding="utf-8").split("\n"), 1)
        if alvo in texto
    ]
    if len(linhas) != 1:
        raise ValueError(f"o rótulo {rotulo!r} aparece {len(linhas)} vezes em {caminho}")
    return linhas[0]


def gerar(dados: dict, tex: Path) -> str:
    saida: list[str] = dados["cabecalho"].rstrip("\n").split("\n") + [""]
    parte_atual = None
    for entrada in dados["entradas"]:
        if entrada["parte"] != parte_atual:
            if parte_atual is not None:
                saida.append("")
            parte_atual = entrada["parte"]
            saida += [f"## Parte {parte_atual}", ""]
        saida += [f"## {entrada['id']} — {entrada['titulo']}", ""]
        if entrada["original"] is not None:
            saida += [f"Original de 77 páginas: {entrada['original']}.", ""]
        if entrada["rotulo"]:
            n = linha_do_rotulo(tex, entrada["arquivo_tex"], entrada["rotulo"])
            arq = entrada["arquivo_tex"]
            saida += [
                f"Fonte editável: [tex/partes/{arq}:{n}](../tex/partes/{arq}); "
                f"rótulo `{entrada['rotulo']}`.",
                "",
            ]
        if entrada["estado"]:
            estado_linhas = (f"Estado: **{entrada['estado']}**" + entrada["estado_sufixo"]).split("\n")
            saida += estado_linhas + [""]
        for bloco in entrada["corpo"]:
            saida += bloco.split("\n") + [""]
        if entrada["lean"]:
            for ref in entrada["lean"]:
                if ref.get("quebra_antes"):
                    saida.append("")
                saida.append(
                    f"- [`{ref['nome']}`]({ref['arquivo']}) — linha {ref['linha']}.{ref['nota']}"
                )
            saida.append("")
    while saida and saida[-1] == "":
        saida.pop()
    return "\n".join(saida) + "\n"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dados", type=Path, default=DADOS)
    parser.add_argument("--tex", type=Path, default=TEX_PADRAO, help="diretório com partes/")
    parser.add_argument("--saida", type=Path, default=SAIDA_PADRAO)
    parser.add_argument("--verificar", action="store_true",
                        help="não escreve; falha se --saida não for igual ao gerado")
    args = parser.parse_args(argv)

    dados = json.loads(args.dados.read_text(encoding="utf-8"))
    texto = gerar(dados, args.tex)

    if args.verificar:
        atual = args.saida.read_text(encoding="utf-8") if args.saida.exists() else ""
        if atual != texto:
            print(f"{args.saida} está desatualizado; rode python3 mapas/gerar_mapa.py", file=sys.stderr)
            return 1
        print(f"{args.saida} está atualizado ({len(dados['entradas'])} entradas)")
        return 0

    args.saida.write_text(texto, encoding="utf-8")
    print(f"{args.saida} gerado ({len(dados['entradas'])} entradas)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
