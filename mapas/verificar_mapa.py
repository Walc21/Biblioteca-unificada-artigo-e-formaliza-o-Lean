#!/usr/bin/env python3
"""Verifica a correspondência TeX → Lean em mapas/dados/mapa.json.

Verificações, em ordem:

1. Estrutura: identificadores únicos, partes conhecidas, estados do vocabulário controlado.
2. Rótulos: o conjunto de `\\label{map:...}` em tex/partes/ é igual ao conjunto
   de rótulos do mapa, e cada rótulo aparece exatamente uma vez, no arquivo indicado.
3. Atualidade: MAPA_TEX_LEAN.md é exatamente o que gerar_mapa.py produz a partir dos dados.
4. Arquivos e linhas: cada referência Lean aponta para um arquivo existente, e a
   linha indicada contém o último componente do nome.
5. Existência no Lean: cada nome é checado com `#check @nome` pelo próprio Lean,
   no ambiente indicado pelo caminho (exige que os ambientes estejam compilados).

Não verifica o conteúdo das prosas nem a fidelidade semântica dos enunciados;
isso continua sendo a reauditoria documentada em documentacao/.

Uso (a partir da raiz do repositório, com os ambientes compilados):
    python3 mapas/verificar_mapa.py
    python3 mapas/verificar_mapa.py --sem-lean     # pula a etapa 5
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gerar_mapa  # noqa: E402

RAIZ = gerar_mapa.RAIZ
ESTADOS_VALIDOS = {
    "Correspondência confirmada",
    "Correspondência inspecionada",
    "Correspondência inspecionada com ressalva",
    "Correspondência parcial",
    "Integrado à base",
    "Formalizado e compilado",
    "Formalizado no modelo de custo explícito",
    "Formalizado no modelo `BitModel`",
    "Generalização documentada",
    "Observação editorial",
    "Prova textual nova e formalização Lean",
    "Prova textual sincronizada",
}
PARTES_VALIDAS = {"I", "II", "III", "IV", "V"}
AMBIENTES = RAIZ / "lean4" / "ambientes"
LABEL = re.compile(r"\\label\{(map:[^}]+)\}")


class Falhas:
    def __init__(self) -> None:
        self.itens: list[str] = []

    def add(self, msg: str) -> None:
        self.itens.append(msg)

    def relatorio(self, titulo: str) -> None:
        if self.itens:
            print(f"FALHA [{titulo}]: {len(self.itens)} problema(s)")
            for item in self.itens:
                print(f"  - {item}")
        else:
            print(f"ok    [{titulo}]")


def verificar_estrutura(dados: dict, f: Falhas) -> None:
    ids = [e["id"] for e in dados["entradas"]]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        f.add(f"identificador repetido: {dup}")
    for e in dados["entradas"]:
        if e["parte"] not in PARTES_VALIDAS:
            f.add(f"{e['id']}: parte desconhecida {e['parte']!r}")
        if e["estado"] not in ESTADOS_VALIDOS:
            f.add(f"{e['id']}: estado fora do vocabulário: {e['estado']!r}")
        if not e["rotulo"]:
            f.add(f"{e['id']}: sem rótulo TeX")


def verificar_rotulos(dados: dict, tex: Path, f: Falhas) -> None:
    no_mapa = {e["rotulo"] for e in dados["entradas"] if e["rotulo"]}
    no_tex: dict[str, list[str]] = defaultdict(list)
    for arq in sorted((tex / "partes").glob("*.tex")):
        for rot in LABEL.findall(arq.read_text(encoding="utf-8")):
            no_tex[rot].append(arq.name)
    for rot in sorted(no_mapa - set(no_tex)):
        f.add(f"rótulo do mapa ausente do TeX: {rot}")
    for rot in sorted(set(no_tex) - no_mapa):
        f.add(f"rótulo do TeX sem entrada no mapa: {rot}")
    for e in dados["entradas"]:
        rot = e["rotulo"]
        if not rot:
            continue
        arquivos = no_tex.get(rot, [])
        if len(arquivos) != 1:
            f.add(f"{e['id']}: {rot} aparece em {len(arquivos)} arquivo(s)")
        elif arquivos[0] != e["arquivo_tex"]:
            f.add(f"{e['id']}: {rot} está em {arquivos[0]}, o mapa indica {e['arquivo_tex']}")


def verificar_atualidade(dados: dict, tex: Path, saida: Path, f: Falhas) -> None:
    try:
        esperado = gerar_mapa.gerar(dados, tex)
    except ValueError as erro:
        f.add(str(erro))
        return
    atual = saida.read_text(encoding="utf-8") if saida.exists() else ""
    if atual != esperado:
        f.add(f"{saida.name} está desatualizado; rode python3 mapas/gerar_mapa.py")


def verificar_arquivos_e_linhas(dados: dict, f: Falhas) -> list[tuple[str, str, str, str]]:
    """Retorna (entrada, nome, caminho absoluto, ambiente) para a etapa Lean."""
    pendentes = []
    for e in dados["entradas"]:
        for ref in e["lean"]:
            alvo = (RAIZ / "mapas" / ref["arquivo"]).resolve()
            if not alvo.is_file():
                f.add(f"{e['id']}: arquivo inexistente {ref['arquivo']}")
                continue
            linhas = alvo.read_text(encoding="utf-8").split("\n")
            if not 1 <= ref["linha"] <= len(linhas):
                f.add(f"{e['id']}: {ref['nome']} aponta para a linha {ref['linha']}, fora do arquivo")
                continue
            curto = ref["nome"].split(".")[-1]
            if not re.search(r"\b" + re.escape(curto) + r"\b", linhas[ref["linha"] - 1]):
                f.add(f"{e['id']}: linha {ref['linha']} de {alvo.name} não contém {curto!r}")
            try:
                ambiente = alvo.relative_to(AMBIENTES).parts[0]
            except ValueError:
                f.add(f"{e['id']}: {ref['arquivo']} fora de lean4/ambientes/")
                continue
            pendentes.append((e["id"], ref["nome"], str(alvo), ambiente))
    return pendentes


def verificar_lean(pendentes: list[tuple[str, str, str, str]], f: Falhas) -> None:
    por_ambiente: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    for entrada, nome, caminho, ambiente in pendentes:
        por_ambiente[ambiente].append((entrada, nome, caminho))

    for ambiente, itens in sorted(por_ambiente.items()):
        raiz_amb = AMBIENTES / ambiente
        modulos = set()
        for _, _, caminho in itens:
            rel = Path(caminho).relative_to(raiz_amb).with_suffix("")
            modulos.add(".".join(rel.parts))
        linhas = [f"import {m}" for m in sorted(modulos)] + [""]
        mapa_linha: dict[int, tuple[str, str]] = {}
        for entrada, nome, _ in itens:
            mapa_linha[len(linhas) + 1] = (entrada, nome)
            linhas.append(f"#check @{nome}")
        with tempfile.TemporaryDirectory() as tmp:
            arq = Path(tmp) / "VerificaMapa.lean"
            arq.write_text("\n".join(linhas) + "\n", encoding="utf-8")
            proc = subprocess.run(
                ["lake", "env", "lean", str(arq)],
                cwd=raiz_amb, capture_output=True, text=True,
            )
        saida = proc.stdout + proc.stderr
        erros = re.findall(r"VerificaMapa\.lean:(\d+):\d+: error(?:\([^)]*\))?: (.*)", saida)
        marcados = set()
        for linha, msg in erros:
            n = int(linha)
            if n in mapa_linha:
                entrada, nome = mapa_linha[n]
                marcados.add(n)
                f.add(f"{entrada}: {nome} — {msg.splitlines()[0][:160]}")
            else:
                f.add(f"[{ambiente}] {msg.splitlines()[0][:200]} (linha {linha})")
        if proc.returncode != 0 and not erros:
            f.add(f"[{ambiente}] lake env lean falhou sem erro identificável: {saida[-300:]}")
        print(f"      {ambiente}: {len(itens)} nomes, {len(modulos)} módulos, "
              f"{len(erros)} erro(s) do Lean")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--dados", type=Path, default=gerar_mapa.DADOS)
    parser.add_argument("--tex", type=Path, default=gerar_mapa.TEX_PADRAO)
    parser.add_argument("--saida", type=Path, default=gerar_mapa.SAIDA_PADRAO)
    parser.add_argument("--sem-lean", action="store_true", help="pula a verificação de nomes com o Lean")
    args = parser.parse_args(argv)

    import json
    dados = json.loads(args.dados.read_text(encoding="utf-8"))
    total = len(dados["entradas"])
    print(f"Mapa: {total} entradas, {sum(len(e['lean']) for e in dados['entradas'])} referências Lean")

    falhas_total = 0
    f = Falhas(); verificar_estrutura(dados, f); f.relatorio("estrutura"); falhas_total += len(f.itens)

    f = Falhas(); verificar_rotulos(dados, args.tex, f); f.relatorio("rótulos TeX"); falhas_total += len(f.itens)

    f = Falhas(); verificar_atualidade(dados, args.tex, args.saida, f); f.relatorio("mapa gerado"); falhas_total += len(f.itens)

    f = Falhas(); pendentes = verificar_arquivos_e_linhas(dados, f); f.relatorio("arquivos e linhas"); falhas_total += len(f.itens)

    if args.sem_lean:
        print("skip  [nomes Lean] (--sem-lean)")
    else:
        f = Falhas(); print("[nomes Lean]"); verificar_lean(pendentes, f); f.relatorio("nomes Lean"); falhas_total += len(f.itens)

    if falhas_total:
        print(f"\nVerificação do mapa falhou: {falhas_total} problema(s).")
        return 1
    print("\nMapa verificado.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
