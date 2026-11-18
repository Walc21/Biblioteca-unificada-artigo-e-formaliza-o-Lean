#!/usr/bin/env python3
"""Executa os verificadores e geradores em diretórios de saída independentes."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys


PROGRAMAS = (
    ("reproduzir_curvas", "resultados.json"),
    ("figuras_parte_1", "dados/refinamento.json"),
    ("seletor_dinamico_exato", "reproducibility/selecao/resultados.json"),
    ("constante_diadica", "reproducibility/selecao/resultados_constante_diadica.json"),
    ("espacos_aproximacao", "reproducibility/selecao/resultados_espacos_aproximacao.json"),
    ("reversibilidade_regularizada", "reproducibility/selecao/resultados_reversibilidade.json"),
    ("restricoes_rede", "reproducibility/selecao/resultados_restricoes_rede.json"),
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", required=True, type=Path)
    args = parser.parse_args()
    root = args.output_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    scripts = Path(__file__).resolve().parent
    env = dict(os.environ, MPLBACKEND="Agg")
    # PYTHONOPTIMIZE/-O desativa os asserts que implementam as verificações.
    env.pop("PYTHONOPTIMIZE", None)
    registros = []
    resumo = root / "resumo_execucao.json"
    resumo.write_text(json.dumps({"status": "em_execucao", "programas": []}), encoding="utf-8")
    for nome, resultado_relativo in PROGRAMAS:
        destino = root / nome
        log = root / f"{nome}.log"
        with log.open("w", encoding="utf-8") as stream:
            processo = subprocess.run(
                [sys.executable, str(scripts / f"{nome}.py"), "--output-root", str(destino)],
                stdout=stream, stderr=subprocess.STDOUT, env=env, check=False,
            )
        resultado = destino / resultado_relativo
        valido = processo.returncode == 0 and resultado.is_file()
        if valido:
            try:
                json.loads(resultado.read_text(encoding="utf-8"))
            except (OSError, ValueError):
                valido = False
        registros.append({
            "programa": nome, "codigo_saida": processo.returncode,
            "resultado_json_valido": valido, "log": str(log),
            "resultado": str(resultado),
        })
        resumo.write_text(json.dumps({
            "status": "em_execucao" if valido else "falha",
            "programas": registros,
        }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"{nome}: {'ok' if valido else 'falha'}", flush=True)
        if not valido:
            raise SystemExit(f"Verificação interrompida; consulte {log}")
    resumo.write_text(json.dumps({
        "status": "ok", "programas": registros,
    }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Resumo: {resumo}")


if __name__ == "__main__":
    main()
