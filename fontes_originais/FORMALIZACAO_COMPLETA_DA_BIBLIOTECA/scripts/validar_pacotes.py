#!/usr/bin/env python3
"""Valida os pacotes recebidos isoladamente ou resume uma execução registrada."""

from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
from datetime import datetime
from zoneinfo import ZoneInfo

ROOT = Path(__file__).resolve().parents[1]


def run(folder, args, logfile):
    with (folder / logfile).open("w") as output:
        result = subprocess.run(args, cwd=folder, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f"Falha em {folder.name}: {args}; consultar {logfile}")
    return result.returncode


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--resumir", action="store_true", help="Confere fontes e resume logs já concluídos, sem recompilar.")
    args = parser.parse_args()
    reports = {}
    for name, expected_count in [("parte_1", 9), ("artigo_2", 31)]:
        folder = ROOT / "validacao" / name
        received = ROOT / "entradas" / name
        origin = json.loads((folder / "fontes-recebidas.json").read_text())
        sources = sorted((received / "RequestProject").glob("*.lean"))
        if len(sources) != expected_count or len(origin["sources"]) != expected_count:
            raise RuntimeError(f"Contagem inesperada de fontes: {name}")
        for item in origin["sources"]:
            for path in [received / item["path"], folder / item["path"]]:
                if hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
                    raise RuntimeError(f"Fonte alterado: {path}")
        expected_imports = {"import RequestProject." + path.stem for path in sources}
        if set((folder / "ValidationAll.lean").read_text().splitlines()) != expected_imports:
            raise RuntimeError(f"O agregador não alcança todos os módulos: {name}")
        if not args.resumir:
            codes = {
                "build": run(folder, ["lake", "build", "ValidationAll"], "compilacao.log"),
                "axioms": run(folder, ["lake", "env", "lean", "AuditoriaPacote.lean"], "axiomas.log"),
                "mapped_names": run(folder, ["lake", "env", "lean", "CorrespondenciasAudit.lean"], "correspondencias.log"),
            }
            (folder / "execucao.json").write_text(json.dumps({"exit_codes": codes}, indent=2) + "\n")
        codes = json.loads((folder / "execucao.json").read_text())["exit_codes"]
        if any(code != 0 for code in codes.values()):
            raise RuntimeError(f"Execução incompleta ou com falha: {name}")
        build = (folder / "compilacao.log").read_text()
        build_match = re.search(r"Build completed successfully \((\d+) jobs\)", build)
        if not build_match:
            raise RuntimeError(f"Conclusão de compilação ausente: {name}")
        audit_lines = [line.removeprefix("AUDIT_JSON ") for line in (folder / "axiomas.log").read_text().splitlines() if line.startswith("AUDIT_JSON ")]
        if len(audit_lines) != 1:
            raise RuntimeError(f"Resumo de axiomas ausente ou ambíguo: {name}")
        audit = json.loads(audit_lines[0])
        if audit["unexpected_axioms"] or not audit["declarations"]:
            raise RuntimeError(f"Auditoria rejeitada: {name}")
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        if not set(audit["axioms_union"]) <= allowed:
            raise RuntimeError(f"Axiomas fora da lista: {name}")
        for path in sources:
            if not (folder / ".lake/build/lib/lean/RequestProject" / (path.stem + ".olean")).is_file():
                raise RuntimeError(f"Artefato de módulo ausente: {name}/{path.name}")
        reports[name] = {
            "status": "validado_localmente", "lean_modules": expected_count,
            "build_jobs": int(build_match[1]), "sources_unchanged": True,
            "all_modules_imported": True, "exit_codes": codes, "axiom_audit": audit,
            "environment": origin["validation_kind"],
            "semantic_integration_with_v2": "not_checked_by_this_isolated_validation",
        }
    report = {"completed_at": datetime.now(ZoneInfo("America/Sao_Paulo")).isoformat(),
              "packages": reports, "scope": "Compilação integral isolada e dependências axiomáticas; não substitui as pontes semânticas ao artigo e à base v2."}
    (ROOT / "validacao/resultados.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    for name, result in reports.items():
        audit = result["axiom_audit"]
        print(f'{name}: {result["lean_modules"]} módulos; {audit["theorems"]} teoremas; zero axiomas fora da lista.')


if __name__ == "__main__":
    main()
