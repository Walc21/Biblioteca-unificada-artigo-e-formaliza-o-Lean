#!/usr/bin/env python3
"""Confere o retrato anterior e as alteracoes editoriais explicitamente registradas."""

from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def conferir():
    evidence = ROOT / "evidencias/recebimento_2026-10-22"
    previous = json.loads((evidence / "resultado_etapas_1_2.json").read_text())
    ledger_path = evidence / "recorte_editorial.json"
    ledger = json.loads(ledger_path.read_text()) if ledger_path.is_file() else {"alteracoes": []}
    allowed = {r["arquivo"]: r for r in ledger["alteracoes"]}
    result = []
    for item in previous["preservacao_matematica"]:
        name = item["arquivo"]
        now = digest(ROOT / name)
        state = "intacto"
        if now != item["sha256_antes"]:
            change = allowed.get(name)
            editorial = name.startswith("artigos/artigo_1/") and name.endswith(".tex")
            aggregator = name == "SemanticAudit.lean"
            if not change or not (editorial or aggregator):
                raise ValueError(f"Alteracao matematica nao registrada: {name}")
            if (change["sha256_antes"] != item["sha256_antes"]
                    or change["sha256_depois"] != now
                    or digest(Path(change["original_preservado"])) != item["sha256_antes"]):
                raise ValueError(f"Registro editorial divergente: {name}")
            if aggregator:
                def body(path):
                    return "\n".join(line for line in path.read_text().splitlines()
                                     if not line.startswith("public import "))
                if body(ROOT / name) != body(Path(change["original_preservado"])):
                    raise ValueError("O agregador alterou algo alem das importacoes.")
            state = "recorte_editorial_com_original_preservado"
        result.append({"arquivo": name, "sha256_atual": now, "estado": state})
    return result


if __name__ == "__main__":
    rows = conferir()
    changed = sum(row["estado"] != "intacto" for row in rows)
    print(f"PASS: {len(rows)} arquivos anteriores conferidos; {changed} alteracoes editoriais registradas; originais preservados.")
