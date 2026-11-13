#!/usr/bin/env python3
"""Inventaria enunciados e liga um mapa revisado aos fontes, sem os modificar."""

from pathlib import Path
import csv
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "documentacao"
KINDS = {
    "theorem": "teorema", "teorema": "teorema", "lemma": "lema", "lema": "lema",
    "proposition": "proposicao", "proposicao": "proposicao",
    "corollary": "corolario", "corolario": "corolario",
    "definition": "definicao", "definicao": "definicao",
    "algorithm": "algoritmo", "algoritmo": "algoritmo",
    "remark": "observacao", "observacao": "observacao", "contract": "contrato",
}


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def uncomment(text):
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def expanded(path, tex_root, stack=()):
    if path in stack:
        raise ValueError(f"Ciclo de input: {path}")
    result = []
    for line_no, line in enumerate(path.read_text().splitlines(keepends=True), 1):
        active = uncomment(line)
        inputs = re.findall(r"\\input\{([^}]+)\}", active)
        result.append((str(path.relative_to(ROOT)), line_no, active))
        for name in inputs:
            if "#" in name:
                continue
            target = tex_root / name
            if target.suffix != ".tex":
                target = target.with_suffix(".tex")
            if target.is_file():
                result.extend(expanded(target, tex_root, (*stack, path)))
    return result


def tex_claims(doc_id, path):
    lines = expanded(path, path.parent)
    text = "".join(line[2] for line in lines)
    offsets, acc = [], 0
    for source, number, line in lines:
        offsets.append((acc, source, number))
        acc += len(line)
    import bisect
    positions = [p[0] for p in offsets]
    section = 0
    counter = 0
    section_title = ""
    claims = []
    events = re.compile(r"\\section(\*)?\{([^\n]+)\}|\\begin\{(" + "|".join(KINDS) + r")\}(?:\[([^\n]+?)\])?|\\setcounter\{section\}\{(\d+)\}")
    for event in events.finditer(text):
        if event.group(5) is not None:
            section = int(event.group(5))
            counter = 0
            continue
        if event.group(3) is None:
            if not event.group(1):
                section += 1
                counter = 0
                section_title = event.group(2)
            continue
        env = event.group(3)
        end = text.find("\\end{" + env + "}", event.end())
        if end < 0:
            raise ValueError(f"Ambiente sem fechamento em {doc_id}")
        counter += 1
        statement = text[event.end():end].strip()
        _, source, line = offsets[bisect.bisect_right(positions, event.start()) - 1]
        number = f"{section}.{counter}"
        claims.append({
            "id": f"{doc_id}:{number}", "documento": doc_id, "numero": number,
            "tipo": KINDS[env], "titulo": event.group(4) or "",
            "secao": section, "titulo_secao": section_title,
            "arquivo_tex": source, "linha_tex": line,
            "rotulos_tex": re.findall(r"\\label\{([^}]+)\}", statement),
            "enunciado_tex": statement, "sha256_enunciado": digest(statement),
        })
    return claims


def lean_without_comments(source):
    out = list(source)
    i, depth = 0, 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            out[i:i + 2] = "  "
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out[i:i + 2] = "  "
            i += 2
        elif depth:
            if source[i] != "\n":
                out[i] = " "
            i += 1
        elif source.startswith("--", i):
            j = source.find("\n", i)
            if j < 0:
                j = len(source)
            out[i:j] = " " * (j - i)
            i = j
        else:
            i += 1
    return "".join(out)


def lean_decls(folder, package):
    declarations = []
    for path in sorted(folder.rglob("*.lean")):
        original = path.read_text()
        source = lean_without_comments(original)
        scopes = []
        for number, line in enumerate(source.splitlines(), 1):
            scope = re.match(r"^\s*(?:noncomputable\s+)?(namespace|section)\s*(\S*)", line)
            if scope:
                scopes.append((scope[1], scope[2]))
                continue
            end = re.match(r"^\s*end(?:\s+(\S+))?\s*$", line)
            if end:
                if scopes:
                    scopes.pop()
                continue
            decl = re.match(r"^\s*(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(theorem|lemma|def|abbrev|structure|inductive|axiom|opaque)\s+([^\s:({\[]+)", line)
            if not decl:
                continue
            name = decl[2]
            namespace = ".".join(value for kind, value in scopes if kind == "namespace")
            if name.startswith("_root_."):
                full_name = name.removeprefix("_root_.")
            else:
                full_name = ".".join(filter(None, [namespace, name]))
            declarations.append({"pacote": package, "nome": full_name,
                                 "tipo": decl[1], "arquivo_lean": str(path.relative_to(ROOT)),
                                 "linha_lean": number})
    return declarations


def main():
    OUT.mkdir(exist_ok=True)
    docs = {
        "artigo_1": ROOT / "artigos/artigo_1/artigo.tex",
        "artigo_2": ROOT / "artigos/artigo_2/Artigo_2.tex",
        "artigo_3": ROOT / "artigos/artigo_3/Artigo_3.tex",
        "normalizacao": ROOT / "entradas/parte_1/Solucao_Equivalencia_Montagens_Parte_1 (1).tex",
        "complemento_original": ROOT / "artigos/complemento_original_77/complemento.tex",
    }
    closure = ROOT / "entradas/fechamento_parte_2/Fechamento_Parte_2_Formalizacao_Aristotle.tex"
    if closure.is_file():
        docs["fechamento_parte_2"] = closure
    claims = [claim for doc, path in docs.items() for claim in tex_claims(doc, path)]
    assert len({claim["id"] for claim in claims}) == len(claims)
    declarations = []
    for folder, name in [(ROOT / "Unified", "base_v2"),
                         (ROOT / "entradas/parte_1/RequestProject", "parte_1"),
                         (ROOT / "entradas/artigo_2/RequestProject", "artigo_2")]:
        declarations.extend(lean_decls(folder, name))
    by_ref = {(item["pacote"], item["nome"]): item for item in declarations}
    mapping_file = OUT / "correspondencias_revisadas.json"
    mappings = json.loads(mapping_file.read_text()) if mapping_file.exists() else {}
    unknown = set(mappings) - {claim["id"] for claim in claims}
    if unknown:
        raise ValueError(f"Identificadores de enunciados inexistentes: {sorted(unknown)}")
    errors = []
    for claim in claims:
        mapping = mappings.get(claim["id"], {})
        claim.update(mapping)
        claim.setdefault("status", "a_mapear")
        claim.setdefault("observacao", "")
        claim["resultados_lean"] = []
        for package, name in mapping.get("lean", []):
            item = by_ref.get((package, name))
            if item is None:
                errors.append((claim["id"], package, name))
            else:
                claim["resultados_lean"].append(item)
        claim.pop("lean", None)
    if errors:
        raise ValueError(f"Referencias Lean inexistentes: {errors}")
    payload = {"versao": 1, "criterio": "Cada ambiente numerado tem enunciado integral preservado; ligacoes sao inspecionadas e os estados distinguem compilacao de equivalencia semantica.",
               "documentos": {doc: {"arquivo": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for doc, path in docs.items()},
               "fechamento_recuperado": closure.is_file(), "enunciados": claims}
    (OUT / "enunciados.json").write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
    (OUT / "declaracoes_lean.json").write_text(json.dumps(declarations, ensure_ascii=False, indent=2) + "\n")
    origins = {
        "consolidado": ("artigo_1", "artigo_restante_formalizacao_integral_autocontido.tex"),
        "fase3": ("artigo_1", "artigo_fase3_taxas_refinamento_autocontido.tex"),
        "fase2": ("artigo_1", "artigo_fase2_densidade_autocontido.tex"),
        "artigo2": ("artigo_2", "Artigo_2.tex"),
    }
    by_number = {(c["documento"], c["numero"]): c for c in claims}
    provenance = {}
    for origin, (destination, filename) in origins.items():
        path = ROOT / "evidencias/recebimento_2026-10-22/fontes_de_origem" / origin / filename
        if not path.is_file():
            continue
        rows = []
        for item in tex_claims("origem_" + origin, path):
            target = by_number.get((destination, item["numero"]))
            transferred = False
            if target is None and destination == "artigo_1" and item["secao"] == 7:
                target = by_number.get(("artigo_2", "3." + item["numero"].split(".")[1]))
                transferred = target is not None
            rows.append({
                "id_origem": item["id"], "arquivo_origem": str(path.relative_to(ROOT)),
                "linha_origem": item["linha_tex"], "tipo_origem": item["tipo"],
                "titulo_origem": item["titulo"],
                "sha256_enunciado_origem": item["sha256_enunciado"],
                "destino": target["id"] if target else None,
                "transferido_editorialmente": transferred,
                "mesmo_tipo": target is not None and target["tipo"] == item["tipo"],
                "mesmo_titulo": target is not None and target["titulo"] == item["titulo"],
                "mesmo_enunciado_sem_espacos": target is not None and
                re.sub(r"\s+", "", target["enunciado_tex"]) ==
                re.sub(r"\s+", "", item["enunciado_tex"]),
            })
        provenance[origin] = rows
    (OUT / "procedencia_enunciados.json").write_text(
        json.dumps(provenance, ensure_ascii=False, indent=2) + "\n")
    fields = ["id", "documento", "numero", "tipo", "titulo", "arquivo_tex", "linha_tex", "rotulos_tex", "status", "resultados_lean", "observacao", "sha256_enunciado"]
    with (OUT / "correspondencia_artigos_lean.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for claim in claims:
            row = {field: claim[field] for field in fields}
            row["rotulos_tex"] = "; ".join(row["rotulos_tex"])
            row["resultados_lean"] = "; ".join(f'{d["pacote"]}:{d["nome"]} ({d["arquivo_lean"]}:{d["linha_lean"]})' for d in row["resultados_lean"])
            writer.writerow(row)
    for doc in docs:
        items = [c for c in claims if c["documento"] == doc]
        print(doc, len(items), "enunciados", sum(c["status"] == "a_mapear" for c in items), "a mapear")
        for claim in items:
            print(claim["id"], claim["tipo"], claim["titulo"], ";".join(claim["rotulos_tex"]))


if __name__ == "__main__":
    main()
