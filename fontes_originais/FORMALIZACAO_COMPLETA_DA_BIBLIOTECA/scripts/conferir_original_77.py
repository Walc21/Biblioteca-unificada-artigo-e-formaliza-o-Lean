#!/usr/bin/env python3
"""Confere o original de 77 paginas contra recortes inspecionados, sem editar fontes."""

from collections import Counter
from pathlib import Path
import hashlib
import json
import re

from mapear_corpus import tex_claims
from verificar_preservacao import conferir

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "documentacao"
ORIGINAL = ROOT / "entradas/original_77_paginas"
MATHEMATICAL = {"teorema", "lema", "proposicao", "corolario"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def without_labels_and_spaces(text):
    return re.sub(r"\s+", "", re.sub(r"\\label\{[^}]+\}", "", text))


def source_link(claim):
    return f"<{ROOT / claim['arquivo_tex']}:{claim['linha_tex']}>"


def main():
    receipt = read_json(ROOT / "evidencias/recebimento_2026-10-22/original_77_paginas.json")
    for item in receipt["arquivos_preservados"]:
        if digest(ORIGINAL / item["arquivo"]) != item["sha256"]:
            raise ValueError(f"Original recebido alterado: {item['arquivo']}")
    if not all(item["ok"] for item in receipt["manifesto_recebido"]):
        raise ValueError("O manifesto recebido tem divergencias.")

    originals = tex_claims("original_77", ORIGINAL / "artigo/artigo_nacional.tex")
    current = read_json(OUT / "enunciados.json")["enunciados"]
    by_id = {claim["id"]: claim for claim in current}
    docs = {
        "artigo_1": ROOT / "artigos/artigo_1/artigo.tex",
        "artigo_2": ROOT / "artigos/artigo_2/Artigo_2.tex",
        "artigo_3": ROOT / "artigos/artigo_3/Artigo_3.tex",
        "complemento_original": ROOT / "artigos/complemento_original_77/complemento.tex",
    }
    for doc, path in docs.items():
        for claim in tex_claims(doc, path):
            if claim["sha256_enunciado"] != by_id[claim["id"]]["sha256_enunciado"]:
                raise ValueError("Inventario desatualizado; executar mapear_corpus.py primeiro.")

    reviews = read_json(OUT / "recortes_original_77_revisados.json")["recortes"]
    reviewed = {row["original"]: row for row in reviews}
    if len(reviewed) != len(reviews) or set(reviewed) != {o["id"] for o in originals}:
        raise ValueError("O mapa revisado nao cobre exatamente o original.")
    rows = []
    for original in originals:
        review = reviewed[original["id"]]
        if original["sha256_enunciado"] != review["sha256_original"]:
            raise ValueError(f"Revisar novamente o original: {original['id']}")
        targets = []
        for reference in review["destinos"]:
            target = by_id[reference["id"]]
            if target["sha256_enunciado"] != reference["sha256_enunciado"]:
                raise ValueError(f"Revisar novamente o destino: {target['id']}")
            if target["tipo"] != original["tipo"]:
                raise ValueError(f"Tipo de ambiente divergente: {target['id']}")
            targets.append({
                "id": target["id"], "papel": reference["papel"],
                "arquivo_tex": target["arquivo_tex"], "linha_tex": target["linha_tex"],
                "sha256_enunciado": target["sha256_enunciado"],
                "igual_sem_rotulos_e_espacos": without_labels_and_spaces(original["enunciado_tex"])
                == without_labels_and_spaces(target["enunciado_tex"]),
                "estado_formal_no_mapa_derivado": target["status"],
                "ressalva_formal": target["observacao"],
                "resultados_lean": target["resultados_lean"],
            })
        for related in review.get("locais_relacionados", []):
            if related not in by_id:
                raise ValueError(f"Referencia relacionada inexistente: {related}")
        rows.append({"original": original, "destinos": targets,
                     "status": review["status"], "observacao": review["observacao"],
                     "locais_relacionados": review.get("locais_relacionados", [])})

    mapped = [r for r in rows if r["destinos"]]
    residuals = [r for r in rows if not r["destinos"]]
    summary = {
        "ambientes_originais": len(rows),
        "afirmacoes_matematicas_originais": sum(r["original"]["tipo"] in MATHEMATICAL for r in rows),
        "ambientes_com_destino_direto": len(mapped),
        "afirmacoes_matematicas_com_destino_direto": sum(r["original"]["tipo"] in MATHEMATICAL for r in mapped),
        "ambientes_sem_reproducao_integral": len(residuals),
        "duplicacoes_do_bloco_original_8": sum(len(r["destinos"]) == 2 for r in rows),
        "destinos_principais": dict(Counter(r["destinos"][0]["id"].split(":")[0] for r in mapped)),
        "textos_principais_iguais_sem_rotulos_e_espacos": sum(r["destinos"][0]["igual_sem_rotulos_e_espacos"] for r in mapped),
    }
    preservation = conferir()
    unchanged = sum(r["estado"] == "intacto" for r in preservation)
    payload = {"versao": 1, "resumo": summary,
               "criterio": "Correspondencia editorial revisada; nao substitui equivalencia semantica nem prova Lean.",
               "original_integral_preservado": True,
               "manifesto_recebido_conferido": len(receipt["manifesto_recebido"]),
               "arquivos_matematicos_anteriores_conferidos": len(preservation),
               "arquivos_matematicos_anteriores_intactos": unchanged,
               "alteracoes_registradas_com_original_preservado": len(preservation) - unchanged,
               "enunciados": rows}
    (OUT / "enunciados_original_77.json").write_text(json.dumps(originals, ensure_ascii=False, indent=2) + "\n")
    (OUT / "conferencia_original_77.json").write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
    evidence = {"resumo": summary, "arquivos_originais_preservados": len(receipt["arquivos_preservados"]),
                "preservacao_matematica_anterior": preservation,
                "fontes_lean_de_origem_editados": False,
                "recorte_editorial_registrado": True}
    (ROOT / "evidencias/recebimento_2026-10-22/conferencia_original_77.json").write_text(
        json.dumps(evidence, ensure_ascii=False, indent=2) + "\n")

    lines = [
        "# Conferência do original de 77 páginas", "",
        "O original integral foi recebido em 22/10/2026. Seus 135 arquivos foram preservados em",
        "`entradas/original_77_paginas/`; as 133 entradas do manifesto recebido conferem.",
        f"Os {len(preservation)} arquivos do retrato anterior foram conferidos: {unchanged} permanecem byte a byte iguais;",
        f"{len(preservation) - unchanged} alterações autorizadas constam do registro, com os originais preservados fora da raiz ativa.", "",
        f"O original contém **{len(rows)} ambientes numerados**, dos quais **{summary['afirmacoes_matematicas_originais']}** são teoremas, lemas, proposições ou corolários.",
        f"Há **{len(mapped)} correspondências editoriais diretas** e **{len(residuals)} enunciados sem destino integral** nos derivados e no complemento.",
        "Essas contagens não são contagens de teoremas formalizados em Lean.", "",
        "## Redistribuição observada nos fontes", "",
        "| Original | Destino atual | Situação |",
        "| --- | --- | --- |",
        "| Seções 2–5 | Artigo 1, seções 2–5 | Construção, densidade, ReLU e taxas |",
        "| Seção 6 | Complemento, seção 6 | Três enunciados e provas preservados integralmente |",
        "| Seção 7 | Artigo 1, seção 6 | Refinamento certificado |",
        "| Seção 8 | Artigo 2, seção 3 | 25 ambientes transferidos; versão anterior do Artigo 1 arquivada |",
        "| Seções 9–14 | Artigo 2, seções 4–9 | Seleção, recorrências e custos |",
        "| Seção 15 | Artigo 2, seção 10 | Validação computacional; sem ambiente numerado |",
        "| Seções 16–17 | Artigo 2, seções 11–12 | Constantes e fases diádicas |",
        "| Seções 18–20 | Artigo 3, seções 3–5 | Agendas de altura e teoria direta–inversa |",
        "| Seção 21 | Exemplos e reprodução redistribuídos; complemento, seção 21 | Lema de Runge e prova preservados no complemento |", "",
        "A arquitetura A/B/C/R recebida é uma recomendação editorial histórica. Ela não usa a mesma",
        "numeração dos Artigos 1/2/3 atuais. A terceira parte analítica do original aparece nos dois",
        "últimos derivados: seções 16–17 no Artigo 2 e 18–20 no Artigo 3. Portanto, o Artigo 3 atual",
        "não pode ser identificado como uma etapa antiga de formalização nem como simples continuação da programação dinâmica.", "",
        "O fonte ativo do Artigo 1 foi reduzido a 24 ambientes, sem alterar os enunciados retidos.",
        "Resumo, introdução, conclusão e notação acompanham o recorte. O calibre usado na proposição 4.4",
        "foi mantido nas preliminares. Os 25 ambientes transferidos permanecem no Artigo 2; o estado anterior está arquivado.", "",
        "## Preservação e diferenças", "",
        "A correspondência foi inspecionada sobre hipóteses e conclusões, com hashes congelados no mapa revisado.",
        f"Em {summary['textos_principais_iguais_sem_rotulos_e_espacos']} destinos principais o texto coincide após remover somente rótulos e espaços.",
        "Nos demais há macros, numeração de referências, diagramação ou redação diferentes; o JSON mantém os hashes e a classificação por enunciado.",
        "A Observação original 8.8 tem um esclarecimento operacional relevante já presente no Artigo 2:",
        "a inversa fechada é atribuída à etapa de Cantor, e os decodificadores de Q e Q* são explicitados.",
        "A alegação anterior de decodificação total sem enumeração auxiliar não deve ser reutilizada.", "",
        "Os quatro resultados antes classificados como resíduos foram reproduzidos no complemento,",
        "com a mesma numeração, os mesmos enunciados e as mesmas demonstrações matemáticas.",
        "Somente remissões externas das demonstrações foram adaptadas. Sua reprodução documental",
        "não significa que tenham sido formalizados em Lean.", "",
        "## Resultados preservados no complemento", "",
    ]
    for row in rows:
        if not any(t["id"].startswith("complemento_original:") for t in row["destinos"]):
            continue
        c = row["original"]
        lines += [f"- [{c['numero']} — {c['titulo']}]({source_link(c)}): {row['observacao']}"]
    lines += ["", "## Estado formal e prosseguimento", "",
              "As ligações Lean abaixo são herdadas do mapa dos derivados, incluindo suas ressalvas.",
              "A validação isolada dos pacotes certifica compilação local e axiomas. O transporte da normalização",
              "à base v2 foi provado em seis módulos; consultar INTEGRACAO_NORMALIZACAO.md. O Artigo 3 conserva as 19 afirmações",
              "matemáticas cuja formalização integral não foi localizada.", "",
              "1. Concluído: recorte do Artigo 1, complemento dos quatro resultados e revisão dos PDFs recompostos.",
              "2. Concluído: integração da normalização aos tipos concretos da v2, conservando hipóteses, N, H e erro.",
              "3. Próxima frente: pontes C² do Artigo 2, árvore em raiz única, execução das recorrências e custos; sincronização de fórmulas e provas textuais.",
              "4. Frente separada: formalização do Artigo 3 e dos resultados do complemento, explicitamente não contada como concluída.",
              "5. Concluído: validação completa e auditoria da base integrada, validação integral dos dois pacotes separados e organização após conferir os hashes e o escopo.", "",
              "O documento posterior chamado Fechamento_Parte_2_Formalizacao_Aristotle continua parcialmente",
              "recuperado, mas sua ausência não bloqueia esta conferência com o original integral.", "",
              "O registro de preservação distingue o recorte autorizado da alteração de uma prova.",
              "Nenhum fonte Lean recebido ou declaração Lean anterior foi reescrito.", "",
              "## Matriz completa", "",
              "| Original | Tipo e título | Destino(s) | Situação formal do destino principal |",
              "| --- | --- | --- | --- |"]
    for row in rows:
        c = row["original"]
        title = (c["titulo"] or "sem título").replace("|", "&#124;")
        destinations = "; ".join(f"[{t['id']}]({source_link(t)})" for t in row["destinos"])
        if row["destinos"]:
            state = row["destinos"][0]["estado_formal_no_mapa_derivado"]
        else:
            state = row["status"]
        lines.append(f"| [{c['numero']}]({source_link(c)}) | {c['tipo']} · {title} | {destinations or 'Resíduo preservado'} | {state} |")
    lines += ["", "Para reproduzir: `python3 scripts/mapear_corpus.py` e `python3 scripts/conferir_original_77.py`.", ""]
    (OUT / "CONFERENCIA_ORIGINAL_77.md").write_text("\n".join(lines))
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == "__main__":
    main()
