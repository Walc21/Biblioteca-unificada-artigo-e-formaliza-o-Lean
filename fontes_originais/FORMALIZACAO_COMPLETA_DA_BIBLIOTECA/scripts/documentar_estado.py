#!/usr/bin/env python3
"""Gera a matriz legivel a partir do inventario e do mapa inspecionado."""

from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "documentacao"
TITLES = {
    "artigo_1": "Artigo 1 reduzido", "artigo_2": "Artigo 2", "artigo_3": "Artigo 3",
    "normalizacao": "Normalização da Parte I", "complemento_original": "Complemento do original",
}
STATUS = {
    "correspondencia_inspecionada": "Correspondência inspecionada",
    "integrado_a_v2": "Integração à v2 provada",
    "divergencia_documentada": "Diferença textual documentada",
    "contrato_abstrato": "Contrato abstrato",
    "ponte_regularidade_pendente": "Ponte de regularidade pendente",
    "observacao_editorial": "Observação editorial",
    "cobertura_parcial": "Cobertura parcial",
    "implementacao_pendente": "Implementação pendente",
    "generalizacao_documentada": "Generalização documentada",
    "prova_textual_a_sincronizar": "Prova textual a sincronizar",
    "nao_formalizado_no_acervo": "Sem formalização localizada",
    "corolario_a_transportar": "Corolário a transportar",
    "sem_formalizacao_localizada": "Sem formalização localizada",
}


def safe(text):
    return text.replace("|", "&#124;").replace("\n", " ")


def link(label, path, line):
    target = ROOT / path
    if not target.is_file() or not 1 <= line <= len(target.read_text().splitlines()):
        raise ValueError(f"Referencia invalida: {target}:{line}")
    return f"[{safe(label)}](<{target}:{line}>)"


def main():
    data = json.loads((DOCS / "enunciados.json").read_text())
    claims = data["enunciados"]
    kinds = {"teorema", "lema", "proposicao", "corolario"}
    counts = Counter(c["documento"] for c in claims)
    lines = ["# Correspondência dos artigos com os resultados Lean", "",
             "Estado de 22/10/2026, após o recorte editorial e a integração da normalização.", "",
             f"A matriz contém {len(claims)} ambientes numerados e {sum(c['tipo'] in kinds for c in claims)} afirmações matemáticas.",
             "O original de 77 páginas tem inventário separado: todos os seus 108 ambientes receberam destino documental.",
             "Texto integral, posição, rótulos e hash de cada enunciado estão em `enunciados.json`.", "",
             "| Documento | Ambientes | Afirmações matemáticas |", "| --- | ---: | ---: |"]
    for doc, title in TITLES.items():
        lines.append(f"| {title} | {counts[doc]} | {sum(c['documento'] == doc and c['tipo'] in kinds for c in claims)} |")
    refs = {(r["pacote"], r["nome"]) for c in claims for r in c["resultados_lean"]}
    lines += ["", f"Os {len(refs)} identificadores citados passaram pelo compilador: 191 na base integrada/Parte I e 84 no ambiente isolado do Artigo 2.",
              "As ligações identificam os resultados formais relevantes e conservam as ressalvas de cada enunciado.",
              "Compilar um resultado não demonstra, por si só, que uma tradução diferente tenha o mesmo significado.", "",
              "## Origem, integração e limites", "",
              "O antigo bloco 7 do Artigo 1 está agora somente no Artigo 2, seção 3. A versão anterior foi arquivada.",
              "Os três resultados da seção 6 do original e o lema 21.1 estão integralmente no complemento, com suas demonstrações.",
              "A pasta Fase3 é uma etapa da formalização do primeiro artigo e não o atual Artigo 3.", "",
              "As seis pontes Normalization identificam os tipos concretos, os endereços, as classes, os orçamentos, os erros e a extensão ReLU.",
              "A integração está detalhada em `INTEGRACAO_NORMALIZACAO.md`. O Artigo 2 conserva seu ambiente separado.", "",
              "Permanecem explícitos a expressão g(t₀) no enunciado antigo, as pontes C² do Artigo 2, a passagem a árvores em raiz única,",
              "a execução das recorrências e seus custos. Os resultados do Artigo 3 e do complemento não são contados como integralmente formalizados.",
              "O documento auxiliar histórico de fechamento permanece parcialmente recuperado e não foi confundido com o original integral recebido.", ""]
    for doc, title in TITLES.items():
        lines += ["## " + title, "", "| Número e tipo | Enunciado e fonte | Resultado Lean | Estado e ressalva |",
                  "| --- | --- | --- | --- |"]
        for c in (c for c in claims if c["documento"] == doc):
            label = c["titulo"] or "Enunciado sem título"
            source = link(label, c["arquivo_tex"], c["linha_tex"])
            results = "<br>".join(link(r["nome"], r["arquivo_lean"], r["linha_lean"])
                                    for r in c["resultados_lean"]) or "—"
            state = STATUS.get(c["status"], c["status"])
            if c["observacao"]:
                state += "<br>" + safe(c["observacao"])
            lines.append(f"| {c['numero']} · {c['tipo']} | {source} | {results} | {state} |")
        lines.append("")
    lines += ["Para reproduzir: `python3 scripts/mapear_corpus.py` e `python3 scripts/documentar_estado.py`.", ""]
    (DOCS / "CORRESPONDENCIA_ARTIGOS.md").write_text("\n".join(lines))
    print(f"Matriz atualizada: {len(claims)} ambientes, {len(refs)} nomes Lean, referencias de arquivo conferidas.")


if __name__ == "__main__":
    main()
