#!/usr/bin/env python3
"""Auditoria estática dos fontes LaTeX do documento-sistema corrigido."""

from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ARTICLE = ROOT / "artigo"
SECTIONS = ARTICLE / "secoes"

MASTERS = [ARTICLE / "artigo_nacional.tex"]
FORBIDDEN = (
    "artigo precedente",
    "plano preliminar",
    "plano antigo",
    "etapa 8",
    "etapa 9",
    "etapa 10",
    "etapa 11",
    "parte~8",
    "parte~9",
    "parte~10",
    "parte~11",
    "versão restritiva",
    "versão alternativa",
    "corrige o erro",
    "retroativamente",
    "não se afirma",
    "não afirma que",
    "não substituem as provas",
)


def active_inputs(master: Path) -> list[str]:
    text = master.read_text(encoding="utf-8")
    return re.findall(r"\\input\{(secoes/[^}]+)\}", text)


def expand_sources(master: Path) -> list[Path]:
    return [master, ARTICLE / "comandos.tex", ARTICLE / "abstract_en.tex"] + [
        ARTICLE / f"{name}.tex" if not name.endswith(".tex") else ARTICLE / name
        for name in active_inputs(master)
    ]


def main() -> int:
    errors: list[str] = []
    sources = expand_sources(MASTERS[0])
    sources.extend([ARTICLE / "resumo_pt.tex", ARTICLE / "declaracoes.tex"])
    missing = [str(path.relative_to(ROOT)) for path in sources if not path.exists()]
    if missing:
        errors.append(f"Fontes ausentes: {missing}")

    corpus = "\n".join(path.read_text(encoding="utf-8") for path in sources if path.exists())
    labels = re.findall(r"\\label\{([^}]+)\}", corpus)
    duplicates = sorted(key for key, count in Counter(labels).items() if count > 1)
    if duplicates:
        errors.append(f"Rótulos duplicados: {duplicates}")

    refs: set[str] = set()
    for command, payload in re.findall(
        r"\\(cref|Cref|ref|eqref|autoref)\{([^}]+)\}", corpus
    ):
        del command
        refs.update(key.strip() for key in payload.split(","))
    undefined_refs = sorted(refs - set(labels))
    if undefined_refs:
        errors.append(f"Referências internas sem rótulo: {undefined_refs}")

    bib_text = (ROOT / "references.bib").read_text(encoding="utf-8")
    bib_keys = set(re.findall(r"^@\w+\{([^,]+),", bib_text, flags=re.MULTILINE))
    cites: set[str] = set()
    for payload in re.findall(
        r"\\cite(?:t|p)?(?:\[[^\]]*\]){0,2}\{([^}]+)\}", corpus
    ):
        cites.update(key.strip() for key in payload.split(","))
    undefined_cites = sorted(cites - bib_keys)
    if undefined_cites:
        errors.append(f"Citações sem entrada bibliográfica: {undefined_cites}")
    unused_bib = sorted(bib_keys - cites)
    if unused_bib:
        errors.append(f"Entradas bibliográficas não citadas: {unused_bib}")

    for master in MASTERS:
        master_text = master.read_text(encoding="utf-8")
        if not re.search(r"\\bibliography\{[^}]*references[^}]*\}", master_text):
            errors.append(
                f"Bibliografia ausente do mestre {master.relative_to(ROOT)}."
            )

    lower = corpus.lower()
    found_forbidden = sorted(term for term in FORBIDDEN if term in lower)
    if found_forbidden:
        errors.append(f"Marcas editoriais proibidas: {found_forbidden}")

    theorem_starts = len(
        re.findall(
            r"\\begin\{(?:theorem|lemma|proposition|corollary|definition|algorithm)\}",
            corpus,
        )
    )
    theorem_ends = len(
        re.findall(
            r"\\end\{(?:theorem|lemma|proposition|corollary|definition|algorithm)\}",
            corpus,
        )
    )
    if theorem_starts != theorem_ends:
        errors.append(
            f"Ambientes matemáticos desequilibrados: {theorem_starts} inícios e {theorem_ends} finais."
        )

    # Regressões específicas dos cinco achados do laudo Wolfram de 07/08/2026.
    selector_source = (SECTIONS / "15_validacao_selecao.tex").read_text(
        encoding="utf-8"
    )
    correct_selector_path = r"\path{reproducibility/selecao/seletor_dinamico_exato.py}"
    if correct_selector_path not in selector_source:
        errors.append("R-01: caminho completo do seletor ausente da Seção 15.")
    if not (ROOT / "reproducibility/selecao/seletor_dinamico_exato.py").exists():
        errors.append("R-01: programa do seletor não existe no caminho publicado.")

    verification_source = (SECTIONS / "21_verificacao_computacional.tex").read_text(
        encoding="utf-8"
    )
    if "executados por um único programa" in verification_source:
        errors.append("R-02: a Seção 21 ainda atribui os testes a um único programa.")
    if "coordena seis" not in verification_source:
        errors.append("R-02: a Seção 21 não registra os seis programas coordenados.")

    direct_source = (SECTIONS / "19_teoremas_diretos.tex").read_text(
        encoding="utf-8"
    )
    if "k_0+r,," in direct_source:
        errors.append("E-01: vírgula duplicada no índice da célula diádica.")

    reverse_source = (SECTIONS / "20_reversibilidade.tex").read_text(
        encoding="utf-8"
    )
    complete_match = re.search(
        r"\\begin\{theorem\}\[caracterização pelo funcional de realização\]"
        r".*?\\end\{proof\}",
        reverse_source,
        flags=re.DOTALL,
    )
    if complete_match is None or r"\cref{lem:universal-regularized-inverse}" not in complete_match.group(0):
        errors.append("L-01: a direção inversa não cita diretamente o lema universal.")

    architecture_match = re.search(
        r"\\begin\{theorem\}\[reversibilidade estável por inclusão de redes\]"
        r".*?\\end\{proof\}",
        reverse_source,
        flags=re.DOTALL,
    )
    if architecture_match is None:
        errors.append("M-01: teorema de estabilidade arquitetural não localizado.")
    else:
        architecture_block = architecture_match.group(0)
        if r"\mathcal N_N\subseteq\mathcal N_{N+1}" not in architecture_block:
            errors.append("M-01: aninhamento neural não consta do enunciado.")
        if r"d=2^{\lceil\log_2c\rceil}" not in architecture_block:
            errors.append("M-01: prova não preserva explicitamente os índices diádicos.")

    summary_pt = (ARTICLE / "resumo_pt.tex").read_text(encoding="utf-8")
    abstract_en = (ARTICLE / "abstract_en.tex").read_text(encoding="utf-8")
    conclusion_pt = (SECTIONS / "22_conclusao.tex").read_text(encoding="utf-8")
    if "direção inversa é universal" not in summary_pt:
        errors.append("M-01: resumo não qualifica a universalidade da direção inversa.")
    if "inverse direction is universal" not in abstract_en:
        errors.append("M-01: abstract não qualifica a universalidade da direção inversa.")
    if not re.search(r"aninhada\s+no\s+orçamento", conclusion_pt):
        errors.append("M-01: conclusão não qualifica o aninhamento no orçamento.")

    # Regressões incorporadas após o parecer técnico e o plano revisado.
    if "hristovivanov1990" not in reverse_source or "funcional de realização" not in reverse_source:
        errors.append("M-1: citação clássica ou reformulação do funcional de realização ausente.")
    if "rem:realization-functional-scope" not in reverse_source:
        errors.append("M-1: escopo universal do funcional de realização não explicitado.")
    if "cor:uniform-besov-ball-embedding" not in direct_source:
        errors.append("M-2: imersão quantitativa uniforme sobre bolas ausente.")

    comb_match = re.search(
        r"\\begin\{theorem\}\[agudeza por um pente de tendas\]"
        r".*?\\end\{proof\}", reverse_source, flags=re.DOTALL
    )
    if comb_match is None:
        errors.append("M-3: teorema do pente crítico não localizado.")
    else:
        comb_block = comb_match.group(0)
        if r"e_N^{\Library,H}" not in comb_block or r"\Aclass^\square" in comb_block:
            errors.append("M-3: testemunha ainda não foi transferida para a biblioteca original.")
        if "inclinação não nula em toda folha" not in comb_block:
            errors.append("M-3: perturbação de inclinação não nula não está explicitada.")
    reverse_script = (ROOT / "reproducibility/selecao/reversibilidade_regularizada.py").read_text(
        encoding="utf-8"
    )
    if '"original_library": True' not in reverse_script or "perturbation_error == delta" not in reverse_script:
        errors.append("M-3: auditoria executável da transferência para a biblioteca original ausente.")

    complexity_source = (SECTIONS / "14_complexidade_estabilidade.tex").read_text(
        encoding="utf-8"
    )
    if "thm:bit-complexity" not in complexity_source or "B_{\\rm cost}" not in complexity_source:
        errors.append("M-5: cota de complexidade de bits não localizada.")

    address_source = (SECTIONS / "08_complexidade.tex").read_text(encoding="utf-8")
    if "o menor numerador $b_j$" not in address_source:
        errors.append("M-6: regra exata de desempate não consta do orçamento conjunto.")
    if "3/2$ na mesma normalização" not in verification_source:
        errors.append("E-7: normalização do certificado quadrático não foi corrigida.")
    if "do primeiro artigo" in direct_source or "tab:part9-audit" in corpus:
        errors.append("E-2: vestígio de origem multiartigo ainda presente.")

    required_float_labels = (
        "fig:boundary-state", "fig:c2-envelope", "fig:height-schedules",
        "fig:piecewise-phases", "fig:quadratic-sawtooth",
        "fig:regularized-reversibility", "fig:selector-comparison",
        "tab:approximate-reverse-audit", "tab:dp-audit",
        "tab:kink-regularized-certificate", "tab:dyadic-constants-audit",
        "tab:quadratic-exact",
    )
    orphaned = [key for key in required_float_labels if corpus.count(key) < 2]
    if orphaned:
        errors.append(f"E-1: floats sem chamada explícita: {orphaned}")

    def prose_word_count(text: str) -> int:
        stripped = re.sub(r"\\[A-Za-z@]+(?:\[[^\]]*\])?", " ", text)
        stripped = re.sub(r"[{}$^_]", " ", stripped)
        return len(re.findall(r"[A-Za-zÀ-ÖØ-öø-ÿ0-9]+(?:[-'][A-Za-zÀ-ÖØ-öø-ÿ0-9]+)*", stripped))

    for label, text in (("resumo", summary_pt), ("abstract", abstract_en)):
        count = prose_word_count(text)
        if count > 250:
            errors.append(f"E-5: {label} excede 250 palavras ({count}).")
        if r"\[" in text or r"\begin{equation}" in text or r"\begin{align}" in text:
            errors.append(f"E-5: {label} contém matemática em display.")

    declarations = (ARTICLE / "declaracoes.tex").read_text(encoding="utf-8")
    for heading in ("Agradecimentos", "Financiamento", "Conflitos de interesse",
                    "Disponibilidade de dados e código", "ORCID", "Nota biográfica"):
        if heading not in declarations:
            errors.append(f"E-6: declaração ausente: {heading}.")
    if (ARTICLE / "artigo_ieee.tex").exists():
        errors.append("B-1: composição IEEE em português ainda está presente.")

    # L-01: cleveref rotula section/figure/table/equation em inglês por padrão.
    # O mestre precisa declarar os nomes portugueses e o conector de intervalo.
    master_text = MASTERS[0].read_text(encoding="utf-8")
    for tipo, singular in (
        ("section", "seção"),
        ("subsection", "subseção"),
        ("figure", "figura"),
        ("table", "tabela"),
        ("equation", "equação"),
        ("appendix", "apêndice"),
    ):
        if not re.search(r"\\crefname\{" + tipo + r"\}\{" + singular + r"\}", master_text):
            errors.append(
                f"L-01: \\crefname{{{tipo}}} em português ausente do mestre; "
                f"as referências a {tipo} sairiam em inglês."
            )
    if r"\crefrangeconjunction" not in master_text:
        errors.append(
            "L-01: \\crefrangeconjunction não redefinido; intervalos sairiam com "
            "o conector inglês \"to\"."
        )

    # L-02: o bloco auxiliar de seleção precisa ser aberto e fechado.
    partes = re.findall(r"\\part\*\{([^}]+)\}", corpus)
    if len(partes) < 2:
        errors.append(
            "L-02: o bloco auxiliar de seleção abre com \\part* mas não é fechado "
            "por uma retomada; as seções 16 em diante herdariam o rótulo auxiliar."
        )

    if errors:
        for error in errors:
            print(f"ERRO: {error}", file=sys.stderr)
        return 1

    print(
        "Auditoria estática aprovada: "
        f"{len(sources)} fontes ativos, {len(labels)} rótulos, "
        f"{len(refs)} referências internas, {len(cites)} chaves citadas e "
        f"{theorem_starts} ambientes matemáticos."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
