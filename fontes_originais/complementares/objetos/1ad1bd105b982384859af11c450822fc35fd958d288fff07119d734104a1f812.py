#!/usr/bin/env python3
"""Verificação de integridade editorial da composição LaTeX."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def expand(path):
    text = path.read_text(encoding="utf-8")
    return re.sub(r"\\input\{([^}]+)\}",
                  lambda m: expand(ROOT/(m.group(1)+".tex")), text)


def main():
    text = expand(ROOT/"artigo.tex")
    eqs = re.findall(r"\\eqn\{(\d+)\}", text)
    assert eqs == [f"{j:02d}" for j in range(1,96)], eqs
    labels = re.findall(r"\\label\{([^}]+)\}",text)
    assert len(labels) == len(set(labels)), "Rótulo duplicado."
    declared = set(labels)|{"eq:"+n for n in eqs}
    declared.update("fig:"+k for k in re.findall(r"\\figura.*\{([^{}]+)\}\s*$",text,re.M))
    refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}",text)
    assert set(refs)<=declared, set(refs)-declared
    proofs = len(re.findall(r"\\begin\{proof\}",text))
    assert proofs == 37, proofs
    assert len(re.findall(r"\\end\{proof\}",text)) == proofs
    expected = {2:5,3:6,4:5,5:2,6:6,7:25}
    sections = re.split(r"\\section\{", text)[1:]
    for num,count in expected.items():
        block = sections[num-1]
        actual = len(re.findall(
            r"\\begin\{(?:teorema|lema|proposicao|corolario|definicao|algoritmo|observacao)\}",block))
        assert actual == count,(num,actual,count)
    bib = (ROOT/"referencias.bib").read_text(encoding="utf-8")
    keys = set(re.findall(r"@\w+\{([^,]+),",bib))
    used = set()
    for group in re.findall(r"\\cite[pt]?(?:\[[^\]]*\])?\{([^}]+)\}",text):
        used.update(group.split(","))
    assert used == keys, {"sem_referencia":used-keys,"sem_citacao":keys-used}
    for removed in ["Teoria auxiliar de seleção exata", "Programação dinâmica em uma árvore fixa",
                    "Funcional aditivo e representação canônica", "Validação computacional exata"]:
        assert removed not in text, removed
    print(f"Integridade: 95 equações, 49 enunciados, {proofs} demonstrações, "
          f"{len(keys)} referências citadas; remissões resolvidas.")


if __name__=="__main__":
    main()
