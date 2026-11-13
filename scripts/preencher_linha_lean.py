#!/usr/bin/env python3
"""Preenche `linha_lean` nas associações TeX->Lean dos casos fechados em 11/11
(status formalizado_compilado), que foram adicionadas sem esse campo.
A linha é a da declaração (theorem/lemma/def/...) cujo último componente de nome
coincide com `nome`. Falha se alguma declaração não for encontrada."""
import json, re, sys
from pathlib import Path

R = Path(sys.argv[1]).resolve()
mp = R / 'mapas/correspondencia_completa.json'
rows = json.loads(mp.read_text())
KW = r'(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)'
filled, failed = 0, []
for r in rows:
    for l in r['resultados_lean']:
        if 'linha_lean' in l:
            continue
        path = R / l['caminho_entrega']
        last = l['nome'].split('.')[-1]
        pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
                         + KW + r'\s+(?:[\w.]*\.)?' + re.escape(last) + r"(?![\w'])")
        hit = None
        for i, line in enumerate(path.read_text().splitlines(), 1):
            if pat.search(line):
                hit = i
                break
        if hit is None:
            failed.append((r['id'], l['nome'], l['caminho_entrega']))
        else:
            l['linha_lean'] = hit
            filled += 1
if failed:
    print('NÃO ENCONTRADAS:', *failed, sep='\n  ')
    sys.exit(1)
mp.write_text(json.dumps(rows, ensure_ascii=False, indent=2))
print(f'linha_lean preenchida em {filled} associações')
