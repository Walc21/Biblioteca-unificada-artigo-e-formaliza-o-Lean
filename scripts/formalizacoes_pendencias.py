#!/usr/bin/env python3
"""Reaplica, de forma idempotente, as provas Lean que fecharam lacunas (biblioteca Pendencias).

Fonte de verdade: mapas/formalizacoes_pendencias.json. Chamado por reconstruir.py para que a
reconstrução do volume não perca (a) o estado «formalizado_compilado» dos casos fechados,
(b) as declarações de lean4/ambientes/artigo_2/Pendencias e (c) o bloco lean_lib Pendencias do lakefile.
"""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
NOME_ESTADO='Formalizado e compilado'
LIB_BLOCO='\n[[lean_lib]]\nname = "Pendencias"\nglobs = ["Pendencias", "Pendencias.+"]\n'
def casos():
    return json.loads((ROOT/'mapas/formalizacoes_pendencias.json').read_text())['casos']
def aplicar_linhas(allrows):
    ov=casos()
    for r in allrows:
        o=ov.get(r['id'])
        if not o:continue
        r['status']=o['status']
        if o['observacao_adicional'] not in r['observacao']:
            r['observacao']=(r['observacao']+' '+o['observacao_adicional']).strip()
        tem={x['nome'] for x in r['resultados_lean']}
        for x in o['resultados_lean']:
            if x['nome'] not in tem:r['resultados_lean'].append(dict(x))
def restaurar_lakefile():
    p=ROOT/'lean4/ambientes/artigo_2/lakefile.toml';t=p.read_text()
    if 'name = "Pendencias"' not in t:p.write_text(t.rstrip('\n')+'\n'+LIB_BLOCO)
def nota_mapa_tex():
    """Parágrafo no aparato de correspondência do PDF; idempotente."""
    p=ROOT/'tex/mapa_formal.tex';t=p.read_text()
    n=sum(o['status']=='formalizado_compilado' for o in casos().values())
    nota=('Até 13/11/2026, %d resultados antes pendentes passaram ao estado «Formalizado e compilado»: '
          'provas Lean compiladas com Lean/Mathlib 4.28.0 nas bibliotecas \\texttt{Pendencias} e \\texttt{PendenciasParte1} dos ambientes \\texttt{artigo\\_2} e \\texttt{base\\_integrada}, '
          'sem \\texttt{sorry} e apenas com os axiomas \\texttt{propext}, \\texttt{Classical.choice} e \\texttt{Quot.sound}. '
          'Os demais casos pendentes seguem descritos acima e em \\texttt{pendencias\\_lean/}.\n\n')%n
    if 'Formalizado e compilado»' in t:return
    a='\\subsection*{Parte I}'
    assert t.count(a)==1
    p.write_text(t.replace(a,nota+a))

TAIL_TEX=r'Compilado com Lean/Mathlib 4.28.0 (\texttt{lake build Pendencias}); axiomas: \texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}.'
def nota_tex(r,esc):
    """Texto LaTeX-seguro (sem Unicode matemático) da linha do aparato do PDF, ou None se o caso não foi fechado aqui."""
    o=casos().get(r['id'])
    if not o:return None
    if o['status']=='prova_textual_sincronizada':
        return 'Prova textual sincronizada. '+o['observacao_tex']
    base=re.split(r' \[\d{2}/\d{2}/\d{4}\]', r['observacao'])[0].strip()
    tail=TAIL_TEX
    if any(x.get('pacote')=='base_v2' for x in o['resultados_lean']):
        tail=tail.replace('lake build Pendencias', 'lake build PendenciasParte1')
    s=NOME_ESTADO+'. '+o['observacao_tex']+' '+tail
    if base:s+=' Ressalva anterior: '+esc(base).replace('^',r'\textasciicircum{}')
    return s
