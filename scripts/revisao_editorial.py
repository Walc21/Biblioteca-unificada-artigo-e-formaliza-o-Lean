#!/usr/bin/env python3
"""Revisão editorial (itens 1-3) aplicada de forma idempotente sobre a saída de reconstruir.py.

Os trechos estão em revisao_editorial.json: {arquivo: [[antigo, novo], ...]}.
Cada trecho antigo deve ocorrer uma única vez; se o novo já está presente, é ignorado.
"""
from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parent
OBS={
 'artigo_2:3.12':('coding_gap_family prova uma cadeia para todo N par. Falta a arvore em raiz unica para N=2^r; H=N=6 produz suporte [0,3/16], que nao e uma celula diadica unica.',
  'coding_gap_family prova uma cadeia para todo N par. O enunciado deste volume usa N=2^r e raiz J(H-1-r,0); a arvore em raiz unica para N=2^r continua nao formalizada em Lean (H=N=6 produz suporte [0,3/16], que nao e uma celula diadica unica).'),
 'artigo_1:4.3':('O enunciado TeX antigo ainda usa g(t0) onde t0 pode estar fora de K; a diferenca textual permanece explicita, sem mudar silenciosamente o enunciado.',
  'O enunciado TeX deste volume le g(t0) como o valor em t0 da primeira peca (t0 pode estar fora de K); essa leitura nao foi reverificada contra o enunciado Lean.'),
}
def aplicar_observacoes(allrows):
    for r in allrows:
        if r['id'] in OBS:r['observacao']=r['observacao'].replace(*OBS[r['id']])
def aplicar_trechos(root,arquivos=None):
    patches=json.loads((HERE/'revisao_editorial.json').read_text())
    for rel,hunks in patches.items():
        if arquivos is not None and rel not in arquivos:continue
        p=Path(root)/rel;t=p.read_text()
        for old,new in hunks:
            if t.count(old)==1:t=t.replace(old,new)
            elif new in t:continue
            else:raise RuntimeError(('trecho da revisão não encontrado',rel,old[:80]))
        p.write_text(t)
def recalcular_linhas(root,allrows):
    cache={}
    for r in allrows:
        lines=cache.setdefault(r['tex_volume'],(Path(root)/r['tex_volume']).read_text().splitlines())
        r['linha_volume']=next(i for i,l in enumerate(lines,1) if '\\label{'+r['rotulo_volume']+'}' in l)
