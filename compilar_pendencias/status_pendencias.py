#!/usr/bin/env python3
"""Relatório das pendências formais da Biblioteca (somente leitura).

Lê mapas/correspondencia_completa.json, lista os itens ainda sem prova Lean completa
e procura, nas bibliotecas Pendencias e PendenciasParte1, uma declaração que os cubra.
Um item conta como encontrado quando um arquivo .lean traz, no cabeçalho ou docstring,
"Teorema IV.5.2", "Lema ...", "Proposição ...", "Corolário ...", "Definição ...",
"Algoritmo ...", "# IV.5.2" ou "-- ITEM: IV.5.2".
"""
import json, re, sys
from collections import Counter
from pathlib import Path

RAIZ = Path(__file__).resolve().parents[1]
ABERTOS = {'nao_formalizado_no_acervo', 'sem_formalizacao_localizada', 'cobertura_parcial'}
BIBS = [RAIZ / 'lean4/ambientes/artigo_2/Pendencias',
        RAIZ / 'lean4/ambientes/base_integrada/PendenciasParte1']
KIND = r'(?:Teorema|Lema|Proposi[cç][aã]o|Corol[aá]rio|Defini[cç][aã]o|Algoritmo|ITEM:?|#)'
ID = r'[IVX]+\.\d+\.\d+'


def sem_comentarios(t):
    t = re.sub(r'/-.*?-/', '', t, flags=re.S)
    return re.sub(r'--[^\n]*', '', t)


def arquivos_lean():
    for b in BIBS:
        if b.is_dir():
            yield from sorted(b.rglob('*.lean'))


def main():
    rows = json.loads((RAIZ / 'mapas/correspondencia_completa.json').read_text(encoding='utf-8'))
    total = len(rows)
    formalizaveis = [r for r in rows if r['tipo'] != 'observacao']
    pend = [r for r in rows if r['status'] in ABERTOS]
    textos = {p: p.read_text(encoding='utf-8') for p in arquivos_lean()}

    achados = {}
    for r in pend:
        num = r['numero_volume']
        pat = re.compile(KIND + r'\s*\**\s*' + re.escape(num) + r'(?!\d)')
        for p, t in textos.items():
            if pat.search(t):
                tem_sorry = re.search(r'\bsorry\b', sem_comentarios(t)) is not None
                achados[num] = (p.relative_to(RAIZ).as_posix(), tem_sorry)
                break

    # dependências entre pendentes, a partir dos arquivos de itens
    ids = {r['numero_volume'] for r in pend}
    deps = {}
    for r in pend:
        f = RAIZ / 'pendencias_restantes/itens' / (r['numero_volume'] + '.md')
        d = set()
        if f.is_file():
            m = re.search(r'Depend[êe]ncias[^:\n]*:\*\*([^\n]*)', f.read_text(encoding='utf-8'))
            if m:
                d = set(re.findall(ID, m.group(1))) & ids
        deps[r['numero_volume']] = d - {r['numero_volume']}
    ordem, resto = [], dict(deps)
    while resto:
        livres = sorted(k for k, v in resto.items() if not (v - set(ordem)))
        if not livres:
            livres = sorted(resto)
        for k in livres:
            ordem.append(k)
            resto.pop(k)
    por_id = {r['numero_volume']: r for r in pend}

    print(f'Itens: {total} ambientes, {len(formalizaveis)} formalizáveis (sem observações).')
    for s, n in Counter(r['status'] for r in rows).most_common():
        print(f'  {s:32s} {n:4d}')
    print()
    print(f'Pendências abertas segundo o mapa: {len(pend)} '
          f'({100 * len(pend) / len(formalizaveis):.1f}% dos formalizáveis)')
    print()
    print(f'{"#":>2}  {"item":9s} {"tipo":10s} {"Lean encontrado":18s} depende de (abertas)')
    resolvidos = 0
    for i, num in enumerate(ordem, 1):
        r = por_id[num]
        if num in achados:
            arq, sorry = achados[num]
            est = 'COM sorry' if sorry else 'ENCONTRADO'
            resolvidos += 0 if sorry else 1
        else:
            est = 'aberto'
        print(f'{i:>2}  {num:9s} {r["tipo"]:10s} {est:18s} {", ".join(sorted(deps[num])) or "-"}')
        if num in achados:
            print(f'      -> {achados[num][0]}')
    print()
    print(f'Com Lean encontrado e sem sorry: {resolvidos} de {len(pend)}.')
    if resolvidos:
        print('Atualize o mapa (mapas/formalizacoes_pendencias.json) para refletir os itens novos.')
    print('Detalhes de cada item: pendencias_restantes/itens/<item>.md')


if __name__ == '__main__':
    sys.exit(main())
