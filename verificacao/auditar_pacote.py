#!/usr/bin/env python3
"""Auditoria reprodutível do pacote; não certifica equivalência matemática TeX–Lean.

Uso: python3 -I verificacao/auditar_pacote.py linha_base|final
Requer o ambiente Python documentado em AGENTS.md. Não altera fontes/derivados.
Logs de build e caches .lake são evidências de trabalho, excluídos da entrega.
"""
from pathlib import Path
import os
import json
import re
import subprocess
import sys
import unicodedata
import pymupdf

ROOT = Path(__file__).resolve().parents[1]
phase = sys.argv[1]
assert phase in {'linha_base', 'final'}
errors = []
report = {'fase': phase, 'erros': errors}

def norm(s):
    s = unicodedata.normalize('NFKD', s).lower()
    return ''.join(c for c in s if c.isalnum())

allowed = {'AGENTS.md', 'LEIA_PRIMEIRO.md', 'Biblioteca_Unificada.pdf',
           'SHA256SUMS.txt', 'requirements.txt', 'STATUS_AUTOMATICO.md', 'LOG_TRABALHO.md',
           'gemini.md', 'README.md', '.gitignore', '.gitattributes'}
report['arquivos_raiz_inesperados'] = [p.name for p in ROOT.iterdir() if p.is_file() and p.name not in allowed]
if report['arquivos_raiz_inesperados']:
    errors.append('arquivos soltos na raiz')
required = ['tex', 'tex/partes', 'tex/figuras', 'lean4/ambientes/artigo_2',
            'lean4/ambientes/base_integrada', 'lean4/ambientes/parte_1', 'lean4/por_parte',
            'mapas', 'pendencias_restantes/itens', 'compilar_pendencias',
            'scripts', 'verificacao', 'fontes_originais', 'historico']
report['diretorios_ausentes'] = [p for p in required if not (ROOT / p).is_dir()]
if report['diretorios_ausentes']:
    errors.append('diretórios obrigatórios ausentes')
report['modulos_sem_readme'] = []
for rel in ['lean4/ambientes/artigo_2/Pendencias', 'lean4/ambientes/base_integrada/PendenciasParte1']:
    folder = ROOT / rel
    readme = (folder / 'README.md').read_text()
    report['modulos_sem_readme'].extend(str(p.relative_to(ROOT)) for p in folder.glob('*.lean') if p.name not in readme)
if report['modulos_sem_readme']:
    errors.append('módulos novos sem índice README')
files = []
for folder, dirs, names in os.walk(ROOT):
    dirs[:] = [d for d in dirs if d not in {'.lake', '.git', '.agents', '.codex', '.aws'}
               and not (Path(folder) == ROOT / 'compilar_pendencias' and d == 'logs')]
    files.extend(Path(folder) / name for name in names)
report['temporarios'] = [str(p.relative_to(ROOT)) for p in files
                        if p.suffix in {'.pyc', '.tmp', '.bak', '.swp'} or '__pycache__' in p.parts]
if report['temporarios']:
    errors.append('temporários no pacote')

pdf = pymupdf.open(ROOT / 'Biblioteca_Unificada.pdf')
other = pymupdf.open(ROOT / 'tex/principal.pdf')
report['paginas'] = len(pdf)
report['pdfs_identicos'] = (ROOT / 'Biblioteca_Unificada.pdf').read_bytes() == (ROOT / 'tex/principal.pdf').read_bytes()
if not report['pdfs_identicos']:
    errors.append('PDF da raiz diferente do PDF modular')
report['paginas_sem_conteudo'] = [i + 1 for i, p in enumerate(pdf)
                                if not p.get_text().strip() and not p.get_images() and not p.get_drawings()]
if report['paginas_sem_conteudo']:
    errors.append('páginas sem conteúdo')
report['avisos_latex'] = re.findall(r'^.*(?:undefined|Missing character|Overfull|multiply defined|Float too large|same identifier).*$',
                                  (ROOT / 'tex/principal.log').read_text(errors='replace'), re.M)
if report['avisos_latex']:
    errors.append('avisos proibidos no LaTeX')
text = subprocess.check_output(['pdftotext', '-layout', str(ROOT / 'Biblioteca_Unificada.pdf'), '-']).decode()
report['referencias_quebradas'] = re.findall(r'\?\?|\\(?:ref|cite|begin)\b', text)
if report['referencias_quebradas']:
    errors.append('referências quebradas no texto do PDF')
fonts = subprocess.check_output(['pdffonts', str(ROOT / 'Biblioteca_Unificada.pdf')]).decode()
report['fontes_nao_incorporadas'] = [s for s in fonts.splitlines()[2:]
                                   if re.search(r'\sno\s+(?:yes|no)\s+(?:yes|no)\s+\d+\s+\d+\s*$', s)]
if report['fontes_nao_incorporadas']:
    errors.append('fontes não incorporadas')

toc = pdf.get_toc()
report['sumario_entradas'] = len(toc)
report['sumario_paginas_crescentes'] = all(a[2] <= b[2] for a, b in zip(toc, toc[1:]))
report['sumario_titulos_ausentes'] = [t for _, t, n in toc if norm(t) not in norm(pdf[n - 1].get_text())]
# Also require the printed .toc's page sequence to match the PDF outline sequence.
source_toc = (ROOT / 'tex/principal.toc').read_text()
toc_pages = [int(n) for kind, n in re.findall(r'^\\contentsline \{([^}]+)\}.*\}\{(\d+)\}\{[^}]+\}', source_toc, re.M) if kind in {'part', 'section', 'subsection'}]
report['sumario_impresso_paginas_conferem'] = toc_pages == [n for _, _, n in toc]
if not report['sumario_paginas_crescentes'] or report['sumario_titulos_ausentes'] or not report['sumario_impresso_paginas_conferem']:
    errors.append('sumário precisa de inspeção')

figs = ROOT / 'tex/figuras'
report['figuras_por_formato'] = {ext: len(list(figs.rglob('*.' + ext))) for ext in ['pdf', 'svg', 'png']}
report['figuras_sem_tres_formatos'] = [str(p.relative_to(ROOT)) for p in figs.rglob('*.pdf')
                                     if not all(p.with_suffix('.' + ext).is_file() for ext in ['svg', 'png'])]
if report['figuras_por_formato'] != {'pdf': 17, 'svg': 17, 'png': 17} or report['figuras_sem_tres_formatos']:
    errors.append('exportações de figuras divergentes')
report['inclusoes_ausentes'] = []
for p in (ROOT / 'tex/partes').glob('*.tex'):
    for f in re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}', p.read_text()):
        if not (ROOT / 'tex' / f).is_file():
            report['inclusoes_ausentes'].append(f)
if report['inclusoes_ausentes']:
    errors.append('includegraphics sem arquivo')

bib = (ROOT / 'tex/referencias.bib').read_text()
keys = set(re.findall(r'@\w+\s*\{([^,]+),', bib))
cited = set()
for p in (ROOT / 'tex/partes').glob('*.tex'):
    for ks in re.findall(r'\\cite\w*\*?(?:\[[^\]]*\]){0,2}\{([^}]+)\}', p.read_text()):
        cited.update(k.strip() for k in ks.split(','))
report['bibliografia'] = {'entradas': len(keys), 'citadas': len(cited),
                          'citacoes_sem_entrada': sorted(cited - keys), 'sem_uso': sorted(keys - cited)}
if cited - keys:
    errors.append('citação sem entrada bibliográfica')

rows = json.loads((ROOT / 'mapas/correspondencia_completa.json').read_text())
report['copias_lean_desatualizadas'] = []
for row in rows:
    for item in row['resultados_lean']:
        source = Path(item['caminho_entrega'])
        mirror = ROOT / 'lean4/por_parte' / row['documento'] / 'fontes_referenciados' / source.relative_to('lean4/ambientes')
        if not mirror.is_file() or mirror.read_bytes() != (ROOT / source).read_bytes():
            report['copias_lean_desatualizadas'].append(str(mirror.relative_to(ROOT)))
report['copias_lean_desatualizadas'] = sorted(set(report['copias_lean_desatualizadas']))
if report['copias_lean_desatualizadas']:
    errors.append('cópias Lean por parte desatualizadas')

def expand(p):
    return re.sub(r'\\input\{([^}]+)\}', lambda m: expand(p.parent / (m[1] + ('' if Path(m[1]).suffix else '.tex'))), p.read_text())
flat = expand(ROOT / 'tex/principal.tex').replace('\\bibliographystyle{plainnat}', '').replace(
    '\\bibliography{referencias}', (ROOT / 'tex/principal.bbl').read_text())
expected = '% Fonte único completo. Compilar nesta pasta com pdflatex duas vezes.\n% Figuras externas: figuras/<parte>/<nome>.pdf; bibliografia incorporada.\n' + flat
report['fonte_unico_sincronizado'] = (ROOT / 'tex/documento_completo.tex').read_text() == expected
if not report['fonte_unico_sincronizado']:
    errors.append('fonte único desatualizado')

# Duplicate bytes in protected originals, context dossiers and generated reading copies
# are intentional provenance/mirrors, not candidates for automatic deletion.
report['duplicacoes_documentadas'] = ['fontes_originais', 'historico', 'pendencias_restantes/contexto',
                                     'lean4/por_parte', 'Biblioteca_Unificada.pdf = tex/principal.pdf']
report['integridade'] = 'Verificar separadamente com sha256sum -c SHA256SUMS.txt após a última escrita.'
output = ROOT / 'verificacao' / ('auditoria_' + phase + '.json')
output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(report, ensure_ascii=False, indent=2))

if phase == "final" and errors:
    raise SystemExit(1)
