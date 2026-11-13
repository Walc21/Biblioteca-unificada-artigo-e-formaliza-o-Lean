#!/usr/bin/env python3
"""Exporta matrizes PDF para PNG a 600 dpi e SVG vetorial, sem redesenhar os dados."""
from pathlib import Path
import pymupdf,json,subprocess,re
R=Path(__file__).resolve().parents[1]
f=R/'tex/figuras/artigo_1';source=(R/'fontes_originais/FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_1/figuras/circuito.tex').read_text()
picture=source[source.index('\\begin{tikzpicture}'):source.index('\\end{tikzpicture}')+len('\\end{tikzpicture}')]
standalone=r'''\documentclass[tikz,border=5pt]{standalone}
\usepackage[T1]{fontenc}\usepackage[utf8]{inputenc}\usepackage{lmodern,amsmath,amssymb}
\usetikzlibrary{arrows.meta,positioning,calc,fit}
\definecolor{ink}{HTML}{172C3C}\definecolor{accent}{HTML}{166F80}
\newcommand{\LL}{\mathcal L}
\begin{document}
'''+picture+'\n\\end{document}\n'
(f/'07_circuito.tex').write_text(standalone)
subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','07_circuito.tex'],cwd=f,stdout=subprocess.DEVNULL,check=True)
manifest=[]
for p in sorted((R/'tex/figuras').rglob('*.pdf')):
 doc=pymupdf.open(p);page=doc[0]
 png=p.with_suffix('.png');svg=p.with_suffix('.svg')
 pix=page.get_pixmap(dpi=600,alpha=False);pix.save(png);svg.write_text(page.get_svg_image())
 manifest.append({'pdf_vetorial':str(p.relative_to(R)),'png_600dpi':str(png.relative_to(R)),'svg':str(svg.relative_to(R)),'largura_px':pix.width,'altura_px':pix.height,'dpi':600})
(R/'mapas/exportacoes_figuras.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2))
print('Exportadas',len(manifest),'matrizes vetoriais para PNG 600 dpi e SVG.')
