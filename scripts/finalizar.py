#!/usr/bin/env python3
from pathlib import Path
import json,re,shutil,hashlib,collections,csv
R=Path(__file__).resolve().parents[1]
rows=json.loads((R/'mapas/correspondencia_completa.json').read_text());aux=(R/'tex/principal.aux').read_text()
for r in rows:
 m=re.search(r'\\newlabel\{'+re.escape(r['rotulo_volume'])+r'\}\{\{([^}]+)\}\{([^}]+)\}',aux)
 r['pagina_volume']=int(m[2])
# Mirrored per-part sources are reading copies. Executable import trees stay intact.
for doc in dict.fromkeys(r['documento'] for r in rows):
 folder=R/'lean4/por_parte'/doc;part=[r for r in rows if r['documento']==doc]
 paths=sorted({v['caminho_entrega'] for r in part for v in r['resultados_lean']})
 for path in paths:
  q=folder/'fontes_referenciados'/Path(path).relative_to('lean4/ambientes');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(R/path,q)
 if doc=='normalizacao':
  for p in (R/'lean4/ambientes/base_integrada/Unified/SemanticBridge').glob('Normalization*.lean'):
   q=folder/'pontes_integradas'/p.name;q.parent.mkdir(exist_ok=True);shutil.copy2(p,q)
 text=(folder/'README.md').read_text();text+='\n## Cópias para leitura\n\n`fontes_referenciados/` reúne cópias byte a byte dos módulos associados. Para compilar, use os ambientes completos em `../../ambientes/`, que preservam imports e dependências.\n'
 (folder/'README.md').write_text(text)
 (folder/'mapa.json').write_text(json.dumps(part,ensure_ascii=False,indent=2))
# Dedicated gap dossier: distinguish source-origin gaps from auxiliary extensions.
notgap={'correspondencia_inspecionada','integrado_a_v2','observacao_editorial','generalizacao_documentada','formalizado_compilado'}
gaps=[r for r in rows if r['status'] not in notgap]
md='# Lacunas e diferenças semânticas localizadas\n\nEste inventário deriva das ressalvas já presentes na entrega recebida. Não cria novas provas ou obrigações presumidas. O número original identifica o manuscrito de 77 páginas; o número do volume identifica a presente edição.\n\n'
for r in gaps:
 md+='## '+r['numero_volume']+' — '+r['titulo']+'\n\nOriginal: **'+(', '.join(r['originais_77']) or 'desenvolvimento posterior, sem ambiente original diretamente associado')+'**. Página do volume: **'+str(r['pagina_volume'])+'**. Estado: `'+r['status']+'`.\n\n'+r['observacao']+'\n\nFonte: `'+r['tex_volume']+':'+str(r['linha_volume'])+'`; rótulo `'+r['rotulo_volume']+'`.\n\n'
 for l in r['resultados_lean']:md+='- `'+l['nome']+'` — `'+l['caminho_entrega']+':'+str(l['linha_lean'])+'`.\n'
 if not r['resultados_lean']:md+='Nenhuma declaração Lean localizada para este ambiente.\n'
 md+='\n'
(R/'mapas/LACUNAS_POR_ORIGEM.md').write_text(md)
(R/'mapas/correspondencia_completa.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
# Resolve inputs into a single editable TeX; bibliography is embedded, figures remain external.
def expand(path):
 s=path.read_text()
 return re.sub(r'\\input\{([^}]+)\}',lambda m:expand(path.parent/(m[1]+('' if Path(m[1]).suffix else '.tex'))),s)
flat=expand(R/'tex/principal.tex')
flat=flat.replace('\\bibliographystyle{plainnat}','').replace('\\bibliography{referencias}',(R/'tex/principal.bbl').read_text())
(R/'tex/documento_completo.tex').write_text('% Fonte único completo. Compilar nesta pasta com pdflatex duas vezes.\n% Figuras externas: figuras/<parte>/<nome>.pdf; bibliografia incorporada.\n'+flat)
shutil.copy2(R/'tex/principal.pdf',R/'Biblioteca_Unificada.pdf')
# Exact figure-to-source and PDF page lookup.
figs=json.loads((R/'mapas/figuras.json').read_text());index='# Figuras e pontos de uso\n\nOs PDFs são matrizes vetoriais usadas pelo LaTeX. PNG: 600 dpi. SVG: exportação vetorial. A figura de circuito foi recuperada do TikZ recebido e incluída na Parte I.\n\n'
for fig in figs:
 p=R/'tex'/fig['arquivo'];script='fontes_originais/FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/artigo_1/scripts/figuras.py' if fig['parte']=='artigo_1' else 'fontes_originais/FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/reproducibility/selecao/'
 t=R/'tex/partes'/(fig['parte']+'.tex');line=next(i for i,l in enumerate(t.read_text().splitlines(),1) if fig['arquivo'] in l)
 index+='- `tex/'+fig['arquivo']+'` — `tex/partes/'+fig['parte']+'.tex:'+str(line)+'`; script de origem: `'+script+'`.\n'
index+='\n- `tex/figuras/artigo_1/07_circuito.pdf` — mesma construção TikZ usada na Parte I; fonte editável `07_circuito.tex`. O uso no volume é TikZ direto, preservando a natureza vetorial.\n'
(R/'mapas/FIGURAS_E_USOS.md').write_text(index)
# Inventory every source Lean variant, including historical materials, without conflating them with active proofs.
inv=[]
for p in (R/'fontes_originais').rglob('*.lean'):
 inv.append({'arquivo':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(R/'mapas/inventario_lean_todo_acervo.json').write_text(json.dumps(inv,ensure_ascii=False,indent=2))
print('Finalizado:',len(rows),'ambientes,',len(gaps),'entradas com pendência/diferença,',len(inv),'arquivos Lean de origem.')
