#!/usr/bin/env python3
"""Verificação editorial e estrutural; não substitui lake build nem revisão de provas."""
from pathlib import Path
import json,re,hashlib,collections
import pymupdf
R=Path(__file__).resolve().parents[1]
rows=json.loads((R/'mapas/correspondencia_completa.json').read_text());aux=(R/'tex/principal.aux').read_text()
errors=[];associations=0
for row in rows:
 source=(R/row['tex_volume']).read_text().splitlines()
 if '\\label{'+row['rotulo_volume']+'}' not in source[row['linha_volume']-1]:errors.append('rótulo deslocado: '+row['id'])
 match=re.search(r'\\newlabel\{'+re.escape(row['rotulo_volume'])+r'\}\{\{([^}]+)\}\{([^}]+)\}',aux)
 if not match or match[1]!=row['numero_volume']:errors.append('numeração: '+row['id'])
 else:row['pagina_volume']=int(match[2])
 for lean in row['resultados_lean']:
  path=R/lean['caminho_entrega'];associations+=1
  if not path.is_file():errors.append('arquivo Lean ausente: '+str(path))
  else:
   # Source map lines point at a declaration. Compare the final identifier component.
   lines=path.read_text().splitlines();line=lean['linha_lean'];name=lean['nome'].split('.')[-1]
   if name not in '\n'.join(lines[max(0,line-3):line+5]):errors.append('declaração/linha divergente: '+lean['nome'])
log=(R/'tex/principal.log').read_text(errors='replace')
for pattern in ['Overfull', 'undefined references','multiply defined','Missing character']:
 if pattern in log:errors.append('LaTeX: '+pattern)
originals={n for row in rows for n in row['originais_77']}
if len(rows)!=151:errors.append('número de ambientes')
if len(originals)!=108:errors.append('cobertura original')
# Byte preservation against received source copies, including every mirrored Lean module.
source=R/'fontes_originais/FORMALIZACAO_COMPLETA_DA_BIBLIOTECA';checks=0
for dest,orig in [('base_integrada/Unified','Unified'),('base_integrada/entradas/parte_1','entradas/parte_1'),('parte_1','validacao/parte_1'),('artigo_2','validacao/artigo_2')]:
 for p in (source/orig).rglob('*.lean'):
  q=R/'lean4/ambientes'/dest/p.relative_to(source/orig);checks+=1
  if p.read_bytes()!=q.read_bytes():errors.append('Lean alterado: '+str(q))
report={'escopo':'Verificação editorial/estrutural nesta sessão. Lean não recompilado.','ambientes':len(rows),'ambientes_original_77_cobertos':len(originals),'associacoes_lean':associations,'fontes_lean_comparados_byte_a_byte':checks,'paginas':len(pymupdf.open(R/'tex/principal.pdf')),'categorias_recebidas':dict(collections.Counter(x['status'] for x in rows)),'erros':errors}
(R/'verificacao/resultado_editorial.json').write_text(json.dumps(report,ensure_ascii=False,indent=2))
(R/'mapas/correspondencia_completa.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
print(json.dumps(report,ensure_ascii=False,indent=2))
if errors:raise SystemExit(1)
