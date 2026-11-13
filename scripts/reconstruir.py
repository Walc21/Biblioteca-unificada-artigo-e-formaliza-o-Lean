#!/usr/bin/env python3
"""Reconstrói o volume a partir da cópia integral dos fontes recebidos."""
from pathlib import Path
import re,json,shutil,csv,hashlib
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'fontes_originais/FORMALIZACAO_COMPLETA_DA_BIBLIOTECA'
if not SRC.exists():
    origem=Path('input/Biblioteca_Consolidada')
    shutil.copytree(origem,ROOT/'fontes_originais',dirs_exist_ok=True)
B=SRC
for n in ['tex/partes','tex/figuras','mapas','lean4/por_parte','lean4/ambientes','verificacao']:(ROOT/n).mkdir(parents=True,exist_ok=True)
D=json.loads((B/'documentacao/enunciados.json').read_text())
C=json.loads((B/'documentacao/conferencia_original_77.json').read_text())
parts=[('artigo_1','I','Biblioteca, endereçamento e refinamento','artigos/artigo_1/artigo.tex'),('normalizacao','II','Normalização e equivalência das montagens','entradas/parte_1/Solucao_Equivalencia_Montagens_Parte_1 (1).tex'),('artigo_2','III','Custo, entropia e seleção exata','artigos/artigo_2/Artigo_2.tex'),('artigo_3','IV','Agendas de altura e teoria direta--inversa','artigos/artigo_3/Artigo_3.tex'),('complemento_original','V','Complementos do manuscrito original','artigos/complemento_original_77/complemento.tex')]
partno={x[0]:x[1] for x in parts}
originals={}
for row in C['enunciados']:
 for dest in row['destinos']:originals.setdefault(dest['id'],[]).append(row['original']['numero'])
byline={(r['arquivo_tex'],r['linha_tex']):r for r in D['enunciados']}
allrows=[]; figures=[]
# Copy executable Lean environments with their import trees intact.
base=ROOT/'lean4/ambientes/base_integrada'
base.mkdir(exist_ok=True)
for name in ['Unified','Unified.lean','lakefile.toml','lake-manifest.json','lean-toolchain','AuditoriaIntegracao.lean','AuditoriaAxiomas.lean','AuditoriaAxiomasPontes.lean','SemanticAudit.lean']:
 p=B/name; q=base/name
 if p.is_dir():shutil.copytree(p,q,dirs_exist_ok=True)
 else:shutil.copy2(p,q)
shutil.copytree(B/'entradas/parte_1',base/'entradas/parte_1',dirs_exist_ok=True)
for name in ['parte_1','artigo_2']:shutil.copytree(B/'validacao'/name,ROOT/'lean4/ambientes'/name,dirs_exist_ok=True)
for doc,roman,title,rel in parts:
 p=B/rel; source=p.read_text(); pre,body=source.split('\\begin{document}',1);body=body.split('\\end{document}')[0]
 # Use native body. Drop only the separate title and the per-article bibliography.
 body=re.sub(r'\\maketitle(?:\\thispagestyle\{plain\})?','',body)
 body=body.replace('\\thispagestyle{plain}','').replace('\\vspace{-9mm}','')
 body=re.sub(r'\\FloatBarrier\s*\\clearpage\s*\\renewcommand\{\\refname\}.*','',body,flags=re.S) if doc in ['artigo_2','artigo_3'] else body
 if doc=='complemento_original':body=re.sub(r'\\renewcommand\{\\refname\}.*','',body,flags=re.S)
 if doc=='artigo_1':body=body[:body.index('\\bibliographystyle')]
 def expand_text(txt,path,offset=0):
  out=[]
  for i,line in enumerate(txt.splitlines(),1):
   key=(str(path.relative_to(B)),i+offset)
   row=byline.get(key)
   if row:
    out.append('% MAPA '+row['id']+' | fonte '+key[0]+':'+str(key[1]))
    # Place stable label after the optional theorem title, never before it.
    line=re.sub(r'(\\begin\{(?:teorema|lema|proposicao|corolario|definicao|algoritmo|observacao|theorem|lemma|proposition|corollary|definition|algorithm|remark)\}(?:\[[^\]]*\])?)',lambda m:m[0]+'\\label{map:'+row['id']+'}',line,count=1)
   m=re.search(r'\\input\{([^}]+)\}',line)
   if m:
    name=m[1]; target=path.parent/name
    if not target.suffix:target=target.with_suffix('.tex')
    out.append('% INICIO '+str(target.relative_to(B)))
    out.append(expand_text(target.read_text(),target))
    out.append('% FIM '+str(target.relative_to(B)))
   else:out.append(line)
  return '\n'.join(out)
 # Preserve original physical line offsets while applying initial body substitutions.
 # Monolithic article rows are inserted by matching the source line's environment prefix.
 if doc in ['artigo_2','artigo_3','normalizacao']:
  rows=[r for r in D['enunciados'] if r['documento']==doc]
  lines=source.splitlines(); cursor=0
  for r in rows:
   origline=lines[r['linha_tex']-1]
   pos=body.find(origline,cursor)
   if pos<0:raise RuntimeError(('cannot locate environment',r['id'],origline))
   labeled=re.sub(r'(\\begin\{(?:theorem|lemma|proposition|corollary|definition|algorithm|remark|teorema|lema|proposicao|corolario|definicao)\}(?:\[[^\]]*\])?)',lambda m:m[0]+'\\label{map:'+r['id']+'}',origline,count=1)
   body=body[:pos]+'% MAPA '+r['id']+'\n'+labeled+body[pos+len(origline):];cursor=pos+len(labeled)+len(r['id'])+8
  # no input statements in these bodies
 else:body=expand_text(body,p)
 if doc=='artigo_1':
  body=body.replace('\\section{Conclusão}',(p.parent/'figuras/circuito.tex').read_text()+'\n\\section{Conclusão}')
 if doc=='normalizacao':body=body.replace('\\appendix','\\clearpage\n\\setcounter{section}{0}\\renewcommand{\\thesection}{II.\\Alph{section}}')
 # Make every label/reference unique across the five native documents.
 def labelrewrite(m):
  cmd,arg=m[1],m[2]
  return '\\'+cmd+'{'+','.join(a if a.strip().startswith('map:') else doc+':'+a.strip() for a in arg.split(','))+'}'
 body=re.sub(r'\\(label|ref|eqref|cref|Cref|pageref|autoref)\{([^}]+)\}',labelrewrite,body)
 if doc=='artigo_1':
  body=re.sub(r'\\eqn\{([^}]+)\}',lambda m:'\\eqn{'+doc+':'+m[1]+'}',body)
  # eqn helper itself adds eq:, so use a local helper with the namespaced prefix.
  body=body.replace('\\eqn{'+doc+':','\\eqn{')
  body='\\renewcommand{\\eqn}[2]{\\begin{equation}\\label{artigo_1:eq:#1}#2\\end{equation}}\n'+body
  body=body.replace('\\appendix','\\clearpage\n\\section*{Apêndice da Parte I}\\addcontentsline{toc}{section}{Apêndice da Parte I}\n\\setcounter{section}{0}\\renewcommand{\\thesection}{I.\\Alph{section}}')
  body=body.replace('\\input{figuras/circuito.tex}',(p.parent/'figuras/circuito.tex').read_text())
 # Qualify graphic paths. PDF is vector master, PNG is a secondary export.
 figdir=ROOT/'tex/figuras'/doc;figdir.mkdir(exist_ok=True)
 for fp in (p.parent/'figuras').glob('*.pdf') if (p.parent/'figuras').exists() else []:shutil.copy2(fp,figdir/fp.name)
 if doc=='artigo_1':
  def fmacro(m):
   name,width,cap,label=m.groups();figures.append({'parte':doc,'arquivo':f'figuras/{doc}/{name}.pdf','rotulo':f'{doc}:fig:{label}','legenda':cap})
   return '\\begin{figure}[!htbp]\\centering\n\\includegraphics[width='+width+'\\linewidth]{figuras/'+doc+'/'+name+'.pdf}\n\\caption{'+cap+'}\\label{'+doc+':fig:'+label+'}\\end{figure}'
  # Arguments here are single-line simple braces except captions, handled with balanced parser below.
  def parse_args(text,start,n):
   args=[];j=start
   for _ in range(n):
    while text[j].isspace():j+=1
    assert text[j]=='{';depth=1;k=j+1;j+=1
    while depth:
     if text[j]=='{':depth+=1
     elif text[j]=='}':depth-=1
     j+=1
    args.append(text[k:j-1])
   return args,j
  while '\\figura{' in body:
   pos=body.index('\\figura{');args,end=parse_args(body,pos+len('\\figura'),4);name,width,cap,label=args
   figures.append({'parte':doc,'arquivo':f'figuras/{doc}/{name}.pdf','rotulo':f'{doc}:fig:{label}','legenda':cap})
   replacement='\\begin{figure}[!htbp]\\centering\n\\includegraphics[width='+width+'\\linewidth]{figuras/'+doc+'/'+name+'.pdf}\n\\caption{'+cap+'}\\label{'+doc+':fig:'+label+'}\\end{figure}'
   body=body[:pos]+replacement+body[end:]
 else:
  body=re.sub(r'\\includegraphics(\[[^\]]*\])?\{([^}]+)\}',lambda m:'\\includegraphics'+(m[1] or '')+'{figuras/'+doc+'/'+Path(m[2]).name+'}',body)
  for name in re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}',body):figures.append({'parte':doc,'arquivo':name})
 # Direct graphic inclusions in Part I also need a qualified path.
 if doc=='artigo_1':
  body=re.sub(r'\\includegraphics(\[[^\]]*\])?\{figuras/(?!artigo_1/)([^}]+)\}',lambda m:'\\includegraphics'+(m[1] or '')+'{figuras/artigo_1/'+m[2]+'}',body)
  existing={v['arquivo'] for v in figures}
  for name in re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}',body):
   if name not in existing:figures.append({'parte':doc,'arquivo':name});existing.add(name)
 if doc=='artigo_2':body=body.replace('$[I(f)^2/8,I(f)^2/2]$', '$[I(f)^2/8,\\allowbreak I(f)^2/2]$')
 # Cite keys get a namespace; the final volume has one bibliography.
 body=re.sub(r'(\\cite\w*\*?(?:\[[^\]]*\]){0,2})\{([^}]+)\}',lambda m:m[1]+'{'+','.join(doc+'-'+x.strip() for x in m[2].split(','))+'}',body)
 target=ROOT/'tex/partes'/f'{doc}.tex';target.write_text('% Reconstruído de '+rel+'\n'+body+'\n')
 # Save derived line positions and immutable source positions side by side.
 for row in [r for r in D['enunciados'] if r['documento']==doc]:
  rr=dict(row);rr['parte_volume']=roman;rr['numero_volume']=roman+'.'+row['numero'];rr['originais_77']=originals.get(row['id'],[]);rr['rotulo_volume']='map:'+row['id'];rr['tex_volume']='tex/partes/'+doc+'.tex'
  rr['linha_volume']=next(i for i,l in enumerate(target.read_text().splitlines(),1) if '\\label{map:'+row['id']+'}' in l)
  allrows.append(rr)
# Shared preamble: keep all mathematical macros, one theorem counter per section.
preamble=(B/'artigos/artigo_1/artigo.tex').read_text().split('\\title{')[0]
preamble=preamble.replace('\\usepackage{microtype,graphicx,xcolor,booktabs,longtable,array,float}','\\usepackage{microtype,graphicx,xcolor,booktabs,longtable,array,float,tabularx,multicol,placeins,mathrsfs,xurl}')
preamble=preamble.replace('\\usepackage{hyperref}','\\usepackage{hyperref}\n\\usepackage[nameinlink,noabbrev]{cleveref}')
# add non-conflicting macros from the other native preambles
known=set(re.findall(r'\\(?:newcommand|renewcommand)\{(\\\w+)\}',preamble))
extra=[]
for doc,roman,title,rel in parts[1:]:
 pre=(B/rel).read_text().split('\\begin{document}')[0]
 for line in pre.splitlines():
  m=re.match(r'\\newcommand\{(\\\w+)\}',line)
  if m and m[1] not in known:extra.append(line);known.add(m[1])
 for line in pre.splitlines():
  if line.startswith('\\crefname') or line.startswith('\\Crefname'):extra.append(line)
extra += ['\\DeclareMathOperator*{\\argmin}{arg\\,min}']
for en,pt in [('theorem','Teorema'),('lemma','Lema'),('proposition','Proposição'),('corollary','Corolário'),('definition','Definição'),('algorithm','Algoritmo'),('remark','Observação')]:
 extra.append(('\\theoremstyle{definition}\n' if en in ['definition','remark'] else '\\theoremstyle{preciso}\n')+'\\newtheorem{'+en+'}[teorema]{'+pt+'}')
preamble+='\n'+'\n'.join(dict.fromkeys(extra))+'\n'
# Portable pdfLaTeX fonts preserve vector mathematical glyphs.
preamble=re.sub(r'\\usepackage\{fontspec\}.*?\\setmonofont\{[^}]+\}',r'\\usepackage[T1]{fontenc}\n\\usepackage[utf8]{inputenc}\n\\usepackage{lmodern,amssymb}',preamble,flags=re.S)
preamble=re.sub(r'\\usepackage\{unicode-math\}\s*\\setmathfont\{[^}]+\}\s*\\AtBeginDocument\{[^\n]+', '', preamble)
preamble+=r'''
\renewcommand{\partname}{Parte}
\renewcommand{\contentsname}{Sumário}
\renewcommand{\refname}{Referências}
\renewcommand{\thesection}{\Roman{part}.\arabic{section}}
\renewcommand{\thefigure}{\Roman{part}.\arabic{figure}}
\renewcommand{\thetable}{\Roman{part}.\arabic{table}}
\renewcommand{\theequation}{\Roman{part}.\arabic{equation}}
\renewcommand{\theHsection}{\arabic{part}.\arabic{section}}
\renewcommand{\theHfigure}{\arabic{part}.\arabic{figure}}
\renewcommand{\theHtable}{\arabic{part}.\arabic{table}}
\renewcommand{\theHequation}{\arabic{part}.\arabic{equation}}
\newcommand{\volumeparte}[1]{\clearpage\part{#1}\setcounter{section}{0}\setcounter{figure}{0}\setcounter{table}{0}\setcounter{equation}{0}\renewcommand{\thesection}{\Roman{part}.\arabic{section}}}
\makeatletter
\renewcommand*{\l@section}{\@dottedtocline{1}{1.5em}{4em}}
\renewcommand*{\l@subsection}{\@dottedtocline{2}{4em}{5em}}
\renewcommand*{\l@subsubsection}{\@dottedtocline{3}{8em}{6em}}
\makeatother
\fancyhead[L]{\small\itshape Biblioteca determinística: volume unificado}
\hypersetup{pdftitle={Biblioteca determinística: volume unificado e correspondência Lean 4},pdfauthor={Victor Gabriel de Oliveira}}
\title{\bfseries Biblioteca determinística de segmentos afins racionais\\[8pt]\Large Construção, seleção, aproximação e normalização\\[8pt]\large Volume unificado com correspondência Lean 4}
\author{Victor Gabriel de Oliveira}
\date{Edição consolidada de 7 de novembro de 2026}
\begin{document}
\maketitle
\begin{abstract}
Este volume reúne a construção da biblioteca racional em células diádicas, a normalização das montagens, os custos aritméticos e a seleção exata, a teoria direta--inversa e os complementos do manuscrito de 77 páginas. Os enunciados e as demonstrações disponíveis são preservados em cinco partes. A correspondência final relaciona os 151 ambientes da edição atual aos fontes Lean existentes e aos 108 ambientes do manuscrito original. As diferenças semânticas e os resultados ainda sem formalização localizada permanecem identificados.
\end{abstract}
\section*{Convenções desta edição}
A numeração tem a forma parte.seção.resultado. As remissões numéricas textuais herdadas dos artigos usam a numeração local da própria parte, salvo indicação explícita de outro artigo. A Parte I corresponde ao Artigo 1; a Parte II contém a normalização auxiliar; as Partes III e IV correspondem aos Artigos 2 e 3; a Parte V conserva os complementos das seções 6 e 21 originais. A correspondência documental reúne os destinos do original sem duplicar seu bloco de custo aritmético.

Os fontes Lean recebidos permanecem inalterados. As evidências de compilação incluídas são históricas, de outubro de 2026. Esta edição verificou a composição LaTeX e as ligações de arquivos; não executou novamente o compilador Lean. A pasta \texttt{Fase3} é uma fase da base do Artigo 1. A formalização integral do Artigo 3 permanece pendente.
\tableofcontents
'''
master=preamble
for doc,roman,title,rel in parts:master+='\n% '+roman+' | fonte original: '+rel+'\n\\volumeparte{'+title+'}\n\\input{partes/'+doc+'}\n'
master+='\n\\clearpage\\part*{Correspondência documental e formal}\\addcontentsline{toc}{part}{Correspondência documental e formal}\n\\input{mapa_formal}\n\\clearpage\\bibliographystyle{plainnat}\n\\bibliography{referencias}\n\\end{document}\n'
(ROOT/'tex/principal.tex').write_text(master)
# Bibliographic namespaces preserve each article's existing references exactly.
bib=''
for doc,roman,title,rel in parts:
 bp=(B/rel).parent/'referencias.bib'
 if bp.exists():bib+=re.sub(r'(@\w+\s*\{)([^,]+)',lambda m:m[1]+doc+'-'+m[2],bp.read_text())+'\n'
# Merge repeated bibliography records by normalized title, retaining first record.
entries=re.split(r'(?=@\w+\s*\{)',bib)
seen={};aliases={};unique=[]
for entry in entries:
 m=re.match(r'@\w+\s*\{([^,]+),',entry)
 if not m:continue
 key=m[1]
 tm=re.search(r'\btitle\s*=\s*[{\"](.*?)(?:\n\s*\w+\s*=|\n\s*\})',entry,re.I|re.S)
 title=tm[1] if tm else key.split('-',1)[-1]
 title=re.sub(r'[^a-z0-9]','',title.lower())
 if title in seen:aliases[key]=seen[title]
 else:seen[title]=key;unique.append(entry)
for pt in (ROOT/'tex/partes').glob('*.tex'):
 txt=pt.read_text()
 def canon(m):return m[1]+'{'+','.join(dict.fromkeys(aliases.get(k.strip(),k.strip()) for k in m[2].split(',')))+'}'
 txt=re.sub(r'(\\cite\w*\*?(?:\[[^\]]*\]){0,2})\{([^}]+)\}',canon,txt)
 pt.write_text(txt)
# Revisão editorial (itens 1-3): trechos, observações e linhas recalculadas.
import sys;sys.path.insert(0,str(Path(__file__).resolve().parent))
import revisao_editorial as REV
REV.aplicar_trechos(ROOT,['tex/partes/artigo_1.tex','tex/partes/artigo_2.tex','tex/partes/artigo_3.tex','tex/principal.tex'])
REV.aplicar_observacoes(allrows);REV.recalcular_linhas(ROOT,allrows)
# Provas Lean que fecharam lacunas (biblioteca Pendencias): reaplica estado e declarações.
import formalizacoes_pendencias as FP
FP.aplicar_linhas(allrows)
(ROOT/'tex/referencias.bib').write_text('\n'.join(unique))
(ROOT/'mapas/bibliografia_aliases.json').write_text(json.dumps(aliases,ensure_ascii=False,indent=2))
# Readable and machine-readable maps, one folder per mathematical part.
statusnames={'correspondencia_inspecionada':'Correspondência inspecionada','integrado_a_v2':'Integrado à base','nao_formalizado_no_acervo':'Não formalizado no acervo','observacao_editorial':'Observação editorial','ponte_regularidade_pendente':'Ponte de regularidade pendente','sem_formalizacao_localizada':'Sem formalização localizada','cobertura_parcial':'Cobertura parcial','implementacao_pendente':'Implementação pendente','contrato_abstrato':'Contrato abstrato','divergencia_documentada':'Divergência documentada','generalizacao_documentada':'Generalização documentada','prova_textual_a_sincronizar':'Prova textual a sincronizar','corolario_a_transportar':'Corolário a transportar','formalizado_compilado':'Formalizado e compilado','prova_textual_sincronizada':'Prova textual sincronizada'}
def leanpath(r):
 pkg=r['pacote'];path=r['arquivo_lean']
 if pkg=='base_v2':return 'lean4/ambientes/base_integrada/'+path
 if pkg=='parte_1':return 'lean4/ambientes/parte_1/'+('RequestProject/'+Path(path).name if 'RequestProject' in path else path)
 return 'lean4/ambientes/artigo_2/'+('RequestProject/'+Path(path).name if 'RequestProject' in path else path)
for row in allrows:
 for result in row['resultados_lean']:
  result['caminho_entrega']=leanpath(result)
  if not (ROOT/result['caminho_entrega']).exists():raise RuntimeError(result)
(ROOT/'mapas/correspondencia_completa.json').write_text(json.dumps(allrows,ensure_ascii=False,indent=2))
(ROOT/'mapas/figuras.json').write_text(json.dumps(figures,ensure_ascii=False,indent=2))
with (ROOT/'mapas/correspondencia_completa.csv').open('w') as f:
 w=csv.writer(f);w.writerow(['id','numero_volume','original_77','tex','linha_tex','rotulo','estado','ressalva','lean'])
 for r in allrows:w.writerow([r['id'],r['numero_volume'],','.join(r['originais_77']),r['tex_volume'],r['linha_volume'],r['rotulo_volume'],r['status'],r['observacao'],'; '.join(x['nome']+' @ '+x['caminho_entrega']+':'+str(x['linha_lean']) for x in r['resultados_lean'])])
md='# Correspondência do volume com Lean 4\n\nAs ligações abaixo são derivadas da matriz recebida, com caminhos locais conferidos. A compilação histórica não é uma nova validação semântica.\n\n'
for doc,roman,title,rel in parts:
 rows=[r for r in allrows if r['documento']==doc];folder=ROOT/'lean4/por_parte'/doc;folder.mkdir(exist_ok=True)
 text=f'# Parte {roman} — {title}\n\nOs módulos executáveis ficam em `../../ambientes/`. Este diretório contém o índice da parte, sem mover os módulos e quebrar imports.\n\n'
 for r in rows:
  text+='## '+r['numero_volume']+' — '+r['tipo']+' '+r['titulo']+'\n\n'
  text+='Original de 77 páginas: '+(', '.join(r['originais_77']) or 'sem correspondência direta; desenvolvimento da edição atual')+'.\n\n'
  text+='Fonte editável: ['+r['tex_volume']+':'+str(r['linha_volume'])+'](../../../'+r['tex_volume']+'); rótulo `'+r['rotulo_volume']+'`.\n\n'
  text+='Estado: **'+statusnames[r['status']]+'**. '+r['observacao']+'\n\n'
  for v in r['resultados_lean']:text+='- [`'+v['nome']+'`](../../../'+v['caminho_entrega']+') — linha '+str(v['linha_lean'])+'.\n'
  if not r['resultados_lean']:text+='Nenhuma declaração Lean associada na matriz recebida.\n'
  text+='\n'
 (folder/'README.md').write_text(text)
 (folder/'mapa.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2))
 md+='## Parte '+roman+'\n\n'+text.split('\n\n',2)[2]+'\n'
(ROOT/'mapas/MAPA_TEX_LEAN.md').write_text(md.replace('](../../../','](../'))
# Original-to-volume table, including every original numbered environment.
origmd='# Destino dos 108 ambientes do original de 77 páginas\n\n| Original | Destino no volume | Estado |\n|---|---|---|\n'
for r in C['enunciados']:
 ds=[];ss=[]
 for x in r['destinos']:
  rr=next((y for y in allrows if y['id']==x['id']),None)
  if rr:ds.append(rr['numero_volume']);ss.append(statusnames[rr['status']])
 origmd+='| '+r['original']['numero']+' | '+', '.join(ds)+' | '+'; '.join(dict.fromkeys(ss))+' |\n'
(ROOT/'mapas/ORIGINAL_77_PARA_VOLUME.md').write_text(origmd)
# A compact correspondence apparatus inside the PDF, with per-result page links.
def esc(s):
 return s.replace('\\',r'\textbackslash{}').replace('_',r'\_').replace('&',r'\&').replace('%',r'\%').replace('#',r'\#')
maptex=r'''\section*{Estado da correspondência}
As categorias abaixo reproduzem a matriz recebida. Correspondência inspecionada identifica declarações relevantes; integração à base exige as pontes documentadas. Contratos abstratos, cobertura parcial e pendências conservam seu alcance. Os diretórios \texttt{lean4/por\_parte/} e \texttt{mapas/} contêm os nomes Lean, os caminhos e as posições de cada resultado.

As principais pendências são: sincronização textual de $g(t_0)$ no resultado I.4.3; ligação executável do refinamento I.6.3--I.6.4; pontes de regularidade $C^2$, árvores em raiz única e execução das recorrências no Artigo 2; formalização integral do Artigo 3 e dos quatro resultados complementares. A Parte II registra a construção normalizada da extensão, sem substituir silenciosamente o enunciado antigo da Parte I.
'''
for doc,roman,title,rel in parts:
 maptex+='\n\\subsection*{Parte '+roman+'}\n\\small\n\\begin{longtable}{@{}p{.13\\linewidth}p{.12\\linewidth}p{.23\\linewidth}p{.42\\linewidth}@{}}\n\\toprule Resultado & Original & Página & Estado e ressalva\\\\\\midrule\\endhead\n'
 for r in [x for x in allrows if x['documento']==doc]:
  note=statusnames[r['status']]+('. '+r['observacao'] if r['observacao'] else '')
  maptex+='\\hyperref['+r['rotulo_volume']+']{'+r['numero_volume']+'} & '+(', '.join(r['originais_77']) or '--')+' & \\pageref{'+r['rotulo_volume']+'} & '+(FP.nota_tex(r,esc) or esc(note).replace('^',r'\textasciicircum{}'))+'\\\\[4pt]\n'
 maptex+='\\bottomrule\\end{longtable}\\normalsize\n'
(ROOT/'tex/mapa_formal.tex').write_text(maptex)
REV.aplicar_trechos(ROOT,['tex/mapa_formal.tex'])
FP.nota_mapa_tex();FP.restaurar_lakefile()
print('Reconstructed',len(allrows),'environments;',len(figures),'figure uses')
