#!/usr/bin/env python3
"""Executa os cinco verificadores recebidos em saídas isoladas. Não é uma prova Lean."""
from pathlib import Path
import subprocess,sys,json,time,os
from concurrent.futures import ThreadPoolExecutor
R=Path(__file__).resolve().parents[1]
source=R/'fontes_originais/FORMALIZACAO_COMPLETA_DA_BIBLIOTECA/artigos/reproducibility/selecao'
names=['seletor_dinamico_exato','constante_diadica','espacos_aproximacao','restricoes_rede','reversibilidade_regularizada']
def run(name):
 out=R/'verificacao/numerica'/name
 for n in ['reproducibility/selecao/figures/pt','reproducibility/selecao/figures/en','artigo/secoes']:(out/n).mkdir(parents=True,exist_ok=True)
 env=dict(os.environ,MPLBACKEND='Agg',MPLCONFIGDIR=str(out/'matplotlib_cache'))
 t=time.monotonic()
 p=subprocess.run([sys.executable,str(source/(name+'.py')),'--output-root',str(out)],env=env,capture_output=True,text=True)
 (out/'execucao.log').write_text(p.stdout+'\n'+p.stderr)
 return {'verificador':name,'exit_code':p.returncode,'segundos':round(time.monotonic()-t,3),'log':str((out/'execucao.log').relative_to(R))}
with ThreadPoolExecutor(max_workers=5) as pool:results=list(pool.map(run,names))
(R/'verificacao/numerica/resultados.json').write_text(json.dumps(results,ensure_ascii=False,indent=2))
print(json.dumps(results,ensure_ascii=False,indent=2))
if any(x['exit_code'] for x in results):raise SystemExit(1)
