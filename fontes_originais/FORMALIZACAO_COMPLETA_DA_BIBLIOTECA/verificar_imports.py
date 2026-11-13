#!/usr/bin/env python3
"""Static import graph checker; does not replace `lake build`."""
from pathlib import Path
import csv, re, sys, hashlib
root=Path(__file__).resolve().parent
with (root/'PROVENIENCIA.csv').open(encoding='utf-8') as f:rows=list(csv.DictReader(f))
modset={r['modulo_integrado'] for r in rows}
graph={}
fail=[]
for r in rows:
  file=root/r['arquivo_integrado'];content=file.read_text(encoding='utf-8')
  digest=hashlib.sha256(content.encode('utf-8')).hexdigest()
  if digest != r['sha256_integrado']:fail.append((str(file),['SHA-256 divergente']))
  imports=re.findall(r'(?m)^\s*(?:public )?import\s+(\S+)',content)
  bad=[i for i in imports if i not in modset and not i.startswith('Mathlib')]
  if bad:fail.append((str(file),bad))
  graph[r['modulo_integrado']]=[i for i in imports if i in modset]
visiting=set();visited=set()
def dfs(m):
  if m in visiting:raise RuntimeError('Circular imports: '+m)
  if m in visited:return
  visiting.add(m)
  for n in graph[m]:dfs(n)
  visiting.remove(m);visited.add(m)
for m in graph:dfs(m)
# Aggregator: Lean requires imports before any documentation/declaration command.
aggregator = (root/'Unified.lean').read_text(encoding='utf-8')
all_imports = list(re.finditer(r'(?m)^(?:public )?import\s+\S+\s*$', aggregator))
if not all_imports:
  fail.append(('Unified.lean', ['no imports in aggregator']))
else:
  prefix = aggregator[:all_imports[0].start()]
  if not re.fullmatch(r'\s*module\s*', prefix):
    fail.append(('Unified.lean', ['documentation/declaration before imports']))
  between = aggregator[all_imports[0].start():all_imports[-1].end()]
  if re.sub(r'(?m)^(?:public )?import\s+\S+\s*$', '', between).strip():
    fail.append(('Unified.lean', ['non-import command between imports']))
if fail:
 for f,items in fail:print(f,'imports unresolved:',items)
 sys.exit(1)
print(f'PASS: {len(rows)} source modules, SHA-256 verified, all imports resolved, no import cycles')
print('NOTE: this is a static check; it does not validate the Lean kernel or compile proofs.')
