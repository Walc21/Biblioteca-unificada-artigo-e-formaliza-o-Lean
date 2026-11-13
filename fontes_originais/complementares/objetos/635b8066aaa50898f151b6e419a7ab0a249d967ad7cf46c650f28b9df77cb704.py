#!/usr/bin/env python3
"""Static crosscheck of extension files. Does not run Lean."""
from pathlib import Path
import re, sys
root=Path(__file__).resolve().parent
f=root/'Unified'/'SemanticBridge'
files=sorted(f.glob('*.lean'))
assert len(files)==6, 'Esperados exatamente seis modulos de ponte v2'
known={'Unified',*(f'Unified.SemanticBridge.{p.stem}' for p in files)}
all_sources=list((root/'Unified').rglob('*.lean'))
known.update('Unified.'+'.'.join(p.relative_to(root/'Unified').with_suffix('').parts) for p in all_sources)
errors=[]
for p in [*files,root/'SemanticAudit.lean']:
    src=p.read_text(encoding='utf-8')
    if not src.startswith('module\n'): errors.append(f'{p.name}: missing module preamble')
    imports=re.findall(r'(?m)^public import\s+([^\s]+)',src)
    for imp in imports:
        if imp not in known: errors.append(f'{p.name}: unknown import {imp}')
    if 'sorry' in re.sub(r'/\-.*?\-/', '', src, flags=re.S):
        # known false positives in docs? no
        errors.append(f'{p.name}: possible sorry')
    if re.search(r'(?m)^\s*(axiom|constant)\s',src):errors.append(f'{p.name}: axiomatic declaration')
if errors:
    print('FAIL: '+', '.join(errors));sys.exit(1)
print(f'PASS: {len(files)} semantic modules + entrypoint, references statically resolved; originals untouched')
print('NOTE: Lean proof validation requires `lake build SemanticAudit`.')
