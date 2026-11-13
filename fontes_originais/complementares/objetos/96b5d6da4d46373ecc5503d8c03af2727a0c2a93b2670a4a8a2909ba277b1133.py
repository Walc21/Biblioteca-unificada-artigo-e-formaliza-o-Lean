#!/usr/bin/env python3
"""Static integrity and scope check; does NOT replace Lean's kernel."""
from pathlib import Path
import csv
import hashlib
import re

root = Path(__file__).resolve().parent
orig = root / 'Unified'
all_lean = list(orig.rglob('*.lean'))
with (root / 'PROVENIENCIA.csv').open(newline='', encoding='utf-8') as stream:
    provenance = list(csv.DictReader(stream))
assert len(provenance) == 41
assert len(all_lean) >= 47, (len(all_lean), 'expected 41 originals + 6 bridges')
assert (root / 'SemanticAudit.lean').is_file()
assert (root / 'AuditoriaAxiomasPontes.lean').is_file()
assert (root / 'lakefile.toml').read_text().count('name = "SemanticAudit"') == 1
for p in all_lean:
    source = p.read_text()
    # Simple omissions check; limited to new modules, comments removed.
    if p.parent.name == 'SemanticBridge':
        active = re.sub(r'/\-.*?-/', '', source, flags=re.S)
        active = re.sub(r'--[^\n]*', '', active)
        assert not re.search(r'\b(sorry|admit|axiom)\b', active), p
for row in provenance:
    target = root / row['arquivo_integrado']
    assert target.is_file() and hashlib.sha256(target.read_bytes()).hexdigest() == row['sha256_integrado'], f'changed baseline file {target}'
modules = {p.relative_to(root).with_suffix('').as_posix().replace('/', '.') for p in all_lean}
modules.update({'SemanticAudit', 'Unified'})
for p in [*all_lean, root / 'SemanticAudit.lean']:
    for name in re.findall(r'(?:public\s+)?import\s+([A-Za-z0-9_.]+)', p.read_text()):
        assert name in modules or name in {'Lean', 'Mathlib'}, (p,name)
print(f'PASS: {len(all_lean)} Lean modules ({len(provenance)} baseline unchanged), all local imports found, no sorry/admit/axiom in bridges.')
print('WARNING: static check only; kernel validation and axiom audit run on the user Lean installation.')
