#!/usr/bin/env python3
"""Verifica integridade, cobertura do catálogo e recorte editorial, sem dependências externas."""
from pathlib import Path, PurePosixPath
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def checked_path(name):
    p = PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts:
        raise ValueError(f'Caminho inválido: {name}')
    return ROOT / str(p)

manifest = json.loads((ROOT / 'MANIFESTO_SHA256.json').read_text())
for name, expected in manifest.items():
    p = checked_path(name)
    if p.is_symlink() or not p.is_file() or sha(p) != expected:
        raise ValueError(f'Integridade divergente: {name}')
actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()}
if actual != set(manifest) | {'MANIFESTO_SHA256.json'}:
    raise ValueError('Arquivos extras ou ausentes em relação ao manifesto.')
catalog = json.loads((ROOT / 'CATALOGO.json').read_text())
for row in catalog['arquivos']:
    p = checked_path(row['destino'])
    if p.stat().st_size != row['bytes'] or sha(p) != row['sha256']:
        raise ValueError(f'Conteúdo original divergente: {row["origem"]}')
base = ROOT / 'FORMALIZACAO_COMPLETA_DA_BIBLIOTECA'
current = json.loads((base / 'documentacao/enunciados.json').read_text())
original = json.loads((base / 'documentacao/conferencia_original_77.json').read_text())
assert len(current['enunciados']) == 151
assert len(original['enunciados']) == 108
assert len(list((base / 'Unified').rglob('*.lean'))) == 53
for package, count in [('parte_1', 9), ('artigo_2', 31)]:
    received = base / 'entradas' / package / 'RequestProject'
    isolated = base / 'validacao' / package / 'RequestProject'
    assert len(list(received.glob('*.lean'))) == count
    for p in received.glob('*.lean'):
        assert sha(p) == sha(isolated / p.name)
print(f'OK: {len(manifest)} arquivos da entrega; {len(catalog["arquivos"])} origens cobertas; 151 ambientes atuais e 108 originais; 53 módulos da base e pacotes 9/31 íntegros.')
