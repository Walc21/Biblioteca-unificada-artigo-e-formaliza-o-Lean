from pathlib import Path, PurePosixPath
import json, hashlib, argparse
p=argparse.ArgumentParser(description="Restaura as arvores de fontes, inclusive membros dos pacotes, em pasta nova.")
p.add_argument("destino",type=Path);a=p.parse_args();a.destino.mkdir(parents=True,exist_ok=False)
r=Path(__file__).resolve().parent
for x in json.loads((r/"CATALOGO.json").read_text())["arquivos"]:
    parts=x["origem"].split("!/")
    name="/".join([s+"_conteudo" for s in parts[:-1]]+[parts[-1]])
    q=PurePosixPath(name)
    if q.is_absolute() or ".." in q.parts:raise ValueError(name)
    b=(r/x["destino"]).read_bytes()
    if hashlib.sha256(b).hexdigest()!=x["sha256"]:raise ValueError(name)
    t=a.destino/str(q);t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b);t.chmod(x["modo"])
print("Fontes restaurados; os conteineres antigos foram substituidos por seu conteudo integral.")
