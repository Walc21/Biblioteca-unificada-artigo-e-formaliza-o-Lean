from pathlib import Path
import runpy, sys
import matplotlib
matplotlib.use("Agg")
matplotlib.rcParams["pdf.fonttype"] = 42
root = Path(__file__).resolve().parent
dest = root / "gerado"
for name in ["seletor_dinamico_exato.py", "constante_diadica.py", "espacos_aproximacao.py", "restricoes_rede.py", "reversibilidade_regularizada.py"]:
    sys.argv = [name, "--output-root", str(dest)]
    runpy.run_path(str(root / "reproducibility" / "selecao" / name), run_name="__main__")
