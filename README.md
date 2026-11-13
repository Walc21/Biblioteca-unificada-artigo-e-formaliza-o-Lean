# Biblioteca unificada — artigo e formalização em Lean 4

Artigo (PDF + LaTeX) com **151 ambientes matemáticos** e a formalização em
Lean 4.28.0 / Mathlib 4.28.0. Estado: **38 dos 42 casos do dossiê original tratados**
(37 provas Lean + 1 prova textual); abertos: III.9.1, III.9.3, IV.5.5 e IV.5.6.
IV.5.4 foi fechado com o enunciado inverso corrigido (a cota impressa original era falsa).

| O quê | Onde |
|---|---|
| PDF final (122 páginas) | `Biblioteca_Unificada.pdf` (= `tex/principal.pdf`) |
| LaTeX | `tex/principal.tex`, `tex/partes/` |
| Provas Lean | `lean4/ambientes/{artigo_2,base_integrada,parte_1}` |
| Mapa resultado TeX → Lean | `mapas/MAPA_TEX_LEAN.md` |
| Estado e log | `STATUS_AUTOMATICO.md`, `LOG_TRABALHO.md`, `LEIA_PRIMEIRO.md` |

## Reproduzir

```bash
# em cada ambiente de lean4/ambientes/*, baixe o cache do Mathlib:
lake exe cache get
# gate completo (lento):
./compilar_pendencias/compilar_tudo.sh --axiomas
# PDF:
cd tex && latexmk -pdf -interaction=nonstopmode -halt-on-error principal.tex
```

Os caches `.lake` (~22 GB) não são versionados. Detalhes: `LEIA_PRIMEIRO.md`.
