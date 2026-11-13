# Parte V — Complementos do manuscrito original

Os módulos executáveis ficam em `../../ambientes/`. Este diretório contém o índice da parte, sem mover os módulos e quebrar imports.

## V.6.1 — teorema taxa garantida em árvores

Original de 77 páginas: 6.1.

Fonte editável: [tex/partes/complemento_original.tex:27](../../../tex/partes/complemento_original.tex); rótulo `map:complemento_original:6.1`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondencia editorial nao afirma prova Lean. [11/11/2026] σ_N^dia = `Edia`; f ∈ C²(K) via `ContDiffOn`; taxas M L²/(8N²) (N = 2^r) e M L²/(2N²); montagem racional na mesma árvore (qualquer `DShape`) com erro < ‖f − P_Λ f‖ + δ. Compilado com Lean/Mathlib 4.28.0; `#print axioms`: só `propext`, `Classical.choice`, `Quot.sound`.

- [`Pendencias.tree_rate_pow`](../../../lean4/ambientes/artigo_2/Pendencias/Arvores.lean) — linha 54.
- [`Pendencias.tree_rate`](../../../lean4/ambientes/artigo_2/Pendencias/Arvores.lean) — linha 62.
- [`Pendencias.tree_rationalization`](../../../lean4/ambientes/artigo_2/Pendencias/Arvores.lean) — linha 255.

## V.6.2 — teorema cota assintótica com nós livres

Original de 77 páginas: 6.2.

Fonte editável: [tex/partes/complemento_original.tex:57](../../../tex/partes/complemento_original.tex); rótulo `map:complemento_original:6.2`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondencia editorial nao afirma prova Lean. [13/11/2026] Cota assintotica com nos livres e derivadas unilaterais para funcoes C2 no intervalo fechado. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.NosLivres.free_knots`](../../../lean4/ambientes/artigo_2/Pendencias/NosLivres.lean) — linha 123.

## V.6.3 — teorema estimativa direta

Original de 77 páginas: 6.3.

Fonte editável: [tex/partes/complemento_original.tex:109](../../../tex/partes/complemento_original.tex); rótulo `map:complemento_original:6.3`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondencia editorial nao afirma prova Lean. [13/11/2026] Estimativa direta em raiz diadica geral, constante de Whitney explicita e montagem racional com erro adicional arbitrario. Compilado com Lean/Mathlib 4.28.0; axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Jackson.besov_direct`](../../../lean4/ambientes/artigo_2/Pendencias/BesovDireta.lean) — linha 129.
- [`Pendencias.Jackson.besov_direct_whitney`](../../../lean4/ambientes/artigo_2/Pendencias/BesovDireta.lean) — linha 109.

## V.21.1 — lema majorante local da função de Runge

Original de 77 páginas: 21.1.

Fonte editável: [tex/partes/complemento_original.tex:152](../../../tex/partes/complemento_original.tex); rótulo `map:complemento_original:21.1`.

Estado: **Formalizado e compilado**. Resultado original integralmente preservado no complemento; a correspondencia editorial nao afirma prova Lean. [11/11/2026] Provado; a forma `runge_majorant` dispensa J ⊆ [-1,1]. Inclui `deriv2_runge`. Compilado com Lean/Mathlib 4.28.0 (lake build Pendencias); axiomas: propext, Classical.choice, Quot.sound.

- [`Pendencias.Runge.runge_majorant_sub`](../../../lean4/ambientes/artigo_2/Pendencias/Runge.lean) — linha 118.
- [`Pendencias.Runge.runge_majorant`](../../../lean4/ambientes/artigo_2/Pendencias/Runge.lean) — linha 84.


## Cópias para leitura

`fontes_referenciados/` reúne cópias byte a byte dos módulos associados. Para compilar, use os ambientes completos em `../../ambientes/`, que preservam imports e dependências.
