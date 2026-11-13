# Summary of changes for run 2251b7de-38f4-48c0-927a-83cc582a3683
Formalizei em Lean 4 o documento "Equivalência das montagens locais e consolidadas" (Seções 1–8 e os predicados auxiliares do Apêndice A). O projeto compila, não há nenhum `sorry`, e os teoremas principais dependem apenas dos axiomas padrão (`propext`, `Classical.choice`, `Quot.sound`). As construções seguem o texto ao pé da letra: \(T\), \(\pi\), \(w\) definido como máximo de um filtro, \(Z\) e \(Z^{-1}\), \(\mathcal Q_H\), a ordem lexicográfica \((\mathrm{ht}, q, p)\), a chave \(\kappa\), os postos dados por cardinalidade dos predecessores, `enc`/`dec`, \(T_i\), \(I\), \(\sigma_\Lambda\), \(e_{i,\Lambda}\), \(p_K\), \(E_0\), `sort` por recursão bem fundada na cardinalidade, `NormChain` e \(F_r\) por recursão em \(r<M\).

**Arquivos, em `RequestProject/`:**
- `Basic.lean`: domínio \(K\), altura, células, átomos, `lem:geometry` e `lem:line`.
- `Normalization.lean`: os contratos (`Sep`, `Cover`, `Match`, `Agree`, `LocalRep`, `StrongRep` e versões globais), `Active`, `NormK` (\(\mathrm{Norm}_K\)), `lem:active`, `lem:separated`, `thm:norm` (versões em \(C_K\) e global) e `cor:classes`.
- `Enumeration.lean`: `lem:pair` (inclusive a fórmula com `Nat.sqrt`), as identidades de \(Z\), a caracterização de \(\mathcal Q_H\), `lem:rank` (as três ordens coincidem; `rank_i` e `rank*_i` são bijetivas), \(Q_i\), \(Q^*_i\) e `lem:codec` com as propriedades de \(\tau_{i\to j}\).
- `Bridge.lean`: `CellRep`, `ContOn`, `Res`, `ResImage`, as classes \(\mathcal B_2, \mathcal B_3, \mathcal B_{\rm con}\), `lem:witnesses` (cardinalidade, \(T_i(I(\Lambda), e)=\Lambda\), \(I(T_i(F,e))=F\)), a extensão \(E_0\) e `thm:bridge`.
- `Error.lean`: orçamentos, `thm:budget`, \(d_K\) (o máximo é atingido e vale \(\|f-g\|\)), `Err` em `ENNReal`, o corolário dos erros e das alturas, e `prop:fixed`.
- `Chain.lean`: a ordem \(\zeta\), `sort`, `lem:sort`, `NormChain` e a cadeia construída de `thm:chain` (`chainOf`), com nós diádicos.
- `ReLU.lean`: \(F_r\), \(R(q)\), `lem:sum` (fórmulas `eq:relu_sum` e `eq:relu_anchor`, e o caso \(M=1\)), `lem:incident`, `thm:extension`, `lem:two_points`, `thm:unique` e o operador \(\mathcal E_K\), que independe das escolhas e satisfaz \(\mathrm{Res}_K(\mathcal E_K(g))=g\).
- `Appendix.lean`: `InnerAgree`, `IntersectionsInside` e as implicações enunciadas no apêndice.

**Observações:**
- O Apêndice A pede a identificação com um pacote Lean externo (`Biblioteca_Lean_Equivalencias_v2_COMPLETO.zip`), que não foi enviado. Essas identidades de adaptador não foram feitas; formalizei apenas as definições e implicações matemáticas do apêndice. O enunciado global final corresponde a `B3_eq_Bcon`.
- No `thm:budget`, a hipótese \(H \ge 2\) do documento não é usada na prova, então o enunciado formal vale para todo \(H\).
- O conjunto de alturas admissíveis no corolário dos erros é formalizado sem a hipótese \(\varepsilon \ge 0\), que também não é necessária.
- Alguns nomes diferem do texto para evitar conflitos com a Mathlib: `NormK` para \(\mathrm{Norm}_K\), `Rext` para \(R(q)\) e `extOp` para \(\mathcal E_K\).

Os resultados principais estão registrados na tabela de propriedades como provados.