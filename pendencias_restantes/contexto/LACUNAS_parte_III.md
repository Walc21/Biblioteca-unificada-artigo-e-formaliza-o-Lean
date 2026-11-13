# Lacunas de prova em Lean: Parte III (artigo_2)

15 caso(s) cujo enunciado do volume não está integralmente provado por uma declaração Lean existente. Marque `[x]` quando o caso for fechado e atualize o `status` em `mapas/correspondencia_completa.json`.

## [x] III.2.3. proposicao — densidade, interpolação e forma ReLU

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 54, rótulo `map:artigo_2:2.3`; PDF unificado, p. 37.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** Ponte de regularidade (abaixo); `Fase3.errP_le`.

**Enunciado no volume (TeX):**

```latex
\begin{proposition}[densidade, interpolação e forma ReLU]
As montagens são densas em $C(K)$. Se $P_Jf$ interpola $f$ nos extremos de $J$ e $f\in C^2(J)$, então
\begin{equation}
 \|f-P_Jf\|_{\infty,J}\le\frac{|J|^2}{8}\|f''\|_{\infty,J}.
 
\end{equation}
Para uma montagem com nós $t_0<\cdots<t_N$ e inclinações $s_j$, vale, com $\rho(z)=\max\{0,z\}$,
\begin{equation}
 g(x)=g(t_0)+s_0(x-t_0)+\sum_{j=1}^{N-1}(s_j-s_{j-1})\rho(x-t_j).
 
\end{equation}
\end{proposition}
```

**Declarações Lean associadas (assinatura):**

`Artigo.assemblies_dense` — `lean4/ambientes/artigo_2/RequestProject/Uniform.lean`, linha 231

```lean
/-- **Proposition 2.3 (density)**: assemblies are dense in `C(K)` for `K = J_{k₀,m₀}`. -/
theorem assemblies_dense {k₀ : ℕ} {m₀ : ℤ} {f : ℝ → ℝ} (hf : ContinuousOn f (cellIcc k₀ m₀))
    {ε : ℝ} (hε : 0 < ε) : ∃ T : LTree, WF k₀ m₀ T ∧ ∀ x ∈ cellIcc k₀ m₀, |f x - T.eval k₀ m₀ x| < ε
```

`Artigo.interp_remainder_C2` — `lean4/ambientes/artigo_2/RequestProject/Interp.lean`, linha 126

```lean
/-- version for `C²` functions on `ℝ` -/
theorem interp_remainder_C2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ} (hab : a < b)
    (hM : ∀ x ∈ Icc a b, |deriv (deriv f) x| ≤ M) :
    ∀ x ∈ Icc a b, |f x - linInterp f a b x| ≤ (b - a) ^ 2 / 8 * M
```

`Artigo.LTree.eval_relu_form` — `lean4/ambientes/artigo_2/RequestProject/Trees.lean`, linha 392

```lean
/-- **Proposition 2.3 (ReLU form)**: an assembly with knots `t₀ < ⋯ < t_N` and slopes `s_j`
satisfies, on its root cell,
`g(x) = g(t₀) + s₀ (x - t₀) + ∑_{j=1}^{N-1} (s_j - s_{j-1}) ρ(x - t_j)`. -/
theorem eval_relu_form {k : ℕ} {m : ℤ} {T : LTree} (h : WF k m T) :
    ∀ x ∈ cellIcc k m, T.eval k m x =
      T.eval k m (cL k m) + (T.firstLeaf.s : ℝ) * (x - cL k m) + hingeSum T.leaves x
```

**O que difere:** `Artigo.interp_remainder_C2` exige `hf : ContDiff ℝ 2 f` e `hM` sobre `deriv (deriv f)`; o texto pede apenas `f ∈ C²(J)` com `‖f″‖∞,J`. A densidade (`assemblies_dense`, `ContinuousOn`) e a forma ReLU (`eval_relu_form`) batem.

**O que provar:** Provar a cota `|f − linInterp f a b| ≤ (b−a)²/8·M` com `ContDiffOn ℝ 2 f (Icc a b)` e `|derivWithin (derivWithin f (Icc a b)) (Icc a b) x| ≤ M`. A prova existente da Fase 3 (`Fase3.errP_le`) já usa `ContDiffOn`: reaproveitar.


**Fechado em 11/11/2026.** Cota de interpolação provada com `ContDiffOn ℝ 2 f (Icc a b)` e `derivWithin`, via extensão C² portada da Fase 3 (`Pendencias/Extensao.lean`). Densidade e forma ReLU já batiam. Declarações: `Pendencias.interp_remainder_C2On` (`lean4/ambientes/artigo_2/Pendencias/Interpolacao.lean`). Compilado com `lake build Pendencias` em `lean4/ambientes/artigo_2`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound` (`axiomas_pendencias.log`).
---

## [ ] III.3.12. teorema — comparação rigorosa dos formatos

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 436, rótulo `map:artigo_2:3.12`; PDF unificado, p. 43.
- **Categoria P:** Cobertura parcial: o Lean prova algo mais fraco ou diferente do enunciado.
- **Status no mapa:** `cobertura_parcial`.
- **Dependências / ordem:** `Artigo.LTree`, `WF`, `Latom/Lstr/Lrat`, `coding_gap_family` (reaproveitar a estimativa de `Lrat`).

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[comparação rigorosa dos formatos]

Os três fluxos acima são prefix-free e possuem decodificadores exatos. Para
toda montagem com $N$ folhas e altura atômica máxima $H\ge2$,
\begin{equation}
 L_{\rm atom}(g)=O(N\log H),\qquad
 L_{\rm ReLU,str}(g)=O(N\log H),\qquad
 L_{\rm ReLU,rat}(g)=O(NH),
 
\end{equation}
com constantes universais. A última ordem é atingida conjuntamente em $N$ e
$H$: para todo $H\ge2$ e toda potência de dois $N=2^r$ com $2\le N\le H$, seja
$K=J_{H-1-r,0}$ e considere as folhas $J_{H-1,j}$, $0\le j<N$, que são
exatamente as folhas da árvore diádica cheia de profundidade $r$ com raiz $K$.
Tome em cada folha o valor central zero e a inclinação $(-1)^j$.
Essa montagem contínua em $\Aclass(K)$ tem altura $H$, e
\begin{equation}
 L_{\rm atom}=O(N\log H),\qquad
 L_{\rm ReLU,str}=O(N\log H),\qquad
 L_{\rm ReLU,rat}=\Omega(NH).
 
\end{equation}
Assim, a equivalência funcional montagem--ReLU preserva a ordem de bits sob o
formato estrutural fixado, mas não sob a expansão racional ingênua dos
diádicos. Para $N$ qualquer com $2\le N\le H$, a mesma construção com
$N'=2^{\lfloor\log_2N\rfloor}>N/2$ folhas dá uma montagem com no máximo $N$
folhas e $L_{\rm ReLU,rat}=\Omega(N'H)=\Omega(NH)$.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.coding_formats_decoders` — `lean4/ambientes/artigo_2/RequestProject/Formats.lean`, linha 270

```lean
/-- **Theorem 3.8 (exact decoders)**: the three streams are self-delimiting (hence prefix-free)
with exact decoders: `C_atom` recovers the list of leaf atoms, the ReLU streams recover their
parameters. -/
theorem coding_formats_decoders :
    CatomCodec.RT (fun L => L ≠ []) ∧
    (∀ L : List Atom, ∀ t, strCodec.dec (strCodec.enc (strParams L) ++ t) = some (strParams L, t)) ∧
    (∀ L : List Atom, ∀ t, ratReluCodec.dec (ratReluCodec.enc (ratParams L) ++ t) = some (ratParams L, t))
```

`Artigo.coding_format_orders` — `lean4/ambientes/artigo_2/RequestProject/Formats.lean`, linha 421

```lean
/-- **Theorem 3.8 (orders)**: for every assembly with `N` leaves and maximal atomic height
`H ≥ 2`, `L_atom = O(N log H)`, `L_{ReLU,str} = O(N log H)`, `L_{ReLU,rat} = O(N H)`, with
universal constants. -/
theorem coding_format_orders : ∃ C : ℕ, ∀ H : ℕ, 2 ≤ H → ∀ L : List Atom, L ≠ [] →
    (∀ a ∈ L, a.height ≤ H) →
    Latom L ≤ C * L.length * Nat.log 2 H ∧ Lstr L ≤ C * L.length * Nat.log 2 H ∧
    Lrat L ≤ C * L.length * H
```

`Artigo.coding_gap_family` — `lean4/ambientes/artigo_2/RequestProject/Formats.lean`, linha 526

```lean
/-- **Theorem 3.8 (extremal family)**: for `H ≥ 2` and even `N` with `2 ≤ N ≤ H`, the leaves
`J_{H-1,j}`, `0 ≤ j < N`, with central values `0` and slopes `(-1)^j` form a continuous
assembly of height exactly `H`, with `L_atom, L_{ReLU,str} = O(N log H)` and
`L_{ReLU,rat} = Ω(NH)` (explicitly `NH ≤ 2 L_{ReLU,rat}`). -/
theorem coding_gap_family : ∃ C : ℕ, ∀ H N : ℕ, 2 ≤ H → Even N → 2 ≤ N → N ≤ H →
    List.IsChain Contig (famList H N) ∧ (∀ a ∈ famList H N, a.height = H) ∧
    (famList H N).length = N ∧
    Latom (famList H N) ≤ C * N * Nat.log 2 H ∧ Lstr (famList H N) ≤ C * N * Nat.log 2 H ∧
    N * H ≤ 2 * Lrat (famList H N)
```

**O que difere:** O enunciado do volume (corrigido na revisão) usa `N = 2^r`, `K = J_{H−1−r,0}` e as folhas `J_{H−1,j}`, `0 ≤ j < N`, com `L_rat ≥ c·N·H`. `Artigo.coding_gap_family` prova a cota para `N` par com a família `famList H N` e cadeia `Contig`; a montagem em raiz única com `N = 2^r` folhas na altura `H−1` não foi formalizada (a observação do mapa cita que `H = N = 6` produz suporte fora do esperado na família do Lean). `coding_formats_decoders` e `coding_format_orders` (as duas primeiras partes do teorema) batem.

**O que provar:** Provar `coding_gap_pow2`: para `H ≥ 2`, `N = 2^r`, `2 ≤ N ≤ H`, existe uma `LTree` bem-formada com raiz `J_{H−1−r,0}`, exatamente `N` folhas `J_{H−1,j}` de altura atômica `H`, tal que `Latom, Lstr ≤ C·N·log H` e `N·H ≤ 2·Lrat`. Depois, o caso geral `N` qualquer via `N′ = 2^{⌊log₂ N⌋} > N/2` (como no texto).

---

## [x] III.3.15. lema — controle uniforme da primeira derivada

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 578, rótulo `map:artigo_2:3.15`; PDF unificado, p. 44.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** Primeiro da cadeia III.3.15 → 3.16 → 3.17 → 3.18; também IV.4.5.

**Enunciado no volume (TeX):**

```latex
\begin{lemma}[controle uniforme da primeira derivada]

Se $f\in\mathcal F_{R,M}$ e
\begin{equation}
 C_0:=4R+\frac M2,
 
\end{equation}
então $\|f'\|_\infty\le C_0$.
\end{lemma}
```

**Declarações Lean associadas (assinatura):**

`Artigo.derivative_control` — `lean4/ambientes/artigo_2/RequestProject/Interp.lean`, linha 231

```lean
/-- **Lemma 3.9 (controle uniforme da primeira derivada)**: for `f ∈ 𝓕_{R,M}`,
`‖f'‖_∞ ≤ C₀
```

**O que difere:** O Lean usa `FRM R M := {f | ContDiff ℝ 2 f ∧ (∀ x∈Icc 0 1, |f x| ≤ R) ∧ ∀ x∈Icc 0 1, |deriv (deriv f) x| ≤ M}` (Interp.lean), isto é, `f` é C² em toda a reta. O enunciado do volume define 𝓕_{R,M} = {f ∈ C²[0,1] : ‖f‖∞ ≤ R, ‖f″‖∞ ≤ M}. Toda f do Lean está na classe do texto, mas não o contrário: o Lean prova o teorema para uma subclasse.

**O que provar:** Fechar a ponte de regularidade UMA vez e derivar os demais itens dela: (1) definir `FRMIcc R M` com `ContDiffOn ℝ 2 f (Icc 0 1)` e `derivWithin`; (2) provar que toda `f ∈ FRMIcc R M` tem uma extensão `F ∈ FRM R M` com `F = f` em [0,1] (extensão C² da Fase 3, `Fase3.extF`, ou extensão por polinômio de Taylor de ordem 2 nos extremos), preservando `|F| ≤ R` e `|F″| ≤ M` em [0,1]; (3) transportar o enunciado por restrição a [0,1], já que todas as grandezas (erro uniforme, folhas, altura) só olham [0,1].


**Fechado em 11/11/2026.** Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; |f′| ≤ 4R+M/2 com f′ unilateral. Declarações: `Pendencias.derivative_control_Icc`, `Pendencias.FRM_subset_FRMIcc`, `Pendencias.extF_mem_FRM` (`lean4/ambientes/artigo_2/Pendencias/Ponte.lean`). Compilado com `lake build Pendencias`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound`.
---

## [x] III.3.16. teorema — controle simultâneo de erro, folhas, altura e bits

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 600, rótulo `map:artigo_2:3.16`; PDF unificado, p. 44.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** III.3.15 (extensão).

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[controle simultâneo de erro, folhas, altura e bits]

Defina
\begin{equation}
 C_H:=\max\{4(R+1),\ 2(C_0+1)\}.
 
\end{equation}
Para toda potência diádica $n=2^r\ge2$ e todo
$f\in\mathcal F_{R,M}$, existe uma montagem $g_n$ com exatamente $n$
folhas tal que
\begin{align}
 \|f-g_n\|_\infty
 &\le\frac{M+4}{8n^2},
 \\
 \height_{\max}(g_n)&\le C_Hn^2.
 
\end{align}
Nos três formatos do \cref{artigo_2:thm:coding-formats}, a mesma montagem satisfaz
\begin{equation}
 L_{\rm atom}(g_n),\ L_{\rm ReLU,str}(g_n),\
 L_{\rm ReLU,rat}(g_n)=O_{R,M}(n\log(2n)).
 
\end{equation}
Consequentemente, para todo inteiro $N\ge2$,
\begin{equation}
 E_{N,\lceil C_HN^2\rceil}^{\Library}(f)_\infty
 <\frac{M+4}{2N^2}.
 
\end{equation}
A construção é determinística: quando $f(t_j)$ é equidistante dos dois
pontos admissíveis da grade alternada, escolhe-se o ponto menor, ou,
equivalentemente no denominador comum de \eqref{artigo_2:eq:joint-common-denominator},
o menor numerador $b_j$.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.joint_budget` — `lean4/ambientes/artigo_2/RequestProject/JointBudget.lean`, linha 424

```lean
/-- **Theorem 3.12 (controle simultâneo de erro, folhas, altura e bits)**.  There is a constant
`C_b` (depending only on `R, M`) such that for every dyadic power `n = 2^r ≥ 2` and every
`f ∈ 𝓕_{R,M}`, the (deterministic) assembly `g_n` interpolating the alternating-grid nodal
values `v_j` (see `jvals`, `jvals_nearest`) has exactly `n` leaves and satisfies
`‖f - g_n‖_∞ ≤ (M+4)/(8n²)`, `ht_max(g_n) ≤ C_H n²`, and its three code lengths are
`≤ C_b n log₂(2n)`. -/
theorem joint_budget (R M : ℝ) : ∃ Cb : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ f ∈ FRM R M,
    ∃ T : LTree, T = uniformTree (jvals f r) r 0 0 ∧
      WF 0 0 T ∧ T.numLeaves = 2 ^ r ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |f x - T.eval 0 0 x| ≤ (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2)) ∧
      (T.maxHeight : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 ∧
      Latom T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) ∧
      Lstr T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) ∧
      Lrat T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r)
```

`Artigo.joint_all_N` — `lean4/ambientes/artigo_2/RequestProject/JointBudget.lean`, linha 509

```lean
/-- **Theorem 3.12**, consequence (eq. joint-all-N): for every integer `N ≥ 2`,
`E_{N,⌈C_H N²⌉}(f)_∞ < (M+4)/(2N²)`. -/
theorem joint_all_N {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) (N : ℕ) (hN : 2 ≤ N) :
    jointErr N ⌈CH R M * (N : ℝ) ^ 2⌉₊ f < ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2))
```

**O que difere:** O Lean usa `FRM R M := {f | ContDiff ℝ 2 f ∧ (∀ x∈Icc 0 1, |f x| ≤ R) ∧ ∀ x∈Icc 0 1, |deriv (deriv f) x| ≤ M}` (Interp.lean), isto é, `f` é C² em toda a reta. O enunciado do volume define 𝓕_{R,M} = {f ∈ C²[0,1] : ‖f‖∞ ≤ R, ‖f″‖∞ ≤ M}. Toda f do Lean está na classe do texto, mas não o contrário: o Lean prova o teorema para uma subclasse. Em `joint_budget` e `joint_all_N` a hipótese é `f ∈ FRM R M`.

**O que provar:** Reaplicar `joint_budget`/`joint_all_N` à extensão `F` de cada `f ∈ FRMIcc R M` e transportar as conclusões por restrição a [0,1] (a árvore `uniformTree (jvals f r)` só amostra f em [0,1], o que facilita).


**Fechado em 11/11/2026.** Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; mesma árvore determinística `uniformTree (jvals f r)` (só amostra f em [0,1]) e consequência para todo N ≥ 2. Declarações: `Pendencias.joint_budget_Icc`, `Pendencias.joint_all_N_Icc` (`lean4/ambientes/artigo_2/Pendencias/Ponte.lean`). Compilado com `lake build Pendencias`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound`.
---

## [x] III.3.17. corolario — altura suficiente para precisão prescrita

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 715, rótulo `map:artigo_2:3.17`; PDF unificado, p. 46.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** III.3.16.

**Enunciado no volume (TeX):**

```latex
\begin{corollary}[altura suficiente para precisão prescrita]

Para $\varepsilon>0$, seja
\begin{equation}
 n_\varepsilon
 =2^{\left\lceil\log_2\max\left\{2,
        \sqrt{\frac{M+4}{8\varepsilon}}\right\}\right\rceil},
 \qquad
 H_\varepsilon=\lceil C_Hn_\varepsilon^2\rceil.
 
\end{equation}
Então, uniformemente para $f\in\mathcal F_{R,M}$,
\begin{align}
 E_{n_\varepsilon,H_\varepsilon}^{\Library}(f)_\infty
 &\le\varepsilon,\\
 n_\varepsilon&=O_{R,M}(\varepsilon^{-1/2}),
 &H_\varepsilon&=O_{R,M}(\varepsilon^{-1}),
 \\
 L_{\rm atom},\ L_{\rm ReLU,str},\ L_{\rm ReLU,rat}
 &=O_{R,M}\!\left(\varepsilon^{-1/2}
                   \log\frac{2}{\varepsilon}\right).
 
\end{align}
Em particular,
$H_{\varepsilon,n_\varepsilon}^{\Library}(f)\le H_\varepsilon$.
\end{corollary}
```

**Declarações Lean associadas (assinatura):**

`Artigo.height_for_epsilon` — `lean4/ambientes/artigo_2/RequestProject/JointBudget.lean`, linha 663

```lean
/-- **Corollary 3.13 (altura suficiente para precisão prescrita)**.  Uniformly for
`f ∈ 𝓕_{R,M}`: `E_{n_ε,H_ε}(f)_∞ ≤ ε` and `H_{ε,n_ε}(f) ≤ H_ε`; moreover, for `0 < ε ≤ 1`,
`n_ε = O(ε^{-1/2})`, `H_ε = O(ε^{-1})`, and the three code lengths of the certifying assembly
are `O(ε^{-1/2} log(2/ε))`, with constants depending only on `R, M`. -/
theorem height_for_epsilon (R M : ℝ) :
    (∀ f ∈ FRM R M, ∀ ε : ℝ, 0 < ε →
      jointErr (nEps M ε) (HEps R M ε) f ≤ ENNReal.ofReal ε ∧
      heightFor ε (nEps M ε) f ≤ HEps R M ε) ∧
    ∃ C : ℝ, ∀ f ∈ FRM R M, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (nEps M ε : ℝ) ≤ C / Real.sqrt ε ∧ (HEps R M ε : ℝ) ≤ C / ε ∧
      ∃ T : LTree, AdmNH (nEps M ε) (HEps R M ε) T ∧ supDist f T ≤ ENNReal.ofReal ε ∧
        (Latom T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) ∧
        (Lstr T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) ∧
        (Lrat T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε)
```

**O que difere:** O Lean usa `FRM R M := {f | ContDiff ℝ 2 f ∧ (∀ x∈Icc 0 1, |f x| ≤ R) ∧ ∀ x∈Icc 0 1, |deriv (deriv f) x| ≤ M}` (Interp.lean), isto é, `f` é C² em toda a reta. O enunciado do volume define 𝓕_{R,M} = {f ∈ C²[0,1] : ‖f‖∞ ≤ R, ‖f″‖∞ ≤ M}. Toda f do Lean está na classe do texto, mas não o contrário: o Lean prova o teorema para uma subclasse. `height_for_epsilon` quantifica `∀ f ∈ FRM R M`.

**O que provar:** Idem: derivar de III.3.16 com `FRMIcc`; constantes `n_ε`, `H_ε` não mudam.


**Fechado em 11/11/2026.** Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; n_ε, H_ε inalterados; `jointErr`, `heightFor` e `supDist` só dependem de f em [0,1]. Declarações: `Pendencias.height_for_epsilon_Icc` (`lean4/ambientes/artigo_2/Pendencias/Ponte.lean`). Compilado com `lake build Pendencias`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound`.
---

## [x] III.3.18. teorema — entropia e codebook explícito

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 794, rótulo `map:artigo_2:3.18`; PDF unificado, p. 47.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** III.3.17.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[entropia e codebook explícito]
Existem $\varepsilon_0,c,C,C_1>0$, dependentes apenas de $R$ e $M$, tais que, para $0<\varepsilon<\varepsilon_0$,
\begin{equation}
 c\varepsilon^{-1/2}
 \le\mathcal{H}_\varepsilon(\mathcal{F}_{R,M})
 \le C\varepsilon^{-1/2}.
 
\end{equation}
Existe também um codebook finito $\mathcal{C}_\varepsilon\subset\Aclass([0,1])$, composto somente por montagens de átomos de $\Library$, com distorção no máximo $\varepsilon$. Quando o codebook e seu decodificador são informação compartilhada, o comprimento de seu índice global de comprimento fixo é
\begin{equation}
 L_\varepsilon^{\mathrm{global}}(\mathcal C_\varepsilon)
 :=\left\lceil\log_2|\mathcal{C}_\varepsilon|\right\rceil
 \le C_1\varepsilon^{-1/2}.
 
\end{equation}
Logo esse codebook atinge em ordem a entropia métrica da classe em cardinalidade e em bits de índice global.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.entropy_codebook` — `lean4/ambientes/artigo_2/RequestProject/Entropy.lean`, linha 46

```lean
/-- **Theorem 3.14 (entropia e codebook explícito)**.  For `R, M > 0` there are
`ε₀, c, C, C₁ > 0` such that for `0 < ε < ε₀`:
`c ε^{-1/2} ≤ 𝓗_ε(𝓕_{R,M}) ≤ C ε^{-1/2}`, and there is a finite codebook of assemblies of
library atoms with distortion `≤ ε` whose global fixed-length index has
`⌈log₂ |𝒞_ε|⌉ ≤ C₁ ε^{-1/2}` bits. -/
theorem entropy_codebook (R M : ℝ) (hR : 0 < R) (hM : 0 < M) :
    ∃ ε₀ c C C₁ : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 < C ∧ 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      c / Real.sqrt ε ≤ entropyH ε (FRM R M) ∧ entropyH ε (FRM R M) ≤ C / Real.sqrt ε ∧
      ∃ CB : Finset LTree, (∀ T ∈ CB, WF 0 0 T) ∧
        (∀ f ∈ FRM R M, ∃ T ∈ CB, supDist f T ≤ ENNReal.ofReal ε) ∧
        (Nat.clog 2 CB.card : ℝ) ≤ C₁ / Real.sqrt ε
```

**O que difere:** O Lean usa `FRM R M := {f | ContDiff ℝ 2 f ∧ (∀ x∈Icc 0 1, |f x| ≤ R) ∧ ∀ x∈Icc 0 1, |deriv (deriv f) x| ≤ M}` (Interp.lean), isto é, `f` é C² em toda a reta. O enunciado do volume define 𝓕_{R,M} = {f ∈ C²[0,1] : ‖f‖∞ ≤ R, ‖f″‖∞ ≤ M}. Toda f do Lean está na classe do texto, mas não o contrário: o Lean prova o teorema para uma subclasse. `entropy_codebook` usa `entropyH ε (FRM R M)`: a entropia é de um conjunto de funções ℝ→ℝ.

**O que provar:** Provar que `entropyH ε (FRMIcc R M)` calculada com a distância uniforme em [0,1] coincide com a da classe restrita a [0,1] e que as cotas `c/√ε ≤ H_ε ≤ C/√ε` valem para ela (a cota superior segue da inclusão da restrição; a inferior exige que o conjunto de Lean, subclasse, já contenha uma família ε-separada suficientemente grande).


**Fechado em 11/11/2026.** Classe do texto `FRMIcc R M` (`ContDiffOn ℝ 2 f [0,1]`, f″ unilateral); `FRM ⊆ FRMIcc` e `extF f 0 1 ∈ FRM` coincide com f em [0,1]; coberturas de FRMIcc e FRM coincidem (`isCover_iff`), logo `entropyH ε (FRMIcc R M) = entropyH ε (FRM R M)`; codebook transportado. Declarações: `Pendencias.entropy_codebook_Icc` (`lean4/ambientes/artigo_2/Pendencias/Ponte.lean`). Compilado com `lake build Pendencias`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound`.
---

## [ ] III.3.25. algoritmo — enumeração exata do catálogo

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 1138, rótulo `map:artigo_2:3.25`; PDF unificado, p. 51.
- **Categoria A:** Algoritmo sem implementação certificada: há prova da recorrência, falta o programa e a prova de que ele a calcula.
- **Status no mapa:** `implementacao_pendente`.
- **Dependências / ordem:** III.3.23, III.3.24.

**Enunciado no volume (TeX):**

```latex
\begin{algorithm}[enumeração exata do catálogo]
Para parâmetros pequenos, gere recursivamente todas as formas de
$\mathfrak T_D(K)$; em cada folha, liste somente os átomos de $\Library_H$ com
o suporte exigido; ao unir duas subárvores, descarte pares cujos valores na
fronteira diferem. Reduza representações funcionalmente idênticas ao menor
fluxo $\operatorname{ser}_\sharp$, avalie $\mathcal J$ em aritmética racional
exata e aplique o desempate shortlex.
\end{algorithm}
```

**Declarações Lean associadas (assinatura):**

`Artigo.finite_catalog_minimizer` — `lean4/ambientes/artigo_2/RequestProject/Catalog.lean`, linha 329

```lean
/-- **Theorem 3.19 (finitude, existência e desempate canônico)**.  For `H ≥ H_K`:
`1 ≤ |Σ_{D,H}(K)| ≤ |𝔑_{D,H}(K)| ≤ T_D |𝓛_H|^{2^D}`; every functional `J` on `Σ_{D,H}(K)` attains
its minimum; and among all minimizing representations exactly one has the shortlex-least stream
`ser♯` (hence a unique canonical function and representation). -/
theorem finite_catalog_minimizer {H D k : ℕ} {m : ℤ} (hH : HK k m ≤ H) :
    1 ≤ (SigmaCat H D k m).card ∧ (SigmaCat H D k m).card ≤ (RepCat H D k m).card ∧
    (RepCat H D k m).card ≤ Tshape D * (LH H).card ^ 2 ^ D ∧
    (∀ J : (cellIcc k m → ℝ) → ℝ, ∃ g ∈ SigmaCat H D k m, ∀ g' ∈ SigmaCat H D k m, J g ≤ J g') ∧
    (∀ J : (cellIcc k m → ℝ) → ℝ, ∃! R, R ∈ minSet H D k m J ∧
      ∀ R' ∈ minSet H D k m J, canKey R ≤ canKey R')
```

**O que difere:** O Lean tem `finite_catalog_minimizer` (finitude, existência do minimizador, cardinalidade). Não há função executável de enumeração nem prova de que ela produz exatamente `SigmaCat`.

**O que provar:** Implementar `enumCatalog : ℕ → ℕ → ℕ → ℤ → List LTree` (D, H, raiz), com aritmética racional exata, redução ao menor fluxo `ser♯` e desempate shortlex; provar `∀ T, T ∈ enumCatalog … ↔ T ∈ RepCat …` e que o selecionado é o minimizador canônico. Testar com `#eval` em parâmetros pequenos.

---

## [ ] III.6.3. algoritmo — rotulação exata de uma árvore fixa

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 1675, rótulo `map:artigo_2:6.3`; PDF unificado, p. 57.
- **Categoria A:** Algoritmo sem implementação certificada: há prova da recorrência, falta o programa e a prova de que ele a calcula.
- **Status no mapa:** `implementacao_pendente`.
- **Dependências / ordem:** III.6.1, III.6.2.

**Enunciado no volume (TeX):**

```latex
\begin{algorithm}[rotulação exata de uma árvore fixa]

Enumere $\Pairs_H(J)$ em cada folha. Percorra $T$ em pós-ordem. Em cada nó
interno, agrupe os estados do filho direito pelo valor de fronteira esquerdo
$w$ e una apenas pares com o mesmo $w$. Para cada estado externo $(u,v)$,
retenha a menor chave \eqref{artigo_2:eq:tie-key} e um apontador para os dois filhos.
Na raiz, escolha a menor entrada finita e siga os apontadores.
\end{algorithm}
```

**Declarações Lean associadas (assinatura):**

`Artigo.Setup.fixed_correctness` — `lean4/ambientes/artigo_2/RequestProject/DP.lean`, linha 164

```lean
/-- **Theorem 6.2 (correção para árvore fixa)**: for every node `J` of the fixed tree (a
descendant of `K` at relative depth `r`, with `r + depth(T) ≤ D`) and every pair of states,
`C_T(J;u,v) = min_{R ∈ 𝔑_H(T_J;u,v)} cost(R)` (`+∞` if empty). -/
theorem fixed_correctness (hH : 2 ≤ S.H) : ∀ (T : Shape) (k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + T.depth ≤ S.D →
      S.Cfix T k m u v = (S.RsetS T k m u v).inf S.costW
```

`Artigo.Setup.fixed_global` — `lean4/ambientes/artigo_2/RequestProject/DP.lean`, linha 189

```lean
/-- **Theorem 6.2 (global form)**: `min_{u,v ∈ 𝒱} C_T(K;u,v) = min_{R ∈ 𝔑_H(T)} cost(R)`, and the
`κ`-least labelling of `T` is unique. -/
theorem fixed_global (hH : 2 ≤ S.H) (T : Shape) (hT : T.depth ≤ S.D) :
    (S.V ×ˢ S.V).inf (fun p => S.Cfix T S.k₀ S.m₀ p.1 p.2) = (S.RepShape T).inf S.costW ∧
    ((S.RepShape T).Nonempty → ∃! R, R ∈ S.RepShape T ∧ ∀ R' ∈ S.RepShape T, S.kappa R ≤ S.kappa R')
```

**O que difere:** `Setup.fixed_correctness` e `fixed_global` provam que a recorrência `Cfix` calcula o custo mínimo e que o representante canônico é único. Falta o algoritmo (pós-ordem, agrupamento por `w`, apontadores) e sua prova.

**O que provar:** Implementar a rotulação em pós-ordem com tabela `(u,v) ↦ (custo, chave κ, apontadores)`; provar que a tabela da raiz é igual a `Cfix` e que a retropropagação reconstrói o `R` canônico de `fixed_global`.

---

## [ ] III.7.4. algoritmo — seletor exato por programação dinâmica

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 1801, rótulo `map:artigo_2:7.4`; PDF unificado, p. 58.
- **Categoria A:** Algoritmo sem implementação certificada: há prova da recorrência, falta o programa e a prova de que ele a calcula.
- **Status no mapa:** `implementacao_pendente`.
- **Dependências / ordem:** III.7.1, III.7.2, III.8.1.

**Enunciado no volume (TeX):**

```latex
\begin{algorithm}[seletor exato por programação dinâmica]

Construa as tabelas em pós-ordem na árvore diádica completa de profundidade
$D$. Inicialize cada estado com o candidato folha, quando admissível. Una as
tabelas dos filhos pelo valor intermediário $w$, acrescente o marcador e a
penalidade de subdivisão e substitua a entrada somente quando a chave completa
diminuir. A tabela da raiz e os apontadores guardados fornecem o ótimo global
e sua representação.
\end{algorithm}
```

**Declarações Lean associadas (assinatura):**

`Artigo.Setup.variable_correctness` — `lean4/ambientes/artigo_2/RequestProject/DP.lean`, linha 43

```lean
/-- **Theorem 7.2 (exatidão)**: for a descendant `J` of `K` at relative depth `r` and `d ≤ D - r`,
`C_d(J;u,v) = min_{R ∈ 𝔑_{d,H}(J;u,v)} cost(R)` (`+∞` if empty). -/
theorem variable_correctness (hH : 2 ≤ S.H) : ∀ (d k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + d ≤ S.D → S.Cvar d k m u v = (S.Rset d k m u v).inf S.costW
```

`Artigo.Setup.variable_global` — `lean4/ambientes/artigo_2/RequestProject/DP.lean`, linha 67

```lean
/-- **Theorem 7.2 (global value, existence, determinism)**: `C⋆_{D,H}(K)` equals the minimum of
the objective over `𝔑_{D,H}(K)`; it is finite when `H ≥ max {2, k₀+1, |m₀|+1}`, in which case it
is attained; and the total tie key `κ` selects a unique representation, independently of any
enumeration order. -/
theorem variable_global (hH : 2 ≤ S.H) :
    S.Cstar = (RepCat S.H S.D S.k₀ S.m₀).inf S.costW ∧
    (HK S.k₀ S.m₀ ≤ S.H → S.Cstar ≠ ⊤ ∧
      ∃ R ∈ RepCat S.H S.D S.k₀ S.m₀, S.costW R = S.Cstar) ∧
    (HK S.k₀ S.m₀ ≤ S.H → ∃! R, R ∈ RepCat S.H S.D S.k₀ S.m₀ ∧
      ∀ R' ∈ RepCat S.H S.D S.k₀ S.m₀, S.kappa R ≤ S.kappa R')
```

**O que difere:** `variable_correctness`/`variable_global` provam a recorrência `Cvar` e a unicidade do ótimo canônico. Falta o seletor por programação dinâmica como programa certificado.

**O que provar:** Implementar o DP sobre a árvore diádica completa de profundidade D com atualização “somente se a chave completa diminuir”; provar que coincide com `Cvar`/`Cstar` e devolve o `R` de `variable_global`. Inclui o orçamento de folhas (III.8.1) se for desejado.

---

## [ ] III.9.1. teorema — complexidade em número de estados

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 1996, rótulo `map:artigo_2:9.1`; PDF unificado, p. 60.
- **Categoria P:** Cobertura parcial: o Lean prova algo mais fraco ou diferente do enunciado.
- **Status no mapa:** `cobertura_parcial`.
- **Dependências / ordem:** III.7.4 (implementação).

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[complexidade em número de estados]

Suponha os custos de folha pré-computados. Uma implementação densa do
\cref{artigo_2:alg:variable-tree} usa
\begin{equation}
 O(S_DM^3)
 
\end{equation}
operações e
\begin{equation}
 O(S_DM^2)
 
\end{equation}
entradas de memória quando preserva todos os apontadores de reconstrução.
A versão com orçamento de até $N$ folhas usa
\begin{equation}
 O(S_DN^2M^3)
 
\end{equation}
operações e $O(S_DNM^2)$ entradas. Se cada custo local
\eqref{artigo_2:eq:local-loss} for calculado diretamente sobre $P$ observações, a
inicialização densa acrescenta $O(S_DPM^2)$ operações.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.Setup.state_complexity` — `lean4/ambientes/artigo_2/RequestProject/Complexity.lean`, linha 89

```lean
`S_D M³`;
(iii) with a budget of up to `N` leaves, the table has `S_D N M²` entries and the transitions
(one per internal node, triple `(u,w,v)` and budget pair `n_L + n_R = n ≤ N`) number at most
`S_D N² M³`;
(iv) computing every local loss directly over the `P` observations costs `S_D P M²` operations;
(v) with `M ≤ 36 H⁶` (Lemma 4.4), the transitions number at most `36³ S_D H¹⁸`. -/
theorem state_complexity (hH : 2 ≤ S.H) (N : ℕ) :
    (cellsD S.D ×ˢ (S.V ×ˢ S.V)).card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V)).card ≤ (2 ^ (S.D + 1) - 1) * S.V.card ^ 3 ∧
    (cellsD S.D ×ˢ (S.V ×ˢ S.V) ×ˢ Finset.Icc 1 N).card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V) ×ˢ budgetPairs N).card ≤
      (2 ^ (S.D + 1) - 1) * N ^ 2 * S.V.card ^ 3 ∧
    (cellsD S.D ×ˢ (S.V ×ˢ S.V) ×ˢ Finset.range S.data.length).card =
      (2 ^ (S.D + 1) - 1) * S.data.length * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V)).card ≤ (2 ^ (S.D + 1) - 1) * (36 ^ 3 * S.H ^ 18)
```

**O que difere:** `Setup.state_complexity` prova as cardinalidades (tabelas `O(S_D M²)`, transições `O(S_D M³)`, com orçamento `S_D N M²` e `S_D N² M³`). O texto afirma número de OPERAÇÕES e de entradas de memória de uma implementação densa; não há semântica de execução nem modelo de custo no Lean.

**O que provar:** Definir um modelo de custo (por exemplo, uma mônada de contagem de passos `TimeM`) para a implementação densa de III.7.4 e provar que ela faz `O(S_D M³)` operações e usa `O(S_D M²)` células.

---

## [ ] III.9.3. teorema — cota grosseira de complexidade de bits

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 2083, rótulo `map:artigo_2:9.3`; PDF unificado, p. 61.
- **Categoria P:** Cobertura parcial: o Lean prova algo mais fraco ou diferente do enunciado.
- **Status no mapa:** `cobertura_parcial`.
- **Dependências / ordem:** III.9.1.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[cota grosseira de complexidade de bits]

Todos os custos racionais que aparecem na recorrência possuem numeradores e
denominadores de comprimento no máximo
\begin{equation}
 B_{\rm cost}
 =O\!\left(
 P\bigl(B_{\mathcal Z}+D+|k_0|+\log(2H)\bigr)
 +B_{\mathcal Z}+D+\log(2L)
 \right).
 
\end{equation}
Consequentemente, a versão densa sem orçamento de folhas pode ser executada em
\begin{equation}
 O\!\left(
 (S_DM^3+S_DPM^2)
 \bigl[\mathsf M_{\mathbb Z}(B_{\rm cost})
       \log(2B_{\rm cost})+L\bigr]
 \right)
 
\end{equation}
operações de bit e
\begin{equation}
 O\!\left(S_DM^2(B_{\rm cost}+L)\right)
 
\end{equation}
bits de memória quando todos os estados e fluxos são armazenados. Na versão
com até $N$ folhas, substituem-se $S_DM^3$ e $S_DM^2$ por
$S_DN^2M^3$ e $S_DNM^2$, respectivamente. Com multiplicação escolar,
$\mathsf M_{\mathbb Z}(b)=O(b^2)$.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.Setup.bit_complexity` — `lean4/ambientes/artigo_2/RequestProject/BitComplexity.lean`, linha 266

```lean
Let `B` bound the bit length `bl` of all abscissae, responses, weights and penalties, let
`P = |𝒵|` be the number of observations and `L` a bound on the stream lengths. Then every cost
`cost_𝒵(R)` occurring in the recursion — of a representation `R` rooted at a descendant `J` of
`K` within the depth budget, with atoms in `𝓛_H` and `|ser_rec(R)| ≤ L` — satisfies
`bl(cost_𝒵(R)) ≤ 2 (P (5B + 6⌈log₂H⌉ + 2(k₀+D) + 9) + 2B + 2⌈log₂L⌉ + 2) + 3`,
i.e. `bl = O(P (B_𝒵 + D + k₀ + log(2H)) + B_𝒵 + log(2L))`. -/
theorem bit_complexity {B L : ℕ}
    (hdata : ∀ p ∈ S.data, bl p.1 ≤ B ∧ bl p.2.1 ≤ B ∧ bl p.2.2 ≤ B) (hlb : bl S.lb ≤ B)
    (hls : bl S.ls ≤ B) {k r : ℕ} {m : ℤ} (hd : IsDesc S.k₀ S.m₀ k m r) {R : LTree}
    (hR : WF k m R) (hdep : r + R.depth ≤ S.D) (hh : R.maxHeight ≤ S.H) (hL : (serRec R).length ≤ L) :
    bl (S.costT R) ≤ 2 * (S.data.length * (5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 9) +
      2 * B + 2 * Nat.clog 2 L + 2) + 3
```

**O que difere:** `Setup.bit_complexity` limita o tamanho em bits dos custos racionais `B_cost`. As cotas de TEMPO e MEMÓRIA em bits do texto (produto `M_ℤ(B_cost)·log(2B_cost)` etc.) dependem de custo de multiplicação e comparação de racionais, que o Lean não modela.

**O que provar:** Estender o modelo de custo de III.9.1 com custo de operações em ℚ (multiplicação, soma, comparação, desempate shortlex) e provar a cota do enunciado.

---

## [x] III.11.2. lema — expansão local uniforme

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 2581, rótulo `map:artigo_2:11.2`; PDF unificado, p. 68.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** Ponte de regularidade; base de III.11.3 e III.12.1.

**Enunciado no volume (TeX):**

```latex
\begin{lemma}[expansão local uniforme]

Para toda célula $J\subseteq K$ e todo $x\in J$,
\begin{equation}
 \left|e_f(J)-\frac{|f''(x)|}{8}|J|^2\right|
 \le \frac{\omega_{f''}(|J|)}{8}|J|^2.
 
\end{equation}
\end{lemma}
```

**Declarações Lean associadas (assinatura):**

`Artigo.local_asymptotic_error` — `lean4/ambientes/artigo_2/RequestProject/Dyadic.lean`, linha 455

```lean
/-- **Lemma 11.2 (expansão local uniforme)**: for `f ∈ C²(K)`, every dyadic cell `J ⊆ K` and
every `x ∈ J`, `|e_f(J) - |f''(x)| |J|²/8| ≤ ω_{f''}(|J|) |J|²/8`. -/
theorem local_asymptotic_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ} {k : ℕ}
    {m : ℤ} (hJ : cellIcc k m ⊆ cellIcc k₀ m₀) {x : ℝ} (hx : x ∈ cellIcc k m) :
    |locErr f k m - |deriv (deriv f) x| / 8 * (cR k m - cL k m) ^ 2| ≤
      modCont (deriv (deriv f)) (cellIcc k₀ m₀) (cR k m - cL k m) / 8 * (cR k m - cL k m) ^ 2
```

**O que difere:** `Artigo.local_asymptotic_error` assume `hf : ContDiff ℝ 2 f` e usa `deriv (deriv f)` e `modCont (deriv (deriv f)) (cellIcc k₀ m₀)`. O texto: `f ∈ C²(K)` com ω_{f″} o módulo de continuidade de f″ em K.

**O que provar:** Reenunciar com `ContDiffOn ℝ 2 f (cellIcc k₀ m₀)` e `derivWithin`; ou provar que toda `f` C² em K tem extensão C² global que coincide com f em K e usar a versão atual.


**Fechado em 11/11/2026.** f ∈ C²(K) via `ContDiffOn`; e_f(J), f″ e ω_{f″} unilaterais em K, por `extF` e lemas de congruência. Declarações: `Pendencias.local_asymptotic_error_on` (`lean4/ambientes/artigo_2/Pendencias/Ponte.lean`). Compilado com `lake build Pendencias`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound`.
---

## [x] III.11.3. teorema — envelope diádico universal e agudo

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 2608, rótulo `map:artigo_2:11.3`; PDF unificado, p. 68.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** III.11.2.

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[envelope diádico universal e agudo]

Se $f\in C^2(K)$ e $I(f)>0$, então
\begin{align}
 \frac{I(f)}{\sqrt8}
 &\le \liminf_{\varepsilon\downarrow0}
       \sqrt\varepsilon\,n_f(\varepsilon)
 \le \limsup_{\varepsilon\downarrow0}
       \sqrt\varepsilon\,n_f(\varepsilon)
 \le \frac{I(f)}{\sqrt2},
 \\
 \frac{I(f)^2}{8}
 &\le \liminf_{N\to\infty}N^2E_N^{\rm dia}(f)_\infty
 \le \limsup_{N\to\infty}N^2E_N^{\rm dia}(f)_\infty
 \le \frac{I(f)^2}{2}.
 
\end{align}
As afirmações continuam válidas se $f''$ possui zeros ou muda de sinal. Se
$I(f)=0$, então $f$ é afim e ambos os erros são identicamente zero.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.general_dyadic_envelope` — `lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean`, linha 519

```lean
/-- **Theorem 11.3 (envelope diádico universal e agudo)**: if `f ∈ C²(K)` and `I(f) > 0`, then
`I/√8 ≤ liminf_{ε↓0} √ε n_f(ε) ≤ limsup_{ε↓0} √ε n_f(ε) ≤ I/√2` and
`I²/8 ≤ liminf_N N² E_N^{dia}(f)_∞ ≤ limsup_N N² E_N^{dia}(f)_∞ ≤ I²/2`,
stated in the equivalent form: for every `δ > 0` the bounds hold up to `δ` eventually
(as `ε → 0⁺`, resp. `N → ∞`). No assumption on the zeros or sign changes of `f''` is made. -/
theorem general_dyadic_envelope {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ}
    (hI : 0 < curvI f k₀ m₀) :
    (∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      curvI f k₀ m₀ / Real.sqrt 8 - δ ≤ Real.sqrt ε * nThr f ε k₀ m₀ ∧
      Real.sqrt ε * nThr f ε k₀ m₀ ≤ curvI f k₀ m₀ / Real.sqrt 2 + δ) ∧
    (∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      curvI f k₀ m₀ ^ 2 / 8 - δ ≤ (N : ℝ) ^ 2 * Edia f k₀ m₀ N ∧
      (N : ℝ) ^ 2 * Edia f k₀ m₀ N ≤ curvI f k₀ m₀ ^ 2 / 2 + δ)
```

`Artigo.general_dyadic_envelope_zero` — `lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean`, linha 544

```lean
/-- **Theorem 11.3 (degenerate case)**: if `I(f) = 0` then `f` is affine on `K` and both errors
vanish identically: `n_f(ε) = 1` for every `ε > 0` and `E_N^{dia}(f)_∞ = 0` for every `N ≥ 1`. -/
theorem general_dyadic_envelope_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ}
    (hI : curvI f k₀ m₀ = 0) :
    (∃ α β : ℝ, ∀ x ∈ cellIcc k₀ m₀, f x = α + β * x) ∧
    (∀ ε > 0, nThr f ε k₀ m₀ = 1) ∧ (∀ N : ℕ, 1 ≤ N → Edia f k₀ m₀ N = 0)
```

`Artigo.general_dyadic_envelope_liminf` — `lean4/ambientes/artigo_2/RequestProject/DyadicEnvelope.lean`, linha 597

```lean
/-- **Theorem 11.3 (envelope diádico universal e agudo), `liminf`/`limsup` form**: if `f ∈ C²(K)`
and `I(f) > 0`, then
`I/√8 ≤ liminf_{ε↓0} √ε n_f(ε)`, `limsup_{ε↓0} √ε n_f(ε) ≤ I/√2`,
`I²/8 ≤ liminf_N N² E_N^{dia}(f)_∞` and `limsup_N N² E_N^{dia}(f)_∞ ≤ I²/2`. -/
theorem general_dyadic_envelope_liminf {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ}
    (hI : 0 < curvI f k₀ m₀) :
    curvI f k₀ m₀ / Real.sqrt 8 ≤
      liminf (fun ε => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] (0 : ℝ)) ∧
    limsup (fun ε => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] (0 : ℝ)) ≤
      curvI f k₀ m₀ / Real.sqrt 2 ∧
    curvI f k₀ m₀ ^ 2 / 8 ≤ liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop ≤ curvI f k₀ m₀ ^ 2 / 2
```

**O que difere:** `general_dyadic_envelope` (e `_zero`, `_liminf`) assumem `ContDiff ℝ 2 f`; o texto exige `f ∈ C²(K)`.

**O que provar:** Derivar da versão atual por extensão C² (mesmo método de III.3.15) ou reprovar com `ContDiffOn`. O número `curvI f k₀ m₀` só depende de f em K.


**Fechado em 11/11/2026.** f ∈ C²(K) via `ContDiffOn`, com `curvIOn` (I(f) com f″ unilateral); as três formas (eventual, liminf/limsup, caso I(f)=0). Declarações: `Pendencias.general_dyadic_envelope_on`, `Pendencias.general_dyadic_envelope_liminf_on`, `Pendencias.general_dyadic_envelope_zero_on` (`lean4/ambientes/artigo_2/Pendencias/Ponte.lean`). Compilado com `lake build Pendencias`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound`.
---

## [x] III.12.1. teorema — lei exata e intervalo de acumulação

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 2705, rótulo `map:artigo_2:12.1`; PDF unificado, p. 69.
- **Categoria H:** Hipótese diferente (regularidade): o Lean exige C² na reta toda; o texto exige C² só no intervalo.
- **Status no mapa:** `ponte_regularidade_pendente`.
- **Dependências / ordem:** III.11.2 (ou o argumento do polinômio quadrático).

**Enunciado no volume (TeX):**

```latex
\begin{theorem}[lei exata e intervalo de acumulação]

Se $K$ é uma célula diádica de comprimento $L$ e
$q''\equiv\kappa\ne0$ em $K$, ponha
\begin{equation}
 A=\frac{|\kappa|L^2}{8}.
 
\end{equation}
Então, para todo $N\ge1$,
\begin{equation}
 E_N^{\rm dia}(q)_\infty
 =A\,4^{-\lfloor\log_2N\rfloor}.
 
\end{equation}
Consequentemente,
\begin{equation}
 \liminf_{N\to\infty}N^2E_N^{\rm dia}(q)_\infty=A,
 \qquad
 \limsup_{N\to\infty}N^2E_N^{\rm dia}(q)_\infty=4A,
 
\end{equation}
e o conjunto completo dos valores de acumulação de
$N^2E_N^{\rm dia}(q)_\infty$ é o intervalo $[A,4A]$. Em particular, a
constante obtida por um limite simples não existe.
\end{theorem}
```

**Declarações Lean associadas (assinatura):**

`Artigo.quadratic_dyadic_constant` — `lean4/ambientes/artigo_2/RequestProject/DyadicExact.lean`, linha 58

```lean
/-- **Theorem 12.1 (lei exata e intervalo de acumulação)**: if `K = J_{k₀,m₀}` has length `L`,
`q ∈ C²` and `q'' ≡ κ ≠ 0` on `K`, put `A = |κ| L²/8`. Then
`E_N^{dia}(q)_∞ = A 4^{-⌊log₂ N⌋}` for every `N ≥ 1` (`Nat.log 2 N = ⌊log₂ N⌋`); the set of
accumulation values of `N² E_N^{dia}(q)_∞` is exactly `[A, 4A]`,
`liminf = A`, `limsup = 4A`, and in particular `N² E_N^{dia}(q)_∞` has no limit.
Dually, `n_q(ε) = 2^{max(0, ⌈log₄(A/ε)⌉)}` for every `ε > 0`. -/
theorem quadratic_dyadic_constant {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) {k₀ : ℕ} {m₀ : ℤ}
    {κ : ℝ} (hκ : κ ≠ 0) (hκq : ∀ x ∈ cellIcc k₀ m₀, deriv (deriv q) x = κ)
    {A : ℝ} (hA : A = |κ| * (cR k₀ m₀ - cL k₀ m₀) ^ 2 / 8) :
    (∀ N : ℕ, 1 ≤ N → Edia q k₀ m₀ N = A / 4 ^ Nat.log 2 N) ∧
    {x | MapClusterPt x atTop (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N)} = Icc A (4 * A) ∧
    liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop = A ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop = 4 * A ∧
    (¬ ∃ c, Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop (𝓝 c)) ∧
    (∀ ε > 0, nThr q ε k₀ m₀ = 2 ^ (⌈Real.logb 4 (A / ε)⌉).toNat)
```

**O que difere:** `quadratic_dyadic_constant` assume `hq : ContDiff ℝ 2 q` e `deriv (deriv q) x = κ` em K. O texto trata `q` com `q″ ≡ κ` em K (q é só definida/C² em K).

**O que provar:** Para `q` C² em K com `q″ ≡ κ`, `q` coincide em K com um polinômio de grau 2: provar isso e aplicar a versão atual ao polinômio. Fecha o item sem nova prova analítica.


**Fechado em 11/11/2026.** Mesmas seis conclusões de `quadratic_dyadic_constant` com `q ∈ C²(K)` (`ContDiffOn`) e `q″ ≡ κ` unilateral em K; usa `extF` e lemas de congruência (`Edia_congr`, `nThr_congr`). Declarações: `Pendencias.quadratic_dyadic_constant_on` (`lean4/ambientes/artigo_2/Pendencias/LeiExata.lean`). Compilado com `lake build Pendencias` em `lean4/ambientes/artigo_2`; `#print axioms` só mostra `propext`, `Classical.choice`, `Quot.sound` (`axiomas_pendencias.log`).
---

## [ ] III.12.3. corolario — fases sincronizadas

- **Onde no TeX:** `tex/partes/artigo_2.tex`, linha 2860, rótulo `map:artigo_2:12.3`; PDF unificado, p. 71.
- **Categoria S:** Prova textual e prova Lean fora de sincronia (o enunciado bate; a demonstração em TeX precisa ser atualizada).
- **Status no mapa:** `prova_textual_a_sincronizar`.
- **Dependências / ordem:** III.12.2.

**Enunciado no volume (TeX):**

```latex
\begin{corollary}[fases sincronizadas]

Nas hipóteses do \cref{artigo_2:thm:piecewise-quadratic-count}, suponha ainda que
$A_i/A_j\in4^{\mathbb Z}$ para todos $i,j$. Então
\begin{equation}
 \liminf_{N\to\infty}N^2E_N^{\rm dia}(f)_\infty=\frac{I(f)^2}{8},
 \qquad
 \limsup_{N\to\infty}N^2E_N^{\rm dia}(f)_\infty=\frac{I(f)^2}{2}.
 
\end{equation}
\end{corollary}
```

**Declarações Lean associadas (assinatura):**

`Artigo.synchronized_phases` — `lean4/ambientes/artigo_2/RequestProject/DyadicSync.lean`, linha 99

```lean
/-- **Corollary 12.3 (fases sincronizadas)**: under the hypotheses of Theorem 12.2, if moreover
`Aᵢ/Aⱼ ∈ 4^ℤ` for all `i, j`, then
`liminf N² E_N^{dia}(f)_∞ = I(f)²/8` and `limsup N² E_N^{dia}(f)_∞ = I(f)²/2`,
where `I(f) = ∫₀¹ √|f''|`. -/
theorem synchronized_phases {f : ℝ → ℝ} {q₀ : ℕ} {κ : ℕ → ℝ}
    (hκ : ∀ i < 2 ^ q₀, κ i ≠ 0)
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ),
      f x = κ i / 2 * x ^ 2 + b * x + c)
    {A : ℕ → ℝ} (hA : ∀ i, A i = |κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8)
    (hsync : ∀ i < 2 ^ q₀, ∀ j < 2 ^ q₀, ∃ z : ℤ, A i / A j = (4 : ℝ) ^ z) :
    liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia f 0 0 N) atTop =
      (∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x|) ^ 2 / 8 ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia f 0 0 N) atTop =
      (∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x|) ^ 2 / 2
```

**O que difere:** O enunciado bate com `Artigo.synchronized_phases`. A demonstração em TeX aplica o envelope C² global a uma função quadrática POR PARTES, que pode não ser C²; a demonstração Lean evita isso (usa `piecewise_quadratic_count`).

**O que provar:** Não é prova Lean: reescrever a demonstração textual do Corolário III.12.3 seguindo a estrutura da prova Lean (usar a contagem exata de III.12.2 e a periodicidade em 4^ℤ, sem invocar o envelope C²).

---
