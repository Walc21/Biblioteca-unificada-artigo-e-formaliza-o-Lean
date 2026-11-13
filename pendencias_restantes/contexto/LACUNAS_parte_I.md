# Lacunas de prova em Lean: Parte I (Biblioteca, endereçamento, refinamento)

2 caso(s) cujo enunciado do volume não está integralmente provado por uma declaração Lean existente. Marque `[x]` quando o caso for fechado e atualize o `status` em `mapas/correspondencia_completa.json`.

## [ ] I.6.3. algoritmo — refinamento certificado

- **Onde no TeX:** `tex/partes/artigo_1.tex`, linha 434, rótulo `map:artigo_1:6.3`; PDF unificado, p. 16.
- **Categoria C:** Contrato abstrato: o Lean prova sob um majorante genérico; falta ligar ao avaliador concreto.
- **Status no mapa:** `contrato_abstrato`.
- **Dependências / ordem:** I.6.2 (`boundSecondDerivative_correct`, `Mint_ge_supNorm`), I.6.4.

**Enunciado no volume (TeX):**

```latex
\begin{algoritmo}[refinamento certificado]
Dados $f\in C^2[\alpha,\beta]$, tolerâncias $\varepsilon_I,\varepsilon_R>0$ e a extensão $F$ de \eqref{artigo_1:eq:30}, use, para toda célula $J$, um majorante validado
\eqn{40}{\normK{F''}{J}\le M(J)\le M_*<\infty.}
Quando $F$ é fornecida por uma expressão de $\EE$, tome $M(J)=M_{\rm int}(J)$ de \eqref{artigo_1:eq:39}; se a certificação falhar, aborte sem emitir uma montagem garantida. Para uma função $C^2$ fora dessa interface, \eqref{artigo_1:eq:40} é um contrato de entrada.
\begin{enumerate}[label=(\roman*),topsep=6pt,itemsep=3pt]
\item Inicie com uma cobertura diádica finita de $[\alpha,\beta]$.
\item Para cada folha $J$, calcule
\eqn{41}{\eta_{\rm cert}(J)=\frac{|J|^2M(J)}8.}
\item Enquanto existir folha com $\eta_{\rm cert}(J)>\varepsilon_I$, substitua-a por seus dois filhos.
\item Nos nós finais, escolha racionais compartilhados $v_t$ com $|v_t-F(t)|<\varepsilon_R$ e valores adjacentes distintos.
\item Emita, em cada folha, o endereço do átomo que interpola seus dois valores nodais.
\end{enumerate}
\end{algoritmo}
```

**Declarações Lean associadas (assinatura):**

`Fase3.refineCell` — `lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean`, linha 29

```lean
/-- Step (iii) of Algorithm 6.3 applied below one cell, with at most `r` levels:
a leaf with `η_cert(J) > ε` is replaced by its two children. -/
noncomputable def refineCell (M : ℕ × ℤ → ℝ) (ε : ℝ) : ℕ → ℕ × ℤ → List (ℕ × ℤ)
  | 0, J => [J]
  | r + 1, J => if cert M J ≤ ε then [J] else
      refineCell M ε r (child0 J) ++ refineCell M ε r (child1 J)
```

`Fase3.refineAll` — `lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean`, linha 35

```lean
/-- Algorithm 6.3, steps (i)–(iii): refine every root of the initial cover. -/
noncomputable def refineAll (M : ℕ × ℤ → ℝ) (ε : ℝ) (roots : List (ℕ × ℤ)) (r : ℕ) :
    List (ℕ × ℤ)
```

`Fase3.rStar` — `lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean`, linha 39

```lean
/-- The depth bound `r* = max{0, ⌈½ log₂(h₀² M* / (8 ε_I))⌉}` (equation (43)). -/
noncomputable def rStar (h0 Mstar εI : ℝ) : ℕ
```

**O que difere:** `Fase3.refineCell/refineAll/rStar` formalizam os passos (i)–(iii) com um majorante abstrato `M : ℕ×ℤ → ℝ`, e `refine_correct` cobre (iv)–(v) por existência. Não há composição com `boundSecondDerivative` (I.6.2) para uma expressão de 𝓔, nem o ramo “se a certificação falhar, aborte”.

**O que provar:** Enunciar e provar `refine_correct_expr`: para `E : Expr` com `boundSecondDerivative` bem-sucedido em toda célula visitada, tomar `M J := Mint (I J)` e concluir `‖f−g‖ ≤ ε_I+ε_R`; provar também que, se alguma célula falha, o algoritmo devolve “abortar” (tipo `Option`).

---

## [ ] I.6.4. teorema — correção, término e tamanho

- **Onde no TeX:** `tex/partes/artigo_1.tex`, linha 449, rótulo `map:artigo_1:6.4`; PDF unificado, p. 17.
- **Categoria C:** Contrato abstrato: o Lean prova sob um majorante genérico; falta ligar ao avaliador concreto.
- **Status no mapa:** `contrato_abstrato`.
- **Dependências / ordem:** I.6.3.

**Enunciado no volume (TeX):**

```latex
\begin{teorema}[correção, término e tamanho]
O algoritmo~6.3 termina e produz $g\in\Asm([\alpha,\beta])$ com
\eqn{42}{\norm{f-g}\le\varepsilon_I+\varepsilon_R.}
Se a cobertura inicial tem $R_0$ raízes de largura máxima $h_0$ e $M_*>0$, nenhuma ramificação ultrapassa
\eqn{43}{r_*=\max\left\{0,\left\lceil\frac12\log_2\left(\frac{h_0^2M_*}{8\varepsilon_I}\right)\right\rceil\right\}}
níveis, e há no máximo $R_02^{r_*}$ folhas. Se $M_*=0$, pode-se tomar $r_*=0$.
\end{teorema}
```

**Declarações Lean associadas (assinatura):**

`Fase3.refine_terminates` — `lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean`, linha 222

```lean
/-- **Theorem 6.4 (termination and size).** With `M(J) ≤ M*` for every cell and roots of
width at most `h₀`, the refinement (run with `r*` levels) is stable — running it longer does
not change the output, i.e. the loop of step (iii) has terminated — every leaf satisfies
`η_cert ≤ ε_I`, no branch exceeds `r*` levels, and there are at most `R₀ 2^{r*}` leaves. -/
theorem refine_terminates (M : ℕ × ℤ → ℝ) {Mstar εI h0 : ℝ} (hM : ∀ J, M J ≤ Mstar)
    (hεI : 0 < εI) (roots : List (ℕ × ℤ)) (hh0 : ∀ J ∈ roots, mesh J.1 ≤ h0) :
    (∀ s, refineAll M εI roots (rStar h0 Mstar εI + s) = refineAll M εI roots (rStar h0 Mstar εI)) ∧
    (∀ L ∈ refineAll M εI roots (rStar h0 Mstar εI), cert M L ≤ εI) ∧
    (∀ L ∈ refineAll M εI roots (rStar h0 Mstar εI), ∃ J0 ∈ roots,
        J0.1 ≤ L.1 ∧ L.1 ≤ J0.1 + rStar h0 Mstar εI ∧ cC L ⊆ cC J0) ∧
    (refineAll M εI roots (rStar h0 Mstar εI)).length ≤ roots.length * 2 ^ rStar h0 Mstar εI
```

`Fase3.refine_correct` — `lean4/ambientes/base_integrada/Unified/Fase3/Refinement.lean`, linha 292

```lean
/-- **Theorem 6.4 (correctness).** Under the validated-majorant contract (40)
`‖F''‖_{∞,J} ≤ M(J) ≤ M*`, steps (iv)–(v) of Algorithm 6.3 can be carried out — rational
nodal values within `ε_R` of `F` with distinct values at the two ends of every leaf exist —
and, for **any** such choice, the emitted interpolant is a continuous assembly
`g ∈ 𝒜([α,β])` whose leaf atoms have unique addresses and with
`‖f - g‖_∞ ≤ ε_I + ε_R` (equation (42)). -/
theorem refine_correct {f : ℝ → ℝ} {α β : ℝ} (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β))
    (M : ℕ × ℤ → ℝ) {Mstar εI εR h0 : ℝ}
    (hM : ∀ J, (∀ x ∈ cC J, |deriv (deriv (extF f α β)) x| ≤ M J) ∧ M J ≤ Mstar)
    (hεI : 0 < εI) (hεR : 0 < εR) (roots : List (ℕ × ℤ)) (hroots : roots.Pairwise DisjInt)
    (hcov : Icc α β ⊆ ⋃ J ∈ roots, cC J) (hh0 : ∀ J ∈ roots, mesh J.1 ≤ h0) :
    (∃ v : ℝ → ℚ, (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI),
        |(v (cL J) : ℝ) - extF f α β (cL J)| < εR ∧ |(v (cR J) : ℝ) - extF f α β (cR J)| < εR) ∧
      ∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI), v (cL J) ≠ v (cR J)) ∧
    ∀ v : ℝ → ℚ, (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI),
        |(v (cL J) : ℝ) - extF f α β (cL J)| < εR ∧ |(v (cR J) : ℝ) - extF f α β (cR J)| < εR) →
      (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI), v (cL J) ≠ v (cR J)) →
      IsAssembly α β (cellInterp (refineAll M εI roots (rStar h0 Mstar εI)).toFinset
          (fun t => (v t : ℝ))) ∧
      (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI), ∃! n, gK n = J.1 ∧ gM n = J.2 ∧
          ∀ x, atomLine n x = lin J (fun t => (v t : ℝ)) x) ∧
      supNormOn (Icc α β) (fun x => f x - cellInterp (refineAll M εI roots (rStar h0 Mstar εI)).toFinset
          (fun t => (v t : ℝ)) x) ≤ εI + εR
```

**O que difere:** `Fase3.refine_terminates` e `refine_correct` provam término, cota `R₀·2^{r*}` e erro `≤ ε_I+ε_R` sob o contrato (40) com `M` abstrato. O texto diz “o algoritmo 6.3 termina e produz g”: falta o enunciado para o algoritmo executável com avaliação intervalar.

**O que provar:** Mesmo fecho de I.6.3: instanciar `M` com o majorante intervalar certificado e provar o enunciado (42)–(43) para essa instância.

---
