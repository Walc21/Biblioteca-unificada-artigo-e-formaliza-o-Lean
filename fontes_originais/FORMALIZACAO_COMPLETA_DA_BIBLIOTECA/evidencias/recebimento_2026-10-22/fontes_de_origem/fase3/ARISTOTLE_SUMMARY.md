# Summary of changes for run 8e1639fb-20f4-46aa-8a6d-d55fdc8f23f6
I formalized the whole paper in Lean: the main targets, Sections 5 and 6, plus everything they depend on from Sections 2, 3 and 4. Everything builds with no `sorry`, and checking the axioms of the main theorems shows only the standard ones (`propext`, `Classical.choice`, `Quot.sound`). The code is in 11 files under `RequestProject/`, all in the namespace `Fase3`. `FORMALIZATION.md` maps each numbered result in the paper to its Lean name and lists the modelling choices.

**What is proved:**
- **Section 2:** Lemmas 2.1–2.5. This covers the Cantor pairing with the formula \(w=\lfloor(\sqrt{8n+1}-1)/2\rfloor\), the enumeration `Z`, the height count \(c_1 H^2\le|Q_H|\le 3H^2\), and the enumerations `Q`, `Q*` with position \(<3H^2\). For Lemma 2.5, \(CW(2^{q-1})=1/q\).
- **Section 3:** Lemmas 3.1, 3.2 and 3.4, Theorem 3.5 (`Γ` is injective) and Theorem 3.6 (the jet dictionary is a bijection onto \(\mathbb D_{mid}\times\mathbb Q\times\mathbb Q^*\) and its image is dense).
- **Section 4:** Definition 4.1 (`IsAssembly`), Theorem 4.2 (`assembly_dense`) and equation (23), stated as \((\beta-\alpha)2^k\le N_k<(\beta-\alpha)2^k+2\).
- **Section 5:**
  - The extension (30) is \(C^2\) on \(\mathbb R\) and \(\|F''\|_{\mathbb R}=\|f''\|_{[\alpha,\beta]}\).
  - Theorem 5.1: the bound (31), the limit (32) and the assembly estimate (33).
  - Corollary 5.2.
  - Equation (35), plus the version with no boundary term when \(\alpha,\beta\) are mesh nodes.
- **Section 6:**
  - Lemma 6.1: the bounds (37) and (38), and the inflate-and-intersect enclosures.
  - Proposition 6.2, proved for a concrete model of the routine described below.
  - Algorithm 6.3 and Theorem 6.4. One theorem gives termination, depth at most \(r^*\) and at most \(R_0 2^{r^*}\) leaves; a second gives correctness (42). For correctness, valid rational nodal values exist, and *any* such choice produces an assembly with unique addresses.
  - Proposition 6.5: exactly \(2^{r(\varepsilon)}\) leaves, and the liminf/limsup values \(\tfrac1{\sqrt8}\int|f''|^{1/2}\) and \(\tfrac1{\sqrt2}\int|f''|^{1/2}\).
  - Observation 6.6, including \(\|x^3-x\|_{\infty,[-1,1]}=2/(3\sqrt3)\).

**Modelling choices you should know about:**
- **Proposition 6.2:** the paper describes `BoundSecondDerivative` only informally, so I wrote a concrete, executable version and proved that one correct. It uses rational intervals, argument reduction plus the bound (37) for `exp`, and Maclaurin polynomials plus (38) intersected with \([-1,1]\) for `sin`/`cos`. It propagates 2-jets, does `d` levels of bisection, and fails when a denominator interval contains 0. In this model, success already implies that `E` is \(C^2\) near \(J\), so the paper's \(C^2\) hypothesis isn't needed.
- **Algorithm 6.3:** the `while` loop is modelled as a recursion with a cap on the number of levels. "Terminates" means the output doesn't change for any cap \(\ge r^*\) and no leaf meets the loop condition.
- **Lemma 2.3:** I proved \(|Q_H|\ge H^2/4\) for every \(H\) by counting coprime pairs, instead of using Mertens' asymptotic. The statement is unchanged.
- **Derivatives on \([\alpha,\beta]\):** \(f'\) and \(f''\) are the one-sided derivatives on \([\alpha,\beta]\).

**Not formalized:** the numerical table for \(e^x\) and the figures, which are illustrations rather than statements; and the cited background fact that Calkin–Wilf lists every positive rational exactly once.

All results are recorded in the Properties table as proved.