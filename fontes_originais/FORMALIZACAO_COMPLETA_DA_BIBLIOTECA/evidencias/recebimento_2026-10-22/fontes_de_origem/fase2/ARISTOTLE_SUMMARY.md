# Summary of changes for run dd8a2546-daa2-4505-a060-7c3dcf056216
I formalized and proved in Lean every numbered result in Sections 2–3 of `artigo_fase2_densidade_autocontido.tex`, plus Section 4 through Theorem 4.2 and Equation (23). The project builds with no `sorry`, and the main theorems use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Everything is in namespace `Dyadic2`, split into four files under `RequestProject/`.

**`Pairing.lean` (Section 2.1–2.2)**
- **Lemma 2.1:** the Cantor pairing \(\pi(u,v)=T_{u+v}+v\) is a bijection (`cpair_bijective`). Its inverse equals the floor formula (02) with \(\lfloor(\sqrt{8n+1}-1)/2\rfloor\) (`cunpair_eq_floor_formula`), and \(\pi(u,v)\le(u+v+1)^2\) (`cpair_le`).
- **Lemma 2.2:** \(Z\) is a bijection (`Zenum_bijective`), with the stated inverse formulas and the bound \(Z^{-1}(m)\le 2|m|+1\).

**`HeightEnum.lean` (Section 2.2–2.3)**
- **Lemma 2.3:** \(|\mathbb Q_H|\le 3H^2\) for \(H\ge1\). The lower bound \(|\mathbb Q_H|\ge H^2/4\) holds for every \(H\), so the claim with \(c_1=1/4\) follows. The proof differs from the paper's: Mathlib doesn't provide Mertens' asymptotic, so I used an elementary sieve instead. At least \(H^2/4\) pairs in \([1,H]^2\) are coprime, because \(\sum_{d\ge2}1/d^2<3/4\).
- **Lemma 2.4:** I built \(Q\) and \(Q^*\) as bijections `ℕ ≃ ℚ` and `ℕ ≃ ℚ*` that follow the order "height, then \(q\), then \(p\)" (`Qenum_lt_iff`, `Qstar_lt_iff`). A rational of height \(\le H\) has rank \(<3H^2\) in either one.
- **Lemma 2.5:** for Stern's sequence (08), \(CW(2^{q-1})=1/q\).

**`DyadicCells.lean` (Section 3)**
- **Lemma 3.1:** the owned cells partition \(\mathbb R\); the refinement identity holds and the length is \(2^{-k}\); the centers give a bijection \(\mathbb N_0\times\mathbb Z\to\mathbb D_{\rm mid}\); and \(\mathbb D_{\rm mid}\) is dense.
- **Lemma 3.2:** the unpacking \(n\mapsto(k,\mu,r,t)\) is a bijection onto \(\mathbb N_0^4\).
- **Definition 3.3:** the generator \(\Gamma\) and the library \(\mathcal L\), following Equations (14)–(18).
- **Lemma 3.4:** \(I^x_n=J_{k(n),m(n)}\).
- **Theorem 3.5:** \(\Gamma\) is injective, so it is a bijection onto \(\mathcal L\).
- **Theorem 3.6:** the jet map is a bijection onto \(\mathbb D_{\rm mid}\times\mathbb Q\times\mathbb Q^*\), and its image is dense in \(\mathbb R^3\).

**`Assemblies.lean` (Section 4)**
- **Definition 4.1** is `Asm`. It also requires that each address's own cell is the cell it is used on, which the paper leaves implicit. This makes the theorem below slightly stronger.
- **Theorem 4.2** (`assemblies_dense`): for \(\alpha<\beta\), every \(f\in C[\alpha,\beta]\) and every \(\varepsilon>0\), some \(g\in\mathcal A([\alpha,\beta])\) has \(\|f-g\|_\infty<\varepsilon\). The proof follows the paper's construction (extension by constants, rational nodal values with \(v_{j+1}\ne v_j\), linear interpolation).
- **Equation (23):** \(0\le N_k-(\beta-\alpha)2^k<2\), and the uniform cover has exactly \(N_k\) cells and covers \([\alpha,\beta]\).

**Not formalized:** the text's passing remark that Calkin–Wilf lists \(\mathbb Q_{>0}\) without repetition. The paper states it without proof and no numbered result depends on it.