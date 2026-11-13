# Formalization of `artigo_fase3_taxas_refinamento_autocontido.tex`

Everything is in the namespace `Fase3`. All files build without `sorry`, and the only axioms used
are the standard ones (`propext`, `Classical.choice`, `Quot.sound`).

| File | Content |
| --- | --- |
| `RequestProject/Indexing.lean` | Section 2.1–2.2: Cantor pairing, the enumeration `Z` |
| `RequestProject/Heights.lean` | Section 2.2–2.3: height, `Q_H`, the enumerations `Q`, `Q*`, Stern / Calkin–Wilf |
| `RequestProject/Cells.lean` | Section 3: dyadic cells, centres, the generator `Γ`, recovery of the cell, address uniqueness, the jet dictionary |
| `RequestProject/Assembly.lean` | Section 4: Definition 4.1, Theorem 4.2, equation (23), and the interpolation tools reused later |
| `RequestProject/Extension.lean` | Equation (30): the quadratic extension `F`, `F ∈ C²(ℝ)`, `‖F''‖_ℝ = ‖f''‖_[α,β]` |
| `RequestProject/Rates.lean` | Section 5: Theorem 5.1 (31)–(33), Corollary 5.2, equation (35) |
| `RequestProject/Transcendental.lean` | Lemma 6.1: (37), (38) and the enclosure facts |
| `RequestProject/IntervalArith.lean` | Proposition 6.2: a concrete model of `BoundSecondDerivative` (36) and its correctness (39) |
| `RequestProject/Refinement.lean` | Algorithm 6.3 (as an explicit recursion) and Theorem 6.4 |
| `RequestProject/Calibration.lean` | Proposition 6.5 (44)–(45) |
| `RequestProject/Observation.lean` | Observation 6.6 |

## Where each result is

* **Lemma 2.1**: `cpair_bijective`, `cunpair_cpair`, `cpair_cunpair`, `cdiag_eq_floor` (the formula
  `w = ⌊(√(8n+1)-1)/2⌋`), `cpair_le`.
* **Lemma 2.2**: `zEnum_bijective`, `zEnum_zInv`, `zInv_zEnum`, `zInv_le`.
* **Lemma 2.3**: `card_QH_le` (`|Q_H| ≤ 3H²`), `card_QH_ge` (`|Q_H| ≥ H²/4` for every `H`, so
  `c₁ = 1/4` and `H₀ = 0`), `exists_card_QH_ge`. The lower bound is proved by an elementary count
  of coprime pairs instead of Mertens' theorem; the statement is unchanged.
* **Lemma 2.4**: `Qenum_bijective`, `QstarEnum_bijective`, `rankQ_lt`, `rankQstar_lt`. `Q` is
  defined as the inverse of the rank in the order "height, then denominator, then numerator".
* **Lemma 2.5**: `calkinWilf_two_pow` (with `stern_even`, `stern_odd` for the recurrence (08)).
* **Lemma 3.1**: `cellOwn_partition`, `cell_refine`, `cell_length`, `center_bijOn`, `dyadicMid_dense`.
* **Lemma 3.2**: `decode4_bijective`.
* **Definition 3.3**: `gen`, `library`, `atomLine`, plus `cLo_lt_dHi` (the interval is non-degenerate).
* **Lemma 3.4**: `preimageInterval_eq`.
* **Theorem 3.5**: `gen_injective`.
* **Theorem 3.6**: `jet_bijective`, `jet_dense`.
* **Definition 4.1**: `IsAssembly`.
* **Theorem 4.2**: `assembly_dense`.
* **Equation (23)**: `numCells_bounds` (`(β-α)2^k ≤ N_k < (β-α)2^k + 2`), `card_uniformCover`.
* **Equation (30)**: `extF`, `extF_contDiff`, `supNorm_extF2`.
* **Theorem 5.1**: `errP_le` (31), `tendsto_errP` (32), `exists_assembly_rate` (33).
* **Corollary 5.2**: `exists_assembly_seq_constant`.
* **Equation (35)**: `errP_le_numCells`, and `errP_le_numCells_of_nodes` (nodal endpoints: no
  boundary term).
* **Lemma 6.1**: `exp_sub_expPoly_bounds` (37), `sin_cos_lagrange` (38), `sin_mem_inflated`,
  `cos_mem_inflated`, `exp_reduction`, `exp_neg_reciprocal`, `exp_image_subset`; the rational
  routines of the model are proved correct in `expQ_sound`, `Iv.expEncl_mem`, `Iv.sinEncl_mem`,
  `Iv.cosEncl_mem`.
* **Proposition 6.2**: `boundSecondDerivative_correct`, `Mint_ge_supNorm`, `ivJet_inv_fail`,
  `Iv.inv_eq_none_iff`.
* **Algorithm 6.3**: `cert` (41), `refineCell`, `refineAll`, `rStar` (43).
* **Theorem 6.4**: `refine_terminates` (termination, depth `≤ r*`, at most `R₀ 2^{r*}` leaves),
  `refine_correct` (steps (iv)–(v) can be carried out, and any valid choice gives an assembly
  with unique addresses satisfying (42)), `rStar_zero`.
* **Proposition 6.5**: `calibration`.
* **Observation 6.6**: `center_error_eq`, `cube_example`.

## Modelling choices

* **Functions on `[α, β]`.** Functions are `ℝ → ℝ`. "f ∈ C²[α,β]" is `ContDiffOn ℝ 2 f (Icc α β)`.
  `f'` and `f''` are the one-sided derivatives `derivWithin` on `[α,β]` (`d1`, `d2`), and
  `M = ‖f''‖_{∞,[α,β]}` is `normD2`. Uniform norms on a set are `supNormOn K u = sup_{x∈K} |u x|`.
* **Cells.** Cells are pairs `(k, m)`. `P_k F` is `interpP k F`, the interpolant at the nodes
  `j 2^{-k}`; `h = 2^{-k}` is `mesh k`.
* **Assemblies.** `IsAssembly α β g` requires that every address `n(J)` has its atom on the cell
  `J`. Agreement at shared boundaries is automatic because `g` is a single function.
* **Algorithm 6.3.** The `while` loop of step (iii) is modelled by a recursion with a bound `r` on
  the number of levels. Termination is stated as two facts: the output does not change for any
  bound `≥ r*`, and on the output no leaf satisfies the loop condition `η_cert > ε_I`.
  Steps (iv)–(v) are certified for *every* admissible choice of rational nodal values.
* **Proposition 6.2.** The paper only describes the routine (36) informally. We give a concrete
  executable model and prove it correct:
  * expressions `Expr`, where composition is syntactic substitution;
  * rational intervals `Iv`;
  * exponential enclosures by argument reduction and the bound (37), with Taylor order `P`;
  * sine and cosine enclosures by interval evaluation of the Maclaurin polynomial, inflation by
    (38), and intersection with `[-1,1]`;
  * 2-jet propagation with the rules of Section 6.1;
  * failure (`none`) when a denominator interval contains `0`;
  * `d` levels of bisection, joined by convex hull.

  Correctness shows that success already implies that `E` is `C²` near every point of `J`. The
  paper's hypothesis "E defines a C² function on J" is therefore not needed.
* **Proposition 6.5.** `[α,β] = J₀`. The hypotheses are `M(J) = |κ|` on every descendant of `J₀`
  and `f'' ≡ κ` on `J₀`. `N(ε)` is the length of the output of the refinement with `r(ε)` levels.
  We also prove that the output does not change for more levels.

## Not formalized

* The numerical table for `e^x` and the figures: these are numerical illustrations, not statements.
* The cited fact that the Calkin–Wilf sequence lists every positive rational exactly once. The
  paper only uses it as background; Lemma 2.5 itself is proved.
* Mertens' asymptotic `Φ(H) = 3H²/π² + O(H log H)`. Lemma 2.3 is proved without it.
