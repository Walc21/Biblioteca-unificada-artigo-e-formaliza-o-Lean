import RequestProject.DyadicExact
import Pendencias.Extensao

/-!
# III.12.1 — lei exata com `q ∈ C²(K)` só na célula

`Artigo.quadratic_dyadic_constant` exige `ContDiff ℝ 2 q` na reta. Aqui `q` é `C²` só em
`K = J_{k₀,m₀}` e `q'' ≡ κ` em `K` no sentido unilateral (`derivWithin`). Como `E_N^{dia}`
e `n_q(ε)` só dependem dos valores de `q` em `K` (lemas `*_congr`), basta aplicar a versão
global à extensão `extF q`, que coincide com `q` em `K` e tem `extF'' = κ` em `K`.
-/

namespace Pendencias

open Set Filter Topology Artigo DShape

section congr

variable {f g : ℝ → ℝ}

lemma locErr_congr {k : ℕ} {m : ℤ} (h : EqOn f g (cellIcc k m)) :
    locErr f k m = locErr g k m := by
  have hab := cL_lt_cR k m
  have ha : f (cL k m) = g (cL k m) := h (by rw [cellIcc_eq]; exact ⟨le_rfl, hab.le⟩)
  have hb : f (cR k m) = g (cR k m) := h (by rw [cellIcc_eq]; exact ⟨hab.le, le_rfl⟩)
  unfold locErr
  congr 1
  apply Set.image_congr
  intro x hx
  simp only [linInterp, h hx, ha, hb]

lemma treeErr_congr : ∀ (T : DShape) (k : ℕ) (m : ℤ), EqOn f g (cellIcc k m) →
    T.treeErr f k m = T.treeErr g k m
  | .leaf, _, _, h => locErr_congr h
  | .node l r, k, m, h => by
      simp only [DShape.treeErr]
      rw [treeErr_congr l _ _ (h.mono (cell_child_left_sub k m)),
        treeErr_congr r _ _ (h.mono (cell_child_right_sub k m))]

lemma Edia_congr {k : ℕ} {m : ℤ} (h : EqOn f g (cellIcc k m)) (N : ℕ) :
    Edia f k m N = Edia g k m N := by
  unfold Edia
  have e : ∀ T : DShape, T.treeErr f k m = T.treeErr g k m := fun T => treeErr_congr T k m h
  simp_rw [e]

lemma isThr_congr {ε : ℝ} {k : ℕ} {m : ℤ} {T : DShape} (hT : IsThr f ε k m T) :
    EqOn f g (cellIcc k m) → IsThr g ε k m T := by
  induction hT with
  | leaf hle =>
      intro h
      exact IsThr.leaf (by rwa [← locErr_congr h])
  | node hlt _ _ ihl ihr =>
      intro h
      exact IsThr.node (by rwa [← locErr_congr h]) (ihl (h.mono (cell_child_left_sub _ _)))
        (ihr (h.mono (cell_child_right_sub _ _)))

lemma thrTree_congr {ε : ℝ} {k : ℕ} {m : ℤ} (h : EqOn f g (cellIcc k m)) :
    thrTree f ε k m = thrTree g ε k m := by
  by_cases hex : ∃ T, IsThr f ε k m T
  · have hf := thrTree_spec hex
    have hex' : ∃ T, IsThr g ε k m T := ⟨_, isThr_congr hf h⟩
    exact (isThr_congr hf h).unique (thrTree_spec hex')
  · have hex' : ¬ ∃ T, IsThr g ε k m T := fun ⟨T, hT⟩ => hex ⟨T, isThr_congr hT h.symm⟩
    unfold thrTree
    rw [dif_neg hex, dif_neg hex']

lemma nThr_congr {k : ℕ} {m : ℤ} (h : EqOn f g (cellIcc k m)) (ε : ℝ) :
    nThr f ε k m = nThr g ε k m := by
  unfold nThr; rw [thrTree_congr h]

end congr

/-- **Teorema III.12.1** com `q ∈ C²(K)` e `q'' ≡ κ` em `K` (derivadas unilaterais). -/
theorem quadratic_dyadic_constant_on {q : ℝ → ℝ} {k₀ : ℕ} {m₀ : ℤ}
    (hq : ContDiffOn ℝ 2 q (cellIcc k₀ m₀)) {κ : ℝ} (hκ : κ ≠ 0)
    (hκq : ∀ x ∈ cellIcc k₀ m₀,
      derivWithin (derivWithin q (cellIcc k₀ m₀)) (cellIcc k₀ m₀) x = κ)
    {A : ℝ} (hA : A = |κ| * (cR k₀ m₀ - cL k₀ m₀) ^ 2 / 8) :
    (∀ N : ℕ, 1 ≤ N → Edia q k₀ m₀ N = A / 4 ^ Nat.log 2 N) ∧
    {x | MapClusterPt x atTop (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N)} = Icc A (4 * A) ∧
    liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop = A ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop = 4 * A ∧
    (¬ ∃ c, Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop (𝓝 c)) ∧
    (∀ ε > 0, nThr q ε k₀ m₀ = 2 ^ (⌈Real.logb 4 (A / ε)⌉).toNat) := by
  have hab := cL_lt_cR k₀ m₀
  have hK : cellIcc k₀ m₀ = Icc (cL k₀ m₀) (cR k₀ m₀) := cellIcc_eq k₀ m₀
  rw [hK] at hq hκq
  have hQ := extF_contDiff hab hq
  have hQκ : ∀ x ∈ cellIcc k₀ m₀, deriv (deriv (extF q (cL k₀ m₀) (cR k₀ m₀))) x = κ := by
    intro x hx
    rw [hK] at hx
    rw [deriv2_extF hab hq, extF2_eq_comp hab, clamp_of_mem hx]
    exact hκq x hx
  have heq : EqOn (extF q (cL k₀ m₀) (cR k₀ m₀)) q (cellIcc k₀ m₀) := fun x hx =>
    extF_of_mem (by rw [hK] at hx; exact hx)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := quadratic_dyadic_constant hQ hκ hQκ hA
  have hE : ∀ N, Edia (extF q (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ N = Edia q k₀ m₀ N := Edia_congr heq
  have hT : ∀ ε, nThr (extF q (cL k₀ m₀) (cR k₀ m₀)) ε k₀ m₀ = nThr q ε k₀ m₀ := nThr_congr heq
  simp only [hE, hT] at h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Pendencias
