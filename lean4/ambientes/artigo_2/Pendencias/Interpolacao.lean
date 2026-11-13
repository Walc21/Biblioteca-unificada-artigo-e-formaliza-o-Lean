import RequestProject.Interp
import Pendencias.Extensao

/-!
# III.2.3 — cota de interpolação com `f ∈ C²(J)` só no intervalo

O Lean existente (`Artigo.interp_remainder_C2`) exige `ContDiff ℝ 2 f` na reta.
Aqui a hipótese é `ContDiffOn ℝ 2 f (Icc a b)` e a cota usa a segunda derivada
unilateral `derivWithin (derivWithin f [a,b]) [a,b]`. A prova aplica a versão global
à extensão `Pendencias.extF`, que coincide com `f` em `[a,b]`.
A densidade (`Artigo.assemblies_dense`) e a forma ReLU (`Artigo.LTree.eval_relu_form`)
já batiam com o texto.
-/

namespace Pendencias

open Set Artigo

/-- **Proposição III.2.3** (cota de interpolação, hipótese `C²(J)`). -/
theorem interp_remainder_C2On {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Icc a b))
    (hM : ∀ x ∈ Icc a b, |derivWithin (derivWithin f (Icc a b)) (Icc a b) x| ≤ M) :
    ∀ x ∈ Icc a b, |f x - linInterp f a b x| ≤ (b - a) ^ 2 / 8 * M := by
  intro x hx
  have h := interp_remainder_C2 (extF_contDiff hab hf) hab (M := M) (fun y hy => by
    rw [deriv2_extF hab hf, extF2_eq_comp hab, clamp_of_mem hy]
    exact hM y hy) x hx
  unfold linInterp at h ⊢
  rw [extF_of_mem hx, extF_of_mem (left_mem_Icc.2 hab.le),
    extF_of_mem (right_mem_Icc.2 hab.le)] at h
  exact h

end Pendencias
