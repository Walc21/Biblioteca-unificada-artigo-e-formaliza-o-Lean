import Pendencias.ReversaoRacional
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Formas ReLU com parâmetros reais e quebras efetivas

Infraestrutura analítica para a necessidade na reversibilidade rasa e para a volta
quantizada. Nenhum item inteiro é declarado fechado neste módulo.
-/

noncomputable section

namespace Pendencias.Marcada

open Artigo Set Filter Finset
open scoped Topology

/-- Dados da fórmula (reduced-relu-reverse) do TeX com `M` hinges, permitindo parâmetros
reais. As condições de redução são registradas separadamente em `Reduced`. -/
structure RealReLU (M : ℕ) where
  c : ℝ
  q : ℝ
  a : Fin M → ℝ
  τ : Fin M → ℝ

namespace RealReLU

/-- A fórmula é reduzida exatamente nas condições do TeX: quebras estritamente
crescentes em `(0,1)` e saltos de inclinação não nulos. Inclui o caso afim `M=0`. -/
def Reduced {M : ℕ} (R : RealReLU M) : Prop :=
  StrictMono R.τ ∧ (∀ i, 0 < R.τ i ∧ R.τ i < 1) ∧ ∀ i, R.a i ≠ 0

/-- Avaliação da fórmula (reduced-relu-reverse) com os parâmetros reais fornecidos. -/
def eval {M : ℕ} (R : RealReLU M) (x : ℝ) : ℝ :=
  R.c + R.q * x + ∑ i, R.a i * max 0 (x - R.τ i)

/-- Inclinação em um ponto sem quebra: soma de `q` com os saltos das quebras à esquerda.
Na ordem estrita de `Reduced`, é exatamente uma das somas `σ_i` do TeX. -/
def slope {M : ℕ} (R : RealReLU M) (x : ℝ) : ℝ :=
  R.q + ∑ i, if R.τ i < x then R.a i else 0

lemma hasDerivAt_hinge {t x : ℝ} (hne : x ≠ t) :
    HasDerivAt (fun y : ℝ ↦ max 0 (y - t)) (if t < x then 1 else 0) x := by
  by_cases ht : t < x
  · rw [if_pos ht]
    apply ((hasDerivAt_id x).sub_const t).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact max_eq_right (sub_nonneg.mpr hy.le)
  · have hx : x < t := lt_of_le_of_ne (le_of_not_gt ht) hne
    rw [if_neg ht]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact max_eq_left (sub_nonpos.mpr hy.le)

lemma hasDerivAt_eval {M : ℕ} (R : RealReLU M) {x : ℝ}
    (hx : ∀ i, x ≠ R.τ i) : HasDerivAt R.eval (R.slope x) x := by
  have hs : HasDerivAt (fun y ↦ ∑ i, R.a i * max 0 (y - R.τ i))
      (∑ i, if R.τ i < x then R.a i else 0) x := by
    convert HasDerivAt.sum (u := Finset.univ)
      (fun i _ ↦ (hasDerivAt_hinge (hx i)).const_mul (R.a i)) using 1
    · funext y
      simp only [Finset.sum_apply]
    · simp only [mul_ite, mul_one, mul_zero]
  have hcq : HasDerivAt (fun y ↦ R.c + R.q * y) R.q x := by
    simpa using ((hasDerivAt_id x).const_mul R.q).const_add R.c
  simpa only [eval, slope] using hcq.add hs

lemma not_differentiableAt_hinge (t : ℝ) :
    ¬ DifferentiableAt ℝ (fun y : ℝ ↦ max 0 (y - t)) t := by
  intro h
  have htranslate : DifferentiableAt ℝ (fun y : ℝ ↦ max 0 ((y + t) - t)) 0 := by
    have ht : DifferentiableAt ℝ (fun y : ℝ ↦ max 0 (y - t)) (0 + t) := by simpa using h
    have hc := ht.comp 0
      ((differentiableAt_id : DifferentiableAt ℝ (id : ℝ → ℝ) 0).add_const t)
    exact hc
  have hz : DifferentiableAt ℝ (fun y : ℝ ↦ max 0 y) 0 := by
    simpa only [add_sub_cancel_right] using htranslate
  have habs := (hz.const_mul 2).sub differentiableAt_id
  have heq : (fun y : ℝ ↦ 2 * max 0 y - y) = (abs : ℝ → ℝ) := by
    funext y
    by_cases hy : 0 ≤ y
    · simp only [max_eq_right hy, abs_of_nonneg hy]
      ring
    · simp only [max_eq_left (le_of_not_ge hy), abs_of_nonpos (le_of_not_ge hy)]
      ring
  exact not_differentiableAt_abs_zero (heq ▸ habs)

/-- Cada hinge da forma reduzida é uma quebra efetiva: sua função não é diferenciável
naquele ponto. Os demais hinges são diferenciáveis ali por terem quebras distintas. -/
theorem not_differentiableAt_break {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (i : Fin M) :
    ¬ DifferentiableAt ℝ R.eval (R.τ i) := by
  let smooth : ℝ → ℝ := fun y ↦ R.c + R.q * y +
    ∑ j ∈ Finset.univ.erase i, R.a j * max 0 (y - R.τ j)
  have hs : DifferentiableAt ℝ smooth (R.τ i) := by
    have hsum := DifferentiableAt.sum (u := Finset.univ.erase i) (fun j hj ↦
      (hasDerivAt_hinge (show R.τ i ≠ R.τ j from fun h ↦
        (Finset.mem_erase.mp hj).1 (hR.1.injective h.symm))).differentiableAt.const_mul (R.a j))
    apply DifferentiableAt.add
    · exact (differentiableAt_const R.c).add (differentiableAt_id.const_mul R.q)
    · convert hsum using 1
      funext y
      simp only [Finset.sum_apply]
  intro h
  have ha : DifferentiableAt ℝ (fun y ↦ R.a i * max 0 (y - R.τ i)) (R.τ i) := by
    convert h.sub hs using 1
    funext y
    have hsum := Finset.sum_erase_add Finset.univ
      (fun j ↦ R.a j * max 0 (y - R.τ j)) (Finset.mem_univ i)
    change R.a i * max 0 (y - R.τ i) = R.eval y - smooth y
    dsimp only [eval, smooth]
    linarith
  apply not_differentiableAt_hinge (R.τ i)
  simpa only [← mul_assoc, inv_mul_cancel₀ (hR.2.2 i), one_mul] using
    ha.const_mul (R.a i)⁻¹

end RealReLU

end Pendencias.Marcada
