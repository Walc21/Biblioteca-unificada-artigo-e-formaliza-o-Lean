import Pendencias.Marcada
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Diagnóstico da cota inversa de IV.5.4

O TeX não exclui a forma reduzida sem hinges. Para `R(x) = x`, os dados são
`M = 0`, `W = 1`, `D = 0`, e `H_can = 2`. Logo o lado direito da desigualdade
(reverse-height-bit-bound) é zero para toda constante universal, mas o esquerdo é 1.
Este arquivo certifica o contraexemplo; não fecha IV.5.4 nem altera seu enunciado.

Reproduzir no ambiente artigo_2:
`lake env lean ../../../verificacao/lean/ContraexemploAltura.lean`.
-/

open Pendencias.Marcada

namespace DiagnosticoAltura

/-- A forma reduzida (reduced-relu-reverse) com `c=0`, `q=1` e soma vazia, isto é, `R(x)=x`. -/
def affine : RedReLU := ⟨0, 1, []⟩

theorem affine_eval (x : ℚ) : affine.evalQ x = x := by
  simp [affine, RedReLU.evalQ]

theorem affine_parameters :
    Artigo.ht affine.c ≤ 1 ∧ Artigo.ht affine.q ≤ 1 ∧
      affine.data.length = 0 ∧ affine.depth = 0 := by
  norm_num [affine, Artigo.ht, RedReLU.depth, RedReLU.breaks]

theorem affine_height : affine.Hcan = 2 := by
  norm_num [affine, RedReLU.Hcan, RedReLU.depth, RedReLU.breaks, canonShape,
    RedReLU.hShape, RedReLU.evalQ, RedReLU.slopeAt, Artigo.ht]

theorem affine_refutes_bound (C : ℝ) :
    ¬ Real.logb 2 (affine.Hcan : ℝ) ≤
      C * ((0 : ℝ) * Real.log (2 * 1) + 0 + Real.log (0 + 1)) := by
  rw [affine_height]
  norm_num [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]

#print axioms affine_eval
#print axioms affine_parameters
#print axioms affine_height
#print axioms affine_refutes_bound
end DiagnosticoAltura
