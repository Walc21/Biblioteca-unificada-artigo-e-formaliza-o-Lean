import Pendencias.AlturaInversa

open Pendencias.Marcada.AlturaInversa

#print axioms Hcan_le
#print axioms reverse_height_bit_bound
#print axioms affineW_Hcan_ge
#print axioms no_additive_constant_fix

/-- o enunciado corrigido contém o caso do contraexemplo `R(x)=x` (`M=0,D=0,W=1`). -/
example : Real.logb 2 (((Pendencias.Marcada.AlturaInversa.affineW 1).Hcan : ℕ) : ℝ) ≤
    5 * ((((Pendencias.Marcada.AlturaInversa.affineW 1).data.length : ℕ) + 1 : ℝ) *
      Real.logb 2 (2 * ((1 : ℕ) : ℝ)) + ((0 : ℕ) : ℝ) +
      Real.logb 2 ((((Pendencias.Marcada.AlturaInversa.affineW 1).data.length : ℕ) : ℝ) + 1)) :=
  reverse_height_bit_bound _ 1 0 (affineW_hip 1 le_rfl)
