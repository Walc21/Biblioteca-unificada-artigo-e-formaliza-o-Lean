module

public import Unified.Fase3.IntervalArith

/-!
# Lema 6.1 — rotinas de intervalos racionais para `exp`, `sin`, `cos`

O texto afirma: se `I = [a,b]` tem extremos racionais, as rotinas produzem intervalos de extremos
racionais que contêm `exp(I)`, `sin(I)` e `cos(I)`, com as cotas racionais (37) e (38).

* (37) forma racional: para `0 ≤ z ≤ 1/2` racional, `0 ≤ e^z − T_n(z) ≤ R_n(z)`, com `T_n`
  e `R_n` as quantidades racionais `expTaylorQ` e `expRemQ` que a rotina efetivamente calcula.
* (38) e a conclusão de inclusão são as propriedades de `expEncl`, `sinEncl` e `cosEncl`.
-/

namespace Fase3

open Iv

/-- Forma racional de (37): a soma de Taylor e o resto geométrico, ambos racionais. -/
public theorem lemma61_exp_rational (P : ℕ) (z : ℚ) (h0 : 0 ≤ z) (h1 : z ≤ 1 / 2) :
    0 ≤ Real.exp (z : ℝ) - ((expTaylorQ P z : ℚ) : ℝ) ∧
      Real.exp (z : ℝ) - ((expTaylorQ P z : ℚ) : ℝ) ≤ ((expRemQ P z : ℚ) : ℝ) := by
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h0
  have hz1 : (z : ℝ) ≤ 1 / 2 := by
    have : (z : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast h1
    simpa using this
  obtain ⟨b1, b2⟩ := exp_sub_expPoly_bounds hz0 hz1 P
  rw [expTaylorQ_cast, expRemQ_cast]
  exact ⟨b1, b2⟩

/-- Inclusão: para todo `x ∈ A` (com `A` de extremos racionais), as três rotinas contêm
`e^x`, `sin x` e `cos x`. -/
public theorem lemma61_enclosures (P : ℕ) (A : Iv) {x : ℝ} (hx : A.Mem x) :
    (expEncl P A).Mem (Real.exp x) ∧ (sinEncl P A).Mem (Real.sin x) ∧
      (cosEncl P A).Mem (Real.cos x) :=
  ⟨expEncl_mem P hx, sinEncl_mem P hx, cosEncl_mem P hx⟩

end Fase3
