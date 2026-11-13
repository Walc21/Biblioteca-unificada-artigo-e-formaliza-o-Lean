module
public import Unified.Fase3.Assembly

/-!
# Observation 6.6: second difference and the error at the centre
-/

@[expose] public section

namespace Fase3

open Set

/-- **Observation 6.6.** At the centre `x₀ = (x_L + x_R)/2` the interpolation error equals half
the central second difference: `|f(x₀) - P_J f(x₀)| = ½ |f(x_L) - 2 f(x₀) + f(x_R)|`. -/
theorem center_error_eq (f : ℝ → ℝ) {xL xR : ℝ} (h : xL ≠ xR) :
    |f ((xL + xR) / 2) - linInterp xL xR (f xL) (f xR) ((xL + xR) / 2)| =
      1 / 2 * |f xL - 2 * f ((xL + xR) / 2) + f xR| := by
  have hne : xR - xL ≠ 0 := sub_ne_zero.2 h.symm
  have : f ((xL + xR) / 2) - linInterp xL xR (f xL) (f xR) ((xL + xR) / 2) =
      -(1 / 2) * (f xL - 2 * f ((xL + xR) / 2) + f xR) := by
    unfold linInterp; field_simp; ring
  rw [this, abs_mul]; norm_num

/-- **Observation 6.6, example.** For `f(x) = x³` on `[-1, 1]`: `P_J f(x) = x`, the central
second difference vanishes, but `‖x³ - x‖_{∞,[-1,1]} = 2/(3√3)`. -/
theorem cube_example :
    (∀ x, linInterp (-1) 1 ((-1) ^ 3) (1 ^ 3) x = x) ∧
    ((-1 : ℝ) ^ 3 - 2 * 0 ^ 3 + 1 ^ 3 = 0) ∧
    supNormOn (Icc (-1) 1) (fun x => x ^ 3 - x) = 2 / (3 * Real.sqrt 3) := by
  refine ⟨fun x => by unfold linInterp; ring, by norm_num, ?_⟩
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := by positivity
  set s := 1 / Real.sqrt 3 with hs
  have hs2 : s ^ 2 = 1 / 3 := by rw [hs, div_pow, h3]; norm_num
  have hspos : 0 < s := by positivity
  have hs1 : 2 * s > 1 := by
    have : (2 * s) ^ 2 > 1 := by nlinarith
    nlinarith
  have hval : 2 / (3 * Real.sqrt 3) = 2 * s ^ 3 := by
    rw [hs, div_pow, one_pow, pow_succ, h3]; ring
  have hsl : s < 1 := by nlinarith
  rw [hval]
  apply le_antisymm
  · refine supNormOn_le ⟨0, by norm_num, by norm_num⟩ ?_
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    rw [abs_le]
    constructor
    · have : 0 ≤ (x - s) ^ 2 * (x + 2 * s) := mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith
    · have : 0 ≤ (x + s) ^ 2 * (2 * s - x) := mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith
  · have hmem : -s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hbd : ∀ x ∈ Icc (-1 : ℝ) 1, |x ^ 3 - x| ≤ 2 := by
      intro x hx
      obtain ⟨h1, h2⟩ := hx
      have : |x| ≤ 1 := abs_le.2 ⟨h1, h2⟩
      calc |x ^ 3 - x| ≤ |x ^ 3| + |x| := abs_sub _ _
        _ = |x| ^ 3 + |x| := by rw [abs_pow]
        _ ≤ 1 + 1 := by gcongr; exact pow_le_one₀ (abs_nonneg x) this
        _ = 2 := by norm_num
    have := le_supNormOn hbd hmem
    have e : (-s) ^ 3 - -s = 2 * s ^ 3 := by nlinarith
    simp only at this
    rw [e, abs_of_pos (by positivity)] at this
    exact this

end Fase3
