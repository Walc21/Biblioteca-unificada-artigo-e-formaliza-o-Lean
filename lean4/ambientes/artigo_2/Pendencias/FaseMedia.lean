import Pendencias.FaseLei5

/-!
# III.12.5(iii) — a média de `Ψ_f`

`∫₀¹ g(t + b) dt = 1/ln 2` para todo `b`, e `∫₀¹ Ψ_f = I(f)/(√8 ln 2)` (Fubini).
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

lemma integral_two_rpow_one_sub :
    ∫ u in (0 : ℝ)..1, (2 : ℝ) ^ (1 - u) = 1 / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => -((2 : ℝ) ^ (1 - u)) / Real.log 2)
      ((2 : ℝ) ^ (1 - u)) u := fun u => by
    have h2 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := (hasDerivAt_id u).const_sub 1
    have h3 := (HasDerivAt.const_rpow (by norm_num : (0 : ℝ) < 2) h2).neg.div_const (Real.log 2)
    convert h3 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (Continuous.intervalIntegrable (Real.continuous_const_rpow (by norm_num) |>.comp (continuous_const.sub continuous_id)) _ _)]
  simp only [sub_self, Real.rpow_zero, Real.rpow_one]
  rw [show (2 : ℝ) ^ (1 - 0 : ℝ) = 2 by norm_num]
  field_simp
  ring

lemma integral_gC_period : ∫ u in (0 : ℝ)..1, gC u = 1 / Real.log 2 := by
  rw [← integral_two_rpow_one_sub, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have : ⌈u⌉ = 1 := by
    rw [Int.ceil_eq_iff]; constructor <;> simp <;> linarith [hu.1, hu.2]
  simp [gC, this]

lemma integral_gC_shift (b : ℝ) : ∫ t in (0 : ℝ)..1, gC (t + b) = 1 / Real.log 2 := by
  rw [intervalIntegral.integral_comp_add_right (fun u => gC u) b]
  have hper : Function.Periodic gC 1 := fun u => gC_add_one u
  rw [show (0 : ℝ) + b = b by ring, show (1 : ℝ) + b = b + 1 by ring,
    hper.intervalIntegral_add_eq b 0, zero_add]
  exact integral_gC_period

section media

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
/-- **III.12.5(iii), média**: `∫₀¹ Ψ_f = I(f)/(√8 ln 2)` -/
theorem integral_psiF :
    ∫ t in (0 : ℝ)..1, PsiF f k₀ m₀ t = curvI f k₀ m₀ / (Real.sqrt 8 * Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Cw, hCw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (wPh_continuous hf).continuousOn (s := Icc (cL k₀ m₀) (cR k₀ m₀))
  set F : ℝ × ℝ → ℝ := fun p => wPh f p.2 * gC (p.1 + aPh f k₀ m₀ p.2) with hF
  have hmeas : Measurable F :=
    ((wPh_continuous hf).measurable.comp measurable_snd).mul
      (measurable_gC.comp (measurable_fst.add ((aPh_measurable hf k₀ m₀).comp measurable_snd)))
  have hab := cL_lt_cR k₀ m₀
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  haveI : IsFiniteMeasure (volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))) := ⟨by simp⟩
  have hint : Integrable F ((volume.restrict (Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀)))) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Cw * 2) ?_
    rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_
    have h1 := hCw p.2 (Ioc_subset_Icc_self hp.2)
    rw [Real.norm_eq_abs, abs_of_nonneg (wPh_nonneg f _)] at h1
    rw [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg (wPh_nonneg f _)]
    exact mul_le_mul h1 (abs_gC_le _) (abs_nonneg _) (le_trans (wPh_nonneg f _) h1)
  have hswap := integral_integral_swap (f := fun t x => wPh f x * gC (t + aPh f k₀ m₀ x)) hint
  unfold PsiF
  simp only [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hab.le]
  rw [hswap]
  have : ∀ x, ∫ t in Ioc (0 : ℝ) 1, wPh f x * gC (t + aPh f k₀ m₀ x) = wPh f x / Real.log 2 := by
    intro x
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_gC_shift]
    field_simp
  simp only [this]
  rw [integral_div, ← intervalIntegral.integral_of_le hab.le, integral_wPh (f := f) k₀ m₀]
  field_simp

end media

end Pendencias
