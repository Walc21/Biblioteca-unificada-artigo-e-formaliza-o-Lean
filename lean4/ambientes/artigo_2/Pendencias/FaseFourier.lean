import Pendencias.FaseSalto

/-!
# III.12.5(iii) — coeficientes de Fourier de `Ψ_f`

`ĝ(m) = ∫₀¹ g(u) e^{-2πimu} du = 1/(ln 2 + 2πim)` e, por Fubini,
`∫₀¹ Ψ_f(t) e^{-2πimt} dt = ĝ(m) · ∫_K √(|f''|/8) e^{2πim a(x)} dx`.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo
open scoped Real

/-- `e^{-2πimu}` -/
noncomputable def eF (m : ℤ) (u : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * m * u))

lemma eF_add_one (m : ℤ) (u : ℝ) : eF m (u + 1) = eF m u := by
  unfold eF
  have : -(2 * (Real.pi : ℂ) * Complex.I * m * ((u + 1 : ℝ) : ℂ)) =
      -(2 * (Real.pi : ℂ) * Complex.I * m * u) + ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma eF_norm (m : ℤ) (u : ℝ) : ‖eF m u‖ = 1 := by
  unfold eF
  rw [Complex.norm_exp]
  simp

lemma eF_shift (m : ℤ) (t b : ℝ) :
    eF m t = eF m (t + b) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * b) := by
  unfold eF
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma eF_continuous (m : ℤ) : Continuous (eF m) := by
  unfold eF; fun_prop

/-- coeficiente de Fourier de `g` -/
theorem integral_gC_eF (m : ℤ) :
    ∫ u in (0 : ℝ)..1, (gC u : ℂ) * eF m u =
      1 / ((Real.log 2 : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * m) := by
  set α : ℂ := (Real.log 2 : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * m with hα
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hα0 : α ≠ 0 := by
    intro h
    have h2 : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)).re = 0 := by simp
    have h3 : α.re = Real.log 2 := by
      rw [hα, Complex.add_re, Complex.ofReal_re, h2, add_zero]
    rw [h, Complex.zero_re] at h3
    linarith
  have hint : ∀ u ∈ Ioc (0 : ℝ) 1, (gC u : ℂ) * eF m u = 2 * Complex.exp (-α * u) := by
    intro u hu
    have hc : ⌈u⌉ = 1 := by
      rw [Int.ceil_eq_iff]; constructor <;> simp <;> linarith [hu.1, hu.2]
    have h1 : gC u = 2 * Real.exp (-(Real.log 2) * u) := by
      unfold gC
      rw [hc, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      push_cast
      rw [show Real.log 2 * ((1 : ℝ) - u) = Real.log 2 + (-(Real.log 2) * u) by ring,
        Real.exp_add, Real.exp_log (by norm_num)]
    rw [h1]
    unfold eF
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hα]; ring
  rw [intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_fun measurableSet_Ioc hint,
    ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => -(2 / α) * Complex.exp (-α * u))
      (2 * Complex.exp (-α * u)) u := fun u => by
    have h1 : HasDerivAt (fun w : ℂ => -(2 / α) * Complex.exp (-α * w))
        (-(2 / α) * (Complex.exp (-α * (u : ℂ)) * (-α * 1))) (u : ℂ) :=
      (((hasDerivAt_id' (u : ℂ)).const_mul (-α)).cexp).const_mul (-(2 / α))
    have h2 := h1.comp_ofReal
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hexp : Complex.exp (-α) = 1 / 2 := by
    rw [hα]
    have : -((Real.log 2 : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * m) =
        -(Real.log 2 : ℂ) + ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_neg,
      ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    push_cast; norm_num
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_one, mul_one]
  rw [hexp]
  field_simp
  ring

lemma integral_gC_eF_shift (m : ℤ) (b : ℝ) :
    ∫ t in (0 : ℝ)..1, (gC (t + b) : ℂ) * eF m t =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * b) *
        ∫ u in (0 : ℝ)..1, (gC u : ℂ) * eF m u := by
  have h1 : ∀ t : ℝ, (gC (t + b) : ℂ) * eF m t =
      ((gC (t + b) : ℂ) * eF m (t + b)) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * b) := by
    intro t; rw [mul_assoc, ← eF_shift]
  simp_rw [h1]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_comp_add_right (fun u => (gC u : ℂ) * eF m u) b]
  have hper : Function.Periodic (fun u : ℝ => (gC u : ℂ) * eF m u) 1 := fun u => by
    simp only [gC_add_one, eF_add_one]
  rw [show (0 : ℝ) + b = b by ring, show (1 : ℝ) + b = b + 1 by ring,
    hper.intervalIntegral_add_eq b 0, zero_add, mul_comm]

section fourier

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
/-- **III.12.5(iii)**: coeficientes de Fourier de `Ψ_f` -/
theorem fourier_psiF (m : ℤ) :
    ∫ t in (0 : ℝ)..1, (PsiF f k₀ m₀ t : ℂ) * eF m t =
      (1 / ((Real.log 2 : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * m)) *
        ∫ x in cL k₀ m₀..cR k₀ m₀, (wPh f x : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * aPh f k₀ m₀ x) := by
  obtain ⟨Cw, hCw⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (wPh_continuous hf).continuousOn (s := Icc (cL k₀ m₀) (cR k₀ m₀))
  set F : ℝ × ℝ → ℂ := fun p =>
    (wPh f p.2 : ℂ) * (gC (p.1 + aPh f k₀ m₀ p.2) : ℂ) * eF m p.1 with hF
  have hmeas : Measurable F := by
    refine (Complex.measurable_ofReal.comp ((wPh_continuous hf).measurable.comp
      measurable_snd)).mul ?_ |>.mul ?_
    · exact Complex.measurable_ofReal.comp (measurable_gC.comp
        (measurable_fst.add ((aPh_measurable hf k₀ m₀).comp measurable_snd)))
    · exact (eF_continuous m).measurable.comp measurable_fst
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
    rw [hF]
    simp only [norm_mul, Complex.norm_real, eF_norm, mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (wPh_nonneg f _)]
    exact mul_le_mul h1 (abs_gC_le _) (abs_nonneg _) (le_trans (wPh_nonneg f _) h1)
  have hswap := integral_integral_swap
    (f := fun t x => (wPh f x : ℂ) * (gC (t + aPh f k₀ m₀ x) : ℂ) * eF m t) hint
  have hL : ∫ t in (0 : ℝ)..1, (PsiF f k₀ m₀ t : ℂ) * eF m t =
      ∫ t in Ioc (0 : ℝ) 1, ∫ x in Ioc (cL k₀ m₀) (cR k₀ m₀),
        (wPh f x : ℂ) * (gC (t + aPh f k₀ m₀ x) : ℂ) * eF m t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    unfold PsiF
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const,
      intervalIntegral.integral_of_le hab.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [Complex.ofReal_mul]
  rw [hL, hswap]
  have hinner : ∀ x, ∫ t in Ioc (0 : ℝ) 1, (wPh f x : ℂ) * (gC (t + aPh f k₀ m₀ x) : ℂ) * eF m t =
      (wPh f x : ℂ) * (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * aPh f k₀ m₀ x) *
        ∫ u in (0 : ℝ)..1, (gC u : ℂ) * eF m u) := by
    intro x
    have e1 : ∫ t in Ioc (0 : ℝ) 1, (wPh f x : ℂ) * (gC (t + aPh f k₀ m₀ x) : ℂ) * eF m t =
        ∫ t in Ioc (0 : ℝ) 1, (wPh f x : ℂ) * ((gC (t + aPh f k₀ m₀ x) : ℂ) * eF m t) := by
      congr 1; funext t; exact mul_assoc _ _ _
    rw [e1, integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_gC_eF_shift]
  simp only [hinner]
  rw [← intervalIntegral.integral_of_le hab.le, integral_gC_eF m]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

end fourier

end Pendencias
