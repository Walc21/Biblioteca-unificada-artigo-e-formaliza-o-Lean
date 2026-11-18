import Pendencias.FaseOn

/-!
# III.12.5(i)–(ii) — o salto `Ψ_f⁺ - Ψ_f` e a descontinuidade nos átomos

`Ψ_f⁺(t) - Ψ_f(t) = ∫_{K ∩ {t + a ∈ ℤ}} √(|f''|/8) dx` (isto é, `8^{-1/2} μ_f({-t})`), e
`Ψ_f` é contínua em `t` ⟺ `t` não é fase atômica.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

/-- `{x | t + a(x) ∈ ℤ}` -/
def Sphase (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : Set ℝ :=
  {x | ∃ z : ℤ, t + aPh f k₀ m₀ x = z}

section salto

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
lemma measurableSet_Sphase (t : ℝ) : MeasurableSet (Sphase f k₀ m₀ t) := by
  have : Sphase f k₀ m₀ t = ⋃ z : ℤ, {x | t + aPh f k₀ m₀ x = z} := by
    ext x; simp [Sphase]
  rw [this]
  exact MeasurableSet.iUnion fun z =>
    measurableSet_eq_fun (measurable_const.add (aPh_measurable hf k₀ m₀)) measurable_const

include hf in
/-- **III.12.5(i)**: `Ψ_f⁺(t) - Ψ_f(t) = ∫_{K ∩ {t + a ∈ ℤ}} √(|f''|/8)` -/
theorem psiP_sub_psiF (t : ℝ) :
    PsiP f k₀ m₀ t - PsiF f k₀ m₀ t =
      ∫ x in Ioc (cL k₀ m₀) (cR k₀ m₀), (Sphase f k₀ m₀ t).indicator (wPh f) x := by
  classical
  have hab := cL_lt_cR k₀ m₀
  unfold PsiP PsiF
  rw [← intervalIntegral.integral_sub
    (integrand_intervalIntegrable hf k₀ m₀ measurable_gP abs_gP_le t)
    (integrand_intervalIntegrable hf k₀ m₀ measurable_gC abs_gC_le t),
    intervalIntegral.integral_of_le hab.le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  show wPh f x * gP (t + aPh f k₀ m₀ x) - wPh f x * gC (t + aPh f k₀ m₀ x) =
    (Sphase f k₀ m₀ t).indicator (wPh f) x
  rw [← mul_sub, gP_sub_gC]
  by_cases h : x ∈ Sphase f k₀ m₀ t
  · have h' : ∃ z : ℤ, t + aPh f k₀ m₀ x = z := h
    rw [Set.indicator_of_mem h, if_pos h']; ring
  · have h' : ¬ ∃ z : ℤ, t + aPh f k₀ m₀ x = z := h
    rw [Set.indicator_of_notMem h, if_neg h']; ring

include hf in
/-- `t` é fase atômica ⟺ `Ψ_f(t) < Ψ_f⁺(t)` -/
theorem isAtomPhase_iff_gap (t : ℝ) :
    IsAtomPhase f k₀ m₀ t ↔ PsiF f k₀ m₀ t < PsiP f k₀ m₀ t := by
  have hab := cL_lt_cR k₀ m₀
  set μ : Measure ℝ := volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀)) with hμ
  have hS := measurableSet_Sphase hf k₀ m₀ t
  have hW : MeasurableSet {x : ℝ | 0 < wPh f x} :=
    measurableSet_lt measurable_const (wPh_continuous hf).measurable
  have hwint : Integrable (wPh f) μ :=
    (wPh_continuous hf).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : Integrable ((Sphase f k₀ m₀ t).indicator (wPh f)) μ := hwint.indicator hS
  have hnn : 0 ≤ᵐ[μ] (Sphase f k₀ m₀ t).indicator (wPh f) :=
    Eventually.of_forall fun x => Set.indicator_nonneg (fun y _ => wPh_nonneg f y) x
  have hsupp : Function.support ((Sphase f k₀ m₀ t).indicator (wPh f)) =
      Sphase f k₀ m₀ t ∩ {x | 0 < wPh f x} := by
    rw [Set.support_indicator]
    congr 1
    ext x
    simp only [Function.mem_support, mem_setOf_eq]
    exact ⟨fun h => lt_of_le_of_ne (wPh_nonneg f x) (Ne.symm h), fun h => h.ne'⟩
  have key : 0 < ∫ x, (Sphase f k₀ m₀ t).indicator (wPh f) x ∂μ ↔ IsAtomPhase f k₀ m₀ t := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint, hsupp]
    unfold IsAtomPhase atomMeasure
    rw [Measure.restrict_apply' hW]
    rfl
  rw [← key, show PsiF f k₀ m₀ t < PsiP f k₀ m₀ t ↔ 0 < PsiP f k₀ m₀ t - PsiF f k₀ m₀ t from
    sub_pos.symm, psiP_sub_psiF hf k₀ m₀ t]

include hf in
/-- **III.12.5(ii)**: `Ψ_f` contínua em `t` ⟺ `t` não é fase atômica -/
theorem continuousAt_psiF_iff (t : ℝ) :
    ContinuousAt (PsiF f k₀ m₀) t ↔ ¬ IsAtomPhase f k₀ m₀ t := by
  constructor
  · intro hc hat
    have h1 : Tendsto (PsiF f k₀ m₀) (𝓝[>] t) (𝓝 (PsiF f k₀ m₀ t)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 := psiF_tendsto_right hf k₀ m₀ t
    have := tendsto_nhds_unique h2 h1
    have hgap := (isAtomPhase_iff_gap hf k₀ m₀ t).mp hat
    linarith
  · exact continuousAt_psiF_of_not_atom hf k₀ m₀

end salto

section on

variable {f : ℝ → ℝ} {k₀ : ℕ} {m₀ : ℤ}

/-- versão `C²(K)` -/
theorem isAtomPhaseOn_iff_gap (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    IsAtomPhaseOn f k₀ m₀ t ↔ PsiFOn f k₀ m₀ t < PsiPOn f k₀ m₀ t := by
  have := isAtomPhase_iff_gap (extF_cell_contDiff hf) k₀ m₀ t
  rwa [psiFOn_eq hf, psiPOn_eq hf] at this

theorem continuousAt_psiFOn_iff (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    ContinuousAt (PsiFOn f k₀ m₀) t ↔ ¬ IsAtomPhaseOn f k₀ m₀ t := by
  have := continuousAt_psiF_iff (extF_cell_contDiff hf) k₀ m₀ t
  rwa [psiFOn_funext hf] at this

end on

end Pendencias
