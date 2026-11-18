import Pendencias.FaseLei2

/-!
# III.12.7 — a lei de fase (cotas inferior e superior)
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo DShape

section assembly

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

lemma wPh_eq (x : ℝ) : wPh f x = sqc f x / Real.sqrt 8 := by
  unfold wPh sqc
  rw [Real.sqrt_div (abs_nonneg _)]

lemma aPh_eq (x : ℝ) :
    aPh f k₀ m₀ x = Real.logb 4 (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * (sqc f x) ^ 2 / 8) := by
  unfold aPh
  rw [cell_len, sqc_sq]

lemma cell_of_mem {d : ℕ} {x : ℝ} (hx : x ∈ Ioc (cL k₀ m₀) (cR k₀ m₀)) :
    cidx (k₀ + d) x / 2 ^ d = m₀ ∧ x ∈ cellIcc (k₀ + d) (cidx (k₀ + d) x) := by
  refine ⟨cidx_mem hx, ?_⟩
  have := (cidx_eq_iff (k₀ + d) (cidx (k₀ + d) x) x).mp rfl
  rw [cellIcc_eq]
  exact ⟨this.1.le, this.2⟩

include hf in
lemma sLow_tendsto {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {x : ℝ}
    (hx : x ∈ Ioc (cL k₀ m₀) (cR k₀ m₀)) :
    Tendsto (fun j => sLow hf k₀ m₀ (φ j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x)) atTop
      (𝓝 (sqc f x)) := by
  have hb : Tendsto (fun j => 2 * etaN (φ j)) atTop (𝓝 0) := by
    simpa using (etaN_tendsto.comp hφ).const_mul 2
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun j => ?_) hb
  obtain ⟨h1, h2⟩ := cell_of_mem k₀ m₀ (d := depthN hf k₀ m₀ (φ j)) hx
  exact sLow_close hf k₀ m₀ h1 h2

include hf in
lemma sUp_tendsto {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {x : ℝ}
    (hx : x ∈ Ioc (cL k₀ m₀) (cR k₀ m₀)) :
    Tendsto (fun j => sUp hf k₀ m₀ (φ j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x)) atTop
      (𝓝 (sqc f x)) := by
  have hb : Tendsto (fun j => 2 * etaN (φ j)) atTop (𝓝 0) := by
    simpa using (etaN_tendsto.comp hφ).const_mul 2
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun j => ?_) hb
  obtain ⟨h1, h2⟩ := cell_of_mem k₀ m₀ (d := depthN hf k₀ m₀ (φ j)) hx
  exact sUp_close hf k₀ m₀ h1 h2

include hf in
/-- **III.12.7, cota inferior** -/
theorem phase_lower {ε : ℕ → ℝ} (hε0 : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    {z : ℕ → ℤ} {τ : ℝ}
    (hz : Tendsto (fun j => -Real.logb 4 (ε j) - z j) atTop (𝓝 τ)) :
    ∀ δ > 0, ∀ᶠ j in atTop, PsiF f k₀ m₀ τ - δ < Real.sqrt (ε j) * nThr f (ε j) k₀ m₀ := by
  choose thr hthr hbound using fun n => lower_integral_bound hf k₀ m₀ n
  obtain ⟨φ, hφ, hPφ⟩ := exists_diag (fun n j => ε j < thr n)
    (fun n => hε.eventually (gt_mem_nhds (hthr n)))
  intro δ hδ
  have hfat := fatou_eventually (cL_lt_cR k₀ m₀).le
    (F := fun j x => Gl hf k₀ m₀ (φ j) (ε j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x))
    (G := fun x => wPh f x * gC (τ + aPh f k₀ m₀ x))
    (fun j => measurable_step _ _)
    (fun j x _ => by
      unfold Gl
      exact mul_nonneg (div_nonneg (sLow_nonneg hf k₀ m₀ _ _) (Real.sqrt_nonneg _)) (gC_nonneg _))
    (fun x _ => mul_nonneg (wPh_nonneg f x) (gC_nonneg _))
    (integrand_measurable hf k₀ m₀ measurable_gC τ)
    (integrand_intervalIntegrable hf k₀ m₀ measurable_gC abs_gC_le τ)
    (fun j => step_intervalIntegrable k₀ m₀ _ _)
    (fun x hx δ' hδ' => by
      have h := pointwise_lower (L := ((2 : ℝ) ^ k₀)⁻¹) (by positivity)
        (s := fun j => sLow hf k₀ m₀ (φ j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x))
        (sLim := sqc f x) (fun j => sLow_nonneg hf k₀ m₀ _ _)
        (sLow_tendsto hf k₀ m₀ hφ hx) (T := fun j => -Real.logb 4 (ε j)) hz δ' hδ'
      filter_upwards [h] with j hj
      rw [wPh_eq, aPh_eq]
      unfold Gl
      exact hj) δ hδ
  filter_upwards [hfat, hPφ] with j hj hlt
  have := hbound (φ j) (ε j) (hε0 j) hlt
  unfold PsiF
  linarith

include hf in
/-- **III.12.7, cota superior** -/
theorem phase_upper {ε : ℕ → ℝ} (hε0 : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    {z : ℕ → ℤ} {τ : ℝ}
    (hz : Tendsto (fun j => -Real.logb 4 (ε j) - z j) atTop (𝓝 τ)) :
    ∀ δ > 0, ∀ᶠ j in atTop, Real.sqrt (ε j) * nThr f (ε j) k₀ m₀ < PsiP f k₀ m₀ τ + δ := by
  have hsqrt : Tendsto (fun j => Real.sqrt (ε j)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hε
  obtain ⟨φ, hφ, hPφ⟩ := exists_diag
    (fun n j => 2 ^ (depthN hf k₀ m₀ n) * Real.sqrt (ε j) ≤ etaN n) (fun n => by
      have := hsqrt.const_mul ((2 : ℝ) ^ (depthN hf k₀ m₀ n))
      rw [mul_zero] at this
      exact (this.eventually (gt_mem_nhds (etaN_pos n))).mono fun j hj => hj.le)
  obtain ⟨Cs, hCs⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (sqc_continuous hf).continuousOn (s := Icc (cL k₀ m₀) (cR k₀ m₀))
  have h8 : 0 < Real.sqrt 8 := by positivity
  have hCs' : ∀ x ∈ Ioc (cL k₀ m₀) (cR k₀ m₀), sqc f x ≤ Cs := fun x hx => by
    have := hCs x (Ioc_subset_Icc_self hx)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sqc_nonneg f x)] at this
  set B : ℝ := 2 * (Cs + 2) / Real.sqrt 8 with hB
  intro δ hδ
  have hrev := rev_fatou_eventually (cL_lt_cR k₀ m₀).le (B := B)
    (F := fun j x => Gu hf k₀ m₀ (φ j) (ε j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x))
    (G := fun x => wPh f x * gP (τ + aPh f k₀ m₀ x))
    (fun j => measurable_step _ _)
    (fun j x hx => by
      obtain ⟨h1, h2⟩ := cell_of_mem k₀ m₀ (d := depthN hf k₀ m₀ (φ j)) hx
      have hcl := sUp_close hf k₀ m₀ h1 h2
      have hsU : sUp hf k₀ m₀ (φ j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x) ≤ Cs + 2 := by
        have := (abs_le.mp hcl).2
        linarith [hCs' x hx, etaN_le_one (φ j)]
      unfold Gu
      have hg := gC_lt_two (-Real.logb 4 (ε j) + Real.logb 4
        (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * (sUp hf k₀ m₀ (φ j)
          (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x)) ^ 2 / 8))
      have hs0 := (sUp_pos hf k₀ m₀ (φ j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x)).le
      have hdiv : sUp hf k₀ m₀ (φ j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x) / Real.sqrt 8 ≤
          (Cs + 2) / Real.sqrt 8 := div_le_div_of_nonneg_right hsU h8.le
      rw [hB, mul_div_assoc]
      nlinarith [gC_nonneg (-Real.logb 4 (ε j) + Real.logb 4
        (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * (sUp hf k₀ m₀ (φ j)
          (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x)) ^ 2 / 8)), div_nonneg hs0 h8.le])
    (integrand_measurable hf k₀ m₀ measurable_gP τ)
    (fun x hx => by
      have hg := gP_le_two (τ + aPh f k₀ m₀ x)
      have hw : wPh f x ≤ Cs / Real.sqrt 8 := by
        rw [wPh_eq]; exact div_le_div_of_nonneg_right (hCs' x hx) h8.le
      have hCs0 : 0 ≤ Cs := le_trans (sqc_nonneg f x) (hCs' x hx)
      rw [hB]
      have : Cs / Real.sqrt 8 ≤ (Cs + 2) / Real.sqrt 8 :=
        div_le_div_of_nonneg_right (by linarith) h8.le
      nlinarith [wPh_nonneg f x, gP_nonneg (τ + aPh f k₀ m₀ x), mul_div_assoc 2 (Cs + 2) (Real.sqrt 8)])
    (integrand_intervalIntegrable hf k₀ m₀ measurable_gP abs_gP_le τ)
    (fun j => step_intervalIntegrable k₀ m₀ _ _)
    (fun x hx δ' hδ' => by
      have h := pointwise_upper (L := ((2 : ℝ) ^ k₀)⁻¹) (by positivity)
        (s := fun j => sUp hf k₀ m₀ (φ j) (cidx (k₀ + depthN hf k₀ m₀ (φ j)) x))
        (sLim := sqc f x) (fun j => (sUp_pos hf k₀ m₀ _ _).le)
        (sUp_tendsto hf k₀ m₀ hφ hx) (T := fun j => -Real.logb 4 (ε j)) hz δ' hδ'
      filter_upwards [h] with j hj
      rw [wPh_eq, aPh_eq]
      unfold Gu
      exact hj) (δ / 2) (by linarith)
  have heta : ∀ᶠ j in atTop, etaN (φ j) < δ / 2 :=
    (etaN_tendsto.comp hφ).eventually (gt_mem_nhds (by linarith))
  filter_upwards [hrev, hPφ, heta] with j hj hP hη
  have hub := upper_integral_bound hf k₀ m₀ (φ j) (hε0 j)
  unfold PsiP
  linarith

end assembly

end Pendencias
