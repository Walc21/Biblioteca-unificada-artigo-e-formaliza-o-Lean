import RequestProject.DyadicEnvelope
import Pendencias.FaseNucleo

/-!
# III.12.5 — a função de fase `Ψ_f`

Para `K = J_{k₀,m₀}`, `c = |f''|`, `L = |K|` e `a(x) = log₄(L² c(x)/8)`:

* `PsiF t = ∫_K √(c/8) · gC(t + a(x)) dx` e `PsiP t = ∫_K √(c/8) · gP(t + a(x)) dx`.

Esta parte prova que são bem definidas (integrandos mensuráveis e dominados), `1`-periódicas,
limitadas por `I/√8` e `I/√2`, e calcula os limites laterais por convergência dominada.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

section defs

/-- `√(|f''|/8)` -/
noncomputable def wPh (f : ℝ → ℝ) (x : ℝ) : ℝ := Real.sqrt (|deriv (deriv f) x| / 8)

/-- `a(x) = log₄(L² |f''(x)| / 8)` com `L = |K|` -/
noncomputable def aPh (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (x : ℝ) : ℝ :=
  Real.logb 4 ((cR k₀ m₀ - cL k₀ m₀) ^ 2 * |deriv (deriv f) x| / 8)

/-- a função de fase `Ψ_f` -/
noncomputable def PsiF (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : ℝ :=
  ∫ x in cL k₀ m₀..cR k₀ m₀, wPh f x * gC (t + aPh f k₀ m₀ x)

/-- a regularização à direita `Ψ_f⁺` -/
noncomputable def PsiP (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : ℝ :=
  ∫ x in cL k₀ m₀..cR k₀ m₀, wPh f x * gP (t + aPh f k₀ m₀ x)

end defs

section basic

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

lemma wPh_nonneg (f : ℝ → ℝ) (x : ℝ) : 0 ≤ wPh f x := Real.sqrt_nonneg _

lemma wPh_continuous (hf : ContDiff ℝ 2 f) : Continuous (wPh f) :=
  ((C2_continuous_deriv2 hf).abs.div_const 8).sqrt

lemma aPh_measurable (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ) : Measurable (aPh f k₀ m₀) := by
  unfold aPh Real.logb
  have h1 : Continuous fun x => (cR k₀ m₀ - cL k₀ m₀) ^ 2 * |deriv (deriv f) x| / 8 :=
    (continuous_const.mul (C2_continuous_deriv2 hf).abs).div_const 8
  exact (Real.measurable_log.comp h1.measurable).div_const _

lemma measurable_gC : Measurable gC := by
  unfold gC
  have hceil : Measurable (fun u : ℝ => ((⌈u⌉ : ℤ) : ℝ)) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp Int.measurable_ceil
  exact Measurable.pow measurable_const (hceil.sub measurable_id)

end basic

lemma measurable_gP : Measurable gP := by
  unfold gP
  have hfl : Measurable (fun u : ℝ => ((⌊u⌋ : ℤ) : ℝ)) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp Int.measurable_floor
  exact Measurable.pow measurable_const (((hfl.add_const 1)).sub measurable_id)

section integrals

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
lemma integrand_measurable {G : ℝ → ℝ} (hG : Measurable G) (t : ℝ) :
    Measurable (fun x => wPh f x * G (t + aPh f k₀ m₀ x)) :=
  (wPh_continuous hf).measurable.mul (hG.comp (measurable_const.add (aPh_measurable hf k₀ m₀)))

include hf in
lemma integrand_intervalIntegrable {G : ℝ → ℝ} (hG : Measurable G) (hb : ∀ u, |G u| ≤ 2) (t : ℝ) :
    IntervalIntegrable (fun x => wPh f x * G (t + aPh f k₀ m₀ x)) volume (cL k₀ m₀) (cR k₀ m₀) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (cL_lt_cR k₀ m₀).le]
  have hg : IntegrableOn (fun x => 2 * wPh f x) (Ioc (cL k₀ m₀) (cR k₀ m₀)) :=
    (continuous_const.mul (wPh_continuous hf)).continuousOn.integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  refine Integrable.mono' hg (integrand_measurable hf k₀ m₀ hG t).aestronglyMeasurable ?_
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wPh_nonneg f x)]
  nlinarith [hb (t + aPh f k₀ m₀ x), wPh_nonneg f x, abs_nonneg (G (t + aPh f k₀ m₀ x))]

include hf in
/-- convergência dominada para o funcional de fase -/
lemma tendsto_phase_integral {G G' : ℝ → ℝ} (hG : Measurable G) (hb : ∀ u, |G u| ≤ 2)
    {l : Filter ℝ} [l.IsCountablyGenerated] {t : ℝ}
    (hlim : ∀ b : ℝ, Tendsto (fun r => G (r + b)) l (𝓝 (G' (t + b)))) :
    Tendsto (fun r => ∫ x in cL k₀ m₀..cR k₀ m₀, wPh f x * G (r + aPh f k₀ m₀ x)) l
      (𝓝 (∫ x in cL k₀ m₀..cR k₀ m₀, wPh f x * G' (t + aPh f k₀ m₀ x))) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => 2 * wPh f x) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun r =>
      (integrand_measurable hf k₀ m₀ hG r).aestronglyMeasurable
  · refine Eventually.of_forall fun r => Eventually.of_forall fun x _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wPh_nonneg f x)]
    nlinarith [hb (r + aPh f k₀ m₀ x), wPh_nonneg f x, abs_nonneg (G (r + aPh f k₀ m₀ x))]
  · exact (continuous_const.mul (wPh_continuous hf)).intervalIntegrable _ _
  · refine Eventually.of_forall fun x _ => ?_
    exact (hlim (aPh f k₀ m₀ x)).const_mul (wPh f x)

end integrals

lemma tendsto_add_nhdsLT (t b : ℝ) : Tendsto (fun r : ℝ => r + b) (𝓝[<] t) (𝓝[<] (t + b)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_add_right b).tendsto t).mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun r hr => by simp only [mem_Iio] at hr ⊢; linarith

lemma tendsto_add_nhdsGT (t b : ℝ) : Tendsto (fun r : ℝ => r + b) (𝓝[>] t) (𝓝[>] (t + b)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_add_right b).tendsto t).mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun r hr => by simp only [mem_Ioi] at hr ⊢; linarith

section limits

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

lemma abs_gC_le (u : ℝ) : |gC u| ≤ 2 := by
  rw [abs_of_nonneg (gC_nonneg u)]; exact (gC_lt_two u).le

lemma abs_gP_le (u : ℝ) : |gP u| ≤ 2 := by
  rw [abs_of_nonneg (gP_nonneg u)]; exact gP_le_two u

include hf in
/-- `Ψ_f` é contínua à esquerda -/
lemma psiF_tendsto_left (t : ℝ) : Tendsto (PsiF f k₀ m₀) (𝓝[<] t) (𝓝 (PsiF f k₀ m₀ t)) :=
  tendsto_phase_integral hf k₀ m₀ measurable_gC abs_gC_le (G' := gC) fun b =>
    (tendsto_gC_left (t + b)).comp
      ((tendsto_add_nhdsLT t b).mono_right (nhdsWithin_mono _ Iio_subset_Iic_self))

include hf in
/-- à direita, `Ψ_f` tende a `Ψ_f⁺` -/
lemma psiF_tendsto_right (t : ℝ) : Tendsto (PsiF f k₀ m₀) (𝓝[>] t) (𝓝 (PsiP f k₀ m₀ t)) :=
  tendsto_phase_integral hf k₀ m₀ measurable_gC abs_gC_le (G' := gP) fun b =>
    (tendsto_gC_right (t + b)).comp (tendsto_add_nhdsGT t b)

include hf in
lemma psiP_tendsto_right (t : ℝ) : Tendsto (PsiP f k₀ m₀) (𝓝[>] t) (𝓝 (PsiP f k₀ m₀ t)) :=
  tendsto_phase_integral hf k₀ m₀ measurable_gP abs_gP_le (G' := gP) fun b =>
    (tendsto_gP_right (t + b)).comp (tendsto_add_nhdsGT t b)

include hf in
lemma psiP_tendsto_left (t : ℝ) : Tendsto (PsiP f k₀ m₀) (𝓝[<] t) (𝓝 (PsiF f k₀ m₀ t)) :=
  tendsto_phase_integral hf k₀ m₀ measurable_gP abs_gP_le (G' := gC) fun b =>
    (tendsto_gP_left (t + b)).comp (tendsto_add_nhdsLT t b)

end limits

section props

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

lemma psiF_periodic (t : ℝ) : PsiF f k₀ m₀ (t + 1) = PsiF f k₀ m₀ t := by
  unfold PsiF
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [show t + 1 + aPh f k₀ m₀ x = (t + aPh f k₀ m₀ x) + 1 by ring, gC_add_one]

lemma psiP_periodic (t : ℝ) : PsiP f k₀ m₀ (t + 1) = PsiP f k₀ m₀ t := by
  unfold PsiP
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [show t + 1 + aPh f k₀ m₀ x = (t + aPh f k₀ m₀ x) + 1 by ring, gP_add_one]

lemma psiF_add_int (t : ℝ) (z : ℤ) : PsiF f k₀ m₀ (t + z) = PsiF f k₀ m₀ t := by
  unfold PsiF
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [show t + z + aPh f k₀ m₀ x = (t + aPh f k₀ m₀ x) + z by ring, gC_add_int]

lemma psiP_add_int (t : ℝ) (z : ℤ) : PsiP f k₀ m₀ (t + z) = PsiP f k₀ m₀ t := by
  unfold PsiP
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [show t + z + aPh f k₀ m₀ x = (t + aPh f k₀ m₀ x) + z by ring, gP_add_int]

/-- `∫_K √(|f''|/8) = I(f)/√8` -/
lemma integral_wPh (k₀ : ℕ) (m₀ : ℤ) :
    ∫ x in cL k₀ m₀..cR k₀ m₀, wPh f x = curvI f k₀ m₀ / Real.sqrt 8 := by
  unfold curvI wPh
  rw [← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [Real.sqrt_div (abs_nonneg _)]

include hf in
lemma psiF_ge (t : ℝ) : curvI f k₀ m₀ / Real.sqrt 8 ≤ PsiF f k₀ m₀ t := by
  rw [← integral_wPh (f := f) k₀ m₀]
  unfold PsiF
  refine intervalIntegral.integral_mono_on (cL_lt_cR k₀ m₀).le ?_ ?_ fun x _ => ?_
  · exact (wPh_continuous hf).intervalIntegrable _ _
  · exact integrand_intervalIntegrable hf k₀ m₀ measurable_gC abs_gC_le t
  · nlinarith [gC_ge_one (t + aPh f k₀ m₀ x), wPh_nonneg f x]

include hf in
lemma psiF_le_psiP (t : ℝ) : PsiF f k₀ m₀ t ≤ PsiP f k₀ m₀ t := by
  unfold PsiF PsiP
  refine intervalIntegral.integral_mono_on (cL_lt_cR k₀ m₀).le
    (integrand_intervalIntegrable hf k₀ m₀ measurable_gC abs_gC_le t)
    (integrand_intervalIntegrable hf k₀ m₀ measurable_gP abs_gP_le t) fun x _ => ?_
  nlinarith [gC_le_gP (t + aPh f k₀ m₀ x), wPh_nonneg f x]

include hf in
lemma psiP_le (t : ℝ) : PsiP f k₀ m₀ t ≤ 2 * (curvI f k₀ m₀ / Real.sqrt 8) := by
  rw [← integral_wPh (f := f) k₀ m₀, ← intervalIntegral.integral_const_mul]
  unfold PsiP
  refine intervalIntegral.integral_mono_on (cL_lt_cR k₀ m₀).le
    (integrand_intervalIntegrable hf k₀ m₀ measurable_gP abs_gP_le t)
    ((wPh_continuous hf).intervalIntegrable _ _ |>.const_mul 2) fun x _ => ?_
  nlinarith [gP_le_two (t + aPh f k₀ m₀ x), wPh_nonneg f x]

end props

section semicont

lemma nhdsLE_eq (t : ℝ) : 𝓝[≤] t = 𝓝[<] t ⊔ pure t := by
  rw [← Iio_union_Icc_eq_Iic le_rfl, nhdsWithin_union]
  simp

lemma nhdsGE_eq (t : ℝ) : 𝓝[≥] t = pure t ⊔ 𝓝[>] t := by
  rw [← Icc_union_Ioi_eq_Ici le_rfl, nhdsWithin_union]
  simp

lemma lsc_of_sided {h : ℝ → ℝ} (hl : ∀ t, Tendsto h (𝓝[<] t) (𝓝 (h t)))
    (hr : ∀ t, ∃ b, h t ≤ b ∧ Tendsto h (𝓝[>] t) (𝓝 b)) : LowerSemicontinuous h := by
  intro t y hy
  obtain ⟨b, hb, hbt⟩ := hr t
  have h1 : ∀ᶠ r in 𝓝[<] t, y < h r := (hl t).eventually (lt_mem_nhds hy)
  have h2 : ∀ᶠ r in 𝓝[>] t, y < h r := hbt.eventually (lt_mem_nhds (hy.trans_le hb))
  have h3 : ∀ᶠ r in 𝓝[≤] t, y < h r := by
    rw [nhdsLE_eq, eventually_sup]; exact ⟨h1, eventually_pure.mpr hy⟩
  rw [← nhdsLE_sup_nhdsGT, eventually_sup]
  exact ⟨h3, h2⟩

lemma usc_of_sided {h : ℝ → ℝ} (hr : ∀ t, Tendsto h (𝓝[>] t) (𝓝 (h t)))
    (hl : ∀ t, ∃ a, a ≤ h t ∧ Tendsto h (𝓝[<] t) (𝓝 a)) : UpperSemicontinuous h := by
  intro t y hy
  obtain ⟨a, ha, hat⟩ := hl t
  have h1 : ∀ᶠ r in 𝓝[<] t, h r < y := hat.eventually (gt_mem_nhds (ha.trans_lt hy))
  have h2 : ∀ᶠ r in 𝓝[>] t, h r < y := (hr t).eventually (gt_mem_nhds hy)
  have h3 : ∀ᶠ r in 𝓝[≥] t, h r < y := by
    rw [nhdsGE_eq, eventually_sup]; exact ⟨eventually_pure.mpr hy, h2⟩
  rw [← nhdsLT_sup_nhdsGE, eventually_sup]
  exact ⟨h1, h3⟩

lemma exists_min_periodic {h : ℝ → ℝ} (hlsc : LowerSemicontinuous h)
    (hper : ∀ (t : ℝ) (z : ℤ), h (t + z) = h t) : ∃ t₀, ∀ t, h t₀ ≤ h t := by
  obtain ⟨t₀, -, hmin⟩ := hlsc.lowerSemicontinuousOn (s := Icc (0 : ℝ) 1) |>.exists_isMinOn
    ⟨0, by simp⟩ isCompact_Icc
  refine ⟨t₀, fun t => ?_⟩
  have e : h t = h (Int.fract t) := by
    have := hper (Int.fract t) ⌊t⌋
    rw [Int.fract_add_floor] at this
    exact this
  rw [e]
  exact hmin ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

lemma exists_max_periodic {h : ℝ → ℝ} (husc : UpperSemicontinuous h)
    (hper : ∀ (t : ℝ) (z : ℤ), h (t + z) = h t) : ∃ t₁, ∀ t, h t ≤ h t₁ := by
  obtain ⟨t₁, -, hmax⟩ := husc.upperSemicontinuousOn (s := Icc (0 : ℝ) 1) |>.exists_isMaxOn
    ⟨0, by simp⟩ isCompact_Icc
  refine ⟨t₁, fun t => ?_⟩
  have e : h t = h (Int.fract t) := by
    have := hper (Int.fract t) ⌊t⌋
    rw [Int.fract_add_floor] at this
    exact this
  rw [e]
  exact hmax ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
/-- `Ψ_f` é semicontínua inferiormente -/
lemma psiF_lsc : LowerSemicontinuous (PsiF f k₀ m₀) :=
  lsc_of_sided (psiF_tendsto_left hf k₀ m₀) fun t =>
    ⟨PsiP f k₀ m₀ t, psiF_le_psiP hf k₀ m₀ t, psiF_tendsto_right hf k₀ m₀ t⟩

include hf in
/-- `Ψ_f⁺` é semicontínua superiormente -/
lemma psiP_usc : UpperSemicontinuous (PsiP f k₀ m₀) :=
  usc_of_sided (psiP_tendsto_right hf k₀ m₀) fun t =>
    ⟨PsiF f k₀ m₀ t, psiF_le_psiP hf k₀ m₀ t, psiP_tendsto_left hf k₀ m₀ t⟩

include hf in
/-- `m_f = min Ψ_f` é atingido -/
lemma exists_min_psiF : ∃ t₀, ∀ t, PsiF f k₀ m₀ t₀ ≤ PsiF f k₀ m₀ t :=
  exists_min_periodic (psiF_lsc hf k₀ m₀) (psiF_add_int k₀ m₀)

include hf in
/-- `M_f = max Ψ_f⁺` é atingido -/
lemma exists_max_psiP : ∃ t₁, ∀ t, PsiP f k₀ m₀ t ≤ PsiP f k₀ m₀ t₁ :=
  exists_max_periodic (psiP_usc hf k₀ m₀) (psiP_add_int k₀ m₀)

include hf in
/-- `max Ψ_f⁺ = sup Ψ_f` -/
lemma psiP_eq_sup {t₁ : ℝ} (ht₁ : ∀ t, PsiP f k₀ m₀ t ≤ PsiP f k₀ m₀ t₁) :
    (∀ t, PsiF f k₀ m₀ t ≤ PsiP f k₀ m₀ t₁) ∧
      ∀ δ > 0, ∃ t, PsiP f k₀ m₀ t₁ - δ < PsiF f k₀ m₀ t := by
  refine ⟨fun t => (psiF_le_psiP hf k₀ m₀ t).trans (ht₁ t), fun δ hδ => ?_⟩
  have := (psiF_tendsto_right hf k₀ m₀ t₁).eventually (lt_mem_nhds (show PsiP f k₀ m₀ t₁ - δ <
    PsiP f k₀ m₀ t₁ by linarith))
  obtain ⟨t, ht, -⟩ := (this.and (self_mem_nhdsWithin : Ioi t₁ ∈ 𝓝[>] t₁)).exists
  exact ⟨t, ht⟩

end semicont

section atoms

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

/-- a medida `√c`-ponderada de `K`, restrita a `{f'' ≠ 0}`: usada só para dizer «quase sempre» e
«conjunto de medida positiva» sobre os átomos de `μ_f` (o peso `√c` é positivo nesse conjunto) -/
noncomputable def atomMeasure (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) : Measure ℝ :=
  (volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))).restrict {x | 0 < wPh f x}

instance (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) : IsFiniteMeasure (atomMeasure f k₀ m₀) := by
  unfold atomMeasure; infer_instance

/-- `t` é uma fase atômica: `μ_f({-t}) > 0`, isto é, `t + a(x) ∈ ℤ` em um conjunto de medida
positiva de `{f'' ≠ 0}` -/
def IsAtomPhase (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : Prop :=
  0 < atomMeasure f k₀ m₀ {x | ∃ z : ℤ, t + aPh f k₀ m₀ x = z}

include hf in
/-- as fases atômicas são enumeráveis -/
lemma countable_atomPhase : {t : ℝ | IsAtomPhase f k₀ m₀ t}.Countable := by
  set ν := atomMeasure f k₀ m₀
  have hg : Measurable (fun x => Int.fract (aPh f k₀ m₀ x)) :=
    measurable_fract.comp (aPh_measurable hf k₀ m₀)
  have hC := Measure.countable_meas_level_set_pos (μ := ν) hg
  have hsub : {t : ℝ | IsAtomPhase f k₀ m₀ t} ⊆
      ⋃ θ ∈ {θ : ℝ | 0 < ν {x | Int.fract (aPh f k₀ m₀ x) = θ}},
        range (fun n : ℤ => (n : ℝ) - θ) := by
    intro t ht
    have h1 : {x | ∃ z : ℤ, t + aPh f k₀ m₀ x = z} ⊆
        {x | Int.fract (aPh f k₀ m₀ x) = Int.fract (-t)} := by
      rintro x ⟨z, hz⟩
      have : aPh f k₀ m₀ x = (z : ℝ) + (-t) := by linarith
      show Int.fract (aPh f k₀ m₀ x) = Int.fract (-t)
      rw [this, Int.fract_intCast_add]
    have h2 : 0 < ν {x | Int.fract (aPh f k₀ m₀ x) = Int.fract (-t)} :=
      lt_of_lt_of_le ht (measure_mono h1)
    refine mem_biUnion (x := Int.fract (-t)) h2 ?_
    refine ⟨-⌊-t⌋, ?_⟩
    have := Int.floor_add_fract (-t)
    push_cast
    linarith
  exact (hC.biUnion fun θ _ => countable_range _).mono hsub

include hf in
lemma psiP_eq_psiF_of_not_atom {t : ℝ} (ht : ¬ IsAtomPhase f k₀ m₀ t) :
    PsiP f k₀ m₀ t = PsiF f k₀ m₀ t := by
  have h0 : atomMeasure f k₀ m₀ {x | ∃ z : ℤ, t + aPh f k₀ m₀ x = z} = 0 := by
    unfold IsAtomPhase at ht
    exact le_antisymm (not_lt.mp ht) (zero_le _)
  have hmeas : MeasurableSet {x : ℝ | 0 < wPh f x} :=
    measurableSet_lt measurable_const (wPh_continuous hf).measurable
  unfold atomMeasure at h0
  rw [Measure.restrict_apply' hmeas, Measure.restrict_apply' measurableSet_Ioc] at h0
  have hae := (measure_eq_zero_iff_ae_notMem.mp h0)
  unfold PsiP PsiF
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae] with x hx hxI
  have hxI : x ∈ Ioc (cL k₀ m₀) (cR k₀ m₀) := by
    rwa [uIoc_of_le (cL_lt_cR k₀ m₀).le] at hxI
  by_cases hw : 0 < wPh f x
  · have : ¬ ∃ z : ℤ, t + aPh f k₀ m₀ x = z := fun hz => hx ⟨⟨hz, hw⟩, hxI⟩
    push_neg at this
    rw [gC_eq_gP_of_not_int this]
  · have : wPh f x = 0 := le_antisymm (not_lt.mp hw) (wPh_nonneg f x)
    rw [this]; simp

end atoms

end Pendencias
