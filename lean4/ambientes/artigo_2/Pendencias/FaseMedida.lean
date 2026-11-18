import Pendencias.FaseFourier

/-!
# III.12.8(b): medida de fase `μ̃_f` no círculo e `Ψ_f` constante ⇔ `μ_f` uniforme

Constrói `μ̃_f` como medida em `AddCircle (1:ℝ)`: imagem de `√(|f''|/8) dx` em `K` pela
fase `x ↦ a(x) mod 1`. No texto, `μ_f = √8 · μ̃_f`; em particular a massa total de `μ̃_f` é
`I(f)/√8`.

Resultados (`f ∈ C²(ℝ)`, versões `_on` para `f ∈ C²(K)` via `extF`):

* `circ_fourier_uniqueness`: medidas finitas no círculo com os mesmos coeficientes de Fourier
  são iguais (densidade dos polinômios trigonométricos, `span_fourier_closure_eq_top`);
* `PsiF_eq_circ`: `Ψ_f(t) = ∫ gCirc (t + θ) dμ̃_f(θ)`;
* `psi_const_iff_muCirc`: `Ψ_f` constante ⇔ `μ̃_f = (I(f)/√8) · haar`, ou seja, `μ_f` uniforme.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory AddCircle Artigo
open scoped ENNReal

section Uniqueness

lemma circ_integrable (μ : Measure (AddCircle (1:ℝ))) [IsFiniteMeasure μ]
    (g : C(AddCircle (1:ℝ), ℂ)) : Integrable g μ :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma circ_integral_fourier_span {μ ν : Measure (AddCircle (1:ℝ))} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ n : ℤ, ∫ x, fourier (T := (1:ℝ)) n x ∂μ = ∫ x, fourier (T := (1:ℝ)) n x ∂ν)
    {p : C(AddCircle (1:ℝ), ℂ)} (hp : p ∈ Submodule.span ℂ (range (fourier (T := (1:ℝ))))) :
    ∫ x, p x ∂μ = ∫ x, p x ∂ν := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    exact h n
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [ContinuousMap.add_apply]
    rw [integral_add (circ_integrable μ x) (circ_integrable μ y),
      integral_add (circ_integrable ν x) (circ_integrable ν y), hx, hy]
  | smul a x _ hx =>
    simp only [ContinuousMap.smul_apply]
    rw [integral_smul, integral_smul, hx]

lemma circ_integral_eq_of_fourier {μ ν : Measure (AddCircle (1:ℝ))} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ n : ℤ, ∫ x, fourier (T := (1:ℝ)) n x ∂μ = ∫ x, fourier (T := (1:ℝ)) n x ∂ν)
    (g : C(AddCircle (1:ℝ), ℂ)) : ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
  set M : ℝ := μ.real univ + ν.real univ with hM
  have hM0 : 0 ≤ M := by positivity
  have hg : g ∈ (Submodule.span ℂ (range (fourier (T := (1:ℝ))))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; exact Submodule.mem_top
  have hg2 : g ∈ closure ((Submodule.span ℂ (range (fourier (T := (1:ℝ))))) :
      Set C(AddCircle (1:ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hg
  have key : ∀ ε > 0, ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ ≤ ε * M := by
    intro ε hε
    obtain ⟨p, hpS, hd⟩ := Metric.mem_closure_iff.1 hg2 ε hε
    have hpe := circ_integral_fourier_span h hpS
    have hbd : ∀ x, ‖g x - p x‖ ≤ ε := fun x => by
      have := ContinuousMap.dist_apply_le_dist (f := g) (g := p) x
      rw [dist_eq_norm] at this
      exact this.trans hd.le
    have h1 : ‖∫ x, (g - p) x ∂μ‖ ≤ ε * μ.real univ :=
      norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => hbd x)
    have h2 : ‖∫ x, (g - p) x ∂ν‖ ≤ ε * ν.real univ :=
      norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => hbd x)
    have e1 : ∫ x, (g - p) x ∂μ = (∫ x, g x ∂μ) - ∫ x, p x ∂μ := by
      simp only [ContinuousMap.sub_apply]
      rw [integral_sub (circ_integrable μ g) (circ_integrable μ p)]
    have e2 : ∫ x, (g - p) x ∂ν = (∫ x, g x ∂ν) - ∫ x, p x ∂ν := by
      simp only [ContinuousMap.sub_apply]
      rw [integral_sub (circ_integrable ν g) (circ_integrable ν p)]
    rw [e1] at h1
    rw [e2] at h2
    have : (∫ x, g x ∂μ) - ∫ x, g x ∂ν =
        ((∫ x, g x ∂μ) - ∫ x, p x ∂μ) - ((∫ x, g x ∂ν) - ∫ x, p x ∂ν) := by
      rw [hpe]; ring
    rw [this]
    have := norm_sub_le (((∫ x, g x ∂μ) - ∫ x, p x ∂μ)) (((∫ x, g x ∂ν) - ∫ x, p x ∂ν))
    have hμν : ε * μ.real univ + ε * ν.real univ = ε * M := by rw [hM]; ring
    linarith
  by_contra hne
  have hpos : 0 < ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set δ := ‖(∫ x, g x ∂μ) - ∫ x, g x ∂ν‖ with hδ
  have hε : 0 < δ / (2 * (M + 1)) := by positivity
  have := key _ hε
  have hlt : δ / (2 * (M + 1)) * M < δ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Unicidade de Fourier no círculo**: medidas finitas com os mesmos coeficientes são iguais. -/
theorem circ_fourier_uniqueness {μ ν : Measure (AddCircle (1:ℝ))} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h : ∀ n : ℤ, ∫ x, fourier (T := (1:ℝ)) n x ∂μ = ∫ x, fourier (T := (1:ℝ)) n x ∂ν) :
    μ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have := circ_integral_eq_of_fourier h
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  simp only [ContinuousMap.coe_mk] at this
  rw [integral_complex_ofReal, integral_complex_ofReal] at this
  exact_mod_cast this

end Uniqueness

section Descent

lemma gC_periodic_one : Function.Periodic gC 1 := fun u => gC_add_one u

/-- `gC` descida ao círculo `ℝ / ℤ` (período `1`) -/
noncomputable def gCirc : AddCircle (1:ℝ) → ℝ := Function.Periodic.lift gC_periodic_one

lemma gCirc_coe (u : ℝ) : gCirc (u : AddCircle (1:ℝ)) = gC u :=
  Function.Periodic.lift_coe gC_periodic_one u

lemma gCirc_measurable : Measurable gCirc := by
  rw [QuotientAddGroup.measurable_from_quotient]
  have : (gCirc ∘ ((↑) : ℝ → AddCircle (1:ℝ))) = gC := funext gCirc_coe
  rw [this]; exact measurable_gC

lemma coe_circ_measurable : Measurable ((↑) : ℝ → AddCircle (1:ℝ)) := by
  intro s hs
  exact QuotientAddGroup.measurable_coe hs

end Descent

section Measure

variable {f : ℝ → ℝ} (k₀ : ℕ) (m₀ : ℤ)

/-- **Medida de fase `μ̃_f`** no círculo `AddCircle 1`: imagem de `√(|f''|/8) dx` em `K` pela
fase `x ↦ a(x) mod 1`. No texto `μ_f = √8 · μ̃_f`. -/
noncomputable def muCirc (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) : Measure (AddCircle (1:ℝ)) :=
  Measure.map (fun x : ℝ => ((aPh f k₀ m₀ x : ℝ) : AddCircle (1:ℝ)))
    ((volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))).withDensity
      (fun x => ENNReal.ofReal (wPh f x)))

lemma muCirc_integral (hf : ContDiff ℝ 2 f) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] (g : AddCircle (1:ℝ) → E) (hg : Measurable g) :
    ∫ θ, g θ ∂(muCirc f k₀ m₀) =
      ∫ x in Ioc (cL k₀ m₀) (cR k₀ m₀), wPh f x • g ((aPh f k₀ m₀ x : ℝ) : AddCircle (1:ℝ)) := by
  unfold muCirc
  have hφ : Measurable (fun x : ℝ => ((aPh f k₀ m₀ x : ℝ) : AddCircle (1:ℝ))) :=
    coe_circ_measurable.comp (aPh_measurable hf k₀ m₀)
  rw [integral_map hφ.aemeasurable hg.aestronglyMeasurable]
  have hdens : Measurable (fun x => ENNReal.ofReal (wPh f x)) :=
    ENNReal.measurable_ofReal.comp (wPh_continuous hf).measurable
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (wPh f x))
    hdens (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [ENNReal.toReal_ofReal (wPh_nonneg f x)]

lemma muCirc_isFinite (hf : ContDiff ℝ 2 f) : IsFiniteMeasure (muCirc f k₀ m₀) := by
  unfold muCirc
  haveI : IsFiniteMeasure ((volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))).withDensity
      (fun x => ENNReal.ofReal (wPh f x))) := by
    apply isFiniteMeasure_withDensity_ofReal
    exact ((wPh_continuous hf).integrableOn_Icc.mono_set Ioc_subset_Icc_self).hasFiniteIntegral
  infer_instance

end Measure

section Main

variable {f : ℝ → ℝ} (k₀ : ℕ) (m₀ : ℤ)

lemma wPh_eq_div (f : ℝ → ℝ) (x : ℝ) :
    wPh f x = Real.sqrt |deriv (deriv f) x| / Real.sqrt 8 := by
  unfold wPh; exact Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 8)

/-- massa total: `μ̃_f(S¹) = I(f)/√8` (no texto, `μ_f(S¹) = I(f)`) -/
lemma muCirc_mass (hf : ContDiff ℝ 2 f) :
    (muCirc f k₀ m₀).real univ = curvI f k₀ m₀ / Real.sqrt 8 := by
  have h := muCirc_integral k₀ m₀ hf (fun _ => (1:ℝ)) measurable_const
  have hI : ∫ x in Ioc (cL k₀ m₀) (cR k₀ m₀), wPh f x = curvI f k₀ m₀ / Real.sqrt 8 := by
    unfold curvI
    rw [← intervalIntegral.integral_of_le (cL_lt_cR k₀ m₀).le, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => ?_
    exact wPh_eq_div f x
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [h, hI]

/-- `Ψ_f(t) = ∫ gCirc(t + θ) dμ̃_f(θ)`: a representação de `Ψ_f` pela medida no círculo -/
lemma PsiF_eq_circ (hf : ContDiff ℝ 2 f) (t : ℝ) :
    PsiF f k₀ m₀ t = ∫ θ, gCirc ((t : AddCircle (1:ℝ)) + θ) ∂(muCirc f k₀ m₀) := by
  have hmeas : Measurable (fun θ : AddCircle (1:ℝ) => gCirc ((t : AddCircle (1:ℝ)) + θ)) := by
    rw [QuotientAddGroup.measurable_from_quotient]
    have : ((fun θ : AddCircle (1:ℝ) => gCirc ((t : AddCircle (1:ℝ)) + θ)) ∘
        ((↑) : ℝ → AddCircle (1:ℝ))) = fun u => gC (t + u) := by
      funext u; exact gCirc_coe (t + u)
    rw [this]; exact measurable_gC.comp (measurable_const.add measurable_id)
  rw [muCirc_integral k₀ m₀ hf _ hmeas]
  unfold PsiF
  rw [intervalIntegral.integral_of_le (cL_lt_cR k₀ m₀).le]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  simp only [smul_eq_mul]
  congr 1

/-- The jump at phase `t` is the mass of the singleton `{-t}` for the normalized measure. -/
theorem psi_gap_eq_muCirc (hf : ContDiff ℝ 2 f) (t : ℝ) :
    PsiP f k₀ m₀ t - PsiF f k₀ m₀ t =
      (muCirc f k₀ m₀).real {-(t : AddCircle (1 : ℝ))} := by
  classical
  let s : Set (AddCircle (1 : ℝ)) := {-(t : AddCircle (1 : ℝ))}
  have hs : MeasurableSet s := measurableSet_singleton _
  have h := muCirc_integral k₀ m₀ hf (s.indicator (1 : AddCircle (1 : ℝ) → ℝ))
    (measurable_const.indicator hs)
  rw [integral_indicator_one hs] at h
  rw [psiP_sub_psiF hf k₀ m₀, h]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ ↦ ?_
  have hm : (aPh f k₀ m₀ x : AddCircle (1 : ℝ)) ∈ s ↔ x ∈ Sphase f k₀ m₀ t := by
    change (aPh f k₀ m₀ x : AddCircle (1 : ℝ)) = -(t : AddCircle (1 : ℝ)) ↔
      ∃ z : ℤ, t + aPh f k₀ m₀ x = z
    rw [← add_eq_zero_iff_eq_neg', ← AddCircle.coe_add, AddCircle.coe_eq_zero_iff]
    simpa [zsmul_one] using
      (exists_congr fun z : ℤ ↦ eq_comm (a := (z : ℝ)) (b := t + aPh f k₀ m₀ x))
  by_cases hx : x ∈ Sphase f k₀ m₀ t
  · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hm.mpr hx)]
  · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hm.mp hx)]

/-- The singleton-mass identity for functions of class `C²(K)`. -/
theorem psiOn_gap_eq_muCirc (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    PsiPOn f k₀ m₀ t - PsiFOn f k₀ m₀ t =
      (muCirc (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀).real {-(t : AddCircle (1 : ℝ))} := by
  rw [← psiPOn_eq hf, ← psiFOn_eq hf]
  exact psi_gap_eq_muCirc k₀ m₀ (extF_cell_contDiff hf) t

/-- coeficientes de Fourier de `μ̃_f`: `∫ e_m dμ̃_f = ∫_K √(|f''|/8) e^{2πi m a}` -/
lemma fourier_muCirc (hf : ContDiff ℝ 2 f) (m : ℤ) :
    ∫ θ, fourier (T := (1:ℝ)) m θ ∂(muCirc f k₀ m₀) =
      ∫ x in Ioc (cL k₀ m₀) (cR k₀ m₀), (wPh f x : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * m * aPh f k₀ m₀ x) := by
  rw [muCirc_integral k₀ m₀ hf _ (fourier (T := (1:ℝ)) m).continuous.measurable]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  rw [Complex.real_smul, fourier_coe_apply]
  simp

lemma integral_fourier_haar_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x, fourier (T := (1:ℝ)) n x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))) = 0 :=
  integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hn one_pos)

lemma integral_eF_eq_zero {n : ℤ} (hn : n ≠ 0) : ∫ t in (0:ℝ)..1, eF n t = 0 := by
  have hfun : (fun t : ℝ => eF n t) =
      fun t : ℝ => Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * n)) * (t : ℂ)) :=
    funext fun t => by unfold eF; ring_nf
  have hc : (-(2 * (Real.pi : ℂ) * Complex.I * n)) ≠ 0 := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
  rw [hfun, integral_exp_mul_complex hc]
  have h1 : Complex.exp ((-(2 * (Real.pi : ℂ) * Complex.I * n)) * ((1:ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_one, mul_one, show -(2 * (Real.pi : ℂ) * Complex.I * n) =
      ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h1]
  simp

/-- **III.12.8(b)**, forma `ℝ`: `Ψ_f` constante ⇔ `μ̃_f` é `(I(f)/√8)` vezes a Haar do círculo,
isto é, `μ_f` uniforme. -/
theorem psi_const_iff_muCirc (hf : ContDiff ℝ 2 f) :
    (∃ c : ℝ, ∀ t, PsiF f k₀ m₀ t = c) ↔
      muCirc f k₀ m₀ = ENNReal.ofReal (curvI f k₀ m₀ / Real.sqrt 8) • haarAddCircle := by
  haveI := muCirc_isFinite k₀ m₀ hf
  have hcurv : 0 ≤ curvI f k₀ m₀ :=
    intervalIntegral.integral_nonneg (cL_lt_cR k₀ m₀).le fun x _ => Real.sqrt_nonneg _
  have hM : 0 ≤ curvI f k₀ m₀ / Real.sqrt 8 := div_nonneg hcurv (Real.sqrt_nonneg _)
  haveI : IsFiniteMeasure (ENNReal.ofReal (curvI f k₀ m₀ / Real.sqrt 8) •
      (haarAddCircle : Measure (AddCircle (1:ℝ)))) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  constructor
  · rintro ⟨c, hc⟩
    apply circ_fourier_uniqueness
    intro n
    rw [integral_smul_measure, ENNReal.toReal_ofReal hM]
    by_cases hn : n = 0
    · subst hn
      simp only [fourier_zero, integral_const, probReal_univ, muCirc_mass k₀ m₀ hf, one_smul]
    · rw [integral_fourier_haar_ne_zero hn, smul_zero, fourier_muCirc k₀ m₀ hf n]
      have hL : ∫ t in (0:ℝ)..1, (PsiF f k₀ m₀ t : ℂ) * eF n t = 0 := by
        simp only [hc]
        rw [intervalIntegral.integral_const_mul, integral_eF_eq_zero hn, mul_zero]
      have h := fourier_psiF hf k₀ m₀ n
      rw [hL] at h
      have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hα : (Real.log 2 : ℂ) + 2 * (Real.pi : ℂ) * Complex.I * n ≠ 0 := by
        intro h0
        have h2 : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)).re = 0 := by simp
        have h1 := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re, h2] at h1
        linarith
      have hJ := (mul_eq_zero.mp h.symm).resolve_left (one_div_ne_zero hα)
      rw [intervalIntegral.integral_of_le (cL_lt_cR k₀ m₀).le] at hJ
      exact hJ
  · intro hμ
    refine ⟨(ENNReal.ofReal (curvI f k₀ m₀ / Real.sqrt 8)).toReal *
      ∫ θ, gCirc θ ∂(haarAddCircle : Measure (AddCircle (1:ℝ))), fun t => ?_⟩
    rw [PsiF_eq_circ k₀ m₀ hf t, hμ, integral_smul_measure,
      integral_add_left_eq_self gCirc (t : AddCircle (1:ℝ))]
    rfl

/-- **III.12.8(b)**, forma `C²(K)`: `Ψ_f` constante ⇔ `μ̃_f = (I(f)/√8)·haar`, com `μ̃_f` obtida
da extensão `extF` (que coincide com `f` em `K`). -/
theorem psiOn_const_iff_muCirc (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    (∃ c : ℝ, ∀ t, PsiFOn f k₀ m₀ t = c) ↔
      muCirc (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ =
        ENNReal.ofReal (curvIOn f k₀ m₀ / Real.sqrt 8) • haarAddCircle := by
  have h := psi_const_iff_muCirc k₀ m₀ (extF_cell_contDiff hf)
  rw [curvI_extF hf] at h
  have hfun : ∀ t, PsiFOn f k₀ m₀ t = PsiF (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ t :=
    fun t => (psiFOn_eq hf t).symm
  simp only [hfun]
  exact h

/-- **III.12.8(b)**: o limite de `N² E_N^dia(f)_∞` existe ⇔ `μ_f` é uniforme (forma `C²(K)`). -/
theorem limit_iff_muCirc_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    (∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop (𝓝 L)) ↔
      muCirc (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ =
        ENNReal.ofReal (curvIOn f k₀ m₀ / Real.sqrt 8) • haarAddCircle := by
  rw [limit_iff_const_on hf]
  exact psiOn_const_iff_muCirc k₀ m₀ hf

/-- **III.12.8(b)**, forma `ℝ`: o limite de `N² E_N^dia(f)_∞` existe ⇔ `μ_f` é uniforme. -/
theorem limit_iff_muCirc (hf : ContDiff ℝ 2 f) :
    (∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop (𝓝 L)) ↔
      muCirc f k₀ m₀ = ENNReal.ofReal (curvI f k₀ m₀ / Real.sqrt 8) • haarAddCircle := by
  rw [limit_iff_const hf k₀ m₀]
  exact psi_const_iff_muCirc k₀ m₀ hf

end Main

end Pendencias
