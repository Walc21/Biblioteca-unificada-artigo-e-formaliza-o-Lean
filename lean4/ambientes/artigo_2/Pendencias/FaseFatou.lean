import Mathlib

/-!
# Fatou em forma eventual

Para integrais `∫_a^b` de funções mensuráveis e limitadas: se, em quase todo ponto, `F n x`
fica eventualmente acima de `G x - δ` (para todo `δ > 0`), então, para todo `δ > 0`,
`∫ G - δ < ∫ F n` eventualmente. E a versão reversa, com cota superior comum.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory

lemma fatou_eventually {a b : ℝ} (hab : a ≤ b) {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hmeas : ∀ n, Measurable (F n)) (hnn : ∀ n, ∀ x ∈ Ioc a b, 0 ≤ F n x)
    (hGnn : ∀ x ∈ Ioc a b, 0 ≤ G x) (hGm : Measurable G) (hGint : IntervalIntegrable G volume a b)
    (hFint : ∀ n, IntervalIntegrable (F n) volume a b)
    (hlim : ∀ x ∈ Ioc a b, ∀ δ > 0, ∀ᶠ n in atTop, G x - δ ≤ F n x) :
    ∀ δ > 0, ∀ᶠ n in atTop,
      (∫ x in a..b, G x) - δ < ∫ x in a..b, F n x := by
  intro δ hδ
  set μ : Measure ℝ := volume.restrict (Ioc a b) with hμ
  have hGi : Integrable G μ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hGint
  have hFi : ∀ n, Integrable (F n) μ := fun n =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hFint n)
  have eG : ∫ x in a..b, G x = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (G x) ∂μ) := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_eq_lintegral_of_nonneg_ae ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hGnn)) hGm.aestronglyMeasurable
  have eF : ∀ n, ∫ x in a..b, F n x = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) := by
    intro n
    rw [intervalIntegral.integral_of_le hab]
    exact integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (hnn n)))
      (hmeas n).aestronglyMeasurable
  have fG : (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≠ ⊤ := ((hasFiniteIntegral_iff_ofReal
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall hGnn))).mp
    hGi.hasFiniteIntegral).ne
  have fF : ∀ n, (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) ≠ ⊤ := fun n =>
    ((hasFiniteIntegral_iff_ofReal
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (hnn n)))).mp
      (hFi n).hasFiniteIntegral).ne
  -- pointwise: `ofReal (G x) ≤ liminf ofReal (F n x)` (a.e.)
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (G x) ≤ liminf (fun n => ENNReal.ofReal (F n x)) atTop := by
    rw [hμ, ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun x hx => ?_
    refine ENNReal.le_of_forall_pos_le_add fun e he _ => ?_
    have h1 := hlim x hx (e : ℝ) (by exact_mod_cast he)
    have h2 : ENNReal.ofReal (G x - e) ≤ liminf (fun n => ENNReal.ofReal (F n x)) atTop :=
      le_liminf_of_le (by isBoundedDefault) (h1.mono fun n hn => ENNReal.ofReal_le_ofReal hn)
    calc ENNReal.ofReal (G x) = ENNReal.ofReal ((G x - e) + e) := by ring_nf
      _ ≤ ENNReal.ofReal (G x - e) + ENNReal.ofReal e := ENNReal.ofReal_add_le
      _ ≤ liminf (fun n => ENNReal.ofReal (F n x)) atTop + (e : ENNReal) := by
          rw [ENNReal.ofReal_coe_nnreal]; gcongr
  have hfat := lintegral_liminf_le (μ := μ) (f := fun n x => ENNReal.ofReal (F n x))
    (fun n => (hmeas n).ennreal_ofReal)
  have hle : (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop :=
    (lintegral_mono_ae hpt).trans hfat
  by_cases hneg : (∫ x in a..b, G x) - δ < 0
  · exact Eventually.of_forall fun n => by
      have : 0 ≤ ∫ x in a..b, F n x := by
        rw [intervalIntegral.integral_of_le hab]
        exact setIntegral_nonneg measurableSet_Ioc (hnn n)
      linarith
  · push_neg at hneg
    have hIGpos : 0 < ∫ x in a..b, G x := by linarith
    have hlt : ENNReal.ofReal ((∫ x in a..b, G x) - δ) <
        liminf (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop := by
      refine lt_of_lt_of_le ?_ hle
      have : ENNReal.ofReal (∫ x in a..b, G x) = ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
        rw [eG, ENNReal.ofReal_toReal fG]
      rw [← this]
      exact (ENNReal.ofReal_lt_ofReal_iff hIGpos).mpr (by linarith)
    filter_upwards [Filter.eventually_lt_of_lt_liminf hlt] with n hn
    rw [eF n]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hneg (fF n)).mp hn

lemma rev_fatou_eventually {a b : ℝ} (hab : a ≤ b) {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {B : ℝ}
    (hmeas : ∀ n, Measurable (F n)) (hFB : ∀ n, ∀ x ∈ Ioc a b, F n x ≤ B)
    (hGm : Measurable G) (hGB : ∀ x ∈ Ioc a b, G x ≤ B)
    (hGint : IntervalIntegrable G volume a b)
    (hFint : ∀ n, IntervalIntegrable (F n) volume a b)
    (hlim : ∀ x ∈ Ioc a b, ∀ δ > 0, ∀ᶠ n in atTop, F n x ≤ G x + δ) :
    ∀ δ > 0, ∀ᶠ n in atTop,
      ∫ x in a..b, F n x < (∫ x in a..b, G x) + δ := by
  intro δ hδ
  have hB : IntervalIntegrable (fun _ : ℝ => B) volume a b := intervalIntegrable_const
  have key := fatou_eventually hab (F := fun n x => B - F n x) (G := fun x => B - G x)
    (fun n => measurable_const.sub (hmeas n)) (fun n x hx => by linarith [hFB n x hx])
    (fun x hx => by linarith [hGB x hx]) (measurable_const.sub hGm) (hB.sub hGint)
    (fun n => hB.sub (hFint n)) (fun x hx δ' hδ' => by
      filter_upwards [hlim x hx δ' hδ'] with n hn
      linarith) δ hδ
  filter_upwards [key] with n hn
  rw [intervalIntegral.integral_sub hB hGint, intervalIntegral.integral_sub hB (hFint n)] at hn
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hn
  linarith

end Pendencias
