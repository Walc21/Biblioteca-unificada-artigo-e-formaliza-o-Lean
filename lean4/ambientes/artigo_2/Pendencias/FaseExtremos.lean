import Pendencias.FaseMediaFase

/-!
# III.12.8(d) — extremos atingidos ⟺ massa pontual

* `m_f = I/√8` ⟺ `∃ t, Ψ_f(t) = I/√8` ⟺ `|f''| ∈ c₀ 4^ℤ` q.t.p. em `{f'' ≠ 0}`;
* `M_f = I/√2` ⟺ `∃ t, Ψ_f⁺(t) = 2 I/√8` ⟺ a mesma condição.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

lemma gC_eq_one_iff (u : ℝ) : gC u = 1 ↔ ∃ z : ℤ, u = z := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have hpos : 0 < (⌈u⌉ : ℝ) - u := by
      have h1 : u ≤ ⌈u⌉ := Int.le_ceil u
      have h2 : u ≠ ⌈u⌉ := hne ⌈u⌉
      have := lt_of_le_of_ne h1 h2
      linarith
    have : 1 < gC u := Real.one_lt_rpow (by norm_num) hpos
    linarith
  · rintro ⟨z, rfl⟩; exact gC_int z

lemma gP_eq_two_iff (u : ℝ) : gP u = 2 ↔ ∃ z : ℤ, u = z := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    have := gC_eq_gP_of_not_int hne
    linarith [gC_lt_two u]
  · rintro ⟨z, rfl⟩; exact gP_int z

section ext

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

/-- "`μ_f` é massa pontual em `-t`" (forma bruta) -/
def PointMass (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : Prop :=
  ∀ᵐ x ∂(volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))),
    0 < wPh f x → ∃ z : ℤ, t + aPh f k₀ m₀ x = z

include hf in
lemma min_attained_iff {t : ℝ} :
    PsiF f k₀ m₀ t = curvI f k₀ m₀ / Real.sqrt 8 ↔ PointMass f k₀ m₀ t := by
  have hab := cL_lt_cR k₀ m₀
  have hI1 := integrand_intervalIntegrable hf k₀ m₀ measurable_gC abs_gC_le t
  have hw : IntervalIntegrable (wPh f) volume (cL k₀ m₀) (cR k₀ m₀) :=
    (wPh_continuous hf).intervalIntegrable _ _
  have hdiff : ∫ x in cL k₀ m₀..cR k₀ m₀, (wPh f x * gC (t + aPh f k₀ m₀ x) - wPh f x) =
      PsiF f k₀ m₀ t - curvI f k₀ m₀ / Real.sqrt 8 := by
    rw [intervalIntegral.integral_sub hI1 hw, integral_wPh]; rfl
  have hnn : ∀ x, 0 ≤ wPh f x * gC (t + aPh f k₀ m₀ x) - wPh f x := fun x => by
    nlinarith [wPh_nonneg f x, gC_ge_one (t + aPh f k₀ m₀ x)]
  constructor
  · intro h
    have h0 : ∫ x in cL k₀ m₀..cR k₀ m₀, (wPh f x * gC (t + aPh f k₀ m₀ x) - wPh f x) = 0 := by
      rw [hdiff, h, sub_self]
    have := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Eventually.of_forall hnn) (hI1.sub hw)).mp h0
    filter_upwards [this] with x hx hxpos
    have hx' : wPh f x * (gC (t + aPh f k₀ m₀ x) - 1) = 0 := by
      simp only [Pi.zero_apply] at hx; linarith
    have : gC (t + aPh f k₀ m₀ x) = 1 := by
      rcases mul_eq_zero.mp hx' with h1 | h1
      · exact absurd h1 hxpos.ne'
      · linarith
    exact (gC_eq_one_iff _).mp this
  · intro h
    have : ∫ x in cL k₀ m₀..cR k₀ m₀, (wPh f x * gC (t + aPh f k₀ m₀ x) - wPh f x) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      rw [Set.uIoc_of_le hab.le]
      have h' := (ae_restrict_iff' measurableSet_Ioc).mp h
      filter_upwards [h'] with x hx hxI
      by_cases hwpos : 0 < wPh f x
      · obtain ⟨z, hz⟩ := hx hxI hwpos
        rw [hz, gC_int]; ring
      · have : wPh f x = 0 := le_antisymm (not_lt.mp hwpos) (wPh_nonneg f x)
        simp [this]
    rw [hdiff] at this
    linarith

include hf in
lemma max_attained_iff {t : ℝ} :
    PsiP f k₀ m₀ t = 2 * (curvI f k₀ m₀ / Real.sqrt 8) ↔ PointMass f k₀ m₀ t := by
  have hab := cL_lt_cR k₀ m₀
  have hI2 := integrand_intervalIntegrable hf k₀ m₀ measurable_gP abs_gP_le t
  have hw : IntervalIntegrable (wPh f) volume (cL k₀ m₀) (cR k₀ m₀) :=
    (wPh_continuous hf).intervalIntegrable _ _
  have hdiff : ∫ x in cL k₀ m₀..cR k₀ m₀, (2 * wPh f x - wPh f x * gP (t + aPh f k₀ m₀ x)) =
      2 * (curvI f k₀ m₀ / Real.sqrt 8) - PsiP f k₀ m₀ t := by
    rw [intervalIntegral.integral_sub (hw.const_mul 2) hI2, intervalIntegral.integral_const_mul,
      integral_wPh]; rfl
  have hnn : ∀ x, 0 ≤ 2 * wPh f x - wPh f x * gP (t + aPh f k₀ m₀ x) := fun x => by
    nlinarith [wPh_nonneg f x, gP_le_two (t + aPh f k₀ m₀ x)]
  constructor
  · intro h
    have h0 : ∫ x in cL k₀ m₀..cR k₀ m₀,
        (2 * wPh f x - wPh f x * gP (t + aPh f k₀ m₀ x)) = 0 := by
      rw [hdiff, h, sub_self]
    have := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
      (Eventually.of_forall hnn) ((hw.const_mul 2).sub hI2)).mp h0
    filter_upwards [this] with x hx hxpos
    have hx' : wPh f x * (2 - gP (t + aPh f k₀ m₀ x)) = 0 := by
      simp only [Pi.zero_apply] at hx; linarith
    have : gP (t + aPh f k₀ m₀ x) = 2 := by
      rcases mul_eq_zero.mp hx' with h1 | h1
      · exact absurd h1 hxpos.ne'
      · linarith
    exact (gP_eq_two_iff _).mp this
  · intro h
    have : ∫ x in cL k₀ m₀..cR k₀ m₀,
        (2 * wPh f x - wPh f x * gP (t + aPh f k₀ m₀ x)) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      rw [Set.uIoc_of_le hab.le]
      have h' := (ae_restrict_iff' measurableSet_Ioc).mp h
      filter_upwards [h'] with x hx hxI
      by_cases hwpos : 0 < wPh f x
      · obtain ⟨z, hz⟩ := hx hxI hwpos
        rw [hz, gP_int]; ring
      · have : wPh f x = 0 := le_antisymm (not_lt.mp hwpos) (wPh_nonneg f x)
        simp [this]
    rw [hdiff] at this
    linarith

/-- álgebra: fase inteira ⟺ `d ∈ (8/L²) 4^{-t} 4^ℤ` -/
lemma phase_int_iff {L d t : ℝ} (hL : 0 < L) (hd : 0 < d) (z : ℤ) :
    t + Real.logb 4 (L ^ 2 * d / 8) = z ↔ d = 8 / L ^ 2 * (4 : ℝ) ^ (-t) * (4 : ℝ) ^ z := by
  have hy : 0 < L ^ 2 * d / 8 := by positivity
  have h4 : (4 : ℝ) ^ ((z : ℝ) - t) = (4 : ℝ) ^ (-t) * (4 : ℝ) ^ z := by
    rw [show (z : ℝ) - t = -t + z by ring, Real.rpow_add (by norm_num), Real.rpow_intCast]
  constructor
  · intro h
    have h1 := (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hy).mp
      (show Real.logb 4 (L ^ 2 * d / 8) = z - t by linarith)
    rw [h4] at h1
    field_simp
    nlinarith [h1]
  · intro h
    have : L ^ 2 * d / 8 = (4 : ℝ) ^ ((z : ℝ) - t) := by
      rw [h4, h]; field_simp
    rw [this, Real.logb_rpow (by norm_num) (by norm_num)]
    ring

/-- a condição `|f''| ∈ c₀ 4^ℤ` q.t.p. em `{f'' ≠ 0}` -/
def FourPowers (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᵐ x ∂(volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))),
    deriv (deriv f) x ≠ 0 → ∃ z : ℤ, |deriv (deriv f) x| = c₀ * (4 : ℝ) ^ z

lemma wPh_pos_iff (f : ℝ → ℝ) (x : ℝ) : 0 < wPh f x ↔ deriv (deriv f) x ≠ 0 := by
  unfold wPh
  rw [Real.sqrt_pos, div_pos_iff_of_pos_right (by norm_num), abs_pos]

lemma pointMass_iff_fourPowers (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) :
    (∃ t, PointMass f k₀ m₀ t) ↔ FourPowers f k₀ m₀ := by
  have hL : 0 < cR k₀ m₀ - cL k₀ m₀ := sub_pos.mpr (cL_lt_cR k₀ m₀)
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨8 / (cR k₀ m₀ - cL k₀ m₀) ^ 2 * (4 : ℝ) ^ (-t), by positivity, ?_⟩
    filter_upwards [ht] with x hx hne
    obtain ⟨z, hz⟩ := hx ((wPh_pos_iff f x).mpr hne)
    refine ⟨z, ?_⟩
    have hd : 0 < |deriv (deriv f) x| := abs_pos.mpr hne
    exact (phase_int_iff hL hd z).mp hz
  · rintro ⟨c₀, hc₀, h⟩
    set L := cR k₀ m₀ - cL k₀ m₀ with hLdef
    refine ⟨-Real.logb 4 (c₀ * L ^ 2 / 8), ?_⟩
    filter_upwards [h] with x hx hxpos
    have hne := (wPh_pos_iff f x).mp hxpos
    obtain ⟨z, hz⟩ := hx hne
    refine ⟨z, ?_⟩
    have hd : 0 < |deriv (deriv f) x| := abs_pos.mpr hne
    rw [aPh]
    refine (phase_int_iff hL hd z).mpr ?_
    rw [hz, neg_neg, Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    field_simp

include hf in
/-- **III.12.8(d), mínimo**: `m_f = I/√8` ⟺ `|f''| ∈ c₀ 4^ℤ` q.t.p. em `{f'' ≠ 0}` -/
theorem min_attained_iff_fourPowers :
    (∃ t, PsiF f k₀ m₀ t = curvI f k₀ m₀ / Real.sqrt 8) ↔ FourPowers f k₀ m₀ := by
  rw [← pointMass_iff_fourPowers]
  exact ⟨fun ⟨t, h⟩ => ⟨t, (min_attained_iff hf k₀ m₀).mp h⟩,
    fun ⟨t, h⟩ => ⟨t, (min_attained_iff hf k₀ m₀).mpr h⟩⟩

include hf in
/-- **III.12.8(d), máximo**: `M_f = I/√2` ⟺ a mesma condição -/
theorem max_attained_iff_fourPowers :
    (∃ t, PsiP f k₀ m₀ t = 2 * (curvI f k₀ m₀ / Real.sqrt 8)) ↔ FourPowers f k₀ m₀ := by
  rw [← pointMass_iff_fourPowers]
  exact ⟨fun ⟨t, h⟩ => ⟨t, (max_attained_iff hf k₀ m₀).mp h⟩,
    fun ⟨t, h⟩ => ⟨t, (max_attained_iff hf k₀ m₀).mpr h⟩⟩

include hf in
/-- **III.12.8(d)** com os extremos `m_f = min Ψ_f` e `M_f = max Ψ_f⁺` -/
theorem extremes_iff_fourPowers {t₀ t₁ : ℝ}
    (h0 : ∀ t, PsiF f k₀ m₀ t₀ ≤ PsiF f k₀ m₀ t)
    (h1 : ∀ t, PsiP f k₀ m₀ t ≤ PsiP f k₀ m₀ t₁) :
    (PsiF f k₀ m₀ t₀ = curvI f k₀ m₀ / Real.sqrt 8 ↔ FourPowers f k₀ m₀) ∧
    (PsiP f k₀ m₀ t₁ = 2 * (curvI f k₀ m₀ / Real.sqrt 8) ↔ FourPowers f k₀ m₀) := by
  refine ⟨?_, ?_⟩
  · rw [← min_attained_iff_fourPowers hf k₀ m₀]
    refine ⟨fun h => ⟨t₀, h⟩, fun ⟨t, h⟩ => le_antisymm ?_ (psiF_ge hf k₀ m₀ t₀)⟩
    exact (h0 t).trans h.le
  · rw [← max_attained_iff_fourPowers hf k₀ m₀]
    refine ⟨fun h => ⟨t₁, h⟩, fun ⟨t, h⟩ => le_antisymm (psiP_le hf k₀ m₀ t₁) ?_⟩
    exact h.ge.trans (h1 t)

end ext

end Pendencias
