import Pendencias.FaseLei3

/-!
# III.12.7 — a lei de fase (empacotamento)

Com `X(ε) = √ε · n_f(ε)` e fase `u(ε) = -log₄ ε`:

* (i) se `τ` não é fase atômica e `u(ε_j) - z_j → τ`, então `X(ε_j) → Ψ_f(τ)`;
* (ii) se `μ_f` não tem átomos, `X(ε) - Ψ_f(-log₄ ε) → 0` (uniforme);
* (iii) `liminf X = m_f` e `limsup X = M_f` (formas eventual/frequente).
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

section pack

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

/-- extração de sequência `ε_j → 0⁺` com propriedade `P` e fase convergente módulo inteiros -/
lemma exists_phase_subseq {P : ℝ → Prop} (h : ∃ᶠ ε in 𝓝[>] (0 : ℝ), P ε) :
    ∃ (ε : ℕ → ℝ) (z : ℕ → ℤ) (τ : ℝ), (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ j, P (ε j)) ∧ Tendsto (fun j => -Real.logb 4 (ε j) - z j) atTop (𝓝 τ) := by
  have hne : NeBot (𝓝[>] (0 : ℝ) ⊓ 𝓟 {ε | P ε}) := Filter.frequently_iff_neBot.mp h
  obtain ⟨e, he⟩ := Filter.exists_seq_tendsto (𝓝[>] (0 : ℝ) ⊓ 𝓟 {ε | P ε})
  have he1 : Tendsto e atTop (𝓝[>] 0) := he.mono_right inf_le_left
  have he2 : ∀ᶠ j in atTop, P (e j) := tendsto_principal.mp (he.mono_right inf_le_right)
  have he3 : ∀ᶠ j in atTop, 0 < e j := (tendsto_nhdsWithin_iff.mp he1).2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he2.and he3)
  have hε0 : Tendsto (fun j => e (j + N)) atTop (𝓝 0) :=
    (tendsto_nhdsWithin_iff.mp he1).1.comp (tendsto_add_atTop_nat N)
  obtain ⟨τ, -, φ, hφm, hφ⟩ := isCompact_Icc.tendsto_subseq
    (x := fun j => Int.fract (-Real.logb 4 (e (j + N)))) (s := Icc (0 : ℝ) 1)
    (fun j => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
  refine ⟨fun j => e (φ j + N), fun j => ⌊-Real.logb 4 (e (φ j + N))⌋, τ,
    fun j => (hN _ (Nat.le_add_left _ _)).2, hε0.comp hφm.tendsto_atTop,
    fun j => (hN _ (Nat.le_add_left _ _)).1, ?_⟩
  refine hφ.congr fun j => ?_
  exact (Int.self_sub_floor _).symm

include hf in
/-- `Ψ_f` é contínua nas fases não atômicas -/
lemma continuousAt_psiF_of_not_atom {t : ℝ} (ht : ¬ IsAtomPhase f k₀ m₀ t) :
    ContinuousAt (PsiF f k₀ m₀) t := by
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨continuousWithinAt_Iio_iff_Iic.mp (psiF_tendsto_left hf k₀ m₀ t),
    continuousWithinAt_Ioi_iff_Ici.mp ?_⟩
  have := psiF_tendsto_right hf k₀ m₀ t
  rwa [psiP_eq_psiF_of_not_atom hf k₀ m₀ ht] at this

include hf in
/-- **III.12.7 (i)**: convergência em fases não atômicas -/
theorem phase_law_nonatom {ε : ℕ → ℝ} (hε0 : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0))
    {z : ℕ → ℤ} {τ : ℝ} (hτ : ¬ IsAtomPhase f k₀ m₀ τ)
    (hz : Tendsto (fun j => -Real.logb 4 (ε j) - z j) atTop (𝓝 τ)) :
    Tendsto (fun j => Real.sqrt (ε j) * nThr f (ε j) k₀ m₀) atTop (𝓝 (PsiF f k₀ m₀ τ)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · have := phase_lower hf k₀ m₀ hε0 hε hz (PsiF f k₀ m₀ τ - a) (by linarith)
    filter_upwards [this] with j hj
    linarith
  · have := phase_upper hf k₀ m₀ hε0 hε hz (a - PsiF f k₀ m₀ τ) (by linarith)
    rw [psiP_eq_psiF_of_not_atom hf k₀ m₀ hτ] at this
    filter_upwards [this] with j hj
    linarith

include hf in
/-- **III.12.7 (ii)**: lei uniforme sem átomos -/
theorem phase_law_uniform (hno : ∀ t, ¬ IsAtomPhase f k₀ m₀ t) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |Real.sqrt ε * nThr f ε k₀ m₀ - PsiF f k₀ m₀ (-Real.logb 4 ε)| < δ := by
  intro δ hδ
  by_contra hcon
  have hfr : ∃ᶠ ε in 𝓝[>] (0 : ℝ),
      δ ≤ |Real.sqrt ε * nThr f ε k₀ m₀ - PsiF f k₀ m₀ (-Real.logb 4 ε)| :=
    (Filter.not_eventually.mp hcon).mono fun ε h => not_lt.mp h
  obtain ⟨ε, z, τ, hε0, hε, hP, hz⟩ := exists_phase_subseq hfr
  have h1 := phase_law_nonatom hf k₀ m₀ hε0 hε (hno τ) hz
  have h2 : Tendsto (fun j => PsiF f k₀ m₀ (-Real.logb 4 (ε j))) atTop
      (𝓝 (PsiF f k₀ m₀ τ)) := by
    have := (continuousAt_psiF_of_not_atom hf k₀ m₀ (hno τ)).tendsto.comp hz
    refine this.congr fun j => ?_
    show PsiF f k₀ m₀ (-Real.logb 4 (ε j) - z j) = PsiF f k₀ m₀ (-Real.logb 4 (ε j))
    rw [sub_eq_add_neg, ← Int.cast_neg]
    exact psiF_add_int k₀ m₀ _ _
  have h3 := (h1.sub h2)
  rw [sub_self] at h3
  have h4 := (h3.abs).eventually (gt_mem_nhds (show |(0:ℝ)| < δ by simpa using hδ))
  obtain ⟨j, hj⟩ := (h4.and (Eventually.of_forall fun j => hP j)).exists
  exact absurd hj.1 (not_lt.mpr hj.2)

include hf in
/-- **III.12.7 (iii), cota inferior**: `liminf X ≥ m` para toda cota `m ≤ Ψ_f` -/
theorem phase_liminf_ge {m : ℝ} (hm : ∀ t, m ≤ PsiF f k₀ m₀ t) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), m - δ < Real.sqrt ε * nThr f ε k₀ m₀ := by
  intro δ hδ
  by_contra hcon
  have hfr : ∃ᶠ ε in 𝓝[>] (0 : ℝ), Real.sqrt ε * nThr f ε k₀ m₀ ≤ m - δ :=
    (Filter.not_eventually.mp hcon).mono fun ε h => not_lt.mp h
  obtain ⟨ε, z, τ, hε0, hε, hP, hz⟩ := exists_phase_subseq hfr
  have := phase_lower hf k₀ m₀ hε0 hε hz δ hδ
  obtain ⟨j, hj⟩ := (this.and (Eventually.of_forall fun j => hP j)).exists
  linarith [hm τ, hj.1, hj.2]

include hf in
/-- **III.12.7 (iii), cota superior**: `limsup X ≤ M` para toda cota `Ψ_f⁺ ≤ M` -/
theorem phase_limsup_le {M : ℝ} (hM : ∀ t, PsiP f k₀ m₀ t ≤ M) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sqrt ε * nThr f ε k₀ m₀ < M + δ := by
  intro δ hδ
  by_contra hcon
  have hfr : ∃ᶠ ε in 𝓝[>] (0 : ℝ), M + δ ≤ Real.sqrt ε * nThr f ε k₀ m₀ :=
    (Filter.not_eventually.mp hcon).mono fun ε h => not_lt.mp h
  obtain ⟨ε, z, τ, hε0, hε, hP, hz⟩ := exists_phase_subseq hfr
  have := phase_upper hf k₀ m₀ hε0 hε hz δ hδ
  obtain ⟨j, hj⟩ := (this.and (Eventually.of_forall fun j => hP j)).exists
  linarith [hM τ, hj.1, hj.2]

/-- `ε = 4^{-u}` tem fase `u` -/
lemma logb_four_rpow_neg (u : ℝ) : -Real.logb 4 ((4 : ℝ) ^ (-u)) = u := by
  rw [Real.logb_rpow (by norm_num) (by norm_num)]; ring

include hf in
/-- fases não atômicas `τ` dão pontos de acumulação em `Ψ_f(τ)` -/
theorem phase_frequently_nonatom {τ : ℝ} (hτ : ¬ IsAtomPhase f k₀ m₀ τ) :
    ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun j => Real.sqrt (ε j) * nThr f (ε j) k₀ m₀) atTop (𝓝 (PsiF f k₀ m₀ τ)) := by
  set ε : ℕ → ℝ := fun j => (4 : ℝ) ^ (-(τ + j)) with hεdef
  have hε0 : ∀ j, 0 < ε j := fun j => Real.rpow_pos_of_pos (by norm_num) _
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h : Tendsto (fun j : ℕ => -(τ + (j : ℝ))) atTop atBot := by
      refine tendsto_neg_atTop_atBot.comp ?_
      exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_atBot_of_base_gt_one 4 (by norm_num)).comp h
  refine ⟨ε, hε0, hεt, phase_law_nonatom hf k₀ m₀ hε0 hεt hτ (z := fun j => (j : ℤ)) ?_⟩
  refine tendsto_const_nhds.congr fun j => ?_
  simp only [hεdef, logb_four_rpow_neg]
  push_cast; ring

end pack

end Pendencias
