import Pendencias.FaseLei

/-!
# III.12.7 — aproximações por degraus e cotas por integral

Para `n : ℕ` ponha `η_n = 1/(n+1)` e `d_n` uma profundidade em que `√|f''|` oscila `≤ η_n` em
todas as células; `sLow`/`sUp` são `√μ_j` e `√M_j` do texto (`max(s - η, 0)` e `s + η`, com `s` o
valor de `√|f''|` no extremo esquerdo da célula). As cotas inferior e superior de `√ε · n_f(ε)`
por integrais de funções em degraus saem de III.12.6.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo DShape

noncomputable def etaN (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma etaN_pos (n : ℕ) : 0 < etaN n := by unfold etaN; positivity
lemma etaN_le_one (n : ℕ) : etaN n ≤ 1 := by
  unfold etaN; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
lemma etaN_tendsto : Tendsto etaN atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

section approx

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

noncomputable def depthN (n : ℕ) : ℕ := (exists_depth_osc hf k₀ m₀ (etaN_pos n)).choose

lemma depthN_spec (n : ℕ) : ∀ j : ℤ, j / 2 ^ (depthN hf k₀ m₀ n) = m₀ →
    ∀ y ∈ cellIcc (k₀ + depthN hf k₀ m₀ n) j,
      |sqc f y - sqc f (cL (k₀ + depthN hf k₀ m₀ n) j)| ≤ etaN n :=
  (exists_depth_osc hf k₀ m₀ (etaN_pos n)).choose_spec

noncomputable def sLow (n : ℕ) (j : ℤ) : ℝ :=
  max (sqc f (cL (k₀ + depthN hf k₀ m₀ n) j) - etaN n) 0

noncomputable def sUp (n : ℕ) (j : ℤ) : ℝ :=
  sqc f (cL (k₀ + depthN hf k₀ m₀ n) j) + etaN n

lemma sLow_nonneg (n : ℕ) (j : ℤ) : 0 ≤ sLow hf k₀ m₀ n j := le_max_right _ _
lemma sUp_pos (n : ℕ) (j : ℤ) : 0 < sUp hf k₀ m₀ n j := by
  unfold sUp; linarith [sqc_nonneg f (cL (k₀ + depthN hf k₀ m₀ n) j), etaN_pos n]

lemma sLow_le {n : ℕ} {j : ℤ} (hj : j / 2 ^ (depthN hf k₀ m₀ n) = m₀) {y : ℝ}
    (hy : y ∈ cellIcc (k₀ + depthN hf k₀ m₀ n) j) : sLow hf k₀ m₀ n j ≤ sqc f y := by
  have := (abs_le.mp (depthN_spec hf k₀ m₀ n j hj y hy)).1
  unfold sLow; exact max_le (by linarith) (sqc_nonneg f y)

lemma le_sUp {n : ℕ} {j : ℤ} (hj : j / 2 ^ (depthN hf k₀ m₀ n) = m₀) {y : ℝ}
    (hy : y ∈ cellIcc (k₀ + depthN hf k₀ m₀ n) j) : sqc f y ≤ sUp hf k₀ m₀ n j := by
  have := (abs_le.mp (depthN_spec hf k₀ m₀ n j hj y hy)).2
  unfold sUp; linarith

lemma sLow_close {n : ℕ} {j : ℤ} (hj : j / 2 ^ (depthN hf k₀ m₀ n) = m₀) {y : ℝ}
    (hy : y ∈ cellIcc (k₀ + depthN hf k₀ m₀ n) j) :
    |sLow hf k₀ m₀ n j - sqc f y| ≤ 2 * etaN n := by
  have h1 := abs_le.mp (depthN_spec hf k₀ m₀ n j hj y hy)
  have h2 := sLow_le hf k₀ m₀ hj hy
  have h3 : sqc f y - 2 * etaN n ≤ sLow hf k₀ m₀ n j := by
    unfold sLow
    exact le_trans (by linarith [h1.1, h1.2]) (le_max_left _ _)
  rw [abs_le]; constructor <;> linarith

lemma sUp_close {n : ℕ} {j : ℤ} (hj : j / 2 ^ (depthN hf k₀ m₀ n) = m₀) {y : ℝ}
    (hy : y ∈ cellIcc (k₀ + depthN hf k₀ m₀ n) j) :
    |sUp hf k₀ m₀ n j - sqc f y| ≤ 2 * etaN n := by
  have h1 := abs_le.mp (depthN_spec hf k₀ m₀ n j hj y hy)
  unfold sUp; rw [abs_le]; constructor <;> linarith [h1.1, h1.2]

include hf in
/-- limiar dos ancestrais -/
lemma exists_anc_threshold {d : ℕ} {μ : ℤ → ℝ}
    (hμ : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j, μ j ≤ |deriv (deriv f) y|) :
    ∃ ε₂ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₂ → ∀ k' : ℕ, k₀ ≤ k' → k' < k₀ + d → ∀ i : ℕ, i < 2 ^ d →
      0 < μ (m₀ * 2 ^ d + i) →
      ε < locErr f k' ((m₀ * 2 ^ d + i) / 2 ^ (k₀ + d - k')) := by
  set q := k₀ + d
  set S := ((Finset.range d) ×ˢ (Finset.range (2 ^ d))).filter
    (fun p : ℕ × ℕ => 0 < μ (m₀ * 2 ^ d + p.2))
  obtain ⟨ε₂, hε₂, hS⟩ := exists_pos_le_all S
    (fun p => locErr f (k₀ + p.1) ((m₀ * 2 ^ d + p.2) / 2 ^ (d - p.1))) (by
      intro p hp
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨⟨hp1, hp2⟩, hpos⟩ := hp
      set j := m₀ * 2 ^ d + (p.2 : ℤ)
      have hj : j / 2 ^ d = m₀ := desc_index m₀ d p.2 hp2
      have hsub : cellIcc q j ⊆ cellIcc (k₀ + p.1) (j / 2 ^ (d - p.1)) :=
        cell_sub_of_desc (by omega) (by rw [show q - (k₀ + p.1) = d - p.1 by omega])
      have hQ := locErr_ge_of_abs_deriv2 hf hpos (hμ j hj)
      have hQpos : 0 < locErr f q j := lt_of_lt_of_le (by
        have := cL_lt_cR q j
        have : 0 < (cR q j - cL q j) ^ 2 := by nlinarith
        positivity) hQ
      exact locErr_pos_of_sub hf.continuous.continuousOn hsub hQpos)
  refine ⟨ε₂, hε₂, fun ε hε hlt k' hk hk' i hi hpos => ?_⟩
  have := hS (k' - k₀, i) (by
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, hi⟩, hpos⟩)
  simp only at this
  rw [show k₀ + (k' - k₀) = k' by omega, show d - (k' - k₀) = k₀ + d - k' by omega] at this
  exact lt_of_lt_of_le hlt this

end approx

section bounds

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

noncomputable def Gl (n : ℕ) (ε : ℝ) (j : ℤ) : ℝ :=
  sLow hf k₀ m₀ n j / Real.sqrt 8 *
    gC (-Real.logb 4 ε + Real.logb 4 (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * (sLow hf k₀ m₀ n j) ^ 2 / 8))

noncomputable def Gu (n : ℕ) (ε : ℝ) (j : ℤ) : ℝ :=
  sUp hf k₀ m₀ n j / Real.sqrt 8 *
    gC (-Real.logb 4 ε + Real.logb 4 (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * (sUp hf k₀ m₀ n j) ^ 2 / 8))

lemma pow_toNat_le (z : ℤ) : (2 : ℝ) ^ z.toNat ≤ 1 + (2 : ℝ) ^ z := by
  rcases le_or_gt 0 z with h | h
  · have : (2 : ℝ) ^ z = 2 ^ z.toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg h]
    rw [this]; linarith [pow_pos (show (0 : ℝ) < 2 by norm_num) z.toNat]
  · rw [Int.toNat_of_nonpos h.le]
    simp only [pow_zero]
    linarith [zpow_pos (show (0 : ℝ) < 2 by norm_num) z]

include hf in
lemma lower_integral_bound (n : ℕ) : ∃ ε₂ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₂ →
    ∫ x in cL k₀ m₀..cR k₀ m₀, Gl hf k₀ m₀ n ε (cidx (k₀ + depthN hf k₀ m₀ n) x) ≤
      Real.sqrt ε * nThr f ε k₀ m₀ := by
  set d := depthN hf k₀ m₀ n
  have hμ : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j,
      (sLow hf k₀ m₀ n j) ^ 2 ≤ |deriv (deriv f) y| := by
    intro j hj y hy
    rw [← sqc_sq]
    exact pow_le_pow_left₀ (sLow_nonneg hf k₀ m₀ n j) (sLow_le hf k₀ m₀ hj hy) 2
  obtain ⟨ε₂, hε₂, hanc⟩ := exists_anc_threshold hf k₀ m₀
    (μ := fun j => (sLow hf k₀ m₀ n j) ^ 2) hμ
  refine ⟨ε₂, hε₂, fun ε hε hlt => ?_⟩
  have hthr := (threshold_optimality (k := k₀) (m := m₀) hf.continuous.continuousOn hε).2.1
  have hlow := lower_count_pow hf (μ := fun j => (sLow hf k₀ m₀ n j) ^ 2) hμ hε
    (hanc ε hε hlt) hthr
  rw [step_integral]
  have hsq : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hn : ((thrTree f ε k₀ m₀).numLeaves : ℝ) = (nThr f ε k₀ m₀ : ℝ) := rfl
  rw [hn] at hlow
  calc ∑ i ∈ Finset.range (2 ^ d), Gl hf k₀ m₀ n ε (m₀ * 2 ^ d + i) / 2 ^ (k₀ + d)
      = Real.sqrt ε * ∑ i ∈ Finset.range (2 ^ d),
          (if 0 < (sLow hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 then
            (2 : ℝ) ^ (⌈Real.logb 4 ((sLow hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 *
              ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hpos : 0 < sLow hf k₀ m₀ n (m₀ * 2 ^ d + i)
        · have hp2 : 0 < (sLow hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 := by positivity
          rw [if_pos hp2, cell_term_eq k₀ d hpos hε]
          unfold Gl; ring
        · have h0 : sLow hf k₀ m₀ n (m₀ * 2 ^ d + i) = 0 :=
            le_antisymm (not_lt.mp hpos) (sLow_nonneg hf k₀ m₀ n _)
          rw [if_neg (by rw [h0]; simp)]
          unfold Gl; rw [h0]; simp
    _ ≤ Real.sqrt ε * nThr f ε k₀ m₀ := mul_le_mul_of_nonneg_left hlow hsq

include hf in
lemma upper_integral_bound (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt ε * nThr f ε k₀ m₀ ≤ 2 ^ (depthN hf k₀ m₀ n) * Real.sqrt ε +
      ∫ x in cL k₀ m₀..cR k₀ m₀, Gu hf k₀ m₀ n ε (cidx (k₀ + depthN hf k₀ m₀ n) x) := by
  set d := depthN hf k₀ m₀ n
  have hM : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j,
      |deriv (deriv f) y| ≤ (sUp hf k₀ m₀ n j) ^ 2 := by
    intro j hj y hy
    rw [← sqc_sq]
    exact pow_le_pow_left₀ (sqc_nonneg f y) (le_sUp hf k₀ m₀ hj hy) 2
  have hup := upper_count_pow hf (Mv := fun j => (sUp hf k₀ m₀ n j) ^ 2)
    (fun j => sq_nonneg _) hM hε
  rw [step_integral]
  have hsq : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  calc Real.sqrt ε * (nThr f ε k₀ m₀ : ℝ)
      ≤ Real.sqrt ε * ∑ i ∈ Finset.range (2 ^ d),
          (2 : ℝ) ^ thrDepth ((sUp hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 *
            ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8) ε := mul_le_mul_of_nonneg_left hup hsq
    _ = ∑ i ∈ Finset.range (2 ^ d), Real.sqrt ε * (2 : ℝ) ^ thrDepth
          ((sUp hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8) ε := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (2 ^ d),
          (Real.sqrt ε + Gu hf k₀ m₀ n ε (m₀ * 2 ^ d + i) / 2 ^ (k₀ + d)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hpos := sUp_pos hf k₀ m₀ n (m₀ * 2 ^ d + i)
        have hcell := cell_term_eq k₀ d hpos hε
        unfold thrDepth
        have h1 := pow_toNat_le ⌈Real.logb 4 ((sUp hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 *
          ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉
        have h2 : (2 : ℝ) ^ (⌈Real.logb 4 ((sUp hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 *
          ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / (ε))⌉).toNat ≤ _ := h1
        calc Real.sqrt ε * (2 : ℝ) ^ (⌈Real.logb 4 ((sUp hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 *
              ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉).toNat
            ≤ Real.sqrt ε * (1 + (2 : ℝ) ^ (⌈Real.logb 4 ((sUp hf k₀ m₀ n (m₀ * 2 ^ d + i)) ^ 2 *
              ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉)) := mul_le_mul_of_nonneg_left h1 hsq
          _ = Real.sqrt ε + Real.sqrt ε * (2 : ℝ) ^ (⌈Real.logb 4 ((sUp hf k₀ m₀ n
              (m₀ * 2 ^ d + i)) ^ 2 * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉) := by ring
          _ = _ := by rw [hcell]; unfold Gu; ring
    _ = 2 ^ d * Real.sqrt ε + ∑ i ∈ Finset.range (2 ^ d),
          Gu hf k₀ m₀ n ε (m₀ * 2 ^ d + i) / 2 ^ (k₀ + d) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_range]

end bounds

end Pendencias
