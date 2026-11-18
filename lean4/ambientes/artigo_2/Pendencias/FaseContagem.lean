import RequestProject.DyadicEnvelope

/-!
# III.12.6 — contagem de folhas por células (com tetos)

Versões, com o teto `⌈log₄(A/ε)⌉` do texto, dos lemas `upper_count` e `lower_count` de
`RequestProject.DyadicEnvelope` (que usam a cota em raiz quadrada).

Para a partição de `K = J_{k₀,m₀}` em células `Q_j = J_{k₀+d, j}` e `A_j = μ_j (2^{k₀+d})⁻² / 8`:

* (a) se `|f''| ≤ M_j` em `Q_j`, então `n_f(ε) ≤ ∑_j 2^{thrDepth (M_j ℓ²/8) ε}`;
* (b) se `|f''| ≥ μ_j` em `Q_j` e `ε` é menor que os erros dos ancestrais próprios das células
  com `μ_j > 0`, então `∑_{μ_j>0} 2^{⌈log₄(A_j/ε)⌉} ≤ n_f(ε)`.
-/

namespace Pendencias

open Set Filter Topology Artigo DShape

/-- `A = 0` dá profundidade `0` -/
lemma thrDepth_zero_left (ε : ℝ) : thrDepth 0 ε = 0 := by
  simp [thrDepth]

lemma thrDepth_bound {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    A / 4 ^ thrDepth A ε ≤ ε := by
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0]; simp [hε.le]
  · exact (le_eps_iff_thrDepth_le hpos hε _).mpr le_rfl

/-- **III.12.6(a)**: cota superior com tetos -/
lemma upper_count_pow {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ} {d : ℕ}
    {Mv : ℤ → ℝ} (hM0 : ∀ j, 0 ≤ Mv j)
    (hM : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j, |deriv (deriv f) y| ≤ Mv j)
    {ε : ℝ} (hε : 0 < ε) :
    (nThr f ε k₀ m₀ : ℝ) ≤ ∑ i ∈ Finset.range (2 ^ d),
      (2 : ℝ) ^ thrDepth (Mv (m₀ * 2 ^ d + i) * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8) ε := by
  set q := k₀ + d
  set A : ℤ → ℝ := fun j => Mv j * ((2 : ℝ) ^ q)⁻¹ ^ 2 / 8
  have hA : ∀ j, 0 ≤ A j := fun j => by have := hM0 j; positivity
  set sub : ℤ → DShape := fun j => uniform (thrDepth (A j) ε)
  set T := graft sub d m₀
  have hfeas : T.treeErr f k₀ m₀ ≤ ε := by
    rw [treeErr_le_iff]
    refine allLeaves_graft sub d k₀ m₀ fun i hi => ?_
    set j := m₀ * 2 ^ d + (i : ℤ)
    have hj : j / 2 ^ d = m₀ := desc_index m₀ d i hi
    refine allLeaves_uniform _ _ _ fun i2 hi2 => ?_
    have hsub : cellIcc (q + thrDepth (A j) ε) (j * 2 ^ thrDepth (A j) ε + i2) ⊆ cellIcc q j :=
      cell_sub_of_desc (by omega) (by
        rw [show q + thrDepth (A j) ε - q = thrDepth (A j) ε by omega]
        exact desc_index j _ i2 hi2)
    have := locErr_near hf (c := 0) (w := Mv j)
      (k := q + thrDepth (A j) ε) (m := j * 2 ^ thrDepth (A j) ε + i2)
      (fun y hy => by rw [sub_zero]; exact hM j hj y (hsub hy))
    rw [abs_zero, zero_div, zero_mul, sub_zero, cell_len_desc q _ j, cell_len] at this
    have hle := thrDepth_bound (hA j) hε
    refine le_trans (le_abs_self _) (le_trans this (le_of_eq_of_le ?_ hle))
    simp only [A, div_pow]
    rw [show (4 : ℝ) ^ thrDepth (A j) ε = ((2 : ℝ) ^ thrDepth (A j) ε) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring
  have hn : (nThr f ε k₀ m₀ : ℝ) ≤ T.numLeaves := by
    exact_mod_cast (threshold_optimality hf.continuous.continuousOn hε).2.2.2.2.1 T hfeas
  refine hn.trans (le_of_eq ?_)
  rw [numLeaves_graft]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sub, numLeaves_uniform]
  push_cast
  rfl

/-- **III.12.6(b)**: cota inferior com tetos -/
lemma lower_count_pow {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ} {d : ℕ} {μ : ℤ → ℝ}
    (hμ : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j, μ j ≤ |deriv (deriv f) y|)
    {ε : ℝ} (hε : 0 < ε)
    (hanc : ∀ k' : ℕ, k₀ ≤ k' → k' < k₀ + d → ∀ i : ℕ, i < 2 ^ d → 0 < μ (m₀ * 2 ^ d + i) →
      ε < locErr f k' ((m₀ * 2 ^ d + i) / 2 ^ (k₀ + d - k')))
    {T : DShape} (hT : T.treeErr f k₀ m₀ ≤ ε) :
    ∑ i ∈ Finset.range (2 ^ d), (if 0 < μ (m₀ * 2 ^ d + i) then
        (2 : ℝ) ^ (⌈Real.logb 4 (μ (m₀ * 2 ^ d + i) * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉)
      else 0) ≤ T.numLeaves := by
  set q := k₀ + d with hq
  set sC : ℤ → ℤ := fun j => ⌈Real.logb 4 (μ j * ((2 : ℝ) ^ q)⁻¹ ^ 2 / 8 / ε)⌉ with hsC
  set w : ℤ → ℝ := fun j =>
    if j / 2 ^ d = m₀ then (if 0 < μ j then (2 : ℝ) ^ (sC j) * 2 ^ q else 0) else 0 with hw
  have hleaf : T.AllLeaves (fun k m => cellW q w k m ≤ 1) k₀ m₀ := by
    refine ((treeErr_le_iff T k₀ m₀).mp hT).desc.mono ?_
    rintro k' m' ⟨hk, hm, hle⟩
    unfold cellW
    by_cases hqk : q ≤ k'
    · rw [if_pos hqk]
      set j := m' / 2 ^ (k' - q) with hjdef
      have hj : j / 2 ^ d = m₀ := by
        simp only [j]
        rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add,
          show k' - q + d = k' - k₀ by omega]
        exact hm
      simp only [w, if_pos hj]
      by_cases hpos : 0 < μ j
      · rw [if_pos hpos]
        have hsub : cellIcc k' m' ⊆ cellIcc q j := cell_sub_of_desc hqk rfl
        have hge := locErr_ge_of_abs_deriv2 hf hpos (fun y hy => hμ j hj y (hsub hy))
        rw [cell_len] at hge
        have h1 := hge.trans hle
        obtain ⟨N, hN⟩ := Nat.exists_eq_add_of_le hqk
        have hP : (0 : ℝ) < 2 ^ q := by positivity
        have hR : (0 : ℝ) < 2 ^ N := by positivity
        have hk'2 : (2 : ℝ) ^ k' = 2 ^ q * 2 ^ N := by rw [hN, pow_add]
        have harg : μ j * ((2 : ℝ) ^ q)⁻¹ ^ 2 / 8 / ε ≤ (4 : ℝ) ^ (N : ℝ) := by
          rw [Real.rpow_natCast, show (4 : ℝ) ^ N = (2 ^ N) ^ 2 by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          rw [hk'2] at h1
          have h2 : μ j / 8 * ((2 ^ q * 2 ^ N)⁻¹) ^ 2 ≤ ε := h1
          rw [div_le_iff₀ hε]
          rw [mul_inv, mul_pow] at h2
          have : μ j * ((2 : ℝ) ^ q)⁻¹ ^ 2 / 8 = (μ j / 8 * ((2 ^ q)⁻¹ ^ 2 * ((2 ^ N)⁻¹) ^ 2)) *
              (2 ^ N) ^ 2 := by field_simp
          rw [this]
          calc _ ≤ ε * (2 ^ N) ^ 2 := by gcongr
            _ = _ := by ring
        have hlog : Real.logb 4 (μ j * ((2 : ℝ) ^ q)⁻¹ ^ 2 / 8 / ε) ≤ (N : ℝ) := by
          rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
          exact harg
        have hs : sC j ≤ (N : ℤ) := Int.ceil_le.mpr (by exact_mod_cast hlog)
        have hz : (2 : ℝ) ^ (sC j) ≤ 2 ^ N := by
          have := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hs
          simpa using this
        rw [div_le_one (by positivity), hk'2]
        calc (2 : ℝ) ^ (sC j) * 2 ^ q ≤ 2 ^ N * 2 ^ q := by gcongr
          _ = 2 ^ q * 2 ^ N := by ring
      · rw [if_neg hpos]; simp
    · rw [if_neg hqk]
      apply le_trans (le_of_eq _) zero_le_one
      apply Finset.sum_eq_zero
      intro i hi
      have h0 : w (m' * 2 ^ (q - k') + i) = 0 := by
        simp only [w]
        by_cases hj : (m' * 2 ^ (q - k') + (i : ℤ)) / 2 ^ d = m₀
        · rw [if_pos hj]
          by_cases hpos : 0 < μ (m' * 2 ^ (q - k') + i)
          · exfalso
            obtain ⟨i', hi', hji⟩ := exists_index_of_div hj
            have := hanc k' hk (by omega) i' hi' (by rw [← hji]; exact hpos)
            rw [← hji, desc_index m' (q - k') i (Finset.mem_range.mp hi)] at this
            linarith
          · rw [if_neg hpos]
        · rw [if_neg hj]
      rw [h0, zero_div]
  have hroot := numLeaves_ge_of_weight (cellW q w) (fun k m => (cellW_add q w k m).le) hleaf
  rw [cellW_root k₀ d w m₀] at hroot
  refine le_trans (le_of_eq ?_) hroot
  refine Finset.sum_congr rfl fun i hi => ?_
  have hj := desc_index m₀ d i (Finset.mem_range.mp hi)
  simp only [w, if_pos hj]
  split_ifs with hpos
  · have hP : (0 : ℝ) < 2 ^ q := by positivity
    rw [mul_div_cancel_right₀ _ hP.ne']
  · simp

end Pendencias
