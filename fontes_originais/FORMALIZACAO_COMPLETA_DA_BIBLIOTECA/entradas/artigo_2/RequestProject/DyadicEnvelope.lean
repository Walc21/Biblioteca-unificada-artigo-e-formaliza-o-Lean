import RequestProject.DyadicPhase

/-!
# Theorem 11.3 — the universal dyadic envelope
-/

namespace Artigo

open Set Filter Topology MeasureTheory DShape

/-- `√|f''|` -/
noncomputable def sqc (f : ℝ → ℝ) (x : ℝ) : ℝ := Real.sqrt |deriv (deriv f) x|

/-- the curvature functional `I(f) = ∫_K √|f''|` on `K = J_{k,m}` -/
noncomputable def curvI (f : ℝ → ℝ) (k : ℕ) (m : ℤ) : ℝ :=
  ∫ x in cL k m..cR k m, Real.sqrt |deriv (deriv f) x|

lemma sqc_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (sqc f) :=
  (C2_continuous_deriv2 hf).abs.sqrt

lemma sqc_nonneg (f : ℝ → ℝ) (x : ℝ) : 0 ≤ sqc f x := Real.sqrt_nonneg _

lemma sqc_sq (f : ℝ → ℝ) (x : ℝ) : sqc f x ^ 2 = |deriv (deriv f) x| :=
  Real.sq_sqrt (abs_nonneg _)

lemma desc_cell_sub_root (k₀ d : ℕ) (m₀ j : ℤ) (hj : j / 2 ^ d = m₀) :
    cellIcc (k₀ + d) j ⊆ cellIcc k₀ m₀ :=
  cell_sub_of_desc (by omega) (by rw [show k₀ + d - k₀ = d by omega]; exact hj)

lemma exists_index_of_div {d : ℕ} {m₀ j : ℤ} (hj : j / 2 ^ d = m₀) :
    ∃ i : ℕ, i < 2 ^ d ∧ j = m₀ * 2 ^ d + i := by
  have hP : (0 : ℤ) < 2 ^ d := by positivity
  have h1 : m₀ * 2 ^ d ≤ j := hj ▸ Int.ediv_mul_le j hP.ne'
  have h2 : j < (m₀ + 1) * 2 ^ d := hj ▸ Int.lt_ediv_add_one_mul_self j hP
  refine ⟨(j - m₀ * 2 ^ d).toNat, ?_, ?_⟩
  · have : j - m₀ * 2 ^ d < 2 ^ d := by linarith
    have h3 : ((j - m₀ * 2 ^ d).toNat : ℤ) < ((2 ^ d : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg (by linarith)]; push_cast; exact this
    exact_mod_cast h3
  · rw [Int.toNat_of_nonneg (by linarith)]; ring

lemma cL_desc_zero (k₀ d : ℕ) (m₀ : ℤ) : cL (k₀ + d) (m₀ * 2 ^ d) = cL k₀ m₀ := by
  unfold cL; push_cast; rw [pow_add]; field_simp

lemma cL_desc_top (k₀ d : ℕ) (m₀ : ℤ) :
    cL (k₀ + d) (m₀ * 2 ^ d + ((2 ^ d : ℕ) : ℤ)) = cR k₀ m₀ := by
  unfold cL cR; push_cast; rw [pow_add]; field_simp

lemma cL_desc_succ (q : ℕ) (j : ℤ) (i : ℕ) :
    cL q (j + ((i + 1 : ℕ) : ℤ)) = cR q (j + i) := by
  unfold cL cR; push_cast; ring

/-- uniform continuity of `√|f''|`: a depth where it oscillates by at most `η` on every cell -/
lemma exists_depth_osc {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ) {η : ℝ}
    (hη : 0 < η) : ∃ d : ℕ, ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j,
      |sqc f y - sqc f (cL (k₀ + d) j)| ≤ η := by
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (sqc_continuous hf).continuousOn
      (s := cellIcc k₀ m₀)) η hη
  obtain ⟨d, hd⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨d, fun j hj y hy => ?_⟩
  have hsub := desc_cell_sub_root k₀ d m₀ j hj
  have hab := cL_lt_cR (k₀ + d) j
  have hx : cL (k₀ + d) j ∈ cellIcc (k₀ + d) j := by
    rw [cellIcc_eq]; exact left_mem_Icc.mpr hab.le
  have hlen : cR (k₀ + d) j - cL (k₀ + d) j < δ := by
    rw [cell_len]
    calc ((2 : ℝ) ^ (k₀ + d))⁻¹ = (1 / 2) ^ (k₀ + d) := by rw [one_div, inv_pow]
      _ ≤ (1 / 2) ^ d := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ < δ := hd
  have hy' := hy
  rw [cellIcc_eq] at hy'
  have := hU y (hsub hy) _ (hsub hx) (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy'.1, hy'.2])
  rw [Real.dist_eq] at this
  exact this.le

/-- Riemann-sum approximation of `I(f)` on the level-`(k₀+d)` partition -/
lemma riemann_approx {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ} {d : ℕ} {η : ℝ}
    (hosc : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j,
      |sqc f y - sqc f (cL (k₀ + d) j)| ≤ η) :
    |curvI f k₀ m₀ - ∑ i ∈ Finset.range (2 ^ d),
      sqc f (cL (k₀ + d) (m₀ * 2 ^ d + i)) / 2 ^ (k₀ + d)| ≤ η / 2 ^ k₀ := by
  set q := k₀ + d
  set a : ℕ → ℝ := fun i => cL q (m₀ * 2 ^ d + i)
  have hcont := sqc_continuous hf
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := sqc f) (μ := volume)
    (a := a) (n := 2 ^ d) (fun i _ => hcont.intervalIntegrable _ _)
  have h0 : a 0 = cL k₀ m₀ := by simp [a, q, cL_desc_zero]
  have h1 : a (2 ^ d) = cR k₀ m₀ := cL_desc_top k₀ d m₀
  rw [h0, h1] at hsum
  have hcI : curvI f k₀ m₀ = ∫ x in cL k₀ m₀..cR k₀ m₀, sqc f x := rfl
  rw [hcI, ← hsum, ← Finset.sum_sub_distrib]
  have hterm : ∀ i ∈ Finset.range (2 ^ d), |(∫ x in a i..a (i + 1), sqc f x) -
      sqc f (cL q (m₀ * 2 ^ d + i)) / 2 ^ q| ≤ η / 2 ^ q := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hj : (m₀ * 2 ^ d + i) / 2 ^ d = m₀ := desc_index m₀ d i hi'
    have ha1 : a (i + 1) = cR q (m₀ * 2 ^ d + i) := cL_desc_succ q _ i
    have hlen : a (i + 1) - a i = 1 / 2 ^ q := by rw [ha1, cell_len]; simp
    have e : (∫ x in a i..a (i + 1), sqc f x) - sqc f (cL q (m₀ * 2 ^ d + i)) / 2 ^ q =
        ∫ x in a i..a (i + 1), (sqc f x - sqc f (cL q (m₀ * 2 ^ d + i))) := by
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const, hlen, smul_eq_mul]
      ring
    rw [e]
    have hle : a i ≤ a (i + 1) := by linarith [show (0 : ℝ) < 1 / 2 ^ q by positivity]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a i) (b := a (i + 1))
      (C := η) (f := fun x => sqc f x - sqc f (cL q (m₀ * 2 ^ d + i))) (fun x hx => by
        rw [uIoc_of_le hle] at hx
        rw [Real.norm_eq_abs]
        apply hosc _ hj
        rw [cellIcc_eq, ← ha1]
        exact ⟨hx.1.le, hx.2⟩)
    rw [Real.norm_eq_abs, hlen, abs_of_pos (show (0 : ℝ) < 1 / 2 ^ q by positivity)] at this
    calc _ ≤ η * (1 / 2 ^ q) := this
      _ = η / 2 ^ q := by ring
  calc _ ≤ ∑ i ∈ Finset.range (2 ^ d), |(∫ x in a i..a (i + 1), sqc f x) -
        sqc f (cL q (m₀ * 2 ^ d + i)) / 2 ^ q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2 ^ d), η / 2 ^ q := Finset.sum_le_sum hterm
    _ = η / 2 ^ k₀ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        simp only [q, pow_add]; push_cast; field_simp

lemma cellW_root (k d : ℕ) (w : ℤ → ℝ) (m : ℤ) :
    cellW (k + d) w k m = ∑ i ∈ Finset.range (2 ^ d), w (m * 2 ^ d + i) / 2 ^ (k + d) := by
  unfold cellW
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [if_neg (by omega), show k + d - k = d by omega]

/-- **lower count**: if `|f''| ≥ μⱼ` on the level-`(k₀+d)` cells `Qⱼ` and `ε` is below the local
errors of all proper ancestors of the cells with `μⱼ > 0`, then every feasible tree has at least
`∑ⱼ √μⱼ |Qⱼ| / √(8ε)` leaves. -/
lemma lower_count {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ} {d : ℕ} {μ : ℤ → ℝ}
    (hμ0 : ∀ j, 0 ≤ μ j)
    (hμ : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j, μ j ≤ |deriv (deriv f) y|)
    {ε : ℝ} (hε : 0 < ε)
    (hanc : ∀ k' : ℕ, k₀ ≤ k' → k' < k₀ + d → ∀ i : ℕ, i < 2 ^ d → 0 < μ (m₀ * 2 ^ d + i) →
      ε < locErr f k' ((m₀ * 2 ^ d + i) / 2 ^ (k₀ + d - k')))
    {T : DShape} (hT : T.treeErr f k₀ m₀ ≤ ε) :
    ∑ i ∈ Finset.range (2 ^ d), Real.sqrt (μ (m₀ * 2 ^ d + i)) / 2 ^ (k₀ + d) ≤
      Real.sqrt (8 * ε) * T.numLeaves := by
  set q := k₀ + d
  have hs : 0 < Real.sqrt (8 * ε) := Real.sqrt_pos.mpr (by positivity)
  set w : ℤ → ℝ := fun j => if j / 2 ^ d = m₀ then Real.sqrt (μ j) / Real.sqrt (8 * ε) else 0
  have hleaf : T.AllLeaves (fun k m => cellW q w k m ≤ 1) k₀ m₀ := by
    refine ((treeErr_le_iff T k₀ m₀).mp hT).desc.mono ?_
    rintro k' m' ⟨hk, hm, hle⟩
    unfold cellW
    by_cases hqk : q ≤ k'
    · rw [if_pos hqk]
      set j := m' / 2 ^ (k' - q)
      have hj : j / 2 ^ d = m₀ := by
        simp only [j]
        rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add,
          show k' - q + d = k' - k₀ by omega]
        exact hm
      simp only [w, if_pos hj]
      rcases (hμ0 j).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have hsub : cellIcc k' m' ⊆ cellIcc q j := cell_sub_of_desc hqk rfl
        have hge := locErr_ge_of_abs_deriv2 hf hpos (fun y hy => hμ j hj y (hsub hy))
        rw [cell_len] at hge
        have h1 := hge.trans hle
        have hp : (0 : ℝ) < 2 ^ k' := by positivity
        have key : μ j / 8 * ((2 : ℝ) ^ k')⁻¹ ^ 2 * (8 * (2 ^ k') ^ 2) = μ j := by
          field_simp
        have h2 : μ j ≤ 8 * ε * (2 ^ k') ^ 2 := by
          have := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ 8 * (2 ^ k') ^ 2 by positivity)
          rw [key] at this; linarith
        rw [div_div, div_le_one (by positivity)]
        calc Real.sqrt (μ j) ≤ Real.sqrt (8 * ε * (2 ^ k') ^ 2) := Real.sqrt_le_sqrt h2
          _ = Real.sqrt (8 * ε) * 2 ^ k' := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]
    · rw [if_neg hqk]
      apply le_trans (le_of_eq _) zero_le_one
      apply Finset.sum_eq_zero
      intro i hi
      simp only [w]
      split_ifs with hj
      · obtain ⟨i', hi', hji⟩ := exists_index_of_div hj
        rcases (hμ0 (m' * 2 ^ (q - k') + i)).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · exfalso
          have := hanc k' hk (by omega) i' hi' (by rw [← hji]; exact hpos)
          rw [← hji, desc_index m' (q - k') i (Finset.mem_range.mp hi)] at this
          linarith
      · simp
  have hroot := numLeaves_ge_of_weight (cellW q w) (fun k m => (cellW_add q w k m).le) hleaf
  rw [cellW_root k₀ d w m₀] at hroot
  have hw : ∀ i ∈ Finset.range (2 ^ d), w (m₀ * 2 ^ d + i) / 2 ^ q =
      (Real.sqrt (μ (m₀ * 2 ^ d + i)) / 2 ^ q) / Real.sqrt (8 * ε) := by
    intro i hi
    simp only [w, if_pos (desc_index m₀ d i (Finset.mem_range.mp hi))]
    ring
  rw [Finset.sum_congr rfl hw, ← Finset.sum_div, div_le_iff₀ hs] at hroot
  linarith

lemma two_pow_thrDepth_le {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    (2 : ℝ) ^ thrDepth A ε ≤ 1 + 2 * Real.sqrt (A / ε) := by
  rcases Nat.eq_zero_or_pos (thrDepth A ε) with h0 | hpos
  · rw [h0]; simp
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_lt hpos
    have hnot : ¬ A / 4 ^ e ≤ ε := fun h => by
      have := (le_eps_iff_thrDepth_le hA hε e).mp h; omega
    push_neg at hnot
    have h4 : (4 : ℝ) ^ e < A / ε := by
      rw [lt_div_iff₀ hε]; rw [lt_div_iff₀ (by positivity)] at hnot; linarith
    have h2 : (2 : ℝ) ^ e < Real.sqrt (A / ε) := by
      rw [show (2 : ℝ) ^ e = Real.sqrt (4 ^ e) by
        rw [show (4 : ℝ) ^ e = (2 ^ e) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
          Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_lt_sqrt (by positivity) h4
    rw [he, zero_add, pow_succ]
    linarith

/-- **upper count**: if `|f''| ≤ Mⱼ` on the level-`(k₀+d)` cells `Qⱼ`, then
`n_f(ε) ≤ 2^d + ∑ⱼ √Mⱼ |Qⱼ| / √(2ε)`. -/
lemma upper_count {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ} {d : ℕ} {Mv : ℤ → ℝ}
    (hM0 : ∀ j, 0 < Mv j)
    (hM : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j, |deriv (deriv f) y| ≤ Mv j)
    {ε : ℝ} (hε : 0 < ε) :
    (nThr f ε k₀ m₀ : ℝ) ≤ 2 ^ d + ∑ i ∈ Finset.range (2 ^ d),
      Real.sqrt (Mv (m₀ * 2 ^ d + i)) / 2 ^ (k₀ + d) / Real.sqrt (2 * ε) := by
  set q := k₀ + d
  set A : ℤ → ℝ := fun j => Mv j * ((2 : ℝ) ^ q)⁻¹ ^ 2 / 8
  have hA : ∀ j, 0 < A j := fun j => by have := hM0 j; positivity
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
    have hle := (le_eps_iff_thrDepth_le (hA j) hε (thrDepth (A j) ε)).mpr le_rfl
    refine le_trans (le_abs_self _) (le_trans this (le_of_eq_of_le ?_ hle))
    simp only [A, div_pow]
    rw [show (4 : ℝ) ^ thrDepth (A j) ε = ((2 : ℝ) ^ thrDepth (A j) ε) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring
  have hn : (nThr f ε k₀ m₀ : ℝ) ≤ T.numLeaves := by
    exact_mod_cast (threshold_optimality hf.continuous.continuousOn hε).2.2.2.2.1 T hfeas
  refine hn.trans ?_
  rw [numLeaves_graft]
  have hterm : ∀ i ∈ Finset.range (2 ^ d), ((sub (m₀ * 2 ^ d + i)).numLeaves : ℝ) ≤
      1 + Real.sqrt (Mv (m₀ * 2 ^ d + i)) / 2 ^ q / Real.sqrt (2 * ε) := by
    intro i _
    set j := m₀ * 2 ^ d + (i : ℤ)
    simp only [sub, numLeaves_uniform]
    push_cast
    refine (two_pow_thrDepth_le (hA j) hε).trans (le_of_eq ?_)
    congr 1
    have h1 : 0 ≤ 2 * Real.sqrt (A j / ε) := by positivity
    have h2 : 0 ≤ Real.sqrt (Mv j) / 2 ^ q / Real.sqrt (2 * ε) := by positivity
    refine (sq_eq_sq₀ h1 h2).mp ?_
    rw [mul_pow, div_pow, div_pow, Real.sq_sqrt (div_pos (hA j) hε).le,
      Real.sq_sqrt (hM0 j).le, Real.sq_sqrt (by positivity)]
    simp only [A]
    field_simp
    ring
  calc _ ≤ ∑ i ∈ Finset.range (2 ^ d),
        (1 + Real.sqrt (Mv (m₀ * 2 ^ d + i)) / 2 ^ q / Real.sqrt (2 * ε)) :=
        Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- the lower half of the threshold envelope -/
lemma envelope_lower {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      curvI f k₀ m₀ / Real.sqrt 8 - δ ≤ Real.sqrt ε * nThr f ε k₀ m₀ := by
  have h8 : 0 < Real.sqrt 8 := by positivity
  set η := δ * Real.sqrt 8 * 2 ^ k₀ / 2
  have hη : 0 < η := by positivity
  obtain ⟨d, hosc⟩ := exists_depth_osc hf k₀ m₀ hη
  have hR := riemann_approx hf hosc
  set q := k₀ + d
  set μ : ℤ → ℝ := fun j => (max (sqc f (cL q j) - η) 0) ^ 2
  have hμ0 : ∀ j, 0 ≤ μ j := fun j => sq_nonneg _
  have hμ : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc q j, μ j ≤ |deriv (deriv f) y| := by
    intro j hj y hy
    have h1 := hosc j hj y hy
    rw [← sqc_sq]
    apply pow_le_pow_left₀ (le_max_right _ _)
    refine max_le ?_ (sqc_nonneg f y)
    linarith [(abs_le.mp h1).1]
  -- positivity of the ancestors' errors
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
  filter_upwards [Ioo_mem_nhdsGT hε₂] with ε hε
  have hanc : ∀ k' : ℕ, k₀ ≤ k' → k' < k₀ + d → ∀ i : ℕ, i < 2 ^ d →
      0 < μ (m₀ * 2 ^ d + i) → ε < locErr f k' ((m₀ * 2 ^ d + i) / 2 ^ (k₀ + d - k')) := by
    intro k' hk hk' i hi hpos
    have := hS (k' - k₀, i) (by
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, hi⟩, hpos⟩)
    simp only at this
    rw [show k₀ + (k' - k₀) = k' by omega, show d - (k' - k₀) = k₀ + d - k' by omega] at this
    exact lt_of_lt_of_le hε.2 this
  have hthr := (threshold_optimality (k := k₀) (m := m₀) hf.continuous.continuousOn hε.1).2.1
  have hlow := lower_count hf hμ0 hμ hε.1 hanc hthr
  change _ ≤ Real.sqrt (8 * ε) * (nThr f ε k₀ m₀ : ℝ) at hlow
  -- `∑ √μⱼ |Qⱼ| ≥ R - η|K| ≥ I - 2η|K|`
  have hsum : curvI f k₀ m₀ - 2 * η / 2 ^ k₀ ≤
      ∑ i ∈ Finset.range (2 ^ d), Real.sqrt (μ (m₀ * 2 ^ d + i)) / 2 ^ q := by
    have h1 : ∑ i ∈ Finset.range (2 ^ d), (sqc f (cL q (m₀ * 2 ^ d + i)) - η) / 2 ^ q ≤
        ∑ i ∈ Finset.range (2 ^ d), Real.sqrt (μ (m₀ * 2 ^ d + i)) / 2 ^ q := by
      apply Finset.sum_le_sum
      intro i _
      simp only [μ]
      rw [Real.sqrt_sq (le_max_right _ _)]
      gcongr
      exact le_max_left _ _
    have h2 : ∑ i ∈ Finset.range (2 ^ d), (sqc f (cL q (m₀ * 2 ^ d + i)) - η) / 2 ^ q =
        ∑ i ∈ Finset.range (2 ^ d), sqc f (cL q (m₀ * 2 ^ d + i)) / 2 ^ q - η / 2 ^ k₀ := by
      simp only [sub_div]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      simp only [q, pow_add]; push_cast; field_simp
    have h3 := (abs_le.mp hR).2
    calc curvI f k₀ m₀ - 2 * η / 2 ^ k₀ = (curvI f k₀ m₀ - η / 2 ^ k₀) - η / 2 ^ k₀ := by ring
      _ ≤ ∑ i ∈ Finset.range (2 ^ d), sqc f (cL q (m₀ * 2 ^ d + i)) / 2 ^ q - η / 2 ^ k₀ := by
          linarith
      _ = _ := h2.symm
      _ ≤ _ := h1
  rw [Real.sqrt_mul (by norm_num)] at hlow
  have hfin : curvI f k₀ m₀ / Real.sqrt 8 - δ =
      (curvI f k₀ m₀ - 2 * η / 2 ^ k₀) / Real.sqrt 8 := by
    simp only [η]; field_simp
  rw [hfin, div_le_iff₀ h8]
  nlinarith

/-- the upper half of the threshold envelope -/
lemma envelope_upper {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Real.sqrt ε * nThr f ε k₀ m₀ ≤ curvI f k₀ m₀ / Real.sqrt 2 + δ := by
  have h2 : 0 < Real.sqrt 2 := by positivity
  set η := δ * Real.sqrt 2 * 2 ^ k₀ / 4
  have hη : 0 < η := by positivity
  obtain ⟨d, hosc⟩ := exists_depth_osc hf k₀ m₀ hη
  have hR := riemann_approx hf hosc
  set q := k₀ + d
  set Mv : ℤ → ℝ := fun j => (sqc f (cL q j) + η) ^ 2
  have hM0 : ∀ j, 0 < Mv j := fun j => by have := sqc_nonneg f (cL q j); positivity
  have hM : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc q j, |deriv (deriv f) y| ≤ Mv j := by
    intro j hj y hy
    have h1 := hosc j hj y hy
    rw [← sqc_sq]
    exact pow_le_pow_left₀ (sqc_nonneg f y) (by linarith [(abs_le.mp h1).2]) 2
  set ε₃ := (δ / (2 * 2 ^ d)) ^ 2
  have hε₃ : 0 < ε₃ := by positivity
  filter_upwards [Ioo_mem_nhdsGT hε₃] with ε hε
  have hup := upper_count hf hM0 hM hε.1
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε.1
  have hsmall : Real.sqrt ε * 2 ^ d ≤ δ / 2 := by
    have : Real.sqrt ε < δ / (2 * 2 ^ d) := by
      rw [show δ / (2 * 2 ^ d) = Real.sqrt ε₃ by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_lt_sqrt hε.1.le hε.2
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hsum : ∑ i ∈ Finset.range (2 ^ d), Real.sqrt (Mv (m₀ * 2 ^ d + i)) / 2 ^ q /
      Real.sqrt (2 * ε) ≤ (curvI f k₀ m₀ + 2 * η / 2 ^ k₀) / Real.sqrt (2 * ε) := by
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have h1 : ∑ i ∈ Finset.range (2 ^ d), Real.sqrt (Mv (m₀ * 2 ^ d + i)) / 2 ^ q =
        ∑ i ∈ Finset.range (2 ^ d), sqc f (cL q (m₀ * 2 ^ d + i)) / 2 ^ q + η / 2 ^ k₀ := by
      simp only [Mv]
      rw [Finset.sum_congr rfl (fun i _ => by
        rw [Real.sqrt_sq (by have := sqc_nonneg f (cL q (m₀ * 2 ^ d + i)); positivity),
          add_div])]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      simp only [q, pow_add]; push_cast; field_simp
    have h3 := (abs_le.mp hR).1
    rw [h1]
    calc ∑ i ∈ Finset.range (2 ^ d), sqc f (cL q (m₀ * 2 ^ d + i)) / 2 ^ q + η / 2 ^ k₀
        ≤ (curvI f k₀ m₀ + η / 2 ^ k₀) + η / 2 ^ k₀ := by linarith
      _ = curvI f k₀ m₀ + 2 * η / 2 ^ k₀ := by ring
  have key : Real.sqrt ε * ((curvI f k₀ m₀ + 2 * η / 2 ^ k₀) / Real.sqrt (2 * ε)) =
      curvI f k₀ m₀ / Real.sqrt 2 + δ / 2 := by
    rw [Real.sqrt_mul (by norm_num)]
    simp only [η]
    field_simp
    ring
  calc Real.sqrt ε * nThr f ε k₀ m₀
      ≤ Real.sqrt ε * (2 ^ d + (curvI f k₀ m₀ + 2 * η / 2 ^ k₀) / Real.sqrt (2 * ε)) := by
        apply mul_le_mul_of_nonneg_left _ hs.le
        linarith
    _ = Real.sqrt ε * 2 ^ d + curvI f k₀ m₀ / Real.sqrt 2 + δ / 2 := by rw [mul_add, key]; ring
    _ ≤ curvI f k₀ m₀ / Real.sqrt 2 + δ := by linarith

/-- transfer of the tolerance envelope to the budget envelope via the inversion of Theorem 11.1 -/
lemma budget_of_threshold {n : ℝ → ℕ} {E : ℕ → ℝ} (hE0 : ∀ N, 0 ≤ E N)
    (hiff : ∀ ε > 0, ∀ N : ℕ, 1 ≤ N → (E N ≤ ε ↔ n ε ≤ N)) {a b : ℝ} (ha : 0 < a)
    (hlow : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), a - δ ≤ Real.sqrt ε * n ε)
    (hup : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sqrt ε * n ε ≤ b + δ) (hb : 0 ≤ b) :
    (∀ δ > 0, ∀ᶠ N : ℕ in atTop, a ^ 2 - δ ≤ (N : ℝ) ^ 2 * E N) ∧
    (∀ δ > 0, ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 2 * E N ≤ b ^ 2 + δ) := by
  constructor
  · intro δ hδ
    set δ' := min (a / 2) (δ / (2 * a))
    have hδ' : 0 < δ' := lt_min (by positivity) (by positivity)
    have hδ'a : δ' ≤ a / 2 := min_le_left _ _
    have hsq : a ^ 2 - δ ≤ (a - δ') ^ 2 := by
      have : 2 * a * δ' ≤ δ := by
        have := min_le_right (a / 2) (δ / (2 * a))
        calc 2 * a * δ' ≤ 2 * a * (δ / (2 * a)) := by gcongr
          _ = δ := by field_simp
      nlinarith [sq_nonneg δ']
    obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hlow δ' hδ')
    replace hε₁ : (0 : ℝ) < ε₁ := hε₁
    filter_upwards [eventually_ge_atTop (max 1 (n (ε₁ / 2)))] with N hN
    have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
    have hEN : E N ≤ ε₁ / 2 := (hiff (ε₁ / 2) (by positivity) N hN1).mpr
      (le_trans (le_max_right _ _) hN)
    have hpos : 0 < E N := by
      rcases (hE0 N).eq_or_lt with h0 | h0
      · exfalso
        set ε := min (ε₁ / 2) (((a - δ') / (2 * N)) ^ 2)
        have hε : 0 < ε := lt_min (by positivity) (by
          have : (0 : ℝ) < N := by exact_mod_cast hN1
          have : 0 < a - δ' := by linarith
          positivity)
        have hεlt : ε < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have h1 := hsub ⟨hε, hεlt⟩
        have hn : n ε ≤ N := (hiff ε hε N hN1).mp (by rw [← h0]; exact hε.le)
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
        have hs : Real.sqrt ε ≤ (a - δ') / (2 * N) := by
          rw [show (a - δ') / (2 * N) = Real.sqrt (((a - δ') / (2 * N)) ^ 2) by
            rw [Real.sqrt_sq (by have : 0 < a - δ' := by linarith
                                 positivity)]]
          exact Real.sqrt_le_sqrt (min_le_right _ _)
        have : Real.sqrt ε * n ε ≤ Real.sqrt ε * N :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (Real.sqrt_nonneg _)
        have : Real.sqrt ε * N ≤ (a - δ') / 2 := by
          calc Real.sqrt ε * N ≤ (a - δ') / (2 * N) * N := by gcongr
            _ = (a - δ') / 2 := by field_simp
        simp only [mem_setOf_eq] at h1
        linarith
      · exact h0
    have h1 := hsub ⟨hpos, by linarith⟩
    simp only [mem_setOf_eq] at h1
    have hn : n (E N) ≤ N := (hiff (E N) hpos N hN1).mp le_rfl
    have h2 : a - δ' ≤ Real.sqrt (E N) * N :=
      h1.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (Real.sqrt_nonneg _))
    have h3 : (a - δ') ^ 2 ≤ (Real.sqrt (E N) * N) ^ 2 :=
      pow_le_pow_left₀ (by linarith) h2 2
    rw [mul_pow, Real.sq_sqrt (hE0 N)] at h3
    linarith
  · intro δ hδ
    set δ' := min 1 (δ / (2 * b + 1))
    have hδ' : 0 < δ' := lt_min one_pos (by positivity)
    have hsq : (b + δ') ^ 2 ≤ b ^ 2 + δ := by
      have h1 : δ' ≤ 1 := min_le_left _ _
      have h2 : δ' * (2 * b + 1) ≤ δ := by
        calc δ' * (2 * b + 1) ≤ δ / (2 * b + 1) * (2 * b + 1) := by
              gcongr; exact min_le_right _ _
          _ = δ := by field_simp
      nlinarith
    obtain ⟨ε₂, hε₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hup δ' hδ')
    replace hε₂ : (0 : ℝ) < ε₂ := hε₂
    have hbd : 0 < b + δ' := by linarith
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b + δ') / Real.sqrt ε₂)
    filter_upwards [eventually_ge_atTop (max 1 N₀)] with N hN
    have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNN₀ : (N₀ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
    set ε := ((b + δ') / N) ^ 2
    have hε : 0 < ε := by positivity
    have hsε : Real.sqrt ε = (b + δ') / N := Real.sqrt_sq (by positivity)
    have hεlt : ε < ε₂ := by
      have h1 : (b + δ') / N < Real.sqrt ε₂ := by
        rw [div_lt_iff₀ hNr]
        rw [div_lt_iff₀ (Real.sqrt_pos.mpr hε₂)] at hN₀
        nlinarith [Real.sqrt_pos.mpr hε₂]
      calc ε = ((b + δ') / N) ^ 2 := rfl
        _ < Real.sqrt ε₂ ^ 2 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
        _ = ε₂ := Real.sq_sqrt hε₂.le
    have h1 := hsub ⟨hε, hεlt⟩
    simp only [mem_setOf_eq] at h1
    rw [hsε] at h1
    have hn : (n ε : ℝ) ≤ N := by
      have := (div_mul_eq_mul_div (b + δ') (N : ℝ) (n ε)) ▸ h1
      rw [div_le_iff₀ hNr] at this
      nlinarith
    have hEN : E N ≤ ε := (hiff ε hε N hN1).mpr (by exact_mod_cast hn)
    calc (N : ℝ) ^ 2 * E N ≤ (N : ℝ) ^ 2 * ε := by gcongr
      _ = (b + δ') ^ 2 := by simp only [ε]; field_simp
      _ ≤ b ^ 2 + δ := hsq

/-- **Theorem 11.3 (envelope diádico universal e agudo)**: if `f ∈ C²(K)` and `I(f) > 0`, then
`I/√8 ≤ liminf_{ε↓0} √ε n_f(ε) ≤ limsup_{ε↓0} √ε n_f(ε) ≤ I/√2` and
`I²/8 ≤ liminf_N N² E_N^{dia}(f)_∞ ≤ limsup_N N² E_N^{dia}(f)_∞ ≤ I²/2`,
stated in the equivalent form: for every `δ > 0` the bounds hold up to `δ` eventually
(as `ε → 0⁺`, resp. `N → ∞`). No assumption on the zeros or sign changes of `f''` is made. -/
theorem general_dyadic_envelope {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ}
    (hI : 0 < curvI f k₀ m₀) :
    (∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      curvI f k₀ m₀ / Real.sqrt 8 - δ ≤ Real.sqrt ε * nThr f ε k₀ m₀ ∧
      Real.sqrt ε * nThr f ε k₀ m₀ ≤ curvI f k₀ m₀ / Real.sqrt 2 + δ) ∧
    (∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      curvI f k₀ m₀ ^ 2 / 8 - δ ≤ (N : ℝ) ^ 2 * Edia f k₀ m₀ N ∧
      (N : ℝ) ^ 2 * Edia f k₀ m₀ N ≤ curvI f k₀ m₀ ^ 2 / 2 + δ) := by
  have hlow := fun δ (hδ : δ > 0) => envelope_lower hf k₀ m₀ hδ
  have hup := fun δ (hδ : δ > 0) => envelope_upper hf k₀ m₀ hδ
  have hiff : ∀ ε > 0, ∀ N : ℕ, 1 ≤ N → (Edia f k₀ m₀ N ≤ ε ↔ nThr f ε k₀ m₀ ≤ N) :=
    fun ε hε N hN => (threshold_optimality hf.continuous.continuousOn hε).2.2.2.2.2 N hN
  obtain ⟨hB1, hB2⟩ := budget_of_threshold (fun N => Edia_nonneg N) hiff
    (div_pos hI (by positivity)) hlow hup (div_nonneg hI.le (by positivity))
  have e8 : (curvI f k₀ m₀ / Real.sqrt 8) ^ 2 = curvI f k₀ m₀ ^ 2 / 8 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have e2 : (curvI f k₀ m₀ / Real.sqrt 2) ^ 2 = curvI f k₀ m₀ ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  refine ⟨fun δ hδ => (hlow δ hδ).and (hup δ hδ), fun δ hδ => ?_⟩
  filter_upwards [hB1 δ hδ, hB2 δ hδ] with N h1 h2
  rw [e8] at h1; rw [e2] at h2
  exact ⟨h1, h2⟩

/-- **Theorem 11.3 (degenerate case)**: if `I(f) = 0` then `f` is affine on `K` and both errors
vanish identically: `n_f(ε) = 1` for every `ε > 0` and `E_N^{dia}(f)_∞ = 0` for every `N ≥ 1`. -/
theorem general_dyadic_envelope_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ}
    (hI : curvI f k₀ m₀ = 0) :
    (∃ α β : ℝ, ∀ x ∈ cellIcc k₀ m₀, f x = α + β * x) ∧
    (∀ ε > 0, nThr f ε k₀ m₀ = 1) ∧ (∀ N : ℕ, 1 ≤ N → Edia f k₀ m₀ N = 0) := by
  have hab := cL_lt_cR k₀ m₀
  -- `f'' = 0` on `K`
  have hzero : ∀ y ∈ cellIcc k₀ m₀, deriv (deriv f) y = 0 := by
    intro y hy
    by_contra hne
    have hpos : 0 < curvI f k₀ m₀ := by
      apply intervalIntegral.integral_pos hab (sqc_continuous hf).continuousOn
        (fun x _ => sqc_nonneg f x)
      exact ⟨y, hy, Real.sqrt_pos.mpr (abs_pos.mpr hne)⟩
    linarith
  have hloc : ∀ (j : ℕ) (m' : ℤ), m' / 2 ^ j = m₀ → locErr f (k₀ + j) m' = 0 := by
    intro j m' hm'
    have hsub := desc_cell_sub_root k₀ j m₀ m' hm'
    have := locErr_near hf (k := k₀ + j) (m := m') (c := 0) (w := 0)
      (fun y hy => by rw [hzero y (hsub hy), sub_zero, abs_zero])
    simp only [abs_zero, zero_div, zero_mul, sub_zero, abs_nonpos_iff] at this
    exact this
  have hK : locErr f k₀ m₀ = 0 := by simpa using hloc 0 m₀ (by simp)
  refine ⟨?_, fun ε hε => ?_, fun N hN => ?_⟩
  · have hcont : ContinuousOn f (cellIcc k₀ m₀) := hf.continuous.continuousOn
    refine ⟨f (cL k₀ m₀) - (f (cR k₀ m₀) - f (cL k₀ m₀)) / (cR k₀ m₀ - cL k₀ m₀) * cL k₀ m₀,
      (f (cR k₀ m₀) - f (cL k₀ m₀)) / (cR k₀ m₀ - cL k₀ m₀), fun x hx => ?_⟩
    have := (locErr_le_iff hcont).mp hK.le x hx
    rw [abs_nonpos_iff, sub_eq_zero] at this
    rw [this, linInterp]; ring
  · have hT : IsThr f ε k₀ m₀ DShape.leaf := IsThr.leaf (by rw [hK]; exact hε.le)
    have := (thrTree_spec ⟨_, hT⟩).unique hT
    unfold nThr; rw [this]; rfl
  · apply le_antisymm _ (Edia_nonneg N)
    have := Edia_le_treeErr (f := f) (k := k₀) (m := m₀) (T := DShape.leaf)
      (by simpa [numLeaves] using hN)
    simpa [treeErr, hK] using this

lemma liminf_limsup_of_eventually {α : Type*} {l : Filter α} [l.NeBot] {u : α → ℝ} {a b : ℝ}
    (h : ∀ δ > 0, ∀ᶠ x in l, a - δ ≤ u x ∧ u x ≤ b + δ) : a ≤ liminf u l ∧ limsup u l ≤ b := by
  have hb1 : IsBoundedUnder (· ≤ ·) l u :=
    isBoundedUnder_of_eventually_le ((h 1 one_pos).mono fun _ h => h.2)
  have hb2 : IsBoundedUnder (· ≥ ·) l u :=
    isBoundedUnder_of_eventually_ge ((h 1 one_pos).mono fun _ h => h.1)
  constructor
  · refine le_of_forall_sub_le fun δ hδ => ?_
    exact le_liminf_of_le hb1.isCoboundedUnder_ge ((h δ hδ).mono fun _ h => h.1)
  · refine le_of_forall_pos_le_add fun δ hδ => ?_
    exact limsup_le_of_le hb2.isCoboundedUnder_le ((h δ hδ).mono fun _ h => h.2)

/-- **Theorem 11.3 (envelope diádico universal e agudo), `liminf`/`limsup` form**: if `f ∈ C²(K)`
and `I(f) > 0`, then
`I/√8 ≤ liminf_{ε↓0} √ε n_f(ε)`, `limsup_{ε↓0} √ε n_f(ε) ≤ I/√2`,
`I²/8 ≤ liminf_N N² E_N^{dia}(f)_∞` and `limsup_N N² E_N^{dia}(f)_∞ ≤ I²/2`. -/
theorem general_dyadic_envelope_liminf {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ}
    (hI : 0 < curvI f k₀ m₀) :
    curvI f k₀ m₀ / Real.sqrt 8 ≤
      liminf (fun ε => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] (0 : ℝ)) ∧
    limsup (fun ε => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] (0 : ℝ)) ≤
      curvI f k₀ m₀ / Real.sqrt 2 ∧
    curvI f k₀ m₀ ^ 2 / 8 ≤ liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop ≤ curvI f k₀ m₀ ^ 2 / 2 := by
  obtain ⟨h1, h2⟩ := general_dyadic_envelope hf hI
  obtain ⟨a1, a2⟩ := liminf_limsup_of_eventually h1
  obtain ⟨b1, b2⟩ := liminf_limsup_of_eventually h2
  exact ⟨a1, a2, b1, b2⟩

end Artigo
