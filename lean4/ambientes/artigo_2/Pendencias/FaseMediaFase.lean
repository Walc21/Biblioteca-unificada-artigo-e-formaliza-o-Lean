import Pendencias.FaseCoro

/-!
# III.12.8(c) — média universal de fase

Para toda `f ∈ C²`:  `∫_T^{T+1} 2^{-t} n_f(4^{-t}) dt → I(f)/(√8 ln 2)` quando `T → ∞`.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

/-- `ε(u) = 4^{-u}` -/
noncomputable def eU (u : ℝ) : ℝ := (4 : ℝ) ^ (-u)

lemma eU_pos (u : ℝ) : 0 < eU u := Real.rpow_pos_of_pos (by norm_num) _

lemma eU_continuous : Continuous eU :=
  (Real.continuous_const_rpow (by norm_num : (4 : ℝ) ≠ 0)).comp continuous_neg

lemma eU_tendsto {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (s : ℝ) :
    Tendsto (fun n => eU (T n + s)) atTop (𝓝 0) :=
  (tendsto_rpow_atBot_of_base_gt_one 4 (by norm_num)).comp
    (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right _ s hT))

lemma sqrt_eU (u : ℝ) : Real.sqrt (eU u) = (2 : ℝ) ^ (-u) := by
  have h : eU u = ((2 : ℝ) ^ (-u)) ^ 2 := by
    unfold eU
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; push_cast; ring
  rw [h, Real.sqrt_sq (Real.rpow_nonneg (by norm_num) _)]

/-- `√ε n_f(ε)` na fase `u` (`ε = 4^{-u}`) -/
noncomputable def Xph (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (u : ℝ) : ℝ :=
  Real.sqrt (eU u) * nThr f (eU u) k₀ m₀

lemma Xph_nonneg (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (u : ℝ) : 0 ≤ Xph f k₀ m₀ u :=
  mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)

section avg

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
lemma nThr_anti {ε₁ ε₂ : ℝ} (h1 : 0 < ε₁) (h : ε₁ ≤ ε₂) :
    nThr f ε₂ k₀ m₀ ≤ nThr f ε₁ k₀ m₀ := by
  have h2 : 0 < ε₂ := h1.trans_le h
  have hfeas : (thrTree f ε₁ k₀ m₀).treeErr f k₀ m₀ ≤ ε₂ :=
    ((threshold_optimality (k := k₀) (m := m₀) hf.continuous.continuousOn h1).2.1).trans h
  exact (threshold_optimality (k := k₀) (m := m₀) hf.continuous.continuousOn h2).2.2.2.2.1 _ hfeas

include hf in
lemma measurable_Xph : Measurable (Xph f k₀ m₀) := by
  unfold Xph
  refine Measurable.mul (Real.continuous_sqrt.comp eU_continuous).measurable ?_
  have hmono : Monotone (fun u : ℝ => nThr f (eU u) k₀ m₀) := fun u v huv =>
    nThr_anti hf k₀ m₀ (eU_pos v)
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  exact (measurable_from_top (f := fun n : ℕ => (n : ℝ))).comp hmono.measurable

include hf in
lemma Xph_bound : ∃ U₀ B : ℝ, ∀ u ≥ U₀, Xph f k₀ m₀ u ≤ B := by
  obtain ⟨t₁, h1⟩ := exists_max_psiP hf k₀ m₀
  have h := phase_limsup_le hf k₀ m₀ h1 1 one_pos
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp h
  refine ⟨-Real.logb 4 u + 1, PsiP f k₀ m₀ t₁ + 1, fun x hx => ?_⟩
  have hE : eU x < u := by
    have : (4 : ℝ) ^ (-x) < (4 : ℝ) ^ (Real.logb 4 u) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (show (0:ℝ) < u from hu)] at this
  exact (hsub ⟨eU_pos x, hE⟩).le

include hf in
/-- **III.12.8(c)**: média universal de fase -/
theorem phase_average :
    Tendsto (fun T : ℝ => ∫ t in T..T + 1, (2 : ℝ) ^ (-t) * nThr f ((4 : ℝ) ^ (-t)) k₀ m₀)
      atTop (𝓝 (curvI f k₀ m₀ / (Real.sqrt 8 * Real.log 2))) := by
  have hXeq : ∀ t : ℝ, (2 : ℝ) ^ (-t) * nThr f ((4 : ℝ) ^ (-t)) k₀ m₀ = Xph f k₀ m₀ t := by
    intro t; simp only [Xph, sqrt_eU]; rfl
  have hfun : (fun T : ℝ => ∫ t in T..T + 1, (2 : ℝ) ^ (-t) * nThr f ((4 : ℝ) ^ (-t)) k₀ m₀) =
      fun T => ∫ t in T..T + 1, Xph f k₀ m₀ t := by
    funext T; congr 1; funext t; exact hXeq t
  rw [hfun]
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨θ, -, φ, hφ, hθ⟩ := isCompact_Icc.tendsto_subseq
    (x := fun j => Int.fract (ns j)) (s := Icc (0 : ℝ) 1)
    (fun j => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
  refine ⟨φ, ?_⟩
  set T : ℕ → ℝ := fun n => ns (φ n) with hTdef
  have hT : Tendsto T atTop atTop := hns.comp hφ.tendsto_atTop
  have hθ' : Tendsto (fun n => Int.fract (T n)) atTop (𝓝 θ) := hθ
  have hshift : ∀ n, ∫ t in T n..T n + 1, Xph f k₀ m₀ t =
      ∫ s in (0 : ℝ)..1, Xph f k₀ m₀ (T n + s) := fun n => by
    rw [intervalIntegral.integral_comp_add_left (fun t => Xph f k₀ m₀ t) (T n)]; simp
  have hlim_int : ∫ s in (0 : ℝ)..1, PsiF f k₀ m₀ (θ + s) =
      curvI f k₀ m₀ / (Real.sqrt 8 * Real.log 2) := by
    rw [intervalIntegral.integral_comp_add_left (fun t => PsiF f k₀ m₀ t) θ]
    have hper : Function.Periodic (PsiF f k₀ m₀) 1 := fun t => psiF_periodic k₀ m₀ t
    simp only [add_zero]
    rw [hper.intervalIntegral_add_eq θ 0, zero_add]
    exact integral_psiF hf k₀ m₀
  rw [← hlim_int]
  show Tendsto (fun n => ∫ t in T n..T n + 1, Xph f k₀ m₀ t) atTop _
  refine Tendsto.congr (fun n => (hshift n).symm) ?_
  obtain ⟨U₀, B, hB⟩ := Xph_bound hf k₀ m₀
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => B)
    (Eventually.of_forall fun n =>
      ((measurable_Xph hf k₀ m₀).comp (measurable_const.add measurable_id)).aestronglyMeasurable)
    ?_ intervalIntegrable_const ?_
  · filter_upwards [hT.eventually_ge_atTop U₀] with n hn
    refine Eventually.of_forall fun s hs => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Xph_nonneg _ _ _ _)]
    exact hB _ (by linarith [hs.1])
  · have hc : {s : ℝ | IsAtomPhase f k₀ m₀ (θ + s)}.Countable :=
      (countable_atomPhase hf k₀ m₀).preimage (add_right_injective θ)
    have hnull : ∀ᵐ s : ℝ, ¬ IsAtomPhase f k₀ m₀ (θ + s) := by
      rw [ae_iff]; simpa using hc.measure_zero volume
    filter_upwards [hnull] with s hs hsI
    rw [Set.uIoc_of_le zero_le_one] at hsI
    have hs0 : 0 ≤ s := hsI.1.le
    have hεt := eU_tendsto hT s
    have hz : Tendsto (fun n => -Real.logb 4 (eU (T n + s)) - ((⌊T n⌋ : ℤ) : ℝ)) atTop
        (𝓝 (θ + s)) := by
      refine (hθ'.add_const s).congr fun n => ?_
      unfold eU
      rw [logb_four_rpow_neg, ← Int.self_sub_floor]
      ring
    exact phase_law_nonatom hf k₀ m₀ (fun n => eU_pos _) hεt hs hz

end avg

end Pendencias
