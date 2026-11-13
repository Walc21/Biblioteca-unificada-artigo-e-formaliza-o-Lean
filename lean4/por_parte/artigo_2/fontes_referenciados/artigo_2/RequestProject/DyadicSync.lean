import RequestProject.DyadicPhase

/-!
# Corollary 12.3 (fases sincronizadas)
-/

namespace Artigo

open Set Filter Topology MeasureTheory DShape

lemma thrDepth_mul_four_pow {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) (hlt : ε < A) (ρ : ℕ) :
    thrDepth (A * 4 ^ ρ) ε = thrDepth A ε + ρ := by
  have hA' : 0 < A * 4 ^ ρ := by positivity
  apply le_antisymm
  · rw [← le_eps_iff_thrDepth_le hA' hε, pow_add, mul_comm ((4 : ℝ) ^ thrDepth A ε),
      ← div_div, mul_div_cancel_right₀ _ (by positivity)]
    exact (le_eps_iff_thrDepth_le hA hε _).mpr le_rfl
  · set D' := thrDepth (A * 4 ^ ρ) ε
    have h := (le_eps_iff_thrDepth_le hA' hε D').mpr le_rfl
    have hρ : ρ ≤ D' := by
      by_contra hcon
      push_neg at hcon
      have : A ≤ A * 4 ^ ρ / 4 ^ D' := by
        rw [le_div_iff₀ (by positivity)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcon.le) hA.le
      linarith
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hρ
    rw [he, pow_add, ← div_div, mul_div_cancel_right₀ _ (by positivity)] at h
    have := (le_eps_iff_thrDepth_le hA hε e).mp h
    omega

/-- equality from the same upper sets below a threshold -/
lemma eq_of_forall_small_le_iff {E c ε₁ : ℝ} (hE : 0 ≤ E) (hc : 0 < c) (hcε : c < ε₁)
    (h : ∀ ε, 0 < ε → ε < ε₁ → (E ≤ ε ↔ c ≤ ε)) : E = c := by
  apply le_antisymm ((h c hc hcε).mpr le_rfl)
  by_contra hlt
  push_neg at hlt
  have := (h ((E + c) / 2) (by linarith) (by linarith)).mp (by linarith)
  linarith

/-- the curvature functional on a piecewise quadratic: `I(f) = ∑ᵢ √|κᵢ| |Qᵢ|` -/
lemma pw_integral {f : ℝ → ℝ} {q₀ : ℕ} {κ : ℕ → ℝ}
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ),
      f x = κ i / 2 * x ^ 2 + b * x + c) :
    ∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x| =
      ∑ i ∈ Finset.range (2 ^ q₀), Real.sqrt |κ i| * (cR q₀ i - cL q₀ i) := by
  set g : ℝ → ℝ := fun x => Real.sqrt |deriv (deriv f) x|
  have hint : ∀ i : ℕ, i < 2 ^ q₀ → ∀ x ∈ Ioo (cL q₀ i) (cR q₀ i), g x = Real.sqrt |κ i| := by
    intro i hi x hx
    obtain ⟨b, c, h⟩ := hquad i hi
    set p : ℝ → ℝ := fun y => κ i / 2 * y ^ 2 + b * y + c
    have hev : f =ᶠ[𝓝 x] p := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact h y (Ioo_subset_Icc_self hy)
    have hp : deriv p = fun y => κ i * y + b := by
      funext y
      have : HasDerivAt p (κ i / 2 * (2 * y) + b) y := by
        have h1 := (((hasDerivAt_pow 2 y).const_mul (κ i / 2)).add
          ((hasDerivAt_id y).const_mul b)).add_const c
        convert h1 using 1
        simp
      rw [this.deriv]; ring
    have hpp : deriv (fun y => κ i * y + b) x = κ i := by
      have := ((hasDerivAt_id x).const_mul (κ i)).add_const b
      simpa using this.deriv
    simp only [g]
    rw [hev.deriv.deriv_eq, hp, hpp]
  have hpiece : ∀ i : ℕ, i < 2 ^ q₀ → ∫ x in cL q₀ i..cR q₀ i, g x =
      Real.sqrt |κ i| * (cR q₀ i - cL q₀ i) := by
    intro i hi
    have hle := (cL_lt_cR q₀ i).le
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (hint i hi), setIntegral_const, smul_eq_mul,
      Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hii : ∀ i : ℕ, i < 2 ^ q₀ → IntervalIntegrable g volume (cL q₀ i) (cR q₀ i) := by
    intro i hi
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (cL_lt_cR q₀ i).le,
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (integrableOn_const (by simp) (by simp)).congr_fun
      (fun x hx => (hint i hi x hx).symm) measurableSet_Ioo
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
    (a := fun i : ℕ => cL q₀ i) (n := 2 ^ q₀) (fun i hi => by
      have := hii i hi
      show IntervalIntegrable g volume (cL q₀ i) (cL q₀ ((i + 1 : ℕ) : ℤ))
      rwa [show cL q₀ ((i + 1 : ℕ) : ℤ) = cR q₀ i by unfold cL cR; push_cast; ring])
  have h0 : cL q₀ ((0 : ℕ) : ℤ) = 0 := by simp [cL]
  have h1 : cL q₀ ((2 ^ q₀ : ℕ) : ℤ) = 1 := by unfold cL; push_cast; field_simp
  simp only [h0, h1] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [show cL q₀ ((i + 1 : ℕ) : ℤ) = cR q₀ i by unfold cL cR; push_cast; ring]
  exact hpiece i (Finset.mem_range.mp hi)

/-- **Corollary 12.3 (fases sincronizadas)**: under the hypotheses of Theorem 12.2, if moreover
`Aᵢ/Aⱼ ∈ 4^ℤ` for all `i, j`, then
`liminf N² E_N^{dia}(f)_∞ = I(f)²/8` and `limsup N² E_N^{dia}(f)_∞ = I(f)²/2`,
where `I(f) = ∫₀¹ √|f''|`. -/
theorem synchronized_phases {f : ℝ → ℝ} {q₀ : ℕ} {κ : ℕ → ℝ}
    (hκ : ∀ i < 2 ^ q₀, κ i ≠ 0)
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ),
      f x = κ i / 2 * x ^ 2 + b * x + c)
    {A : ℕ → ℝ} (hA : ∀ i, A i = |κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8)
    (hsync : ∀ i < 2 ^ q₀, ∀ j < 2 ^ q₀, ∃ z : ℤ, A i / A j = (4 : ℝ) ^ z) :
    liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia f 0 0 N) atTop =
      (∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x|) ^ 2 / 8 ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia f 0 0 N) atTop =
      (∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x|) ^ 2 / 2 := by
  have hApos := pw_A_pos hκ hA
  have hcont := pw_continuousOn hquad
  -- the smallest `Aᵢ`
  obtain ⟨i₀, hi₀, hmin⟩ := (Finset.range (2 ^ q₀)).exists_min_image A
    ⟨0, Finset.mem_range.mpr (by positivity)⟩
  have hi₀' := Finset.mem_range.mp hi₀
  set As := A i₀
  have hAs : 0 < As := hApos i₀ hi₀'
  have hρex : ∀ i : ℕ, ∃ ρ : ℕ, i < 2 ^ q₀ → A i = As * 4 ^ ρ := by
    intro i
    by_cases hi : i < 2 ^ q₀
    · obtain ⟨z, hz⟩ := hsync i hi i₀ hi₀'
      have hz0 : 0 ≤ z := by
        rw [← one_le_zpow_iff_right₀ (show (1 : ℝ) < 4 by norm_num), ← hz,
          le_div_iff₀ hAs, one_mul]
        exact hmin i (Finset.mem_range.mpr hi)
      refine ⟨z.toNat, fun _ => ?_⟩
      rw [div_eq_iff hAs.ne'] at hz
      rw [hz, ← zpow_natCast, Int.toNat_of_nonneg hz0, mul_comm]
    · exact ⟨0, fun h => absurd h hi⟩
  choose ρ hρ using hρex
  set M : ℕ := ∑ i ∈ Finset.range (2 ^ q₀), 2 ^ ρ i
  have hM : 1 ≤ M := by
    have : 2 ^ ρ 0 ≤ M := Finset.single_le_sum (f := fun i => 2 ^ ρ i) (fun _ _ => by positivity)
      (Finset.mem_range.mpr (by positivity))
    have := Nat.one_le_two_pow (n := ρ 0)
    omega
  -- the counting law
  obtain ⟨ε₀, hε₀, hcount⟩ := pw_count hκ hquad hA
  set ε₁ := min ε₀ As
  have hε₁ : 0 < ε₁ := lt_min hε₀ hAs
  have hn : ∀ ε, 0 < ε → ε < ε₁ → nThr f ε 0 0 = M * 2 ^ thrDepth As ε := by
    intro ε hε hlt
    obtain ⟨-, h⟩ := hcount ε hε (lt_of_lt_of_le hlt (min_le_left _ _))
    have hlt' : ε < As := lt_of_lt_of_le hlt (min_le_right _ _)
    have : (nThr f ε 0 0 : ℝ) = ((M * 2 ^ thrDepth As ε : ℕ) : ℝ) := by
      rw [h]
      simp only [M]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hρ i (Finset.mem_range.mp hi), thrDepth_mul_four_pow hAs hε hlt', pow_add, mul_comm]
    exact_mod_cast this
  -- the exact law for large budgets
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, As / 4 ^ R₀ < ε₁ := by
    obtain ⟨R₀, hR₀⟩ := exists_pow_lt_of_lt_one (div_pos hε₁ hAs) (show (1 / 4 : ℝ) < 1 by norm_num)
    refine ⟨R₀, ?_⟩
    calc As / 4 ^ R₀ = As * (1 / 4) ^ R₀ := by rw [div_pow, one_pow]; ring
      _ < As * (ε₁ / As) := mul_lt_mul_of_pos_left hR₀ hAs
      _ = ε₁ := by field_simp
  have hlaw : ∀ N : ℕ, M * 2 ^ R₀ ≤ N → Edia f 0 0 N = As / 4 ^ Nat.log 2 (N / M) := by
    intro N hN
    have hNM : M ≤ N := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hN
    have hN1 : 1 ≤ N := le_trans hM hNM
    have hR : R₀ ≤ Nat.log 2 (N / M) := by
      rw [Nat.le_log_iff_pow_le (by norm_num) (Nat.div_pos hNM (by omega)).ne',
        Nat.le_div_iff_mul_le (by omega), mul_comm]
      exact hN
    have hc : As / 4 ^ Nat.log 2 (N / M) < ε₁ :=
      lt_of_le_of_lt (div_le_div_of_nonneg_left hAs.le (by positivity)
        (pow_le_pow_right₀ (by norm_num) hR)) hR₀
    apply eq_of_forall_small_le_iff (Edia_nonneg N) (by positivity) hc
    intro ε hε hlt
    rw [(threshold_optimality hcont hε).2.2.2.2.2 N hN1, hn ε hε hlt,
      le_eps_iff_thrDepth_le hAs hε, Nat.le_log_iff_pow_le (by norm_num)
        (Nat.div_pos hNM (by omega)).ne', Nat.le_div_iff_mul_le (by omega), mul_comm]
  obtain ⟨-, h2, h3⟩ := sawtooth (u := fun N : ℕ => (N : ℝ) ^ 2 * Edia f 0 0 N) hM hAs (by
    filter_upwards [eventually_ge_atTop (M * 2 ^ R₀)] with N hN
    rw [hlaw N hN]; ring)
  -- `I(f)² / 8 = M² A⋆`
  have hI : (∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x|) ^ 2 / 8 = (M : ℝ) ^ 2 * As := by
    rw [pw_integral hquad]
    have hterm : ∀ i ∈ Finset.range (2 ^ q₀), Real.sqrt |κ i| * (cR q₀ i - cL q₀ i) =
        Real.sqrt 8 * (Real.sqrt As * 2 ^ ρ i) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hlen : 0 < cR q₀ i - cL q₀ i := by linarith [cL_lt_cR q₀ (i : ℤ)]
      have e1 : Real.sqrt |κ i| * (cR q₀ i - cL q₀ i) = Real.sqrt (8 * A i) := by
        rw [hA i, show 8 * (|κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8) =
          |κ i| * (cR q₀ i - cL q₀ i) ^ 2 by ring, Real.sqrt_mul (abs_nonneg _),
          Real.sqrt_sq hlen.le]
      rw [e1, Real.sqrt_mul (by norm_num), hρ i hi', Real.sqrt_mul hAs.le,
        show (4 : ℝ) ^ ρ i = (2 ^ ρ i) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        Real.sqrt_sq (by positivity)]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.mul_sum, mul_pow, mul_pow,
      Real.sq_sqrt (by norm_num), Real.sq_sqrt hAs.le]
    simp only [M]
    push_cast
    ring
  refine ⟨by rw [h2, hI], ?_⟩
  rw [h3, show (∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x|) ^ 2 / 2 =
    4 * ((∫ x in (0 : ℝ)..1, Real.sqrt |deriv (deriv f) x|) ^ 2 / 8) by ring, hI]
  ring

end Artigo
