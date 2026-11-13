module
public import Unified.Fase3.Refinement

/-!
# Proposition 6.5: exact calibration for constant curvature
-/

@[expose] public section

namespace Fase3

open Set Filter Topology

/-- `r(ε) = max{0, ⌈log₄(A/ε)⌉}` (equation (44)). -/
noncomputable def rcal (A ε : ℝ) : ℕ := (max 0 ⌈Real.logb 4 (A / ε)⌉).toNat

lemma rcal_eq {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) {n : ℕ} (h1 : A / ε ≤ 4 ^ n)
    (h2 : ∀ e : ℕ, e < n → (4 : ℝ) ^ e < A / ε) : rcal A ε = n := by
  have hpos : 0 < A / ε := div_pos hA hε
  have hx : Real.logb 4 (A / ε) ≤ n := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) hpos, Real.rpow_natCast]; exact h1
  unfold rcal
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : ⌈Real.logb 4 (A / ε)⌉ ≤ 0 := Int.ceil_le.2 (by simpa using hx)
    simp [max_eq_left this]
  · have hlo : ((n - 1 : ℕ) : ℝ) < Real.logb 4 (A / ε) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) hpos, Real.rpow_natCast]; exact h2 _ (by omega)
    have hc : ⌈Real.logb 4 (A / ε)⌉ = n := by
      rw [Int.ceil_eq_iff]
      push_cast [Nat.cast_sub hn] at hlo
      exact ⟨hlo, hx⟩
    rw [hc, max_eq_right (by positivity)]
    simp

lemma rcal_spec {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    A / ε ≤ 4 ^ rcal A ε ∧ ∀ e : ℕ, e < rcal A ε → (4 : ℝ) ^ e < A / ε := by
  have hpos : 0 < A / ε := div_pos hA hε
  constructor
  · have h1 : Real.logb 4 (A / ε) ≤ (rcal A ε : ℝ) := by
      unfold rcal
      have := Int.le_ceil (Real.logb 4 (A / ε))
      have h2 : (⌈Real.logb 4 (A / ε)⌉ : ℝ) ≤ ((max 0 ⌈Real.logb 4 (A / ε)⌉).toNat : ℤ) := by
        exact_mod_cast le_trans (le_max_right _ _) (Int.self_le_toNat _)
      push_cast at h2 ⊢
      linarith
    rwa [Real.logb_le_iff_le_rpow (by norm_num) hpos, Real.rpow_natCast] at h1
  · intro e he
    have hr : 0 < rcal A ε := lt_of_le_of_lt (Nat.zero_le e) he
    have hc : (rcal A ε : ℤ) = ⌈Real.logb 4 (A / ε)⌉ := by
      unfold rcal at hr ⊢
      have : 0 < max 0 ⌈Real.logb 4 (A / ε)⌉ := by omega
      rw [Int.toNat_of_nonneg this.le, max_eq_right]
      rcases le_total 0 ⌈Real.logb 4 (A / ε)⌉ with h | h
      · exact h
      · rw [max_eq_left h] at this; omega
    have : (e : ℤ) < ⌈Real.logb 4 (A / ε)⌉ := by rw [← hc]; exact_mod_cast he
    have : (e : ℝ) < Real.logb 4 (A / ε) := Int.lt_ceil.1 this
    rwa [Real.lt_logb_iff_rpow_lt (by norm_num) hpos, Real.rpow_natCast] at this

section
variable {M : ℕ × ℤ → ℝ} {J0 : ℕ × ℤ} {κ : ℝ}

lemma cert_calib (hM : ∀ J, cC J ⊆ cC J0 → M J = |κ|) {D : ℕ × ℤ} (hsub : cC D ⊆ cC J0)
    {d : ℕ} (hd : D.1 = J0.1 + d) : cert M D = mesh J0.1 ^ 2 * |κ| / 8 / 4 ^ d := by
  unfold cert
  rw [hM D hsub, hd, mesh_add, mul_pow, ← pow_mul, one_div_pow, mul_comm d 2, pow_mul]
  norm_num
  ring

lemma length_calib (hM : ∀ J, cC J ⊆ cC J0 → M J = |κ|) {ε : ℝ} {r : ℕ}
    (hgt : ∀ e : ℕ, e < r → ε < mesh J0.1 ^ 2 * |κ| / 8 / 4 ^ e) :
    ∀ d, ∀ J : ℕ × ℤ, cC J ⊆ cC J0 → J.1 = J0.1 + (r - d) → d ≤ r →
      (refineCell M ε d J).length = 2 ^ d := by
  intro d
  induction d with
  | zero => intro J _ _ _; simp [refineCell]
  | succ d ih =>
    intro J hsub hJ hd
    have hc : ¬ cert M J ≤ ε := by
      rw [cert_calib hM hsub hJ]
      exact not_le.2 (hgt _ (by omega))
    simp only [refineCell, hc, if_false, List.length_append]
    rw [ih (child0 J) ((cC_child0 J).trans hsub) (by simp only [child0]; omega) (by omega),
      ih (child1 J) ((cC_child1 J).trans hsub) (by simp only [child1]; omega) (by omega)]
    ring

/-- **Proposition 6.5 (exact calibration for constant curvature).** Let `[α,β] = J₀` be a
single initial dyadic cell, `F'' ≡ κ ≠ 0` on `J₀` and `M(J) = |κ|` on every descendant, and
`A = |J₀|² |κ| / 8`.  Then for every tolerance the algorithm terminates after
`r(ε) = max{0, ⌈log₄(A/ε)⌉}` levels with exactly `N(ε) = 2^{r(ε)}` leaves (44), and
(45) holds:
`liminf_{ε↓0} √ε N(ε) = (1/√8) ∫_α^β |f''|^{1/2}`,
`limsup_{ε↓0} √ε N(ε) = (1/√2) ∫_α^β |f''|^{1/2}`. -/
theorem calibration (f : ℝ → ℝ) (hκ : κ ≠ 0) (hM : ∀ J, cC J ⊆ cC J0 → M J = |κ|)
    (hf2 : ∀ x ∈ Icc (cL J0) (cR J0), d2 f (cL J0) (cR J0) x = κ) :
    (∀ ε > 0,
      (∀ s, refineAll M ε [J0] (rcal (mesh J0.1 ^ 2 * |κ| / 8) ε + s) =
        refineAll M ε [J0] (rcal (mesh J0.1 ^ 2 * |κ| / 8) ε)) ∧
      (refineAll M ε [J0] (rcal (mesh J0.1 ^ 2 * |κ| / 8) ε)).length =
        2 ^ rcal (mesh J0.1 ^ 2 * |κ| / 8) ε) ∧
    liminf (fun ε => Real.sqrt ε *
        (refineAll M ε [J0] (rcal (mesh J0.1 ^ 2 * |κ| / 8) ε)).length) (𝓝[>] 0) =
      1 / Real.sqrt 8 * ∫ x in cL J0..cR J0, Real.sqrt |d2 f (cL J0) (cR J0) x| ∧
    limsup (fun ε => Real.sqrt ε *
        (refineAll M ε [J0] (rcal (mesh J0.1 ^ 2 * |κ| / 8) ε)).length) (𝓝[>] 0) =
      1 / Real.sqrt 2 * ∫ x in cL J0..cR J0, Real.sqrt |d2 f (cL J0) (cR J0) x| := by
  set A := mesh J0.1 ^ 2 * |κ| / 8 with hAdef
  have hm := mesh_pos J0.1
  have hA : 0 < A := by have := abs_pos.2 hκ; positivity
  -- termination and the leaf count
  have hcount : ∀ ε > 0,
      (∀ s, refineAll M ε [J0] (rcal A ε + s) = refineAll M ε [J0] (rcal A ε)) ∧
      (refineAll M ε [J0] (rcal A ε)).length = 2 ^ rcal A ε := by
    intro ε hε
    obtain ⟨h1, h2⟩ := rcal_spec hA hε
    refine ⟨fun s => ?_, ?_⟩
    · simp only [refineAll, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      apply refineCell_stable
      intro D hD hsub
      rw [cert_calib hM hsub hD, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at h1; linarith
    · simp only [refineAll, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      apply length_calib hM (r := rcal A ε) _ _ J0 subset_rfl (by simp) le_rfl
      intro e he
      have := h2 e he
      rw [lt_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ hε] at this; linarith
  refine ⟨hcount, ?_⟩
  -- the integral
  have hint : ∫ x in cL J0..cR J0, Real.sqrt |d2 f (cL J0) (cR J0) x| = mesh J0.1 * Real.sqrt |κ| := by
    have hle : cL J0 ≤ cR J0 := (cellL_lt_cellR J0.1 J0.2).le
    rw [intervalIntegral.integral_congr (g := fun _ => Real.sqrt |κ|)]
    · rw [intervalIntegral.integral_const, smul_eq_mul, cell_width]
    · intro x hx
      rw [uIcc_of_le hle] at hx
      simp only [hf2 x hx]
  rw [hint]
  have hsA : Real.sqrt A = mesh J0.1 * Real.sqrt |κ| / Real.sqrt 8 := by
    rw [hAdef, Real.sqrt_div' _ (by norm_num), Real.sqrt_mul (by positivity),
      Real.sqrt_sq hm.le]
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have e1 : 1 / Real.sqrt 8 * (mesh J0.1 * Real.sqrt |κ|) = Real.sqrt A := by
    rw [hsA]; ring
  have e2 : 1 / Real.sqrt 2 * (mesh J0.1 * Real.sqrt |κ|) = 2 * Real.sqrt A := by
    rw [hsA, h8]; field_simp
  rw [e1, e2]
  -- the function and its eventual bounds
  set g : ℝ → ℝ := fun ε => Real.sqrt ε * (refineAll M ε [J0] (rcal A ε)).length
  have hg : ∀ ε > 0, g ε = Real.sqrt ε * 2 ^ rcal A ε := by
    intro ε hε; simp only [g, (hcount ε hε).2]; push_cast; ring
  have hsq4 : ∀ n : ℕ, Real.sqrt (4 ^ n) = 2 ^ n := by
    intro n; rw [show (4 : ℝ) ^ n = (2 ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      Real.sqrt_sq (by positivity)]
  have hbounds : ∀ ε, 0 < ε → ε < A → Real.sqrt A ≤ g ε ∧ g ε < 2 * Real.sqrt A := by
    intro ε hε hεA
    obtain ⟨h1, h2⟩ := rcal_spec hA hε
    set r := rcal A ε
    have hr : 0 < r := by
      by_contra h0
      push_neg at h0
      have : r = 0 := by omega
      rw [this, pow_zero, div_le_one hε] at h1
      linarith
    have h3 := h2 (r - 1) (by omega)
    rw [div_le_iff₀ hε] at h1
    rw [lt_div_iff₀ hε] at h3
    have h4 : (4 : ℝ) ^ r = 4 * 4 ^ (r - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hlo : A ≤ ε * 4 ^ r := by linarith
    have hhi : ε * 4 ^ r < 4 * A := by rw [h4]; nlinarith
    rw [hg ε hε, ← hsq4, ← Real.sqrt_mul hε.le]
    constructor
    · exact Real.sqrt_le_sqrt hlo
    · rw [show 2 * Real.sqrt A = Real.sqrt (4 * A) by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by positivity) hhi
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sqrt A ≤ g ε ∧ g ε < 2 * Real.sqrt A := by
    filter_upwards [Ioo_mem_nhdsGT hA] with ε hε using hbounds ε hε.1 hε.2
  have hbdd_ge : IsBoundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ)) g :=
    isBoundedUnder_of_eventually_ge (hev.mono fun _ h => h.1)
  have hbdd_le : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) g :=
    isBoundedUnder_of_eventually_le (hev.mono fun _ h => h.2.le)
  -- sequences tending to `0⁺`
  have hseq : ∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => c / 4 ^ n) atTop (𝓝[>] 0) := by
    intro c hc
    apply tendsto_nhdsWithin_iff.2
    refine ⟨?_, Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).const_mul c
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div_pow, mul_one_div]
  have hsA0 : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  constructor
  · apply le_antisymm
    · apply liminf_le_of_frequently_le _ hbdd_ge
      apply (hseq A hA).frequently
      refine Frequently.of_forall fun n => ?_
      have h4n : (0 : ℝ) < 4 ^ n := by positivity
      have hε : 0 < A / 4 ^ n := by positivity
      have hAε : A / (A / 4 ^ n) = 4 ^ n := by field_simp
      have hr : rcal A (A / 4 ^ n) = n := by
        apply rcal_eq hA hε
        · rw [hAε]
        · intro e he
          rw [hAε]
          exact pow_lt_pow_right₀ (by norm_num) he
      rw [hg _ hε, hr, Real.sqrt_div' _ h4n.le, hsq4]
      have : (0 : ℝ) < 2 ^ n := by positivity
      field_simp; rfl
    · exact le_liminf_of_le hbdd_le.isCoboundedUnder_flip (hev.mono fun _ h => h.1)
  · apply le_antisymm
    · exact limsup_le_of_le hbdd_ge.isCoboundedUnder_flip (hev.mono fun _ h => h.2.le)
    · apply le_of_forall_pos_le_add
      intro η hη
      set θ := min (1 / 4) (η / (4 * Real.sqrt A))
      have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
      have hθ1 : θ ≤ 1 / 4 := min_le_left _ _
      have hθη : 2 * Real.sqrt A * θ < η := by
        have : θ ≤ η / (4 * Real.sqrt A) := min_le_right _ _
        have h2 : 2 * Real.sqrt A * θ ≤ 2 * Real.sqrt A * (η / (4 * Real.sqrt A)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        have h3 : 2 * Real.sqrt A * (η / (4 * Real.sqrt A)) = η / 2 := by field_simp; ring
        linarith
      have h1θ : 0 < 1 - θ := by linarith
      have hc : 0 < A * (1 - θ) ^ 2 := by positivity
      have hfreq : ∃ᶠ ε in 𝓝[>] (0 : ℝ), 2 * Real.sqrt A - η ≤ g ε := by
        apply (hseq _ hc).frequently
        refine Frequently.of_forall fun m => ?_
        have h4m : (0 : ℝ) < 4 ^ m := by positivity
        have hε : 0 < A * (1 - θ) ^ 2 / 4 ^ m := by positivity
        have hAε : A / (A * (1 - θ) ^ 2 / 4 ^ m) = 4 ^ m / (1 - θ) ^ 2 := by field_simp
        have hsq : 0 < (1 - θ) ^ 2 := by positivity
        have hr : rcal A (A * (1 - θ) ^ 2 / 4 ^ m) = m + 1 := by
          apply rcal_eq hA hε
          · rw [hAε, div_le_iff₀ hsq, pow_succ]
            have h1 : 1 ≤ 4 * (1 - θ) ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left h1 h4m.le]
          · intro e he
            rw [hAε, lt_div_iff₀ hsq]
            have h4 : (4 : ℝ) ^ e ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
            have h5 : (1 - θ) ^ 2 < 1 := by nlinarith
            have h6 : (0 : ℝ) < 4 ^ e := by positivity
            nlinarith
        rw [hg _ hε, hr, Real.sqrt_div' _ h4m.le, Real.sqrt_mul hA.le, Real.sqrt_sq h1θ.le, hsq4,
          pow_succ]
        have h2m : (0 : ℝ) < 2 ^ m := by positivity
        have : Real.sqrt A * (1 - θ) / 2 ^ m * (2 ^ m * 2) = 2 * Real.sqrt A - 2 * Real.sqrt A * θ := by
          field_simp
        rw [this]; linarith
      have := le_limsup_of_frequently_le hfreq hbdd_le
      linarith

end

end Fase3
