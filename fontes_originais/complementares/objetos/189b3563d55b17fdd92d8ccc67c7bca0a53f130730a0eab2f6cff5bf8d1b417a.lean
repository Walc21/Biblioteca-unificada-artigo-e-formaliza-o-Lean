module
public import RequestProject.Sec7.EntropyUpper
@[expose] public section

/-!
# Theorem 7.18 (entropy and explicit codebook)

Choice of the parameters `N = 2^k` (least power of two with `M/(8N²) ≤ ε/2`, up to the floor `1`)
and `δ = 2^{-⌈log₂(1/ε)⌉}`, cardinality estimate `log₂ |𝒞_ε| = O(ε^{-1/2})`, and the final
statement combining the upper bound with the lower bound of `EntropyLower`.
-/

open Set Finset

namespace Dyadic.Lib

attribute [local instance] Classical.propDecidable

/-- For `y ≥ 1` and `k = ⌈log₂ y⌉`, `y ≤ 2^k < 2y`. -/
lemma pow_ceil_logb_spec {y : ℝ} (hy : 1 ≤ y) :
    y ≤ (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ ∧ (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ < 2 * y := by
  have hy0 : 0 < y := by linarith
  have hl : 0 ≤ Real.logb 2 y := Real.logb_nonneg (by norm_num) hy
  have h1 := Nat.le_ceil (Real.logb 2 y)
  have h2 := Nat.ceil_lt_add_one hl
  constructor
  · calc y = (2 : ℝ) ^ Real.logb 2 y := (Real.rpow_logb (by norm_num) (by norm_num) hy0).symm
      _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 y⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = _ := Real.rpow_natCast _ _
  · calc (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ = (2 : ℝ) ^ (⌈Real.logb 2 y⌉₊ : ℝ) := (Real.rpow_natCast _ _).symm
      _ < (2 : ℝ) ^ (Real.logb 2 y + 1) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
      _ = 2 * y := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hy0, Real.rpow_one]
        ring

/-- `log₂ x ≤ 3 √x` for `x > 0`. -/
lemma logb_two_le_three_sqrt {x : ℝ} (hx : 0 < x) : Real.logb 2 x ≤ 3 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have e : Real.log x = 2 * Real.log (Real.sqrt x) := by
      have := Real.log_pow (Real.sqrt x) 2
      rw [Real.sq_sqrt hx.le] at this
      rw [this]; norm_num
    have := Real.log_le_sub_one_of_pos hs
    linarith
  have h2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  unfold Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The constant `C` of the upper bound in (86)–(87). -/
noncomputable def CEnt (R M : ℝ) : ℝ :=
  3 * Real.sqrt (8 * R + 5) + 3 * Real.sqrt (8 * C0 R M + 7) + 12 * (1 + Real.sqrt (M / 4))

lemma CEnt_pos {R : ℝ} (M : ℝ) (hR : 0 ≤ R) : 0 < CEnt R M := by
  unfold CEnt; positivity

/-- The codebook `𝒞_ε` for `0 < ε ≤ 1`: a finite set of assemblies on `[0,1]` with distortion at
most `ε` on `𝓕_{R,M}` and `log₂ |𝒞_ε| ≤ C ε^{-1/2}`. -/
theorem codebook_eps {R M ε : ℝ} (hR : 0 < R) (hM : 0 < M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ CB : Finset (ℝ → ℝ), (CB : Set (ℝ → ℝ)) ⊆ Asm (Icc 0 1) ∧
      (∀ f ∈ FRM R M, ∃ g ∈ CB, ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ ε) ∧
      Real.logb 2 CB.card ≤ CEnt R M / Real.sqrt ε := by
  set q := ⌈Real.logb 2 (1 / ε)⌉₊
  set y := max 1 (Real.sqrt (M / (4 * ε)))
  set k := ⌈Real.logb 2 y⌉₊
  obtain ⟨hq1, hq2⟩ := pow_ceil_logb_spec (y := 1 / ε) (by rw [le_div_iff₀ hε]; linarith)
  obtain ⟨hk1, hk2⟩ := pow_ceil_logb_spec (y := y) (le_max_left _ _)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hy : Real.sqrt (M / (4 * ε)) ≤ y := le_max_right _ _
  have hy2 : M / (4 * ε) ≤ ((2 : ℝ) ^ k) ^ 2 := by
    have := Real.sq_sqrt (show 0 ≤ M / (4 * ε) by positivity)
    nlinarith [Real.sqrt_nonneg (M / (4 * ε))]
  have hMN : M / ((2 : ℝ) ^ k) ^ 2 ≤ 4 * ε := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hy2
    nlinarith
  have hpq : (2 : ℝ) ^ (q + 1) = 2 * 2 ^ q := by rw [pow_succ]; ring
  have herr : M / (8 * ((2 : ℝ) ^ k) ^ 2) + 1 / 2 ^ (q + 1) ≤ ε := by
    have e1 : M / (8 * ((2 : ℝ) ^ k) ^ 2) = M / ((2 : ℝ) ^ k) ^ 2 / 8 := by ring
    have e2 : 1 / (2 : ℝ) ^ (q + 1) ≤ ε / 2 := by
      rw [hpq, div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at hq1
      nlinarith
    rw [e1]; linarith
  have hcurv : 2 ^ (q + 1) * M / ((2 : ℝ) ^ k) ^ 2 ≤ 16 := by
    rw [mul_div_assoc, hpq]
    have : (2 : ℝ) ^ q * ε < 2 := by
      have := hq2; rw [show 2 * (1 / ε) = 2 / ε by ring, lt_div_iff₀ hε] at this; exact this
    have hMN0 : 0 ≤ M / ((2 : ℝ) ^ k) ^ 2 := by positivity
    calc 2 * 2 ^ q * (M / ((2 : ℝ) ^ k) ^ 2) ≤ 2 * 2 ^ q * (4 * ε) :=
          mul_le_mul_of_nonneg_left hMN (by positivity)
      _ = 8 * (2 ^ q * ε) := by ring
      _ ≤ 16 := by linarith
  refine ⟨codebook R M q k, codebook_subset_Asm R M q k,
    codebook_distortion hM.le herr hcurv, ?_⟩
  -- cardinality
  have hcard := card_codebook_le R M q k
  rcases Nat.eq_zero_or_pos (codebook R M q k).card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.logb_zero]
    exact div_nonneg (CEnt_pos M hR.le).le (Real.sqrt_nonneg _)
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have hC0 : 0 ≤ C0 R M := by unfold C0; positivity
  -- the three factors
  set A := 2 * B0c R q + 1
  set B := 2 * B1c R M q k + 1
  have hA : (A : ℝ) ≤ (8 * R + 5) / ε := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ (q + 1) * R by positivity)
    simp only [A, B0c]; push_cast
    rw [le_div_iff₀ hε]
    have : (2 : ℝ) ^ q * ε < 2 := by
      have := hq2; rw [show 2 * (1 / ε) = 2 / ε by ring, lt_div_iff₀ hε] at this; exact this
    rw [hpq] at h ⊢
    nlinarith [mul_lt_mul_of_pos_right h hε, mul_lt_mul_of_pos_left this (by positivity : (0 : ℝ) < 4 * R)]
  have hB : (B : ℝ) ≤ (8 * C0 R M + 7) / ε := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2 ^ (q + 1) * C0 R M / 2 ^ k by positivity)
    simp only [B, B1c]; push_cast
    rw [le_div_iff₀ hε]
    have hqe : (2 : ℝ) ^ q * ε < 2 := by
      have := hq2; rw [show 2 * (1 / ε) = 2 / ε by ring, lt_div_iff₀ hε] at this; exact this
    have hk1' : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have : 2 ^ (q + 1) * C0 R M / 2 ^ k ≤ 2 ^ (q + 1) * C0 R M :=
      div_le_self (by positivity) hk1'
    rw [hpq] at h this ⊢
    nlinarith [mul_lt_mul_of_pos_right h hε, mul_le_mul_of_nonneg_left this hC0,
      mul_le_mul_of_nonneg_left hqe.le (by positivity : (0 : ℝ) ≤ 4 * C0 R M)]
  have hN : ((2 : ℝ) ^ k) ≤ 2 * (1 + Real.sqrt (M / 4)) / Real.sqrt ε := by
    have e : Real.sqrt (M / (4 * ε)) = Real.sqrt (M / 4) / Real.sqrt ε := by
      rw [show M / (4 * ε) = M / 4 / ε by field_simp, Real.sqrt_div' _ hε.le]
    have hy' : y ≤ (1 + Real.sqrt (M / 4)) / Real.sqrt ε := by
      apply max_le
      · rw [le_div_iff₀ hs]; nlinarith [Real.sqrt_nonneg (M / 4)]
      · rw [e]; apply div_le_div_of_nonneg_right _ hs.le; linarith
    rw [mul_div_assoc]; linarith
  have hApos : (0 : ℝ) < A := by positivity
  have hBpos : (0 : ℝ) < B := by positivity
  have hlogA : Real.logb 2 A ≤ 3 * Real.sqrt (8 * R + 5) / Real.sqrt ε := by
    calc Real.logb 2 A ≤ Real.logb 2 ((8 * R + 5) / ε) :=
          Real.logb_le_logb_of_le (by norm_num) hApos hA
      _ ≤ 3 * Real.sqrt ((8 * R + 5) / ε) := logb_two_le_three_sqrt (by positivity)
      _ = _ := by rw [Real.sqrt_div' _ hε.le]; ring
  have hlogB : Real.logb 2 B ≤ 3 * Real.sqrt (8 * C0 R M + 7) / Real.sqrt ε := by
    calc Real.logb 2 B ≤ Real.logb 2 ((8 * C0 R M + 7) / ε) :=
          Real.logb_le_logb_of_le (by norm_num) hBpos hB
      _ ≤ 3 * Real.sqrt ((8 * C0 R M + 7) / ε) := logb_two_le_three_sqrt (by positivity)
      _ = _ := by rw [Real.sqrt_div' _ hε.le]; ring
  have hlog41 : Real.logb 2 41 ≤ 6 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
  have hcardR : ((codebook R M q k).card : ℝ) ≤ A * B * 41 ^ (2 ^ k) := by exact_mod_cast hcard
  calc Real.logb 2 (codebook R M q k).card ≤ Real.logb 2 (A * B * 41 ^ (2 ^ k)) :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) hcardR
    _ = Real.logb 2 A + Real.logb 2 B + (2 ^ k : ℕ) * Real.logb 2 41 := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
          (by positivity), Real.logb_pow]
    _ ≤ 3 * Real.sqrt (8 * R + 5) / Real.sqrt ε + 3 * Real.sqrt (8 * C0 R M + 7) / Real.sqrt ε +
          2 * (1 + Real.sqrt (M / 4)) / Real.sqrt ε * 6 := by
        push_cast
        exact add_le_add (add_le_add hlogA hlogB) (mul_le_mul hN hlog41
          (Real.logb_nonneg (by norm_num) (by norm_num)) (by positivity))
    _ = CEnt R M / Real.sqrt ε := by unfold CEnt; ring

/-- A function on `ℝ`, viewed in `C([0,1])` (`0` if it is not continuous on `[0,1]`). -/
noncomputable def toC' (g : ℝ → ℝ) : C(Icc (0 : ℝ) 1, ℝ) :=
  if h : ContinuousOn g (Icc 0 1) then toC g h else 0

/-- A finite set of assemblies with distortion `≤ ε` on `𝓕_{R,M}` yields an `ε`-cover of
`𝓕_{R,M} ⊆ C([0,1])` with at most `|𝒞|` balls. -/
lemma cover_of_codebook {R M ε : ℝ} (hε : 0 ≤ ε) (CB : Finset (ℝ → ℝ))
    (hCB : (CB : Set (ℝ → ℝ)) ⊆ Asm (Icc 0 1))
    (hd : ∀ f ∈ FRM R M, ∃ g ∈ CB, ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ ε) :
    (∀ F ∈ FRMC R M, ∃ c ∈ CB.image toC', dist F c ≤ ε) ∧
      coveringNumber (FRMC R M) ε ≤ CB.card := by
  have hcov : ∀ F ∈ FRMC R M, ∃ c ∈ CB.image toC', dist F c ≤ ε := by
    rintro F ⟨f, hf, hF⟩
    obtain ⟨g, hg, hfg⟩ := hd f hf
    have hgc : ContinuousOn g (Icc 0 1) := (hCB hg).1
    refine ⟨toC' g, Finset.mem_image_of_mem _ hg, ?_⟩
    rw [ContinuousMap.dist_le hε]
    intro x
    simp only [toC', dif_pos hgc, toC_apply, hF x, Real.dist_eq]
    exact hfg x x.2
  refine ⟨hcov, ?_⟩
  unfold coveringNumber
  have h : (CB.image toC').card ∈
      {n | ∃ C : Finset C(Icc (0 : ℝ) 1, ℝ), C.card = n ∧ ∀ f ∈ FRMC R M, ∃ c ∈ C, dist f c ≤ ε} :=
    ⟨_, rfl, hcov⟩
  exact (Nat.sInf_le h).trans Finset.card_image_le

/-- **Theorem 7.18** (entropy and explicit codebook).  There are `ε₀, c, C, C₁ > 0`, depending
only on `R, M`, such that for `0 < ε < ε₀`:
* `c ε^{-1/2} ≤ ℋ_ε(𝓕_{R,M}) ≤ C ε^{-1/2}` (86), where `ℋ_ε = log₂ 𝒩_ε` is the metric entropy of
  `𝓕_{R,M}` in `C([0,1])` with the uniform norm;
* there is a finite codebook `𝒞_ε ⊆ 𝒜([0,1])` (assemblies of atoms of `𝓛`) with distortion at most
  `ε` on `𝓕_{R,M}` (uniform norm on `[0,1]`) whose global fixed-length index has length
  `⌈log₂ |𝒞_ε|⌉ ≤ C₁ ε^{-1/2}` (87);
* the codebook attains the order of the entropy: `c ε^{-1/2} ≤ ℋ_ε ≤ log₂ |𝒞_ε|`. -/
theorem entropy_codebook {R M : ℝ} (hR : 0 < R) (hM : 0 < M) :
    ∃ ε₀ > 0, ∃ c > 0, ∃ C > 0, ∃ C₁ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      c / Real.sqrt ε ≤ metricEntropy (FRMC R M) ε ∧
      metricEntropy (FRMC R M) ε ≤ C / Real.sqrt ε ∧
      ∃ CB : Finset (ℝ → ℝ), (CB : Set (ℝ → ℝ)) ⊆ Asm (Icc 0 1) ∧
        (∀ f ∈ FRM R M, ∃ g ∈ CB, ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ ε) ∧
        (⌈Real.logb 2 CB.card⌉₊ : ℝ) ≤ C₁ / Real.sqrt ε ∧
        metricEntropy (FRMC R M) ε ≤ Real.logb 2 CB.card := by
  obtain ⟨ε₁, hε₁, c, hc, hlow⟩ := entropy_lower hR hM
  have hC := CEnt_pos M hR.le
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, c, hc, CEnt R M, hC, CEnt R M + 1, by linarith,
    fun ε hε hε0 => ?_⟩
  have hεε₁ : ε < ε₁ := lt_of_lt_of_le hε0 (min_le_left _ _)
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hε0 (min_le_right _ _)).le
  obtain ⟨CB, hCB, hd, hlog⟩ := codebook_eps hR hM hε hε1
  obtain ⟨hcov, hN⟩ := cover_of_codebook hε.le CB hCB hd
  have hL := hlow ε hε hεε₁ ⟨_, hcov⟩
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  -- `𝒩_ε > 0`, since `ℋ_ε ≥ c ε^{-1/2} > 0`
  have hNpos : 0 < coveringNumber (FRMC R M) ε := by
    rcases Nat.eq_zero_or_pos (coveringNumber (FRMC R M) ε) with h0 | h
    · have : metricEntropy (FRMC R M) ε = 0 := by simp [metricEntropy, h0]
      have : 0 < c / Real.sqrt ε := by positivity
      linarith
    · exact h
  have hHle : metricEntropy (FRMC R M) ε ≤ Real.logb 2 CB.card :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hNpos) (by exact_mod_cast hN)
  refine ⟨hL, hHle.trans hlog, CB, hCB, hd, ?_, hHle⟩
  have h2 : 1 ≤ 1 / Real.sqrt ε := by rw [le_div_iff₀ hs]; linarith
  rw [add_div]
  rcases le_or_gt 0 (Real.logb 2 CB.card) with hcard0 | hcard0
  · have h1 := Nat.ceil_lt_add_one hcard0
    linarith
  · rw [Nat.ceil_eq_zero.2 hcard0.le, Nat.cast_zero]
    have : 0 ≤ CEnt R M / Real.sqrt ε := by positivity
    linarith

end Dyadic.Lib
