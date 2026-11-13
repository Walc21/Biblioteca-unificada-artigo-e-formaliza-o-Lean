import RequestProject.Codebook

/-!
# Theorem 3.14 (entropia e codebook explícito), Definition 3.15 (codec resources),
# Proposition 3.16 (information lower bound for decodable representation)

All metric notions refer to the uniform distance on `[0,1]` between functions `ℝ → ℝ`.
-/

namespace Artigo

open Set LTree

/-! ## Theorem 3.14 -/

lemma supDist_le_iff {f : ℝ → ℝ} {T : LTree} {ε : ℝ} (hε : 0 ≤ ε) :
    supDist f T ≤ ENNReal.ofReal ε ↔ ∀ x ∈ Icc (0 : ℝ) 1, |f x - T.eval 0 0 x| ≤ ε := by
  constructor
  · intro h x hx
    have : ENNReal.ofReal |f x - T.eval 0 0 x| ≤ supDist f T := le_iSup₂ (f := fun x _ =>
      ENNReal.ofReal |f x - T.eval 0 0 x|) x hx
    exact (ENNReal.ofReal_le_ofReal_iff hε).mp (this.trans h)
  · exact supDist_le

open Classical in
/-- a codebook of assemblies gives an `ε`-cover by their evaluations -/
lemma cover_of_codebook {ε : ℝ} (hε : 0 ≤ ε) {F : Set (ℝ → ℝ)} {CB : Finset LTree}
    (h : ∀ f ∈ F, ∃ T ∈ CB, supDist f T ≤ ENNReal.ofReal ε) :
    IsCover ε F (CB.image fun T => T.eval 0 0) := by
  classical
  intro f hf
  obtain ⟨T, hT, hd⟩ := h f hf
  exact ⟨_, Finset.mem_image_of_mem _ hT, (supDist_le_iff hε).mp hd⟩

lemma nEps_le_C2 {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (nEps M ε : ℝ) ≤ 2 * (2 + Real.sqrt ((M + 4) / 8)) / Real.sqrt ε := by
  have := nEps_lt M ε
  have := Xeps_le hM hε hε1
  rw [mul_div_assoc]; linarith

/-- **Theorem 3.14 (entropia e codebook explícito)**.  For `R, M > 0` there are
`ε₀, c, C, C₁ > 0` such that for `0 < ε < ε₀`:
`c ε^{-1/2} ≤ 𝓗_ε(𝓕_{R,M}) ≤ C ε^{-1/2}`, and there is a finite codebook of assemblies of
library atoms with distortion `≤ ε` whose global fixed-length index has
`⌈log₂ |𝒞_ε|⌉ ≤ C₁ ε^{-1/2}` bits. -/
theorem entropy_codebook (R M : ℝ) (hR : 0 < R) (hM : 0 < M) :
    ∃ ε₀ c C C₁ : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 < C ∧ 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      c / Real.sqrt ε ≤ entropyH ε (FRM R M) ∧ entropyH ε (FRM R M) ≤ C / Real.sqrt ε ∧
      ∃ CB : Finset LTree, (∀ T ∈ CB, WF 0 0 T) ∧
        (∀ f ∈ FRM R M, ∃ T ∈ CB, supDist f T ≤ ENNReal.ofReal ε) ∧
        (Nat.clog 2 CB.card : ℝ) ≤ C₁ / Real.sqrt ε := by
  classical
  obtain ⟨K, hK1, hK⟩ := psi2_bound
  obtain ⟨c0, hc0⟩ := codebook_clog R M
  set C2 := 2 + Real.sqrt ((M + 4) / 8)
  have hC2 : 2 ≤ C2 := by have := Real.sqrt_nonneg ((M + 4) / 8); linarith
  set C₁ := (c0 : ℝ) * (2 * C2) + 1
  have hC₁ : 0 < C₁ := by positivity
  refine ⟨min (min 1 (R / 4)) (M / (16 * K)), Real.sqrt (M / K) / 4, C₁, C₁,
    by positivity, by positivity, hC₁, hC₁, fun ε hε hε0 => ?_⟩
  have hε1 : ε ≤ 1 := by linarith [min_le_left (min 1 (R / 4)) (M / (16 * K)), min_le_left 1 (R / 4)]
  have hεR : 4 * ε ≤ R := by
    linarith [min_le_left (min 1 (R / 4)) (M / (16 * K)), min_le_right 1 (R / 4)]
  have hεM : ε ≤ M / (16 * K) := by linarith [min_le_right (min 1 (R / 4)) (M / (16 * K))]
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  -- the codebook
  set r := rEps M ε
  set CB := codebookSet R M r
  have hcover : ∀ f ∈ FRM R M, ∃ T ∈ CB, supDist f T ≤ ENNReal.ofReal ε := fun f hf =>
    ⟨_, codebook_mem hf (rEps_ge M ε), (eps_construction hf hε).2⟩
  have hclog : (Nat.clog 2 CB.card : ℝ) ≤ C₁ / Real.sqrt ε := by
    have h1 : (Nat.clog 2 CB.card : ℝ) ≤ c0 * (nEps M ε : ℝ) := by
      have := hc0 r (rEps_ge M ε); unfold nEps; exact_mod_cast this
    have h2 := nEps_le_C2 hM.le hε hε1
    calc _ ≤ c0 * (nEps M ε : ℝ) := h1
      _ ≤ c0 * (2 * C2 / Real.sqrt ε) := by gcongr
      _ = (c0 * (2 * C2)) / Real.sqrt ε := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hs.le
  have hcov := cover_of_codebook hε.le hcover
  have hNle : coverNum ε (FRM R M) ≤ CB.card := (coverNum_le hcov).trans Finset.card_image_le
  refine ⟨?_, ?_, CB, fun T hT => codebookSet_WF hT, hcover, hclog⟩
  · -- lower bound via the packing
    set w := Real.sqrt (4 * ε * K / M)
    have hw : 0 < w := Real.sqrt_pos.mpr (by positivity)
    have hw2 : w ^ 2 = 4 * ε * K / M := Real.sq_sqrt (by positivity)
    set m := ⌊1 / w⌋₊
    have hmw : (m : ℝ) * w ≤ 1 := by
      have := Nat.floor_le (show 0 ≤ 1 / w by positivity)
      calc (m : ℝ) * w ≤ 1 / w * w := by gcongr
        _ = 1 := by field_simp
    have hMcond : 4 * ε * K / w ^ 2 ≤ M := by rw [hw2]; field_simp; rfl
    have hpack : 2 ^ m ≤ coverNum ε (FRM R M) :=
      le_coverNum ⟨_, hcov⟩ fun s hs => packing_lower hε hεR hw hK hMcond hmw hs
    have hw_half : w ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ hM]
      have : ε * (16 * K) ≤ M := by rwa [le_div_iff₀ (by positivity)] at hεM
      linarith
    have hm : 1 / (2 * w) ≤ m := by
      have := Nat.sub_one_lt_floor (1 / w)
      have h2 : 1 / (2 * w) ≤ 1 / w - 1 := by
        rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, one_mul]
        field_simp
        nlinarith
      linarith
    have hlog : (m : ℝ) ≤ entropyH ε (FRM R M) := by
      unfold entropyH
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      calc (m : ℝ) = Real.logb 2 ((2 : ℝ) ^ m) := by
            rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
        _ ≤ Real.logb 2 (coverNum ε (FRM R M)) :=
            Real.logb_le_logb_of_le (by norm_num) hpos (by exact_mod_cast hpack)
    have hcw : Real.sqrt (M / K) / 4 / Real.sqrt ε = 1 / (2 * w) := by
      have e : w = 2 * Real.sqrt ε * Real.sqrt (K / M) := by
        simp only [w]
        rw [show 4 * ε * K / M = 2 ^ 2 * ε * (K / M) by ring, Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      rw [e]
      have hKM : Real.sqrt (M / K) * Real.sqrt (K / M) = 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show M / K * (K / M) = 1 by field_simp, Real.sqrt_one]
      have hKM0 : 0 < Real.sqrt (K / M) := Real.sqrt_pos.mpr (by positivity)
      field_simp
      nlinarith [hKM]
    rw [hcw]; linarith
  · -- upper bound via the codebook
    unfold entropyH
    rcases Nat.eq_zero_or_pos (coverNum ε (FRM R M)) with h0 | h0
    · rw [h0]; simp; positivity
    · have hcard : (CB.card : ℝ) ≤ 2 ^ (Nat.clog 2 CB.card) := by
        exact_mod_cast Nat.le_pow_clog (by norm_num) _
      calc Real.logb 2 (coverNum ε (FRM R M)) ≤ Real.logb 2 ((2 : ℝ) ^ (Nat.clog 2 CB.card)) :=
            Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h0)
              ((by exact_mod_cast hNle : (coverNum ε (FRM R M) : ℝ) ≤ CB.card).trans hcard)
        _ = Nat.clog 2 CB.card := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
        _ ≤ _ := hclog

end Artigo
