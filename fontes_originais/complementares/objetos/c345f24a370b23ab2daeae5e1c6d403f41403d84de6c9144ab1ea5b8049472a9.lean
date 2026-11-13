module
public import RequestProject.Sec7.Simultaneous
@[expose] public section

/-!
# Corollary 7.17: sufficient height for a prescribed precision
-/

open Set

namespace Dyadic.Lib

/-- The exponent `⌈log₂ max{2, √((M+4)/(8ε))}⌉` of `n_ε`. -/
noncomputable def rEps (M ε : ℝ) : ℕ := ⌈Real.logb 2 (max 2 (Real.sqrt ((M + 4) / (8 * ε))))⌉₊

/-- `n_ε = 2^{⌈log₂ max{2, √((M+4)/(8ε))}⌉}` (eq. (82)). -/
noncomputable def nEps (M ε : ℝ) : ℕ := 2 ^ rEps M ε

/-- `H_ε = ⌈C_H n_ε²⌉` (eq. (82)). -/
noncomputable def HEps (R M ε : ℝ) : ℕ := ⌈CH R M * (nEps M ε : ℝ) ^ 2⌉₊

section

variable {M ε : ℝ}

lemma rEps_spec :
    1 ≤ rEps M ε ∧ max 2 (Real.sqrt ((M + 4) / (8 * ε))) ≤ (nEps M ε : ℝ) ∧
      (nEps M ε : ℝ) < 2 * max 2 (Real.sqrt ((M + 4) / (8 * ε))) := by
  set x := max 2 (Real.sqrt ((M + 4) / (8 * ε)))
  have hx : 2 ≤ x := le_max_left _ _
  have hl : 1 ≤ Real.logb 2 x := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hx
  have he : Real.logb 2 x ≤ rEps M ε := Nat.le_ceil _
  have he' : (rEps M ε : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one (by linarith)
  refine ⟨Nat.one_le_iff_ne_zero.2 (fun h => by
      have := Nat.ceil_eq_zero.1 h; linarith), ?_, ?_⟩
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith), Real.rpow_natCast] at he
    unfold nEps; push_cast; exact he
  · have : (2 : ℝ) ^ (rEps M ε : ℝ) < 2 ^ (Real.logb 2 x + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) he'
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
      Real.rpow_one, Real.rpow_natCast] at this
    unfold nEps; push_cast; linarith

lemma nEps_le (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (nEps M ε : ℝ) ≤ (4 + 2 * Real.sqrt ((M + 4) / 8)) / Real.sqrt ε := by
  obtain ⟨-, -, h⟩ := rEps_spec (M := M) (ε := ε)
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have e : Real.sqrt ((M + 4) / (8 * ε)) = Real.sqrt ((M + 4) / 8) / Real.sqrt ε := by
    rw [show (M + 4) / (8 * ε) = (M + 4) / 8 / ε by field_simp, Real.sqrt_div' _ hε.le]
  have hA := Real.sqrt_nonneg ((M + 4) / 8)
  have hmax : max 2 (Real.sqrt ((M + 4) / (8 * ε))) ≤ (2 + Real.sqrt ((M + 4) / 8)) /
      Real.sqrt ε := by
    rw [e]
    apply max_le
    · rw [le_div_iff₀ hs]; nlinarith
    · rw [div_le_div_iff_of_pos_right hs]; linarith
  calc (nEps M ε : ℝ) ≤ 2 * max 2 (Real.sqrt ((M + 4) / (8 * ε))) := h.le
    _ ≤ 2 * ((2 + Real.sqrt ((M + 4) / 8)) / Real.sqrt ε) := by linarith
    _ = _ := by ring

end

/-- **Corollary 7.17** (sufficient height for a prescribed precision).  With
`n_ε = 2^{⌈log₂ max{2, √((M+4)/(8ε))}⌉}` and `H_ε = ⌈C_H n_ε²⌉`, uniformly for `f ∈ 𝓕_{R,M}`:
(83) `E_{n_ε, H_ε}(f) ≤ ε` and in particular `H_{ε,n_ε}(f) ≤ H_ε`;
(84) `n_ε = O_{R,M}(ε^{-1/2})`, `H_ε = O_{R,M}(ε^{-1})`;
(85) the three formats of the assembly `g_{n_ε}` of Theorem 7.16 have length
`O_{R,M}(ε^{-1/2} log(2/ε))`.  The asymptotic bounds are stated for `0 < ε ≤ 1`. -/
theorem precision_height (R M : ℝ) :
    (∀ ε : ℝ, 0 < ε → ∀ f ∈ FRM R M,
      jointError (Icc 0 1) (nEps M ε) (HEps R M ε) f ≤ ENNReal.ofReal ε ∧
      minHeight (Icc 0 1) ε (nEps M ε) f ≤ HEps R M ε) ∧
    (∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (nEps M ε : ℝ) ≤ C / Real.sqrt ε ∧ (HEps R M ε : ℝ) ≤ C / ε) ∧
    (∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ f ∈ FRM R M,
      ((streamAtom (leafAtom f (rEps M ε)) (nEps M ε)).length : ℝ) ≤
        C / Real.sqrt ε * Real.logb 2 (2 / ε) ∧
      ((streamStr (leafAtom f (rEps M ε)) (nEps M ε)).length : ℝ) ≤
        C / Real.sqrt ε * Real.logb 2 (2 / ε) ∧
      ((streamRat (leafAtom f (rEps M ε)) (nEps M ε)).length : ℝ) ≤
        C / Real.sqrt ε * Real.logb 2 (2 / ε)) := by
  set A := Real.sqrt ((M + 4) / 8)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  set Cn := 4 + 2 * A
  have hCn : 4 ≤ Cn := by simp only [Cn]; linarith
  refine ⟨fun ε hε f hf => ?_, ⟨Cn + |CH R M| * Cn ^ 2 + 1, fun ε hε hε1 => ?_⟩, ?_⟩
  · -- (83)
    have hM := FRM.M_nonneg hf
    obtain ⟨hr1, hx, -⟩ := rEps_spec (M := M) (ε := ε)
    set n := nEps M ε
    have hn : Real.sqrt ((M + 4) / (8 * ε)) ≤ n := (le_max_right _ _).trans hx
    have hn2 : (2 : ℝ) ≤ n := (le_max_left _ _).trans hx
    have hsq : (M + 4) / (8 * ε) ≤ (n : ℝ) ^ 2 := by
      have := Real.sq_sqrt (show 0 ≤ (M + 4) / (8 * ε) by positivity)
      nlinarith [Real.sqrt_nonneg ((M + 4) / (8 * ε))]
    have herr : (M + 4) / (8 * (n : ℝ) ^ 2) ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hsq
      nlinarith
    have hg : gN f (rEps M ε) ∈ AsmNH (Icc 0 1) n (HEps R M ε) := by
      apply gN_mem_AsmNH hf le_rfl
      unfold HEps; refine le_trans ?_ (Nat.le_ceil _)
      simp only [nEps]; push_cast; exact le_rfl
    have h83 : jointError (Icc 0 1) n (HEps R M ε) f ≤ ENNReal.ofReal ε := by
      refine (jointError_le_of_mem hg (by positivity) (fun x hx => ?_)).trans
        (ENNReal.ofReal_le_ofReal herr)
      have := gN_error hf (rEps M ε) x hx
      simp only [n, nEps]; push_cast; exact this
    refine ⟨h83, Nat.sInf_le ⟨?_, h83⟩⟩
    have hCH := CH_pos hf
    have : (2 : ℝ) ≤ CH R M * (n : ℝ) ^ 2 := by nlinarith
    have h3 := Nat.le_ceil (CH R M * (n : ℝ) ^ 2)
    have h2 : (2 : ℝ) ≤ (⌈CH R M * (n : ℝ) ^ 2⌉₊ : ℝ) := by linarith
    unfold HEps
    exact_mod_cast h2
  · -- (84)
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    have hsε : ε ≤ Real.sqrt ε := (Real.le_sqrt hε.le hε.le).2 (by nlinarith)
    have hn := nEps_le (M := M) hε hε1
    have hn0 : (0 : ℝ) ≤ nEps M ε := by positivity
    have hC0 : 0 ≤ |CH R M| * Cn ^ 2 + 1 := by positivity
    constructor
    · calc (nEps M ε : ℝ) ≤ Cn / Real.sqrt ε := hn
        _ ≤ (Cn + |CH R M| * Cn ^ 2 + 1) / Real.sqrt ε :=
          div_le_div_of_nonneg_right (by linarith) hs.le
    · have hn' : (nEps M ε : ℝ) ^ 2 ≤ Cn ^ 2 / ε := by
        have := pow_le_pow_left₀ hn0 hn 2
        rwa [div_pow, Real.sq_sqrt hε.le] at this
      have h1 : CH R M * (nEps M ε : ℝ) ^ 2 ≤ |CH R M| * (Cn ^ 2 / ε) :=
        (le_abs_self _ |> fun h => mul_le_mul h hn' (by positivity) (abs_nonneg _))
      have hceil : (HEps R M ε : ℝ) ≤ |CH R M| * (Cn ^ 2 / ε) + 1 := by
        unfold HEps
        rcases le_or_gt 0 (CH R M * (nEps M ε : ℝ) ^ 2) with h | h
        · have := Nat.ceil_lt_add_one h; linarith
        · rw [Nat.ceil_eq_zero.2 h.le]; simp only [Nat.cast_zero]; positivity
      have h2 : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
      calc (HEps R M ε : ℝ) ≤ |CH R M| * (Cn ^ 2 / ε) + 1 / ε := by linarith
        _ = (|CH R M| * Cn ^ 2 + 1) / ε := by ring
        _ ≤ (Cn + |CH R M| * Cn ^ 2 + 1) / ε := div_le_div_of_nonneg_right (by linarith) hε.le
  · -- (85)
    set K := 200 * (|Real.logb 2 (CH R M)| + 2) + (8 * |Real.logb 2 (6 * CH R M ^ 2)| + 40)
    refine ⟨K * Cn * (|Real.logb 2 Cn| + 1), fun ε hε hε1 f hf => ?_⟩
    obtain ⟨b1, b2⟩ := gN_bits_atom_str hf (r := rEps M ε)
    have b3 := gN_bits_rat hf (r := rEps M ε)
    set r := rEps M ε
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    have hsε : ε ≤ Real.sqrt ε := (Real.le_sqrt hε.le hε.le).2 (by nlinarith)
    have hn : ((2 : ℝ) ^ r) ≤ Cn / Real.sqrt ε := by
      have := nEps_le (M := M) hε hε1; simp only [nEps] at this; push_cast at this; exact this
    -- `r + 1 = log₂(2n) ≤ (|log₂ Cn| + 1) log₂(2/ε)`
    have hl2 : 1 ≤ Real.logb 2 (2 / ε) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one,
        le_div_iff₀ hε]; linarith
    have hr1 : (r : ℝ) + 1 ≤ (|Real.logb 2 Cn| + 1) * Real.logb 2 (2 / ε) := by
      rw [← logb_two_pow_succ]
      have h2n : 2 * (2 : ℝ) ^ r ≤ Cn * (2 / ε) := by
        have : Cn / Real.sqrt ε ≤ Cn / ε := div_le_div_of_nonneg_left (by linarith) hε hsε
        have := hn.trans this
        calc 2 * (2 : ℝ) ^ r ≤ 2 * (Cn / ε) := by linarith
          _ = Cn * (2 / ε) := by ring
      calc Real.logb 2 (2 * 2 ^ r) ≤ Real.logb 2 (Cn * (2 / ε)) :=
            Real.logb_le_logb_of_le (by norm_num) (by positivity) h2n
        _ = Real.logb 2 Cn + Real.logb 2 (2 / ε) := by
            rw [Real.logb_mul (by linarith) (by positivity)]
        _ ≤ |Real.logb 2 Cn| * Real.logb 2 (2 / ε) + Real.logb 2 (2 / ε) := by
            have := le_abs_self (Real.logb 2 Cn)
            have : |Real.logb 2 Cn| ≤ |Real.logb 2 Cn| * Real.logb 2 (2 / ε) :=
              le_mul_of_one_le_right (abs_nonneg _) hl2
            linarith
        _ = _ := by ring
    have hK1 : 200 * (Real.logb 2 (CH R M) + 2) ≤ K := by
      simp only [K]; linarith [le_abs_self (Real.logb 2 (CH R M)),
        abs_nonneg (Real.logb 2 (6 * CH R M ^ 2))]
    have hK2 : 8 * Real.logb 2 (6 * CH R M ^ 2) + 40 ≤ K := by
      simp only [K]; linarith [le_abs_self (Real.logb 2 (6 * CH R M ^ 2)),
        abs_nonneg (Real.logb 2 (CH R M))]
    have hK0 : 0 ≤ K := by simp only [K]; positivity
    have hr0 : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
    have key : ∀ c : ℝ, c ≤ K → c * 2 ^ r * (r + 1) ≤
        K * Cn * (|Real.logb 2 Cn| + 1) / Real.sqrt ε * Real.logb 2 (2 / ε) := by
      intro c hc
      have h1 : c * 2 ^ r * (r + 1) ≤ K * 2 ^ r * (r + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hr0
      have h2 : K * (2 : ℝ) ^ r * (r + 1) ≤ K * (Cn / Real.sqrt ε) *
          ((|Real.logb 2 Cn| + 1) * Real.logb 2 (2 / ε)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hn hK0) hr1 hr0 (by positivity)
      calc c * 2 ^ r * (r + 1) ≤ _ := h1.trans h2
        _ = _ := by ring
    have hnE : nEps M ε = 2 ^ r := rfl
    rw [hnE]
    exact ⟨b1.trans (key _ hK1), b2.trans (key _ hK1), b3.trans (key _ hK2)⟩

end Dyadic.Lib
