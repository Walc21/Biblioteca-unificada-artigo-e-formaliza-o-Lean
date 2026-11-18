import Pendencias.FaseNucleo

/-!
# III.12.7 — passos pontuais

Para sequências `s_j → sLim ≥ 0` e fases `T_j` com `T_j - z_j → τ` (módulo inteiros):

* (inferior) `(sLim/√8)·gC(τ + aLim) - δ ≤ (s_j/√8)·gC(T_j + a_j)` eventualmente;
* (superior) `(s_j/√8)·gC(T_j + a_j) ≤ (sLim/√8)·gP(τ + aLim) + δ` eventualmente,

onde `a_j = log₄(L² s_j²/8)` e `aLim = log₄(L² sLim²/8)`. Usam só `gC` semicontínua inferior e
`gP` semicontínua superior.
-/

namespace Pendencias

open Set Filter Topology

/-- `diagonal`: se cada `P n` vale eventualmente em `j`, existe `φ → ∞` com `P (φ j) j` eventual -/
lemma exists_diag (P : ℕ → ℕ → Prop) (hP : ∀ n, ∀ᶠ j in atTop, P n j) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ ∀ᶠ j in atTop, P (φ j) j := by
  classical
  refine ⟨fun j => Nat.findGreatest (fun n => P n j) j, ?_, ?_⟩
  · refine tendsto_atTop.mpr fun N => ?_
    filter_upwards [hP N, eventually_ge_atTop N] with j hj hNj
    exact Nat.le_findGreatest hNj hj
  · filter_upwards [hP 0] with j hj
    exact Nat.findGreatest_spec (P := fun n => P n j) (Nat.zero_le j) hj

lemma gC_sub_int (u : ℝ) (z : ℤ) : gC (u - z) = gC u := by
  have := gC_add_int u (-z)
  simpa [sub_eq_add_neg] using this

variable {L : ℝ}

lemma logb_tendsto {s : ℕ → ℝ} {sLim : ℝ} (hL : 0 < L) (hs : Tendsto s atTop (𝓝 sLim))
    (hpos : 0 < sLim) :
    Tendsto (fun j => Real.logb 4 (L ^ 2 * s j ^ 2 / 8)) atTop
      (𝓝 (Real.logb 4 (L ^ 2 * sLim ^ 2 / 8))) := by
  have h1 : Tendsto (fun j => L ^ 2 * s j ^ 2 / 8) atTop (𝓝 (L ^ 2 * sLim ^ 2 / 8)) :=
    ((hs.pow 2).const_mul _).div_const _
  have hne : (L ^ 2 * sLim ^ 2 / 8) ≠ 0 := by positivity
  unfold Real.logb
  exact ((Real.continuousAt_log hne).tendsto.comp h1).div_const _

lemma gP_sub_int (u : ℝ) (z : ℤ) : gP (u - z) = gP u := by
  have := gP_add_int u (-z)
  simpa [sub_eq_add_neg] using this

lemma pointwise_lower (hL : 0 < L) {s : ℕ → ℝ} {sLim : ℝ} (hs0 : ∀ j, 0 ≤ s j)
    (hs : Tendsto s atTop (𝓝 sLim)) {T : ℕ → ℝ} {z : ℕ → ℤ} {τ : ℝ}
    (hT : Tendsto (fun j => T j - z j) atTop (𝓝 τ)) :
    ∀ δ > 0, ∀ᶠ j in atTop,
      sLim / Real.sqrt 8 * gC (τ + Real.logb 4 (L ^ 2 * sLim ^ 2 / 8)) - δ ≤
        s j / Real.sqrt 8 * gC (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8)) := by
  intro δ hδ
  have h8 : 0 < Real.sqrt 8 := by positivity
  have hsLim : 0 ≤ sLim := ge_of_tendsto' hs hs0
  rcases hsLim.eq_or_lt with h0 | hpos
  · refine Eventually.of_forall fun j => ?_
    rw [← h0]
    have := mul_nonneg (div_nonneg (hs0 j) h8.le)
      (gC_nonneg (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8)))
    simp only [zero_div, zero_mul]
    linarith
  · set aLim := Real.logb 4 (L ^ 2 * sLim ^ 2 / 8)
    have ha := logb_tendsto hL hs hpos
    have hv : Tendsto (fun j => T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8) - z j) atTop
        (𝓝 (τ + aLim)) :=
      (hT.add ha).congr fun j => by ring
    set gLim := gC (τ + aLim)
    set p := sLim / Real.sqrt 8
    have hp : 0 < p := by positivity
    have hg1 : 1 ≤ gLim := gC_ge_one _
    set κ : ℝ := min 1 (δ / (p + gLim + 1)) with hκ
    have hκpos : 0 < κ := lt_min one_pos (by positivity)
    have hκ1 : κ ≤ 1 := min_le_left _ _
    have hκδ : κ * (p + gLim + 1) ≤ δ := by
      have := min_le_right 1 (δ / (p + gLim + 1))
      calc κ * (p + gLim + 1) ≤ δ / (p + gLim + 1) * (p + gLim + 1) := by gcongr
        _ = δ := by field_simp
    have e1 : ∀ᶠ j in atTop, gLim - κ < gC (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8)) := by
      have h2 := hv.eventually (gC_lsc (τ + aLim) (gLim - κ) (by linarith))
      filter_upwards [h2] with j hj
      rwa [gC_sub_int] at hj
    have e2 : ∀ᶠ j in atTop, p - κ < s j / Real.sqrt 8 :=
      (hs.div_const _).eventually (lt_mem_nhds (by linarith))
    filter_upwards [e1, e2] with j h1 h2
    have hA0 : 0 ≤ s j / Real.sqrt 8 := div_nonneg (hs0 j) h8.le
    have hGge : 0 ≤ gLim - κ := by linarith
    have h3 : (p - κ) * (gLim - κ) ≤
        s j / Real.sqrt 8 * gC (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8)) := by
      nlinarith [mul_nonneg hA0 (sub_nonneg.mpr h1.le), mul_nonneg (sub_nonneg.mpr h2.le) hGge]
    nlinarith [h3, hκδ, sq_nonneg κ]

lemma pointwise_upper (hL : 0 < L) {s : ℕ → ℝ} {sLim : ℝ} (hs0 : ∀ j, 0 ≤ s j)
    (hs : Tendsto s atTop (𝓝 sLim)) {T : ℕ → ℝ} {z : ℕ → ℤ} {τ : ℝ}
    (hT : Tendsto (fun j => T j - z j) atTop (𝓝 τ)) :
    ∀ δ > 0, ∀ᶠ j in atTop,
      s j / Real.sqrt 8 * gC (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8)) ≤
        sLim / Real.sqrt 8 * gP (τ + Real.logb 4 (L ^ 2 * sLim ^ 2 / 8)) + δ := by
  intro δ hδ
  have h8 : 0 < Real.sqrt 8 := by positivity
  have hsLim : 0 ≤ sLim := ge_of_tendsto' hs hs0
  rcases hsLim.eq_or_lt with h0 | hpos
  · have e : ∀ᶠ j in atTop, s j / Real.sqrt 8 < δ / 2 := by
      have := hs.div_const (Real.sqrt 8)
      rw [← h0, zero_div] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    filter_upwards [e] with j hj
    rw [← h0]
    have hA0 : 0 ≤ s j / Real.sqrt 8 := div_nonneg (hs0 j) h8.le
    have := gC_lt_two (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8))
    simp only [zero_div, zero_mul, zero_add]
    nlinarith [gC_nonneg (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8))]
  · set aLim := Real.logb 4 (L ^ 2 * sLim ^ 2 / 8)
    have ha := logb_tendsto hL hs hpos
    have hv : Tendsto (fun j => T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8) - z j) atTop
        (𝓝 (τ + aLim)) :=
      (hT.add ha).congr fun j => by ring
    set gLim := gP (τ + aLim)
    set p := sLim / Real.sqrt 8
    have hp : 0 < p := by positivity
    have hg1 : 1 ≤ gLim := gP_ge_one _
    set κ : ℝ := min 1 (δ / (p + gLim + 1)) with hκ
    have hκpos : 0 < κ := lt_min one_pos (by positivity)
    have hκ1 : κ ≤ 1 := min_le_left _ _
    have hκδ : κ * (p + gLim + 1) ≤ δ := by
      have := min_le_right 1 (δ / (p + gLim + 1))
      calc κ * (p + gLim + 1) ≤ δ / (p + gLim + 1) * (p + gLim + 1) := by gcongr
        _ = δ := by field_simp
    have e1 : ∀ᶠ j in atTop,
        gP (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8) - z j) < gLim + κ :=
      hv.eventually (gP_usc (τ + aLim) (gLim + κ) (by linarith))
    have e2 : ∀ᶠ j in atTop, s j / Real.sqrt 8 < p + κ :=
      (hs.div_const _).eventually (gt_mem_nhds (by linarith))
    filter_upwards [e1, e2] with j h1 h2
    have hA0 : 0 ≤ s j / Real.sqrt 8 := div_nonneg (hs0 j) h8.le
    rw [gP_sub_int] at h1
    have hG0 := gC_nonneg (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8))
    have hGP := gC_le_gP (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8))
    have h3 : s j / Real.sqrt 8 * gC (T j + Real.logb 4 (L ^ 2 * s j ^ 2 / 8)) ≤
        (p + κ) * (gLim + κ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2.le) hG0,
        mul_nonneg (show (0:ℝ) ≤ p + κ by linarith) (sub_nonneg.mpr (hGP.trans h1.le))]
    nlinarith [h3, hκδ, sq_nonneg κ]

end Pendencias
