import Mathlib

/-!
# V.21.1 — majorante local da função de Runge

`f(x) = 1/(1+25x²)`, `f''(x) = 50(75x²-1)/(1+25x²)³`, `f'''(x) = 7500x(2-50x²)/(1+25x²)⁴`.

Em todo intervalo fechado `J = [a,b]`, o máximo de `|f''|` em `J` é atingido num extremo
de `J` ou num ponto de `{0, -1/5, 1/5} ∩ J`. A prova não usa `J ⊆ [-1,1]`; o enunciado
do volume é o caso particular `runge_majorant_sub`.
-/

namespace Pendencias.Runge

open Set

/-- função de Runge -/
noncomputable def runge (x : ℝ) : ℝ := 1 / (1 + 25 * x ^ 2)
/-- `f'` -/
noncomputable def runge1 (x : ℝ) : ℝ := -50 * x / (1 + 25 * x ^ 2) ^ 2
/-- `f''` -/
noncomputable def runge2 (x : ℝ) : ℝ := 50 * (75 * x ^ 2 - 1) / (1 + 25 * x ^ 2) ^ 3
/-- `f'''` -/
noncomputable def runge3 (x : ℝ) : ℝ := 7500 * x * (2 - 50 * x ^ 2) / (1 + 25 * x ^ 2) ^ 4

lemma den_pos (x : ℝ) : 0 < 1 + 25 * x ^ 2 := by positivity

lemma hasDerivAt_den (x : ℝ) : HasDerivAt (fun y : ℝ => 1 + 25 * y ^ 2) (50 * x) x := by
  have := ((hasDerivAt_id' x).pow 2).const_mul 25 |>.const_add 1
  convert this using 1
  ring

lemma hasDerivAt_runge (x : ℝ) : HasDerivAt runge (runge1 x) x := by
  have hd := (den_pos x).ne'
  have := (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_den x) hd
  convert this using 1
  simp only [runge1]
  field_simp
  ring

lemma hasDerivAt_runge1 (x : ℝ) : HasDerivAt runge1 (runge2 x) x := by
  have hd := (den_pos x).ne'
  have := ((hasDerivAt_id' x).const_mul (-50)).div ((hasDerivAt_den x).pow 2) (pow_ne_zero 2 hd)
  convert this using 1
  simp only [runge2, Pi.pow_apply]
  field_simp
  ring

lemma hasDerivAt_runge2 (x : ℝ) : HasDerivAt runge2 (runge3 x) x := by
  have hd := (den_pos x).ne'
  have h1 : HasDerivAt (fun y : ℝ => 50 * (75 * y ^ 2 - 1)) (7500 * x) x := by
    have := (((hasDerivAt_id' x).pow 2).const_mul 75 |>.sub_const 1).const_mul 50
    convert this using 1
    ring
  have := h1.div ((hasDerivAt_den x).pow 3) (pow_ne_zero 3 hd)
  convert this using 1
  simp only [runge3, Pi.pow_apply]
  field_simp
  ring

/-- `f'' = runge2` -/
theorem deriv2_runge : deriv (deriv runge) = runge2 := by
  have h1 : deriv runge = runge1 := funext fun x => (hasDerivAt_runge x).deriv
  rw [h1]
  exact funext fun x => (hasDerivAt_runge1 x).deriv

lemma continuous_runge2 : Continuous runge2 := by
  unfold runge2
  exact Continuous.div (by fun_prop) (by fun_prop) fun x => (pow_pos (den_pos x) 3).ne'

/-- os zeros de `f'''` são `0, ±1/5` -/
lemma runge3_eq_zero {c : ℝ} (h : runge3 c = 0) : c ∈ ({0, -1/5, 1/5} : Set ℝ) := by
  unfold runge3 at h
  rw [div_eq_zero_iff, or_iff_left (pow_pos (den_pos c) 4).ne'] at h
  have h2 : c * ((5 * c - 1) * (5 * c + 1)) = 0 := by linear_combination (-1 / 15000 : ℝ) * h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · right; right; linarith
    · right; left; linarith

/-- **Lema V.21.1** (forma forte, sem `J ⊆ [-1,1]`). -/
theorem runge_majorant {a b : ℝ} (hab : a ≤ b) :
    ∃ c ∈ Icc a b, (c = a ∨ c = b ∨ c ∈ ({0, -1/5, 1/5} : Set ℝ)) ∧
      ∀ x ∈ Icc a b, |runge2 x| ≤ |runge2 c| := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    continuous_runge2.abs.continuousOn
  have hle : ∀ x ∈ Icc a b, |runge2 x| ≤ |runge2 c| := fun x hx => hmax hx
  by_cases hca : c = a
  · exact ⟨c, hc, Or.inl hca, hle⟩
  by_cases hcb : c = b
  · exact ⟨c, hc, Or.inr (Or.inl hcb), hle⟩
  have hint : Icc a b ∈ nhds c :=
    Icc_mem_nhds (lt_of_le_of_ne hc.1 (Ne.symm hca)) (lt_of_le_of_ne hc.2 hcb)
  rcases lt_trichotomy (runge2 c) 0 with hneg | hzero | hpos
  · have hmin : IsLocalMin runge2 c := by
      filter_upwards [hint] with x hx
      have h1 := hle x hx
      rw [abs_of_neg hneg] at h1
      linarith [neg_abs_le (runge2 x)]
    exact ⟨c, hc, Or.inr (Or.inr (runge3_eq_zero (hmin.hasDerivAt_eq_zero (hasDerivAt_runge2 c)))),
      hle⟩
  · refine ⟨a, left_mem_Icc.mpr hab, Or.inl rfl, fun x hx => ?_⟩
    have h1 := hle x hx
    rw [hzero, abs_zero] at h1
    exact h1.trans (abs_nonneg _)
  · have hmx : IsLocalMax runge2 c := by
      filter_upwards [hint] with x hx
      have h1 := hle x hx
      rw [abs_of_pos hpos] at h1
      linarith [le_abs_self (runge2 x)]
    exact ⟨c, hc, Or.inr (Or.inr (runge3_eq_zero (hmx.hasDerivAt_eq_zero (hasDerivAt_runge2 c)))),
      hle⟩

/-- **Lema V.21.1** como no volume: `J = [a,b] ⊆ [-1,1]`, com `|f''|` escrito via
`deriv (deriv runge)`, e o ponto candidato em `J`. -/
theorem runge_majorant_sub {a b : ℝ} (hab : a ≤ b) (_hJ : Icc a b ⊆ Icc (-1) 1) :
    ∃ c ∈ Icc a b, (c = a ∨ c = b ∨ c ∈ ({0, -1/5, 1/5} : Set ℝ)) ∧
      ∀ x ∈ Icc a b, |deriv (deriv runge) x| ≤ |deriv (deriv runge) c| := by
  rw [deriv2_runge]
  exact runge_majorant hab

end Pendencias.Runge
