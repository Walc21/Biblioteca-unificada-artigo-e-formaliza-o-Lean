module
public import RequestProject.Lib.Assembly
public import RequestProject.Lib.Calculus
@[expose] public section

/-!
# Section 4.2: relation with the Taylor 1-jet (Proposition 4.5)
-/

open Set

namespace Dyadic.Lib

/-- The closed dyadic cell `J_{k,m}` as a real interval. -/
def dyCell (k : ℕ) (m : ℤ) : Set ℝ := Icc ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k)

/-- The centre `x₀(k,m) = (2m+1)/2^{k+1}` as a real number. -/
noncomputable def dyCenter (k : ℕ) (m : ℤ) : ℝ := (2 * (m : ℝ) + 1) / 2 ^ (k + 1)

lemma dyCenter_mem (k : ℕ) (m : ℤ) :
    dyCenter k m ∈ Ioo ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k) := by
  unfold dyCenter
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  rw [pow_succ]
  constructor
  · rw [div_lt_div_iff₀ h2 (by positivity)]; nlinarith
  · rw [div_lt_div_iff₀ (by positivity) h2]; nlinarith

lemma dist_dyCenter_le (k : ℕ) (m : ℤ) {x : ℝ} (hx : x ∈ dyCell k m) :
    |x - dyCenter k m| ≤ (1 / 2 ^ k) / 2 := by
  unfold dyCell at hx
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  obtain ⟨h1, h3⟩ := hx
  rw [div_le_iff₀ h2] at h1
  rw [le_div_iff₀ h2] at h3
  have e : x - dyCenter k m = (x * 2 ^ k - m - 1 / 2) / 2 ^ k := by
    unfold dyCenter; rw [pow_succ]; field_simp; ring
  have e2 : (1 / 2 ^ k : ℝ) / 2 = (1 / 2) / 2 ^ k := by ring
  rw [e, e2, abs_div, abs_of_pos h2]
  apply div_le_div_of_nonneg_right _ h2.le
  rw [abs_le]; constructor <;> linarith

lemma Atom.cell_eq_dyCell (a : Atom) : a.cell = dyCell a.k a.m := by
  simp [Atom.cell, dyCell, Atom.left, Atom.right]

lemma Atom.center_eq_dyCenter (a : Atom) : (a.center : ℝ) = dyCenter a.k a.m := by
  simp [Atom.center, dyCenter]

/-- **Proposition 4.5** (membership and adherence). Let `f ∈ C²(J_{k,m})`, with centre `x₀` and
width `h = 2^{-k}`, and `T_{x₀} f(x) = f(x₀) + f'(x₀)(x - x₀)` its 1-jet.
* If `f(x₀) ∈ ℚ` and `f'(x₀) ∈ ℚ^*`, then `T_{x₀} f` is the atom of `𝓛` attached to the cell.
* In general, for every `δ > 0` there are `q₀ ∈ ℚ`, `q₁ ∈ ℚ^*` such that
  `ℓ_q(x) = q₀ + q₁(x - x₀)` satisfies `‖T_{x₀} f - ℓ_q‖_{J} < δ` (eq. (28)) and
  `‖f - ℓ_q‖_{J} ≤ h²/8 · M + δ` (eq. (29)) for every bound `M` of `|f''|` on `J`. -/
theorem taylor_jet (k : ℕ) (m : ℤ) (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (dyCell k m)) :
    (∀ (y₀ s : ℚ), s ≠ 0 → f (dyCenter k m) = y₀ →
        derivWithin f (dyCell k m) (dyCenter k m) = s →
        ∃ a : Atom, a.k = k ∧ a.m = m ∧ a.cell = dyCell k m ∧
          ∀ x, a.line x = f (dyCenter k m) + derivWithin f (dyCell k m) (dyCenter k m) *
            (x - dyCenter k m)) ∧
    ∀ M : ℝ, (∀ x ∈ dyCell k m, |iteratedDerivWithin 2 f (dyCell k m) x| ≤ M) →
      ∀ δ > 0, ∃ q₀ q₁ : ℚ, q₁ ≠ 0 ∧
        (∀ x ∈ dyCell k m, |(f (dyCenter k m) + derivWithin f (dyCell k m) (dyCenter k m) *
            (x - dyCenter k m)) - (q₀ + q₁ * (x - dyCenter k m))| < δ) ∧
        (∀ x ∈ dyCell k m, |f x - (q₀ + q₁ * (x - dyCenter k m))| ≤
            (1 / 2 ^ k) ^ 2 / 8 * M + δ) := by
  set x₀ := dyCenter k m
  set J := dyCell k m
  set h : ℝ := 1 / 2 ^ k with hh
  have hhpos : 0 < h := by positivity
  constructor
  · intro y₀ s hs hy hd
    refine ⟨⟨k, m, y₀, s, hs⟩, rfl, rfl, Atom.cell_eq_dyCell _, fun x => ?_⟩
    have hc := Atom.center_eq_dyCenter ⟨k, m, y₀, s, hs⟩
    simp only [Atom.line]
    rw [hc, hy, hd]
  · intro M hM δ hδ
    have hx₀ := dyCenter_mem k m
    have hlt : (m : ℝ) / 2 ^ k < ((m : ℝ) + 1) / 2 ^ k := hx₀.1.trans hx₀.2
    have hC2 : C2Bound f ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k) M :=
      C2Bound.of_contDiffOn hlt hf hM le_rfl le_rfl
    have hderiv : derivWithin f J x₀ = deriv f x₀ :=
      derivWithin_of_mem_nhds (Icc_mem_nhds hx₀.1 hx₀.2)
    set d := derivWithin f J x₀
    obtain ⟨q₀, hq₀⟩ := exists_rat_btwn (show f x₀ - δ / 2 < f x₀ by linarith)
    have hq0 : |f x₀ - q₀| < δ / 2 := by rw [abs_lt]; constructor <;> linarith [hq₀.1, hq₀.2]
    obtain ⟨q₁, hq₁ne, hq₁⟩ : ∃ q₁ : ℚ, q₁ ≠ 0 ∧ |d - q₁| < δ / h := by
      have hδh : 0 < δ / h := by positivity
      rcases le_or_gt 0 d with hd | hd
      · obtain ⟨q, hq⟩ := exists_rat_btwn (show d < d + δ / h by linarith)
        refine ⟨q, ?_, ?_⟩
        · intro h0; rw [h0] at hq; simp at hq; linarith [hq.1]
        · rw [abs_lt]; constructor <;> linarith [hq.1, hq.2]
      · obtain ⟨q, hq⟩ := exists_rat_btwn (show d - δ / h < d by linarith)
        refine ⟨q, ?_, ?_⟩
        · intro h0; rw [h0] at hq; simp at hq; linarith [hq.2]
        · rw [abs_lt]; constructor <;> linarith [hq.1, hq.2]
    have hjet : ∀ x ∈ J, |(f x₀ + d * (x - x₀)) - (q₀ + q₁ * (x - x₀))| < δ := by
      intro x hx
      have hdist := dist_dyCenter_le k m hx
      have e : (f x₀ + d * (x - x₀)) - (q₀ + q₁ * (x - x₀)) = (f x₀ - q₀) + (d - q₁) * (x - x₀) := by
        ring
      rw [e]
      calc |(f x₀ - q₀) + (d - q₁) * (x - x₀)| ≤ |f x₀ - q₀| + |d - q₁| * |x - x₀| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ < δ / 2 + δ / h * (h / 2) := by
            apply add_lt_add_of_lt_of_le hq0
            exact mul_le_mul hq₁.le hdist (abs_nonneg _) (by positivity)
        _ = δ := by field_simp; ring
    refine ⟨q₀, q₁, hq₁ne, hjet, fun x hx => ?_⟩
    have ht := taylor1_bound hC2 hx₀ hx
    rw [← hderiv] at ht
    have hdist := dist_dyCenter_le k m hx
    have hsq : (x - x₀) ^ 2 ≤ (h / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hdist 2
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
    have e : f x - (q₀ + q₁ * (x - x₀)) = (f x - f x₀ - d * (x - x₀)) +
        ((f x₀ + d * (x - x₀)) - (q₀ + q₁ * (x - x₀))) := by ring
    rw [e]
    calc _ ≤ |f x - f x₀ - d * (x - x₀)| + |(f x₀ + d * (x - x₀)) - (q₀ + q₁ * (x - x₀))| :=
          abs_add_le _ _
      _ ≤ M / 2 * (h / 2) ^ 2 + δ := by
          apply add_le_add (ht.trans (mul_le_mul_of_nonneg_left hsq (by positivity)))
            (hjet x hx).le
      _ = h ^ 2 / 8 * M + δ := by ring

end Dyadic.Lib
