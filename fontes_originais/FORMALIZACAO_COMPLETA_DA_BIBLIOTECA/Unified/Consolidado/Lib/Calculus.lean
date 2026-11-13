module
public import Mathlib
@[expose] public section

/-!
# Calculus helpers: second-derivative bounds

Taylor bound of order one and the linear interpolation error bound
`|f(x) - P f(x)| ≤ M (x - p)(q - x)/2`, obtained from convexity of `±f + M u²/2`.
-/

open Set

namespace Dyadic.Lib

/-- Interior `C²` regularity with a bound `M` on the second derivative over `(p, q)`, together with
continuity on `[p, q]`. -/
def C2Bound (f : ℝ → ℝ) (p q M : ℝ) : Prop :=
  ContinuousOn f (Icc p q) ∧ ContDiffOn ℝ 2 f (Ioo p q) ∧ ∀ u ∈ Ioo p q, |deriv^[2] f u| ≤ M

lemma C2Bound.mono {f : ℝ → ℝ} {p q M p' q' : ℝ} (h : C2Bound f p q M) (hp : p ≤ p') (hq : q' ≤ q) :
    C2Bound f p' q' M :=
  ⟨h.1.mono (Icc_subset_Icc hp hq), h.2.1.mono (Ioo_subset_Ioo hp hq),
    fun u hu => h.2.2 u (Ioo_subset_Ioo hp hq hu)⟩

lemma convex_aux {f : ℝ → ℝ} {p q M : ℝ} (h : C2Bound f p q M) (c : ℝ) (hc : |c| ≤ 1) :
    ConvexOn ℝ (Icc p q) (fun u => c * f u + M / 2 * u ^ 2) := by
  obtain ⟨hcont, hdiff, hM⟩ := h
  have hint : interior (Icc p q) = Ioo p q := interior_Icc
  have hd1 : DifferentiableOn ℝ f (Ioo p q) := hdiff.differentiableOn (by norm_num)
  have hdf : ContDiffOn ℝ 1 (deriv f) (Ioo p q) := hdiff.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd2 : DifferentiableOn ℝ (deriv f) (Ioo p q) := hdf.differentiableOn (by norm_num)
  have hderiv : ∀ u ∈ Ioo p q, deriv (fun u => c * f u + M / 2 * u ^ 2) u = c * deriv f u + M * u := by
    intro u hu
    have hfu : DifferentiableAt ℝ f u := hd1.differentiableAt (isOpen_Ioo.mem_nhds hu)
    have : HasDerivAt (fun u => c * f u + M / 2 * u ^ 2) (c * deriv f u + M / 2 * (2 * u)) u := by
      have h1 := (hfu.hasDerivAt.const_mul c)
      have h2 := ((hasDerivAt_pow 2 u).const_mul (M / 2))
      convert h1.add h2 using 1
      simp
    rw [this.deriv]; ring
  have heq : EqOn (deriv (fun u => c * f u + M / 2 * u ^ 2)) (fun u => c * deriv f u + M * u)
      (Ioo p q) := hderiv
  apply convexOn_of_deriv2_nonneg (convex_Icc p q)
  · exact (continuousOn_const.mul hcont).add (by fun_prop)
  · rw [hint]
    exact (hd1.const_mul c).add (by fun_prop)
  · rw [hint]
    refine DifferentiableOn.congr ((hd2.const_mul c).add (by fun_prop)) heq
  · intro u hu
    rw [hint] at hu
    have hev : deriv (fun u => c * f u + M / 2 * u ^ 2) =ᶠ[nhds u]
        (fun u => c * deriv f u + M * u) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hu) heq
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    rw [hev.deriv_eq]
    have hdfu : DifferentiableAt ℝ (deriv f) u := hd2.differentiableAt (isOpen_Ioo.mem_nhds hu)
    have : HasDerivAt (fun u => c * deriv f u + M * u) (c * deriv (deriv f) u + M * 1) u :=
      (hdfu.hasDerivAt.const_mul c).add ((hasDerivAt_id u).const_mul M)
    rw [this.deriv]
    have hb := hM u hu
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at hb
    have : |c * deriv (deriv f) u| ≤ M := by
      rw [abs_mul]
      calc |c| * |deriv (deriv f) u| ≤ 1 * |deriv (deriv f) u| :=
            mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ ≤ M := by linarith
    have := neg_abs_le (c * deriv (deriv f) u)
    linarith

/-- Tangent line inequality for a convex function at an interior point of differentiability. -/
lemma convex_tangent {g : ℝ → ℝ} {p q x₀ x : ℝ} (hg : ConvexOn ℝ (Icc p q) g)
    (hx₀ : x₀ ∈ Ioo p q) (hx : x ∈ Icc p q) (hd : DifferentiableAt ℝ g x₀) :
    g x₀ + deriv g x₀ * (x - x₀) ≤ g x := by
  have hx₀' : x₀ ∈ Icc p q := Ioo_subset_Icc_self hx₀
  rcases lt_trichotomy x₀ x with h | h | h
  · have := hg.deriv_le_slope hx₀' hx h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hg.slope_le_deriv hx hx₀' h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- First-order Taylor bound at an interior point: `|f(x) - f(x₀) - f'(x₀)(x - x₀)| ≤ M (x-x₀)²/2`. -/
theorem taylor1_bound {f : ℝ → ℝ} {p q M : ℝ} (h : C2Bound f p q M) {x₀ x : ℝ}
    (hx₀ : x₀ ∈ Ioo p q) (hx : x ∈ Icc p q) :
    |f x - f x₀ - deriv f x₀ * (x - x₀)| ≤ M / 2 * (x - x₀) ^ 2 := by
  have hfd : DifferentiableAt ℝ f x₀ :=
    (h.2.1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx₀)
  have key : ∀ c : ℝ, |c| ≤ 1 → c * f x₀ + M / 2 * x₀ ^ 2 + (c * deriv f x₀ + M * x₀) * (x - x₀)
      ≤ c * f x + M / 2 * x ^ 2 := by
    intro c hc
    have hgd : DifferentiableAt ℝ (fun u => c * f u + M / 2 * u ^ 2) x₀ :=
      (hfd.const_mul c).add (by fun_prop)
    have hder : deriv (fun u => c * f u + M / 2 * u ^ 2) x₀ = c * deriv f x₀ + M * x₀ := by
      have : HasDerivAt (fun u => c * f u + M / 2 * u ^ 2) (c * deriv f x₀ + M / 2 * (2 * x₀))
          x₀ := by
        convert (hfd.hasDerivAt.const_mul c).add ((hasDerivAt_pow 2 x₀).const_mul (M / 2)) using 1
        simp
      rw [this.deriv]; ring
    have := convex_tangent (convex_aux h c hc) hx₀ hx hgd
    rw [hder] at this
    exact this
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  rw [abs_le]; constructor <;> nlinarith

/-- Linear interpolation error: if `P` is the affine interpolant of `f` at `p < q`, then
`|f(x) - P(x)| ≤ M (x - p)(q - x)/2` for `x ∈ [p, q]`. -/
theorem interp_error_bound {f : ℝ → ℝ} {p q M : ℝ} (hpq : p < q) (h : C2Bound f p q M) {x : ℝ}
    (hx : x ∈ Icc p q) :
    |f x - ((q - x) * f p + (x - p) * f q) / (q - p)| ≤ M / 2 * ((x - p) * (q - x)) := by
  have hqp : 0 < q - p := by linarith
  have key : ∀ c : ℝ, |c| ≤ 1 → c * f x + M / 2 * x ^ 2 ≤
      ((q - x) * (c * f p + M / 2 * p ^ 2) + (x - p) * (c * f q + M / 2 * q ^ 2)) / (q - p) := by
    intro c hc
    have hg := convex_aux h c hc
    have ha : 0 ≤ (q - x) / (q - p) := div_nonneg (by linarith [hx.2]) hqp.le
    have hb : 0 ≤ (x - p) / (q - p) := div_nonneg (by linarith [hx.1]) hqp.le
    have hab : (q - x) / (q - p) + (x - p) / (q - p) = 1 := by field_simp; ring
    have := hg.2 (left_mem_Icc.2 hpq.le) (right_mem_Icc.2 hpq.le) ha hb hab
    have hne : q - p ≠ 0 := hqp.ne'
    have hxe : (q - x) / (q - p) * p + (x - p) / (q - p) * q = x := by
      field_simp; ring
    simp only [smul_eq_mul] at this
    rw [hxe] at this
    rw [show ((q - x) * (c * f p + M / 2 * p ^ 2) + (x - p) * (c * f q + M / 2 * q ^ 2)) / (q - p)
      = (q - x) / (q - p) * (c * f p + M / 2 * p ^ 2) + (x - p) / (q - p) *
        (c * f q + M / 2 * q ^ 2) by field_simp]
    exact this
  have hne : q - p ≠ 0 := hqp.ne'
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  have e : ∀ c : ℝ, ((q - x) * (c * f p + M / 2 * p ^ 2) + (x - p) * (c * f q + M / 2 * q ^ 2)) /
      (q - p) = c * (((q - x) * f p + (x - p) * f q) / (q - p)) +
        M / 2 * (x ^ 2 + (x - p) * (q - x)) := by
    intro c; field_simp; ring
  rw [e] at h1 h2
  rw [abs_le]; constructor <;> nlinarith

lemma mul_le_sq_div_four (p q x : ℝ) : (x - p) * (q - x) ≤ (q - p) ^ 2 / 4 := by
  nlinarith [sq_nonneg (2 * x - p - q)]

/-- `C²` regularity on `[a,b]` (as `ContDiffOn` with a bound on the within-derivative) yields
`C2Bound` on every subinterval. -/
lemma C2Bound.of_contDiffOn {f : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f (Icc a b))
    (hM : ∀ x ∈ Icc a b, |iteratedDerivWithin 2 f (Icc a b) x| ≤ M) {p q : ℝ}
    (hp : a ≤ p) (hq : q ≤ b) : C2Bound f p q M := by
  refine ⟨hf.continuousOn.mono (Icc_subset_Icc hp hq), hf.mono (Ioo_subset_Icc_self.trans
    (Icc_subset_Icc hp hq)), fun u hu => ?_⟩
  have hu' : u ∈ Ioo a b := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hca : ContDiffAt ℝ 2 f u := hf.contDiffAt (Icc_mem_nhds hu'.1 hu'.2)
  have := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hca
    (Ioo_subset_Icc_self hu')
  rw [← iteratedDeriv_eq_iterate, ← this]
  exact hM u (Ioo_subset_Icc_self hu')

end Dyadic.Lib
