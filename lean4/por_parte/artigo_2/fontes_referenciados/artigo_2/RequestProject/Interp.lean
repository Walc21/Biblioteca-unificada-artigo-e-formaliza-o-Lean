import Mathlib

/-!
# Linear interpolation error and first-derivative control

* Proposition 2.3 (interpolation remainder): `‖f - P_J f‖_{∞,J} ≤ |J|^2/8 ‖f''‖_{∞,J}`.
* Matching lower bound when `f'' ≥ m > 0` (used in Sections 11–12).
* Lemma 3.9 (controle uniforme da primeira derivada).
-/

namespace Artigo

open Set

/-- the linear interpolant of `f` at the endpoints of `[a,b]` -/
noncomputable def linInterp (f : ℝ → ℝ) (a b : ℝ) (x : ℝ) : ℝ :=
  f a + (f b - f a) / (b - a) * (x - a)

lemma linInterp_left (f : ℝ → ℝ) {a b : ℝ} : linInterp f a b a = f a := by
  simp [linInterp]

lemma linInterp_right (f : ℝ → ℝ) {a b : ℝ} (h : a < b) : linInterp f a b b = f b := by
  simp only [linInterp]; field_simp [sub_ne_zero.mpr h.ne']; ring

/-- A function with nonnegative second derivative on `[a,b]`, nonpositive at the endpoints,
is nonpositive on `[a,b]`. -/
lemma nonpos_of_deriv2_nonneg {h h' h'' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x, HasDerivAt h (h' x) x) (hd2 : ∀ x, HasDerivAt h' (h'' x) x)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ h'' x) (ha : h a ≤ 0) (hb : h b ≤ 0) :
    ∀ x ∈ Icc a b, h x ≤ 0 := by
  have hder : deriv h = h' := funext fun x => (hd x).deriv
  have hder2 : deriv h' = h'' := funext fun x => (hd2 x).deriv
  have hconv : ConvexOn ℝ (Icc a b) h := by
    apply convexOn_of_deriv2_nonneg (convex_Icc a b)
    · exact (fun x _ => (hd x).continuousAt.continuousWithinAt)
    · exact (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    · rw [hder]; exact (fun x _ => (hd2 x).differentiableAt.differentiableWithinAt)
    · intro x hx
      rw [Function.iterate_succ, Function.iterate_one, Function.comp_apply, hder, hder2]
      exact hpos x (interior_subset hx)
  intro x hx
  rcases eq_or_lt_of_le hab with rfl | hlt
  · have : x = a := le_antisymm hx.2 hx.1
    rw [this]; exact ha
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hlt.ne'
  set θ := (x - a) / (b - a) with hθ
  have hxe : (1 - θ) * a + θ * b = x := by rw [hθ]; field_simp; ring
  have h0 : 0 ≤ θ := div_nonneg (by linarith [hx.1]) (by linarith)
  have h1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith [hx.2]
  have := hconv.2 (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
    (show 0 ≤ 1 - θ by linarith) h0 (show 1 - θ + θ = 1 by ring)
  simp only [smul_eq_mul] at this
  rw [hxe] at this
  nlinarith

/-- If `c ≤ f''` on `[a,b]` then `f x - P f x ≤ (c/2)(x-a)(x-b)` on `[a,b]`. -/
lemma interp_upper_of_lower {f f' f'' : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (h1 : ∀ x ∈ Icc a b, c ≤ f'' x) :
    ∀ x ∈ Icc a b, f x - linInterp f a b x ≤ c / 2 * ((x - a) * (x - b)) := by
  set B := (f b - f a) / (b - a)
  have hP : ∀ x, linInterp f a b x = f a + B * (x - a) := fun x => rfl
  have hup : ∀ x ∈ Icc a b, f x - linInterp f a b x - c / 2 * ((x - a) * (x - b)) ≤ 0 := by
    apply nonpos_of_deriv2_nonneg hab.le (h' := fun x => f' x - B - c / 2 * (2 * x - a - b))
      (h'' := fun x => f'' x - c)
    · intro x
      have := (((hd x).sub (((hasDerivAt_id x).sub_const a).const_mul B |>.const_add (f a))).sub
        ((((hasDerivAt_id x).sub_const a).mul ((hasDerivAt_id x).sub_const b)).const_mul (c / 2)))
      convert this using 1
      simp only [id]; ring
    · intro x
      have := ((hd2 x).sub_const B).sub ((((hasDerivAt_id x).const_mul 2).sub_const a |>.sub_const b).const_mul (c / 2))
      convert this using 1
      ring
    · intro x hx; linarith [h1 x hx]
    · simp [linInterp]
    · rw [linInterp_right f hab]; simp
  intro x hx; linarith [hup x hx]

/-- If `f'' ≤ c` on `[a,b]` then `(c/2)(x-a)(x-b) ≤ f x - P f x` on `[a,b]`. -/
lemma interp_lower_of_upper {f f' f'' : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (h2 : ∀ x ∈ Icc a b, f'' x ≤ c) :
    ∀ x ∈ Icc a b, c / 2 * ((x - a) * (x - b)) ≤ f x - linInterp f a b x := by
  have hd' : ∀ x, HasDerivAt (fun y => -f y) (-f' x) x := fun x => (hd x).neg
  have hd2' : ∀ x, HasDerivAt (fun y => -f' y) (-f'' x) x := fun x => (hd2 x).neg
  have := interp_upper_of_lower (c := -c) hab hd' hd2' (fun x hx => by linarith [h2 x hx])
  intro x hx
  have h := this x hx
  simp only [linInterp] at h ⊢
  have e : -f x - (-f a + (-f b - -f a) / (b - a) * (x - a)) =
      -(f x - (f a + (f b - f a) / (b - a) * (x - a))) := by ring
  rw [e] at h
  linarith

/-- **Two-sided interpolation estimate**: if `c₁ ≤ f'' ≤ c₂` on `[a,b]`, then on `[a,b]`
`(c₂/2)(x-a)(x-b) ≤ f x - P f x ≤ (c₁/2)(x-a)(x-b)`. -/
lemma interp_two_sided {f f' f'' : ℝ → ℝ} {a b c₁ c₂ : ℝ} (hab : a < b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (h1 : ∀ x ∈ Icc a b, c₁ ≤ f'' x) (h2 : ∀ x ∈ Icc a b, f'' x ≤ c₂) :
    ∀ x ∈ Icc a b, c₂ / 2 * ((x - a) * (x - b)) ≤ f x - linInterp f a b x ∧
      f x - linInterp f a b x ≤ c₁ / 2 * ((x - a) * (x - b)) :=
  fun x hx => ⟨interp_lower_of_upper hab hd hd2 h2 x hx, interp_upper_of_lower hab hd hd2 h1 x hx⟩

lemma prod_bound {a b x : ℝ} (hx : x ∈ Icc a b) :
    0 ≤ (x - a) * (b - x) ∧ (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
  constructor
  · exact mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  · nlinarith [sq_nonneg (2 * x - a - b)]

/-- **Proposition 2.3 (interpolation remainder)**: if `|f''| ≤ M` on `J = [a,b]` then
`|f - P_J f| ≤ |J|^2/8 · M` on `J`. -/
theorem interp_remainder {f f' f'' : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc a b, |f'' x| ≤ M) :
    ∀ x ∈ Icc a b, |f x - linInterp f a b x| ≤ (b - a) ^ 2 / 8 * M := by
  intro x hx
  have h := interp_two_sided hab hd hd2 (c₁ := -M) (c₂ := M)
    (fun y hy => by linarith [abs_le.mp (hM y hy)]) (fun y hy => by linarith [abs_le.mp (hM y hy)]) x hx
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a (left_mem_Icc.mpr hab.le))
  obtain ⟨p0, p1⟩ := prod_bound hx
  rw [abs_le]
  constructor <;> nlinarith

/-- version for `C²` functions on `ℝ` -/
theorem interp_remainder_C2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ} (hab : a < b)
    (hM : ∀ x ∈ Icc a b, |deriv (deriv f) x| ≤ M) :
    ∀ x ∈ Icc a b, |f x - linInterp f a b x| ≤ (b - a) ^ 2 / 8 * M := by
  have h1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv f) := by
    have : ContDiff ℝ 1 (deriv f) := hf.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  exact interp_remainder hab (fun x => (h1 x).hasDerivAt) (fun x => (h2 x).hasDerivAt) hM

/-- **Lower bound** (used in Sections 11–12): if `f'' ≥ m` on `[a,b]` then at the midpoint
`P f - f ≥ m |J|^2 / 8`. -/
theorem interp_mid_lower {f f' f'' : ℝ → ℝ} {a b m : ℝ} (hab : a < b)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hm : ∀ x ∈ Icc a b, m ≤ f'' x) :
    m * (b - a) ^ 2 / 8 ≤ linInterp f a b ((a + b) / 2) - f ((a + b) / 2) := by
  have hmid : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have := interp_upper_of_lower hab hd hd2 hm _ hmid
  have e : ((a + b) / 2 - a) * ((a + b) / 2 - b) = -((b - a) ^ 2 / 4) := by ring
  rw [e] at this
  linarith

/-! ## Taylor bound and Lemma 3.9 -/

/-- first-order Taylor bound: if `|f''| ≤ M` on `[lo,hi]` then
`|f t - f x - f'(x)(t-x)| ≤ M/2 (t-x)^2` for `x, t ∈ [lo,hi]`. -/
lemma taylor1_bound {f f' f'' : ℝ → ℝ} {lo hi M : ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc lo hi, |f'' x| ≤ M) {x t : ℝ} (hx : x ∈ Icc lo hi) (ht : t ∈ Icc lo hi) :
    |f t - f x - f' x * (t - x)| ≤ M / 2 * (t - x) ^ 2 := by
  -- g(s) = ± (f s - f x - f' x (s - x)) - M/2 (s-x)^2 has g(x) = 0, g'(x) = 0, g'' ≤ 0
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      σ * (f t - f x - f' x * (t - x)) - M / 2 * (t - x) ^ 2 ≤ 0 := by
    intro σ hσ
    have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    set g : ℝ → ℝ := fun s => σ * (f s - f x - f' x * (s - x)) - M / 2 * (s - x) ^ 2
    set g' : ℝ → ℝ := fun s => σ * (f' s - f' x) - M * (s - x)
    have hg : ∀ s, HasDerivAt g (g' s) s := by
      intro s
      have := ((((hd s).sub_const (f x)).sub (((hasDerivAt_id s).sub_const x).const_mul (f' x))).const_mul σ).sub
        ((((hasDerivAt_id s).sub_const x).pow 2).const_mul (M / 2))
      convert this using 1
      simp [g']; ring
    have hg' : ∀ s, HasDerivAt g' (σ * f'' s - M) s := by
      intro s
      have := (((hd2 s).sub_const (f' x)).const_mul σ).sub (((hasDerivAt_id s).sub_const x).const_mul M)
      convert this using 1; simp
    have hg'' : ∀ s ∈ Icc lo hi, σ * f'' s - M ≤ 0 := by
      intro s hs
      have := abs_le.mp (hM s hs)
      rcases hσ with rfl | rfl <;> linarith
    have hgx : g x = 0 := by simp [g]
    have hg'x : g' x = 0 := by simp [g']
    -- g' antitone on [lo,hi]
    have hanti : AntitoneOn g' (Icc lo hi) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc lo hi)
      · exact fun s _ => (hg' s).continuousAt.continuousWithinAt
      · exact fun s _ => (hg' s).differentiableAt.differentiableWithinAt
      · intro s hs; rw [(hg' s).deriv]; exact hg'' s (interior_subset hs)
    have : g t ≤ 0 := by
      rcases le_total x t with hxt | htx
      · -- on [x,t], g' ≤ 0, so g antitone
        have hsub : Icc x t ⊆ Icc lo hi := Icc_subset_Icc hx.1 ht.2
        have hanti2 : AntitoneOn g (Icc x t) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc x t)
          · exact fun s _ => (hg s).continuousAt.continuousWithinAt
          · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
          · intro s hs
            rw [(hg s).deriv]
            have hs' := interior_subset hs
            have := hanti (hsub (left_mem_Icc.mpr hxt)) (hsub hs') hs'.1
            linarith
        have := hanti2 (left_mem_Icc.mpr hxt) (right_mem_Icc.mpr hxt) hxt
        linarith
      · have hsub : Icc t x ⊆ Icc lo hi := Icc_subset_Icc ht.1 hx.2
        have hmono : MonotoneOn g (Icc t x) := by
          apply monotoneOn_of_deriv_nonneg (convex_Icc t x)
          · exact fun s _ => (hg s).continuousAt.continuousWithinAt
          · exact fun s _ => (hg s).differentiableAt.differentiableWithinAt
          · intro s hs
            rw [(hg s).deriv]
            have hs' := interior_subset hs
            have := hanti (hsub hs') (hsub (right_mem_Icc.mpr htx)) hs'.2
            linarith
        have := hmono (left_mem_Icc.mpr htx) (right_mem_Icc.mpr htx) htx
        linarith
    exact this
  have k1 := key 1 (Or.inl rfl)
  have k2 := key (-1) (Or.inr rfl)
  rw [abs_le]; constructor <;> linarith

/-- the class `𝓕_{R,M}`: `C²` functions (on `ℝ`, as a convenient representative of
`C²[0,1]`) with `‖f‖_∞ ≤ R` and `‖f''‖_∞ ≤ M` on `[0,1]`. -/
def FRM (R M : ℝ) : Set (ℝ → ℝ) :=
  {f | ContDiff ℝ 2 f ∧ (∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ R) ∧ ∀ x ∈ Icc (0 : ℝ) 1, |deriv (deriv f) x| ≤ M}

lemma FRM_hasDeriv {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) :
    (∀ x, HasDerivAt f (deriv f x) x) ∧ ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x := by
  have h1 : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv f) := by
    have : ContDiff ℝ 1 (deriv f) := hf.1.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  exact ⟨fun x => (h1 x).hasDerivAt, fun x => (h2 x).hasDerivAt⟩

/-- **Lemma 3.9 (controle uniforme da primeira derivada)**: for `f ∈ 𝓕_{R,M}`,
`‖f'‖_∞ ≤ C₀ := 4R + M/2` on `[0,1]`. -/
theorem derivative_control {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) :
    ∀ x ∈ Icc (0 : ℝ) 1, |deriv f x| ≤ 4 * R + M / 2 := by
  intro x hx
  obtain ⟨hd, hd2⟩ := FRM_hasDeriv hf
  have hR := hf.2.1
  have hM := hf.2.2
  -- choose a ∈ {0,1} with |a - x| ≥ 1/2
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ |a - x| ∧ |a - x| ≤ 1 := by
    rcases le_total x (1 / 2) with h | h
    · refine ⟨1, ⟨by norm_num, le_refl _⟩, ?_, ?_⟩ <;> rw [abs_of_nonneg (by linarith [hx.2])] <;>
        linarith [hx.1]
    · refine ⟨0, ⟨le_refl _, by norm_num⟩, ?_, ?_⟩ <;> rw [abs_of_nonpos (by linarith [hx.1])] <;>
        linarith [hx.2]
  have ht := taylor1_bound hd hd2 hM hx ha
  have hpos : 0 < |a - x| := by linarith [hax.1]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x hx)
  have hfa := hR a ha
  have hfx := hR x hx
  -- |f'(x)| |a-x| ≤ |f a| + |f x| + M/2 (a-x)^2
  have h1 : |deriv f x| * |a - x| ≤ |f a| + |f x| + M / 2 * (a - x) ^ 2 := by
    rw [← abs_mul]
    have e : deriv f x * (a - x) = (f a - f x) - (f a - f x - deriv f x * (a - x)) := by ring
    rw [e]
    calc |(f a - f x) - (f a - f x - deriv f x * (a - x))|
        ≤ |f a - f x| + |f a - f x - deriv f x * (a - x)| := abs_sub _ _
      _ ≤ (|f a| + |f x|) + M / 2 * (a - x) ^ 2 := by
          gcongr
          exact abs_sub _ _
  have hsq : (a - x) ^ 2 = |a - x| * |a - x| := by rw [← sq, sq_abs]
  rw [hsq] at h1
  have h2 : |deriv f x| ≤ (|f a| + |f x|) / |a - x| + M / 2 * |a - x| := by
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]; nlinarith
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hfx
  have h3 : (|f a| + |f x|) / |a - x| ≤ 4 * R := by
    rw [div_le_iff₀ hpos]; nlinarith [mul_le_mul_of_nonneg_left hax.1 hR0]
  nlinarith

end Artigo
