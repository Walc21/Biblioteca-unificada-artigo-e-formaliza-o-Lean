module
public import RequestProject.Extension

/-!
# Section 5: uniform rates and the asymptotic constant

Theorem 5.1 (sharp bound (31), limit (32), assemblies (33)), Corollary 5.2 and estimate (35).
-/

@[expose] public section

namespace Fase3

open Set Filter Topology

/-! ## The one-cell interpolation error -/

/-- If `G'' ≥ c` on `[a,b]` then `G - P G ≤ -(c/2)(x-a)(b-x)` there, where `P G` is the
linear interpolant at `a`, `b` (convexity argument). -/
lemma interp_err_upper {a b : ℝ} (hab : a < b) {G G1 G2 : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (G1 x) x) (hG1 : ∀ x, HasDerivAt G1 (G2 x) x) {c : ℝ}
    (hc : ∀ x ∈ Icc a b, c ≤ G2 x) {x : ℝ} (hx : x ∈ Icc a b) :
    G x - linInterp a b (G a) (G b) x ≤ -(c / 2) * ((x - a) * (b - x)) := by
  set s := (G b - G a) / (b - a)
  set φ : ℝ → ℝ := fun t => G t - (G a + s * (t - a)) + c / 2 * ((t - a) * (b - t))
  set φ1 : ℝ → ℝ := fun t => G1 t - s + c / 2 * (a + b - 2 * t)
  have hφ : ∀ t, HasDerivAt φ (φ1 t) t := by
    intro t
    have := ((hG t).sub ((((hasDerivAt_id t).sub_const a).const_mul s).const_add (G a))).add
      ((((hasDerivAt_id t).sub_const a).mul ((hasDerivAt_id t).const_sub b)).const_mul (c / 2))
    convert this using 1
    simp only [φ1, id]; ring
  have hφ1 : ∀ t, HasDerivAt φ1 (G2 t - c) t := by
    intro t
    have := ((hG1 t).sub_const s).add
      ((((hasDerivAt_id t).const_mul 2).const_sub (a + b)).const_mul (c / 2))
    convert this using 1
    ring
  have hdφ : deriv φ = φ1 := funext fun t => (hφ t).deriv
  have hconv : ConvexOn ℝ (Icc a b) φ := by
    apply convexOn_of_deriv2_nonneg (convex_Icc a b)
    · exact fun t _ => (hφ t).continuousAt.continuousWithinAt
    · exact fun t _ => (hφ t).differentiableAt.differentiableWithinAt
    · rw [hdφ]; exact fun t _ => (hφ1 t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, hdφ]
      rw [(hφ1 t).deriv]
      linarith [hc t (Ioo_subset_Icc_self ht)]
  have ha : φ a = 0 := by simp [φ]
  have hb : φ b = 0 := by simp only [φ, s]; field_simp [sub_ne_zero.2 hab.ne']; ring
  have := hconv.le_on_segment (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
    (by rw [segment_eq_Icc hab.le]; exact hx)
  rw [ha, hb, max_self] at this
  simp only [φ] at this
  unfold linInterp
  linarith

/-- If `G'' ≤ C` on `[a,b]` then `G - P G ≥ -(C/2)(x-a)(b-x)` there. -/
lemma interp_err_lower {a b : ℝ} (hab : a < b) {G G1 G2 : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (G1 x) x) (hG1 : ∀ x, HasDerivAt G1 (G2 x) x) {C : ℝ}
    (hC : ∀ x ∈ Icc a b, G2 x ≤ C) {x : ℝ} (hx : x ∈ Icc a b) :
    -(C / 2) * ((x - a) * (b - x)) ≤ G x - linInterp a b (G a) (G b) x := by
  have := interp_err_upper hab (G := fun t => -G t) (G1 := fun t => -G1 t) (G2 := fun t => -G2 t)
    (fun t => (hG t).neg) (fun t => (hG1 t).neg) (c := -C) (fun t ht => by linarith [hC t ht]) hx
  simp only at this
  unfold linInterp at this ⊢
  have e : (-G b - -G a) / (b - a) * (x - a) = -((G b - G a) / (b - a) * (x - a)) := by ring
  linarith

lemma quad_le {a b x : ℝ} (hx : x ∈ Icc a b) : 0 ≤ (x - a) * (b - x) ∧
    (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 :=
  ⟨mul_nonneg (by linarith [hx.1]) (by linarith [hx.2]), by nlinarith [sq_nonneg (2 * x - a - b)]⟩

/-- `|G - P G| ≤ (b-a)² M / 8` on `[a, b]` when `|G''| ≤ M` there. -/
lemma abs_interp_err_le {a b : ℝ} (hab : a < b) {G G1 G2 : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (G1 x) x) (hG1 : ∀ x, HasDerivAt G1 (G2 x) x) {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |G2 x| ≤ M) {x : ℝ} (hx : x ∈ Icc a b) :
    |G x - linInterp a b (G a) (G b) x| ≤ (b - a) ^ 2 * M / 8 := by
  have h1 := interp_err_upper hab hG hG1 (c := -M) (fun t ht => (abs_le.1 (hM t ht)).1) hx
  have h2 := interp_err_lower hab hG hG1 (C := M) (fun t ht => (abs_le.1 (hM t ht)).2) hx
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x hx)
  obtain ⟨q0, q1⟩ := quad_le hx
  rw [abs_le]; constructor <;> nlinarith

/-! ## The uniform interpolant `P_k` -/

/-- Mesh size `h = 2^{-k}`. -/
noncomputable def mesh (k : ℕ) : ℝ := (2 ^ k)⁻¹

lemma mesh_pos (k : ℕ) : 0 < mesh k := by unfold mesh; positivity

/-- The interpolant `P_k w` of `w` at the nodes `j 2^{-k}`. -/
noncomputable def interpP (k : ℕ) (w : ℝ → ℝ) (x : ℝ) : ℝ := lin (k, ⌊2 ^ k * x⌋) w x

lemma mem_cell_floor (k : ℕ) (x : ℝ) : x ∈ cC (k, ⌊2 ^ k * x⌋) :=
  Ico_subset_Icc_self ((mem_cellOwn_iff k _ x).2 rfl)

lemma interpP_eq_lin {k : ℕ} {j : ℤ} (w : ℝ → ℝ) {x : ℝ} (hx : x ∈ cC (k, j)) :
    interpP k w x = lin (k, j) w x := by
  unfold interpP
  have hxi := mem_cell_floor k x
  set i := ⌊2 ^ k * x⌋
  clear_value i
  by_cases h : i = j
  · rw [h]
  have hdisj : Disjoint (Ioo (cL (k, i)) (cR (k, i))) (Ioo (cL (k, j)) (cR (k, j))) :=
    uniformCover_disjoint_aux k h
  rcases common_point_endpoint hdisj hxi hx with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, lin_right, ← e1, e2, lin_left]
  · rw [e1, lin_left, ← e1, e2, lin_right]
where
  uniformCover_disjoint_aux (k : ℕ) {i j : ℤ} (h : i ≠ j) :
      Disjoint (Ioo (cL (k, i)) (cR (k, i))) (Ioo (cL (k, j)) (cR (k, j))) := by
    rw [Set.disjoint_left]
    rintro x ⟨h1, h2⟩ ⟨h1', h2'⟩
    simp only [cL, cR, cellL, cellR] at h1 h2 h1' h2'
    rw [div_lt_iff₀ (by positivity)] at h1 h1'
    rw [lt_div_iff₀ (by positivity)] at h2 h2'
    have a1 : (i : ℝ) < j + 1 := by linarith
    have a2 : (j : ℝ) < i + 1 := by linarith
    have b1 : i < j + 1 := by exact_mod_cast a1
    have b2 : j < i + 1 := by exact_mod_cast a2
    omega

lemma cell_width (J : ℕ × ℤ) : cR J - cL J = mesh J.1 := by
  simp only [cR, cL]; rw [cellR_sub_cellL, mesh, one_div]

section
variable {f : ℝ → ℝ} {α β : ℝ}

/-- The uniform error `‖f - P_k F‖_{∞,[α,β]}`. -/
noncomputable def errP (f : ℝ → ℝ) (α β : ℝ) (k : ℕ) : ℝ :=
  supNormOn (Icc α β) (fun x => f x - interpP k (extF f α β) x)

lemma pointwise_err_le (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (k : ℕ) (x : ℝ) :
    |extF f α β x - interpP k (extF f α β) x| ≤ mesh k ^ 2 * normD2 f α β / 8 := by
  have hx := mem_cell_floor k x
  rw [interpP_eq_lin _ hx]
  have := abs_interp_err_le (cellL_lt_cellR _ _) (hasDerivAt_extF hαβ hf) (hasDerivAt_extF1 hαβ hf)
    (M := normD2 f α β) (fun t _ => abs_extF2_le hαβ hf t) hx
  have hw := cell_width (k, ⌊2 ^ k * x⌋)
  simp only [cR, cL] at hw
  rw [hw] at this
  exact this

/-- **Theorem 5.1, equation (31).** `‖f - P_k F‖_{∞,[α,β]} ≤ h² M / 8`. -/
theorem errP_le (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (k : ℕ) :
    errP f α β k ≤ mesh k ^ 2 * normD2 f α β / 8 := by
  refine supNormOn_le ⟨α, le_rfl, hαβ.le⟩ ?_
  intro x hx
  have := pointwise_err_le hαβ hf k x
  rwa [extF_of_mem hx] at this

lemma abs_err_le_errP (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc α β) : |f x - interpP k (extF f α β) x| ≤ errP f α β k := by
  apply le_supNormOn (c := mesh k ^ 2 * normD2 f α β / 8) _ hx
  intro y hy
  have := pointwise_err_le hαβ hf k y
  rwa [extF_of_mem hy] at this

lemma errP_nonneg (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (k : ℕ) : 0 ≤ errP f α β k :=
  le_trans (abs_nonneg _) (abs_err_le_errP hαβ hf k ⟨le_rfl, hαβ.le⟩)

lemma exists_max_d2 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    ∃ xs ∈ Icc α β, |d2 f α β xs| = normD2 f α β := by
  obtain ⟨xs, hxs, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨α, le_rfl, hαβ.le⟩
    (continuousOn_d2 hαβ hf).abs
  refine ⟨xs, hxs, le_antisymm (abs_d2_le hαβ hf hxs) ?_⟩
  unfold normD2 supNormOn
  refine csSup_le ⟨|d2 f α β α|, α, ⟨le_rfl, hαβ.le⟩, rfl⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hmax hy

lemma tendsto_mesh : Tendsto mesh atTop (𝓝 0) := by
  have : mesh = fun k => (1 / 2 : ℝ) ^ k := funext fun k => by simp [mesh]
  rw [this]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- A whole cell of scale `k` fits in `[u, v]` once `2 h ≤ v - u`. -/
lemma exists_cell_in {u v : ℝ} {k : ℕ} (h : 2 * mesh k ≤ v - u) :
    ∃ j : ℤ, u ≤ cL (k, j) ∧ cR (k, j) ≤ v := by
  refine ⟨⌈u * 2 ^ k⌉, ?_, ?_⟩
  · simp only [cL, cellL]
    rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _
  · have hw := cell_width (k, ⌈u * 2 ^ k⌉)
    have hL : cL (k, ⌈u * 2 ^ k⌉) < u + mesh k := by
      simp only [cL, cellL, mesh]
      rw [div_lt_iff₀ (by positivity), add_mul, inv_mul_cancel₀ (by positivity)]
      exact Int.ceil_lt_add_one _
    simp only at hw
    linarith

/-- The lower bound behind (32): for every `η > 0`, eventually
`(8/h²)‖f - P_k F‖ ≥ M - η`. -/
lemma eventually_errP_ge (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, normD2 f α β - η ≤ 8 / mesh k ^ 2 * errP f α β k := by
  obtain ⟨xs, hxs, hmax⟩ := exists_max_d2 hαβ hf
  set M := normD2 f α β
  have hcont := (continuous_extF2 hαβ hf).continuousAt (x := xs)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδc⟩ := hcont η hη
  have hF2xs : extF2 f α β xs = d2 f α β xs := by rw [extF2_eq_comp hαβ, clamp_of_mem hxs]
  set u := max α (xs - δ / 2)
  set v := min β (xs + δ / 2)
  have huv : u < v := by
    simp only [u, v, max_lt_iff, lt_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hxs.1, hxs.2]
  have hev : ∀ᶠ k in atTop, 2 * mesh k ≤ v - u := by
    have := tendsto_mesh.eventually (gt_mem_nhds (show (0 : ℝ) < (v - u) / 2 by linarith))
    filter_upwards [this] with k hk; linarith
  filter_upwards [hev] with k hk
  obtain ⟨j, hj1, hj2⟩ := exists_cell_in hk
  set J : ℕ × ℤ := (k, j)
  have hJsub : ∀ y ∈ cC J, y ∈ Icc u v := fun y hy => ⟨le_trans hj1 hy.1, le_trans hy.2 hj2⟩
  have hnear : ∀ y ∈ cC J, |extF2 f α β y - extF2 f α β xs| < η := by
    intro y hy
    have hy' := hJsub y hy
    have h1 : u ≤ y := hy'.1
    have h2 : y ≤ v := hy'.2
    have h3 : xs - δ / 2 ≤ u := le_max_right _ _
    have h4 : v ≤ xs + δ / 2 := min_le_right _ _
    have := hδc (x := y) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  set z := (cL J + cR J) / 2
  have hlt : cL J < cR J := cellL_lt_cellR J.1 J.2
  have hz : z ∈ cC J := by
    show cL J ≤ z ∧ z ≤ cR J
    constructor <;> simp only [z] <;> linarith
  have hzI : z ∈ Icc α β := by
    have := hJsub z hz
    exact ⟨le_trans (le_max_left _ _) this.1, le_trans this.2 (min_le_left _ _)⟩
  have hw := cell_width J
  have hq : (z - cL J) * (cR J - z) = mesh k ^ 2 / 4 := by
    simp only [z]; rw [show mesh k = cR J - cL J from hw.symm]; ring
  have hle := abs_err_le_errP hαβ hf k hzI
  rw [interpP_eq_lin _ hz, ← extF_of_mem (f := f) hzI] at hle
  have hm2 : 0 < mesh k ^ 2 := by have := mesh_pos k; positivity
  have key : (M - η) * mesh k ^ 2 / 8 ≤ |extF f α β z - lin J (extF f α β) z| := by
    rcases abs_eq (normD2_nonneg hαβ hf) |>.1 hmax with hpos | hneg
    · have hc : ∀ y ∈ cC J, M - η ≤ extF2 f α β y := by
        intro y hy
        have := hnear y hy
        rw [hF2xs, hpos] at this
        linarith [(abs_lt.1 this).1]
      have := interp_err_upper (cellL_lt_cellR J.1 J.2) (hasDerivAt_extF hαβ hf)
        (hasDerivAt_extF1 hαβ hf) hc hz
      rw [hq] at this
      unfold lin
      rw [abs_sub_comm]
      refine le_trans ?_ (le_abs_self _)
      linarith
    · have hc : ∀ y ∈ cC J, extF2 f α β y ≤ -(M - η) := by
        intro y hy
        have := hnear y hy
        rw [hF2xs, hneg] at this
        linarith [(abs_lt.1 this).2]
      have := interp_err_lower (cellL_lt_cellR J.1 J.2) (hasDerivAt_extF hαβ hf)
        (hasDerivAt_extF1 hαβ hf) hc hz
      rw [hq] at this
      unfold lin
      refine le_trans ?_ (le_abs_self _)
      nlinarith
  have := le_trans key hle
  rw [div_mul_eq_mul_div, le_div_iff₀ hm2]
  nlinarith

/-- **Theorem 5.1, equation (32).** `(8/h²) ‖f - P_k F‖_{∞,[α,β]} → M` as `k → ∞`. -/
theorem tendsto_errP (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    Tendsto (fun k => 8 / mesh k ^ 2 * errP f α β k) atTop (𝓝 (normD2 f α β)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [eventually_errP_ge hαβ hf (show 0 < (normD2 f α β - a) / 2 by linarith)]
      with k hk
    linarith
  · intro a ha
    refine Eventually.of_forall fun k => lt_of_le_of_lt ?_ ha
    have := errP_le hαβ hf k
    have hm2 : 0 < mesh k ^ 2 := by have := mesh_pos k; positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hm2]
    linarith

/-- An assembly uniformly within `δ` of `P_k F` on `[α, β]`. -/
lemma exists_assembly_near_interpP (hαβ : α < β) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g, IsAssembly α β g ∧ ∀ x ∈ Icc α β, |g x - interpP k (extF f α β) x| < δ := by
  obtain ⟨g, hg, hclose⟩ := exists_assembly_near (uniformCover_disjoint α β k)
    (uniformCover_cover hαβ k) (extF f α β) hδ
  refine ⟨g, hg, fun x hx => ?_⟩
  have hxU := uniformCover_cover hαβ k hx
  simp only [mem_iUnion] at hxU
  obtain ⟨J, hJ, hxJ⟩ := hxU
  have hk : J.1 = k := by
    simp only [uniformCover, Finset.mem_image] at hJ
    obtain ⟨j, -, rfl⟩ := hJ; rfl
  have := hclose x hx
  rw [cellInterp_eq (uniformCover_disjoint α β k) _ hJ hxJ] at this
  obtain ⟨k', j⟩ := J
  simp only at hk; subst hk
  rwa [interpP_eq_lin _ hxJ]

/-- **Theorem 5.1, equation (33).** For every `δ > 0` there is `g_{k,δ} ∈ 𝒜([α,β])` with
`‖f - g_{k,δ}‖_∞ ≤ h² M / 8 + δ`. -/
theorem exists_assembly_rate (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) : ∃ g, IsAssembly α β g ∧
      supNormOn (Icc α β) (fun x => f x - g x) ≤ mesh k ^ 2 * normD2 f α β / 8 + δ := by
  obtain ⟨g, hg, hclose⟩ := exists_assembly_near_interpP (f := f) hαβ k hδ
  refine ⟨g, hg, supNormOn_le ⟨α, le_rfl, hαβ.le⟩ fun x hx => ?_⟩
  have h1 := abs_err_le_errP hαβ hf k hx
  have h2 := errP_le hαβ hf k
  have h3 := hclose x hx
  calc |f x - g x| = |(f x - interpP k (extF f α β) x) - (g x - interpP k (extF f α β) x)| := by
        ring_nf
    _ ≤ |f x - interpP k (extF f α β) x| + |g x - interpP k (extF f α β) x| := abs_sub _ _
    _ ≤ _ := by linarith

/-- **Corollary 5.2 (preservation of the constant).** There are assemblies `g_k ∈ 𝒜([α,β])`
with `(8/h²) ‖f - g_k‖_∞ → M`. -/
theorem exists_assembly_seq_constant (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    ∃ g : ℕ → ℝ → ℝ, (∀ k, IsAssembly α β (g k)) ∧
      Tendsto (fun k => 8 / mesh k ^ 2 * supNormOn (Icc α β) (fun x => f x - g k x)) atTop
        (𝓝 (normD2 f α β)) := by
  have hex : ∀ k, ∃ g, IsAssembly α β g ∧
      ∀ x ∈ Icc α β, |g x - interpP k (extF f α β) x| < mesh k ^ 3 :=
    fun k => exists_assembly_near_interpP hαβ k (by have := mesh_pos k; positivity)
  choose g hg hclose using hex
  refine ⟨g, hg, ?_⟩
  set eg := fun k => supNormOn (Icc α β) (fun x => f x - g k x)
  have hne : (Icc α β).Nonempty := ⟨α, le_rfl, hαβ.le⟩
  have hup : ∀ k, eg k ≤ errP f α β k + mesh k ^ 3 := by
    intro k
    apply supNormOn_le hne
    intro x hx
    have h1 := abs_err_le_errP hαβ hf k hx
    have h3 := hclose k x hx
    calc |f x - g k x| = |(f x - interpP k (extF f α β) x) - (g k x - interpP k (extF f α β) x)| := by
          ring_nf
      _ ≤ |f x - interpP k (extF f α β) x| + |g k x - interpP k (extF f α β) x| := abs_sub _ _
      _ ≤ _ := by linarith
  have hlo : ∀ k, errP f α β k ≤ eg k + mesh k ^ 3 := by
    intro k
    apply supNormOn_le hne
    intro x hx
    have h1 : |f x - g k x| ≤ eg k := le_supNormOn (c := errP f α β k + mesh k ^ 3)
      (fun y hy => by
        have h1 := abs_err_le_errP hαβ hf k hy
        have h3 := hclose k y hy
        calc |f y - g k y| = |(f y - interpP k (extF f α β) y) - (g k y - interpP k (extF f α β) y)| := by
              ring_nf
          _ ≤ |f y - interpP k (extF f α β) y| + |g k y - interpP k (extF f α β) y| := abs_sub _ _
          _ ≤ _ := by linarith) hx
    have h3 := hclose k x hx
    calc |f x - interpP k (extF f α β) x| = |(f x - g k x) + (g k x - interpP k (extF f α β) x)| := by
          ring_nf
      _ ≤ |f x - g k x| + |g k x - interpP k (extF f α β) x| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hdiff : Tendsto (fun k => 8 / mesh k ^ 2 * eg k - 8 / mesh k ^ 2 * errP f α β k) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun k => 8 * mesh k)
    · intro k
      have hm := mesh_pos k
      have hm2 : 0 < mesh k ^ 2 := by positivity
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
      have : |eg k - errP f α β k| ≤ mesh k ^ 3 := by
        rw [abs_le]; constructor <;> linarith [hup k, hlo k]
      calc 8 / mesh k ^ 2 * |eg k - errP f α β k| ≤ 8 / mesh k ^ 2 * mesh k ^ 3 :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 8 * mesh k := by field_simp
    · simpa using tendsto_mesh.const_mul 8
  have := (tendsto_errP hαβ hf).add hdiff
  simp only [add_sub_cancel, add_zero] at this
  exact this

/-- **Equation (35).** With `N_k` from (23),
`‖f - P_k F‖_∞ ≤ (β-α)² M / 8 · N_k^{-2} (1 + O(N_k^{-1}))`. -/
theorem errP_le_numCells (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    ∃ C : ℝ, ∀ k, errP f α β k ≤
      (β - α) ^ 2 * normD2 f α β / 8 * ((numCells α β k : ℝ)⁻¹) ^ 2 * (1 + C / numCells α β k) := by
  set C' := 1 + 2 / (β - α)
  refine ⟨4 * C' + 4 * C' ^ 2, fun k => ?_⟩
  have hM := normD2_nonneg hαβ hf
  obtain ⟨hN1, hN2⟩ := numCells_bounds α β k
  set N : ℝ := (numCells α β k : ℝ)
  have hba : 0 < β - α := by linarith
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hm : mesh k * 2 ^ k = 1 := by simp [mesh]
  have hmpos := mesh_pos k
  have hm1 : mesh k ≤ 1 := by unfold mesh; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN1
  have hN1' : β - α ≤ mesh k * N := by
    have := mul_le_mul_of_nonneg_left hN1 hmpos.le
    nlinarith
  have hN2' : mesh k * N < β - α + 2 * mesh k := by
    have := mul_lt_mul_of_pos_left hN2 hmpos
    nlinarith
  have hN1'' : 1 ≤ N := by
    have : (0 : ℤ) < numCells α β k := Int.cast_pos.1 hNpos
    have h1 : (1 : ℤ) ≤ numCells α β k := this
    show (1 : ℝ) ≤ ((numCells α β k : ℤ) : ℝ)
    exact_mod_cast h1
  have hC'pos : 0 < C' := by positivity
  have hmN : mesh k * N ≤ C' * (β - α) := by
    simp only [C']; rw [add_mul, div_mul_cancel₀ _ hba.ne']; nlinarith
  have hh : mesh k ≤ (β - α) / N * (1 + 2 * C' / N) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hNpos]
    have : mesh k * N < (β - α) + 2 * mesh k := hN2'
    have h2 : 2 * mesh k ≤ (β - α) * (2 * C' / N) := by
      rw [mul_div_assoc', le_div_iff₀ hNpos]; nlinarith
    nlinarith
  have hh2 : mesh k ^ 2 ≤ ((β - α) / N) ^ 2 * (1 + (4 * C' + 4 * C' ^ 2) / N) := by
    have h0 : 0 ≤ mesh k := hmpos.le
    have hsq : mesh k ^ 2 ≤ ((β - α) / N * (1 + 2 * C' / N)) ^ 2 := pow_le_pow_left₀ h0 hh 2
    refine le_trans hsq ?_
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hNinv : 1 / N ≤ 1 := by rw [div_le_one hNpos]; exact hN1''
    have : (1 + 2 * C' / N) ^ 2 = 1 + 4 * C' / N + 4 * C' ^ 2 * (1 / N) * (1 / N) := by
      field_simp; ring
    rw [this]
    have h3 : 4 * C' ^ 2 * (1 / N) * (1 / N) ≤ 4 * C' ^ 2 * (1 / N) := by
      have : 0 ≤ 4 * C' ^ 2 * (1 / N) := by positivity
      nlinarith
    have : (4 * C' + 4 * C' ^ 2) / N = 4 * C' / N + 4 * C' ^ 2 * (1 / N) := by ring
    rw [this]; linarith
  calc errP f α β k ≤ mesh k ^ 2 * normD2 f α β / 8 := errP_le hαβ hf k
    _ ≤ ((β - α) / N) ^ 2 * (1 + (4 * C' + 4 * C' ^ 2) / N) * normD2 f α β / 8 := by
        gcongr
    _ = _ := by rw [div_pow, inv_pow]; ring

/-- **Equation (35), nodal endpoints.** When `α` and `β` are nodes of the mesh, the boundary
term disappears: `‖f - P_k F‖_∞ ≤ (β-α)² M / 8 · N_k^{-2}`. -/
theorem errP_le_numCells_of_nodes (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (k : ℕ)
    {a b : ℤ} (ha : α = a / 2 ^ k) (hb : β = b / 2 ^ k) :
    errP f α β k ≤ (β - α) ^ 2 * normD2 f α β / 8 * ((numCells α β k : ℝ)⁻¹) ^ 2 := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hN : (numCells α β k : ℝ) = (β - α) * 2 ^ k := by
    unfold numCells
    rw [ha, hb, div_mul_cancel₀ _ hp.ne', div_mul_cancel₀ _ hp.ne', Int.ceil_intCast,
      Int.floor_intCast]
    push_cast; field_simp
  rw [hN]
  have hba : 0 < β - α := by linarith
  calc errP f α β k ≤ mesh k ^ 2 * normD2 f α β / 8 := errP_le hαβ hf k
    _ = _ := by unfold mesh; field_simp

end

end Fase3
