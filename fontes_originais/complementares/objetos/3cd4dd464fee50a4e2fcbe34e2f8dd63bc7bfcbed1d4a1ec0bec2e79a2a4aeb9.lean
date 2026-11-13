module
public import RequestProject.Assembly

/-!
# The quadratic `C²` extension (equation (30))

For `f ∈ C²[α, β]` we use the one-sided derivatives `f' = derivWithin f [α,β]` and
`f'' = derivWithin f' [α,β]`, and extend `f` by its second-order Taylor polynomials at the
endpoints. We prove `F ∈ C²(ℝ)` and `‖F''‖_{∞,ℝ} = ‖f''‖_{∞,[α,β]}`.
-/

@[expose] public section

namespace Fase3

open Set

/-- `f'` on `[α, β]` (one-sided at the endpoints). -/
noncomputable def d1 (f : ℝ → ℝ) (α β : ℝ) : ℝ → ℝ := derivWithin f (Icc α β)

/-- `f''` on `[α, β]` (one-sided at the endpoints). -/
noncomputable def d2 (f : ℝ → ℝ) (α β : ℝ) : ℝ → ℝ := derivWithin (d1 f α β) (Icc α β)

/-- `M = ‖f''‖_{∞,[α,β]}`. -/
noncomputable def normD2 (f : ℝ → ℝ) (α β : ℝ) : ℝ := supNormOn (Icc α β) (d2 f α β)

/-- The extension `F` of equation (30). -/
noncomputable def extF (f : ℝ → ℝ) (α β : ℝ) (x : ℝ) : ℝ :=
  if x < α then f α + d1 f α β α * (x - α) + 1 / 2 * d2 f α β α * (x - α) ^ 2
  else if x ≤ β then f x
  else f β + d1 f α β β * (x - β) + 1 / 2 * d2 f α β β * (x - β) ^ 2

/-- `F'`. -/
noncomputable def extF1 (f : ℝ → ℝ) (α β : ℝ) (x : ℝ) : ℝ :=
  if x < α then d1 f α β α + d2 f α β α * (x - α)
  else if x ≤ β then d1 f α β x
  else d1 f α β β + d2 f α β β * (x - β)

/-- `F''`. -/
noncomputable def extF2 (f : ℝ → ℝ) (α β : ℝ) (x : ℝ) : ℝ :=
  if x < α then d2 f α β α else if x ≤ β then d2 f α β x else d2 f α β β

/-- Gluing one-sided derivatives on `(-∞, a]`, `[a, b]`, `[b, ∞)`. -/
lemma glue_hasDerivAt {a b : ℝ} (hab : a < b) {u u' : ℝ → ℝ}
    (hL : ∀ x ≤ a, HasDerivWithinAt u (u' x) (Iic a) x)
    (hM : ∀ x ∈ Icc a b, HasDerivWithinAt u (u' x) (Icc a b) x)
    (hR : ∀ x, b ≤ x → HasDerivWithinAt u (u' x) (Ici b) x) (x : ℝ) :
    HasDerivAt u (u' x) x := by
  rcases lt_trichotomy x a with h | rfl | h
  · exact (hL x h.le).hasDerivAt (Iic_mem_nhds h)
  · have h1 : HasDerivWithinAt u (u' x) (Ici x) x :=
      (hM x ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
    have := (hL x le_rfl).union h1
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  rcases lt_trichotomy x b with h' | rfl | h'
  · exact (hM x ⟨h.le, h'.le⟩).hasDerivAt (Icc_mem_nhds h h')
  · have h1 : HasDerivWithinAt u (u' x) (Iic x) x :=
      (hM x ⟨h.le, le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
    have := h1.union (hR x le_rfl)
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · exact (hR x h'.le).hasDerivAt (Ici_mem_nhds h')

section
variable {f : ℝ → ℝ} {α β : ℝ}

lemma hasDerivWithinAt_d0 (hf : ContDiffOn ℝ 2 f (Icc α β)) {x : ℝ}
    (hx : x ∈ Icc α β) : HasDerivWithinAt f (d1 f α β x) (Icc α β) x :=
  ((hf.differentiableOn (by norm_num)) x hx).hasDerivWithinAt

lemma contDiffOn_d1 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    ContDiffOn ℝ 1 (d1 f α β) (Icc α β) :=
  hf.derivWithin (uniqueDiffOn_Icc hαβ) (by norm_num)

lemma hasDerivWithinAt_d1 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) {x : ℝ}
    (hx : x ∈ Icc α β) : HasDerivWithinAt (d1 f α β) (d2 f α β x) (Icc α β) x :=
  (((contDiffOn_d1 hαβ hf).differentiableOn (by norm_num)) x hx).hasDerivWithinAt

lemma continuousOn_d2 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    ContinuousOn (d2 f α β) (Icc α β) :=
  ((contDiffOn_d1 hαβ hf).derivWithin (m := 0) (uniqueDiffOn_Icc hαβ) (by norm_num)).continuousOn

lemma extF2_eq_comp (hαβ : α < β) (x : ℝ) : extF2 f α β x = d2 f α β (clamp α β x) := by
  unfold extF2 clamp
  split_ifs with h1 h2
  · rw [min_eq_left (by linarith), max_eq_left h1.le]
  · rw [min_eq_left h2, max_eq_right (not_lt.1 h1)]
  · rw [min_eq_right (by linarith), max_eq_right hαβ.le]

lemma extF_of_mem {x : ℝ} (hx : x ∈ Icc α β) : extF f α β x = f x := by
  unfold extF; rw [if_neg (not_lt.2 hx.1), if_pos hx.2]

lemma hasDerivAt_extF (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (x : ℝ) :
    HasDerivAt (extF f α β) (extF1 f α β x) x := by
  apply glue_hasDerivAt hαβ _ _ _ x
  · intro y hy
    have hp : HasDerivAt (fun t => f α + d1 f α β α * (t - α) + 1 / 2 * d2 f α β α * (t - α) ^ 2)
        (d1 f α β α + d2 f α β α * (y - α)) y := by
      have := ((((hasDerivAt_id y).sub_const α).const_mul (d1 f α β α)).const_add (f α)).add
        ((((hasDerivAt_id y).sub_const α).pow 2).const_mul (1 / 2 * d2 f α β α))
      convert this using 1; simp; ring
    have hval : extF1 f α β y = d1 f α β α + d2 f α β α * (y - α) := by
      unfold extF1
      split_ifs with h1 h2
      · rfl
      · have : y = α := le_antisymm hy (not_lt.1 h1); subst this; ring
      · exact absurd (le_trans hy hαβ.le) h2
    rw [hval]
    apply hp.hasDerivWithinAt.congr
    · intro t ht
      unfold extF
      split_ifs with h1 h2
      · rfl
      · have : t = α := le_antisymm ht (not_lt.1 h1); subst this; ring
      · exact absurd (le_trans ht hαβ.le) h2
    · unfold extF
      split_ifs with h1 h2
      · rfl
      · have : y = α := le_antisymm hy (not_lt.1 h1); subst this; ring
      · exact absurd (le_trans hy hαβ.le) h2
  · intro y hy
    have hval : extF1 f α β y = d1 f α β y := by
      unfold extF1; rw [if_neg (not_lt.2 hy.1), if_pos hy.2]
    rw [hval]
    exact (hasDerivWithinAt_d0 hf hy).congr (fun t ht => extF_of_mem ht) (extF_of_mem hy)
  · intro y hy
    have hp : HasDerivAt (fun t => f β + d1 f α β β * (t - β) + 1 / 2 * d2 f α β β * (t - β) ^ 2)
        (d1 f α β β + d2 f α β β * (y - β)) y := by
      have := ((((hasDerivAt_id y).sub_const β).const_mul (d1 f α β β)).const_add (f β)).add
        ((((hasDerivAt_id y).sub_const β).pow 2).const_mul (1 / 2 * d2 f α β β))
      convert this using 1; simp; ring
    have hval : extF1 f α β y = d1 f α β β + d2 f α β β * (y - β) := by
      unfold extF1
      split_ifs with h1 h2
      · linarith
      · have : y = β := le_antisymm h2 hy; subst this; ring
      · rfl
    rw [hval]
    apply hp.hasDerivWithinAt.congr
    · intro t ht
      simp only [mem_Ici] at ht
      unfold extF
      split_ifs with h1 h2
      · linarith
      · have : t = β := le_antisymm h2 ht; subst this; ring
      · rfl
    · unfold extF
      split_ifs with h1 h2
      · linarith
      · have : y = β := le_antisymm h2 hy; subst this; ring
      · rfl

lemma hasDerivAt_extF1 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (x : ℝ) :
    HasDerivAt (extF1 f α β) (extF2 f α β x) x := by
  apply glue_hasDerivAt hαβ _ _ _ x
  · intro y hy
    have hp : HasDerivAt (fun t => d1 f α β α + d2 f α β α * (t - α)) (d2 f α β α) y := by
      have := (((hasDerivAt_id y).sub_const α).const_mul (d2 f α β α)).const_add (d1 f α β α)
      convert this using 1; simp
    have hval : extF2 f α β y = d2 f α β α := by
      unfold extF2
      split_ifs with h1 h2
      · rfl
      · have : y = α := le_antisymm hy (not_lt.1 h1); subst this; rfl
      · exact absurd (le_trans hy hαβ.le) h2
    rw [hval]
    apply hp.hasDerivWithinAt.congr
    · intro t ht
      unfold extF1
      split_ifs with h1 h2
      · rfl
      · have : t = α := le_antisymm ht (not_lt.1 h1); subst this; ring
      · exact absurd (le_trans ht hαβ.le) h2
    · unfold extF1
      split_ifs with h1 h2
      · rfl
      · have : y = α := le_antisymm hy (not_lt.1 h1); subst this; ring
      · exact absurd (le_trans hy hαβ.le) h2
  · intro y hy
    have hval : extF2 f α β y = d2 f α β y := by
      unfold extF2; rw [if_neg (not_lt.2 hy.1), if_pos hy.2]
    rw [hval]
    refine (hasDerivWithinAt_d1 hαβ hf hy).congr (fun t ht => ?_) ?_
    · unfold extF1; rw [if_neg (not_lt.2 ht.1), if_pos ht.2]
    · unfold extF1; rw [if_neg (not_lt.2 hy.1), if_pos hy.2]
  · intro y hy
    have hp : HasDerivAt (fun t => d1 f α β β + d2 f α β β * (t - β)) (d2 f α β β) y := by
      have := (((hasDerivAt_id y).sub_const β).const_mul (d2 f α β β)).const_add (d1 f α β β)
      convert this using 1; simp
    have hval : extF2 f α β y = d2 f α β β := by
      unfold extF2
      split_ifs with h1 h2
      · linarith
      · have : y = β := le_antisymm h2 hy; subst this; rfl
      · rfl
    rw [hval]
    apply hp.hasDerivWithinAt.congr
    · intro t ht
      simp only [mem_Ici] at ht
      unfold extF1
      split_ifs with h1 h2
      · linarith
      · have : t = β := le_antisymm h2 ht; subst this; ring
      · rfl
    · unfold extF1
      split_ifs with h1 h2
      · linarith
      · have : y = β := le_antisymm h2 hy; subst this; ring
      · rfl

lemma deriv_extF (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    deriv (extF f α β) = extF1 f α β :=
  funext fun x => (hasDerivAt_extF hαβ hf x).deriv

lemma deriv_extF1 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    deriv (extF1 f α β) = extF2 f α β :=
  funext fun x => (hasDerivAt_extF1 hαβ hf x).deriv

lemma deriv2_extF (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    deriv (deriv (extF f α β)) = extF2 f α β := by
  rw [deriv_extF hαβ hf, deriv_extF1 hαβ hf]

lemma continuous_extF2 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    Continuous (extF2 f α β) := by
  have : extF2 f α β = fun x => d2 f α β (clamp α β x) := funext (extF2_eq_comp hαβ)
  rw [this]
  exact (continuousOn_d2 hαβ hf).comp_continuous (continuous_clamp α β) (clamp_mem hαβ.le)

/-- The extension of equation (30) is `C²` on `ℝ`. -/
theorem extF_contDiff (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    ContDiff ℝ 2 (extF f α β) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_extF hαβ hf x).differentiableAt, by simp, ?_⟩
  rw [deriv_extF hαβ hf, show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hasDerivAt_extF1 hαβ hf x).differentiableAt, by simp, ?_⟩
  rw [deriv_extF1 hαβ hf, contDiff_zero]
  exact continuous_extF2 hαβ hf

lemma bddAbove_abs_d2 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    BddAbove ((fun x => |d2 f α β x|) '' Icc α β) :=
  isCompact_Icc.bddAbove_image (continuousOn_d2 hαβ hf).abs

lemma abs_d2_le (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) {x : ℝ} (hx : x ∈ Icc α β) :
    |d2 f α β x| ≤ normD2 f α β :=
  le_csSup (bddAbove_abs_d2 hαβ hf) ⟨x, hx, rfl⟩

lemma normD2_nonneg (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) : 0 ≤ normD2 f α β :=
  le_trans (abs_nonneg _) (abs_d2_le hαβ hf ⟨le_rfl, hαβ.le⟩)

lemma abs_extF2_le (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) (x : ℝ) :
    |extF2 f α β x| ≤ normD2 f α β := by
  rw [extF2_eq_comp hαβ]; exact abs_d2_le hαβ hf (clamp_mem hαβ.le x)

/-- `‖F''‖_{∞,ℝ} = ‖f''‖_{∞,[α,β]}`. -/
theorem supNorm_extF2 (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    supNormOn univ (deriv (deriv (extF f α β))) = normD2 f α β := by
  rw [deriv2_extF hαβ hf]
  unfold normD2 supNormOn
  congr 1
  ext e
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨clamp α β x, clamp_mem hαβ.le x, by rw [extF2_eq_comp hαβ]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by rw [extF2_eq_comp hαβ, clamp_of_mem hx]⟩

end

end Fase3
