module
public import RequestProject.Sec7.JointError
public import RequestProject.Sec7.Codec
@[expose] public section

/-!
# Theorem 7.18, lower bound: a `4ε`-separated family of `2^m` bumps in `𝓕_{R,M}`

The class `𝓕_{R,M}` is viewed in `C([0,1])` with the uniform metric.  With a fixed smooth bump
`ψ` (`ψ(1/2) = 1`, `0 ≤ ψ ≤ 1`, supported in `(1/4, 3/4)`), amplitude `A = 4ε` and width
`w = √(A‖ψ''‖/M)`, the functions `f_S = ∑_{j ∈ S} A ψ((x - jw)/w)`, `S ⊆ {0,…,m-1}`,
`m = ⌊1/w⌋`, lie in `𝓕_{R,M}` and are pairwise at distance `A = 4ε`.
-/

open Set Finset

namespace Dyadic.Lib

/-- The class `𝓕_{R,M}` as a subset of `C([0,1])` (restrictions to `[0,1]`). -/
def FRMC (R M : ℝ) : Set C(Icc (0 : ℝ) 1, ℝ) :=
  {g | ∃ f ∈ FRM R M, ∀ x : Icc (0 : ℝ) 1, g x = f x}

/-! ### The bump -/

/-- A fixed smooth bump centred at `1/2`, equal to `1` on `[3/8, 5/8]`, supported in
`(1/4, 3/4)`. -/
noncomputable def bumpPsi : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- `ψ`. -/
noncomputable def psi : ℝ → ℝ := ⇑bumpPsi

lemma psi_contDiff : ContDiff ℝ 2 psi := bumpPsi.contDiff (n := 2)

lemma psi_nonneg (y : ℝ) : 0 ≤ psi y := bumpPsi.nonneg
lemma psi_le_one (y : ℝ) : psi y ≤ 1 := bumpPsi.le_one

lemma psi_half : psi (1 / 2) = 1 := bumpPsi.one_of_mem_closedBall (by simp [bumpPsi])

lemma psi_eq_zero {y : ℝ} (hy : y ∉ Icc (1 / 4 : ℝ) (3 / 4)) : psi y = 0 := by
  have h : y ∉ Metric.ball (1 / 2 : ℝ) (1 / 4) := by
    intro h'
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h'
    exact hy ⟨by linarith [h'.1], by linarith [h'.2]⟩
  have hs : Function.support psi = Metric.ball (1 / 2 : ℝ) (1 / 4) := bumpPsi.support_eq
  rw [← hs] at h
  exact Function.notMem_support.1 h

lemma psi2_eq_zero {y : ℝ} (hy : y ∉ Icc (1 / 4 : ℝ) (3 / 4)) : iteratedDeriv 2 psi y = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have h : y ∉ tsupport psi := by
    have hs : tsupport psi = Metric.closedBall (1 / 2 : ℝ) (1 / 4) := bumpPsi.tsupport_eq
    rw [hs]
    intro h'
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at h'
    exact hy ⟨by linarith [h'.1], by linarith [h'.2]⟩
  have : y ∉ Function.support (iteratedFDeriv ℝ 2 psi) :=
    fun h' => h (support_iteratedFDeriv_subset 2 h')
  rw [Function.notMem_support.1 this]; rfl

lemma psi2_bound : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, |iteratedDeriv 2 psi y| ≤ B := by
  have hc : Continuous (iteratedDeriv 2 psi) := psi_contDiff.continuous_iteratedDeriv 2 le_rfl
  have hs : HasCompactSupport (iteratedDeriv 2 psi) :=
    HasCompactSupport.intro (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 3 / 4))
      (fun y hy => psi2_eq_zero hy)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 1, le_max_right _ _, fun y => (hC y).trans (le_max_left _ _)⟩

/-! ### Bump sums -/

/-- One bump `A ψ((x - jw)/w)`, written as `A ψ(w⁻¹ (x - jw))`. -/
noncomputable def bumpTerm (A w : ℝ) (j : ℕ) (x : ℝ) : ℝ := A * psi (w⁻¹ * (x + -(j * w)))

/-- `f_S = ∑_{j ∈ S} A ψ((x - jw)/w)`. -/
noncomputable def bumpSum (A w : ℝ) (S : Finset ℕ) (x : ℝ) : ℝ := ∑ j ∈ S, bumpTerm A w j x

lemma bumpTerm_contDiff (A w : ℝ) (j : ℕ) : ContDiff ℝ 2 (bumpTerm A w j) := by
  unfold bumpTerm
  exact contDiff_const.mul (psi_contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const)))

lemma bumpSum_contDiff (A w : ℝ) (S : Finset ℕ) : ContDiff ℝ 2 (bumpSum A w S) := by
  unfold bumpSum
  exact ContDiff.sum (fun j _ => bumpTerm_contDiff A w j)

lemma iteratedDeriv_bumpTerm (A w : ℝ) (j : ℕ) (x : ℝ) :
    iteratedDeriv 2 (bumpTerm A w j) x = A * (w⁻¹ ^ 2 * iteratedDeriv 2 psi (w⁻¹ * (x + -(j * w)))) := by
  show iteratedDeriv 2 (fun y => A * psi (w⁻¹ * (y + -(j * w)))) x = _
  rw [iteratedDeriv_const_mul A (f := fun y => psi (w⁻¹ * (y + -(j * w))))
    ((psi_contDiff.comp (contDiff_const.mul (contDiff_id.add contDiff_const))).contDiffAt)]
  congr 1
  have h1 := iteratedDeriv_comp_add_const 2 (fun z => psi (w⁻¹ * z)) (-(j * w))
  have h2 := iteratedDeriv_comp_const_mul psi_contDiff w⁻¹
  have := congrFun h1 x
  simp only at this
  rw [this, h2]

/-- Uniqueness of the active bump at a point. -/
lemma bump_unique {w x : ℝ} (hw : 0 < w) {i j : ℕ}
    (hi : w⁻¹ * (x + -(i * w)) ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hj : w⁻¹ * (x + -(j * w)) ∈ Icc (1 / 4 : ℝ) (3 / 4)) : i = j := by
  have ei : w⁻¹ * (x + -(i * w)) = x / w - i := by field_simp; ring
  have ej : w⁻¹ * (x + -(j * w)) = x / w - j := by field_simp; ring
  rw [ei] at hi; rw [ej] at hj
  have h1 : (i : ℝ) - j < 1 := by linarith [hi.1, hi.2, hj.1, hj.2]
  have h2 : (j : ℝ) - i < 1 := by linarith [hi.1, hi.2, hj.1, hj.2]
  have h3 : (i : ℤ) - j < 1 := by exact_mod_cast h1
  have h4 : (j : ℤ) - i < 1 := by exact_mod_cast h2
  omega

/-- A sum over `S` whose terms vanish except at the (unique) active bump is bounded by the bound
of a single term. -/
lemma sum_single_bound {w x T : ℝ} (hw : 0 < w) (hT : 0 ≤ T) (S : Finset ℕ) (t : ℕ → ℝ)
    (ht0 : ∀ j : ℕ, w⁻¹ * (x + -(j * w)) ∉ Icc (1 / 4 : ℝ) (3 / 4) → t j = 0)
    (htT : ∀ j : ℕ, |t j| ≤ T) : |∑ j ∈ S, t j| ≤ T := by
  by_cases h : ∃ i ∈ S, t i ≠ 0
  · obtain ⟨i, hi, hti⟩ := h
    have hiI : w⁻¹ * (x + -(i * w)) ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
      by_contra hc; exact hti (ht0 i hc)
    rw [Finset.sum_eq_single i (fun j _ hji => by
      by_contra hc
      exact hji (bump_unique hw (by by_contra hc'; exact hc (ht0 j hc')) hiI)) (fun h => absurd hi h)]
    exact htT i
  · push_neg at h
    rw [Finset.sum_eq_zero h]; simpa using hT

lemma bumpSum_mem_FRM {R M A w : ℝ} {B : ℝ} (hw : 0 < w) (hA : 0 ≤ A) (hAR : A ≤ R)
    (hB : ∀ y, |iteratedDeriv 2 psi y| ≤ B) (hAB : A * (w⁻¹ ^ 2 * B) ≤ M) (S : Finset ℕ) :
    bumpSum A w S ∈ FRM R M := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨(bumpSum_contDiff A w S).contDiffOn, fun x _ => ?_, fun x hx => ?_⟩
  · unfold bumpSum
    refine (sum_single_bound (x := x) hw (hA.trans hAR) S _ (fun j hj => ?_) (fun j => ?_))
    · simp [bumpTerm, psi_eq_zero hj]
    · simp only [bumpTerm, abs_mul, abs_of_nonneg hA, abs_of_nonneg (psi_nonneg _)]
      nlinarith [psi_le_one (w⁻¹ * (x + -(j * w))), psi_nonneg (w⁻¹ * (x + -(j * w)))]
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (bumpSum_contDiff A w S).contDiffAt hx]
    unfold bumpSum
    rw [iteratedDeriv_fun_sum (fun j _ => (bumpTerm_contDiff A w j).contDiffAt)]
    refine sum_single_bound (x := x) hw ((by positivity : (0 : ℝ) ≤ A * (w⁻¹ ^ 2 * B)).trans hAB) S _
      (fun j hj => ?_) (fun j => ?_)
    · rw [iteratedDeriv_bumpTerm, psi2_eq_zero hj]; ring
    · rw [iteratedDeriv_bumpTerm, abs_mul, abs_of_nonneg hA, abs_mul,
        abs_of_nonneg (by positivity)]
      refine le_trans ?_ hAB
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB _) (by positivity)) hA

/-- Separation: two different bump sums differ by `A` at the centre of a bump in the symmetric
difference. -/
lemma bumpSum_sep {A w : ℝ} (hw : 0 < w) {m : ℕ} (hmw : (m : ℝ) * w ≤ 1) {S T : Finset ℕ}
    (hS : S ⊆ range m) (hT : T ⊆ range m) (hST : S ≠ T) :
    ∃ x ∈ Icc (0 : ℝ) 1, |bumpSum A w S x - bumpSum A w T x| = |A| := by
  obtain ⟨j, hj⟩ : ∃ j, (j ∈ S ∧ j ∉ T) ∨ (j ∈ T ∧ j ∉ S) := by
    by_contra h; push_neg at h
    exact hST (Finset.ext fun j => ⟨(h j).1, (h j).2⟩)
  have hjm : j < m := by
    rcases hj with ⟨h, -⟩ | ⟨h, -⟩
    · exact mem_range.1 (hS h)
    · exact mem_range.1 (hT h)
  set x := (j : ℝ) * w + w / 2
  have hx : x ∈ Icc (0 : ℝ) 1 := by
    have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hjm
    constructor
    · positivity
    · have : ((j : ℝ) + 1) * w ≤ m * w := mul_le_mul_of_nonneg_right this hw.le
      simp only [x]; nlinarith
  have hval : ∀ i : ℕ, bumpTerm A w i x = if i = j then A else 0 := by
    intro i
    have e : w⁻¹ * (x + -(i * w)) = (j : ℝ) - i + 1 / 2 := by simp only [x]; field_simp; ring
    unfold bumpTerm
    rw [e]
    split_ifs with h
    · subst h; rw [sub_self, zero_add, psi_half]; ring
    · rw [psi_eq_zero]; · ring
      intro hI
      have h1 : (j : ℝ) - i < 1 := by linarith [hI.2]
      have h2 : (i : ℝ) - j < 1 := by linarith [hI.1]
      have h3 : (j : ℤ) - i < 1 := by exact_mod_cast h1
      have h4 : (i : ℤ) - j < 1 := by exact_mod_cast h2
      exact h (by omega)
  have hsum : ∀ U : Finset ℕ, bumpSum A w U x = if j ∈ U then A else 0 := by
    intro U
    unfold bumpSum
    simp only [hval, Finset.sum_ite_eq']
  refine ⟨x, hx, ?_⟩
  rw [hsum, hsum]
  rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · simp [h1, h2]

/-- The restriction of a function continuous on `[0,1]` to an element of `C([0,1])`. -/
def toC (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨Set.restrict _ f, hf.restrict⟩

@[simp] lemma toC_apply (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) (x : Icc (0 : ℝ) 1) :
    toC f hf x = f x := rfl

lemma FRM.continuousOn {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) : ContinuousOn f (Icc 0 1) :=
  hf.1.continuousOn

lemma toC_mem_FRMC {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) : toC f (FRM.continuousOn hf) ∈ FRMC R M :=
  ⟨f, hf, fun _ => rfl⟩

/-- A packing lower bound for the covering number: `2^m` points of `F` pairwise at distance
`> 2ε` force every `ε`-cover to have at least `2^m` centres. -/
lemma coveringNumber_ge_of_packing {X : Type*} [PseudoMetricSpace X] {F : Set X} {ε : ℝ} {m : ℕ}
    (pt : Finset ℕ → X) (hpt : ∀ S ⊆ range m, pt S ∈ F)
    (hsep : ∀ S ⊆ range m, ∀ T ⊆ range m, S ≠ T → 2 * ε < dist (pt S) (pt T))
    (hne : ∃ C : Finset X, ∀ f ∈ F, ∃ c ∈ C, dist f c ≤ ε) :
    2 ^ m ≤ coveringNumber F ε := by
  classical
  have hset : {n | ∃ C : Finset X, C.card = n ∧ ∀ f ∈ F, ∃ c ∈ C, dist f c ≤ ε}.Nonempty := by
    obtain ⟨C, hC⟩ := hne; exact ⟨_, C, rfl, hC⟩
  obtain ⟨C, hCcard, hC⟩ := Nat.sInf_mem hset
  unfold coveringNumber
  rw [← hCcard]
  choose! c hcC hcd using hC
  have hinj : Set.InjOn (fun S => c (pt S)) ((range m).powerset : Set (Finset ℕ)) := by
    intro S hS T hT h
    by_contra hne
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hS hT
    have h1 := hcd (pt S) (hpt S hS)
    have h2 := hcd (pt T) (hpt T hT)
    simp only at h
    rw [h] at h1
    have := dist_triangle_right (pt S) (pt T) (c (pt T))
    have := hsep S hS T hT hne
    linarith
  have := Finset.card_le_card_of_injOn _ (fun S hS => hcC _ (hpt S (mem_powerset.1 hS))) hinj
  rwa [card_powerset, card_range] at this

/-- **Theorem 7.18**, lower bound in (86): there are `ε₀, c > 0` (depending on `R, M`) such that
for `0 < ε < ε₀` (and as soon as a finite `ε`-cover exists), `ℋ_ε(𝓕_{R,M}) ≥ c ε^{-1/2}`. -/
theorem entropy_lower {R M : ℝ} (hR : 0 < R) (hM : 0 < M) :
    ∃ ε₀ > 0, ∃ c > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∃ C : Finset C(Icc (0 : ℝ) 1, ℝ), ∀ f ∈ FRMC R M, ∃ c ∈ C, dist f c ≤ ε) →
      c / Real.sqrt ε ≤ metricEntropy (FRMC R M) ε := by
  obtain ⟨B, hB1, hB⟩ := psi2_bound
  have hBpos : 0 < B := by linarith
  refine ⟨min (R / 4) (M / (16 * B)), lt_min (by positivity) (by positivity),
    Real.sqrt (M / (4 * B)) / 2, by positivity, fun ε hε hε0 hcov => ?_⟩
  have hε1 : ε < R / 4 := lt_of_lt_of_le hε0 (min_le_left _ _)
  have hε2 : ε < M / (16 * B) := lt_of_lt_of_le hε0 (min_le_right _ _)
  set A := 4 * ε
  set w := Real.sqrt (A * B / M)
  have hw : 0 < w := Real.sqrt_pos.2 (by positivity)
  have hw2 : w ^ 2 = A * B / M := Real.sq_sqrt (by positivity)
  set m := ⌊w⁻¹⌋₊
  have hmw : (m : ℝ) * w ≤ 1 := by
    have := Nat.floor_le (inv_nonneg.2 hw.le)
    calc (m : ℝ) * w ≤ w⁻¹ * w := mul_le_mul_of_nonneg_right this hw.le
      _ = 1 := inv_mul_cancel₀ hw.ne'
  have hAB : A * (w⁻¹ ^ 2 * B) ≤ M := by
    have hA0 : A ≠ 0 := by positivity
    have h : A * ((A * B / M)⁻¹ * B) = M := by field_simp
    rw [inv_pow, hw2, h]
  -- the family
  let pt : Finset ℕ → C(Icc (0 : ℝ) 1, ℝ) := fun S =>
    toC (bumpSum A w S) (bumpSum_contDiff A w S).continuous.continuousOn
  have hmem : ∀ S, bumpSum A w S ∈ FRM R M :=
    bumpSum_mem_FRM hw (by positivity) (by linarith) hB hAB
  have hpt : ∀ S ⊆ range m, pt S ∈ FRMC R M := fun S _ => ⟨_, hmem S, fun _ => rfl⟩
  have hsep : ∀ S ⊆ range m, ∀ T ⊆ range m, S ≠ T → 2 * ε < dist (pt S) (pt T) := by
    intro S hS T hT hST
    obtain ⟨x, hx, hxv⟩ := bumpSum_sep (A := A) hw hmw hS hT hST
    have := ContinuousMap.dist_apply_le_dist (f := pt S) (g := pt T) ⟨x, hx⟩
    simp only [pt, toC_apply, Real.dist_eq] at this
    rw [hxv, abs_of_pos (by positivity)] at this
    simp only [A] at this
    linarith
  have hN := coveringNumber_ge_of_packing pt hpt hsep hcov
  -- `ℋ_ε ≥ m ≥ c ε^{-1/2}`
  have hlog : (m : ℝ) ≤ metricEntropy (FRMC R M) ε := by
    unfold metricEntropy
    have : ((2 : ℝ) ^ m) ≤ coveringNumber (FRMC R M) ε := by exact_mod_cast hN
    calc (m : ℝ) = Real.logb 2 ((2 : ℝ) ^ m) := by rw [Real.logb_pow]; simp
      _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by positivity) this
  have hwinv : w⁻¹ = Real.sqrt (M / (4 * B)) / Real.sqrt ε := by
    simp only [w, A]
    rw [← Real.sqrt_inv, show (4 * ε * B / M)⁻¹ = M / (4 * B) / ε by field_simp,
      Real.sqrt_div' _ hε.le]
  have hw2' : 2 ≤ w⁻¹ := by
    rw [hwinv, le_div_iff₀ (Real.sqrt_pos.2 hε)]
    rw [show (2 : ℝ) * Real.sqrt ε = Real.sqrt (4 * ε) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hε2
    nlinarith
  have hm : w⁻¹ / 2 ≤ m := by
    have := Nat.lt_floor_add_one w⁻¹
    linarith
  calc Real.sqrt (M / (4 * B)) / 2 / Real.sqrt ε = w⁻¹ / 2 := by rw [hwinv]; ring
    _ ≤ m := hm
    _ ≤ _ := hlog

end Dyadic.Lib
