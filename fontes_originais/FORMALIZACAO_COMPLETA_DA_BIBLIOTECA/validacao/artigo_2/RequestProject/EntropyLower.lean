import RequestProject.JointBudget

/-!
# Theorem 3.14, lower bound: a `4ε`-separated packing of `𝓕_{R,M}` of size `2^m`

Covering numbers in the uniform norm on `[0,1]` and the bump-function packing.
-/

namespace Artigo

open Set Finset

/-- `S` is an `ε`-cover of `F` (closed balls of radius `ε` in the uniform norm on `[0,1]`) -/
def IsCover (ε : ℝ) (F : Set (ℝ → ℝ)) (s : Finset (ℝ → ℝ)) : Prop :=
  ∀ f ∈ F, ∃ g ∈ s, ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ ε

/-- the covering number `N_ε(F)` -/
noncomputable def coverNum (ε : ℝ) (F : Set (ℝ → ℝ)) : ℕ :=
  sInf {n | ∃ s : Finset (ℝ → ℝ), s.card = n ∧ IsCover ε F s}

/-- the metric entropy `𝓗_ε(F) = log₂ N_ε(F)` -/
noncomputable def entropyH (ε : ℝ) (F : Set (ℝ → ℝ)) : ℝ := Real.logb 2 (coverNum ε F)

lemma coverNum_le {ε : ℝ} {F : Set (ℝ → ℝ)} {s : Finset (ℝ → ℝ)} (h : IsCover ε F s) :
    coverNum ε F ≤ s.card := Nat.sInf_le ⟨s, rfl, h⟩

lemma le_coverNum {ε : ℝ} {F : Set (ℝ → ℝ)} {n : ℕ} (hne : ∃ s, IsCover ε F s)
    (h : ∀ s, IsCover ε F s → n ≤ s.card) : n ≤ coverNum ε F := by
  obtain ⟨s, hs⟩ := hne
  have hmem := Nat.sInf_mem (s := {n | ∃ s : Finset (ℝ → ℝ), s.card = n ∧ IsCover ε F s}) ⟨_, s, rfl, hs⟩
  obtain ⟨t, ht, htc⟩ := hmem
  unfold coverNum; rw [← ht]; exact h t htc

/-! ## The bump -/

/-- a fixed smooth bump on `ℝ`: equal to `1` near `1/2`, supported in `[1/4, 3/4]` -/
noncomputable def psi : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

lemma psi_contDiff : ContDiff ℝ 3 (psi : ℝ → ℝ) := psi.contDiff

lemma psi_half : (psi : ℝ → ℝ) (1 / 2) = 1 := psi.one_of_mem_closedBall (by simp; norm_num [psi])

lemma psi_tsupport : tsupport (psi : ℝ → ℝ) ⊆ Icc (1 / 4) (3 / 4) := by
  rw [psi.tsupport_eq]
  intro x hx
  simp only [Metric.mem_closedBall, Real.dist_eq, psi] at hx
  rw [abs_le] at hx
  constructor <;> linarith [hx.1, hx.2]

lemma deriv_psi_differentiable : Differentiable ℝ (deriv (psi : ℝ → ℝ)) := by
  have : ContDiff ℝ 2 (deriv^[1] (psi : ℝ → ℝ)) := psi_contDiff.iterate_deriv' 2 1
  exact (by simpa using this : ContDiff ℝ 2 (deriv (psi : ℝ → ℝ))).differentiable (by simp)

lemma psi_differentiable : Differentiable ℝ (psi : ℝ → ℝ) := psi_contDiff.differentiable (by norm_num)

lemma psi2_continuous : Continuous (deriv (deriv (psi : ℝ → ℝ))) := by
  have : ContDiff ℝ 1 (deriv^[2] (psi : ℝ → ℝ)) := psi_contDiff.iterate_deriv' 1 2
  simpa using this.continuous

lemma tsupport_deriv_sub {f : ℝ → ℝ} : tsupport (deriv f) ⊆ tsupport f :=
  closure_minimal support_deriv_subset (isClosed_tsupport f)

lemma psi2_zero {u : ℝ} (hu : u ∉ Icc (1 / 4 : ℝ) (3 / 4)) : deriv (deriv (psi : ℝ → ℝ)) u = 0 := by
  by_contra h
  have : u ∈ Function.support (deriv (deriv (psi : ℝ → ℝ))) := h
  exact hu (psi_tsupport (tsupport_deriv_sub (support_deriv_subset this)))

lemma psi_zero {u : ℝ} (hu : u ∉ Icc (1 / 4 : ℝ) (3 / 4)) : (psi : ℝ → ℝ) u = 0 := by
  by_contra h
  exact hu (psi_tsupport (subset_tsupport _ h))

/-- a bound `K ≥ 1` for `|ψ''|` -/
lemma psi2_bound : ∃ K : ℝ, 1 ≤ K ∧ ∀ u, |deriv (deriv (psi : ℝ → ℝ)) u| ≤ K := by
  have hc : HasCompactSupport (deriv (deriv (psi : ℝ → ℝ))) :=
    psi.hasCompactSupport.deriv.deriv
  obtain ⟨C, hC⟩ := psi2_continuous.bounded_above_of_compact_support hc
  exact ⟨max 1 C, le_max_left _ _, fun u => (hC u).trans (le_max_right _ _)⟩

/-! ## The packing family -/

/-- `f_S(x) = Σ_{j ∈ S} A ψ((x - j w)/w)` -/
noncomputable def packFun (A w : ℝ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ S, A * (psi : ℝ → ℝ) ((x - j * w) / w)

/-- at most one translate is active at each point -/
lemma sum_translates_single {g : ℝ → ℝ} (hg : ∀ u, u ∉ Icc (1 / 4 : ℝ) (3 / 4) → g u = 0)
    {B : ℝ} (hB : ∀ u, |g u| ≤ B) (S : Finset ℕ) (w x : ℝ) (hw : 0 < w) (c : ℝ) :
    |∑ j ∈ S, c * g ((x - j * w) / w)| ≤ |c| * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  by_cases h : ∃ j ∈ S, (x - j * w) / w ∈ Icc (1 / 4 : ℝ) (3 / 4)
  · obtain ⟨j0, hj0, hu⟩ := h
    rw [Finset.sum_eq_single_of_mem j0 hj0]
    · rw [abs_mul]; gcongr; exact hB _
    · intro j _ hj
      rw [hg _ ?_, mul_zero]
      intro hu'
      have e : (x - j * w) / w = (x - j0 * w) / w + ((j0 : ℝ) - j) := by field_simp; ring
      rw [e] at hu'
      have hne : (j0 : ℤ) ≠ j := by exact_mod_cast (Ne.symm hj)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have : ((j0 : ℤ) : ℝ) + 1 ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hlt
        push_cast at this
        linarith [hu.1, hu'.2, hu.2, hu'.1]
      · have : ((j : ℤ) : ℝ) + 1 ≤ ((j0 : ℤ) : ℝ) := by exact_mod_cast hlt
        push_cast at this
        linarith [hu.2, hu'.1, hu.1, hu'.2]
  · push_neg at h
    rw [Finset.sum_eq_zero (fun j hj => by rw [hg _ (h j hj), mul_zero])]
    simp; positivity

lemma packFun_hasDerivAt (A w : ℝ) (S : Finset ℕ) (x : ℝ) :
    HasDerivAt (packFun A w S) (∑ j ∈ S, A / w * deriv (psi : ℝ → ℝ) ((x - j * w) / w)) x := by
  unfold packFun
  have : ∀ j ∈ S, HasDerivAt (fun x => A * (psi : ℝ → ℝ) ((x - j * w) / w))
      (A / w * deriv (psi : ℝ → ℝ) ((x - j * w) / w)) x := by
    intro j _
    have h1 : HasDerivAt (fun x : ℝ => (x - j * w) / w) (1 / w) x := by
      simpa using ((hasDerivAt_id x).sub_const ((j : ℝ) * w)).div_const w
    have h2 := (psi_differentiable ((x - j * w) / w)).hasDerivAt.comp x h1
    convert h2.const_mul A using 1; ring
  convert HasDerivAt.fun_sum this using 1

lemma packFun_deriv (A w : ℝ) (S : Finset ℕ) :
    deriv (packFun A w S) = fun x => ∑ j ∈ S, A / w * deriv (psi : ℝ → ℝ) ((x - j * w) / w) :=
  funext fun x => (packFun_hasDerivAt A w S x).deriv

lemma packFun_deriv2 (A w : ℝ) (S : Finset ℕ) (x : ℝ) :
    deriv (deriv (packFun A w S)) x =
      ∑ j ∈ S, A / w ^ 2 * deriv (deriv (psi : ℝ → ℝ)) ((x - j * w) / w) := by
  rw [packFun_deriv]
  have : ∀ j ∈ S, HasDerivAt (fun x => A / w * deriv (psi : ℝ → ℝ) ((x - j * w) / w))
      (A / w ^ 2 * deriv (deriv (psi : ℝ → ℝ)) ((x - j * w) / w)) x := by
    intro j _
    have h1 : HasDerivAt (fun x : ℝ => (x - j * w) / w) (1 / w) x := by
      simpa using ((hasDerivAt_id x).sub_const ((j : ℝ) * w)).div_const w
    have h2 := (deriv_psi_differentiable ((x - j * w) / w)).hasDerivAt.comp x h1
    convert h2.const_mul (A / w) using 1; ring
  exact (HasDerivAt.fun_sum this).deriv

lemma packFun_contDiff (A w : ℝ) (S : Finset ℕ) : ContDiff ℝ 2 (packFun A w S) := by
  unfold packFun
  apply ContDiff.sum
  intro j _
  apply ContDiff.mul contDiff_const
  exact (psi_contDiff.of_le (by norm_num)).comp ((contDiff_id.sub contDiff_const).div_const _)

/-- value at the centre of the `j`-th cell -/
lemma packFun_center (A w : ℝ) (hw : 0 < w) (S : Finset ℕ) (j : ℕ) :
    packFun A w S ((j + 1 / 2) * w) = if j ∈ S then A else 0 := by
  unfold packFun
  have hval : ∀ i : ℕ, (((j : ℝ) + 1 / 2) * w - i * w) / w = 1 / 2 + ((j : ℝ) - i) := by
    intro i; field_simp; ring
  simp only [hval]
  split_ifs with hj
  · rw [Finset.sum_eq_single_of_mem j hj]
    · simp only [sub_self, add_zero, psi_half, mul_one]
    · intro i _ hi
      rw [psi_zero, mul_zero]
      intro hu
      have hne : (j : ℤ) ≠ i := by exact_mod_cast (Ne.symm hi)
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have : ((j : ℤ) : ℝ) + 1 ≤ ((i : ℤ) : ℝ) := by exact_mod_cast hlt
        push_cast at this; linarith [hu.1]
      · have : ((i : ℤ) : ℝ) + 1 ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hlt
        push_cast at this; linarith [hu.2]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [psi_zero, mul_zero]
    intro hu
    have hne : (j : ℤ) ≠ i := by
      intro h; apply hj; have : j = i := by exact_mod_cast h
      rw [this]; exact hi
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : ((j : ℤ) : ℝ) + 1 ≤ ((i : ℤ) : ℝ) := by exact_mod_cast hlt
      push_cast at this; linarith [hu.1]
    · have : ((i : ℤ) : ℝ) + 1 ≤ ((j : ℤ) : ℝ) := by exact_mod_cast hlt
      push_cast at this; linarith [hu.2]

lemma packFun_mem {R M A w K : ℝ} (hA : 0 ≤ A) (hAR : A ≤ R) (hw : 0 < w)
    (hK : ∀ u, |deriv (deriv (psi : ℝ → ℝ)) u| ≤ K) (hM : A * K / w ^ 2 ≤ M) (S : Finset ℕ) :
    packFun A w S ∈ FRM R M := by
  refine ⟨packFun_contDiff A w S, fun x _ => ?_, fun x _ => ?_⟩
  · have := sum_translates_single (g := (psi : ℝ → ℝ)) (fun u hu => psi_zero hu) (B := 1)
      (fun u => by rw [abs_le]; constructor <;> linarith [psi.nonneg (x := u), psi.le_one (x := u)])
      S w x hw A
    unfold packFun
    rw [abs_of_nonneg hA, mul_one] at this
    linarith
  · rw [packFun_deriv2]
    have := sum_translates_single (g := deriv (deriv (psi : ℝ → ℝ))) (fun u hu => psi2_zero hu)
      hK S w x hw (A / w ^ 2)
    rw [abs_of_nonneg (show (0 : ℝ) ≤ A / w ^ 2 from div_nonneg hA (by positivity))] at this
    calc _ ≤ A / w ^ 2 * K := this
      _ = A * K / w ^ 2 := by ring
      _ ≤ M := hM

/-- **packing lower bound**: if `A = 4ε ≤ R`, `w² = A K / M` (`K` bounds `|ψ''|`) and
`m w ≤ 1`, then every `ε`-cover of `𝓕_{R,M}` has at least `2^m` elements. -/
lemma packing_lower {R M ε w K : ℝ} (hε : 0 < ε) (hAR : 4 * ε ≤ R) (hw : 0 < w)
    (hK : ∀ u, |deriv (deriv (psi : ℝ → ℝ)) u| ≤ K) (hM : 4 * ε * K / w ^ 2 ≤ M) {m : ℕ}
    (hm : m * w ≤ 1) {s : Finset (ℝ → ℝ)} (hs : IsCover ε (FRM R M) s) : 2 ^ m ≤ s.card := by
  classical
  have hmem : ∀ S : Finset ℕ, packFun (4 * ε) w S ∈ FRM R M :=
    packFun_mem (by positivity) hAR hw hK hM
  choose! g hg hgd using fun S => hs _ (hmem S)
  have hinj : Set.InjOn g ((Finset.range m).powerset : Set (Finset ℕ)) := by
    intro S hS T hT hST
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ S ↔ j ∈ T) := by
      by_contra h; push_neg at h; exact hne (Finset.ext h)
    have hjS : j ∈ Finset.range m := by
      simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hS hT
      by_cases hjS : j ∈ S
      · exact hS hjS
      · exact hT (by tauto)
    have hjm : (j : ℝ) + 1 ≤ m := by
      have := Finset.mem_range.mp hjS; exact_mod_cast this
    have hx : ((j : ℝ) + 1 / 2) * w ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · nlinarith
    have h1 := hgd S _ hx
    have h2 := hgd T _ hx
    rw [hST] at h1
    simp only [packFun_center _ _ hw] at h1 h2
    have : |(if j ∈ S then 4 * ε else 0) - (if j ∈ T then 4 * ε else 0)| ≤ 2 * ε := by
      calc _ = |((if j ∈ S then 4 * ε else 0) - g T (((j : ℝ) + 1 / 2) * w)) -
            ((if j ∈ T then 4 * ε else 0) - g T (((j : ℝ) + 1 / 2) * w))| := by ring_nf
        _ ≤ _ := abs_sub _ _
        _ ≤ 2 * ε := by linarith
    by_cases hjS' : j ∈ S <;> by_cases hjT : j ∈ T <;> simp_all <;>
      rw [abs_of_pos (by linarith)] at this <;> linarith
  calc 2 ^ m = ((Finset.range m).powerset).card := by simp
    _ ≤ s.card := Finset.card_le_card_of_injOn g (fun S _ => hg S) hinj

end Artigo
