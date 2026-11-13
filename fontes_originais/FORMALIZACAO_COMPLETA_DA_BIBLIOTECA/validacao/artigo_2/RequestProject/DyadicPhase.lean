import RequestProject.DyadicExact

/-!
# Section 12.2 — Piecewise quadratics and the phase law (Theorem 12.2, Corollary 12.3)
-/

namespace Artigo

open Set Filter Topology DShape

/-! ## Covering a cell by its descendants -/

lemma cell_sub_children (k : ℕ) (m : ℤ) :
    cellIcc k m ⊆ cellIcc (k + 1) (2 * m) ∪ cellIcc (k + 1) (2 * m + 1) := by
  intro x hx
  rw [cellIcc_eq] at hx
  by_cases h : x ≤ cR (k + 1) (2 * m)
  · left; rw [cellIcc_eq, cL_child_left]; exact ⟨hx.1, h⟩
  · right; rw [cellIcc_eq, cR_child_right, ← cR_child_left]; exact ⟨(not_le.mp h).le, hx.2⟩

lemma exists_desc_mem : ∀ (d k : ℕ) (m : ℤ) (x : ℝ), x ∈ cellIcc k m →
    ∃ i : ℕ, i < 2 ^ d ∧ x ∈ cellIcc (k + d) (m * 2 ^ d + i)
  | 0, k, m, x, hx => ⟨0, by norm_num, by simpa using hx⟩
  | d + 1, k, m, x, hx => by
    obtain ⟨i, hi, hxi⟩ := exists_desc_mem d k m x hx
    rcases cell_sub_children (k + d) (m * 2 ^ d + i) hxi with h | h
    · refine ⟨2 * i, by rw [pow_succ]; omega, ?_⟩
      have e : 2 * (m * 2 ^ d + i) = m * 2 ^ (d + 1) + ((2 * i : ℕ) : ℤ) := by push_cast; ring
      rw [show k + (d + 1) = k + d + 1 by omega, ← e]; exact h
    · refine ⟨2 * i + 1, by rw [pow_succ]; omega, ?_⟩
      have e : 2 * (m * 2 ^ d + i) + 1 = m * 2 ^ (d + 1) + ((2 * i + 1 : ℕ) : ℤ) := by
        push_cast; ring
      rw [show k + (d + 1) = k + d + 1 by omega, ← e]; exact h

/-- a threshold tree obtained by grafting threshold trees below a level where every ancestor is
split -/
lemma isThr_graft {f : ℝ → ℝ} {ε : ℝ} (sub : ℤ → DShape) : ∀ (d k : ℕ) (m : ℤ),
    (∀ j < d, ∀ i : ℕ, i < 2 ^ j → ε < locErr f (k + j) (m * 2 ^ j + i)) →
    (∀ i : ℕ, i < 2 ^ d → IsThr f ε (k + d) (m * 2 ^ d + i) (sub (m * 2 ^ d + i))) →
    IsThr f ε k m (graft sub d m)
  | 0, k, m, _, h => by simpa [graft] using h 0 (by norm_num)
  | d + 1, k, m, hanc, h => by
      have e : k + 1 + d = k + (d + 1) := by omega
      refine IsThr.node (by simpa using hanc 0 (by omega) 0 (by norm_num))
        (isThr_graft sub d (k + 1) (2 * m) (fun j hj i hi => ?_) (fun i hi => ?_))
        (isThr_graft sub d (k + 1) (2 * m + 1) (fun j hj i hi => ?_) (fun i hi => ?_))
      · have := hanc (j + 1) (by omega) i (by rw [pow_succ]; omega)
        rw [show k + 1 + j = k + (j + 1) by omega]
        convert this using 2; ring
      · have := h i (by rw [pow_succ]; omega)
        have e2 : m * 2 ^ (d + 1) + (i : ℤ) = 2 * m * 2 ^ d + i := by ring
        rw [e2] at this; rw [e]; exact this
      · have := hanc (j + 1) (by omega) (2 ^ j + i) (by rw [pow_succ]; omega)
        rw [show k + 1 + j = k + (j + 1) by omega]
        convert this using 2; push_cast; ring
      · have := h (2 ^ d + i) (by rw [pow_succ]; omega)
        have e2 : m * 2 ^ (d + 1) + ((2 ^ d + i : ℕ) : ℤ) = (2 * m + 1) * 2 ^ d + i := by
          push_cast; ring
        rw [e2] at this; rw [e]; exact this

lemma exists_pos_le_all {α : Type*} (S : Finset α) (g : α → ℝ) (hg : ∀ a ∈ S, 0 < g a) :
    ∃ ε₀ > 0, ∀ a ∈ S, ε₀ ≤ g a := by
  by_cases hS : S.Nonempty
  · obtain ⟨a₀, ha₀, hmin⟩ := S.exists_min_image g hS
    exact ⟨g a₀, hg a₀ ha₀, hmin⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    exact ⟨1, one_pos, by simp [hS]⟩

/-! ## The phase function -/

/-- the phase function `Φ(s) = ∑ᵢ √Aᵢ 2^{⌈s+aᵢ⌉-(s+aᵢ)}`, `aᵢ = log₄ Aᵢ` -/
noncomputable def phaseFn (A : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    Real.sqrt (A i) * (2 : ℝ) ^ ((⌈s + Real.logb 4 (A i)⌉ : ℝ) - (s + Real.logb 4 (A i)))

lemma two_rpow_logb_four {x : ℝ} (hx : 0 < x) : (2 : ℝ) ^ (Real.logb 4 x) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb,
    Real.log_rpow (by norm_num)]
  rw [show Real.log x / (2 * Real.log 2) = Real.logb 2 x * (1 / 2) by rw [Real.logb]; ring]
  rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx]

lemma phaseFn_periodic (A : ℕ → ℝ) (n : ℕ) : Function.Periodic (phaseFn A n) 1 := by
  intro s
  unfold phaseFn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show s + 1 + Real.logb 4 (A i) = (s + Real.logb 4 (A i)) + 1 by ring, Int.ceil_add_one]
  congr 2
  push_cast; ring

lemma sqrt_mul_sum_eq_phaseFn {A : ℕ → ℝ} {n : ℕ} (hA : ∀ i < n, 0 < A i) {ε : ℝ}
    (hε : 0 < ε) :
    Real.sqrt ε * ∑ i ∈ Finset.range n, (2 : ℝ) ^ ⌈Real.logb 4 (A i / ε)⌉ =
      phaseFn A n (-Real.logb 4 ε) := by
  unfold phaseFn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hAi := hA i (Finset.mem_range.mp hi)
  rw [Real.logb_div hAi.ne' hε.ne', show Real.logb 4 (A i) - Real.logb 4 ε =
    -Real.logb 4 ε + Real.logb 4 (A i) by ring]
  set c := ⌈-Real.logb 4 ε + Real.logb 4 (A i)⌉
  rw [← Real.rpow_intCast, Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num),
    Real.rpow_neg (by norm_num), two_rpow_logb_four hε, two_rpow_logb_four hAi]
  have h1 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have h2 : 0 < Real.sqrt (A i) := Real.sqrt_pos.mpr hAi
  field_simp

lemma phaseFn_not_const {A : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hA : ∀ i < n, 0 < A i) :
    ∃ s t, phaseFn A n s ≠ phaseFn A n t := by
  set a : ℕ → ℝ := fun i => Real.logb 4 (A i)
  obtain ⟨τ₀, hτ₀, hle⟩ := exists_pos_le_all (Finset.range n)
    (fun i => a i - (⌈a i⌉ - 1)) (fun i _ => by
      have := Int.ceil_lt_add_one (a i); simp only; linarith)
  set τ := τ₀ / 2
  have hτ : 0 < τ := by positivity
  have hceil : ∀ i ∈ Finset.range n, ⌈-τ + a i⌉ = ⌈0 + a i⌉ := by
    intro i hi
    have := hle i hi
    rw [zero_add, Int.ceil_eq_iff]
    constructor
    · simp only at this; linarith [show τ = τ₀ / 2 from rfl]
    · have := Int.le_ceil (a i); linarith
  refine ⟨-τ, 0, ne_of_gt ?_⟩
  have hsplit : phaseFn A n (-τ) = (2 : ℝ) ^ τ * phaseFn A n 0 := by
    unfold phaseFn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    change Real.sqrt (A i) * (2 : ℝ) ^ ((⌈-τ + a i⌉ : ℝ) - (-τ + a i)) =
      (2 : ℝ) ^ τ * (Real.sqrt (A i) * (2 : ℝ) ^ ((⌈0 + a i⌉ : ℝ) - (0 + a i)))
    rw [hceil i hi, mul_left_comm, ← Real.rpow_add (by norm_num)]
    congr 2; ring
  have hpos : 0 < phaseFn A n 0 := by
    unfold phaseFn
    refine Finset.sum_pos (fun i hi => ?_) ⟨0, Finset.mem_range.mpr hn⟩
    exact mul_pos (Real.sqrt_pos.mpr (hA i (Finset.mem_range.mp hi))) (by positivity)
  rw [hsplit]
  have : (1 : ℝ) < 2 ^ τ := Real.one_lt_rpow (by norm_num) hτ
  nlinarith

/-! ## Piecewise quadratics on a base mesh -/

section Piecewise

variable {f : ℝ → ℝ} {q₀ : ℕ} {κ : ℕ → ℝ} {A : ℕ → ℝ}

lemma pw_continuousOn
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ), f x = κ i / 2 * x ^ 2 + b * x + c) :
    ContinuousOn f (cellIcc 0 0) := by
  have hcover : cellIcc 0 0 ⊆ ⋃ i : Fin (2 ^ q₀), cellIcc q₀ ((i : ℕ) : ℤ) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := exists_desc_mem q₀ 0 0 x hx
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, by simpa using hxi⟩
  refine ContinuousOn.mono ?_ hcover
  refine (locallyFinite_of_finite _).continuousOn_iUnion (fun i => isClosed_Icc) (fun i => ?_)
  obtain ⟨b, c, h⟩ := hquad i i.2
  exact (show Continuous fun x : ℝ => κ i / 2 * x ^ 2 + b * x + c by fun_prop).continuousOn.congr h

lemma pw_A_pos (hκ : ∀ i < 2 ^ q₀, κ i ≠ 0)
    (hA : ∀ i, A i = |κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8) : ∀ i < 2 ^ q₀, 0 < A i := by
  intro i hi
  rw [hA]
  have := cL_lt_cR q₀ i
  have : 0 < |κ i| := abs_pos.mpr (hκ i hi)
  have : 0 < (cR q₀ i - cL q₀ i) ^ 2 := by nlinarith
  positivity

lemma pw_exact
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ), f x = κ i / 2 * x ^ 2 + b * x + c)
    (hA : ∀ i, A i = |κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8) (i : ℕ) (hi : i < 2 ^ q₀) (l : ℕ)
    (m' : ℤ) (hm' : m' / 2 ^ l = i) : locErr f (q₀ + l) m' = A i / 4 ^ l := by
  obtain ⟨b, c, h⟩ := hquad i hi
  have hsub := cell_sub_of_desc (k := q₀) (k' := q₀ + l) (m := i) (m' := m') (by omega)
    (by rw [show q₀ + l - q₀ = l by omega]; exact hm')
  rw [locErr_quadratic (fun x hx => h x (hsub hx)), cell_len_desc q₀ l i m', hA, div_pow,
    ← pow_mul, mul_comm l 2, pow_mul]
  norm_num
  ring

lemma pw_anc_pos (hκ : ∀ i < 2 ^ q₀, κ i ≠ 0)
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ), f x = κ i / 2 * x ^ 2 + b * x + c)
    (hA : ∀ i, A i = |κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8)
    (k' : ℕ) (hk : k' ≤ q₀) (j : ℕ) (hj : j < 2 ^ k') : 0 < locErr f k' j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hi : j * 2 ^ d < 2 ^ (k' + d) := by
    rw [pow_add]; exact Nat.mul_lt_mul_of_pos_right hj (by positivity)
  have hQ := pw_exact hquad hA (j * 2 ^ d) hi 0 ((j * 2 ^ d : ℕ) : ℤ) (by simp)
  simp only [add_zero, pow_zero, div_one] at hQ
  have hsubQ : cellIcc (k' + d) ((j * 2 ^ d : ℕ) : ℤ) ⊆ cellIcc k' j :=
    cell_sub_of_desc (by omega) (by
      rw [show k' + d - k' = d by omega]
      push_cast; simp)
  have hsub0 : cellIcc k' j ⊆ cellIcc 0 0 := cell_sub_of_desc (by omega) (by
    simp only [Nat.sub_zero]
    exact Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hj))
  exact locErr_pos_of_sub ((pw_continuousOn hquad).mono hsub0) hsubQ
    (hQ ▸ pw_A_pos hκ hA _ hi)

/-- the counting law below `ε₀` (with the depths `max(0,⌈log₄(Aᵢ/ε)⌉)`) -/
lemma pw_count (hκ : ∀ i < 2 ^ q₀, κ i ≠ 0)
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ), f x = κ i / 2 * x ^ 2 + b * x + c)
    (hA : ∀ i, A i = |κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → (∀ i < 2 ^ q₀, ε < A i) ∧
      (nThr f ε 0 0 : ℝ) = ∑ i ∈ Finset.range (2 ^ q₀), (2 : ℝ) ^ thrDepth (A i) ε := by
  obtain ⟨ε₁, hε₁, h1⟩ := exists_pos_le_all (Finset.range (2 ^ q₀)) A
    (fun i hi => pw_A_pos hκ hA i (Finset.mem_range.mp hi))
  obtain ⟨ε₂, hε₂, h2⟩ := exists_pos_le_all ((Finset.range q₀).sigma fun k' => Finset.range (2 ^ k'))
    (fun p => locErr f p.1 p.2) (fun p hp => by
      simp only [Finset.mem_sigma, Finset.mem_range] at hp
      exact pw_anc_pos hκ hquad hA p.1 hp.1.le p.2 hp.2)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε hε hlt => ⟨fun i hi => ?_, ?_⟩⟩
  · exact lt_of_lt_of_le (lt_of_lt_of_le hlt (min_le_left _ _)) (h1 i (Finset.mem_range.mpr hi))
  · set sub : ℤ → DShape := fun j => uniform (thrDepth (A j.toNat) ε)
    have hT : IsThr f ε 0 0 (graft sub q₀ 0) := by
      refine isThr_graft sub q₀ 0 0 (fun j hj i hi => ?_) (fun i hi => ?_)
      · have := h2 ⟨j, i⟩ (by simp [hj, hi])
        simp only [zero_mul, zero_add] at this ⊢
        exact lt_of_lt_of_le (lt_of_lt_of_le hlt (min_le_right _ _)) this
      · simp only [zero_mul, zero_add, sub, Int.toNat_natCast]
        have hAi := pw_A_pos hκ hA i hi
        apply isThr_uniform_of_exact _ q₀ i (A i)
          (fun l m' hm' => pw_exact hquad hA i hi l m' hm')
          ((le_eps_iff_thrDepth_le hAi hε _).mpr le_rfl)
        intro j hj
        exact not_le.mp fun h => by have := (le_eps_iff_thrDepth_le hAi hε j).mp h; omega
    have := (thrTree_spec ⟨_, hT⟩).unique hT
    unfold nThr
    rw [this, numLeaves_graft]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sub, numLeaves_uniform]

end Piecewise

/-- **Theorem 12.2 (contagem exata em uma malha diádica base)**: let `K = [0,1]` be split into the
cells `Qᵢ = J_{q₀,i}`, and let `f` be quadratic on each `Qᵢ` with `f'' = κᵢ ≠ 0` there; put
`Aᵢ = |κᵢ| |Qᵢ|²/8`. There is `ε₀ > 0` such that for `0 < ε < ε₀`,
`n_f(ε) = ∑ᵢ 2^{⌈log₄(Aᵢ/ε)⌉}` and `√ε n_f(ε) = Φ(-log₄ ε)`, where
`Φ(s) = ∑ᵢ √Aᵢ 2^{⌈s+aᵢ⌉-(s+aᵢ)}`, `aᵢ = log₄ Aᵢ`; `Φ` is `1`-periodic and not constant.
(The `C¹` hypothesis of the article is not needed: the pieces are given on closed cells.) -/
theorem piecewise_quadratic_count {f : ℝ → ℝ} {q₀ : ℕ} {κ : ℕ → ℝ}
    (hκ : ∀ i < 2 ^ q₀, κ i ≠ 0)
    (hquad : ∀ i : ℕ, i < 2 ^ q₀ → ∃ b c : ℝ, ∀ x ∈ cellIcc q₀ (i : ℤ), f x = κ i / 2 * x ^ 2 + b * x + c)
    {A : ℕ → ℝ} (hA : ∀ i, A i = |κ i| * (cR q₀ i - cL q₀ i) ^ 2 / 8) :
    (∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      (nThr f ε 0 0 : ℝ) = ∑ i ∈ Finset.range (2 ^ q₀), (2 : ℝ) ^ ⌈Real.logb 4 (A i / ε)⌉ ∧
      Real.sqrt ε * nThr f ε 0 0 = phaseFn A (2 ^ q₀) (-Real.logb 4 ε)) ∧
    Function.Periodic (phaseFn A (2 ^ q₀)) 1 ∧
    ∃ s t, phaseFn A (2 ^ q₀) s ≠ phaseFn A (2 ^ q₀) t := by
  have hApos := pw_A_pos hκ hA
  obtain ⟨ε₀, hε₀, hcount⟩ := pw_count hκ hquad hA
  have hcount' : ∀ ε, 0 < ε → ε < ε₀ →
      (nThr f ε 0 0 : ℝ) = ∑ i ∈ Finset.range (2 ^ q₀), (2 : ℝ) ^ ⌈Real.logb 4 (A i / ε)⌉ := by
    intro ε hε hlt
    obtain ⟨hlt', h⟩ := hcount ε hε hlt
    rw [h]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    have hpos : 0 ≤ ⌈Real.logb 4 (A i / ε)⌉ := by
      apply Int.ceil_nonneg
      apply Real.logb_nonneg (by norm_num)
      rw [le_div_iff₀ hε, one_mul]; exact (hlt' i hi').le
    unfold thrDepth
    rw [← zpow_natCast, Int.toNat_of_nonneg hpos]
  refine ⟨⟨ε₀, hε₀, fun ε hε hlt => ⟨hcount' ε hε hlt, ?_⟩⟩, phaseFn_periodic A _,
    phaseFn_not_const (by positivity) hApos⟩
  rw [hcount' ε hε hlt]
  exact sqrt_mul_sum_eq_phaseFn hApos hε

end Artigo
