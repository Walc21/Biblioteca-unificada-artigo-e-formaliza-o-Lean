import RequestProject.DyadicTools
import RequestProject.Sawtooth

/-!
# Section 12 — Exact cases: constant curvature (Theorem 12.1)
-/

namespace Artigo

open Set Filter Topology DShape

/-- the threshold depth `max(0, ⌈log₄(A/ε)⌉)` -/
noncomputable def thrDepth (A ε : ℝ) : ℕ := (⌈Real.logb 4 (A / ε)⌉).toNat

lemma le_eps_iff_thrDepth_le {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) (j : ℕ) :
    A / 4 ^ j ≤ ε ↔ thrDepth A ε ≤ j := by
  unfold thrDepth
  rw [Int.toNat_le, Int.ceil_le, Int.cast_natCast,
    Real.logb_le_iff_le_rpow (by norm_num) (div_pos hA hε), Real.rpow_natCast,
    div_le_iff₀ (by positivity), div_le_iff₀ hε, mul_comm]

/-- if every level-`(k+j)` descendant of `J_{k,m}` has local error exactly `A/4^j`, the threshold
tree is the uniform tree of the first depth `D` with `A/4^D ≤ ε` -/
lemma isThr_uniform_of_exact {f : ℝ → ℝ} {ε : ℝ} : ∀ (D k : ℕ) (m : ℤ) (A : ℝ),
    (∀ (j : ℕ) (m' : ℤ), m' / 2 ^ j = m → locErr f (k + j) m' = A / 4 ^ j) →
    A / 4 ^ D ≤ ε → (∀ j < D, ε < A / 4 ^ j) → IsThr f ε k m (uniform D)
  | 0, k, m, A, hA, hD, _ => IsThr.leaf (by simpa using (hA 0 m (by simp)) ▸ hD)
  | D + 1, k, m, A, hA, hD, hlt => by
      have h0 : locErr f k m = A := by simpa using hA 0 m (by simp)
      have hchild : ∀ m₁ : ℤ, m₁ / 2 = m → ∀ (j : ℕ) (m' : ℤ), m' / 2 ^ j = m₁ →
          locErr f (k + 1 + j) m' = A / 4 / 4 ^ j := by
        intro m₁ hm₁ j m' hm'
        have := hA (j + 1) m' (by rw [int_div_pow_succ, hm', hm₁])
        rw [show k + 1 + j = k + (j + 1) by omega, this, pow_succ]; ring
      refine IsThr.node (by have := hlt 0 (by omega); simpa [h0] using this)
        (isThr_uniform_of_exact D (k + 1) (2 * m) (A / 4) (hchild _ (by omega)) ?_ ?_)
        (isThr_uniform_of_exact D (k + 1) (2 * m + 1) (A / 4) (hchild _ (by omega)) ?_ ?_)
      · rw [div_div, ← pow_succ']; exact hD
      · intro j hj; rw [div_div, ← pow_succ']; exact hlt (j + 1) (by omega)
      · rw [div_div, ← pow_succ']; exact hD
      · intro j hj; rw [div_div, ← pow_succ']; exact hlt (j + 1) (by omega)

/-- a nonnegative quantity with the same upper sets as a positive constant equals it -/
lemma eq_of_forall_pos_le_iff {E c : ℝ} (hE : 0 ≤ E) (hc : 0 < c)
    (h : ∀ ε > 0, E ≤ ε ↔ c ≤ ε) : E = c := by
  apply le_antisymm ((h c hc).mpr le_rfl)
  by_contra hlt
  push_neg at hlt
  have := (h ((E + c) / 2) (by linarith)).mp (by linarith)
  linarith

/-- **Theorem 12.1 (lei exata e intervalo de acumulação)**: if `K = J_{k₀,m₀}` has length `L`,
`q ∈ C²` and `q'' ≡ κ ≠ 0` on `K`, put `A = |κ| L²/8`. Then
`E_N^{dia}(q)_∞ = A 4^{-⌊log₂ N⌋}` for every `N ≥ 1` (`Nat.log 2 N = ⌊log₂ N⌋`); the set of
accumulation values of `N² E_N^{dia}(q)_∞` is exactly `[A, 4A]`,
`liminf = A`, `limsup = 4A`, and in particular `N² E_N^{dia}(q)_∞` has no limit.
Dually, `n_q(ε) = 2^{max(0, ⌈log₄(A/ε)⌉)}` for every `ε > 0`. -/
theorem quadratic_dyadic_constant {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) {k₀ : ℕ} {m₀ : ℤ}
    {κ : ℝ} (hκ : κ ≠ 0) (hκq : ∀ x ∈ cellIcc k₀ m₀, deriv (deriv q) x = κ)
    {A : ℝ} (hA : A = |κ| * (cR k₀ m₀ - cL k₀ m₀) ^ 2 / 8) :
    (∀ N : ℕ, 1 ≤ N → Edia q k₀ m₀ N = A / 4 ^ Nat.log 2 N) ∧
    {x | MapClusterPt x atTop (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N)} = Icc A (4 * A) ∧
    liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop = A ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop = 4 * A ∧
    (¬ ∃ c, Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) atTop (𝓝 c)) ∧
    (∀ ε > 0, nThr q ε k₀ m₀ = 2 ^ (⌈Real.logb 4 (A / ε)⌉).toNat) := by
  have hApos : 0 < A := by
    rw [hA]; have := cL_lt_cR k₀ m₀
    have : 0 < |κ| := abs_pos.mpr hκ
    have : 0 < (cR k₀ m₀ - cL k₀ m₀) ^ 2 := by nlinarith
    positivity
  have hcont : ContinuousOn q (cellIcc k₀ m₀) := hq.continuous.continuousOn
  -- exact local errors
  have hexact : ∀ (j : ℕ) (m' : ℤ), m' / 2 ^ j = m₀ → locErr q (k₀ + j) m' = A / 4 ^ j := by
    intro j m' hm'
    have hsub := cell_sub_of_desc (k := k₀) (k' := k₀ + j) (m := m₀) (m' := m') (by omega)
      (by rw [show k₀ + j - k₀ = j by omega]; exact hm')
    have := locErr_near hq (k := k₀ + j) (m := m') (c := κ) (w := 0)
      (fun y hy => by rw [hκq y (hsub hy), sub_self, abs_zero])
    rw [zero_div, zero_mul, abs_nonpos_iff, sub_eq_zero] at this
    rw [this, cell_len_desc k₀ j m₀ m', hA, div_pow, ← pow_mul, mul_comm j 2, pow_mul]
    ring
  -- the threshold tree is uniform
  have hthr : ∀ ε > 0, nThr q ε k₀ m₀ = 2 ^ thrDepth A ε := by
    intro ε hε
    have hT : IsThr q ε k₀ m₀ (uniform (thrDepth A ε)) :=
      isThr_uniform_of_exact _ k₀ m₀ A hexact ((le_eps_iff_thrDepth_le hApos hε _).mpr le_rfl)
        (fun j hj => not_le.mp fun h => by
          have := (le_eps_iff_thrDepth_le hApos hε j).mp h; omega)
    have := (thrTree_spec ⟨_, hT⟩).unique hT
    unfold nThr; rw [this, numLeaves_uniform]
  -- the exact law
  have hlaw : ∀ N : ℕ, 1 ≤ N → Edia q k₀ m₀ N = A / 4 ^ Nat.log 2 N := by
    intro N hN
    apply eq_of_forall_pos_le_iff (Edia_nonneg N) (by positivity)
    intro ε hε
    rw [(threshold_optimality hcont hε).2.2.2.2.2 N hN, hthr ε hε,
      le_eps_iff_thrDepth_le hApos hε, Nat.le_log_iff_pow_le (by norm_num) (by omega)]
  have hsaw := sawtooth (u := fun N : ℕ => (N : ℝ) ^ 2 * Edia q k₀ m₀ N) (M := 1) le_rfl hApos
    (by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [hlaw N hN, Nat.div_one]; ring)
  simp only [Nat.cast_one, one_pow, one_mul, mul_one] at hsaw
  obtain ⟨h1, h2, h3⟩ := hsaw
  refine ⟨hlaw, h1, h2, h3, ?_, fun ε hε => hthr ε hε⟩
  rintro ⟨c, hc⟩
  have e1 := hc.liminf_eq
  have e2 := hc.limsup_eq
  rw [h2] at e1; rw [h3] at e2
  linarith
