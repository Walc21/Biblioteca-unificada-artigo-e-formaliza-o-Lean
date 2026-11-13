import RequestProject.Trees

/-!
# Uniform dyadic interpolants and density (Proposition 2.3)

The uniform tree of relative depth `r` whose leaves interpolate prescribed rational nodal
values, and the alternating-grid quantizer that makes adjacent nodal values distinct.
-/

namespace Artigo

open Finset Set LTree

/-- the atom on `J_{k,n}` interpolating the nodal values `V n`, `V (n+1)` (junk if equal). -/
def interpAtom (V : ℤ → ℚ) (k : ℕ) (n : ℤ) : Atom :=
  if h : V n ≠ V (n + 1) then Atom.ofEndpoints k n (V n) (V (n + 1)) h else ⟨k, n, 0, 1, one_ne_zero⟩

/-- the uniform tree of relative depth `r` at `J_{k,m}` interpolating `V` (indexed by the
node index at level `k + r`). -/
def uniformTree (V : ℤ → ℚ) : ℕ → ℕ → ℤ → LTree
  | 0, k, m => leaf (interpAtom V k m)
  | r + 1, k, m => node (uniformTree V r (k + 1) (2 * m)) (uniformTree V r (k + 1) (2 * m + 1))

/-- adjacent nodal values below `J_{k,m}` (at relative depth `r`) are distinct -/
def GoodVals (V : ℤ → ℚ) (r : ℕ) (m : ℤ) : Prop :=
  ∀ n : ℤ, 2 ^ r * m ≤ n → n < 2 ^ r * (m + 1) → V n ≠ V (n + 1)

lemma goodVals_left {V : ℤ → ℚ} {r : ℕ} {m : ℤ} (h : GoodVals V (r + 1) m) :
    GoodVals V r (2 * m) := by
  intro n h1 h2; apply h n <;> [rw [pow_succ]; rw [pow_succ]] <;> nlinarith

lemma goodVals_right {V : ℤ → ℚ} {r : ℕ} {m : ℤ} (h : GoodVals V (r + 1) m) :
    GoodVals V r (2 * m + 1) := by
  intro n h1 h2; apply h n <;> [rw [pow_succ]; rw [pow_succ]] <;> nlinarith

lemma interpAtom_lval {V : ℤ → ℚ} {k : ℕ} {n : ℤ} (h : V n ≠ V (n + 1)) :
    (interpAtom V k n).lval = V n := by
  simp only [interpAtom, dif_pos h]; exact Atom.ofEndpoints_lval _ _ _ _ _

lemma interpAtom_rval {V : ℤ → ℚ} {k : ℕ} {n : ℤ} (h : V n ≠ V (n + 1)) :
    (interpAtom V k n).rval = V (n + 1) := by
  simp only [interpAtom, dif_pos h]; exact Atom.ofEndpoints_rval _ _ _ _ _

@[simp] lemma interpAtom_k (V : ℤ → ℚ) (k : ℕ) (n : ℤ) : (interpAtom V k n).k = k := by
  unfold interpAtom; split_ifs <;> rfl

@[simp] lemma interpAtom_m (V : ℤ → ℚ) (k : ℕ) (n : ℤ) : (interpAtom V k n).m = n := by
  unfold interpAtom; split_ifs <;> rfl

lemma uniformTree_lval_rval (V : ℤ → ℚ) : ∀ (r k : ℕ) (m : ℤ), GoodVals V r m →
    (uniformTree V r k m).lval = V (2 ^ r * m) ∧ (uniformTree V r k m).rval = V (2 ^ r * (m + 1)) := by
  intro r
  induction r with
  | zero =>
    intro k m h
    have h0 := h m (by simp) (by simp)
    simp only [uniformTree, lval, rval, pow_zero, one_mul]
    exact ⟨interpAtom_lval h0, interpAtom_rval h0⟩
  | succ r ih =>
    intro k m h
    simp only [uniformTree, lval, rval]
    refine ⟨?_, ?_⟩
    · rw [(ih (k + 1) (2 * m) (goodVals_left h)).1, pow_succ]; ring_nf
    · rw [(ih (k + 1) (2 * m + 1) (goodVals_right h)).2, pow_succ]; ring_nf

lemma uniformTree_WF (V : ℤ → ℚ) : ∀ (r k : ℕ) (m : ℤ), GoodVals V r m →
    WF k m (uniformTree V r k m) := by
  intro r
  induction r with
  | zero => intro k m _; simp [uniformTree, WF]
  | succ r ih =>
    intro k m h
    refine ⟨ih _ _ (goodVals_left h), ih _ _ (goodVals_right h), ?_⟩
    rw [(uniformTree_lval_rval V r (k + 1) (2 * m) (goodVals_left h)).2,
      (uniformTree_lval_rval V r (k + 1) (2 * m + 1) (goodVals_right h)).1]

lemma uniformTree_leaves (V : ℤ → ℚ) : ∀ (r k : ℕ) (m : ℤ), ∀ a ∈ (uniformTree V r k m).leaves,
    ∃ n : ℤ, 2 ^ r * m ≤ n ∧ n < 2 ^ r * (m + 1) ∧ a = interpAtom V (k + r) n := by
  intro r
  induction r with
  | zero =>
    intro k m a ha
    simp [uniformTree, leaves] at ha
    exact ⟨m, by simp, by simp, by simp [ha]⟩
  | succ r ih =>
    intro k m a ha
    simp only [uniformTree, leaves, List.mem_append] at ha
    rcases ha with ha | ha
    · obtain ⟨n, h1, h2, rfl⟩ := ih _ _ a ha
      exact ⟨n, by rw [pow_succ]; nlinarith, by rw [pow_succ]; nlinarith, by
        rw [show k + 1 + r = k + (r + 1) by ring]⟩
    · obtain ⟨n, h1, h2, rfl⟩ := ih _ _ a ha
      exact ⟨n, by rw [pow_succ]; nlinarith, by rw [pow_succ]; nlinarith, by
        rw [show k + 1 + r = k + (r + 1) by ring]⟩

lemma uniformTree_numLeaves (V : ℤ → ℚ) : ∀ (r k : ℕ) (m : ℤ),
    (uniformTree V r k m).numLeaves = 2 ^ r := by
  intro r
  induction r with
  | zero => intro k m; simp [uniformTree, numLeaves, leaves]
  | succ r ih => intro k m; simp only [uniformTree]; rw [numLeaves_node, ih, ih, pow_succ]; ring

lemma uniformTree_depth (V : ℤ → ℚ) : ∀ (r k : ℕ) (m : ℤ), (uniformTree V r k m).depth = r := by
  intro r
  induction r with
  | zero => intro k m; rfl
  | succ r ih => intro k m; simp [uniformTree, depth, ih]

/-- the value of an interpolating atom inside its cell, as a convex combination. -/
lemma interpAtom_eval {V : ℤ → ℚ} {K : ℕ} {n : ℤ} (h : V n ≠ V (n + 1)) (x : ℝ) :
    (interpAtom V K n).eval x =
      (1 - 2 ^ K * (x - cL K n)) * (V n : ℝ) + 2 ^ K * (x - cL K n) * (V (n + 1) : ℝ) := by
  rw [Atom.eval_interp, interpAtom_lval h, interpAtom_rval h, interpAtom_k, interpAtom_m]; ring

lemma theta_mem {K : ℕ} {n : ℤ} {x : ℝ} (hx : x ∈ cellIcc K n) :
    0 ≤ 2 ^ K * (x - cL K n) ∧ 2 ^ K * (x - cL K n) ≤ 1 := by
  rw [cellIcc_eq] at hx
  have hK : (0 : ℝ) < 2 ^ K := by positivity
  constructor
  · exact mul_nonneg hK.le (by linarith [hx.1])
  · have : x - cL K n ≤ cR K n - cL K n := by linarith [hx.2]
    have e : cR K n - cL K n = 1 / 2 ^ K := by unfold cR cL; field_simp; ring
    rw [e] at this
    calc 2 ^ K * (x - cL K n) ≤ 2 ^ K * (1 / 2 ^ K) := mul_le_mul_of_nonneg_left this hK.le
      _ = 1 := by field_simp

/-- the linear interpolant on a cell, written with the same convex weight -/
lemma linInterp_cell (f : ℝ → ℝ) (K : ℕ) (n : ℤ) (x : ℝ) :
    linInterp f (cL K n) (cR K n) x =
      (1 - 2 ^ K * (x - cL K n)) * f (cL K n) + 2 ^ K * (x - cL K n) * f (cR K n) := by
  unfold linInterp
  have e : cR K n - cL K n = 1 / 2 ^ K := by unfold cR cL; field_simp; ring
  rw [e]; field_simp; ring

lemma cR_eq_cL_succ (K : ℕ) (n : ℤ) : cR K n = cL K (n + 1) := by
  unfold cR cL; push_cast; ring

/-- convex combinations are `max`-Lipschitz -/
lemma convex_comb_dist {θ A B A' B' η : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hA : |A - A'| ≤ η) (hB : |B - B'| ≤ η) :
    |((1 - θ) * A + θ * B) - ((1 - θ) * A' + θ * B')| ≤ η := by
  have e : ((1 - θ) * A + θ * B) - ((1 - θ) * A' + θ * B') = (1 - θ) * (A - A') + θ * (B - B') := by ring
  rw [e]
  calc |(1 - θ) * (A - A') + θ * (B - B')| ≤ |(1 - θ) * (A - A')| + |θ * (B - B')| := abs_add_le _ _
    _ = (1 - θ) * |A - A'| + θ * |B - B'| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h0]
    _ ≤ (1 - θ) * η + θ * η := by gcongr; linarith
    _ = η := by ring

/-- **Error of a uniform interpolant**: on a leaf cell `J_{K,n}` (`K = k+r`), if nodal values
are within `η` of `f`, the assembly differs from `f` by at most the interpolation error of `f`
on the cell plus `η`. -/
lemma uniformTree_error {V : ℤ → ℚ} {r k : ℕ} {m : ℤ} (hV : GoodVals V r m) (f : ℝ → ℝ) {η : ℝ}
    (hη : ∀ n : ℤ, 2 ^ r * m ≤ n → n ≤ 2 ^ r * (m + 1) → |f (cL (k + r) n) - V n| ≤ η) :
    ∀ x ∈ cellIcc k m, ∃ n : ℤ, 2 ^ r * m ≤ n ∧ n < 2 ^ r * (m + 1) ∧ x ∈ cellIcc (k + r) n ∧
      cellIcc (k + r) n ⊆ cellIcc k m ∧
      |f x - (uniformTree V r k m).eval k m x| ≤
        |f x - linInterp f (cL (k + r) n) (cR (k + r) n) x| + η := by
  intro x hx
  have hWF := uniformTree_WF V r k m hV
  obtain ⟨a, ha, hxa⟩ := exists_leaf_mem hWF x hx
  obtain ⟨n, h1, h2, rfl⟩ := uniformTree_leaves V r k m a ha
  have hsub := leaves_cell_sub hWF _ ha
  simp only [interpAtom_k, interpAtom_m] at hxa hsub
  refine ⟨n, h1, h2, hxa, hsub, ?_⟩
  rw [eval_leaf hWF _ ha x (by simpa using hxa), interpAtom_eval (hV n h1 h2) x]
  have hθ := theta_mem hxa
  have hc := convex_comb_dist hθ.1 hθ.2 (hη n h1 h2.le) (hη (n + 1) (by omega) (by omega))
  rw [← cR_eq_cL_succ] at hc
  rw [← linInterp_cell] at hc
  calc |f x - ((1 - 2 ^ (k + r) * (x - cL (k + r) n)) * (V n : ℝ) +
          2 ^ (k + r) * (x - cL (k + r) n) * (V (n + 1) : ℝ))|
      ≤ |f x - linInterp f (cL (k + r) n) (cR (k + r) n) x| +
        |linInterp f (cL (k + r) n) (cR (k + r) n) x - ((1 - 2 ^ (k + r) * (x - cL (k + r) n)) *
          (V n : ℝ) + 2 ^ (k + r) * (x - cL (k + r) n) * (V (n + 1) : ℝ))| := abs_sub_le _ _ _
    _ ≤ _ := by gcongr

/-! ## Alternating-grid quantization -/

/-- quantize `y` to the grid `δ (ℤ + p/2)` where `p = n mod 2`; ties resolved by `round`. -/
noncomputable def altQuant (δ : ℚ) (n : ℤ) (y : ℝ) : ℚ :=
  δ * ((round (y / δ - ((n % 2 : ℤ) : ℝ) / 2) : ℤ) + ((n % 2 : ℤ) : ℚ) / 2)

lemma altQuant_err {δ : ℚ} (hδ : 0 < δ) (n : ℤ) (y : ℝ) : |y - altQuant δ n y| ≤ δ / 2 := by
  unfold altQuant
  set p : ℝ := ((n % 2 : ℤ) : ℝ)
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hr := abs_sub_round (y / δ - p / 2)
  push_cast
  have e : y - δ * ((round (y / δ - p / 2) : ℝ) + p / 2) = δ * ((y / δ - p / 2) - round (y / δ - p / 2)) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_pos hδr]
  have : |y / ↑δ - p / 2 - ↑(round (y / ↑δ - p / 2))| ≤ 1 / 2 := hr
  nlinarith

/-- alternating grids are disjoint: adjacent quantized values differ. -/
lemma altQuant_ne {δ : ℚ} (hδ : 0 < δ) (n : ℤ) (y y' : ℝ) : altQuant δ n y ≠ altQuant δ (n + 1) y' := by
  unfold altQuant
  intro h
  have hδ0 : δ ≠ 0 := hδ.ne'
  have h2 := mul_left_cancel₀ hδ0 h
  have hp : (n % 2 = 0 ∧ (n + 1) % 2 = 1) ∨ (n % 2 = 1 ∧ (n + 1) % 2 = 0) := by omega
  rcases hp with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1] at h2
    push_cast at h2
    have : (2 : ℚ) * (round (↑y / ↑δ - ((0 : ℤ) : ℝ) / 2) : ℤ) = 2 * (round (↑y' / ↑δ - ((1 : ℤ) : ℝ) / 2) : ℤ) + 1 := by
      push_cast at h2 ⊢; linarith
    have : (2 * (round (y / δ - ((0 : ℤ) : ℝ) / 2) : ℤ) : ℤ) = 2 * (round (y' / δ - ((1 : ℤ) : ℝ) / 2) : ℤ) + 1 := by
      exact_mod_cast this
    omega
  · rw [h0, h1] at h2
    push_cast at h2
    have : (2 : ℚ) * (round (↑y / ↑δ - ((1 : ℤ) : ℝ) / 2) : ℤ) + 1 = 2 * (round (↑y' / ↑δ - ((0 : ℤ) : ℝ) / 2) : ℤ) := by
      push_cast at h2 ⊢; linarith
    have : (2 * (round (y / δ - ((1 : ℤ) : ℝ) / 2) : ℤ) : ℤ) + 1 = 2 * (round (y' / δ - ((0 : ℤ) : ℝ) / 2) : ℤ) := by
      exact_mod_cast this
    omega

/-- quantized nodal values of `f` at level `K` -/
noncomputable def quantVals (f : ℝ → ℝ) (δ : ℚ) (K : ℕ) (n : ℤ) : ℚ := altQuant δ n (f (cL K n))

lemma quantVals_good (f : ℝ → ℝ) {δ : ℚ} (hδ : 0 < δ) (K r : ℕ) (m : ℤ) :
    GoodVals (quantVals f δ K) r m := fun n _ _ => altQuant_ne hδ n _ _

lemma quantVals_err (f : ℝ → ℝ) {δ : ℚ} (hδ : 0 < δ) (K : ℕ) (n : ℤ) :
    |f (cL K n) - quantVals f δ K n| ≤ δ / 2 := altQuant_err hδ n _

/-! ## Proposition 2.3 (density) -/

/-- **Proposition 2.3 (density)**: assemblies are dense in `C(K)` for `K = J_{k₀,m₀}`. -/
theorem assemblies_dense {k₀ : ℕ} {m₀ : ℤ} {f : ℝ → ℝ} (hf : ContinuousOn f (cellIcc k₀ m₀))
    {ε : ℝ} (hε : 0 < ε) : ∃ T : LTree, WF k₀ m₀ T ∧ ∀ x ∈ cellIcc k₀ m₀, |f x - T.eval k₀ m₀ x| < ε := by
  have hK : IsCompact (cellIcc k₀ m₀) := isCompact_Icc
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hf)
    (ε / 3) (by linarith)
  -- choose the depth
  obtain ⟨r, hr⟩ : ∃ r : ℕ, 1 / (2 : ℝ) ^ (k₀ + r) < δ := by
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨r, lt_of_le_of_lt ?_ hr⟩
    rw [one_div_pow]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  -- choose the rational step
  obtain ⟨q, hq0, hq⟩ : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < ε / 3 := by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 3 by linarith)
    exact ⟨q, by exact_mod_cast h1, h2⟩
  set K := k₀ + r
  set V := quantVals f q K
  refine ⟨uniformTree V r k₀ m₀, uniformTree_WF V r k₀ m₀ (quantVals_good f hq0 K r m₀), ?_⟩
  intro x hx
  obtain ⟨n, h1, h2, hxn, hsub, herr⟩ := uniformTree_error (quantVals_good f hq0 K r m₀) f
    (η := q / 2) (fun n _ _ => quantVals_err f hq0 K n) x hx
  have hlen : cR K n - cL K n = 1 / 2 ^ K := by unfold cR cL; field_simp; ring
  rw [cellIcc_eq] at hxn
  have hlp : |f x - linInterp f (cL K n) (cR K n) x| < ε / 3 := by
    have hθ := theta_mem (K := K) (n := n) (x := x) (by rw [cellIcc_eq]; exact hxn)
    rw [linInterp_cell]
    have hxa : |f x - f (cL K n)| < ε / 3 := by
      have := hunif x hx (cL K n) (hsub (left_mem_Icc.mpr (cL_lt_cR K n).le))
        (by rw [Real.dist_eq, abs_of_nonneg (by linarith [hxn.1])]; linarith [hxn.2])
      rwa [Real.dist_eq] at this
    have hxb : |f x - f (cR K n)| < ε / 3 := by
      have := hunif x hx (cR K n) (hsub (right_mem_Icc.mpr (cL_lt_cR K n).le))
        (by rw [Real.dist_eq, abs_of_nonpos (by linarith [hxn.2])]; linarith [hxn.1])
      rwa [Real.dist_eq] at this
    have e : f x - ((1 - 2 ^ K * (x - cL K n)) * f (cL K n) + 2 ^ K * (x - cL K n) * f (cR K n)) =
        (1 - 2 ^ K * (x - cL K n)) * (f x - f (cL K n)) + 2 ^ K * (x - cL K n) * (f x - f (cR K n)) := by
      ring
    rw [e]
    calc _ ≤ |(1 - 2 ^ K * (x - cL K n)) * (f x - f (cL K n))| +
          |2 ^ K * (x - cL K n) * (f x - f (cR K n))| := abs_add_le _ _
      _ = (1 - 2 ^ K * (x - cL K n)) * |f x - f (cL K n)| +
          2 ^ K * (x - cL K n) * |f x - f (cR K n)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hθ.2]), abs_of_nonneg hθ.1]
      _ < ε / 3 := by
          rcases eq_or_lt_of_le hθ.1 with h0 | h0
          · rw [← h0]; simp; linarith
          · nlinarith
  have : (q : ℝ) / 2 < ε / 3 := by linarith
  calc |f x - (uniformTree V r k₀ m₀).eval k₀ m₀ x| ≤ _ := herr
    _ < ε / 3 + ε / 3 := by linarith
    _ < ε := by linarith

end Artigo
