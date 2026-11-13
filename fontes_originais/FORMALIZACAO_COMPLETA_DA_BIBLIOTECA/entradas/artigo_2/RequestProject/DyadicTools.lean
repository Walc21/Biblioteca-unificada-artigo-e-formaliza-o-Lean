import RequestProject.Dyadic

/-!
# Tools for Sections 11–12: leaves, grafting, weights and local error estimates
-/

namespace Artigo

open Set

/-! ## Integer index arithmetic for dyadic descendants -/

lemma int_div_pow_succ (m : ℤ) (n : ℕ) : m / 2 ^ (n + 1) = m / 2 ^ n / 2 := by
  rw [pow_succ, Int.ediv_ediv_of_nonneg (by positivity)]

lemma desc_index (m : ℤ) (d i : ℕ) (hi : i < 2 ^ d) : (m * 2 ^ d + i) / 2 ^ d = m := by
  have hpos : (0 : ℤ) < 2 ^ d := by positivity
  rw [add_comm, Int.add_mul_ediv_right _ _ hpos.ne']
  have : (i : ℤ) / 2 ^ d = 0 := Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hi)
  rw [this, zero_add]

/-- a descendant cell is contained in its ancestor -/
lemma cell_sub_of_desc {k k' : ℕ} {m m' : ℤ} (hk : k ≤ k') (hm : m' / 2 ^ (k' - k) = m) :
    cellIcc k' m' ⊆ cellIcc k m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp only [Nat.add_sub_cancel_left] at hm
  have hP : (0 : ℤ) < 2 ^ d := by positivity
  have h1 : m * 2 ^ d ≤ m' := hm ▸ Int.ediv_mul_le m' hP.ne'
  have h2 : m' < (m + 1) * 2 ^ d := hm ▸ Int.lt_ediv_add_one_mul_self m' hP
  have h1r : (m : ℝ) * 2 ^ d ≤ m' := by exact_mod_cast h1
  have h2r : (m' : ℝ) + 1 ≤ (m + 1) * 2 ^ d := by
    have : m' + 1 ≤ (m + 1) * 2 ^ d := h2
    exact_mod_cast this
  intro x hx
  simp only [cellIcc, mem_Icc, pow_add] at hx ⊢
  have hk2 : (0 : ℝ) < 2 ^ k := by positivity
  have hd2 : (0 : ℝ) < 2 ^ d := by positivity
  constructor
  · refine le_trans ?_ hx.1
    rw [div_le_div_iff₀ hk2 (by positivity)]
    nlinarith
  · refine hx.2.trans ?_
    rw [div_le_div_iff₀ (by positivity) hk2]
    nlinarith

lemma sum_range_pow_succ_split (g : ℤ → ℝ) (m : ℤ) (d : ℕ) :
    ∑ i ∈ Finset.range (2 ^ (d + 1)), g (m * 2 ^ (d + 1) + i) =
      ∑ i ∈ Finset.range (2 ^ d), g (2 * m * 2 ^ d + i) +
        ∑ i ∈ Finset.range (2 ^ d), g ((2 * m + 1) * 2 ^ d + i) := by
  rw [show 2 ^ (d + 1) = 2 ^ d + 2 ^ d by ring, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; push_cast; ring

/-! ## Leaves of a dyadic tree -/

namespace DShape

/-- every leaf cell `J_{k',m'}` of `T` (rooted at `J_{k,m}`) satisfies `P` -/
def AllLeaves (P : ℕ → ℤ → Prop) : DShape → ℕ → ℤ → Prop
  | leaf, k, m => P k m
  | node l r, k, m => AllLeaves P l (k + 1) (2 * m) ∧ AllLeaves P r (k + 1) (2 * m + 1)

lemma treeErr_le_iff {f : ℝ → ℝ} {ε : ℝ} : ∀ (T : DShape) (k : ℕ) (m : ℤ),
    T.treeErr f k m ≤ ε ↔ T.AllLeaves (fun k m => locErr f k m ≤ ε) k m
  | leaf, _, _ => Iff.rfl
  | node l r, k, m => by
      simp only [treeErr, AllLeaves, max_le_iff, treeErr_le_iff l, treeErr_le_iff r]

lemma AllLeaves.mono {P Q : ℕ → ℤ → Prop} (hPQ : ∀ k m, P k m → Q k m) :
    ∀ {T : DShape} {k : ℕ} {m : ℤ}, AllLeaves P T k m → AllLeaves Q T k m
  | leaf, k, m, h => hPQ k m h
  | node _ _, _, _, h => ⟨h.1.mono hPQ, h.2.mono hPQ⟩

/-- leaves are descendants of the root -/
lemma AllLeaves.desc {P : ℕ → ℤ → Prop} :
    ∀ {T : DShape} {k : ℕ} {m : ℤ}, AllLeaves P T k m →
      AllLeaves (fun k' m' => k ≤ k' ∧ m' / 2 ^ (k' - k) = m ∧ P k' m') T k m
  | leaf, k, m, h => ⟨le_rfl, by simp, h⟩
  | node _ _, k, m, h => by
      refine ⟨h.1.desc.mono ?_, h.2.desc.mono ?_⟩
      · rintro k' m' ⟨hk, hm, hP⟩
        refine ⟨by omega, ?_, hP⟩
        rw [show k' - k = (k' - (k + 1)) + 1 by omega, int_div_pow_succ, hm]; omega
      · rintro k' m' ⟨hk, hm, hP⟩
        refine ⟨by omega, ?_, hP⟩
        rw [show k' - k = (k' - (k + 1)) + 1 by omega, int_div_pow_succ, hm]; omega

/-- **weight lemma**: if `W` is subadditive along subdivision and every leaf has weight
`≤ 1`, then the number of leaves is at least the weight of the root. -/
lemma numLeaves_ge_of_weight (W : ℕ → ℤ → ℝ)
    (hW : ∀ k m, W k m ≤ W (k + 1) (2 * m) + W (k + 1) (2 * m + 1)) :
    ∀ {T : DShape} {k : ℕ} {m : ℤ}, AllLeaves (fun k m => W k m ≤ 1) T k m →
      W k m ≤ T.numLeaves
  | leaf, k, m, h => by simpa [numLeaves] using h
  | node l r, k, m, h => by
      have h1 := numLeaves_ge_of_weight W hW h.1
      have h2 := numLeaves_ge_of_weight W hW h.2
      simp only [numLeaves, Nat.cast_add]
      linarith [hW k m]

/-- grafting trees `sub j` below every level-`(k+d)` descendant of the root -/
def graft (sub : ℤ → DShape) : ℕ → ℤ → DShape
  | 0, m => sub m
  | d + 1, m => node (graft sub d (2 * m)) (graft sub d (2 * m + 1))

lemma numLeaves_graft (sub : ℤ → DShape) : ∀ (d : ℕ) (m : ℤ),
    ((graft sub d m).numLeaves : ℝ) =
      ∑ i ∈ Finset.range (2 ^ d), ((sub (m * 2 ^ d + i)).numLeaves : ℝ)
  | 0, m => by simp [graft]
  | d + 1, m => by
      rw [sum_range_pow_succ_split (fun j => ((sub j).numLeaves : ℝ))]
      simp only [graft, numLeaves, Nat.cast_add, numLeaves_graft sub d]

lemma allLeaves_graft {P : ℕ → ℤ → Prop} (sub : ℤ → DShape) : ∀ (d k : ℕ) (m : ℤ),
    (∀ i : ℕ, i < 2 ^ d → AllLeaves P (sub (m * 2 ^ d + i)) (k + d) (m * 2 ^ d + i)) →
      AllLeaves P (graft sub d m) k m
  | 0, k, m, h => by simpa [graft] using h 0 (by norm_num)
  | d + 1, k, m, h => by
      have e : k + 1 + d = k + (d + 1) := by omega
      refine ⟨allLeaves_graft sub d (k + 1) (2 * m) fun i hi => ?_,
        allLeaves_graft sub d (k + 1) (2 * m + 1) fun i hi => ?_⟩
      · have := h i (by rw [pow_succ]; omega)
        have e2 : m * 2 ^ (d + 1) + (i : ℤ) = 2 * m * 2 ^ d + i := by ring
        rw [e2] at this
        rw [e]; exact this
      · have := h (2 ^ d + i) (by rw [pow_succ]; omega)
        have e2 : m * 2 ^ (d + 1) + ((2 ^ d + i : ℕ) : ℤ) = (2 * m + 1) * 2 ^ d + i := by
          push_cast; ring
        rw [e2] at this
        rw [e]; exact this

lemma graft_leaf_eq_uniform : ∀ (r : ℕ) (m : ℤ), graft (fun _ => leaf) r m = uniform r
  | 0, _ => rfl
  | r + 1, m => by simp only [graft, uniform, graft_leaf_eq_uniform r]

lemma allLeaves_uniform {P : ℕ → ℤ → Prop} (r k : ℕ) (m : ℤ)
    (h : ∀ i : ℕ, i < 2 ^ r → P (k + r) (m * 2 ^ r + i)) : AllLeaves P (uniform r) k m := by
  rw [← graft_leaf_eq_uniform r m]
  exact allLeaves_graft _ r k m fun i hi => h i hi

end DShape

/-! ## Weights of cells -/

/-- the weight of the cell `J_{k,m}` attached to a level-`q` density `w`:
`∫_J w`, where `w` is constant `= w j` on `J_{q,j}` -/
noncomputable def cellW (q : ℕ) (w : ℤ → ℝ) (k : ℕ) (m : ℤ) : ℝ :=
  if q ≤ k then w (m / 2 ^ (k - q)) / 2 ^ k
  else ∑ i ∈ Finset.range (2 ^ (q - k)), w (m * 2 ^ (q - k) + i) / 2 ^ q

lemma cellW_add (q : ℕ) (w : ℤ → ℝ) (k : ℕ) (m : ℤ) :
    cellW q w k m = cellW q w (k + 1) (2 * m) + cellW q w (k + 1) (2 * m + 1) := by
  unfold cellW
  by_cases hk : q ≤ k
  · rw [if_pos hk, if_pos (by omega), if_pos (by omega)]
    have e1 : 2 * m / 2 ^ (k + 1 - q) = m / 2 ^ (k - q) := by
      rw [show k + 1 - q = (k - q) + 1 by omega, pow_succ', ← Int.ediv_ediv_of_nonneg (by norm_num)]
      congr 1; omega
    have e2 : (2 * m + 1) / 2 ^ (k + 1 - q) = m / 2 ^ (k - q) := by
      rw [show k + 1 - q = (k - q) + 1 by omega, pow_succ', ← Int.ediv_ediv_of_nonneg (by norm_num)]
      congr 1; omega
    rw [e1, e2, pow_succ]; ring
  · rw [if_neg hk]
    by_cases hk1 : q = k + 1
    · subst hk1
      rw [if_pos le_rfl, if_pos le_rfl]
      simp [Finset.sum_range_succ]
      ring_nf
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [show q - k = (q - (k + 1)) + 1 by omega]
      exact sum_range_pow_succ_split (fun j => w j / 2 ^ q) m _

/-! ## Local error estimates -/

/-- if `|f''| ≥ μ > 0` on `J` (hence `f''` has constant sign), then `e_f(J) ≥ μ |J|²/8` -/
lemma locErr_ge_of_abs_deriv2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k : ℕ} {m : ℤ} {μ : ℝ}
    (hμ0 : 0 < μ) (hμ : ∀ y ∈ cellIcc k m, μ ≤ |deriv (deriv f) y|) :
    μ / 8 * (cR k m - cL k m) ^ 2 ≤ locErr f k m := by
  have hab := cL_lt_cR k m
  obtain ⟨hd, hd2⟩ := C2_hasDeriv hf
  have hcont2 := (C2_continuous_deriv2 hf).continuousOn (s := cellIcc k m)
  have hmid : (cL k m + cR k m) / 2 ∈ cellIcc k m := by
    rw [cellIcc_eq]; exact ⟨by linarith, by linarith⟩
  refine le_trans ?_ (le_locErr hf.continuous.continuousOn hmid)
  -- constant sign
  have hsign : (∀ y ∈ cellIcc k m, μ ≤ deriv (deriv f) y) ∨
      (∀ y ∈ cellIcc k m, deriv (deriv f) y ≤ -μ) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨y1, hy1, h1⟩, ⟨y2, hy2, h2⟩⟩ := hcon
    have p1 : deriv (deriv f) y1 < 0 := by
      have := hμ y1 hy1
      rcases le_or_gt 0 (deriv (deriv f) y1) with h | h
      · rw [abs_of_nonneg h] at this; linarith
      · exact h
    have p2 : 0 < deriv (deriv f) y2 := by
      have := hμ y2 hy2
      rcases le_or_gt (deriv (deriv f) y2) 0 with h | h
      · rw [abs_of_nonpos h] at this; linarith
      · exact h
    obtain ⟨z, hz, hz0⟩ := isPreconnected_Icc.intermediate_value hy1 hy2 hcont2
      (show (0 : ℝ) ∈ Icc (deriv (deriv f) y1) (deriv (deriv f) y2) from ⟨p1.le, p2.le⟩)
    have := hμ z hz
    rw [hz0, abs_zero] at this; linarith
  have e : ((cL k m + cR k m) / 2 - cL k m) * ((cL k m + cR k m) / 2 - cR k m) =
      -((cR k m - cL k m) ^ 2 / 4) := by ring
  rcases hsign with h | h
  · have := interp_upper_of_lower hab hd hd2 h _ hmid
    rw [e] at this
    refine le_trans ?_ (neg_le_abs _)
    nlinarith
  · have := interp_lower_of_upper hab hd hd2 h _ hmid
    rw [e] at this
    refine le_trans ?_ (le_abs_self _)
    nlinarith

/-- if `f` is not affine on a subcell, it is not affine on the cell: `e_f(J') > 0 ⇒ e_f(J) > 0` -/
lemma locErr_pos_of_sub {f : ℝ → ℝ} {k k' : ℕ} {m m' : ℤ} (hf : ContinuousOn f (cellIcc k m))
    (hsub : cellIcc k' m' ⊆ cellIcc k m) (hpos : 0 < locErr f k' m') : 0 < locErr f k m := by
  by_contra hcon
  have h0 : ∀ x ∈ cellIcc k m, f x = linInterp f (cL k m) (cR k m) x := by
    intro x hx
    have := ((locErr_le_iff hf).mp (not_lt.mp hcon)) x hx
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  have hab := cL_lt_cR k m
  have hab' := cL_lt_cR k' m'
  have ha' : cL k' m' ∈ cellIcc k m := hsub (by rw [cellIcc_eq]; exact left_mem_Icc.mpr hab'.le)
  have hb' : cR k' m' ∈ cellIcc k m := hsub (by rw [cellIcc_eq]; exact right_mem_Icc.mpr hab'.le)
  have : locErr f k' m' ≤ 0 := by
    rw [locErr_le_iff (hf.mono hsub)]
    intro x hx
    rw [h0 x (hsub hx)]
    simp only [linInterp]
    rw [h0 _ ha', h0 _ hb']
    simp only [linInterp]
    have h1 : cR k m - cL k m ≠ 0 := sub_ne_zero.mpr hab.ne'
    have h2 : cR k' m' - cL k' m' ≠ 0 := sub_ne_zero.mpr hab'.ne'
    rw [abs_nonpos_iff, sub_eq_zero]
    field_simp
    ring
  linarith

/-- the local error of a quadratic with leading coefficient `κ/2` on `J` is `|κ| |J|²/8` -/
lemma locErr_quadratic {f : ℝ → ℝ} {k : ℕ} {m : ℤ} {κ b c : ℝ}
    (hq : ∀ x ∈ cellIcc k m, f x = κ / 2 * x ^ 2 + b * x + c) :
    locErr f k m = |κ| / 8 * (cR k m - cL k m) ^ 2 := by
  have hab := cL_lt_cR k m
  have hcont : ContinuousOn f (cellIcc k m) :=
    (show Continuous fun x : ℝ => κ / 2 * x ^ 2 + b * x + c by fun_prop).continuousOn.congr hq
  have ha : cL k m ∈ cellIcc k m := by rw [cellIcc_eq]; exact left_mem_Icc.mpr hab.le
  have hb : cR k m ∈ cellIcc k m := by rw [cellIcc_eq]; exact right_mem_Icc.mpr hab.le
  have key : ∀ x ∈ cellIcc k m, f x - linInterp f (cL k m) (cR k m) x =
      κ / 2 * ((x - cL k m) * (x - cR k m)) := by
    intro x hx
    rw [linInterp, hq x hx, hq _ ha, hq _ hb]
    have h1 : cR k m - cL k m ≠ 0 := sub_ne_zero.mpr hab.ne'
    field_simp
    ring
  apply le_antisymm
  · rw [locErr_le_iff hcont]
    intro x hx
    rw [key x hx, abs_mul, abs_div, abs_two]
    have hx' : x ∈ Icc (cL k m) (cR k m) := hx
    obtain ⟨p0, p1⟩ := prod_bound hx'
    have : |(x - cL k m) * (x - cR k m)| = (x - cL k m) * (cR k m - x) := by
      rw [show (x - cL k m) * (x - cR k m) = -((x - cL k m) * (cR k m - x)) by ring, abs_neg,
        abs_of_nonneg p0]
    rw [this]
    have := abs_nonneg κ
    nlinarith
  · have hmid : (cL k m + cR k m) / 2 ∈ cellIcc k m := by
      rw [cellIcc_eq]; exact ⟨by linarith, by linarith⟩
    refine le_trans (le_of_eq ?_) (le_locErr hcont hmid)
    rw [key _ hmid]
    rw [show κ / 2 * (((cL k m + cR k m) / 2 - cL k m) * ((cL k m + cR k m) / 2 - cR k m)) =
      -(κ * ((cR k m - cL k m) ^ 2 / 8)) by ring, abs_neg, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (cR k m - cL k m) ^ 2 / 8 by positivity)]
    ring

/-- a uniform tree whose leaves all have local error `≤ ε` is feasible -/
lemma treeErr_uniform_le {f : ℝ → ℝ} {ε : ℝ} (r k : ℕ) (m : ℤ)
    (h : ∀ i : ℕ, i < 2 ^ r → locErr f (k + r) (m * 2 ^ r + i) ≤ ε) :
    (DShape.uniform r).treeErr f k m ≤ ε :=
  (DShape.treeErr_le_iff _ _ _).mpr (DShape.allLeaves_uniform r k m h)

/-- cells of level `k + r` below `J_{k,m}` have length `|J_{k,m}| / 2^r` -/
lemma cell_len_desc (k r : ℕ) (m m' : ℤ) :
    cR (k + r) m' - cL (k + r) m' = (cR k m - cL k m) / 2 ^ r := by
  rw [cell_len, cell_len, pow_add]; field_simp

end Artigo
