module
public import Unified.Consolidado.Lib.Library
@[expose] public section

/-!
# Lemma 7.11: elementary height calculus
-/

open Finset

namespace Dyadic.Lib

lemma ratHeight_intDiv_le (n : ℤ) (d : ℕ) (hd : 0 < d) :
    ratHeight ((n : ℚ) / (d : ℚ)) ≤ max n.natAbs d := by
  have heq : ((n : ℚ) / (d : ℚ)) = Rat.divInt n d := by
    rw [Rat.divInt_eq_div]; push_cast; rfl
  unfold ratHeight
  rw [heq]
  apply max_le
  · rcases eq_or_ne n 0 with h | h
    · subst h; simp
    · have := Rat.num_dvd n (b := (d : ℤ)) (by exact_mod_cast hd.ne')
      have := Int.natAbs_le_of_dvd_ne_zero this h
      exact this.trans (le_max_left _ _)
  · have := Rat.den_dvd n d
    have h2 : ((Rat.divInt n d).den : ℤ) ≤ d := Int.le_of_dvd (by exact_mod_cast hd) this
    exact (by exact_mod_cast h2 : (Rat.divInt n d).den ≤ d).trans (le_max_right _ _)

lemma rat_eq_num_div_den (r : ℚ) : r = ((r.num : ℤ) : ℚ) / ((r.den : ℕ) : ℚ) := by
  rw [Rat.num_div_den]

/-- **Lemma 7.11**, eq. (59), sum: `ht(r + s) ≤ 2 ht(r) ht(s)`. -/
theorem ratHeight_add_le (r s : ℚ) : ratHeight (r + s) ≤ 2 * ratHeight r * ratHeight s := by
  have e : r + s = ((r.num * s.den + s.num * r.den : ℤ) : ℚ) / ((r.den * s.den : ℕ) : ℚ) := by
    conv_lhs => rw [rat_eq_num_div_den r, rat_eq_num_div_den s]
    have h1 : (r.den : ℚ) ≠ 0 := by positivity
    have h2 : (s.den : ℚ) ≠ 0 := by positivity
    push_cast; field_simp
  rw [e]
  refine (ratHeight_intDiv_le _ _ (Nat.mul_pos r.den_pos s.den_pos)).trans ?_
  have hr1 := natAbs_num_le_ratHeight r
  have hr2 := den_le_ratHeight r
  have hs1 := natAbs_num_le_ratHeight s
  have hs2 := den_le_ratHeight s
  apply max_le
  · refine (Int.natAbs_add_le _ _).trans ?_
    rw [Int.natAbs_mul, Int.natAbs_mul]
    simp only [Int.natAbs_natCast]
    have := Nat.mul_le_mul hr1 hs2
    have := Nat.mul_le_mul hs1 hr2
    nlinarith
  · have := Nat.mul_le_mul hr2 hs2
    have := one_le_ratHeight r
    have := one_le_ratHeight s
    nlinarith

/-- **Lemma 7.11**, eq. (59), product: `ht(r s) ≤ ht(r) ht(s)`. -/
theorem ratHeight_mul_le (r s : ℚ) : ratHeight (r * s) ≤ ratHeight r * ratHeight s := by
  have e : r * s = ((r.num * s.num : ℤ) : ℚ) / ((r.den * s.den : ℕ) : ℚ) := by
    conv_lhs => rw [rat_eq_num_div_den r, rat_eq_num_div_den s]
    have h1 : (r.den : ℚ) ≠ 0 := by positivity
    have h2 : (s.den : ℚ) ≠ 0 := by positivity
    push_cast; field_simp
  rw [e]
  refine (ratHeight_intDiv_le _ _ (Nat.mul_pos r.den_pos s.den_pos)).trans ?_
  apply max_le
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (natAbs_num_le_ratHeight r) (natAbs_num_le_ratHeight s)
  · exact Nat.mul_le_mul (den_le_ratHeight r) (den_le_ratHeight s)

@[simp] lemma ratHeight_neg (r : ℚ) : ratHeight (-r) = ratHeight r := by
  simp [ratHeight]

/-- **Lemma 7.11**, eq. (59), difference: `ht(r - s) ≤ 2 ht(r) ht(s)`. -/
theorem ratHeight_sub_le (r s : ℚ) : ratHeight (r - s) ≤ 2 * ratHeight r * ratHeight s := by
  rw [sub_eq_add_neg]
  simpa using ratHeight_add_le r (-s)

lemma ratHeight_dyadic_le (u : ℤ) (k : ℕ) : ratHeight ((u : ℚ) / 2 ^ k) ≤ max u.natAbs (2 ^ k) := by
  have := ratHeight_intDiv_le u (2 ^ k) (by positivity)
  simpa using this

/-- Reduced form of a dyadic number `u/2^k`: numerator bounded by `|u|`, denominator `2^j` with
`j ≤ k`. -/
lemma dyadic_reduced (u : ℤ) (k : ℕ) :
    ((u : ℚ) / 2 ^ k).num.natAbs ≤ u.natAbs ∧ ∃ j ≤ k, ((u : ℚ) / 2 ^ k).den = 2 ^ j := by
  have heq : ((u : ℚ) / 2 ^ k) = Rat.divInt u ((2 ^ k : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]; push_cast; rfl
  rw [heq]
  constructor
  · rcases eq_or_ne u 0 with h | h
    · subst h; simp
    · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd u (by positivity)) h
  · have := Rat.den_dvd u ((2 ^ k : ℕ) : ℤ)
    have h2 : (Rat.divInt u ((2 ^ k : ℕ) : ℤ)).den ∣ 2 ^ k := by exact_mod_cast this
    exact (Nat.dvd_prime_pow Nat.prime_two).1 h2

lemma Atom.ratHeight_left_le (a : Atom) {H : ℕ} (h : a.height ≤ H) : ratHeight a.left ≤ 2 ^ H := by
  rw [Atom.height_le_iff] at h
  unfold Atom.left
  refine (ratHeight_dyadic_le a.m a.k).trans (max_le ?_ ?_)
  · have : H < 2 ^ H := Nat.lt_two_pow_self
    omega
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma Atom.ratHeight_right_le (a : Atom) {H : ℕ} (h : a.height ≤ H) :
    ratHeight a.right ≤ 2 ^ H := by
  rw [Atom.height_le_iff] at h
  unfold Atom.right
  have : ((a.m : ℚ) + 1) = ((a.m + 1 : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  refine (ratHeight_dyadic_le (a.m + 1) a.k).trans (max_le ?_ ?_)
  · have : H < 2 ^ H := Nat.lt_two_pow_self
    omega
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma Atom.ratHeight_center_le (a : Atom) {H : ℕ} (h : a.height ≤ H) :
    ratHeight a.center ≤ 2 ^ H := by
  rw [Atom.height_le_iff] at h
  unfold Atom.center
  have : (2 * (a.m : ℚ) + 1) = ((2 * a.m + 1 : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  refine (ratHeight_dyadic_le (2 * a.m + 1) (a.k + 1)).trans (max_le ?_ ?_)
  · have h1 : H < 2 ^ H := Nat.lt_two_pow_self
    have h2 : 2 * H ≤ 2 ^ H := by
      have h3 : H - 1 < 2 ^ (H - 1) := Nat.lt_two_pow_self
      have h4 : 2 ^ H = 2 * 2 ^ (H - 1) := by
        rw [← pow_succ']; congr 1; omega
      omega
    omega
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Lemma 7.11** (height calculus for assemblies). Let `a, b` be atoms of height at most `H`
(e.g. two consecutive leaves of an assembly, `b` following `a`).  Then:
* every node (cell endpoint) `t = u 2^{-k'}` in reduced form has `|u| ≤ H` and `k' ≤ H`;
* eq. (60): `ht(s_b - s_a) ≤ 2H²`;
* eq. (61): `ht(s_b t_b) ≤ H 2^H` where `t_b` is the left node of `b`;
* eq. (62): `ht(y₀ - s x₀) ≤ 2^{H+1} H²` for the intercept of `a`. -/
theorem height_calculus {H : ℕ} (a b : Atom) (ha : a.height ≤ H) (hb : b.height ≤ H) :
    (∀ t ∈ ({a.left, a.right} : Set ℚ), t.num.natAbs ≤ H ∧ ∃ k' ≤ H, t.den = 2 ^ k') ∧
    ratHeight (b.s - a.s) ≤ 2 * H ^ 2 ∧
    ratHeight (b.s * b.left) ≤ H * 2 ^ H ∧
    ratHeight a.intercept ≤ 2 ^ (H + 1) * H ^ 2 := by
  have ha' := (Atom.height_le_iff a).1 ha
  have hb' := (Atom.height_le_iff b).1 hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases ht with rfl | rfl
    · obtain ⟨h1, j, hj, h2⟩ := dyadic_reduced a.m a.k
      exact ⟨by unfold Atom.left; omega, j, by omega, h2⟩
    · have : ((a.m : ℚ) + 1) = ((a.m + 1 : ℤ) : ℚ) := by push_cast; ring
      obtain ⟨h1, j, hj, h2⟩ := dyadic_reduced (a.m + 1) a.k
      unfold Atom.right; rw [this]
      exact ⟨by omega, j, by omega, h2⟩
  · refine (ratHeight_sub_le _ _).trans ?_
    have := Nat.mul_le_mul hb'.2.2.2.2 ha'.2.2.2.2
    nlinarith
  · refine (ratHeight_mul_le _ _).trans (Nat.mul_le_mul hb'.2.2.2.2 (b.ratHeight_left_le hb))
  · unfold Atom.intercept
    refine (ratHeight_sub_le _ _).trans ?_
    have h1 := (ratHeight_mul_le a.s a.center).trans
      (Nat.mul_le_mul ha'.2.2.2.2 (a.ratHeight_center_le ha))
    have h2 := Nat.mul_le_mul ha'.2.2.2.1 h1
    calc 2 * ratHeight a.y0 * ratHeight (a.s * a.center) = 2 * (ratHeight a.y0 *
          ratHeight (a.s * a.center)) := by ring
      _ ≤ 2 * (H * (H * 2 ^ H)) := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (H + 1) * H ^ 2 := by ring

end Dyadic.Lib
