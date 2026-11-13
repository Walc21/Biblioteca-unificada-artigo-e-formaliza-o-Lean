module
public import Mathlib

/-!
# Lemma 6.1: transcendental remainders with rational endpoints

The analytic content of Lemma 6.1: the geometric tail bound (37) for `exp` on `[0, 1/2]`,
the Lagrange bounds (38) for `sin` and `cos`, and the facts used by the enclosure routines
(argument reduction for `exp`, monotone enclosure, inflation and intersection with `[-1,1]`).
-/

@[expose] public section

namespace Fase3

open Finset
open scoped Nat

/-! ## The exponential (equation (37)) -/

/-- The Maclaurin polynomial `∑_{j=0}^n z^j / j!`. -/
noncomputable def expPoly (n : ℕ) (z : ℝ) : ℝ := ∑ j ∈ range (n + 1), z ^ j / (j ! : ℝ)

lemma exp_eq_tsum (z : ℝ) : Real.exp z = ∑' j : ℕ, z ^ j / (j ! : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Tail bound behind (37), valid for `0 ≤ z < n + 2`. -/
theorem exp_sub_expPoly_bounds' {z : ℝ} (hz0 : 0 ≤ z) (n : ℕ) (hzn : z < n + 2) :
    0 ≤ Real.exp z - expPoly n z ∧
      Real.exp z - expPoly n z ≤ z ^ (n + 1) / ((n + 1)! : ℝ) * (1 / (1 - z / (n + 2))) := by
  have hs : Summable (fun j : ℕ => z ^ j / (j ! : ℝ)) := Real.summable_pow_div_factorial z
  have hsplit := (hs.sum_add_tsum_nat_add (n + 1)).symm
  rw [← exp_eq_tsum] at hsplit
  have htail : Real.exp z - expPoly n z = ∑' i : ℕ, z ^ (i + (n + 1)) / ((i + (n + 1))! : ℝ) := by
    unfold expPoly; rw [hsplit]; ring
  rw [htail]
  set q := z / (n + 2) with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hqdef, div_lt_one (by positivity)]; exact hzn
  set t := z ^ (n + 1) / ((n + 1)! : ℝ) with htdef
  have hterm : ∀ i : ℕ, z ^ (i + (n + 1)) / ((i + (n + 1))! : ℝ) ≤ t * q ^ i := by
    intro i
    have hf : (((n + 1)! * (n + 1 + 1) ^ i : ℕ) : ℝ) ≤ ((n + 1 + i)! : ℝ) := by
      exact_mod_cast Nat.factorial_mul_pow_le_factorial
    have e : t * q ^ i = z ^ (i + (n + 1)) / (((n + 1)! * (n + 1 + 1) ^ i : ℕ) : ℝ) := by
      rw [htdef, hqdef]; push_cast; rw [div_pow, pow_add]; field_simp; ring
    rw [e, add_comm i (n + 1)]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf
  have hgeom : Summable (fun i : ℕ => t * q ^ i) := (summable_geometric_of_lt_one hq0 hq1).mul_left t
  have hsT : Summable (fun i : ℕ => z ^ (i + (n + 1)) / ((i + (n + 1))! : ℝ)) :=
    (summable_nat_add_iff (f := fun j : ℕ => z ^ j / (j ! : ℝ)) (n + 1)).2 hs
  constructor
  · exact tsum_nonneg fun i => by positivity
  · calc ∑' i : ℕ, z ^ (i + (n + 1)) / ((i + (n + 1))! : ℝ) ≤ ∑' i : ℕ, t * q ^ i :=
          hsT.tsum_le_tsum hterm hgeom
      _ = t * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
      _ = _ := by rw [one_div]

/-- **Lemma 6.1, equation (37).** For `0 ≤ z ≤ 1/2` and `n ≥ 0`,
`0 ≤ e^z - ∑_{j≤n} z^j/j! ≤ z^{n+1}/(n+1)! · 1/(1 - z/(n+2))`. -/
theorem exp_sub_expPoly_bounds {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 2) (n : ℕ) :
    0 ≤ Real.exp z - expPoly n z ∧
      Real.exp z - expPoly n z ≤ z ^ (n + 1) / ((n + 1)! : ℝ) * (1 / (1 - z / (n + 2))) :=
  exp_sub_expPoly_bounds' hz0 n (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)

/-- Argument reduction: `e^x = (e^{x/2^r})^{2^r}`. -/
theorem exp_reduction (x : ℝ) (r : ℕ) : Real.exp x = Real.exp (x / 2 ^ r) ^ (2 ^ r) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp

/-- Negative arguments: `e^x = 1 / e^{-x}`. -/
theorem exp_neg_reciprocal (x : ℝ) : Real.exp x = 1 / Real.exp (-x) := by
  rw [Real.exp_neg, one_div, inv_inv]

/-- Monotone enclosure: a lower bound at `a` and an upper bound at `b` enclose `exp([a,b])`. -/
theorem exp_image_subset {a b lo hi : ℝ} (hlo : lo ≤ Real.exp a) (hhi : Real.exp b ≤ hi) :
    Real.exp '' Set.Icc a b ⊆ Set.Icc lo hi := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨le_trans hlo (Real.exp_le_exp.2 hz.1), le_trans (Real.exp_le_exp.2 hz.2) hhi⟩

/-! ## Sine and cosine (equation (38)) -/

/-- `P_n^{sin}(z) = ∑_{j=0}^n (-1)^j z^{2j+1}/(2j+1)!`. -/
noncomputable def sinPoly (n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), (-1) ^ j * z ^ (2 * j + 1) / ((2 * j + 1)! : ℝ)

/-- `P_n^{cos}(z) = ∑_{j=0}^n (-1)^j z^{2j}/(2j)!`. -/
noncomputable def cosPoly (n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range (n + 1), (-1) ^ j * z ^ (2 * j) / ((2 * j)! : ℝ)

lemma hasDerivAt_sinPoly (n : ℕ) (z : ℝ) : HasDerivAt (sinPoly n) (cosPoly n z) z := by
  unfold sinPoly cosPoly
  have : ∀ j ∈ range (n + 1), HasDerivAt (fun y => (-1) ^ j * y ^ (2 * j + 1) / ((2 * j + 1)! : ℝ))
      ((-1) ^ j * z ^ (2 * j) / ((2 * j)! : ℝ)) z := by
    intro j _
    have h := (((hasDerivAt_id z).pow (2 * j + 1)).const_mul ((-1 : ℝ) ^ j)).div_const
      ((2 * j + 1)! : ℝ)
    convert h using 1
    simp only [id, Nat.add_sub_cancel, mul_one]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  exact HasDerivAt.fun_sum this

lemma hasDerivAt_cosPoly_succ (n : ℕ) (z : ℝ) :
    HasDerivAt (cosPoly (n + 1)) (-sinPoly n z) z := by
  have hc : cosPoly (n + 1) = fun y => 1 + ∑ j ∈ range (n + 1),
      (-1) ^ (j + 1) * y ^ (2 * j + 2) / ((2 * j + 2)! : ℝ) := by
    ext y; unfold cosPoly; rw [sum_range_succ']; simp only [mul_add, mul_one]; ring
  rw [hc]
  have : ∀ j ∈ range (n + 1), HasDerivAt (fun y => (-1) ^ (j + 1) * y ^ (2 * j + 2) / ((2 * j + 2)! : ℝ))
      (-((-1) ^ j * z ^ (2 * j + 1) / ((2 * j + 1)! : ℝ))) z := by
    intro j _
    have h := (((hasDerivAt_id z).pow (2 * j + 2)).const_mul ((-1 : ℝ) ^ (j + 1))).div_const
      ((2 * j + 2)! : ℝ)
    have hf : ((2 * j + 2)! : ℝ) = (2 * j + 2) * (2 * j + 1)! := by
      rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ]; push_cast; ring
    convert h using 1
    simp only [id, show 2 * j + 2 - 1 = 2 * j + 1 by omega, mul_one]
    rw [hf]
    push_cast
    field_simp
    ring
  have h := (HasDerivAt.fun_sum this).const_add 1
  unfold sinPoly
  convert h using 1
  rw [← sum_neg_distrib]

/-- Integration of a derivative bound: if `u(0) = 0` and `|u'(t)| ≤ t^k/k!` for `t ≥ 0`,
then `|u(z)| ≤ z^{k+1}/(k+1)!` for `z ≥ 0`. -/
lemma abs_le_of_deriv_bound {u u' : ℝ → ℝ} (hu : ∀ t, HasDerivAt u (u' t) t) (h0 : u 0 = 0)
    (k : ℕ) (hb : ∀ t, 0 ≤ t → |u' t| ≤ t ^ k / (k ! : ℝ)) {z : ℝ} (hz : 0 ≤ z) :
    |u z| ≤ z ^ (k + 1) / ((k + 1)! : ℝ) := by
  have hP : ∀ t, HasDerivAt (fun y : ℝ => y ^ (k + 1) / ((k + 1)! : ℝ)) (t ^ k / (k ! : ℝ)) t := by
    intro t
    have h := ((hasDerivAt_id t).pow (k + 1)).div_const ((k + 1)! : ℝ)
    convert h using 1
    simp only [id, Nat.add_sub_cancel]
    rw [Nat.factorial_succ]; push_cast; field_simp
  have mono : ∀ (s : ℝ), (s = 1 ∨ s = -1) → 0 ≤ z ^ (k + 1) / ((k + 1)! : ℝ) - s * u z := by
    intro s hs
    set phi := fun y : ℝ => y ^ (k + 1) / ((k + 1)! : ℝ) - s * u y
    have hphi : ∀ t, HasDerivAt phi (t ^ k / (k ! : ℝ) - s * u' t) t :=
      fun t => (hP t).sub ((hu t).const_mul s)
    have hmon : MonotoneOn phi (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun t _ => (hphi t).continuousAt.continuousWithinAt
      · exact fun t _ => (hphi t).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        rw [(hphi t).deriv]
        have := hb t (le_of_lt ht)
        rcases hs with rfl | rfl
        · linarith [le_abs_self (u' t)]
        · linarith [neg_abs_le (u' t)]
    have := hmon (Set.self_mem_Ici) hz hz
    simp only [phi, h0] at this
    simpa [zero_pow (Nat.succ_ne_zero k)] using this
  have h1 := mono 1 (Or.inl rfl)
  have h2 := mono (-1) (Or.inr rfl)
  rw [abs_le]; constructor <;> linarith

lemma cos_sinPoly_bounds_nonneg (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |Real.cos z - cosPoly n z| ≤ z ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) ∧
      |Real.sin z - sinPoly n z| ≤ z ^ (2 * n + 2) / ((2 * n + 2)! : ℝ) := by
  induction n generalizing z with
  | zero =>
    have hB : ∀ y, 0 ≤ y → |Real.cos y - cosPoly 0 y| ≤ y ^ (2 * 0 + 1) / ((2 * 0 + 1)! : ℝ) := by
      intro y hy
      have := abs_le_of_deriv_bound (u := fun t => Real.cos t - 1) (u' := fun t => -Real.sin t)
        (fun t => by simpa using (Real.hasDerivAt_cos t).sub_const 1) (by simp) 0
        (fun t _ => by simpa using Real.abs_sin_le_one t) hy
      simpa [cosPoly] using this
    refine ⟨hB z hz, ?_⟩
    have := abs_le_of_deriv_bound (u := fun t => Real.sin t - sinPoly 0 t)
      (u' := fun t => Real.cos t - cosPoly 0 t)
      (fun t => (Real.hasDerivAt_sin t).sub (hasDerivAt_sinPoly 0 t)) (by simp [sinPoly]) 1
      (fun t ht => by simpa using hB t ht) hz
    simpa using this
  | succ n ih =>
    have hB : ∀ y, 0 ≤ y → |Real.cos y - cosPoly (n + 1) y| ≤
        y ^ (2 * (n + 1) + 1) / ((2 * (n + 1) + 1)! : ℝ) := by
      intro y hy
      have := abs_le_of_deriv_bound (u := fun t => Real.cos t - cosPoly (n + 1) t)
        (u' := fun t => -(Real.sin t - sinPoly n t))
        (fun t => by
          have := (Real.hasDerivAt_cos t).sub (hasDerivAt_cosPoly_succ n t)
          convert this using 1; ring)
        (by simp [cosPoly, sum_range_succ']) (2 * n + 2)
        (fun t ht => by rw [abs_neg]; exact (ih ht).2) hy
      simpa [show 2 * (n + 1) + 1 = 2 * n + 2 + 1 by ring] using this
    refine ⟨hB z hz, ?_⟩
    have := abs_le_of_deriv_bound (u := fun t => Real.sin t - sinPoly (n + 1) t)
      (u' := fun t => Real.cos t - cosPoly (n + 1) t)
      (fun t => (Real.hasDerivAt_sin t).sub (hasDerivAt_sinPoly (n + 1) t))
      (by simp [sinPoly]) (2 * (n + 1) + 1) (fun t ht => hB t ht) hz
    simpa [show 2 * (n + 1) + 1 + 1 = 2 * (n + 1) + 2 by ring] using this

lemma sinPoly_neg (n : ℕ) (z : ℝ) : sinPoly n (-z) = -sinPoly n z := by
  unfold sinPoly
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [show (-z) ^ (2 * j + 1) = -z ^ (2 * j + 1) by rw [pow_succ, pow_mul, neg_sq, ← pow_mul]; ring]
  ring

lemma cosPoly_neg (n : ℕ) (z : ℝ) : cosPoly n (-z) = cosPoly n z := by
  unfold cosPoly
  refine sum_congr rfl fun j _ => ?_
  rw [show (-z) ^ (2 * j) = z ^ (2 * j) by rw [pow_mul, pow_mul, neg_sq]]

/-- Lagrange bounds with `|z|` in place of `R`. -/
theorem cos_sinPoly_bounds (n : ℕ) (z : ℝ) :
    |Real.cos z - cosPoly n z| ≤ |z| ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) ∧
      |Real.sin z - sinPoly n z| ≤ |z| ^ (2 * n + 2) / ((2 * n + 2)! : ℝ) := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]; exact cos_sinPoly_bounds_nonneg n hz
  · have := cos_sinPoly_bounds_nonneg n (neg_nonneg.2 hz)
    rw [abs_of_nonpos hz]
    rw [Real.cos_neg, cosPoly_neg, Real.sin_neg, sinPoly_neg] at this
    refine ⟨this.1, ?_⟩
    have h := this.2
    rwa [show -Real.sin z - -sinPoly n z = -(Real.sin z - sinPoly n z) by ring, abs_neg] at h

/-- **Lemma 6.1, equation (38).** For `I = [a,b]`, `R = max{|a|,|b|}` and every `z ∈ I`,
`|sin z - P_n^{sin}(z)| ≤ R^{2n+2}/(2n+2)!` and `|cos z - P_n^{cos}(z)| ≤ R^{2n+1}/(2n+1)!`. -/
theorem sin_cos_lagrange (n : ℕ) {a b z : ℝ} (hz : z ∈ Set.Icc a b) :
    |Real.sin z - sinPoly n z| ≤ max |a| |b| ^ (2 * n + 2) / ((2 * n + 2)! : ℝ) ∧
      |Real.cos z - cosPoly n z| ≤ max |a| |b| ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) := by
  have hR : |z| ≤ max |a| |b| := by
    rw [abs_le]; constructor
    · have := neg_abs_le a; have := le_max_left |a| |b|; linarith [hz.1]
    · have := le_abs_self b; have := le_max_right |a| |b|; linarith [hz.2]
  obtain ⟨h1, h2⟩ := cos_sinPoly_bounds n z
  constructor
  · exact le_trans h2 (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg z) hR _) (by positivity))
  · exact le_trans h1 (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg z) hR _) (by positivity))

/-- **Lemma 6.1, enclosure.** If the polynomial value lies in `[lo, hi]`, then inflating by
the remainder and intersecting with `[-1, 1]` still contains `sin z`. -/
theorem sin_mem_inflated (n : ℕ) {a b z lo hi : ℝ} (hz : z ∈ Set.Icc a b)
    (hp : sinPoly n z ∈ Set.Icc lo hi) :
    Real.sin z ∈ Set.Icc (max (-1) (lo - max |a| |b| ^ (2 * n + 2) / ((2 * n + 2)! : ℝ)))
      (min 1 (hi + max |a| |b| ^ (2 * n + 2) / ((2 * n + 2)! : ℝ))) := by
  have h := (sin_cos_lagrange n hz).1
  rw [abs_le] at h
  exact ⟨max_le (Real.neg_one_le_sin z) (by linarith [hp.1]),
    le_min (Real.sin_le_one z) (by linarith [hp.2])⟩

/-- **Lemma 6.1, enclosure** for `cos`. -/
theorem cos_mem_inflated (n : ℕ) {a b z lo hi : ℝ} (hz : z ∈ Set.Icc a b)
    (hp : cosPoly n z ∈ Set.Icc lo hi) :
    Real.cos z ∈ Set.Icc (max (-1) (lo - max |a| |b| ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)))
      (min 1 (hi + max |a| |b| ^ (2 * n + 1) / ((2 * n + 1)! : ℝ))) := by
  have h := (sin_cos_lagrange n hz).2
  rw [abs_le] at h
  exact ⟨max_le (Real.neg_one_le_cos z) (by linarith [hp.1]),
    le_min (Real.cos_le_one z) (by linarith [hp.2])⟩

end Fase3
