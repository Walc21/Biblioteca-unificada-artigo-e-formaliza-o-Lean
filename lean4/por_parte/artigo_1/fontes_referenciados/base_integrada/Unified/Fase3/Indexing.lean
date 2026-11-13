module
public import Mathlib

/-!
# Section 2: indexing tools

Cantor pairing, the integer enumeration `Z`, height of rationals and the
height enumerations `Q : ℕ → ℚ`, `Q* : ℕ → ℚ*`, and the Stern / Calkin–Wilf lemma.
-/

@[expose] public section

namespace Fase3

/-! ## Cantor pairing (Lemma 2.1) -/

/-- Triangular numbers `T_m = m(m+1)/2`. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

/-- Cantor pairing `π(u,v) = T_{u+v} + v` (equation (01)). -/
def cpair (u v : ℕ) : ℕ := tri (u + v) + v

/-- The diagonal index `w = ⌊(√(8n+1) - 1)/2⌋` computed with the integer square root. -/
def cdiag (n : ℕ) : ℕ := (Nat.sqrt (8 * n + 1) - 1) / 2

/-- The inverse of the Cantor pairing (equation (02)). -/
def cunpair (n : ℕ) : ℕ × ℕ :=
  (cdiag n - (n - tri (cdiag n)), n - tri (cdiag n))

lemma two_mul_tri (m : ℕ) : 2 * tri m = m * (m + 1) := by
  unfold tri
  have : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  omega

lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + (m + 1) := by
  have h1 := two_mul_tri m
  have h2 := two_mul_tri (m + 1)
  have : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
  omega

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  have h1 := two_mul_tri a
  have h2 := two_mul_tri b
  have : a * (a + 1) ≤ b * (b + 1) := Nat.mul_le_mul h (by omega)
  omega

lemma cdiag_spec (n : ℕ) : tri (cdiag n) ≤ n ∧ n < tri (cdiag n + 1) := by
  set s := Nat.sqrt (8 * n + 1) with hs
  have h1 : s * s ≤ 8 * n + 1 := Nat.sqrt_le _
  have h2 : 8 * n + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
  have hs1 : 1 ≤ s := by
    rw [hs]; exact Nat.le_sqrt.2 (by omega)
  set w := cdiag n with hw
  have hw' : w = (s - 1) / 2 := rfl
  have ht1 := two_mul_tri w
  have ht2 := two_mul_tri (w + 1)
  have hlo : 2 * w + 1 ≤ s := by omega
  have hhi : s ≤ 2 * w + 2 := by omega
  constructor
  · have : (2 * w + 1) * (2 * w + 1) ≤ s * s := Nat.mul_le_mul hlo hlo
    nlinarith
  · have : (s + 1) * (s + 1) ≤ (2 * w + 3) * (2 * w + 3) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith

lemma tri_block_unique {w w' n : ℕ} (h1 : tri w ≤ n) (h2 : n < tri (w + 1))
    (h1' : tri w' ≤ n) (h2' : n < tri (w' + 1)) : w = w' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := tri_mono (show w + 1 ≤ w' by omega); omega
  · have := tri_mono (show w' + 1 ≤ w by omega); omega

lemma cdiag_cpair (u v : ℕ) : cdiag (cpair u v) = u + v := by
  obtain ⟨h1, h2⟩ := cdiag_spec (cpair u v)
  apply tri_block_unique h1 h2
  · unfold cpair; omega
  · unfold cpair; rw [tri_succ]; omega

lemma cunpair_cpair (u v : ℕ) : cunpair (cpair u v) = (u, v) := by
  unfold cunpair
  rw [cdiag_cpair]
  unfold cpair
  ext <;> simp

lemma cpair_cunpair (n : ℕ) : cpair (cunpair n).1 (cunpair n).2 = n := by
  obtain ⟨h1, h2⟩ := cdiag_spec n
  rw [tri_succ] at h2
  unfold cunpair cpair
  simp only
  have : cdiag n - (n - tri (cdiag n)) + (n - tri (cdiag n)) = cdiag n := by omega
  rw [this]; omega

/-- **Lemma 2.1 (bijectivity).** The Cantor pairing is a bijection `ℕ × ℕ → ℕ`. -/
theorem cpair_bijective : Function.Bijective (fun p : ℕ × ℕ => cpair p.1 p.2) := by
  constructor
  · intro p q h
    have := congrArg cunpair h
    simpa [cunpair_cpair] using this
  · intro n
    exact ⟨cunpair n, cpair_cunpair n⟩

/-- **Lemma 2.1 (inverse formula).** The diagonal index of the inverse is
`w = ⌊(√(8n+1) - 1)/2⌋`, and the inverse is `v = n - T_w`, `u = w - v`. -/
theorem cdiag_eq_floor (n : ℕ) :
    ((cdiag n : ℕ) : ℤ) = ⌊(Real.sqrt (8 * n + 1) - 1) / 2⌋ := by
  obtain ⟨h1, h2⟩ := cdiag_spec n
  set w := cdiag n
  have ht1 := two_mul_tri w
  have ht2 := two_mul_tri (w + 1)
  have hA : ((2 * w + 1 : ℕ) : ℝ) ^ 2 ≤ 8 * n + 1 := by
    have : (2 * w + 1) ^ 2 ≤ 8 * n + 1 := by nlinarith
    exact_mod_cast this
  have hB : (8 * n + 1 : ℝ) < ((2 * w + 3 : ℕ) : ℝ) ^ 2 := by
    have : 8 * n + 1 < (2 * w + 3) ^ 2 := by nlinarith
    exact_mod_cast this
  have hs1 : ((2 * w + 1 : ℕ) : ℝ) ≤ Real.sqrt (8 * n + 1) :=
    Real.le_sqrt_of_sq_le hA
  have hs2 : Real.sqrt (8 * n + 1) < ((2 * w + 3 : ℕ) : ℝ) := by
    rw [Real.sqrt_lt' (by positivity)]; exact hB
  push_cast at hs1 hs2
  symm
  rw [Int.floor_eq_iff]
  push_cast
  constructor <;> linarith

/-- **Lemma 2.1 (bound).** `π(u,v) ≤ (u+v+1)^2`. -/
theorem cpair_le (u v : ℕ) : cpair u v ≤ (u + v + 1) ^ 2 := by
  unfold cpair
  have := two_mul_tri (u + v)
  nlinarith

/-! ## Integer enumeration (Lemma 2.2) -/

/-- `Z(t) = t/2` for even `t`, `-(t+1)/2` for odd `t` (equation (03)). -/
def zEnum (t : ℕ) : ℤ := if t % 2 = 0 then (t / 2 : ℕ) else -(((t + 1) / 2 : ℕ) : ℤ)

/-- The inverse of `Z`: `2m` for `m ≥ 0` and `-2m-1` for `m < 0`. -/
def zInv (m : ℤ) : ℕ := if 0 ≤ m then (2 * m).toNat else (-2 * m - 1).toNat

lemma zEnum_zInv (m : ℤ) : zEnum (zInv m) = m := by
  unfold zEnum zInv
  split_ifs <;> omega

lemma zInv_zEnum (t : ℕ) : zInv (zEnum t) = t := by
  unfold zEnum zInv
  split_ifs <;> omega

/-- **Lemma 2.2.** `Z` is bijective with the stated inverse, and `Z⁻¹(m) ≤ 2|m|+1`. -/
theorem zEnum_bijective : Function.Bijective zEnum :=
  ⟨Function.LeftInverse.injective zInv_zEnum, Function.RightInverse.surjective zEnum_zInv⟩

theorem zInv_le (m : ℤ) : (zInv m : ℤ) ≤ 2 * |m| + 1 := by
  unfold zInv
  split_ifs <;> rcases abs_cases m with h | h <;> omega

end Fase3
