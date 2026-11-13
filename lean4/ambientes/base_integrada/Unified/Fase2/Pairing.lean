module

public import Mathlib

/-!
# Section 2.1–2.2: Cantor pairing and the enumeration `Z : ℕ₀ → ℤ`

Formalization of Lemma 2.1 (pairing and bound) and Lemma 2.2 (the bijection `Z`).
-/

@[expose] public section

namespace Dyadic2

/-- Triangular numbers `T_m = m(m+1)/2`. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

/-- Cantor pairing, Equation (01): `π(u,v) = T_{u+v} + v`. -/
def cpair (u v : ℕ) : ℕ := tri (u + v) + v

/-- The inverse of the pairing, Equation (02), computed with the integer square root.
(`cunpair_eq_floor_formula` shows it is the real-floor formula of the paper.) -/
def cunpair (n : ℕ) : ℕ × ℕ :=
  ((Nat.sqrt (8 * n + 1) - 1) / 2 - (n - tri ((Nat.sqrt (8 * n + 1) - 1) / 2)),
    n - tri ((Nat.sqrt (8 * n + 1) - 1) / 2))

lemma two_mul_tri (m : ℕ) : 2 * tri m = m * (m + 1) := by
  unfold tri
  have : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  omega

lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + m + 1 := by
  have h1 := two_mul_tri m
  have h2 := two_mul_tri (m + 1)
  have : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
  omega

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  unfold tri
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

/-- `T_w ≤ n ↔ (2w+1)^2 ≤ 8n+1`. -/
lemma tri_le_iff (w n : ℕ) : tri w ≤ n ↔ (2 * w + 1) ^ 2 ≤ 8 * n + 1 := by
  have h := two_mul_tri w
  constructor
  · intro hw; nlinarith
  · intro hw; nlinarith

/-- The diagonal block of `n`: the unique `w` with `T_w ≤ n < T_{w+1}`. -/
lemma block_spec (n : ℕ) :
    tri ((Nat.sqrt (8 * n + 1) - 1) / 2) ≤ n ∧ n < tri ((Nat.sqrt (8 * n + 1) - 1) / 2 + 1) := by
  set s := Nat.sqrt (8 * n + 1) with hs
  have h1 : s * s ≤ 8 * n + 1 := Nat.sqrt_le' _ |> fun h => by simpa [sq] using h
  have h2 : 8 * n + 1 < (s + 1) * (s + 1) := by
    have := Nat.lt_succ_sqrt' (8 * n + 1); simpa [sq] using this
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h] at h2; omega
    · exact h
  set w := (s - 1) / 2 with hw
  constructor
  · rw [tri_le_iff]
    have : 2 * w + 1 ≤ s := by omega
    nlinarith
  · by_contra hc
    push_neg at hc
    rw [tri_le_iff] at hc
    have : s + 1 ≤ 2 * (w + 1) + 1 := by omega
    nlinarith

lemma block_unique {w w' n : ℕ} (h1 : tri w ≤ n) (h2 : n < tri (w + 1))
    (h1' : tri w' ≤ n) (h2' : n < tri (w' + 1)) : w = w' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := tri_mono (show w + 1 ≤ w' by omega); omega
  · have := tri_mono (show w' + 1 ≤ w by omega); omega

lemma cunpair_cpair (u v : ℕ) : cunpair (cpair u v) = (u, v) := by
  have hb := block_spec (cpair u v)
  have hw : (Nat.sqrt (8 * cpair u v + 1) - 1) / 2 = u + v := by
    apply block_unique hb.1 hb.2
    · unfold cpair; omega
    · unfold cpair; rw [tri_succ]; omega
  unfold cunpair
  rw [hw]
  unfold cpair
  ext <;> simp

lemma cpair_cunpair (n : ℕ) : cpair (cunpair n).1 (cunpair n).2 = n := by
  have hb := block_spec n
  rw [tri_succ] at hb
  unfold cunpair cpair
  simp only
  have : (Nat.sqrt (8 * n + 1) - 1) / 2 - (n - tri ((Nat.sqrt (8 * n + 1) - 1) / 2)) +
      (n - tri ((Nat.sqrt (8 * n + 1) - 1) / 2)) = (Nat.sqrt (8 * n + 1) - 1) / 2 := by omega
  rw [this]
  omega

/-- **Lemma 2.1 (bijectivity).** The Cantor pairing `π : ℕ₀² → ℕ₀` is bijective. -/
theorem cpair_bijective : Function.Bijective (fun p : ℕ × ℕ => cpair p.1 p.2) := by
  constructor
  · intro p q h
    have := congrArg cunpair h
    simp only [cunpair_cpair] at this
    exact this
  · intro n
    exact ⟨cunpair n, cpair_cunpair n⟩

/-- **Lemma 2.1 (inverse formula).** The inverse of `π` is given by Equation (02):
`w = ⌊(√(8n+1) - 1)/2⌋`, `v = n - T_w`, `u = w - v`. -/
theorem cunpair_eq_floor_formula (n : ℕ) :
    cunpair n =
      (⌊(Real.sqrt (8 * n + 1) - 1) / 2⌋₊ - (n - tri ⌊(Real.sqrt (8 * n + 1) - 1) / 2⌋₊),
        n - tri ⌊(Real.sqrt (8 * n + 1) - 1) / 2⌋₊) := by
  have key : ⌊(Real.sqrt (8 * n + 1) - 1) / 2⌋₊ = (Nat.sqrt (8 * n + 1) - 1) / 2 := by
    set s := Nat.sqrt (8 * n + 1) with hs
    have h1 : s * s ≤ 8 * n + 1 := Nat.sqrt_le' _ |> fun h => by simpa [sq] using h
    have h2 : 8 * n + 1 < (s + 1) * (s + 1) := by
      have := Nat.lt_succ_sqrt' (8 * n + 1); simpa [sq] using this
    have hs1 : 1 ≤ s := by
      rcases Nat.eq_zero_or_pos s with h | h
      · rw [h] at h2; omega
      · exact h
    have hcast : ((8 * n + 1 : ℕ) : ℝ) = 8 * (n : ℝ) + 1 := by push_cast; ring
    have hlo : (s : ℝ) ≤ Real.sqrt (8 * n + 1) := by
      rw [← hcast]; apply Real.le_sqrt_of_sq_le
      exact_mod_cast (by nlinarith : s ^ 2 ≤ 8 * n + 1)
    have hhi : Real.sqrt (8 * n + 1) < (s : ℝ) + 1 := by
      rw [← hcast, Real.sqrt_lt' (by positivity)]
      exact_mod_cast (by nlinarith : 8 * n + 1 < (s + 1) ^ 2)
    rw [Nat.floor_eq_iff (by
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs1
      linarith)]
    have e1 : (((s - 1) / 2 : ℕ) : ℝ) * 2 + 1 ≤ s := by
      have : (s - 1) / 2 * 2 + 1 ≤ s := by omega
      exact_mod_cast this
    have e2 : (s : ℝ) + 1 ≤ (((s - 1) / 2 : ℕ) : ℝ) * 2 + 3 := by
      have : s + 1 ≤ (s - 1) / 2 * 2 + 3 := by omega
      exact_mod_cast this
    constructor <;> linarith
  rw [key]
  rfl

/-- **Lemma 2.1 (bound).** `π(u,v) ≤ (u+v+1)^2`. -/
theorem cpair_le (u v : ℕ) : cpair u v ≤ (u + v + 1) ^ 2 := by
  unfold cpair
  have h := two_mul_tri (u + v)
  nlinarith

/-! ### The enumeration `Z : ℕ₀ → ℤ`, Equation (03) -/

/-- Equation (03): `Z(t) = t/2` for even `t`, `Z(t) = -(t+1)/2` for odd `t`. -/
def Zenum (t : ℕ) : ℤ := if t % 2 = 0 then ((t / 2 : ℕ) : ℤ) else -(((t + 1) / 2 : ℕ) : ℤ)

/-- The inverse of `Z`: `Z⁻¹(m) = 2m` for `m ≥ 0`, `Z⁻¹(m) = -2m-1` for `m < 0`. -/
def Zinv (m : ℤ) : ℕ := if 0 ≤ m then (2 * m).toNat else (-2 * m - 1).toNat

lemma Zenum_Zinv (m : ℤ) : Zenum (Zinv m) = m := by
  unfold Zenum Zinv
  split_ifs <;> omega

lemma Zinv_Zenum (t : ℕ) : Zinv (Zenum t) = t := by
  unfold Zenum Zinv
  split_ifs <;> omega

/-- **Lemma 2.2.** `Z` is bijective. -/
theorem Zenum_bijective : Function.Bijective Zenum := by
  constructor
  · intro a b h
    have := congrArg Zinv h
    rwa [Zinv_Zenum, Zinv_Zenum] at this
  · intro m; exact ⟨Zinv m, Zenum_Zinv m⟩

/-- **Lemma 2.2 (inverse formulas).** -/
theorem Zinv_spec (m : ℤ) :
    (0 ≤ m → (Zinv m : ℤ) = 2 * m) ∧ (m < 0 → (Zinv m : ℤ) = -2 * m - 1) := by
  unfold Zinv
  constructor <;> intro h <;> split_ifs <;> omega

/-- **Lemma 2.2 (bound).** `Z⁻¹(m) ≤ 2|m| + 1`. -/
theorem Zinv_le (m : ℤ) : Zinv m ≤ 2 * m.natAbs + 1 := by
  unfold Zinv
  split_ifs <;> omega

end Dyadic2
