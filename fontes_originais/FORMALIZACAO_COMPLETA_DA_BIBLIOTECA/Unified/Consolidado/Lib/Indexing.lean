module
public import Mathlib
@[expose] public section

/-!
# Section 2: indexing tools

Cantor pairing `π`, the integer enumeration `Z`, the height of a rational number,
the finite sets `ℚ_H`, and the height-ordered ranks of `ℚ` and `ℚ^*`.
-/

open Finset

namespace Dyadic.Lib

/-- Triangular numbers `T_m = m(m+1)/2`. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

/-- Cantor pairing `π(u,v) = T_{u+v} + v` (eq. (01)). -/
def cantorPair (u v : ℕ) : ℕ := tri (u + v) + v

/-- The explicit inverse of the Cantor pairing (eq. (02)). -/
def cantorUnpair (n : ℕ) : ℕ × ℕ :=
  let w := (Nat.sqrt (8 * n + 1) - 1) / 2
  let v := n - tri w
  (w - v, v)

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
  have h1 := two_mul_tri a
  have h2 := two_mul_tri b
  have : a * (a + 1) ≤ b * (b + 1) := Nat.mul_le_mul h (by omega)
  omega

/-- The diagonal block containing `n`: `T_w ≤ n < T_{w+1}` with `w` given by eq. (02). -/
lemma tri_block (n : ℕ) :
    tri ((Nat.sqrt (8 * n + 1) - 1) / 2) ≤ n ∧ n < tri ((Nat.sqrt (8 * n + 1) - 1) / 2 + 1) := by
  set s := Nat.sqrt (8 * n + 1) with hs
  have h1 : s * s ≤ 8 * n + 1 := Nat.sqrt_le (8 * n + 1)
  have h2 : 8 * n + 1 < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (8 * n + 1)
  have hs1 : 1 ≤ s := by
    rw [hs, Nat.le_sqrt]; omega
  set w := (s - 1) / 2 with hw
  have t1 := two_mul_tri w
  have t2 := two_mul_tri (w + 1)
  rcases Nat.even_or_odd' s with ⟨j, hj | hj⟩
  · -- s = 2j, j ≥ 1, w = j - 1
    have hj1 : 1 ≤ j := by omega
    have hwj : w = j - 1 := by omega
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hwi : w = i := by omega
    subst hwi
    rw [hj] at h1 h2
    constructor <;> nlinarith
  · have hwj : w = j := by omega
    subst hwj
    rw [hj] at h1 h2
    constructor <;> nlinarith

lemma tri_block_unique {w w' n : ℕ} (h1 : tri w ≤ n) (h2 : n < tri (w + 1))
    (h1' : tri w' ≤ n) (h2' : n < tri (w' + 1)) : w = w' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := tri_mono (show w + 1 ≤ w' by omega); omega
  · have := tri_mono (show w' + 1 ≤ w by omega); omega

lemma cantorPair_block (u v : ℕ) :
    tri (u + v) ≤ cantorPair u v ∧ cantorPair u v < tri (u + v + 1) := by
  unfold cantorPair; rw [tri_succ]; omega

lemma cantorUnpair_cantorPair (u v : ℕ) : cantorUnpair (cantorPair u v) = (u, v) := by
  have hb := tri_block (cantorPair u v)
  have hc := cantorPair_block u v
  have hw := tri_block_unique hb.1 hb.2 hc.1 hc.2
  simp only [cantorUnpair]
  rw [hw]
  unfold cantorPair
  ext <;> simp <;> omega

lemma cantorPair_cantorUnpair (n : ℕ) :
    cantorPair (cantorUnpair n).1 (cantorUnpair n).2 = n := by
  simp only [cantorUnpair, cantorPair]
  obtain ⟨hb1, hb2⟩ := tri_block n
  set w := (Nat.sqrt (8 * n + 1) - 1) / 2
  have := tri_succ w
  have hv : n - tri w ≤ w := by omega
  rw [show w - (n - tri w) + (n - tri w) = w by omega]
  omega

/-- Lemma 2.1: the Cantor pairing is a bijection `ℕ² → ℕ`. -/
theorem cantorPair_bijective : Function.Bijective (fun p : ℕ × ℕ => cantorPair p.1 p.2) := by
  constructor
  · intro p q h
    have := congrArg cantorUnpair h
    simpa [cantorUnpair_cantorPair] using this
  · intro n; exact ⟨cantorUnpair n, cantorPair_cantorUnpair n⟩

lemma cantorPair_injective {u v u' v' : ℕ} (h : cantorPair u v = cantorPair u' v') :
    u = u' ∧ v = v' := by
  have := congrArg cantorUnpair h
  simp [cantorUnpair_cantorPair] at this
  exact this

/-- Lemma 2.1 (bound): `π(u,v) ≤ (u+v+1)²`. -/
theorem cantorPair_le (u v : ℕ) : cantorPair u v ≤ (u + v + 1) ^ 2 := by
  unfold cantorPair
  have := two_mul_tri (u + v)
  nlinarith

lemma cantorPair_ge (u v : ℕ) : (u + v) ^ 2 ≤ 2 * cantorPair u v := by
  unfold cantorPair
  have := two_mul_tri (u + v)
  nlinarith

lemma cantorPair_mono {u v u' v' : ℕ} (hu : u ≤ u') (hv : v ≤ v') :
    cantorPair u v ≤ cantorPair u' v' := by
  unfold cantorPair
  have := tri_mono (show u + v ≤ u' + v' by omega)
  omega

/-! ### The integer enumeration `Z` -/

/-- `Z : ℕ → ℤ` (eq. (03)). -/
def zDecode (t : ℕ) : ℤ := if t % 2 = 0 then (t / 2 : ℕ) else -(((t + 1) / 2 : ℕ) : ℤ)

/-- `Z⁻¹ : ℤ → ℕ`. -/
def zEncode (m : ℤ) : ℕ := if 0 ≤ m then 2 * m.toNat else 2 * (-m).toNat - 1

lemma zDecode_zEncode (m : ℤ) : zDecode (zEncode m) = m := by
  unfold zDecode zEncode
  split_ifs <;> omega

lemma zEncode_zDecode (t : ℕ) : zEncode (zDecode t) = t := by
  unfold zDecode zEncode
  split_ifs <;> omega

/-- Lemma 2.2: `Z` is a bijection. -/
theorem zDecode_bijective : Function.Bijective zDecode :=
  Function.bijective_iff_has_inverse.2 ⟨zEncode, zEncode_zDecode, zDecode_zEncode⟩

lemma zEncode_injective : Function.Injective zEncode :=
  Function.LeftInverse.injective zDecode_zEncode

/-- Lemma 2.2: `Z⁻¹(m) ≤ 2|m|+1`. -/
theorem zEncode_le (m : ℤ) : zEncode m ≤ 2 * m.natAbs + 1 := by
  unfold zEncode; split_ifs <;> omega

/-! ### Heights of rationals -/

/-- The height `ht(p/q) = max(|p|, q)` of a reduced fraction (eq. (04)). -/
def ratHeight (r : ℚ) : ℕ := max r.num.natAbs r.den

lemma one_le_ratHeight (r : ℚ) : 1 ≤ ratHeight r :=
  le_max_of_le_right r.den_pos

lemma natAbs_num_le_ratHeight (r : ℚ) : r.num.natAbs ≤ ratHeight r := le_max_left _ _
lemma den_le_ratHeight (r : ℚ) : r.den ≤ ratHeight r := le_max_right _ _

/-- The finite set `ℚ_H = {r ∈ ℚ : ht(r) ≤ H}`. -/
def ratsUpTo (H : ℕ) : Finset ℚ :=
  ((Finset.Icc (-(H : ℤ)) H ×ˢ Finset.Icc 1 H).image
    (fun p : ℤ × ℕ => (p.1 : ℚ) / p.2)).filter (fun r => ratHeight r ≤ H)

lemma mem_ratsUpTo {H : ℕ} {r : ℚ} : r ∈ ratsUpTo H ↔ ratHeight r ≤ H := by
  unfold ratsUpTo
  simp only [mem_filter, mem_image, mem_product, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨(r.num, r.den), ?_, ?_⟩, h⟩
    · have h1 := natAbs_num_le_ratHeight r
      have h2 := den_le_ratHeight r
      have h3 := r.den_pos
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
    · simp [Rat.num_div_den]

lemma card_ratsUpTo_le' (H : ℕ) : (ratsUpTo H).card ≤ (2 * H + 1) * H := by
  unfold ratsUpTo
  refine (card_filter_le _ _).trans (card_image_le.trans ?_)
  simp only [card_product, Int.card_Icc, Nat.card_Icc]
  rw [show ((H : ℤ) + 1 - -(H : ℤ)).toNat = 2 * H + 1 by omega, Nat.add_sub_cancel]

/-- Lemma 2.3, eq. (06): `|ℚ_H| ≤ 3H²` for `H ≥ 1`. -/
theorem card_ratsUpTo_le {H : ℕ} (hH : 1 ≤ H) : (ratsUpTo H).card ≤ 3 * H ^ 2 := by
  have := card_ratsUpTo_le' H
  nlinarith

lemma zero_mem_ratsUpTo {H : ℕ} (hH : 1 ≤ H) : (0 : ℚ) ∈ ratsUpTo H := by
  rw [mem_ratsUpTo]; simpa [ratHeight] using hH

/-! ### Lower bound for `|ℚ_H|` -/

/-- Pairs `(p,q) ∈ [1,H]²` that are not coprime are covered by the sets of common multiples. -/
lemma card_noncoprime_le (H : ℕ) :
    (((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2))).card
      ≤ ∑ d ∈ Finset.Icc 2 H, (H / d) ^ 2 := by
  have hsub : ((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2))
      ⊆ (Finset.Icc 2 H).biUnion (fun d =>
          ((Finset.Icc 1 (H / d)) ×ˢ (Finset.Icc 1 (H / d))).image (fun p => (d * p.1, d * p.2))) := by
    intro x hx
    simp only [mem_filter, mem_product, mem_Icc] at hx
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hx
    set d := Nat.gcd x.1 x.2 with hd
    have hd2 : 2 ≤ d := by
      have : d ≠ 1 := h5
      have : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
      omega
    have hdx1 : d ∣ x.1 := Nat.gcd_dvd_left _ _
    have hdx2 : d ∣ x.2 := Nat.gcd_dvd_right _ _
    obtain ⟨a, ha⟩ := hdx1
    obtain ⟨b, hb⟩ := hdx2
    simp only [mem_biUnion, mem_Icc, mem_image, mem_product]
    have hdH : d ≤ H := (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)).trans h2
    refine ⟨d, ⟨hd2, hdH⟩, (a, b), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos a with h | h
      · subst h; omega
      · exact h
    · rw [Nat.le_div_iff_mul_le (by omega)]; nlinarith
    · rcases Nat.eq_zero_or_pos b with h | h
      · subst h; omega
      · exact h
    · rw [Nat.le_div_iff_mul_le (by omega)]; nlinarith
    · ext <;> simp [← ha, ← hb]
  refine (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun d _ => ?_))
  refine card_image_le.trans ?_
  simp [card_product, sq]

lemma sum_div_sq_le (H : ℕ) (hH : 1 ≤ H) :
    (∑ d ∈ Finset.Icc 2 H, ((H / d : ℕ) : ℝ) ^ 2) ≤ 3 / 4 * (H : ℝ) ^ 2 := by
  have key : ∀ d ∈ Finset.Icc 2 H, ((H / d : ℕ) : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
    intro d hd
    simp only [mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    rw [le_div_iff₀ (by positivity), ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : (H / d) * d ≤ H := Nat.div_mul_le_self H d
    exact_mod_cast this
  refine (sum_le_sum key).trans ?_
  have tele : ∀ n : ℕ, ∑ d ∈ Finset.Icc 2 (n + 2), (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 - 1 / (n + 2) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
      have h3 : (1 : ℝ) / ((((n + 2 + 1 : ℕ)) : ℝ)) ^ 2 ≤ 1 / (n + 2) - 1 / (n + 1 + 2) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      push_cast at ih h3 ⊢
      linarith
  rcases Nat.lt_or_ge H 2 with h | h
  · have : Finset.Icc 2 H = ∅ := by ext; simp; omega
    simp [this]
  · obtain ⟨n, rfl⟩ : ∃ n, H = n + 2 := ⟨H - 2, by omega⟩
    have := tele n
    simp_rw [div_eq_mul_one_div ((((n + 2 : ℕ)) : ℝ) ^ 2)]
    rw [← Finset.mul_sum]
    have hpos : (0 : ℝ) ≤ (((n + 2 : ℕ)) : ℝ) ^ 2 := by positivity
    calc (((n + 2 : ℕ)) : ℝ) ^ 2 * ∑ i ∈ Finset.Icc 2 (n + 2), 1 / (i : ℝ) ^ 2
        ≤ (((n + 2 : ℕ)) : ℝ) ^ 2 * (3 / 4 - 1 / (n + 2)) := mul_le_mul_of_nonneg_left this hpos
      _ ≤ 3 / 4 * (((n + 2 : ℕ)) : ℝ) ^ 2 := by
        have : (0 : ℝ) ≤ 1 / (n + 2) := by positivity
        nlinarith

/-- The number of coprime pairs in `[1,H]²` is at least `H²/4`. -/
lemma card_coprime_ge (H : ℕ) :
    (H : ℝ) ^ 2 / 4 ≤ (((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
      (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2))).card := by
  rcases Nat.eq_zero_or_pos H with h | hH
  · subst h; simp
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Finset.Icc 1 H ×ˢ Finset.Icc 1 H) (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)
  have hc : (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).card = H ^ 2 := by simp [card_product, sq]
  have h1 := card_noncoprime_le H
  have h2 := sum_div_sq_le H hH
  have h3 : ((∑ d ∈ Finset.Icc 2 H, (H / d) ^ 2 : ℕ) : ℝ) ≤ 3 / 4 * (H : ℝ) ^ 2 := by
    push_cast; exact h2
  have h4 : (((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
      (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2)).card : ℝ) ≤ 3 / 4 * (H : ℝ) ^ 2 :=
    le_trans (by exact_mod_cast h1) h3
  have h5 : ((((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
      (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2))).card : ℝ) +
      (((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
      (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2)).card : ℝ) = (H : ℝ) ^ 2 := by
    rw [hc] at hsplit; exact_mod_cast hsplit
  linarith

/-- Lemma 2.3, eq. (07) with `c₁ = 1/4` and `H₀ = 1`: `|ℚ_H| ≥ H²/4`. -/
theorem card_ratsUpTo_ge (H : ℕ) : (H : ℝ) ^ 2 / 4 ≤ (ratsUpTo H).card := by
  refine (card_coprime_ge H).trans ?_
  have : (((Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter
      (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2))).card ≤ (ratsUpTo H).card := by
    refine card_le_card_of_injOn (fun p => ((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ)) ?_ ?_
    · intro p hp
      simp only [coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp
      rw [mem_coe, mem_ratsUpTo]
      have hq : (0 : ℤ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
      have hcop : Nat.Coprime (p.1 : ℤ).natAbs ((p.2 : ℤ)).natAbs := by simpa using hp.2
      have hn := Rat.num_div_eq_of_coprime hq hcop
      have hd := Rat.den_div_eq_of_coprime hq hcop
      unfold ratHeight
      rw [hn]
      have hd' : (((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ)).den = p.2 := by exact_mod_cast hd
      rw [hd']
      simp; omega
    · intro p hp p' hp' h
      simp only [coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp hp'
      have hq : (0 : ℤ) < p.2 := by exact_mod_cast (show 0 < p.2 by omega)
      have hq' : (0 : ℤ) < p'.2 := by exact_mod_cast (show 0 < p'.2 by omega)
      have hcop : Nat.Coprime (p.1 : ℤ).natAbs ((p.2 : ℤ)).natAbs := by simpa using hp.2
      have hcop' : Nat.Coprime (p'.1 : ℤ).natAbs ((p'.2 : ℤ)).natAbs := by simpa using hp'.2
      have hn := Rat.num_div_eq_of_coprime hq hcop
      have hd := Rat.den_div_eq_of_coprime hq hcop
      have hn' := Rat.num_div_eq_of_coprime hq' hcop'
      have hd' := Rat.den_div_eq_of_coprime hq' hcop'
      simp only at h
      rw [h] at hn hd
      ext
      · have := hn.symm.trans hn'; omega
      · have := hd.symm.trans hd'; omega
  exact_mod_cast this

/-! ### Height ordering of `ℚ` and generic ranks -/

/-- An injective numerical key that orders `ℚ` first by height, then by denominator, then by
numerator (the order used for the enumerations of eq. (05)). -/
def ratKey (r : ℚ) : ℕ :=
  4 * ratHeight r ^ 3 + r.den * (2 * ratHeight r + 1) + (r.num + ratHeight r).toNat

lemma ratKey_lt_iff_aux (r : ℚ) :
    r.den * (2 * ratHeight r + 1) + (r.num + ratHeight r).toNat < 4 * (ratHeight r + 1) ^ 3
      - 4 * ratHeight r ^ 3 := by
  have h1 := natAbs_num_le_ratHeight r
  have h2 := den_le_ratHeight r
  set H := ratHeight r
  have h3 : (r.num + H).toNat ≤ 2 * H := by omega
  have h4 : r.den * (2 * H + 1) ≤ H * (2 * H + 1) := Nat.mul_le_mul_right _ h2
  have h5 : 4 * (H + 1) ^ 3 = 4 * H ^ 3 + 12 * H ^ 2 + 12 * H + 4 := by ring
  have h6 : H * (2 * H + 1) = 2 * H ^ 2 + H := by ring
  omega

/-- The key is strictly monotone in the height. -/
lemma ratKey_lt_of_height_lt {r r' : ℚ} (h : ratHeight r < ratHeight r') : ratKey r < ratKey r' := by
  have a1 := ratKey_lt_iff_aux r
  have : 4 * (ratHeight r + 1) ^ 3 ≤ 4 * ratHeight r' ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)
  have : 4 * ratHeight r ^ 3 ≤ 4 * (ratHeight r + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  unfold ratKey; omega

lemma height_le_of_ratKey_lt {r r' : ℚ} (h : ratKey r < ratKey r') : ratHeight r ≤ ratHeight r' := by
  by_contra h'
  have := ratKey_lt_of_height_lt (not_le.1 h')
  omega

lemma ratKey_injective : Function.Injective ratKey := by
  intro r r' h
  have hH : ratHeight r = ratHeight r' := by
    rcases lt_trichotomy (ratHeight r) (ratHeight r') with h1 | h1 | h1
    · have := ratKey_lt_of_height_lt h1; omega
    · exact h1
    · have := ratKey_lt_of_height_lt h1; omega
  unfold ratKey at h
  rw [hH] at h
  set H := ratHeight r'
  have hd1 := den_le_ratHeight r
  have hd2 := den_le_ratHeight r'
  have hn1 := natAbs_num_le_ratHeight r
  have hn2 := natAbs_num_le_ratHeight r'
  rw [hH] at hd1 hn1
  have hden : r.den = r'.den := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have : r.den * (2 * H + 1) + (2 * H + 1) ≤ r'.den * (2 * H + 1) := by nlinarith
      omega
    · have : r'.den * (2 * H + 1) + (2 * H + 1) ≤ r.den * (2 * H + 1) := by nlinarith
      omega
  rw [hden] at h
  have hnum : r.num = r'.num := by omega
  exact Rat.ext hnum hden

/-- Generic rank attached to an injective key `e : α → ℕ`: the number of elements whose key is
smaller. -/
noncomputable def keyRank {α : Type*} (e : α → ℕ) (a : α) : ℕ :=
  open Classical in Nat.count (fun n => n ∈ Set.range e) (e a)

lemma keyRank_bijective {α : Type*} {e : α → ℕ} (he : Function.Injective e)
    (hinf : (Set.range e).Infinite) : Function.Bijective (keyRank e) := by
  classical
  constructor
  · intro a b h
    unfold keyRank at h
    exact he (Nat.count_injective (p := fun n => n ∈ Set.range e) ⟨a, rfl⟩ ⟨b, rfl⟩
      (by convert h))
  · intro n
    have hinf' : (setOf fun n => n ∈ Set.range e).Infinite := by simpa using hinf
    obtain ⟨a, ha⟩ := Nat.nth_mem_of_infinite hinf' n
    refine ⟨a, ?_⟩
    unfold keyRank
    rw [ha]
    convert Nat.count_nth_of_infinite hinf' n

lemma keyRank_lt_iff {α : Type*} {e : α → ℕ} (he : Function.Injective e) (a b : α) :
    keyRank e a < keyRank e b ↔ e a < e b := by
  classical
  unfold keyRank
  constructor
  · intro h
    by_contra h'
    have := Nat.count_monotone (fun n => n ∈ Set.range e) (not_lt.1 h')
    exact absurd h (not_lt.2 (by convert this))
  · intro h
    convert Nat.count_strict_mono (p := fun n => n ∈ Set.range e) ⟨a, rfl⟩ h

/-- The rank of `a` is bounded by the number of elements of any finite set containing every
element whose key is smaller. -/
lemma keyRank_le_card {α : Type*} {e : α → ℕ} (he : Function.Injective e) (a : α) (S : Finset α)
    (hS : ∀ b, e b < e a → b ∈ S) : keyRank e a ≤ (S.filter (fun b => e b < e a)).card := by
  classical
  unfold keyRank
  rw [Nat.count_eq_card_filter_range]
  calc ((Finset.range (e a)).filter (fun n => n ∈ Set.range e)).card
      ≤ ((S.filter (fun b => e b < e a)).image e).card := by
        apply card_le_card
        intro n hn
        simp only [mem_filter, mem_range, Set.mem_range] at hn
        obtain ⟨hn, b, rfl⟩ := hn
        simp only [mem_image, mem_filter]
        exact ⟨b, ⟨hS b hn, hn⟩, rfl⟩
    _ ≤ _ := card_image_le

/-- Pigeonhole: an injective map into `ℕ` takes a value `≥ |S| - 1` on a nonempty finite set. -/
lemma exists_ge_card_sub_one {α : Type*} {A : α → ℕ} (hA : Function.Injective A) (S : Finset α)
    (hS : S.Nonempty) : ∃ a ∈ S, S.card - 1 ≤ A a := by
  classical
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image A hS
  refine ⟨a, ha, ?_⟩
  have : (S.image A) ⊆ Finset.range (A a + 1) := by
    intro n hn
    simp only [mem_image] at hn
    obtain ⟨b, hb, rfl⟩ := hn
    simp only [mem_range]; exact Nat.lt_succ_of_le (hmax b hb)
  have h1 := card_le_card this
  rw [card_image_of_injective _ hA, card_range] at h1
  omega

lemma sup_ge_card_sub_one {α : Type*} {A : α → ℕ} (hA : Function.Injective A) (S : Finset α) :
    S.card - 1 ≤ S.sup A := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · obtain ⟨a, ha, h1⟩ := exists_ge_card_sub_one hA S h
    exact h1.trans (Finset.le_sup ha)

lemma ratKey_range_infinite : (Set.range ratKey).Infinite :=
  Set.infinite_range_of_injective ratKey_injective

/-- The rank of a rational in the height enumeration `Q` of eq. (05). -/
noncomputable def rankQ (r : ℚ) : ℕ := keyRank ratKey r

/-- Lemma 2.4: the height enumeration `Q : ℕ → ℚ` is a bijection (here: its rank map). -/
theorem rankQ_bijective : Function.Bijective rankQ :=
  keyRank_bijective ratKey_injective ratKey_range_infinite

/-- The enumeration `Q : ℕ → ℚ`. -/
noncomputable def enumQ : ℕ ≃ ℚ := (Equiv.ofBijective rankQ rankQ_bijective).symm

/-- The height-ordered rank on `ℚ^*`. -/
noncomputable def rankQstar (s : {s : ℚ // s ≠ 0}) : ℕ := keyRank (fun s => ratKey s.1) s

theorem rankQstar_bijective : Function.Bijective rankQstar := by
  refine keyRank_bijective (fun a b h => Subtype.ext (ratKey_injective h)) ?_
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ratKey ((n : ℚ) + 1)) ?_ ?_
  · intro a b h
    have := ratKey_injective h
    simp only [add_left_inj, Nat.cast_inj] at this
    exact this
  · intro n
    exact ⟨⟨(n : ℚ) + 1, by positivity⟩, rfl⟩

/-- The enumeration `Q^* : ℕ → ℚ^*`. -/
noncomputable def enumQstar : ℕ ≃ {s : ℚ // s ≠ 0} :=
  (Equiv.ofBijective rankQstar rankQstar_bijective).symm

/-- Lemma 2.4: if `ht(r) ≤ H` then the rank of `r` is `< 3H²`. -/
theorem rankQ_lt {r : ℚ} {H : ℕ} (h : ratHeight r ≤ H) : rankQ r < 3 * H ^ 2 := by
  have hH : 1 ≤ H := (one_le_ratHeight r).trans h
  have h1 := keyRank_le_card ratKey_injective r (ratsUpTo H) (fun b hb => by
    rw [mem_ratsUpTo]; exact (height_le_of_ratKey_lt hb).trans h)
  have h2 : ((ratsUpTo H).filter (fun b => ratKey b < ratKey r)).card < (ratsUpTo H).card := by
    apply card_lt_card
    refine ⟨filter_subset _ _, fun hsub => ?_⟩
    have := hsub (mem_ratsUpTo.2 h)
    simp at this
  have h3 := card_ratsUpTo_le hH
  unfold rankQ; omega

theorem rankQstar_lt {s : {s : ℚ // s ≠ 0}} {H : ℕ} (h : ratHeight s.1 ≤ H) :
    rankQstar s < 3 * H ^ 2 := by
  have hH : 1 ≤ H := (one_le_ratHeight _).trans h
  classical
  let S : Finset {s : ℚ // s ≠ 0} := (ratsUpTo H).subtype (fun s => s ≠ 0)
  have hmem : ∀ b : {s : ℚ // s ≠ 0}, b ∈ S ↔ ratHeight b.1 ≤ H := by
    intro b; simp [S, mem_ratsUpTo]
  have h1 := keyRank_le_card (e := fun s : {s : ℚ // s ≠ 0} => ratKey s.1)
    (fun a b h => Subtype.ext (ratKey_injective h)) s S (fun b hb => by
      rw [hmem]; exact (height_le_of_ratKey_lt hb).trans h)
  have h2 : (S.filter (fun b => ratKey b.1 < ratKey s.1)).card < S.card := by
    apply card_lt_card
    refine ⟨filter_subset _ _, fun hsub => ?_⟩
    have := hsub ((hmem s).2 h)
    simp at this
  have h3 : S.card ≤ (ratsUpTo H).card := by
    simp only [S]; rw [card_subtype]; exact card_filter_le _ _
  have h4 := card_ratsUpTo_le hH
  beta_reduce at h1
  unfold rankQstar; omega

end Dyadic.Lib
