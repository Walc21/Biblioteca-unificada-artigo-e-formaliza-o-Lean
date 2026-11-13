import Mathlib

/-!
# Section 2 — Elementary indexing (Lemma "indexação elementar")

Cantor pairing `π`, the integer bijection `Z`, the height of a rational,
the finite sets `𝒬_H = {r : ht r ≤ H}`, and the enumerations `Q`, `Q*` of the
rationals by height, then denominator, then numerator.

We also develop a general "shell enumeration" principle: if a type is exhausted by
finite shells `S H = {a : lvl a ≤ H}`, listing the shells in increasing order (each shell
ordered by an injective key) gives a bijection with `ℕ` that lists `S H` first.
-/

namespace Artigo

open Finset

/-! ## Cantor pairing -/

/-- The Cantor pairing `π(u,v) = (u+v)(u+v+1)/2 + v`. -/
def cantorPair (u v : ℕ) : ℕ := (u + v) * (u + v + 1) / 2 + v

/-- triangular numbers -/
def tri (w : ℕ) : ℕ := w * (w + 1) / 2

lemma tri_succ (w : ℕ) : tri (w + 1) = tri w + (w + 1) := by
  unfold tri
  have h1 : (w + 1) * (w + 1 + 1) = w * (w + 1) + 2 * (w + 1) := by ring
  rw [h1, Nat.add_mul_div_left _ _ (by norm_num)]

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  unfold tri; exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

lemma cantorPair_eq (u v : ℕ) : cantorPair u v = tri (u + v) + v := rfl

lemma tri_add_lt {w v : ℕ} (hv : v ≤ w) : tri w + v < tri (w + 1) := by
  rw [tri_succ]; omega

/-- the diagonal index is determined by the value -/
lemma diag_unique {w w' v v' : ℕ} (hv : v ≤ w) (hv' : v' ≤ w')
    (h : tri w + v = tri w' + v') : w = w' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := tri_add_lt hv
    have := tri_mono (show w + 1 ≤ w' by omega)
    omega
  · have := tri_add_lt hv'
    have := tri_mono (show w' + 1 ≤ w by omega)
    omega

theorem cantorPair_injective : Function.Injective (fun p : ℕ × ℕ => cantorPair p.1 p.2) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only [cantorPair_eq] at h
  have hw := diag_unique (by omega) (by omega) h
  have : v = v' := by rw [hw] at h; omega
  simp only [Prod.mk.injEq]; omega

theorem cantorPair_surjective : Function.Surjective (fun p : ℕ × ℕ => cantorPair p.1 p.2) := by
  intro n
  have hex : ∃ w, n < tri (w + 1) := ⟨n, by rw [tri_succ]; omega⟩
  let w := Nat.find hex
  have hw : n < tri (w + 1) := Nat.find_spec hex
  have hw' : tri w ≤ n := by
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · rw [h0]; simp [tri]
    · have := Nat.find_min hex (show w - 1 < w by omega)
      rw [show w - 1 + 1 = w by omega] at this
      omega
  refine ⟨(w - (n - tri w), n - tri w), ?_⟩
  simp only [cantorPair_eq]
  rw [tri_succ] at hw
  rw [show w - (n - tri w) + (n - tri w) = w by omega]
  omega

/-- **Lemma 2.1 (a)**: the Cantor pairing is a bijection `ℕ × ℕ → ℕ`. -/
theorem cantorPair_bijective : Function.Bijective (fun p : ℕ × ℕ => cantorPair p.1 p.2) :=
  ⟨cantorPair_injective, cantorPair_surjective⟩

/-- **Lemma 2.1 (a)**: `π(u,v) ≤ (u+v+1)^2`. -/
theorem cantorPair_le (u v : ℕ) : cantorPair u v ≤ (u + v + 1) ^ 2 := by
  unfold cantorPair
  have : (u + v) * (u + v + 1) / 2 ≤ (u + v) * (u + v + 1) := Nat.div_le_self _ _
  nlinarith

lemma cantorPair_ge_sq (u v : ℕ) : (u + v) ^ 2 ≤ 2 * cantorPair u v := by
  unfold cantorPair
  generalize u + v = w
  have h1 := Nat.div_add_mod (w * (w + 1)) 2
  have h2 : w * (w + 1) % 2 = 0 := by
    rcases Nat.even_or_odd w with ⟨j, hj⟩ | ⟨j, hj⟩ <;> subst hj <;> ring_nf <;> omega
  nlinarith

/-! ## The bijection `Z : ℕ → ℤ` -/

/-- `Z(2j) = j`, `Z(2j+1) = -j-1`. -/
def Zenum (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ) - 1

/-- The inverse of `Z`. -/
def Zinv (m : ℤ) : ℕ := if 0 ≤ m then 2 * m.toNat else 2 * (-m - 1).toNat + 1

lemma Zenum_Zinv (m : ℤ) : Zenum (Zinv m) = m := by
  unfold Zinv Zenum
  split_ifs with h1 h2 h2 <;> omega

lemma Zinv_Zenum (n : ℕ) : Zinv (Zenum n) = n := by
  unfold Zinv Zenum
  split_ifs with h1 h2 h2 <;> omega

/-- **Lemma 2.1 (b)**: `Z` is a bijection. -/
theorem Zenum_bijective : Function.Bijective Zenum :=
  ⟨Function.LeftInverse.injective Zinv_Zenum, Function.RightInverse.surjective Zenum_Zinv⟩

lemma Zinv_injective : Function.Injective Zinv :=
  Function.LeftInverse.injective Zenum_Zinv

/-- **Lemma 2.1 (b)**: `Z⁻¹(m) ≤ 2|m|+1`. -/
theorem Zinv_le (m : ℤ) : (Zinv m : ℤ) ≤ 2 * |m| + 1 := by
  unfold Zinv; split_ifs with h <;> [rw [abs_of_nonneg h]; rw [abs_of_neg (by omega)]] <;> omega

lemma Zinv_le_nat (m : ℤ) : Zinv m ≤ 2 * m.natAbs + 1 := by
  have := Zinv_le m
  have h2 : |m| = (m.natAbs : ℤ) := Int.abs_eq_natAbs m
  omega

/-! ## Height of a rational -/

/-- `ht(p/q) = max{|p|, q}` for the reduced fraction. -/
def ht (r : ℚ) : ℕ := max r.num.natAbs r.den

lemma one_le_ht (r : ℚ) : 1 ≤ ht r := le_max_of_le_right r.den_pos

lemma den_div_le (p : ℤ) (q : ℕ) (hq : 0 < q) : ((p : ℚ) / q).den ≤ q := by
  have := Rat.den_dvd p q
  rw [Rat.divInt_eq_div] at this
  push_cast at this
  exact Nat.le_of_dvd hq (by exact_mod_cast this)

lemma num_div_le (p : ℤ) (q : ℕ) (hq : 0 < q) : ((p : ℚ) / q).num.natAbs ≤ p.natAbs := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have := Rat.num_dvd p (b := q) (by exact_mod_cast hq.ne')
  rw [Rat.divInt_eq_div] at this
  push_cast at this
  exact Nat.le_of_dvd (by omega) (Int.natAbs_dvd_natAbs.mpr this)

/-- Reducing a fraction never increases the height. -/
lemma ht_div_le (p : ℤ) (q : ℕ) (hq : 0 < q) : ht ((p : ℚ) / q) ≤ max p.natAbs q :=
  max_le_max (num_div_le p q hq) (den_div_le p q hq)

lemma ht_div_le' (p : ℤ) (q : ℤ) (hq : 0 < q) : ht ((p : ℚ) / q) ≤ max p.natAbs q.natAbs := by
  have := ht_div_le p q.natAbs (by omega)
  have hq' : ((q.natAbs : ℕ) : ℚ) = (q : ℚ) := by
    have : ((q.natAbs : ℕ) : ℤ) = q := by omega
    rw [← Int.cast_natCast, this]
  rwa [hq'] at this

lemma ht_zero : ht 0 = 1 := by simp [ht]

lemma ht_neg (r : ℚ) : ht (-r) = ht r := by simp [ht]

lemma ht_intCast (z : ℤ) : ht (z : ℚ) = max z.natAbs 1 := by simp [ht]

/-! ## The finite sets `𝒬_H` -/

/-- `𝒬_H = {r ∈ ℚ : ht r ≤ H}` as a (computable) finite set. -/
def QH (H : ℕ) : Finset ℚ :=
  (((Icc (-(H : ℤ)) H) ×ˢ (Icc 1 H)).image (fun p : ℤ × ℕ => (p.1 : ℚ) / p.2)).filter
    (fun r => ht r ≤ H)

lemma mem_QH {H : ℕ} {r : ℚ} : r ∈ QH H ↔ ht r ≤ H := by
  unfold QH
  simp only [mem_filter, mem_image, mem_product, mem_Icc, Prod.exists]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨⟨r.num, r.den, ⟨⟨?_, ?_⟩, r.den_pos, ?_⟩, Rat.num_div_den r⟩, h⟩
    · have := le_trans (le_max_left _ _) h
      unfold ht at *; omega
    · have := le_trans (le_max_left _ _) h
      unfold ht at *; omega
    · exact le_trans (le_max_right _ _) h

lemma QH_mono {H H' : ℕ} (h : H ≤ H') : QH H ⊆ QH H' := by
  intro r; simp only [mem_QH]; omega

lemma zero_mem_QH {H : ℕ} (h : 1 ≤ H) : (0 : ℚ) ∈ QH H := by
  rw [mem_QH, ht_zero]; exact h

/-- **Lemma 2.1 (c)**: `|𝒬_H| ≤ 3H^2`. -/
theorem card_QH_le (H : ℕ) : (QH H).card ≤ 3 * H ^ 2 := by
  unfold QH
  refine le_trans (card_filter_le _ _) (le_trans card_image_le ?_)
  rw [card_product, Int.card_Icc, Nat.card_Icc]
  rcases Nat.eq_zero_or_pos H with h | h
  · subst h; simp
  · have : ((H : ℤ) + 1 - -(H : ℤ)).toNat = 2 * H + 1 := by omega
    rw [this, Nat.add_sub_cancel]; nlinarith

/-! ### Lower bound for `|𝒬_H|` via coprime pairs -/

/-- pairs in `[1,H]^2` both divisible by `d` -/
lemma card_pairs_dvd_le (H d : ℕ) (hd : 0 < d) :
    (((Icc 1 H) ×ˢ (Icc 1 H)).filter (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2)).card ≤ (H / d) ^ 2 := by
  have hsub : ((Icc 1 H) ×ˢ (Icc 1 H)).filter (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2) ⊆
      ((Icc 1 (H / d)) ×ˢ (Icc 1 (H / d))).image (fun p : ℕ × ℕ => (d * p.1, d * p.2)) := by
    rintro ⟨p1, p2⟩ hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hp
    simp only [mem_image, mem_product, mem_Icc, Prod.exists, Prod.mk.injEq]
    refine ⟨a, b, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ha.symm, hb.symm⟩
    · exact Nat.pos_of_ne_zero (by rintro rfl; simp at ha; omega)
    · rw [Nat.le_div_iff_mul_le hd]; rw [ha] at h2; linarith [mul_comm a d]
    · exact Nat.pos_of_ne_zero (by rintro rfl; simp at hb; omega)
    · rw [Nat.le_div_iff_mul_le hd]; rw [hb] at h4; linarith [mul_comm b d]
  refine le_trans (card_le_card hsub) (le_trans card_image_le ?_)
  rw [card_product, Nat.card_Icc, Nat.add_sub_cancel]; ring_nf; rfl

lemma odd_recip_sq_sum (n : ℕ) :
    ∑ i ∈ range n, (1 : ℚ) / (2 * (i : ℚ) + 3) ^ 2 ≤ 1 / 4 - 1 / (4 * ((n : ℚ) + 1)) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ]
    have key : (1 : ℚ) / (2 * (n : ℚ) + 3) ^ 2 ≤ 1 / (4 * ((n : ℚ) + 1)) - 1 / (4 * ((n + 1 : ℕ) + 1)) := by
      push_cast
      have e : (1 : ℚ) / (4 * ((n : ℚ) + 1)) - 1 / (4 * ((n : ℚ) + 1 + 1)) =
          1 / (4 * ((n : ℚ) + 1) * ((n : ℚ) + 2)) := by field_simp; ring
      rw [e]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    push_cast at *
    linarith

/-- the number of non-coprime pairs in `[1,H]^2` is at most `H^2/2`. -/
lemma card_noncoprime_le (H : ℕ) :
    2 * (((Icc 1 H) ×ˢ (Icc 1 H)).filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2)).card ≤ H ^ 2 := by
  set D : Finset ℕ := insert 2 ((range H).image (fun i => 2 * i + 3)) with hD
  have hsub : ((Icc 1 H) ×ˢ (Icc 1 H)).filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2) ⊆
      D.biUnion (fun d => ((Icc 1 H) ×ˢ (Icc 1 H)).filter (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2)) := by
    intro p hp
    simp only [mem_filter, mem_product, mem_Icc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hnc⟩ := hp
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hnc
    have hq1 := (Nat.dvd_gcd_iff.mp hqd)
    simp only [mem_biUnion, mem_filter, mem_product, mem_Icc]
    refine ⟨q, ?_, ⟨⟨h1, h2⟩, h3, h4⟩, hq1⟩
    rcases hq.eq_two_or_odd' with h2q | hodd
    · rw [hD, h2q]; exact mem_insert_self _ _
    · rw [hD]; apply mem_insert_of_mem
      obtain ⟨j, hj⟩ := hodd
      have hq2 := hq.two_le
      have hqH : q ≤ H := le_trans (Nat.le_of_dvd (by omega) hq1.1) h2
      simp only [mem_image, mem_range]
      refine ⟨j - 1, by omega, by omega⟩
  have hcard := le_trans (card_le_card hsub) card_biUnion_le
  have hbound : ∑ d ∈ D, (((Icc 1 H) ×ˢ (Icc 1 H)).filter
      (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2)).card ≤ ∑ d ∈ D, (H / d) ^ 2 := by
    apply sum_le_sum; intro d hd
    apply card_pairs_dvd_le
    rw [hD] at hd; simp only [mem_insert, mem_image] at hd
    rcases hd with h | ⟨i, _, rfl⟩ <;> omega
  have hq : (2 : ℚ) * ∑ d ∈ D, ((H / d : ℕ) : ℚ) ^ 2 ≤ (H : ℚ) ^ 2 := by
    have h2notin : 2 ∉ (range H).image (fun i => 2 * i + 3) := by
      simp only [mem_image, not_exists, not_and]; intro i _; omega
    rw [hD, sum_insert h2notin, sum_image (by intro a _ b _ h; simp at h; omega)]
    have e1 : ((H / 2 : ℕ) : ℚ) ≤ (H : ℚ) / 2 := Nat.cast_div_le
    have e1' : ((H / 2 : ℕ) : ℚ) ^ 2 ≤ ((H : ℚ) / 2) ^ 2 := pow_le_pow_left₀ (by positivity) e1 2
    have e2 : ∑ x ∈ range H, ((H / (2 * x + 3) : ℕ) : ℚ) ^ 2 ≤
        ∑ x ∈ range H, (H : ℚ) ^ 2 * (1 / (2 * (x : ℚ) + 3) ^ 2) := by
      apply sum_le_sum; intro i _
      have : ((H / (2 * i + 3) : ℕ) : ℚ) ≤ (H : ℚ) / (2 * i + 3) := by
        have := (Nat.cast_div_le (α := ℚ) (m := H) (n := 2 * i + 3)); push_cast at this; exact this
      have := pow_le_pow_left₀ (by positivity) this 2
      rw [div_pow] at this; rw [mul_one_div]; exact this
    rw [← mul_sum] at e2
    have e3 := odd_recip_sq_sum H
    have e4 : (1 : ℚ) / 4 - 1 / (4 * ((H : ℚ) + 1)) ≤ 1 / 4 := by
      have : (0 : ℚ) ≤ 1 / (4 * ((H : ℚ) + 1)) := by positivity
      linarith
    have hH : (0 : ℚ) ≤ (H : ℚ) ^ 2 := by positivity
    nlinarith
  have hnat : 2 * ∑ d ∈ D, (H / d) ^ 2 ≤ H ^ 2 := by exact_mod_cast hq
  omega

/-- coprime pairs give distinct rationals of height `≤ H`. -/
lemma card_coprime_le_QH (H : ℕ) :
    (((Icc 1 H) ×ˢ (Icc 1 H)).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card ≤ (QH H).card := by
  apply card_le_card_of_injOn (fun p : ℕ × ℕ => ((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ))
  · intro p hp
    simp only [coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp
    simp only [mem_coe, mem_QH]
    have := ht_div_le' (p.1 : ℤ) (p.2 : ℤ) (by omega)
    simp only [Int.natAbs_natCast] at this
    omega
  · intro p hp q hq hpq
    simp only [coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp hq
    simp only at hpq
    have hp1 := Rat.num_div_eq_of_coprime (a := (p.1 : ℤ)) (b := (p.2 : ℤ)) (by omega)
      (by simpa using hp.2)
    have hp2 := Rat.den_div_eq_of_coprime (a := (p.1 : ℤ)) (b := (p.2 : ℤ)) (by omega)
      (by simpa using hp.2)
    have hq1 := Rat.num_div_eq_of_coprime (a := (q.1 : ℤ)) (b := (q.2 : ℤ)) (by omega)
      (by simpa using hq.2)
    have hq2 := Rat.den_div_eq_of_coprime (a := (q.1 : ℤ)) (b := (q.2 : ℤ)) (by omega)
      (by simpa using hq.2)
    rw [hpq] at hp1 hp2
    ext <;> omega

/-- **Lemma 2.1 (c)**: `|𝒬_H| ≥ H^2/2` (in particular `≥ H^2/4`) for every `H`. -/
theorem card_QH_ge_half (H : ℕ) : H ^ 2 ≤ 2 * (QH H).card := by
  have h1 := card_noncoprime_le H
  have h2 := card_coprime_le_QH H
  have h3 := filter_card_add_filter_neg_card_eq_card (s := (Icc 1 H) ×ˢ (Icc 1 H))
    (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)
  rw [card_product, Nat.card_Icc, Nat.add_sub_cancel] at h3
  nlinarith

/-- **Lemma 2.1 (c)**: `|𝒬_H| ≥ H^2/4` for `H` sufficiently large (in fact for all `H`). -/
theorem card_QH_ge (H : ℕ) : (H : ℝ) ^ 2 / 4 ≤ (QH H).card := by
  have := card_QH_ge_half H
  have h : ((H ^ 2 : ℕ) : ℝ) ≤ ((2 * (QH H).card : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h
  have : (0 : ℝ) ≤ (QH H).card := by positivity
  linarith

/-! ## General shell enumerations

A type exhausted by finite shells `S H = {a : lvl a ≤ H}` is enumerated by listing the
shells in increasing order of `H`, each one ordered by an injective key. -/

section ShellEnum

variable {α γ : Type*} [DecidableEq α] [LinearOrder γ]

/-- The position of `a` in the shell enumeration. -/
def shellRank (S : ℕ → Finset α) (lvl : α → ℕ) (key : α → γ) (a : α) : ℕ :=
  ((S (lvl a)).filter (fun b => toLex (lvl b, key b) < toLex (lvl a, key a))).card

variable (S : ℕ → Finset α) (lvl : α → ℕ) (key : α → γ)
  (hS : ∀ a H, a ∈ S H ↔ lvl a ≤ H) (hkey : Function.Injective key)
include hS

omit [LinearOrder γ] in
lemma shell_mono {H H' : ℕ} (h : H ≤ H') : S H ⊆ S H' := by
  intro a; rw [hS, hS]; omega

lemma lvl_le_of_lt {a b : α} (h : toLex (lvl b, key b) < toLex (lvl a, key a)) : lvl b ≤ lvl a := by
  rw [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, _⟩ <;> omega

lemma shellRank_eq {a : α} {H : ℕ} (ha : lvl a ≤ H) :
    shellRank S lvl key a = ((S H).filter (fun b => toLex (lvl b, key b) < toLex (lvl a, key a))).card := by
  unfold shellRank
  congr 1
  ext b
  simp only [mem_filter, hS]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨_, h2⟩; exact ⟨lvl_le_of_lt S lvl key hS h2, h2⟩

/-- Every element of `S H` has rank `< |S H|`. -/
lemma shellRank_lt {a : α} {H : ℕ} (ha : lvl a ≤ H) : shellRank S lvl key a < (S H).card := by
  rw [shellRank_eq S lvl key hS ha]
  apply card_lt_card
  refine ⟨filter_subset _ _, fun h => ?_⟩
  have := h ((hS a H).mpr ha)
  simp at this

lemma shellRank_strictMono {a a' : α}
    (h : toLex (lvl a, key a) < toLex (lvl a', key a')) :
    shellRank S lvl key a < shellRank S lvl key a' := by
  have hl := lvl_le_of_lt S lvl key hS h
  rw [shellRank_eq S lvl key hS (le_refl (lvl a')), shellRank_eq S lvl key hS hl]
  apply card_lt_card
  refine ⟨fun b hb => ?_, fun hsub => ?_⟩
  · simp only [mem_filter] at hb ⊢; exact ⟨hb.1, lt_trans hb.2 h⟩
  · have : a ∈ (S (lvl a')).filter (fun b => toLex (lvl b, key b) < toLex (lvl a', key a')) := by
      simp only [mem_filter]; exact ⟨(hS _ _).mpr hl, h⟩
    have := hsub this
    simp at this

include hkey in
lemma shellRank_injective : Function.Injective (shellRank S lvl key) := by
  intro a a' h
  by_contra hne
  have hne' : toLex (lvl a, key a) ≠ toLex (lvl a', key a') := by
    intro h'
    simp only [toLex_inj, Prod.mk.injEq] at h'
    exact hne (hkey h'.2)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · have := shellRank_strictMono S lvl key hS hlt; omega
  · have := shellRank_strictMono S lvl key hS hlt; omega

include hkey in
/-- The enumeration lists exactly `S H` in the first `|S H|` positions. -/
lemma shellRank_image (H : ℕ) : (S H).image (shellRank S lvl key) = range (S H).card := by
  apply eq_of_subset_of_card_le
  · intro n hn
    simp only [mem_image] at hn
    obtain ⟨a, ha, rfl⟩ := hn
    exact mem_range.mpr (shellRank_lt S lvl key hS ((hS a H).mp ha))
  · rw [card_range, card_image_of_injective _ (shellRank_injective S lvl key hS hkey)]

include hkey in
lemma shellRank_surjective (hunb : ∀ n, ∃ H, n < (S H).card) :
    Function.Surjective (shellRank S lvl key) := by
  intro n
  obtain ⟨H, hH⟩ := hunb n
  have : n ∈ (S H).image (shellRank S lvl key) := by
    rw [shellRank_image S lvl key hS hkey]; exact mem_range.mpr hH
  simp only [mem_image] at this
  obtain ⟨a, _, ha⟩ := this
  exact ⟨a, ha⟩

end ShellEnum

/-! ## The enumerations `Q : ℕ → ℚ` and `Q* : ℕ → ℚ*` -/

/-- order key: height, then denominator, then numerator. -/
def ratKey (r : ℚ) : ℕ ×ₗ ℤ := toLex (r.den, r.num)

lemma ratKey_injective : Function.Injective ratKey := by
  intro r r' h
  simp only [ratKey, toLex_inj, Prod.mk.injEq] at h
  exact Rat.ext h.2 h.1

/-- the rank of `r` in the enumeration `Q` (by height, then denominator, then numerator). -/
def rankQ (r : ℚ) : ℕ := shellRank QH ht ratKey r

/-- `𝒬_H ∖ {0}` -/
def QsH (H : ℕ) : Finset ℚ := (QH H).erase 0

/-- the level used for `Q*`: same height, but `0` is pushed to infinity is not needed since
`0 ∉ ℚ*`; we use the height on `ℚ*` (subtype). -/
def rankQs (r : ℚ) : ℕ :=
  ((QsH (ht r)).filter (fun b => toLex (ht b, ratKey b) < toLex (ht r, ratKey r))).card

lemma mem_QsH {H : ℕ} {r : ℚ} : r ∈ QsH H ↔ r ≠ 0 ∧ ht r ≤ H := by
  simp [QsH, mem_QH]

lemma QH_unbounded (n : ℕ) : ∃ H, n < (QH H).card := by
  refine ⟨2 * n + 2, ?_⟩
  have := card_QH_ge_half (2 * n + 2)
  nlinarith

theorem rankQ_injective : Function.Injective rankQ :=
  shellRank_injective QH ht ratKey (fun _ _ => mem_QH) ratKey_injective

theorem rankQ_surjective : Function.Surjective rankQ :=
  shellRank_surjective QH ht ratKey (fun _ _ => mem_QH) ratKey_injective QH_unbounded

/-- The enumeration `Q : ℕ → ℚ` (inverse of the rank). -/
noncomputable def Qenum : ℕ → ℚ := Function.invFun rankQ

theorem Qenum_bijective : Function.Bijective Qenum := by
  refine ⟨?_, ?_⟩
  · exact (Function.rightInverse_invFun rankQ_surjective).injective
  · exact (Function.leftInverse_invFun rankQ_injective).surjective

lemma rankQ_lt {r : ℚ} {H : ℕ} (h : ht r ≤ H) : rankQ r < (QH H).card :=
  shellRank_lt QH ht ratKey (fun _ _ => mem_QH) h

lemma rankQ_image (H : ℕ) : (QH H).image rankQ = range (QH H).card :=
  shellRank_image QH ht ratKey (fun _ _ => mem_QH) ratKey_injective H

/-! `Q*` is the shell enumeration of the subtype `ℚ*`. -/

/-- shells of `ℚ*` -/
def QsShell (H : ℕ) : Finset {r : ℚ // r ≠ 0} := (QH H).subtype (fun r => r ≠ 0)

lemma mem_QsShell {H : ℕ} {r : {r : ℚ // r ≠ 0}} : r ∈ QsShell H ↔ ht r.1 ≤ H := by
  simp [QsShell, mem_QH]

lemma rankQs_eq (r : {r : ℚ // r ≠ 0}) :
    rankQs r.1 = shellRank QsShell (fun r => ht r.1) (fun r => ratKey r.1) r := by
  unfold rankQs shellRank QsShell
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext b
  simp only [mem_filter, QsH, mem_erase, mem_map, mem_subtype, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨⟨hb0, hb⟩, hlt⟩; exact ⟨⟨b, hb0⟩, ⟨hb, hlt⟩, rfl⟩
  · rintro ⟨c, ⟨hc, hlt⟩, rfl⟩; exact ⟨⟨c.2, hc⟩, hlt⟩

lemma QsShell_card (H : ℕ) : (QsShell H).card = (QsH H).card := by
  unfold QsShell QsH
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1; ext b; simp [and_comm]

theorem rankQs_injective : Function.Injective (fun r : {r : ℚ // r ≠ 0} => rankQs r.1) := by
  intro a b h
  simp only [rankQs_eq] at h
  exact shellRank_injective QsShell (fun r => ht r.1) (fun r => ratKey r.1)
    (fun _ _ => mem_QsShell) (fun x y hxy => Subtype.ext (ratKey_injective hxy)) h

theorem rankQs_surjective : Function.Surjective (fun r : {r : ℚ // r ≠ 0} => rankQs r.1) := by
  intro n
  obtain ⟨a, ha⟩ := shellRank_surjective QsShell (fun r => ht r.1) (fun r => ratKey r.1)
    (fun _ _ => mem_QsShell) (fun x y hxy => Subtype.ext (ratKey_injective hxy))
    (fun n => by
      obtain ⟨H, hH⟩ := QH_unbounded (n + 1)
      refine ⟨H, ?_⟩
      rw [QsShell_card, QsH]
      have := pred_card_le_card_erase (s := QH H) (a := 0)
      omega) n
  exact ⟨a, by simp only [rankQs_eq]; exact ha⟩

instance : Nonempty {r : ℚ // r ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩

/-- The enumeration `Q* : ℕ → ℚ*`. -/
noncomputable def Qsenum : ℕ → {r : ℚ // r ≠ 0} := Function.invFun (fun r : {r : ℚ // r ≠ 0} => rankQs r.1)

theorem Qsenum_bijective : Function.Bijective Qsenum := by
  refine ⟨?_, ?_⟩
  · exact (Function.rightInverse_invFun rankQs_surjective).injective
  · exact (Function.leftInverse_invFun rankQs_injective).surjective

lemma rankQs_lt {r : ℚ} (hr : r ≠ 0) {H : ℕ} (h : ht r ≤ H) : rankQs r < (QsH H).card := by
  have := shellRank_lt QsShell (fun r => ht r.1) (fun r => ratKey r.1)
    (fun _ _ => mem_QsShell) (a := ⟨r, hr⟩) h
  rw [← rankQs_eq, QsShell_card] at this
  exact this

lemma rankQs_image (H : ℕ) :
    (QsShell H).image (fun r => rankQs r.1) = range (QsH H).card := by
  have := shellRank_image QsShell (fun r => ht r.1) (fun r => ratKey r.1)
    (fun _ _ => mem_QsShell) (fun x y hxy => Subtype.ext (ratKey_injective hxy)) H
  rw [QsShell_card] at this
  rw [← this]
  congr 1
  funext r
  exact rankQs_eq r

/-- **Lemma 2.1 (d)**: ranks of elements of `𝒬_H` in `Q` and in `Q*` are `< 3H^2`. -/
theorem rank_lt_three_sq {r : ℚ} {H : ℕ} (h : ht r ≤ H) :
    rankQ r < 3 * H ^ 2 ∧ (r ≠ 0 → rankQs r < 3 * H ^ 2) := by
  refine ⟨lt_of_lt_of_le (rankQ_lt h) (card_QH_le H), fun hr => ?_⟩
  refine lt_of_lt_of_le (rankQs_lt hr h) (le_trans ?_ (card_QH_le H))
  exact card_erase_le

end Artigo
