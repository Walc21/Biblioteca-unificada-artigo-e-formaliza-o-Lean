module
public import Mathlib

/-!
# Section 2: rationals by height, the enumerations `Q`, `Q*`, and the Stern sequence
-/

@[expose] public section

namespace Fase3

open Finset

/-! ## Height and counting (Lemma 2.3) -/

/-- The elementary multiplicative height `ht(p/q) = max(|p|, q)` of a reduced fraction
(equation (04)). -/
def ht (r : ℚ) : ℕ := max r.num.natAbs r.den

lemma one_le_ht (r : ℚ) : 1 ≤ ht r := le_max_of_le_right r.den_pos

/-- `Q_H = {r ∈ ℚ : ht r ≤ H}` as a finite set. -/
def QH (H : ℕ) : Finset ℚ :=
  ((Icc (-(H : ℤ)) H ×ˢ Ioc 0 H).image (fun p : ℤ × ℕ => (p.1 : ℚ) / p.2)).filter
    (fun r => ht r ≤ H)

lemma mem_QH {H : ℕ} {r : ℚ} : r ∈ QH H ↔ ht r ≤ H := by
  unfold QH
  simp only [mem_filter, mem_image, mem_product, mem_Icc, mem_Ioc, Prod.exists]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨r.num, r.den, ⟨⟨?_, ?_⟩, r.den_pos, ?_⟩, Rat.num_div_den r⟩, h⟩
    · have : r.num.natAbs ≤ H := le_trans (le_max_left _ _) h
      omega
    · have : r.num.natAbs ≤ H := le_trans (le_max_left _ _) h
      omega
    · exact le_trans (le_max_right _ _) h

lemma QH_mono {H H' : ℕ} (h : H ≤ H') : QH H ⊆ QH H' := fun _ hr =>
  mem_QH.2 (le_trans (mem_QH.1 hr) h)

/-- **Lemma 2.3, upper bound.** `|Q_H| ≤ 3 H²` for every `H ≥ 1`. -/
theorem card_QH_le (H : ℕ) (hH : 1 ≤ H) : (QH H).card ≤ 3 * H ^ 2 := by
  unfold QH
  refine le_trans (card_filter_le _ _) (le_trans card_image_le ?_)
  rw [card_product, Int.card_Icc, Nat.card_Ioc]
  have : (H : ℤ) + 1 - -(H : ℤ) = ((2 * H + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast, Nat.sub_zero]
  nlinarith

lemma sum_inv_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Ico 2 (N + 1), (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 / 3 - 2 / (2 * N + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; norm_num
    · rw [Finset.sum_Ico_succ_top (by omega)]
      have := ih hpos
      have hN : (1 : ℝ) ≤ N := by exact_mod_cast hpos
      have key : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 2 / (2 * N + 1) - 2 / (2 * ((N + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at this key ⊢
      linarith

/-- The number of coprime pairs in `[1,H]²` is at least `H²/3`. -/
lemma card_coprime_pairs_ge (H : ℕ) :
    (H : ℝ) ^ 2 / 3 ≤ (((Ioc 0 H) ×ˢ (Ioc 0 H)).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card := by
  rcases Nat.eq_zero_or_pos H with h0 | hH
  · subst h0; simp
  set S := (Ioc 0 H) ×ˢ (Ioc 0 H)
  have hsplit := card_filter_add_card_filter_not (s := S) (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)
  have hS : S.card = H ^ 2 := by simp [S, sq]
  have hnot : (S.filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2)) ⊆
      (Ico 2 (H + 1)).biUnion (fun d => ((Ioc 0 H).filter (d ∣ ·)) ×ˢ ((Ioc 0 H).filter (d ∣ ·))) := by
    intro p hp
    simp only [S, mem_filter, mem_product, mem_Ioc] at hp
    obtain ⟨⟨⟨hp1, hp1'⟩, hp2, hp2'⟩, hnc⟩ := hp
    simp only [mem_biUnion, mem_Ico, mem_product, mem_filter, mem_Ioc]
    refine ⟨Nat.gcd p.1 p.2, ⟨?_, ?_⟩, ⟨⟨hp1, hp1'⟩, Nat.gcd_dvd_left _ _⟩, ⟨hp2, hp2'⟩, Nat.gcd_dvd_right _ _⟩
    · have : Nat.gcd p.1 p.2 ≠ 1 := hnc
      have : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ hp1
      omega
    · have := Nat.gcd_le_left p.2 hp1; omega
  have hcard := le_trans (card_le_card hnot) card_biUnion_le
  simp only [card_product, Nat.Ioc_filter_dvd_card_eq_div] at hcard
  have hcardR : ((S.filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2)).card : ℝ) ≤
      ∑ d ∈ Ico 2 (H + 1), ((H / d : ℕ) : ℝ) * ((H / d : ℕ) : ℝ) := by exact_mod_cast hcard
  have hterm : ∀ d ∈ Ico 2 (H + 1), ((H / d : ℕ) : ℝ) * ((H / d : ℕ) : ℝ) ≤ (H : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by
      have : 2 ≤ d := (mem_Ico.1 hd).1
      exact_mod_cast (by omega : 0 < d)
    have h1 : ((H / d : ℕ) : ℝ) ≤ (H : ℝ) / d := Nat.cast_div_le
    have h0 : (0 : ℝ) ≤ ((H / d : ℕ) : ℝ) := by positivity
    calc ((H / d : ℕ) : ℝ) * ((H / d : ℕ) : ℝ) ≤ ((H : ℝ) / d) * ((H : ℝ) / d) :=
          mul_le_mul h1 h1 h0 (by positivity)
      _ = _ := by field_simp
  have hsum := sum_le_sum hterm
  rw [← mul_sum] at hsum
  have hinv := sum_inv_sq_le H hH
  have hHpos : (0 : ℝ) ≤ (H : ℝ) ^ 2 := by positivity
  have h23 : (H : ℝ) ^ 2 * ∑ d ∈ Ico 2 (H + 1), (1 : ℝ) / (d : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 * (2 / 3) := by
    apply mul_le_mul_of_nonneg_left _ hHpos
    have : (0 : ℝ) ≤ 2 / (2 * H + 1) := by positivity
    linarith
  have hsplitR : ((S.filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card : ℝ) +
      ((S.filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2)).card : ℝ) = (H : ℝ) ^ 2 := by
    have := hsplit.trans hS
    exact_mod_cast this
  linarith

/-- **Lemma 2.3, lower bound** with `c₁ = 1/4` (valid for every `H`, so `H₀ = 0`).
The proof is elementary (counting coprime pairs) instead of using Mertens' asymptotic. -/
theorem card_QH_ge (H : ℕ) : (H : ℝ) ^ 2 / 4 ≤ (QH H).card := by
  have hinj : (((Ioc 0 H) ×ˢ (Ioc 0 H)).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card ≤
      (QH H).card := by
    apply card_le_card_of_injOn (fun p => (p.1 : ℚ) / p.2)
    · intro p hp
      simp only [coe_filter, mem_product, mem_Ioc, Set.mem_setOf_eq] at hp
      obtain ⟨⟨⟨hp1, hp1'⟩, hp2, hp2'⟩, hc⟩ := hp
      rw [mem_coe, mem_QH]
      have hnum : ((p.1 : ℚ) / p.2).num = p.1 := by
        have := Rat.num_div_eq_of_coprime (a := (p.1 : ℤ)) (b := (p.2 : ℤ)) (by omega)
          (by simpa [Int.natAbs_natCast] using hc)
        simpa using this
      have hden : ((p.1 : ℚ) / p.2).den = p.2 := by
        have := Rat.den_div_eq_of_coprime (a := (p.1 : ℤ)) (b := (p.2 : ℤ)) (by omega)
          (by simpa [Int.natAbs_natCast] using hc)
        push_cast at this
        exact_mod_cast this
      unfold ht; rw [hnum, hden]; simp; omega
    · intro p hp q hq hpq
      simp only [coe_filter, mem_product, mem_Ioc, Set.mem_setOf_eq] at hp hq
      obtain ⟨⟨⟨hp1, -⟩, hp2, -⟩, hpc⟩ := hp
      obtain ⟨⟨⟨hq1, -⟩, hq2, -⟩, hqc⟩ := hq
      have e1 := Rat.num_div_eq_of_coprime (a := (p.1 : ℤ)) (b := (p.2 : ℤ)) (by omega)
          (by simpa [Int.natAbs_natCast] using hpc)
      have e2 := Rat.num_div_eq_of_coprime (a := (q.1 : ℤ)) (b := (q.2 : ℤ)) (by omega)
          (by simpa [Int.natAbs_natCast] using hqc)
      have f1 := Rat.den_div_eq_of_coprime (a := (p.1 : ℤ)) (b := (p.2 : ℤ)) (by omega)
          (by simpa [Int.natAbs_natCast] using hpc)
      have f2 := Rat.den_div_eq_of_coprime (a := (q.1 : ℤ)) (b := (q.2 : ℤ)) (by omega)
          (by simpa [Int.natAbs_natCast] using hqc)
      simp only [Int.cast_natCast] at e1 e2 f1 f2
      have hpq' : ((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ) = ((q.1 : ℤ) : ℚ) / ((q.2 : ℤ) : ℚ) := by
        simpa using hpq
      have a1 : (p.1 : ℤ) = q.1 := by rw [← e1, ← e2]; simp only [Int.cast_natCast] at hpq' ⊢; rw [hpq']
      have a2 : (p.2 : ℤ) = q.2 := by rw [← f1, ← f2]; simp only [Int.cast_natCast] at hpq' ⊢; rw [hpq']
      exact Prod.ext (by exact_mod_cast a1) (by exact_mod_cast a2)
  have := card_coprime_pairs_ge H
  have h2 : ((((Ioc 0 H) ×ˢ (Ioc 0 H)).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card : ℝ) ≤
      (QH H).card := by exact_mod_cast hinj
  have : (H : ℝ) ^ 2 / 4 ≤ (H : ℝ) ^ 2 / 3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
  linarith

/-- **Lemma 2.3, lower bound**, in the existential form of equation (07). -/
theorem exists_card_QH_ge : ∃ H₀ : ℕ, ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ H ≥ H₀, c₁ * (H : ℝ) ^ 2 ≤ (QH H).card :=
  ⟨0, 1 / 4, by norm_num, fun H _ => by have := card_QH_ge H; linarith⟩

/-! ## Rank of an element in a well-order of type `ω` -/

theorem rank_bijective {α β : Type*} [LinearOrder β] [Infinite α] (key : α → β)
    (hkey : Function.Injective key) (pred : α → Finset α)
    (hpred : ∀ a b, b ∈ pred a ↔ key b < key a) :
    Function.Bijective (fun a => (pred a).card) := by
  have hmono : ∀ a b, key a < key b → (pred a).card < (pred b).card := by
    intro a b hab
    apply card_lt_card
    refine ⟨fun x hx => (hpred b x).2 (lt_trans ((hpred a x).1 hx) hab), fun h => ?_⟩
    have := (hpred a a).1 (h ((hpred b a).2 hab))
    exact lt_irrefl _ this
  have hinj : Function.Injective (fun a => (pred a).card) := by
    intro a b hab
    simp only at hab
    rcases lt_trichotomy (key a) (key b) with h | h | h
    · exact absurd hab (hmono a b h).ne
    · exact hkey h
    · exact absurd hab (hmono b a h).ne'
  refine ⟨hinj, fun n => ?_⟩
  have hinf : (Set.range (fun a => (pred a).card)).Infinite := Set.infinite_range_of_injective hinj
  obtain ⟨m, ⟨a, rfl⟩, hm⟩ := hinf.exists_gt n
  have himg : (pred a).image (fun b => (pred b).card) = range (pred a).card := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hx
      exact mem_range.2 (hmono b a ((hpred a b).1 hb))
    · rw [card_range, card_image_of_injective _ hinj]
  have : n ∈ (pred a).image (fun b => (pred b).card) := by rw [himg]; exact mem_range.2 hm
  obtain ⟨b, -, hb⟩ := mem_image.1 this
  exact ⟨b, hb⟩

/-! ## The height enumerations `Q` and `Q*` (equation (05), Lemma 2.4) -/

/-- The ordering key: first height, then denominator, then numerator. -/
def htKey (r : ℚ) : ℕ ×ₗ (ℕ ×ₗ ℤ) := toLex (ht r, toLex (r.den, r.num))

lemma htKey_injective : Function.Injective htKey := by
  intro r s h
  simp only [htKey, toLex_inj, Prod.mk.injEq] at h
  exact Rat.ext h.2.2 h.2.1

lemma ht_le_of_htKey_lt {r s : ℚ} (h : htKey s < htKey r) : ht s ≤ ht r := by
  simp only [htKey, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩ <;> omega

/-- The predecessors of `r` in the height order. -/
def predQ (r : ℚ) : Finset ℚ := (QH (ht r)).filter (fun s => htKey s < htKey r)

lemma mem_predQ (r s : ℚ) : s ∈ predQ r ↔ htKey s < htKey r := by
  unfold predQ
  rw [mem_filter, mem_QH]
  exact ⟨fun h => h.2, fun h => ⟨ht_le_of_htKey_lt h, h⟩⟩

/-- The position (rank) of `r` in the height enumeration. -/
def rankQ (r : ℚ) : ℕ := (predQ r).card

theorem rankQ_bijective : Function.Bijective rankQ :=
  rank_bijective htKey htKey_injective predQ mem_predQ

/-- The enumeration `Q : ℕ → ℚ` by height, then denominator, then numerator. -/
noncomputable def Qenum : ℕ → ℚ := (Equiv.ofBijective rankQ rankQ_bijective).symm

/-- Predecessors of a nonzero rational in the height order restricted to `ℚ*`. -/
def predQstar (r : {r : ℚ // r ≠ 0}) : Finset {r : ℚ // r ≠ 0} :=
  (predQ r.1).subtype (fun s => s ≠ 0)

lemma mem_predQstar (r s : {r : ℚ // r ≠ 0}) : s ∈ predQstar r ↔ htKey s.1 < htKey r.1 := by
  unfold predQstar
  rw [mem_subtype, mem_predQ]

instance : Infinite {r : ℚ // r ≠ 0} := by
  refine Infinite.of_injective (fun n : ℕ => (⟨(n : ℚ) + 1, by positivity⟩ : {r : ℚ // r ≠ 0})) ?_
  intro a b h
  simp only [Subtype.mk.injEq, add_left_inj, Nat.cast_inj] at h
  exact h

/-- The position of a nonzero rational in the enumeration `Q*`. -/
def rankQstar (r : {r : ℚ // r ≠ 0}) : ℕ := (predQstar r).card

theorem rankQstar_bijective : Function.Bijective rankQstar :=
  rank_bijective (fun r => htKey r.1) (fun _ _ h => Subtype.ext (htKey_injective h))
    predQstar mem_predQstar

/-- The enumeration `Q* : ℕ → ℚ*` (the same order, omitting `0/1`). -/
noncomputable def QstarEnum : ℕ → {r : ℚ // r ≠ 0} :=
  (Equiv.ofBijective rankQstar rankQstar_bijective).symm

/-- **Lemma 2.4 (bijectivity).** `Q` and `Q*` are bijections. -/
theorem Qenum_bijective : Function.Bijective Qenum :=
  (Equiv.ofBijective rankQ rankQ_bijective).symm.bijective

theorem QstarEnum_bijective : Function.Bijective QstarEnum :=
  (Equiv.ofBijective rankQstar rankQstar_bijective).symm.bijective

lemma Qenum_rankQ (r : ℚ) : Qenum (rankQ r) = r :=
  (Equiv.ofBijective rankQ rankQ_bijective).symm_apply_apply r

lemma QstarEnum_rankQstar (r : {r : ℚ // r ≠ 0}) : QstarEnum (rankQstar r) = r :=
  (Equiv.ofBijective rankQstar rankQstar_bijective).symm_apply_apply r

/-- **Lemma 2.4 (rank by height), for `Q`.** If `ht(r) ≤ H` then the position of `r`
in `Q` is `< 3H²`. -/
theorem rankQ_lt (r : ℚ) (H : ℕ) (hH : ht r ≤ H) : rankQ r < 3 * H ^ 2 := by
  have h1 : predQ r ⊆ (QH H).erase r := by
    intro s hs
    rw [mem_predQ] at hs
    refine mem_erase.2 ⟨fun h => ?_, mem_QH.2 (le_trans (ht_le_of_htKey_lt hs) hH)⟩
    subst h; exact lt_irrefl _ hs
  have h2 := card_le_card h1
  have hr : r ∈ QH H := mem_QH.2 hH
  rw [card_erase_of_mem hr] at h2
  have h3 := card_QH_le H (le_trans (one_le_ht r) hH)
  have : 0 < (QH H).card := card_pos.2 ⟨r, hr⟩
  unfold rankQ; omega

/-- **Lemma 2.4 (rank by height), for `Q*`.** -/
theorem rankQstar_lt (r : {r : ℚ // r ≠ 0}) (H : ℕ) (hH : ht r.1 ≤ H) :
    rankQstar r < 3 * H ^ 2 := by
  have : rankQstar r ≤ rankQ r.1 := by
    unfold rankQstar rankQ predQstar
    rw [card_subtype]; exact card_filter_le _ _
  exact lt_of_le_of_lt this (rankQ_lt r.1 H hH)

/-! ## Stern's diatomic sequence and Calkin–Wilf (Lemma 2.5) -/

/-- Stern's diatomic sequence (equation (08)). -/
def stern : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then stern ((n + 2) / 2) else stern ((n + 1) / 2) + stern ((n + 3) / 2)

lemma stern_zero : stern 0 = 0 := by simp [stern]

lemma stern_one : stern 1 = 1 := by simp [stern]

lemma stern_even (n : ℕ) : stern (2 * n) = stern n := by
  rcases n with _ | n
  · simp [stern]
  · have : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [this, stern]
    simp only [show (2 * n + 2) % 2 = 0 by omega, if_true]
    congr 1; omega

lemma stern_odd (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
  rcases n with _ | n
  · simp [stern]
  · have : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
    rw [this, stern]
    simp only [show (2 * n + 1 + 2) % 2 = 1 by omega]
    simp only [one_ne_zero, if_false]
    congr 2 <;> omega

/-- The Calkin–Wilf enumeration `CW(n) = S_n / S_{n+1}`. -/
def calkinWilf (n : ℕ) : ℚ := (stern n : ℚ) / stern (n + 1)

lemma stern_two_pow (m : ℕ) : stern (2 ^ m) = 1 := by
  induction m with
  | zero => simp [stern_one]
  | succ m ih => rw [pow_succ, mul_comm, stern_even, ih]

lemma stern_two_pow_add_one (m : ℕ) : stern (2 ^ m + 1) = m + 1 := by
  induction m with
  | zero => rw [show 2 ^ 0 + 1 = 2 * 1 by rfl, stern_even, stern_one]
  | succ m ih => rw [pow_succ, mul_comm, stern_odd, stern_two_pow, ih]; ring

/-- **Lemma 2.5.** For every `q ≥ 1`, `CW(2^{q-1}) = 1/q`. -/
theorem calkinWilf_two_pow (q : ℕ) (hq : 1 ≤ q) : calkinWilf (2 ^ (q - 1)) = 1 / q := by
  unfold calkinWilf
  rw [stern_two_pow, stern_two_pow_add_one]
  congr 1
  push_cast [Nat.cast_sub hq]
  ring

end Fase3
