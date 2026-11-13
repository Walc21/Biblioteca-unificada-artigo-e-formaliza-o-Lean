module

public import Mathlib

/-!
# Section 2 — Ferramentas de indexação

Formalization of Section 2 of `artigo_fase1_autocontido.tex`:

* the Cantor pairing `cantorPair` (eq. (01)), its inverse (eq. (02)) and Lemma 2.1;
* the bijection `Zenum : ℕ → ℤ` (eq. (03)) and Lemma 2.2;
* the height `ht` (eq. (04)), the height enumerations `Q : ℕ → ℚ`, `Qstar : ℕ → ℚ*`
  (eq. (05)), Lemma 2.3 (counting by height) and Lemma 2.4 (rank by height);
* Stern's diatomic sequence (eq. (08)), the Calkin–Wilf map and Lemma 2.5.

Here `ℕ` plays the role of `ℕ₀ = {0,1,2,…}`.
-/

@[expose] public section

open Finset

namespace Fase1

/-! ## Triangular numbers and the Cantor pairing -/

/-- Triangular numbers `T_m = m(m+1)/2`. -/
def tri (m : ℕ) : ℕ := m * (m + 1) / 2

/-- The Cantor pairing `π(u,v) = T_{u+v} + v` (eq. (01)). -/
def cantorPair (p : ℕ × ℕ) : ℕ := tri (p.1 + p.2) + p.2

/-- The diagonal index `w = ⌊(√(8n+1) - 1)/2⌋` of eq. (02). -/
noncomputable def cantorDiag (n : ℕ) : ℕ := ⌊(Real.sqrt (8 * n + 1) - 1) / 2⌋₊

/-- The explicit inverse of the Cantor pairing (eq. (02)):
`w = ⌊(√(8n+1)-1)/2⌋`, `v = n - T_w`, `u = w - v`. -/
noncomputable def cantorUnpair (n : ℕ) : ℕ × ℕ :=
  (cantorDiag n - (n - tri (cantorDiag n)), n - tri (cantorDiag n))

lemma two_mul_tri (m : ℕ) : 2 * tri m = m * (m + 1) := by
  unfold tri
  have : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  omega

lemma tri_succ (m : ℕ) : tri (m + 1) = tri m + (m + 1) := by
  have h1 := two_mul_tri m
  have h2 := two_mul_tri (m + 1)
  nlinarith

/-- `w = ⌊(√(8n+1)-1)/2⌋` is the unique integer with `T_w ≤ n < T_{w+1}`. -/
lemma cantorDiag_spec (n : ℕ) : tri (cantorDiag n) ≤ n ∧ n < tri (cantorDiag n + 1) := by
  have hs0 : (1:ℝ) ≤ Real.sqrt (8 * n + 1) := by
    rw [Real.one_le_sqrt]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hy : (0:ℝ) ≤ (Real.sqrt (8 * n + 1) - 1) / 2 := by linarith
  have h1 : (cantorDiag n : ℝ) ≤ _ := Nat.floor_le hy
  have h2 : _ < (cantorDiag n : ℝ) + 1 := Nat.lt_floor_add_one ((Real.sqrt (8 * n + 1) - 1) / 2)
  set w := cantorDiag n with hw
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 8 * n + 1 by positivity)
  have a1 : (2 * (w:ℝ) + 1) ≤ Real.sqrt (8 * n + 1) := by linarith
  have a2 : Real.sqrt (8 * n + 1) < 2 * (w:ℝ) + 3 := by linarith
  have b1 : (2 * (w:ℝ) + 1)^2 ≤ 8 * n + 1 := by
    rw [← hsq]; exact pow_le_pow_left₀ (by positivity) a1 2
  have b2 : (8 * n + 1 : ℝ) < (2 * (w:ℝ) + 3)^2 := by
    rw [← hsq]; exact pow_lt_pow_left₀ a2 (by positivity) (by norm_num)
  have c1 : (2 * w + 1)^2 ≤ 8 * n + 1 := by exact_mod_cast b1
  have c2 : 8 * n + 1 < (2 * w + 3)^2 := by exact_mod_cast b2
  have t1 := two_mul_tri w
  have t2 := two_mul_tri (w + 1)
  constructor <;> nlinarith

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

/-- The diagonal block `[T_w, T_{w+1})` containing `n` is unique. -/
lemma tri_block_unique {a b n : ℕ} (ha : tri a ≤ n ∧ n < tri (a + 1))
    (hb : tri b ≤ n ∧ n < tri (b + 1)) : a = b := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := tri_mono (show a + 1 ≤ b by omega); omega
  · have := tri_mono (show b + 1 ≤ a by omega); omega

/-- **Lemma 2.1**, part 2: the formula (02) is a right inverse of `π`. -/
theorem cantorPair_cantorUnpair (n : ℕ) : cantorPair (cantorUnpair n) = n := by
  have h := cantorDiag_spec n
  have := tri_succ (cantorDiag n)
  unfold cantorPair cantorUnpair
  simp only
  rw [show cantorDiag n - (n - tri (cantorDiag n)) + (n - tri (cantorDiag n)) = cantorDiag n
    by omega]
  omega

/-- **Lemma 2.1**, part 2': the formula (02) is a left inverse of `π`. -/
theorem cantorUnpair_cantorPair (p : ℕ × ℕ) : cantorUnpair (cantorPair p) = p := by
  obtain ⟨u, v⟩ := p
  have hb : tri (u + v) ≤ cantorPair (u, v) ∧ cantorPair (u, v) < tri (u + v + 1) := by
    have := tri_succ (u + v); unfold cantorPair; simp only; omega
  have hw := tri_block_unique (cantorDiag_spec (cantorPair (u, v))) hb
  unfold cantorUnpair
  rw [hw]
  unfold cantorPair
  simp only [Prod.mk.injEq]
  omega

/-- **Lemma 2.1 (pareamento e cota)**, part 1: `π : ℕ₀² → ℕ₀` is bijective. -/
theorem cantorPair_bijective : Function.Bijective cantorPair :=
  Function.bijective_iff_has_inverse.2
    ⟨cantorUnpair, cantorUnpair_cantorPair, cantorPair_cantorUnpair⟩

/-- **Lemma 2.1**, part 3: `π(u,v) ≤ (u+v+1)²`. -/
theorem cantorPair_le (u v : ℕ) : cantorPair (u, v) ≤ (u + v + 1) ^ 2 := by
  have := two_mul_tri (u + v)
  unfold cantorPair
  simp only
  nlinarith

/-! ## Integers enumerated by `ℕ₀` -/

/-- The map `Z : ℕ₀ → ℤ` of eq. (03): `Z(t) = t/2` for even `t`, `-(t+1)/2` for odd `t`. -/
def Zenum (t : ℕ) : ℤ := if t % 2 = 0 then (t / 2 : ℕ) else -(((t + 1) / 2 : ℕ) : ℤ)

/-- The inverse `Z⁻¹(m) = 2m` (`m ≥ 0`), `Z⁻¹(m) = -2m-1` (`m < 0`). -/
def ZenumInv (m : ℤ) : ℕ := if 0 ≤ m then 2 * m.toNat else (-2 * m - 1).toNat

/-- `Z⁻¹` is a right inverse of `Z`. -/
theorem Zenum_ZenumInv (m : ℤ) : Zenum (ZenumInv m) = m := by
  unfold Zenum ZenumInv
  split_ifs <;> omega

theorem ZenumInv_Zenum (t : ℕ) : ZenumInv (Zenum t) = t := by
  unfold Zenum ZenumInv
  split_ifs <;> omega

/-- **Lemma 2.2**: `Z` is bijective. -/
theorem Zenum_bijective : Function.Bijective Zenum :=
  Function.bijective_iff_has_inverse.2 ⟨ZenumInv, ZenumInv_Zenum, Zenum_ZenumInv⟩

/-- **Lemma 2.2**: the inverse formula for `m ≥ 0`. -/
theorem ZenumInv_of_nonneg {m : ℤ} (hm : 0 ≤ m) : (ZenumInv m : ℤ) = 2 * m := by
  unfold ZenumInv; split_ifs; omega

/-- **Lemma 2.2**: the inverse formula for `m < 0`. -/
theorem ZenumInv_of_neg {m : ℤ} (hm : m < 0) : (ZenumInv m : ℤ) = -2 * m - 1 := by
  unfold ZenumInv; split_ifs <;> omega

/-- **Lemma 2.2**: `Z⁻¹(m) ≤ 2|m| + 1`. -/
theorem ZenumInv_le (m : ℤ) : (ZenumInv m : ℤ) ≤ 2 * |m| + 1 := by
  unfold ZenumInv; split_ifs <;> cases abs_cases m <;> omega

/-! ## Rationals ordered by height -/

/-- The elementary multiplicative height `ht(p/q) = max{|p|, q}` of eq. (04), computed on the
reduced representation (`Rat.num`, `Rat.den`). -/
def ht (r : ℚ) : ℕ := max r.num.natAbs r.den

/-- `ℚ_H = {r ∈ ℚ : ht(r) ≤ H}`. -/
def QH (H : ℕ) : Set ℚ := {r | ht r ≤ H}

/-- The sort key: first by height, then by `q`, finally by `p`. -/
def htKey (r : ℚ) : ℕ ×ₗ ℕ ×ₗ ℤ := toLex (ht r, toLex (r.den, r.num))

/-! ### Generic rank of an element w.r.t. a key with finitely many predecessors -/

section KeyRank

variable {α β : Type*} [LinearOrder β] (key : α → β)

/-- The rank (= number of predecessors) of `a` in the order induced by `key`. -/
noncomputable def keyRank (a : α) : ℕ := {b | key b < key a}.ncard

variable {key}

lemma keyRank_lt_of_lt (hfin : ∀ a, {b | key b < key a}.Finite) {a b : α}
    (h : key a < key b) : keyRank key a < keyRank key b := by
  unfold keyRank
  apply Set.ncard_lt_ncard _ (hfin b)
  refine ⟨fun c hc => lt_trans hc h, fun hsub => ?_⟩
  have : a ∈ {c | key c < key a} := hsub h
  exact lt_irrefl _ this

lemma keyRank_bijective [Infinite α] (hinj : Function.Injective key)
    (hfin : ∀ a, {b | key b < key a}.Finite) : Function.Bijective (keyRank key) := by
  have hinjR : Function.Injective (keyRank key) := by
    intro a b hab
    rcases lt_trichotomy (key a) (key b) with h | h | h
    · exact absurd hab (keyRank_lt_of_lt hfin h).ne
    · exact hinj h
    · exact absurd hab (keyRank_lt_of_lt hfin h).ne'
  refine ⟨hinjR, fun n => ?_⟩
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := (Set.infinite_range_of_injective hinjR).exists_gt n
  have hcard : (hfin s).toFinset.card = keyRank key s := by
    unfold keyRank; rw [Set.ncard_eq_toFinset_card _ (hfin s)]
  obtain ⟨b, hb, hbn⟩ := Finset.surj_on_of_inj_on_of_card_le (s := (hfin s).toFinset)
    (t := Finset.range (keyRank key s)) (fun b _ => keyRank key b)
    (fun b hb => by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hb
      exact Finset.mem_range.2 (keyRank_lt_of_lt hfin hb))
    (fun _ _ _ _ h => hinjR h) (by simp [hcard]) n (Finset.mem_range.2 hs)
  exact ⟨b, hbn.symm⟩

lemma keyRank_lt_iff (hinj : Function.Injective key)
    (hfin : ∀ a, {b | key b < key a}.Finite) {a b : α} :
    keyRank key a < keyRank key b ↔ key a < key b := by
  refine ⟨fun h => ?_, keyRank_lt_of_lt hfin⟩
  rcases lt_trichotomy (key a) (key b) with h' | h' | h'
  · exact h'
  · exact absurd (hinj h' ▸ h) (lt_irrefl _)
  · exact absurd (keyRank_lt_of_lt hfin h') (not_lt.2 h.le)

end KeyRank

lemma htKey_injective : Function.Injective htKey := by
  intro r s h
  simp only [htKey, toLex_inj, Prod.mk.injEq] at h
  exact Rat.ext h.2.2 h.2.1

lemma one_le_ht (r : ℚ) : 1 ≤ ht r := le_max_of_le_right r.den_pos

lemma mem_QH_iff (H : ℕ) (r : ℚ) : r ∈ QH H ↔ r.num.natAbs ≤ H ∧ r.den ≤ H := by
  simp [QH, ht]

/-- The reduced representation `r ↦ (p, q)` maps `ℚ_H` injectively into
`[-H, H] × [1, H]`. -/
lemma QH_subset_preimage (H : ℕ) :
    QH H ⊆ (fun r : ℚ => (r.num, r.den)) ⁻¹'
      ((Finset.Icc (-(H : ℤ)) H ×ˢ Finset.Icc 1 H : Finset (ℤ × ℕ)) : Set (ℤ × ℕ)) := by
  intro r hr
  rw [mem_QH_iff] at hr
  have := r.den_pos
  simp only [Set.mem_preimage, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
  omega

lemma numDen_injective : Function.Injective (fun r : ℚ => (r.num, r.den)) := by
  intro r s h
  simp only [Prod.mk.injEq] at h
  exact Rat.ext h.1 h.2

lemma QH_finite (H : ℕ) : (QH H).Finite :=
  ((Finset.finite_toSet _).preimage numDen_injective.injOn).subset (QH_subset_preimage H)

lemma htKey_preds_subset (r : ℚ) : {s | htKey s < htKey r} ⊆ QH (ht r) := by
  intro s hs
  simp only [Set.mem_setOf_eq, htKey, Prod.Lex.toLex_lt_toLex] at hs
  show ht s ≤ ht r
  rcases hs with h | ⟨h, _⟩ <;> omega

lemma htKey_preds_finite (r : ℚ) : {s | htKey s < htKey r}.Finite :=
  (QH_finite _).subset (htKey_preds_subset r)

/-- The rank of `r` in the enumeration by height. -/
noncomputable def htRank (r : ℚ) : ℕ := keyRank htKey r

/-- The nonzero rationals `ℚ*`. -/
abbrev QStar := {r : ℚ // r ≠ 0}

instance : Infinite QStar :=
  Set.infinite_coe_iff.2 (show ({0}ᶜ : Set ℚ).Infinite from (Set.finite_singleton 0).infinite_compl)

/-- The rank of `r ∈ ℚ*` in the enumeration by height omitting `0/1`. -/
noncomputable def htRankStar (r : QStar) : ℕ := keyRank (fun s : QStar => htKey s.1) r

theorem htRank_bijective : Function.Bijective htRank :=
  keyRank_bijective htKey_injective htKey_preds_finite

lemma htKeyStar_preds_finite (r : QStar) :
    {s : QStar | htKey s.1 < htKey r.1}.Finite :=
  (htKey_preds_finite r.1).preimage Subtype.val_injective.injOn

theorem htRankStar_bijective : Function.Bijective htRankStar :=
  keyRank_bijective (fun _ _ h => Subtype.ext (htKey_injective h)) htKeyStar_preds_finite

/-- The enumeration `Q : ℕ₀ → ℚ` of eq. (05): the inverse of the rank by height. -/
noncomputable def Q : ℕ → ℚ := (Equiv.ofBijective htRank htRank_bijective).symm

/-- The enumeration `Q* : ℕ₀ → ℚ*` of eq. (05) (omitting `0/1`). -/
noncomputable def Qstar : ℕ → QStar := (Equiv.ofBijective htRankStar htRankStar_bijective).symm

theorem htRank_Q (n : ℕ) : htRank (Q n) = n :=
  (Equiv.ofBijective htRank htRank_bijective).apply_symm_apply n

theorem Q_htRank (r : ℚ) : Q (htRank r) = r :=
  (Equiv.ofBijective htRank htRank_bijective).symm_apply_apply r

theorem htRankStar_Qstar (n : ℕ) : htRankStar (Qstar n) = n :=
  (Equiv.ofBijective htRankStar htRankStar_bijective).apply_symm_apply n

theorem Qstar_htRankStar (r : QStar) : Qstar (htRankStar r) = r :=
  (Equiv.ofBijective htRankStar htRankStar_bijective).symm_apply_apply r

/-- `Q` lists the rationals in the order "first by height, then by `q`, then by `p`". -/
theorem Q_lt_iff (n m : ℕ) : n < m ↔ htKey (Q n) < htKey (Q m) := by
  conv_lhs => rw [← htRank_Q n, ← htRank_Q m]
  exact keyRank_lt_iff htKey_injective htKey_preds_finite

/-- `Q*` lists the nonzero rationals in the order "first by height, then by `q`, then by `p`". -/
theorem Qstar_lt_iff (n m : ℕ) : n < m ↔ htKey (Qstar n).1 < htKey (Qstar m).1 := by
  conv_lhs => rw [← htRankStar_Qstar n, ← htRankStar_Qstar m]
  exact keyRank_lt_iff (fun _ _ h => Subtype.ext (htKey_injective h)) htKeyStar_preds_finite

/-- **Lemma 2.3 (contagem por altura)**, upper bound (06): `|ℚ_H| ≤ 3H²` for `H ≥ 1`. -/
theorem QH_ncard_le (H : ℕ) (hH : 1 ≤ H) : (QH H).ncard ≤ 3 * H ^ 2 := by
  have h := Set.ncard_le_ncard_of_injOn (fun r : ℚ => (r.num, r.den))
    (t := ((Finset.Icc (-(H : ℤ)) H ×ˢ Finset.Icc 1 H : Finset (ℤ × ℕ)) : Set (ℤ × ℕ)))
    (fun r hr => QH_subset_preimage H hr) numDen_injective.injOn (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_product, Int.card_Icc, Nat.card_Icc] at h
  have : (↑H + 1 - -(H : ℤ)).toNat = 2 * H + 1 := by omega
  rw [this, Nat.add_sub_cancel] at h
  nlinarith

lemma sum_inv_sq_le_aux (N : ℕ) (hN : 2 ≤ N) :
    ∑ d ∈ Icc 2 N, 1 / (d : ℝ) ^ 2 ≤ 3 / 4 - 1 / (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hN' : (2:ℝ) ≤ N := by exact_mod_cast hN
    have : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (N:ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le (N : ℕ) : ∑ d ∈ Icc 2 N, 1 / (d : ℝ) ^ 2 ≤ 3 / 4 := by
  rcases lt_or_ge N 2 with h | h
  · rw [Finset.Icc_eq_empty (by omega)]; norm_num
  · have := sum_inv_sq_le_aux N h
    have : (0:ℝ) ≤ 1 / (N:ℝ) := by positivity
    linarith

/-- At least a quarter of the pairs in `[1,H]²` are coprime (elementary sieve). -/
lemma coprime_pairs_card (H : ℕ) :
    (H : ℝ) ^ 2 / 4 ≤
      ((Ioc 0 H ×ˢ Ioc 0 H).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card := by
  set A := Ioc 0 H ×ˢ Ioc 0 H
  have htot := Finset.card_filter_add_card_filter_not (s := A)
    (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)
  have hA : A.card = H ^ 2 := by simp [A, sq]
  have hsub : A.filter (fun p => ¬ Nat.Coprime p.1 p.2) ⊆
      (Icc 2 H).biUnion (fun d => A.filter (fun p => d ∣ p.1 ∧ d ∣ p.2)) := by
    intro p hp
    simp only [A, mem_filter, mem_product, mem_Ioc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hnc⟩ := hp
    have hg1 : Nat.gcd p.1 p.2 ≠ 1 := hnc
    have hg0 : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ h1
    have hgle : Nat.gcd p.1 p.2 ≤ p.1 := Nat.gcd_le_left _ h1
    simp only [mem_biUnion, mem_Icc, A, mem_filter, mem_product, mem_Ioc]
    exact ⟨Nat.gcd p.1 p.2, ⟨by omega, by omega⟩, ⟨⟨⟨h1, h2⟩, h3, h4⟩,
      Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩⟩
  have hd : ∀ d, (A.filter (fun p => d ∣ p.1 ∧ d ∣ p.2)).card = (H / d) ^ 2 := by
    intro d
    rw [Finset.filter_product (fun a => d ∣ a) (fun a => d ∣ a), card_product,
      Nat.Ioc_filter_dvd_card_eq_div, sq]
  have hbound : ((A.filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ) ≤ 3 / 4 * H ^ 2 := by
    calc ((A.filter (fun p => ¬ Nat.Coprime p.1 p.2)).card : ℝ)
        ≤ (((Icc 2 H).biUnion (fun d => A.filter (fun p => d ∣ p.1 ∧ d ∣ p.2))).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ ∑ d ∈ Icc 2 H, ((A.filter (fun p => d ∣ p.1 ∧ d ∣ p.2)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ d ∈ Icc 2 H, (H : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by
          apply sum_le_sum
          intro d hd'
          rw [hd]
          have hd0 : (0:ℝ) < d := by
            have := (mem_Icc.1 hd').1; exact_mod_cast (show 0 < d by omega)
          push_cast
          have h1 : (((H / d : ℕ)) : ℝ) ≤ (H:ℝ) / d := Nat.cast_div_le
          calc (((H / d : ℕ)) : ℝ) ^ 2 ≤ ((H:ℝ) / d) ^ 2 :=
                pow_le_pow_left₀ (by positivity) h1 2
            _ = _ := by field_simp
      _ = (H : ℝ) ^ 2 * ∑ d ∈ Icc 2 H, 1 / (d : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ (H : ℝ) ^ 2 * (3 / 4) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sq_le H) (by positivity)
      _ = 3 / 4 * H ^ 2 := by ring
  have : ((A.filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card : ℝ)
      + (A.filter (fun p => ¬ Nat.Coprime p.1 p.2)).card = (H:ℝ) ^ 2 := by
    exact_mod_cast htot.trans hA
  linarith

lemma num_den_div_of_coprime {a : ℤ} {b : ℕ} (hb : 0 < b) (h : a.natAbs.Coprime b) :
    ((a : ℚ) / (b : ℚ)).num = a ∧ ((a : ℚ) / (b : ℚ)).den = b := by
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have h' : a.natAbs.Coprime (b : ℤ).natAbs := by simpa using h
  have h1 := Rat.num_div_eq_of_coprime hb' h'
  have h2 := Rat.den_div_eq_of_coprime hb' h'
  simp only [Int.cast_natCast] at h1 h2
  exact ⟨h1, by exact_mod_cast h2⟩

/-- `±p/q`, for coprime `p, q ∈ [1, H]`, are `2 |C|` distinct elements of `ℚ_H`. -/
lemma two_mul_coprime_pairs_le (H : ℕ) :
    2 * ((Ioc 0 H ×ˢ Ioc 0 H).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card
      ≤ (QH H).ncard := by
  set C := (Ioc 0 H ×ˢ Ioc 0 H).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)
  have hC : ∀ p ∈ C, 0 < p.1 ∧ p.1 ≤ H ∧ 0 < p.2 ∧ p.2 ≤ H ∧ Nat.Coprime p.1 p.2 := by
    intro p hp
    simp only [C, mem_filter, mem_product, mem_Ioc] at hp
    omega
  let g1 : ℕ × ℕ → ℚ := fun p => ((p.1 : ℤ) : ℚ) / (p.2 : ℚ)
  let g2 : ℕ × ℕ → ℚ := fun p => ((-(p.1 : ℤ) : ℤ) : ℚ) / (p.2 : ℚ)
  have e1 : ∀ p ∈ C, (g1 p).num = p.1 ∧ (g1 p).den = p.2 := fun p hp =>
    num_den_div_of_coprime (hC p hp).2.2.1 (by simpa using (hC p hp).2.2.2.2)
  have e2 : ∀ p ∈ C, (g2 p).num = -(p.1 : ℤ) ∧ (g2 p).den = p.2 := fun p hp =>
    num_den_div_of_coprime (hC p hp).2.2.1 (by simpa using (hC p hp).2.2.2.2)
  have i1 : Set.InjOn g1 C := by
    intro p hp q hq h
    have a := e1 p hp; have b := e1 q hq
    rw [h] at a
    exact Prod.ext (by omega) (by omega)
  have i2 : Set.InjOn g2 C := by
    intro p hp q hq h
    have a := e2 p hp; have b := e2 q hq
    rw [h] at a
    exact Prod.ext (by omega) (by omega)
  have hdisj : Disjoint (C.image g1) (C.image g2) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hx1
    obtain ⟨q, hq, hpq⟩ := mem_image.1 hx2
    have a := e1 p hp; have b := e2 q hq
    rw [hpq] at b
    have := (hC p hp).1; have := (hC q hq).1
    omega
  have hsub : ((C.image g1 ∪ C.image g2 : Finset ℚ) : Set ℚ) ⊆ QH H := by
    intro x hx
    rw [mem_QH_iff]
    simp only [coe_union, coe_image, Set.mem_union, Set.mem_image, mem_coe] at hx
    rcases hx with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [(e1 p hp).1, (e1 p hp).2]; have := hC p hp; omega
    · rw [(e2 p hp).1, (e2 p hp).2]; have := hC p hp; omega
  calc 2 * C.card = (C.image g1).card + (C.image g2).card := by
        rw [card_image_of_injOn i1, card_image_of_injOn i2]; ring
    _ = (C.image g1 ∪ C.image g2).card := (card_union_of_disjoint hdisj).symm
    _ ≤ (QH H).ncard := by
        rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub (QH_finite H)

/-- **Lemma 2.3**, lower bound (07) with the explicit constant `c₁ = 1/4`
(valid for every `H`). -/
theorem QH_ncard_ge (H : ℕ) : (H : ℝ) ^ 2 / 4 ≤ (QH H).ncard := by
  have h1 := coprime_pairs_card H
  have h2 : (2 * ((Ioc 0 H ×ˢ Ioc 0 H).filter
      (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card : ℝ) ≤ (QH H).ncard := by
    exact_mod_cast two_mul_coprime_pairs_le H
  have : (0:ℝ) ≤ (H : ℝ) ^ 2 / 4 := by positivity
  linarith

/-- **Lemma 2.3**, lower bound (07) in the existential form of the paper. -/
theorem QH_ncard_ge_exists :
    ∃ H₀ : ℕ, ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ H ≥ H₀, c₁ * (H : ℝ) ^ 2 ≤ (QH H).ncard :=
  ⟨0, 1 / 4, by norm_num, fun H _ => by have := QH_ncard_ge H; linarith⟩

/-- **Lemma 2.4 (posto por altura)**, for `Q`: the maps in (05) are bijective (see
`htRank_bijective`) and if `ht(r) ≤ H` the rank of `r` is `< 3H²`. -/
theorem htRank_lt {r : ℚ} {H : ℕ} (hr : ht r ≤ H) : htRank r < 3 * H ^ 2 := by
  have hH : 1 ≤ H := (one_le_ht r).trans hr
  have hsub : {s | htKey s < htKey r} ⊂ QH H := by
    refine ⟨fun s hs => le_trans (htKey_preds_subset r hs) hr, fun h => ?_⟩
    have : r ∈ {s | htKey s < htKey r} := h (show ht r ≤ H from hr)
    exact lt_irrefl (htKey r) this
  exact (Set.ncard_lt_ncard hsub (QH_finite H)).trans_le (QH_ncard_le H hH)

/-- **Lemma 2.4 (posto por altura)**, for `Q*`. -/
theorem htRankStar_lt {r : QStar} {H : ℕ} (hr : ht r.1 ≤ H) : htRankStar r < 3 * H ^ 2 := by
  refine lt_of_le_of_lt ?_ (htRank_lt hr)
  exact Set.ncard_le_ncard_of_injOn Subtype.val (fun s hs => hs)
    Subtype.val_injective.injOn (htKey_preds_finite r.1)

/-! ## Stern's diatomic sequence and Calkin–Wilf -/

/-- Stern's diatomic sequence (eq. (08)). -/
def stern : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    if (n + 2) % 2 = 0 then stern ((n + 2) / 2)
    else stern ((n + 2) / 2) + stern ((n + 2) / 2 + 1)
  decreasing_by all_goals omega

theorem stern_zero : stern 0 = 0 := by simp [stern]

theorem stern_one : stern 1 = 1 := by simp [stern]

theorem stern_even (n : ℕ) : stern (2 * n) = stern n := by
  rcases n with _ | n
  · rfl
  · rw [show 2 * (n + 1) = 2 * n + 2 by ring, stern]
    rw [if_pos (by omega)]
    congr 1; omega

theorem stern_odd (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
  rcases n with _ | n
  · simp [stern]
  · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, stern]
    rw [if_neg (by omega)]
    congr 2 <;> omega

/-- The Calkin–Wilf map `CW(n) = S_n / S_{n+1}`. -/
def CW (n : ℕ) : ℚ := (stern n : ℚ) / stern (n + 1)

/-- **Lemma 2.5**: `CW(2^{q-1}) = 1/q` for `q ≥ 1`. -/
lemma stern_two_pow (m : ℕ) : stern (2 ^ m) = 1 := by
  induction m with
  | zero => simp [stern]
  | succ m ih => rw [pow_succ, mul_comm, stern_even, ih]

lemma stern_two_pow_add_one (m : ℕ) : stern (2 ^ m + 1) = m + 1 := by
  induction m with
  | zero => simp [stern]
  | succ m ih =>
    rw [pow_succ, mul_comm, stern_odd, stern_two_pow, ih]; ring

theorem CW_two_pow (q : ℕ) (hq : 1 ≤ q) : CW (2 ^ (q - 1)) = 1 / q := by
  unfold CW
  rw [stern_two_pow, stern_two_pow_add_one]
  push_cast [Nat.cast_sub hq]
  ring_nf

/-- Remark after Lemma 2.5: the Calkin–Wilf index of `1/q` needs exactly `q` bits... -/
theorem size_CW_index (q : ℕ) (hq : 1 ≤ q) : Nat.size (2 ^ (q - 1)) = q := by
  rw [Nat.size_pow]; omega

/-- ... whereas its index in the height order needs only `O(log q)` bits. -/
theorem size_htRank_inv (q : ℕ) (hq : 1 ≤ q) :
    Nat.size (htRank (1 / q)) ≤ 2 * Nat.size q + 2 := by
  have h := num_den_div_of_coprime (a := 1) (b := q) hq (by simp)
  rw [Int.cast_one] at h
  have hht : ht (1 / (q : ℚ)) ≤ q := by
    unfold ht; rw [h.1, h.2]; simp; omega
  have h1 := htRank_lt hht
  have h2 := Nat.lt_size_self q
  rw [Nat.size_le]
  calc htRank (1 / q) < 3 * q ^ 2 := h1
    _ ≤ 4 * (2 ^ Nat.size q) ^ 2 := by
        have : q ^ 2 ≤ (2 ^ Nat.size q) ^ 2 := Nat.pow_le_pow_left h2.le 2
        omega
    _ = 2 ^ (2 * Nat.size q + 2) := by ring

end Fase1
