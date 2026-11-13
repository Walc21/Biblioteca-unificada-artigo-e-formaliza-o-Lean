module

public import Mathlib

/-!
# Section 2.2–2.3: rationals by height, and the Calkin–Wilf comparison

Formalization of Lemma 2.3 (counting by height), Lemma 2.4 (rank by height) and
Lemma 2.5 (`CW(2^{q-1}) = 1/q`).
-/

@[expose] public section

namespace Dyadic2

open Set Function

/-! ### A general ranking lemma -/

section Rank

variable {α β : Type*} [LinearOrder β] (key : α → β)

/-- The rank of `a` with respect to the order induced by `key`: the number of elements
strictly preceding it. -/
noncomputable def rankBy (a : α) : ℕ := {b | key b < key a}.ncard

variable {key}

lemma rankBy_lt_rankBy (hfin : ∀ a, {b | key b < key a}.Finite) {a b : α}
    (h : key a < key b) : rankBy key a < rankBy key b := by
  unfold rankBy
  apply Set.ncard_lt_ncard _ (hfin b)
  refine ⟨fun c hc => lt_trans (show key c < key a from hc) h, fun hsub => ?_⟩
  have : key a < key a := hsub (show key a < key b from h)
  exact lt_irrefl _ this

lemma rankBy_injective (hk : Injective key) (hfin : ∀ a, {b | key b < key a}.Finite) :
    Injective (rankBy key) := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne (hk.ne hne) with h | h
  · exact absurd hab (rankBy_lt_rankBy hfin h).ne
  · exact absurd hab (rankBy_lt_rankBy hfin h).ne'

lemma rankBy_bijective [Infinite α] (hk : Injective key)
    (hfin : ∀ a, {b | key b < key a}.Finite) : Bijective (rankBy key) := by
  have hinj := rankBy_injective hk hfin
  refine ⟨hinj, fun n => ?_⟩
  obtain ⟨m, ⟨a, rfl⟩, hm⟩ := (Set.infinite_range_of_injective hinj).exists_gt n
  set L := {b | key b < key a} with hL
  have hmaps : MapsTo (rankBy key) L (Iio (rankBy key a)) := fun c hc =>
    rankBy_lt_rankBy hfin hc
  have himg : rankBy key '' L = Iio (rankBy key a) := by
    apply Set.eq_of_subset_of_ncard_le (hmaps.image_subset)
    · rw [Set.ncard_image_of_injective _ hinj]
      simp [Set.ncard_eq_toFinset_card', rankBy, hL]
  have : n ∈ rankBy key '' L := by rw [himg]; exact hm
  obtain ⟨b, -, hb⟩ := this
  exact ⟨b, hb⟩

end Rank

/-! ### Height -/

/-- Equation (04): the height `ht(p/q) = max{|p|, q}` of a reduced fraction. -/
def ht (r : ℚ) : ℕ := max r.num.natAbs r.den

/-- `ℚ_H = {r ∈ ℚ : ht r ≤ H}`. -/
def QH (H : ℕ) : Set ℚ := {r | ht r ≤ H}

lemma one_le_ht (r : ℚ) : 1 ≤ ht r := le_max_of_le_right r.den_pos

lemma mapsTo_numDen (H : ℕ) :
    MapsTo (fun r : ℚ => (r.num, r.den)) (QH H)
      (↑((Finset.Icc (-(H : ℤ)) H) ×ˢ (Finset.Icc 1 H))) := by
  intro r hr
  simp only [QH, ht, mem_setOf_eq, max_le_iff] at hr
  simp only [Finset.coe_product, Finset.coe_Icc, mem_prod, mem_Icc]
  refine ⟨⟨?_, ?_⟩, r.den_pos, hr.2⟩ <;> omega

lemma injOn_numDen (s : Set ℚ) : InjOn (fun r : ℚ => (r.num, r.den)) s := by
  intro a _ b _ h
  simp only [Prod.mk.injEq] at h
  exact Rat.ext h.1 h.2

lemma QH_finite (H : ℕ) : (QH H).Finite :=
  Set.Finite.of_finite_image
    ((Finset.finite_toSet _).subset ((mapsTo_numDen H).image_subset)) (injOn_numDen _)

/-- **Lemma 2.3, Equation (06).** `|ℚ_H| ≤ 3H²` for every `H ≥ 1`. -/
theorem QH_ncard_le (H : ℕ) (hH : 1 ≤ H) : (QH H).ncard ≤ 3 * H ^ 2 := by
  have := Set.ncard_le_ncard_of_injOn _ (mapsTo_numDen H) (injOn_numDen _)
    (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_product, Int.card_Icc, Nat.card_Icc] at this
  have h2 : (↑H + 1 - -(H : ℤ)).toNat = 2 * H + 1 := by omega
  rw [h2, Nat.add_sub_cancel] at this
  nlinarith

/-- The elementary estimate `∑_{d=2}^{N} 1/d² ≤ 3/4 - 1/N` (for `N ≥ 2`). -/
lemma sum_inv_sq_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ d ∈ Finset.Icc 2 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 3 / 4 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have key : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / n - 1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      have e : (1 : ℝ) / n - 1 / (n + 1) = 1 / (n * (n + 1)) := by field_simp; ring
      rw [e]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    linarith

/-- `4 ∑_{d=2}^{H} ⌊H/d⌋² ≤ 3H²`. -/
lemma sum_div_sq_le (H : ℕ) : 4 * ∑ d ∈ Finset.Icc 2 H, (H / d) ^ 2 ≤ 3 * H ^ 2 := by
  rcases lt_or_ge H 2 with hH | hH
  · rw [Finset.Icc_eq_empty (by omega)]; simp
  have hr : (∑ d ∈ Finset.Icc 2 H, ((H / d : ℕ) : ℝ) ^ 2) ≤
      (H : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 2 H, (1 : ℝ) / (d : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd2 : (0 : ℝ) < d := by
      have := (Finset.mem_Icc.1 hd).1; exact_mod_cast (show 0 < d by omega)
    have h1 : ((H / d : ℕ) : ℝ) ≤ (H : ℝ) / d := Nat.cast_div_le
    have h0 : (0 : ℝ) ≤ ((H / d : ℕ) : ℝ) := by positivity
    calc ((H / d : ℕ) : ℝ) ^ 2 ≤ ((H : ℝ) / d) ^ 2 := by gcongr
      _ = (H : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by field_simp
  have hs := sum_inv_sq_le H hH
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have : (4 * ∑ d ∈ Finset.Icc 2 H, (H / d) ^ 2 : ℕ) ≤ ((3 * H ^ 2 : ℕ) : ℝ) := by
    push_cast
    have : (H : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 2 H, (1 : ℝ) / (d : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 * (3 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : (0 : ℝ) < 1 / H := by positivity
      linarith
    linarith
  exact_mod_cast this

/-- The coprime pairs in `[1,H]²`. -/
def coprimePairs (H : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter (fun p => Nat.Coprime p.1 p.2)

/-- Sieve bound: there are at least `H²/4` coprime pairs in `[1,H]²`. -/
lemma coprimePairs_card (H : ℕ) : H ^ 2 ≤ 4 * (coprimePairs H).card := by
  set S := Finset.Icc 1 H ×ˢ Finset.Icc 1 H with hS
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S) (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)
  have hScard : S.card = H ^ 2 := by simp [hS, sq]
  have hsub : S.filter (fun p : ℕ × ℕ => ¬ Nat.Coprime p.1 p.2) ⊆
      (Finset.Icc 2 H).biUnion (fun d => (Finset.Icc 1 (H / d) ×ˢ Finset.Icc 1 (H / d)).image
        (fun ab : ℕ × ℕ => (d * ab.1, d * ab.2))) := by
    intro p hp
    simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hnc⟩ := hp
    set g := Nat.gcd p.1 p.2 with hg
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hg2 : 2 ≤ g := by
      unfold Nat.Coprime at hnc; omega
    have hgle : g ≤ H := le_trans (Nat.gcd_le_left _ (by omega)) h2
    have hd1 : g ∣ p.1 := Nat.gcd_dvd_left _ _
    have hd2 : g ∣ p.2 := Nat.gcd_dvd_right _ _
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_product]
    refine ⟨g, ⟨hg2, hgle⟩, (p.1 / g, p.2 / g), ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hd1) hgpos
    · exact Nat.div_le_div_right h2
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hd2) hgpos
    · exact Nat.div_le_div_right h4
    · ext
      · exact Nat.mul_div_cancel' hd1
      · exact Nat.mul_div_cancel' hd2
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hcard2 : ∑ d ∈ Finset.Icc 2 H,
      ((Finset.Icc 1 (H / d) ×ˢ Finset.Icc 1 (H / d)).image
        (fun ab : ℕ × ℕ => (d * ab.1, d * ab.2))).card ≤ ∑ d ∈ Finset.Icc 2 H, (H / d) ^ 2 := by
    apply Finset.sum_le_sum
    intro d _
    refine Finset.card_image_le.trans ?_
    simp [sq]
  have := sum_div_sq_le H
  unfold coprimePairs
  rw [← hS]
  omega

/-- **Lemma 2.3, Equation (07) with `c₁ = 1/4`.** In fact `|ℚ_H| ≥ H²/4` holds for every `H`.
(The proof uses an elementary sieve instead of Mertens' asymptotic for `∑ φ(q)`.) -/
theorem QH_ncard_ge (H : ℕ) : (H : ℝ) ^ 2 / 4 ≤ (QH H).ncard := by
  have hmaps : MapsTo (fun p : ℕ × ℕ => (p.1 : ℚ) / p.2) (↑(coprimePairs H)) (QH H) := by
    intro p hp
    simp only [coprimePairs, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      mem_setOf_eq] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hc⟩ := hp
    have hq : (0 : ℤ) < (p.2 : ℤ) := by exact_mod_cast (show 0 < p.2 by omega)
    have hc' : Nat.Coprime ((p.1 : ℤ)).natAbs ((p.2 : ℤ)).natAbs := by simpa using hc
    have hnum := Rat.num_div_eq_of_coprime hq hc'
    have hden := Rat.den_div_eq_of_coprime hq hc'
    simp only [QH, ht, mem_setOf_eq]
    have e : ((p.1 : ℚ) / p.2) = ((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ) := by push_cast; rfl
    rw [e, hnum]
    have hden' : (((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ)).den = p.2 := by exact_mod_cast hden
    rw [hden']
    simp only [Int.natAbs_natCast, max_le_iff]
    exact ⟨h2, h4⟩
  have hinj : InjOn (fun p : ℕ × ℕ => (p.1 : ℚ) / p.2) (↑(coprimePairs H)) := by
    intro p hp p' hp' h
    simp only [coprimePairs, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc,
      mem_setOf_eq] at hp hp'
    have hq : (0 : ℤ) < (p.2 : ℤ) := by exact_mod_cast (show 0 < p.2 by omega)
    have hq' : (0 : ℤ) < (p'.2 : ℤ) := by exact_mod_cast (show 0 < p'.2 by omega)
    have e : ((p.1 : ℚ) / p.2) = ((p.1 : ℤ) : ℚ) / ((p.2 : ℤ) : ℚ) := by push_cast; rfl
    have e' : ((p'.1 : ℚ) / p'.2) = ((p'.1 : ℤ) : ℚ) / ((p'.2 : ℤ) : ℚ) := by push_cast; rfl
    simp only at h
    rw [e, e'] at h
    have c1 : Nat.Coprime ((p.1 : ℤ)).natAbs ((p.2 : ℤ)).natAbs := by simpa using hp.2
    have c2 : Nat.Coprime ((p'.1 : ℤ)).natAbs ((p'.2 : ℤ)).natAbs := by simpa using hp'.2
    have n1 := Rat.num_div_eq_of_coprime hq c1
    have n2 := Rat.num_div_eq_of_coprime hq' c2
    have d1 := Rat.den_div_eq_of_coprime hq c1
    have d2 := Rat.den_div_eq_of_coprime hq' c2
    rw [h] at n1 d1
    ext
    · exact_mod_cast n1.symm.trans n2
    · exact_mod_cast d1.symm.trans d2
  have h1 := Set.ncard_le_ncard_of_injOn _ hmaps hinj (QH_finite H)
  rw [Set.ncard_coe_finset] at h1
  have h2 := coprimePairs_card H
  have : (H : ℝ) ^ 2 ≤ 4 * ((QH H).ncard : ℝ) := by exact_mod_cast h2.trans (by omega)
  linarith

/-- **Lemma 2.3, Equation (07).** There are universal `H₀` and `c₁ > 0` with
`|ℚ_H| ≥ c₁ H²` for all `H ≥ H₀`; one can take `c₁ = 1/4`. -/
theorem QH_ncard_ge_exists :
    ∃ H₀ : ℕ, ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ = 1 / 4 ∧ ∀ H ≥ H₀, c₁ * (H : ℝ) ^ 2 ≤ (QH H).ncard :=
  ⟨0, 1 / 4, by norm_num, rfl, fun H _ => by have := QH_ncard_ge H; linarith⟩

/-! ### The enumerations `Q : ℕ₀ → ℚ` and `Q* : ℕ₀ → ℚ*`, Equation (05) -/

/-- The ordering key: first by height, then by the denominator `q`, then by the numerator `p`. -/
def htKey (r : ℚ) : ℕ ×ₗ ℕ ×ₗ ℤ := toLex (ht r, toLex (r.den, r.num))

lemma htKey_injective : Injective htKey := by
  intro a b h
  simp only [htKey, toLex_inj, Prod.mk.injEq] at h
  exact Rat.ext h.2.2 h.2.1

lemma ht_le_of_htKey_lt {a b : ℚ} (h : htKey a < htKey b) : ht a ≤ ht b := by
  simp only [htKey, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

lemma htKey_lowerset_subset (r : ℚ) : {b | htKey b < htKey r} ⊆ QH (ht r) \ {r} := by
  intro b hb
  exact ⟨ht_le_of_htKey_lt hb, fun h => by
    rw [mem_singleton_iff] at h; subst h; exact lt_irrefl (htKey b) hb⟩

lemma htKey_lowerset_finite (r : ℚ) : {b | htKey b < htKey r}.Finite :=
  ((QH_finite _).diff).subset (htKey_lowerset_subset r)

lemma htKey_lowerset_finite' (r : {r : ℚ // r ≠ 0}) :
    {b : {r : ℚ // r ≠ 0} | htKey b.1 < htKey r.1}.Finite :=
  Set.Finite.of_finite_image ((htKey_lowerset_finite r.1).subset (by
    rintro _ ⟨b, hb, rfl⟩; exact hb)) Subtype.val_injective.injOn

instance : Infinite {r : ℚ // r ≠ 0} :=
  Set.infinite_coe_iff.2 ((Set.infinite_univ (α := ℚ)).diff (Set.finite_singleton 0) |>.mono
    (fun x hx => by simpa using hx.2))

/-- Rank of a rational in the height ordering. -/
noncomputable def Qrank : ℚ → ℕ := rankBy htKey

/-- Rank of a nonzero rational in the height ordering of `ℚ*` (with `0/1` omitted). -/
noncomputable def Qstarrank : {r : ℚ // r ≠ 0} → ℕ := rankBy (fun r => htKey r.1)

/-- **Lemma 2.4 (bijectivity for `Q`).** -/
theorem Qrank_bijective : Bijective Qrank :=
  rankBy_bijective htKey_injective htKey_lowerset_finite

/-- **Lemma 2.4 (bijectivity for `Q*`).** -/
theorem Qstarrank_bijective : Bijective Qstarrank :=
  rankBy_bijective (htKey_injective.comp Subtype.val_injective) htKey_lowerset_finite'

/-- Equation (05): `Q : ℕ₀ → ℚ`, reading the reduced fractions by height, then `q`, then `p`. -/
noncomputable def Qenum : ℕ ≃ ℚ := (Equiv.ofBijective Qrank Qrank_bijective).symm

/-- Equation (05): `Q* : ℕ₀ → ℚ*`, the same reading with `0/1` omitted. -/
noncomputable def Qstar : ℕ ≃ {r : ℚ // r ≠ 0} :=
  (Equiv.ofBijective Qstarrank Qstarrank_bijective).symm

/-- `Q` lists the rationals in the order "height, then `q`, then `p`". -/
theorem Qenum_lt_iff (i j : ℕ) : i < j ↔ htKey (Qenum i) < htKey (Qenum j) := by
  have hi : Qrank (Qenum i) = i := (Equiv.ofBijective Qrank Qrank_bijective).apply_symm_apply i
  have hj : Qrank (Qenum j) = j := (Equiv.ofBijective Qrank Qrank_bijective).apply_symm_apply j
  constructor
  · intro h
    rcases lt_trichotomy (htKey (Qenum i)) (htKey (Qenum j)) with h' | h' | h'
    · exact h'
    · have := Qenum.injective (htKey_injective h'); omega
    · have := rankBy_lt_rankBy htKey_lowerset_finite h'
      change Qrank _ < Qrank _ at this; omega
  · intro h
    have := rankBy_lt_rankBy htKey_lowerset_finite h
    change Qrank _ < Qrank _ at this; omega

/-- `Q*` lists the nonzero rationals in the order "height, then `q`, then `p`". -/
theorem Qstar_lt_iff (i j : ℕ) : i < j ↔ htKey (Qstar i).1 < htKey (Qstar j).1 := by
  have hi : Qstarrank (Qstar i) = i :=
    (Equiv.ofBijective Qstarrank Qstarrank_bijective).apply_symm_apply i
  have hj : Qstarrank (Qstar j) = j :=
    (Equiv.ofBijective Qstarrank Qstarrank_bijective).apply_symm_apply j
  constructor
  · intro h
    rcases lt_trichotomy (htKey (Qstar i).1) (htKey (Qstar j).1) with h' | h' | h'
    · exact h'
    · have := Qstar.injective (Subtype.val_injective (htKey_injective h')); omega
    · have := rankBy_lt_rankBy htKey_lowerset_finite' (key := fun x : {r : ℚ // r ≠ 0} => htKey x.1) h'
      change Qstarrank _ < Qstarrank _ at this; omega
  · intro h
    have := rankBy_lt_rankBy htKey_lowerset_finite' (key := fun x : {r : ℚ // r ≠ 0} => htKey x.1) h
    change Qstarrank _ < Qstarrank _ at this; omega

/-- **Lemma 2.4 (rank bound for `Q`).** If `ht r ≤ H`, the rank of `r` is `< 3H²`. -/
theorem Qenum_symm_lt (r : ℚ) (H : ℕ) (h : ht r ≤ H) : Qenum.symm r < 3 * H ^ 2 := by
  change Qrank r < _
  have hH : 1 ≤ H := (one_le_ht r).trans h
  have hsub : {b | htKey b < htKey r} ⊂ QH H := by
    refine ⟨fun b hb => ((htKey_lowerset_subset r hb).1).trans h, fun hs => ?_⟩
    have : htKey r < htKey r := hs (show ht r ≤ H from h)
    exact lt_irrefl _ this
  exact (Set.ncard_lt_ncard hsub (QH_finite H)).trans_le (QH_ncard_le H hH)

/-- **Lemma 2.4 (rank bound for `Q*`).** If `ht r ≤ H`, the rank of `r` in `Q*` is `< 3H²`. -/
theorem Qstar_symm_lt (r : {r : ℚ // r ≠ 0}) (H : ℕ) (h : ht r.1 ≤ H) :
    Qstar.symm r < 3 * H ^ 2 := by
  change Qstarrank r < _
  have hH : 1 ≤ H := (one_le_ht _).trans h
  unfold Qstarrank rankBy
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  have hsub : Subtype.val '' {b : {r : ℚ // r ≠ 0} | htKey b.1 < htKey r.1} ⊂ QH H := by
    refine ⟨?_, fun hs => ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact ((htKey_lowerset_subset r.1 hb).1).trans h
    · obtain ⟨b, hb, hbr⟩ := hs (show ht r.1 ≤ H from h)
      have hb' : htKey b.1 < htKey r.1 := hb
      rw [hbr] at hb'
      exact lt_irrefl _ hb'
  exact (Set.ncard_lt_ncard hsub (QH_finite H)).trans_le (QH_ncard_le H hH)

/-! ### Stern's diatomic sequence and Calkin–Wilf, Equation (08) -/

/-- Stern's diatomic sequence, Equation (08). -/
def stern : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
    if h : (n + 2) % 2 = 0 then stern ((n + 2) / 2)
    else stern ((n + 2) / 2) + stern ((n + 2) / 2 + 1)
  decreasing_by all_goals omega

lemma stern_zero : stern 0 = 0 := by simp [stern]

lemma stern_one : stern 1 = 1 := by simp [stern]

lemma stern_two_mul (n : ℕ) : stern (2 * n) = stern n := by
  rcases n with _ | n
  · simp [stern]
  · rw [show 2 * (n + 1) = 2 * n + 2 by ring, stern]
    simp only [dif_pos (show (2 * n + 2) % 2 = 0 by omega)]
    congr 1; omega

lemma stern_two_mul_add_one (n : ℕ) : stern (2 * n + 1) = stern n + stern (n + 1) := by
  rcases n with _ | n
  · simp [stern]
  · rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, stern]
    simp only [dif_neg (show ¬ (2 * n + 1 + 2) % 2 = 0 by omega)]
    rw [show (2 * n + 1 + 2) / 2 = n + 1 by omega]

/-- The Calkin–Wilf enumeration `CW(n) = S_n / S_{n+1}`. -/
def CW (n : ℕ) : ℚ := (stern n : ℚ) / stern (n + 1)

lemma stern_two_pow (m : ℕ) : stern (2 ^ m) = 1 := by
  induction m with
  | zero => exact stern_one
  | succ m ih => rw [pow_succ, mul_comm, stern_two_mul, ih]

lemma stern_two_pow_add_one (m : ℕ) : stern (2 ^ m + 1) = m + 1 := by
  induction m with
  | zero => simp [stern]
  | succ m ih =>
    rw [pow_succ, mul_comm, stern_two_mul_add_one, stern_two_pow, ih]; ring

/-- **Lemma 2.5.** For every `q ≥ 1`, `CW(2^{q-1}) = 1/q`. -/
theorem CW_two_pow (q : ℕ) (hq : 1 ≤ q) : CW (2 ^ (q - 1)) = 1 / q := by
  unfold CW
  rw [stern_two_pow, stern_two_pow_add_one]
  congr 1
  push_cast [Nat.sub_add_cancel hq]
  ring

end Dyadic2
