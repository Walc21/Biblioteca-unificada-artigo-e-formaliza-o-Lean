import RequestProject.Catalog

/-!
# Section 4 — Library interface and boundary states

* Definition 4.1 (admissible boundary pairs `𝒫_H(J)`),
* Proposition 4.2 (exact endpoint dictionary, `|𝒫_H(J)| = q_H(q_H - 1)`),
* Definition 4.3 / Lemma 4.4 (the finite value alphabet `𝒱_{D,H}(K)`),
* Proposition 4.5 (empty cells and maximal uniform refinement).
-/

namespace Artigo

open Set LTree

/-! ## Definition 4.1 -/

/-- the defining conditions of `𝒫_H(J_{k,m})` -/
def IsAdmPair (H k : ℕ) (m : ℤ) (p : ℚ × ℚ) : Prop :=
  p.1 ≠ p.2 ∧ ht ((p.1 + p.2) / 2) ≤ H ∧ ht (2 ^ k * (p.2 - p.1)) ≤ H ∧ k + 1 ≤ H ∧ m.natAbs + 1 ≤ H

/-- `(y₀, s) ↦ (u, v) = (y₀ - s/2^{k+1}, y₀ + s/2^{k+1})` -/
def endpointsOf (k : ℕ) (p : ℚ × ℚ) : ℚ × ℚ := (p.1 - p.2 / 2 ^ (k + 1), p.1 + p.2 / 2 ^ (k + 1))

open Classical in
/-- `𝒫_H(J_{k,m})` as a finite set -/
noncomputable def PH (H k : ℕ) (m : ℤ) : Finset (ℚ × ℚ) :=
  if k + 1 ≤ H ∧ m.natAbs + 1 ≤ H then ((QH H) ×ˢ ((QH H).erase 0)).image (endpointsOf k) else ∅

lemma endpointsOf_inv (k : ℕ) (p : ℚ × ℚ) :
    ((endpointsOf k p).1 + (endpointsOf k p).2) / 2 = p.1 ∧
      2 ^ k * ((endpointsOf k p).2 - (endpointsOf k p).1) = p.2 := by
  simp only [endpointsOf]; constructor
  · ring
  · rw [pow_succ]; field_simp; ring

lemma mem_PH {H k : ℕ} {m : ℤ} {p : ℚ × ℚ} : p ∈ PH H k m ↔ IsAdmPair H k m p := by
  classical
  unfold PH IsAdmPair
  split_ifs with hg
  · simp only [Finset.mem_image, Finset.mem_product, Finset.mem_erase, mem_QH, Prod.exists]
    constructor
    · rintro ⟨y, s, ⟨hy, hs0, hs⟩, rfl⟩
      obtain ⟨e1, e2⟩ := endpointsOf_inv k (y, s)
      refine ⟨?_, by rw [e1]; exact hy, by rw [e2]; exact hs, hg.1, hg.2⟩
      simp only [endpointsOf]
      intro h
      have : s / 2 ^ (k + 1) = 0 := by linarith
      exact hs0 (by simpa using this)
    · rintro ⟨hne, hy, hs, -, -⟩
      refine ⟨(p.1 + p.2) / 2, 2 ^ k * (p.2 - p.1), ⟨hy, ?_, hs⟩, ?_⟩
      · exact mul_ne_zero (by positivity) (sub_ne_zero.mpr (Ne.symm hne))
      · simp only [endpointsOf]; ext <;> simp only <;> rw [pow_succ] <;> field_simp <;> ring
  · simp only [Finset.notMem_empty, false_iff]
    tauto

/-! ## Proposition 4.2 -/

/-- **Proposition 4.2 (dicionário exato de fronteiras)**.  The endpoint map
`ℓ ↦ (ℓ(left), ℓ(right))` is a bijection from the atoms of `𝓛_H` supported on `J_{k,m}` onto
`𝒫_H(J_{k,m})`, and `|𝒫_H(J)| = q_H (q_H - 1)` if `k+1 ≤ H` and `|m|+1 ≤ H`, `0` otherwise
(here `H ≥ 2`). -/
theorem endpoint_dictionary {H k : ℕ} {m : ℤ} (hH : 2 ≤ H) :
    Set.BijOn (fun a : Atom => (a.lval, a.rval)) {a | a.height ≤ H ∧ a.k = k ∧ a.m = m}
      (PH H k m : Set (ℚ × ℚ)) ∧
    (PH H k m).card = if k + 1 ≤ H ∧ m.natAbs + 1 ≤ H then (QH H).card * ((QH H).card - 1) else 0 := by
  classical
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rintro a ⟨ha, rfl, rfl⟩
    rw [Finset.mem_coe, mem_PH]
    rw [Atom.height_le_iff] at ha
    refine ⟨a.lval_ne_rval, ?_, ?_, ha.2.1, ha.2.2.1⟩
    · rw [← a.y0_eq]; exact ha.2.2.2.1
    · rw [← a.s_eq]; exact ha.2.2.2.2
  · rintro a ⟨-, hk, hm⟩ b ⟨-, hk', hm'⟩ hab
    simp only [Prod.mk.injEq] at hab
    rw [a.eq_ofEndpoints, b.eq_ofEndpoints]
    subst hk hm
    simp only [Atom.ofEndpoints, hab.1, hab.2, hk', hm']
  · rintro ⟨u, v⟩ hp
    rw [Finset.mem_coe, mem_PH] at hp
    obtain ⟨hne, hy, hs, hk, hm⟩ := hp
    refine ⟨Atom.ofEndpoints k m u v hne, ⟨?_, rfl, rfl⟩, ?_⟩
    · rw [Atom.height_le_iff]
      exact ⟨by omega, hk, hm, hy, hs⟩
    · simp only [Atom.ofEndpoints_lval, Atom.ofEndpoints_rval]
  · unfold PH
    split_ifs with hg
    · rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_erase_of_mem (zero_mem_QH (by omega))]
      intro p _ q _ hpq
      have h1 := endpointsOf_inv k p
      have h2 := endpointsOf_inv k q
      rw [hpq] at h1
      exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
    · rfl

/-! ## Definition 4.3 and Lemma 4.4 -/

open Classical in
/-- the value alphabet `𝒱_{D,H}(K)`, `K = J_{k₀,m₀}`: all endpoint values of admissible pairs on the
descendants `J_{k₀+r, 2^r m₀ + j}` (`r ≤ D`, `0 ≤ j < 2^r`) -/
noncomputable def Valphabet (H D k₀ : ℕ) (m₀ : ℤ) : Finset ℚ :=
  (Finset.range (D + 1)).biUnion fun r => (Finset.range (2 ^ r)).biUnion fun j =>
    (PH H (k₀ + r) (2 ^ r * m₀ + j)).biUnion fun p => {p.1, p.2}

lemma WF_leaf_depth : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → ∀ a ∈ T.leaves, a.k ≤ k + T.depth := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h b hb; simp [leaves] at hb; subst hb; simp [depth, h.1]
  | node l r ihl ihr =>
    intro h b hb
    obtain ⟨hl, hr, _⟩ := h
    simp only [leaves, List.mem_append] at hb
    simp only [depth]
    rcases hb with hb | hb
    · have := ihl hl b hb; omega
    · have := ihr hr b hb; omega

/-- **Lemma 4.4 (finitude e suficiência)**: `𝒱_{D,H}(K)` is finite (a `Finset`), contains every
leaf-boundary value of every representation in `𝔑_{D,H}(K)`, and
`|𝒱_{D,H}(K)| ≤ min {2 S_D q_H(q_H-1), 2|𝓛_H|} ≤ min {18 S_D H⁴, 36 H⁶}`, `S_D = 2^{D+1} - 1`. -/
theorem value_alphabet {H D k₀ : ℕ} {m₀ : ℤ} (hH : 2 ≤ H) :
    (∀ T ∈ RepCat H D k₀ m₀, ∀ a ∈ T.leaves, a.lval ∈ Valphabet H D k₀ m₀ ∧
      a.rval ∈ Valphabet H D k₀ m₀) ∧
    (Valphabet H D k₀ m₀).card ≤ 2 * (2 ^ (D + 1) - 1) * ((QH H).card * ((QH H).card - 1)) ∧
    (Valphabet H D k₀ m₀).card ≤ 2 * (LH H).card ∧
    (Valphabet H D k₀ m₀).card ≤ 18 * (2 ^ (D + 1) - 1) * H ^ 4 ∧
    (Valphabet H D k₀ m₀).card ≤ 36 * H ^ 6 := by
  classical
  set q := (QH H).card
  have hq : q ≤ 3 * H ^ 2 := card_QH_le H
  have hPH : ∀ k (m : ℤ), (PH H k m).card ≤ q * (q - 1) := by
    intro k m
    rw [(endpoint_dictionary (k := k) (m := m) hH).2]
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  -- first bound
  have hS : ∑ r ∈ Finset.range (D + 1), 2 ^ r = 2 ^ (D + 1) - 1 := by
    rw [Nat.geomSum_eq le_rfl]; simp
  have h1 : (Valphabet H D k₀ m₀).card ≤ 2 * (2 ^ (D + 1) - 1) * (q * (q - 1)) := by
    unfold Valphabet
    refine Finset.card_biUnion_le.trans ?_
    calc _ ≤ ∑ r ∈ Finset.range (D + 1), 2 ^ r * (2 * (q * (q - 1))) := by
          apply Finset.sum_le_sum; intro r _
          refine Finset.card_biUnion_le.trans ?_
          calc _ ≤ ∑ j ∈ Finset.range (2 ^ r), 2 * (q * (q - 1)) := by
                apply Finset.sum_le_sum; intro j _
                refine Finset.card_biUnion_le.trans ?_
                calc _ ≤ ∑ p ∈ PH H (k₀ + r) (2 ^ r * m₀ + j), 2 := by
                      apply Finset.sum_le_sum; intro p _; exact Finset.card_le_two
                  _ = 2 * (PH H (k₀ + r) (2 ^ r * m₀ + j)).card := by
                      rw [Finset.sum_const, smul_eq_mul, mul_comm]
                  _ ≤ _ := by gcongr; exact hPH _ _
            _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ = (∑ r ∈ Finset.range (D + 1), 2 ^ r) * (2 * (q * (q - 1))) := by rw [Finset.sum_mul]
      _ = _ := by rw [hS]; ring
  -- second bound: every value is an endpoint of an atom of `𝓛_H`
  have hsub : Valphabet H D k₀ m₀ ⊆ (LH H).biUnion fun a => {a.lval, a.rval} := by
    intro x hx
    unfold Valphabet at hx
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton] at hx
    obtain ⟨r, -, j, -, p, hp, hx⟩ := hx
    obtain ⟨a, ⟨ha, -, -⟩, hap⟩ := (endpoint_dictionary hH).1.2.2 (Finset.mem_coe.mpr hp)
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, mem_LH]
    refine ⟨a, ha, ?_⟩
    rw [← hap] at hx; exact hx
  have h2 : (Valphabet H D k₀ m₀).card ≤ 2 * (LH H).card := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    calc _ ≤ ∑ a ∈ LH H, 2 := Finset.sum_le_sum fun a _ => Finset.card_le_two
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  refine ⟨?_, h1, h2, ?_, ?_⟩
  · intro T hT a ha
    obtain ⟨hWF, hd, hh⟩ := mem_RepCat.mp hT
    obtain ⟨hk, hm⟩ := WF_leaf_anc hWF a ha
    have hkd := WF_leaf_depth hWF a ha
    set r := a.k - k₀
    have hpos : (0 : ℤ) < 2 ^ r := by positivity
    have hj0 : 0 ≤ a.m % 2 ^ r := Int.emod_nonneg _ hpos.ne'
    have hj1 : a.m % 2 ^ r < 2 ^ r := Int.emod_lt_of_pos _ hpos
    have hdec : a.m = 2 ^ r * m₀ + (a.m % 2 ^ r) := by rw [← hm]; exact (Int.mul_ediv_add_emod _ _).symm
    have hmemP : (a.lval, a.rval) ∈ PH H (k₀ + r) (2 ^ r * m₀ + ((a.m % 2 ^ r).toNat : ℤ)) := by
      have := (endpoint_dictionary (k := a.k) (m := a.m) hH).1.1 ⟨le_trans (le_maxHeight ha) hh, rfl, rfl⟩
      rw [Finset.mem_coe] at this
      convert this using 2
      · omega
      · rw [Int.toNat_of_nonneg hj0]; exact hdec.symm
    have hjr : (a.m % 2 ^ r).toNat < 2 ^ r := by
      have h' : ((a.m % 2 ^ r).toNat : ℤ) < ((2 ^ r : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hj0]; push_cast; exact hj1
      exact_mod_cast h'
    unfold Valphabet
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨⟨r, by omega, _, hjr, _, hmemP, Or.inl rfl⟩, ⟨r, by omega, _, hjr, _, hmemP, Or.inr rfl⟩⟩
  · refine h1.trans ?_
    have : q * (q - 1) ≤ 9 * H ^ 4 := by
      calc q * (q - 1) ≤ q * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ (3 * H ^ 2) * (3 * H ^ 2) := Nat.mul_le_mul hq hq
        _ = 9 * H ^ 4 := by ring
    calc 2 * (2 ^ (D + 1) - 1) * (q * (q - 1)) ≤ 2 * (2 ^ (D + 1) - 1) * (9 * H ^ 4) := by gcongr
      _ = _ := by ring
  · have := card_LH_le hH; omega

/-! ## Proposition 4.5 -/

lemma PH_nonempty_iff {H k : ℕ} {m : ℤ} (hH : 2 ≤ H) :
    (PH H k m).Nonempty ↔ k + 1 ≤ H ∧ m.natAbs + 1 ≤ H := by
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_PH] at hp
    exact ⟨hp.2.2.2.1, hp.2.2.2.2⟩
  · intro hg
    obtain ⟨e1, e2⟩ := endpointsOf_inv k (0, 1)
    refine ⟨endpointsOf k (0, 1), mem_PH.mpr ⟨?_, ?_, ?_, hg.1, hg.2⟩⟩
    · intro h; rw [h, sub_self, mul_zero] at e2; exact zero_ne_one e2
    · rw [e1, ht_zero]; omega
    · rw [e2]; simp [ht]; omega

lemma PH_desc_nonempty_iff {H k₀ m₀ r j : ℕ} (hH : 2 ≤ H) :
    (PH H (k₀ + r) ((2 ^ r * m₀ + j : ℕ) : ℤ)).Nonempty ↔ k₀ + r + 1 ≤ H ∧ 2 ^ r * m₀ + j + 1 ≤ H := by
  rw [PH_nonempty_iff hH, Int.natAbs_natCast]

open Classical in
/-- **Proposition 4.5 (células vazias e refinamento uniforme máximo)**.  For `K = J_{k₀,m₀}`
(`m₀ ≥ 0`) and the descendants `J = J_{k₀+r, 2^r m₀ + j}`, `0 ≤ j < 2^r`:
(i) `𝒫_H(J) ≠ ∅ ⟺ k₀+r+1 ≤ H ∧ 2^r m₀ + j + 1 ≤ H`;
(ii) the number `N_r` of non-empty cells is `min {2^r, max{0, H - 2^r m₀}}` if `k₀+r+1 ≤ H`, else `0`;
(iii) all `2^r` cells are non-empty iff `k₀+r+1 ≤ H` and `2^r(m₀+1) ≤ H`,
(iv) i.e. iff `r ≤ min {H - k₀ - 1, log₂ (H/(m₀+1))}`. -/
theorem translation_obstruction {H k₀ m₀ r : ℕ} (hH : 2 ≤ H) :
    (∀ j < 2 ^ r, (PH H (k₀ + r) ((2 ^ r * m₀ + j : ℕ) : ℤ)).Nonempty ↔
      k₀ + r + 1 ≤ H ∧ 2 ^ r * m₀ + j + 1 ≤ H) ∧
    ((Finset.range (2 ^ r)).filter fun j => (PH H (k₀ + r) ((2 ^ r * m₀ + j : ℕ) : ℤ)).Nonempty).card =
      (if k₀ + r + 1 ≤ H then min (2 ^ r) (H - 2 ^ r * m₀) else 0) ∧
    ((∀ j < 2 ^ r, (PH H (k₀ + r) ((2 ^ r * m₀ + j : ℕ) : ℤ)).Nonempty) ↔
      k₀ + r + 1 ≤ H ∧ 2 ^ r * (m₀ + 1) ≤ H) ∧
    (k₀ + r + 1 ≤ H ∧ 2 ^ r * (m₀ + 1) ≤ H ↔
      (r : ℝ) ≤ min ((H : ℝ) - k₀ - 1) (Real.logb 2 ((H : ℝ) / (m₀ + 1)))) := by
  have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  refine ⟨fun j _ => PH_desc_nonempty_iff hH, ?_, ?_, ?_⟩
  · split_ifs with hs
    · rw [← Finset.card_range (min (2 ^ r) (H - 2 ^ r * m₀))]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, PH_desc_nonempty_iff hH]
      omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      rw [PH_desc_nonempty_iff hH] at h
      exact hs h.1
  · constructor
    · intro h
      have := (PH_desc_nonempty_iff hH).mp (h (2 ^ r - 1) (by omega))
      refine ⟨this.1, ?_⟩
      have := this.2
      rw [mul_add, mul_one]; omega
    · rintro ⟨h1, h2⟩ j hj
      rw [PH_desc_nonempty_iff hH]
      rw [mul_add, mul_one] at h2
      exact ⟨h1, by omega⟩
  · have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    have hm : (0 : ℝ) < m₀ + 1 := by positivity
    rw [le_min_iff, Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast,
      le_div_iff₀ hm]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : ((k₀ + r + 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast h1
        push_cast at this; linarith
      · have : ((2 ^ r * (m₀ + 1) : ℕ) : ℝ) ≤ H := by exact_mod_cast h2
        push_cast at this; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : ((k₀ + r + 1 : ℕ) : ℝ) ≤ H := by push_cast; linarith
        exact_mod_cast this
      · have : ((2 ^ r * (m₀ + 1) : ℕ) : ℝ) ≤ H := by push_cast; linarith
        exact_mod_cast this

end Artigo
