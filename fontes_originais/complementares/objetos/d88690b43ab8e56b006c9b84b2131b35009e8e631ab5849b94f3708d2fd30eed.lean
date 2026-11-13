module
public import RequestProject.Lib.Library
@[expose] public section

/-!
# Section 7.1–7.2: address length, height counting, minimax addresses

Theorem 7.1, Lemma 7.2, Proposition 7.3, Theorem 7.4, Definition 7.6 and Theorem 7.7.
-/

open Finset

namespace Dyadic.Lib

/-! ### Theorem 7.1 -/

lemma encode_le_height (a : Atom) : encode a ≤ 2116 * a.height ^ 8 := by
  have hk := a.k_lt_height
  have hm := a.m_lt_height
  have hy := rankQ_lt a.y0_le_height
  have hs := rankQstar_lt (s := ⟨a.s, a.hs⟩) a.s_le_height
  have hz := zEncode_le a.m
  have h2 := a.two_le_height
  set H := a.height
  have hu : cantorPair a.k (zEncode a.m) ≤ 9 * H ^ 2 := by
    refine (cantorPair_le _ _).trans ?_
    have : a.k + zEncode a.m + 1 ≤ 3 * H := by omega
    calc (a.k + zEncode a.m + 1) ^ 2 ≤ (3 * H) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 9 * H ^ 2 := by ring
  have hv : cantorPair (rankQ a.y0) (rankQstar ⟨a.s, a.hs⟩) ≤ 36 * H ^ 4 := by
    refine (cantorPair_le _ _).trans ?_
    have : rankQ a.y0 + rankQstar ⟨a.s, a.hs⟩ + 1 ≤ 6 * H ^ 2 := by omega
    calc _ ≤ (6 * H ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 36 * H ^ 4 := by ring
  unfold encode
  refine (cantorPair_le _ _).trans ?_
  have h1 : 1 ≤ H ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : H ^ 2 ≤ H ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have : cantorPair a.k (zEncode a.m) + cantorPair (rankQ a.y0) (rankQstar ⟨a.s, a.hs⟩) + 1
      ≤ 46 * H ^ 4 := by omega
  calc _ ≤ (46 * H ^ 4) ^ 2 := Nat.pow_le_pow_left this 2
    _ = 2116 * H ^ 8 := by ring

/-- **Theorem 7.1** (polynomial bound for the address): the unique address `n` of an atom of
height `H` satisfies `n = O(H⁸)` and `log₂(n+1) = O(log H)`, with universal constants. -/
theorem address_polynomial_bound :
    ∃ C₁ C₂ : ℝ, ∀ a : Atom,
      (encode a : ℝ) ≤ C₁ * (a.height : ℝ) ^ 8 ∧
      Real.logb 2 ((encode a : ℝ) + 1) ≤ C₂ * Real.logb 2 a.height := by
  refine ⟨2116, 20, fun a => ⟨by exact_mod_cast encode_le_height a, ?_⟩⟩
  have hH : (2 : ℝ) ≤ a.height := by exact_mod_cast a.two_le_height
  have hn : ((encode a : ℝ) + 1) ≤ 2117 * (a.height : ℝ) ^ 8 := by
    have := (show ((encode a : ℕ) : ℝ) ≤ 2116 * (a.height : ℝ) ^ 8 by
      exact_mod_cast encode_le_height a)
    have : (1 : ℝ) ≤ (a.height : ℝ) ^ 8 := one_le_pow₀ (by linarith)
    linarith
  have hl1 : 1 ≤ Real.logb 2 a.height := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hH
  have hpos : (0 : ℝ) < (encode a : ℝ) + 1 := by positivity
  calc Real.logb 2 ((encode a : ℝ) + 1) ≤ Real.logb 2 (2117 * (a.height : ℝ) ^ 8) :=
        Real.logb_le_logb_of_le (by norm_num) hpos hn
    _ = Real.logb 2 2117 + 8 * Real.logb 2 a.height := by
        rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]; push_cast; ring
    _ ≤ 12 + 8 * Real.logb 2 a.height := by
        have : Real.logb 2 2117 ≤ 12 := by
          rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
        linarith
    _ ≤ 20 * Real.logb 2 a.height := by linarith

/-! ### Lemma 7.2 -/

/-- **Lemma 7.2**, eq. (48): `|𝓛_H| ≤ 18 H⁶` for `H ≥ 2`. -/
theorem card_atomsUpTo_le {H : ℕ} (hH : 2 ≤ H) : (atomsUpTo H).card ≤ 18 * H ^ 6 := by
  rw [card_atomsUpTo hH]
  have hQ := card_ratsUpTo_le (show 1 ≤ H by omega)
  set Q := (ratsUpTo H).card
  have h1 : Q * (Q - 1) ≤ (3 * H ^ 2) * (3 * H ^ 2) :=
    Nat.mul_le_mul hQ (le_trans (Nat.sub_le _ _) hQ)
  have h2 : H * (2 * H - 1) ≤ H * (2 * H) := Nat.mul_le_mul_left _ (by omega)
  calc H * (2 * H - 1) * (Q * (Q - 1)) ≤ H * (2 * H) * ((3 * H ^ 2) * (3 * H ^ 2)) :=
        Nat.mul_le_mul h2 h1
    _ = 18 * H ^ 6 := by ring

/-- **Lemma 7.2**, eq. (49): `|𝓛_H| ≥ c_𝓛 H⁶` for `H ≥ H₁` (with `c_𝓛 = 1/32`, `H₁ = 4`). -/
theorem card_atomsUpTo_ge : ∃ c : ℝ, 0 < c ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧
    ∀ H ≥ H₁, c * (H : ℝ) ^ 6 ≤ (atomsUpTo H).card := by
  refine ⟨1 / 32, by norm_num, 4, by norm_num, fun H hH => ?_⟩
  rw [card_atomsUpTo (by omega)]
  have hQ := card_ratsUpTo_ge H
  set Q := (ratsUpTo H).card
  have hH' : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hQ4 : (4 : ℝ) ≤ Q := by nlinarith
  have hQ1 : 1 ≤ Q := by exact_mod_cast (show (1 : ℝ) ≤ Q by linarith)
  have h2H : 1 ≤ 2 * H := by omega
  push_cast [Nat.cast_sub hQ1, Nat.cast_sub h2H]
  have e1 : (H : ℝ) ≤ 2 * H - 1 := by linarith
  have e3 : (H : ℝ) ^ 4 / 16 ≤ (Q : ℝ) ^ 2 := by nlinarith
  have hHpos : (0 : ℝ) ≤ H := by positivity
  calc 1 / 32 * (H : ℝ) ^ 6 = (H * H) * ((H : ℝ) ^ 4 / 16 / 2) := by ring
    _ ≤ (H * (2 * H - 1)) * ((Q : ℝ) ^ 2 / 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left e1 hHpos) (by linarith) (by positivity)
          (by nlinarith)
    _ ≤ (H * (2 * H - 1)) * (Q * (Q - 1)) := by
        apply mul_le_mul_of_nonneg_left (by nlinarith) (by nlinarith)

/-! ### Proposition 7.3 -/

/-- The worst address `M_Γ(H) = max_{a ∈ 𝓛_H} Γ⁻¹(a)`. -/
noncomputable def worstAddress (H : ℕ) : ℕ := (atomsUpTo H).sup encode

lemma worstAddress_le {H : ℕ} : (worstAddress H : ℝ) ≤ 2116 * (H : ℝ) ^ 8 := by
  unfold worstAddress
  have : (atomsUpTo H).sup encode ≤ 2116 * H ^ 8 := by
    apply Finset.sup_le
    intro a ha
    rw [mem_atomsUpTo] at ha
    exact (encode_le_height a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha 8))
  exact_mod_cast this

lemma worstAddress_ge {H : ℕ} (hH : 4 ≤ H) : (H : ℝ) ^ 8 / 2048 ≤ worstAddress H := by
  have hQ := card_ratsUpTo_ge H
  have hH' : (4 : ℝ) ≤ H := by exact_mod_cast hH
  obtain ⟨y, hy, hry⟩ := exists_ge_card_sub_one rankQ_bijective.1 (ratsUpTo H)
    ⟨0, zero_mem_ratsUpTo (by omega)⟩
  obtain ⟨s, hs, hrs⟩ := exists_ge_card_sub_one rankQstar_bijective.1 (ratsStarUpTo H)
    ⟨⟨1, one_ne_zero⟩, by rw [mem_ratsStarUpTo]; simp [ratHeight]; omega⟩
  rw [card_ratsStarUpTo (by omega)] at hrs
  rw [mem_ratsUpTo] at hy
  rw [mem_ratsStarUpTo] at hs
  let a : Atom := ⟨0, 0, y, s.1, s.2⟩
  have ha : a ∈ atomsUpTo H := by
    rw [mem_atomsUpTo, Atom.height_le_iff]; simp only [a]; omega
  have hle : encode a ≤ worstAddress H := Finset.le_sup ha
  have henc : encode a = cantorPair 0 (cantorPair (rankQ y) (rankQstar s)) := by
    simp [encode, a, cantorPair, tri, zEncode]
  set Q := (ratsUpTo H).card
  set v := cantorPair (rankQ y) (rankQstar s)
  have hv : ((rankQ y + rankQstar s : ℕ) : ℝ) ^ 2 ≤ 2 * v := by
    exact_mod_cast cantorPair_ge (rankQ y) (rankQstar s)
  have hn : ((v : ℕ) : ℝ) ^ 2 ≤ 2 * encode a := by
    rw [henc]; exact_mod_cast (by simpa using cantorPair_ge 0 v)
  have hQ2 : 2 ≤ Q := by
    have : (2 : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this
  have hrt : (H : ℝ) ^ 2 / 4 ≤ ((rankQ y + rankQstar s : ℕ) : ℝ) := by
    have h1 : (Q : ℝ) - 1 ≤ rankQ y := by
      have : ((Q - 1 : ℕ) : ℝ) ≤ rankQ y := by exact_mod_cast hry
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
    have h2 : (Q : ℝ) - 2 ≤ rankQstar s := by
      have : ((Q - 1 - 1 : ℕ) : ℝ) ≤ rankQstar s := by exact_mod_cast hrs
      rw [Nat.sub_sub, Nat.cast_sub hQ2] at this
      push_cast at this; linarith
    push_cast; nlinarith
  have hv' : (H : ℝ) ^ 4 / 32 ≤ v := by nlinarith
  have hn' : (H : ℝ) ^ 8 / 2048 ≤ encode a := by
    have : ((H : ℝ) ^ 4 / 32) ^ 2 ≤ (v : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hv' 2
    nlinarith
  exact hn'.trans (by exact_mod_cast hle)

/-- **Proposition 7.3** (exact order of the worst arithmetic address):
`M_Γ(H) = Θ(H⁸)`, and the longest word of the arithmetic generator over `𝓛_H` has
`8 log₂ H + O(1)` bits. -/
theorem worstAddress_theta :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ H₀ : ℕ, ∀ H ≥ H₀,
      c * (H : ℝ) ^ 8 ≤ worstAddress H ∧ (worstAddress H : ℝ) ≤ C * (H : ℝ) ^ 8) ∧
    (∃ C : ℝ, ∃ H₀ : ℕ, ∀ H ≥ H₀,
      |Real.logb 2 ((worstAddress H : ℝ) + 1) - 8 * Real.logb 2 H| ≤ C) := by
  refine ⟨⟨1 / 2048, 2116, by norm_num, by norm_num, 4, fun H hH => ⟨?_, worstAddress_le⟩⟩,
    ⟨12, 4, fun H hH => ?_⟩⟩
  · have := worstAddress_ge hH; linarith
  · have hH' : (4 : ℝ) ≤ H := by exact_mod_cast hH
    have h1 := worstAddress_ge hH
    have h2 := (worstAddress_le (H := H))
    have hp : (0 : ℝ) < (H : ℝ) ^ 8 := by positivity
    have hl : Real.logb 2 ((H : ℝ) ^ 8) = 8 * Real.logb 2 H := by rw [Real.logb_pow]; ring
    have up : Real.logb 2 ((worstAddress H : ℝ) + 1) ≤ Real.logb 2 2117 + 8 * Real.logb 2 H := by
      rw [← hl, ← Real.logb_mul (by norm_num) hp.ne']
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      have : (1 : ℝ) ≤ (H : ℝ) ^ 8 := one_le_pow₀ (by linarith)
      linarith
    have lo : Real.logb 2 (1 / 2048) + 8 * Real.logb 2 H ≤
        Real.logb 2 ((worstAddress H : ℝ) + 1) := by
      rw [← hl, ← Real.logb_mul (by norm_num) hp.ne']
      apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
      linarith
    have c1 : Real.logb 2 2117 ≤ 12 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
    have c2 : Real.logb 2 (1 / 2048) = -11 := by
      rw [show (1 / 2048 : ℝ) = 2 ^ (-11 : ℝ) by norm_num, Real.logb_rpow (by norm_num)
        (by norm_num)]
    rw [abs_le]; constructor <;> linarith

/-! ### Theorem 7.4 -/

/-- **Theorem 7.4**, eq. (51): for any injective addressing `A : 𝓛 → ℕ` and `H ≥ 2`,
`max_{a ∈ 𝓛_H} A(a) ≥ |𝓛_H| - 1`. -/
theorem minimax_lower_bound (A : Atom → ℕ) (hA : Function.Injective A) (H : ℕ) :
    (atomsUpTo H).card - 1 ≤ (atomsUpTo H).sup A :=
  sup_ge_card_sub_one hA _

/-- **Theorem 7.4**, eq. (52): for `H ≥ H₁` there is an atom of height `≤ H` with
`A(atom) ≥ c_𝓛 H⁶ - 1` and `log₂(A(atom)+1) ≥ 6 log₂ H - O(1)`; in particular no injective
addressing uses `o(log H)` bits in the worst case over `𝓛_H`. -/
theorem minimax_lower_bound_asymptotic :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ H₁ : ℕ, 2 ≤ H₁ ∧
      ∀ (A : Atom → ℕ), Function.Injective A → ∀ H ≥ H₁,
        ∃ a : Atom, a.height ≤ H ∧ c * (H : ℝ) ^ 6 - 1 ≤ A a ∧
          6 * Real.logb 2 H - C ≤ Real.logb 2 ((A a : ℝ) + 1) := by
  obtain ⟨c, hc, H₁, hH₁, hcard⟩ := card_atomsUpTo_ge
  refine ⟨c, hc, -Real.logb 2 c, H₁, hH₁, fun A hA H hH => ?_⟩
  have hne : (atomsUpTo H).Nonempty := by
    refine ⟨⟨0, 0, 0, 1, one_ne_zero⟩, ?_⟩
    rw [mem_atomsUpTo, Atom.height_le_iff]; simp [ratHeight]; omega
  obtain ⟨a, ha, hAa⟩ := exists_ge_card_sub_one hA _ hne
  have hc' := hcard H hH
  have hcardpos : 1 ≤ (atomsUpTo H).card := Finset.card_pos.2 hne
  have h1 : ((atomsUpTo H).card : ℝ) ≤ A a + 1 := by
    have : (atomsUpTo H).card ≤ A a + 1 := by omega
    exact_mod_cast this
  refine ⟨a, mem_atomsUpTo.1 ha, by linarith, ?_⟩
  have hH' : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hpos : 0 < c * (H : ℝ) ^ 6 := by positivity
  calc 6 * Real.logb 2 H - -Real.logb 2 c = Real.logb 2 (c * (H : ℝ) ^ 6) := by
        rw [Real.logb_mul hc.ne' (by positivity), Real.logb_pow]; push_cast; ring
    _ ≤ Real.logb 2 ((A a : ℝ) + 1) :=
        Real.logb_le_logb_of_le (by norm_num) hpos (by linarith)

/-! ### Definition 7.6 and Theorem 7.7 -/

/-- Numerical key realising the order of Definition 7.6: shells of increasing height, and inside
a shell the lexicographic order of `(k, Z⁻¹(m), rank_Q(y₀), rank_{Q^*}(s))`. -/
noncomputable def sharpKey (a : Atom) : ℕ :=
  64 * a.height ^ 7 +
    (((a.k * (2 * a.height + 1) + zEncode a.m) * (3 * a.height ^ 2) + rankQ a.y0) *
      (3 * a.height ^ 2) + rankQstar ⟨a.s, a.hs⟩)

lemma mix_lt_iff {B x y c d : ℕ} (hc : c < B) (hd : d < B) :
    x * B + c < y * B + d ↔ x < y ∨ (x = y ∧ c < d) := by
  constructor
  · intro h
    rcases lt_trichotomy x y with h' | h' | h'
    · exact Or.inl h'
    · subst h'; right; exact ⟨rfl, by omega⟩
    · exfalso
      have : (y + 1) * B ≤ x * B := Nat.mul_le_mul_right _ h'
      nlinarith
  · rintro (h | ⟨rfl, h⟩)
    · have : (x + 1) * B ≤ y * B := Nat.mul_le_mul_right _ h
      nlinarith
    · omega

lemma mix_eq_iff {B x y c d : ℕ} (hc : c < B) (hd : d < B) :
    x * B + c = y * B + d ↔ x = y ∧ c = d := by
  constructor
  · intro heq
    rcases lt_trichotomy x y with hk | hk | hk
    · exact absurd heq (ne_of_lt ((mix_lt_iff hc hd).2 (Or.inl hk)))
    · exact ⟨hk, by subst hk; omega⟩
    · exact absurd heq.symm (ne_of_lt ((mix_lt_iff hd hc).2 (Or.inl hk)))
  · rintro ⟨rfl, rfl⟩; rfl

lemma sharp_inner_lt (a : Atom) :
    ((a.k * (2 * a.height + 1) + zEncode a.m) * (3 * a.height ^ 2) + rankQ a.y0) *
      (3 * a.height ^ 2) + rankQstar ⟨a.s, a.hs⟩ < 27 * a.height ^ 6 := by
  have hk := a.k_lt_height
  have hm := a.m_lt_height
  have hy := rankQ_lt a.y0_le_height
  have hs := rankQstar_lt (s := ⟨a.s, a.hs⟩) a.s_le_height
  have hz := zEncode_le a.m
  have h2 := a.two_le_height
  set H := a.height
  have e1 : a.k * (2 * H + 1) + zEncode a.m < H * (2 * H + 1) := by
    have := Nat.mul_le_mul_right (2 * H + 1) (show a.k + 1 ≤ H by omega)
    nlinarith
  have e2 : (a.k * (2 * H + 1) + zEncode a.m) * (3 * H ^ 2) + rankQ a.y0 <
      H * (2 * H + 1) * (3 * H ^ 2) := by
    have := Nat.mul_le_mul_right (3 * H ^ 2) (Nat.succ_le_of_lt e1)
    nlinarith
  have e3 : ((a.k * (2 * H + 1) + zEncode a.m) * (3 * H ^ 2) + rankQ a.y0) * (3 * H ^ 2) +
      rankQstar ⟨a.s, a.hs⟩ < H * (2 * H + 1) * (3 * H ^ 2) * (3 * H ^ 2) := by
    have := Nat.mul_le_mul_right (3 * H ^ 2) (Nat.succ_le_of_lt e2)
    nlinarith
  have e4 : H * (2 * H + 1) * (3 * H ^ 2) * (3 * H ^ 2) ≤ 27 * H ^ 6 := by
    have : H * (2 * H + 1) ≤ H * (3 * H) := Nat.mul_le_mul_left _ (by omega)
    calc H * (2 * H + 1) * (3 * H ^ 2) * (3 * H ^ 2) ≤ H * (3 * H) * (3 * H ^ 2) * (3 * H ^ 2) := by
          gcongr
      _ = 27 * H ^ 6 := by ring
  omega

lemma shell_lt_iff {H H' i i' : ℕ} (hi : i < 27 * H ^ 6) (hi' : i' < 27 * H' ^ 6) :
    64 * H ^ 7 + i < 64 * H' ^ 7 + i' ↔ H < H' ∨ (H = H' ∧ i < i') := by
  have key : ∀ {H H' : ℕ}, H < H' → 64 * H ^ 7 + 27 * H ^ 6 ≤ 64 * H' ^ 7 := by
    intro H H' h
    have h1 : (H + 1) ^ 7 ≤ H' ^ 7 := Nat.pow_le_pow_left h 7
    have h2 : H ^ 7 + 7 * H ^ 6 ≤ (H + 1) ^ 7 := by
      have : (H + 1) ^ 7 = H ^ 7 + 7 * H ^ 6 + (21 * H ^ 5 + 35 * H ^ 4 + 35 * H ^ 3 + 21 * H ^ 2
        + 7 * H + 1) := by ring
      omega
    omega
  constructor
  · intro h
    rcases lt_trichotomy H H' with h' | h' | h'
    · exact Or.inl h'
    · subst h'; right; exact ⟨rfl, by omega⟩
    · have := key h'; omega
  · rintro (h | ⟨rfl, h⟩)
    · have := key h; omega
    · omega

/-- The order of Definition 7.6, made explicit: `sharpKey` compares atoms first by height and then
lexicographically by `(k, Z⁻¹(m), rank_Q(y₀), rank_{Q^*}(s))`. -/
theorem sharpKey_lt_iff (a b : Atom) :
    sharpKey a < sharpKey b ↔
      a.height < b.height ∨ (a.height = b.height ∧
        (a.k < b.k ∨ (a.k = b.k ∧
          (zEncode a.m < zEncode b.m ∨ (zEncode a.m = zEncode b.m ∧
            (rankQ a.y0 < rankQ b.y0 ∨ (rankQ a.y0 = rankQ b.y0 ∧
              rankQstar ⟨a.s, a.hs⟩ < rankQstar ⟨b.s, b.hs⟩))))))) := by
  unfold sharpKey
  rw [shell_lt_iff (sharp_inner_lt a) (sharp_inner_lt b)]
  apply or_congr Iff.rfl
  apply and_congr_right
  intro hH
  rw [← hH]
  have hy := rankQ_lt a.y0_le_height
  have hs := rankQstar_lt (s := ⟨a.s, a.hs⟩) a.s_le_height
  have hy' := rankQ_lt (b.y0_le_height.trans hH.ge)
  have hs' := rankQstar_lt (s := ⟨b.s, b.hs⟩) (b.s_le_height.trans hH.ge)
  have hz := zEncode_le a.m
  have hz' := zEncode_le b.m
  have hm := a.m_lt_height
  have hm' := b.m_lt_height
  rw [← hH] at hm'
  have hz1 : zEncode a.m < 2 * a.height + 1 := by omega
  have hz2 : zEncode b.m < 2 * a.height + 1 := by omega
  rw [mix_lt_iff hs hs', mix_lt_iff hy hy', mix_lt_iff hz1 hz2, mix_eq_iff hy hy',
    mix_eq_iff hz1 hz2]
  tauto

lemma sharpKey_injective : Function.Injective sharpKey := by
  intro a b h
  have h1 : ¬ sharpKey a < sharpKey b := by omega
  have h2 : ¬ sharpKey b < sharpKey a := by omega
  rw [sharpKey_lt_iff] at h1 h2
  have hH : a.height = b.height := by omega
  have hk : a.k = b.k := by
    rcases lt_trichotomy a.k b.k with h | h | h
    · exact absurd (Or.inr ⟨hH, Or.inl h⟩) h1
    · exact h
    · exact absurd (Or.inr ⟨hH.symm, Or.inl h⟩) h2
  have hz : zEncode a.m = zEncode b.m := by
    rcases lt_trichotomy (zEncode a.m) (zEncode b.m) with h | h | h
    · exact absurd (Or.inr ⟨hH, Or.inr ⟨hk, Or.inl h⟩⟩) h1
    · exact h
    · exact absurd (Or.inr ⟨hH.symm, Or.inr ⟨hk.symm, Or.inl h⟩⟩) h2
  have hy : rankQ a.y0 = rankQ b.y0 := by
    rcases lt_trichotomy (rankQ a.y0) (rankQ b.y0) with h | h | h
    · exact absurd (Or.inr ⟨hH, Or.inr ⟨hk, Or.inr ⟨hz, Or.inl h⟩⟩⟩) h1
    · exact h
    · exact absurd (Or.inr ⟨hH.symm, Or.inr ⟨hk.symm, Or.inr ⟨hz.symm, Or.inl h⟩⟩⟩) h2
  have hs : rankQstar ⟨a.s, a.hs⟩ = rankQstar ⟨b.s, b.hs⟩ := by
    rcases lt_trichotomy (rankQstar ⟨a.s, a.hs⟩) (rankQstar ⟨b.s, b.hs⟩) with h | h | h
    · exact absurd (Or.inr ⟨hH, Or.inr ⟨hk, Or.inr ⟨hz, Or.inr ⟨hy, h⟩⟩⟩⟩) h1
    · exact h
    · exact absurd (Or.inr ⟨hH.symm, Or.inr ⟨hk.symm, Or.inr ⟨hz.symm, Or.inr ⟨hy.symm, h⟩⟩⟩⟩) h2
  exact Atom.ext hk (zEncode_injective hz) (rankQ_bijective.1 hy)
    (congrArg Subtype.val (rankQstar_bijective.1 hs))

/-- **Definition 7.6**: the address `n^♯(a)` in the height enumeration of the library. -/
noncomputable def addrSharp (a : Atom) : ℕ := keyRank sharpKey a

theorem addrSharp_bijective : Function.Bijective addrSharp :=
  keyRank_bijective sharpKey_injective (Set.infinite_range_of_injective sharpKey_injective)

/-- **Definition 7.6**: the height enumeration `Γ^♯ : ℕ → 𝓛`. -/
noncomputable def GammaSharp : ℕ ≃ Atom := (Equiv.ofBijective addrSharp addrSharp_bijective).symm

/-- Definition 7.6: `Γ^♯` lists the shells by increasing height and orders each shell
lexicographically by `(k, Z⁻¹(m), rank_Q(y₀), rank_{Q^*}(s))`. -/
theorem addrSharp_lt_iff (a b : Atom) :
    addrSharp a < addrSharp b ↔
      a.height < b.height ∨ (a.height = b.height ∧
        (a.k < b.k ∨ (a.k = b.k ∧
          (zEncode a.m < zEncode b.m ∨ (zEncode a.m = zEncode b.m ∧
            (rankQ a.y0 < rankQ b.y0 ∨ (rankQ a.y0 = rankQ b.y0 ∧
              rankQstar ⟨a.s, a.hs⟩ < rankQstar ⟨b.s, b.hs⟩))))))) := by
  rw [addrSharp, addrSharp, keyRank_lt_iff sharpKey_injective, sharpKey_lt_iff]

lemma height_le_of_sharpKey_lt {a b : Atom} (h : sharpKey b < sharpKey a) :
    b.height ≤ a.height := by
  rw [sharpKey_lt_iff] at h
  omega

/-- **Theorem 7.7** (exact minimax address for the exhaustion): `Γ^♯` is a bijection, its worst
index over `𝓛_H` is exactly `|𝓛_H| - 1 ≤ 18H⁶ - 1`, and no injective addressing does better. -/
theorem addrSharp_minimax :
    Function.Bijective addrSharp ∧
    ∀ H ≥ 2,
      (atomsUpTo H).sup addrSharp = (atomsUpTo H).card - 1 ∧
      (atomsUpTo H).card - 1 ≤ 18 * H ^ 6 - 1 ∧
      ∀ A : Atom → ℕ, Function.Injective A → (atomsUpTo H).card - 1 ≤ (atomsUpTo H).sup A := by
  refine ⟨addrSharp_bijective, fun H hH => ⟨le_antisymm ?_ (sup_ge_card_sub_one
    addrSharp_bijective.1 _), Nat.sub_le_sub_right (card_atomsUpTo_le hH) 1,
    fun A hA => minimax_lower_bound A hA H⟩⟩
  apply Finset.sup_le
  intro a ha
  have hha := mem_atomsUpTo.1 ha
  have h1 := keyRank_le_card sharpKey_injective a (atomsUpTo H) (fun b hb =>
    mem_atomsUpTo.2 ((height_le_of_sharpKey_lt hb).trans hha))
  have h2 : ((atomsUpTo H).filter (fun b => sharpKey b < sharpKey a)).card < (atomsUpTo H).card := by
    apply card_lt_card
    refine ⟨filter_subset _ _, fun hsub => ?_⟩
    have := hsub ha
    simp at this
  unfold addrSharp; omega

end Dyadic.Lib
