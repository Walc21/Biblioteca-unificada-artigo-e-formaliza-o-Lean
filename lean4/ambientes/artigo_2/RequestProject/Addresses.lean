import RequestProject.Atoms

/-!
# Section 3.1–3.2 — Address length, height counting, minimax addressing

* Theorem 3.1 (cota polinomial do endereço): `n = O(H^8)`, `log₂(n+1) = O(log H)`.
* Proposition 3.3 (ordem exata do pior endereço aritmético): `M_Γ(H) = Θ(H^8)`.
* Theorem 3.4 (cota minimax relativa ao calibre).
* Definition 3.5 / Theorem 3.6 (enumeração por altura `Γ♯`, endereço minimax exato).
-/

namespace Artigo

open Finset

/-- **Theorem 3.1 (cota polinomial do endereço)**, explicit form: `Γ⁻¹(a) ≤ 2116 H^8`. -/
theorem Atom.addr_le (a : Atom) : a.addr ≤ 2116 * a.height ^ 8 := by
  set H := a.height
  have hH : 2 ≤ H := a.two_le_height
  have hk := a.k_lt_height
  have hm := a.m_lt_height
  have hy := rank_lt_three_sq (a.ht_y0_le_height)
  have hs := rank_lt_three_sq (a.ht_s_le_height)
  have hr : rankQ a.y0 < 3 * H ^ 2 := hy.1
  have ht : rankQs a.s < 3 * H ^ 2 := hs.2 a.hs
  have hz := Zinv_le_nat a.m
  have hu : cantorPair a.k (Zinv a.m) ≤ 9 * H ^ 2 := by
    refine le_trans (cantorPair_le _ _) ?_
    have : a.k + Zinv a.m + 1 ≤ 3 * H := by omega
    calc (a.k + Zinv a.m + 1) ^ 2 ≤ (3 * H) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 9 * H ^ 2 := by ring
  have hv : cantorPair (rankQ a.y0) (rankQs a.s) ≤ 36 * H ^ 4 := by
    refine le_trans (cantorPair_le _ _) ?_
    have : rankQ a.y0 + rankQs a.s + 1 ≤ 6 * H ^ 2 := by omega
    calc (rankQ a.y0 + rankQs a.s + 1) ^ 2 ≤ (6 * H ^ 2) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 36 * H ^ 4 := by ring
  unfold Atom.addr
  refine le_trans (cantorPair_le _ _) ?_
  have h1 : 1 ≤ H ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h2 : H ^ 2 ≤ H ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have : cantorPair a.k (Zinv a.m) + cantorPair (rankQ a.y0) (rankQs a.s) + 1 ≤ 46 * H ^ 4 := by
    omega
  calc _ ≤ (46 * H ^ 4) ^ 2 := Nat.pow_le_pow_left this 2
    _ = 2116 * H ^ 8 := by ring

/-- **Theorem 3.1 (cota polinomial do endereço)**: the unique address `n` of an atom of
height `H` satisfies `n = O(H^8)` and `log₂(n+1) = O(log H)`, with universal constants. -/
theorem index_bound : ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ a : Atom,
    (a.addr : ℝ) ≤ C * (a.height : ℝ) ^ 8 ∧
    Real.logb 2 ((a.addr : ℝ) + 1) ≤ C' * Real.logb 2 (a.height : ℝ) := by
  have hl0 : 0 ≤ Real.logb 2 (2117 : ℝ) := Real.logb_nonneg (by norm_num) (by norm_num)
  refine ⟨2116, Real.logb 2 2117 + 8, by norm_num, by linarith, fun a => ?_⟩
  have hle := a.addr_le
  have hH : (2 : ℝ) ≤ a.height := by exact_mod_cast a.two_le_height
  have hR : (a.addr : ℝ) ≤ 2116 * (a.height : ℝ) ^ 8 := by exact_mod_cast hle
  refine ⟨hR, ?_⟩
  have hlogH : 1 ≤ Real.logb 2 (a.height : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hH
  have hpos : (0 : ℝ) < (a.height : ℝ) ^ 8 := by positivity
  have h1 : (a.addr : ℝ) + 1 ≤ 2117 * (a.height : ℝ) ^ 8 := by
    have : (1 : ℝ) ≤ (a.height : ℝ) ^ 8 := one_le_pow₀ (by linarith)
    linarith
  calc Real.logb 2 ((a.addr : ℝ) + 1) ≤ Real.logb 2 (2117 * (a.height : ℝ) ^ 8) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    _ = Real.logb 2 2117 + 8 * Real.logb 2 (a.height : ℝ) := by
        rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]; push_cast; ring
    _ ≤ (Real.logb 2 2117 + 8) * Real.logb 2 (a.height : ℝ) := by
        have : 0 ≤ Real.logb 2 2117 := Real.logb_nonneg (by norm_num) (by norm_num)
        nlinarith

/-! ## Proposition 3.3 -/

/-- `M_Γ(H) = max_{a ∈ 𝓛_H} Γ⁻¹(a)`. -/
def MGamma (H : ℕ) : ℕ := (LH H).sup Atom.addr

lemma exists_rankQ_eq (H : ℕ) (hH : 1 ≤ H) :
    ∃ y ∈ QH H, rankQ y = (QH H).card - 1 := by
  have hpos : 0 < (QH H).card := card_pos.mpr ⟨0, zero_mem_QH hH⟩
  have : (QH H).card - 1 ∈ (QH H).image rankQ := by
    rw [rankQ_image]; exact mem_range.mpr (by omega)
  simpa using this

lemma exists_rankQs_eq (H : ℕ) (hH : 2 ≤ H) :
    ∃ s : ℚ, s ≠ 0 ∧ ht s ≤ H ∧ rankQs s = (QH H).card - 2 := by
  have hc : (QsH H).card = (QH H).card - 1 := by
    rw [QsH, card_erase_of_mem (zero_mem_QH (by omega))]
  have h1 : (1 : ℚ) ∈ QsH H := mem_QsH.mpr ⟨one_ne_zero, by simp [ht]; omega⟩
  have hpos : 0 < (QsH H).card := card_pos.mpr ⟨1, h1⟩
  have : (QsH H).card - 1 ∈ (QsShell H).image (fun r => rankQs r.1) := by
    rw [rankQs_image]; exact mem_range.mpr (by omega)
  simp only [mem_image] at this
  obtain ⟨r, hr, hrank⟩ := this
  refine ⟨r.1, r.2, mem_QsShell.mp hr, ?_⟩
  rw [hrank, hc]; omega

lemma MGamma_lower {H : ℕ} (hH : 3 ≤ H) : H ^ 8 ≤ 128 * MGamma H := by
  obtain ⟨y, hy, hry⟩ := exists_rankQ_eq H (by omega)
  obtain ⟨s, hs0, hs, hrs⟩ := exists_rankQs_eq H (by omega)
  let a : Atom := ⟨0, 0, y, s, hs0⟩
  have ha : a ∈ LH H := by
    rw [mem_LH, Atom.height_le_iff]
    exact ⟨by omega, by simp [a]; omega, by simp [a]; omega, mem_QH.mp hy, hs⟩
  have hle : a.addr ≤ MGamma H := le_sup ha
  have hq := card_QH_ge_half H
  set q := (QH H).card
  have hq5 : 5 ≤ q := by nlinarith
  set v := cantorPair (rankQ y) (rankQs s)
  have haddr : a.addr = cantorPair 0 v := by
    have h0 : cantorPair 0 (Zinv 0) = 0 := by decide
    simp only [Atom.addr, a, v]; rw [h0]
  have hv : (rankQ y + rankQs s) ^ 2 ≤ 2 * v := cantorPair_ge_sq _ _
  have hn : (0 + v) ^ 2 ≤ 2 * cantorPair 0 v := cantorPair_ge_sq _ _
  rw [hry, hrs] at hv
  have hrt : q ≤ q - 1 + (q - 2) := by omega
  have h1 : q ^ 2 ≤ 2 * v := le_trans (Nat.pow_le_pow_left hrt 2) hv
  have h2 : H ^ 4 ≤ 4 * q ^ 2 := by nlinarith
  have h3 : H ^ 4 ≤ 8 * v := by omega
  have h4 : H ^ 8 ≤ 64 * v ^ 2 := by
    have := Nat.pow_le_pow_left h3 2
    calc H ^ 8 = (H ^ 4) ^ 2 := by ring
      _ ≤ (8 * v) ^ 2 := this
      _ = 64 * v ^ 2 := by ring
  simp only [zero_add] at hn
  rw [haddr] at hle
  omega

lemma MGamma_upper (H : ℕ) : MGamma H ≤ 2116 * H ^ 8 := by
  unfold MGamma
  apply Finset.sup_le
  intro a ha
  refine le_trans a.addr_le ?_
  have := mem_LH.mp ha
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 8)

/-- **Proposition 3.3 (ordem exata do pior endereço aritmético)**: `M_Γ(H) = Θ(H^8)`, and
consequently the longest word of the arithmetic generator on `𝓛_H` has `8 log₂ H + O(1)` bits. -/
theorem MGamma_theta : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ H₀ : ℕ, ∀ H ≥ H₀,
    c * (H : ℝ) ^ 8 ≤ MGamma H ∧ (MGamma H : ℝ) ≤ C * (H : ℝ) ^ 8 := by
  refine ⟨1 / 128, 2116, by norm_num, by norm_num, 3, fun H hH => ⟨?_, ?_⟩⟩
  · have := MGamma_lower hH
    have h : ((H ^ 8 : ℕ) : ℝ) ≤ ((128 * MGamma H : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h; linarith
  · have := MGamma_upper H
    have h : ((MGamma H : ℕ) : ℝ) ≤ ((2116 * H ^ 8 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h; linarith

/-- **Proposition 3.3 (bits)**: `log₂(M_Γ(H)+1) = 8 log₂ H + O(1)`. -/
theorem MGamma_bits : ∃ C : ℝ, ∃ H₀ : ℕ, ∀ H ≥ H₀,
    |Real.logb 2 ((MGamma H : ℝ) + 1) - 8 * Real.logb 2 H| ≤ C := by
  refine ⟨Real.logb 2 2117 + 7, 3, fun H hH => ?_⟩
  have hl := MGamma_lower hH
  have hu := MGamma_upper H
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < (H : ℝ) ^ 8 := by positivity
  have hl' : (H : ℝ) ^ 8 ≤ 128 * (MGamma H : ℝ) := by
    have h : ((H ^ 8 : ℕ) : ℝ) ≤ ((128 * MGamma H : ℕ) : ℝ) := by exact_mod_cast hl
    push_cast at h; linarith
  have hu' : (MGamma H : ℝ) ≤ 2116 * (H : ℝ) ^ 8 := by
    have h : ((MGamma H : ℕ) : ℝ) ≤ ((2116 * H ^ 8 : ℕ) : ℝ) := by exact_mod_cast hu
    push_cast at h; linarith
  have hM0 : (0 : ℝ) ≤ MGamma H := by positivity
  have e8 : 8 * Real.logb 2 (H : ℝ) = Real.logb 2 ((H : ℝ) ^ 8) := by
    rw [Real.logb_pow]; push_cast; ring
  rw [e8, abs_le]
  constructor
  · -- lower: log(M+1) ≥ log(H^8/128) = log H^8 - 7
    have h1 : (H : ℝ) ^ 8 / 128 ≤ (MGamma H : ℝ) + 1 := by linarith
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_div (by positivity) (by norm_num)] at h2
    have h128 : Real.logb 2 (128 : ℝ) = 7 := by
      rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.logb_pow]; simp
    have : 0 ≤ Real.logb 2 2117 := Real.logb_nonneg (by norm_num) (by norm_num)
    linarith
  · have h1 : (MGamma H : ℝ) + 1 ≤ 2117 * (H : ℝ) ^ 8 := by
      have : (1 : ℝ) ≤ (H : ℝ) ^ 8 := one_le_pow₀ (by linarith)
      linarith
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_mul (by norm_num) (by positivity)] at h2
    linarith

/-! ## Theorem 3.4 -/

lemma card_le_sup_succ (s : Finset ℕ) : s.card ≤ s.sup id + 1 := by
  have : s ⊆ range (s.sup id + 1) := by
    intro n hn; rw [mem_range]
    have : id n ≤ s.sup id := le_sup hn
    simp at this; omega
  simpa using card_le_card this

/-- **Theorem 3.4 (pigeonhole)**: for every injective `A : 𝓛 → ℕ` and every `H ≥ 2`,
`max_{a ∈ 𝓛_H} A(a) ≥ |𝓛_H| - 1`. -/
theorem address_pigeonhole (A : Atom → ℕ) (hA : Function.Injective A) (H : ℕ) :
    (LH H).card ≤ (LH H).sup A + 1 := by
  have h1 := card_le_sup_succ ((LH H).image A)
  rw [card_image_of_injective _ hA] at h1
  have h2 : ((LH H).image A).sup id = (LH H).sup A := by
    rw [sup_image]; rfl
  omega

/-- **Theorem 3.4 (cota minimax relativa ao calibre)**: for every injective addressing
`A : 𝓛 → ℕ` and every `H ≥ H₁` there is an atom of height `≤ H` with
`A(atom) ≥ c_𝓛 H^6 - 1` and `log₂(A(atom)+1) ≥ 6 log₂ H - O(1)`. -/
theorem address_lower : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ H₁ : ℕ, 2 ≤ H₁ ∧
    ∀ A : Atom → ℕ, Function.Injective A → ∀ H ≥ H₁, ∃ a : Atom, a.height ≤ H ∧
      c * (H : ℝ) ^ 6 - 1 ≤ A a ∧ 6 * Real.logb 2 H - C ≤ Real.logb 2 ((A a : ℝ) + 1) := by
  refine ⟨1 / 8, by norm_num, 3, 2, le_refl _, fun A hA H hH => ?_⟩
  have hne : (LH H).Nonempty := by
    refine ⟨⟨0, 0, 0, 1, one_ne_zero⟩, mem_LH.mpr ?_⟩
    rw [Atom.height_le_iff]; simp [ht]; omega
  obtain ⟨a, ha, hsup⟩ := exists_mem_eq_sup (LH H) hne A
  have hpig := address_pigeonhole A hA H
  have hcard := card_LH_ge_nat hH
  refine ⟨a, mem_LH.mp ha, ?_, ?_⟩
  · have h : ((H ^ 6 : ℕ) : ℝ) ≤ ((8 * (A a + 1) : ℕ) : ℝ) := by
      have : H ^ 6 ≤ 8 * (A a + 1) := by rw [← hsup]; omega
      exact_mod_cast this
    push_cast at h; linarith
  · have h : ((H ^ 6 : ℕ) : ℝ) ≤ ((8 * (A a + 1) : ℕ) : ℝ) := by
      have : H ^ 6 ≤ 8 * (A a + 1) := by rw [← hsup]; omega
      exact_mod_cast this
    push_cast at h
    have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
    have h1 : (H : ℝ) ^ 6 / 8 ≤ (A a : ℝ) + 1 := by linarith
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_div (by positivity) (by norm_num), Real.logb_pow] at h2
    have h8 : Real.logb 2 (8 : ℝ) = 3 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow]; simp
    push_cast at h2
    linarith

/-! ## Definition 3.5 and Theorem 3.6: the height enumeration `Γ♯` -/

/-- the order key inside a shell: `(k, Z⁻¹(m), rank_Q(y₀), rank_{Q*}(s))`, compared
lexicographically (as lists of equal length). -/
def atomKey (a : Atom) : List ℕ := [a.k, Zinv a.m, rankQ a.y0, rankQs a.s]

lemma atomKey_injective : Function.Injective atomKey := by
  intro a b h
  simp only [atomKey, List.cons.injEq, and_true] at h
  obtain ⟨hk, hm, hy, hs⟩ := h
  exact Atom.ext' hk (Zinv_injective hm) (rankQ_injective hy)
    (congrArg Subtype.val (@rankQs_injective ⟨a.s, a.hs⟩ ⟨b.s, b.hs⟩ hs))

/-- **Definition 3.5**: the address `n♯(a)` of an atom in the height enumeration. -/
def nSharp (a : Atom) : ℕ := shellRank LH Atom.height atomKey a

lemma LH_unbounded (n : ℕ) : ∃ H, n < (LH H).card := by
  refine ⟨n + 2, ?_⟩
  have h1 := card_LH_ge_nat (H := n + 2) (by omega)
  have h2 : 2 ^ 5 ≤ (n + 2) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h3 : (n + 2) ^ 6 = (n + 2) ^ 5 * (n + 2) := by ring
  nlinarith

theorem nSharp_injective : Function.Injective nSharp :=
  shellRank_injective LH Atom.height atomKey (fun _ _ => mem_LH) atomKey_injective

theorem nSharp_surjective : Function.Surjective nSharp :=
  shellRank_surjective LH Atom.height atomKey (fun _ _ => mem_LH) atomKey_injective LH_unbounded

lemma nSharp_image (H : ℕ) : (LH H).image nSharp = range (LH H).card :=
  shellRank_image LH Atom.height atomKey (fun _ _ => mem_LH) atomKey_injective H

lemma nSharp_lt {a : Atom} {H : ℕ} (h : a.height ≤ H) : nSharp a < (LH H).card :=
  shellRank_lt LH Atom.height atomKey (fun _ _ => mem_LH) h

/-- smallest `H` whose shell contains position `n` -/
def shellIndex (n : ℕ) : ℕ := Nat.find (LH_unbounded n)

lemma exists_unique_nSharp (n : ℕ) :
    ∃! a, a ∈ LH (shellIndex n) ∧ nSharp a = n := by
  have hmem : n ∈ (LH (shellIndex n)).image nSharp := by
    rw [nSharp_image]; exact mem_range.mpr (Nat.find_spec (LH_unbounded n))
  simp only [mem_image] at hmem
  obtain ⟨a, ha, hn⟩ := hmem
  exact ⟨a, ⟨ha, hn⟩, fun b hb => nSharp_injective (hb.2.trans hn.symm)⟩

/-- **Definition 3.5**: the (computable) bijection `Γ♯ : ℕ → 𝓛`. It finds the first shell
containing position `n` and selects the unique atom of that shell with rank `n`. -/
def GammaSharp (n : ℕ) : Atom :=
  Finset.choose (fun a => nSharp a = n) (LH (shellIndex n)) (exists_unique_nSharp n)

lemma nSharp_GammaSharp (n : ℕ) : nSharp (GammaSharp n) = n :=
  (Finset.choose_spec (fun a => nSharp a = n) (LH (shellIndex n)) (exists_unique_nSharp n)).2

lemma GammaSharp_nSharp (a : Atom) : GammaSharp (nSharp a) = a :=
  nSharp_injective (nSharp_GammaSharp _)

/-- **Theorem 3.6 (endereço minimax exato para a exaustão)**: `Γ♯` is a bijection
`ℕ → 𝓛`, computable in both directions (`GammaSharp` and `nSharp` are computable Lean
definitions, mutually inverse); for every `H ≥ 2`,
`max_{a ∈ 𝓛_H} n♯(a) = |𝓛_H| - 1 ≤ 18 H^6 - 1`, and every injective addressing `A` satisfies
`max_{a ∈ 𝓛_H} A(a) ≥ |𝓛_H| - 1`. -/
theorem sharp_optimal :
    Function.Bijective GammaSharp ∧
    Function.LeftInverse GammaSharp nSharp ∧ Function.RightInverse GammaSharp nSharp ∧
    (∀ H, 2 ≤ H → (LH H).sup nSharp = (LH H).card - 1 ∧ (LH H).card - 1 ≤ 18 * H ^ 6 - 1) ∧
    (∀ A : Atom → ℕ, Function.Injective A → ∀ H, 2 ≤ H → (LH H).card - 1 ≤ (LH H).sup A) := by
  refine ⟨⟨fun n n' h => ?_, fun a => ⟨nSharp a, GammaSharp_nSharp a⟩⟩, GammaSharp_nSharp,
    nSharp_GammaSharp, fun H hH => ⟨?_, ?_⟩, fun A hA H _ => ?_⟩
  · rw [← nSharp_GammaSharp n, ← nSharp_GammaSharp n', h]
  · have : (LH H).sup nSharp = ((LH H).image nSharp).sup id := by rw [sup_image]; rfl
    rw [this, nSharp_image]
    have hpos : 0 < (LH H).card := by
      have := card_LH_ge_nat hH
      have : 0 < H ^ 6 := by positivity
      omega
    apply le_antisymm
    · apply Finset.sup_le; intro n hn; simp at hn; simp; omega
    · have : (LH H).card - 1 ∈ range (LH H).card := mem_range.mpr (by omega)
      exact le_sup (f := id) this
  · have := card_LH_le hH; omega
  · have := address_pigeonhole A hA H; omega

/-- **Theorem 3.6 (consequence)**: the worst index of `Γ♯` on `𝓛_H` is `Θ(H^6)`. -/
theorem sharp_worst_theta : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ H : ℕ, 2 ≤ H →
    c * (H : ℝ) ^ 6 ≤ (((LH H).sup nSharp : ℕ) : ℝ) + 1 ∧
      (((LH H).sup nSharp : ℕ) : ℝ) + 1 ≤ C * (H : ℝ) ^ 6 := by
  obtain ⟨c, C, hc, hC, h⟩ := card_LH_theta
  refine ⟨c, C, hc, hC, fun H hH => ?_⟩
  have e := (sharp_optimal.2.2.2.1 H hH).1
  have hpos : 0 < (LH H).card := by
    have := card_LH_ge_nat hH
    have : 0 < H ^ 6 := by positivity
    omega
  have : (((LH H).sup nSharp : ℕ) : ℝ) + 1 = (LH H).card := by
    rw [e]; rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [this]; exact h H hH

end Artigo
