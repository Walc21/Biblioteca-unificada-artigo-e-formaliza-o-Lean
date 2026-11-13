import RequestProject.Indexing

/-!
# Atoms, the library `𝓛`, addresses (Sections 2–3)

* Definition 2.2 (átomos): an atom is a quadruple `(k, m, y₀, s) ∈ ℕ × ℤ × ℚ × ℚ*`
  representing `ℓ(x) = y₀ + s (x - x_{k,m})` on `J_{k,m} = [m 2^{-k}, (m+1) 2^{-k}]`.
* Its address `Γ⁻¹(ℓ) = π(π(k, Z⁻¹ m), π(Q⁻¹ y₀, (Q*)⁻¹ s))`.
* The height gauge `H = max{2, k+1, |m|+1, ht y₀, ht s}` and the exhaustion `𝓛_H`.
-/

namespace Artigo

open Finset

/-- An atom of the library: the segment `ℓ(x) = y₀ + s (x - x_{k,m})` on `J_{k,m}`. -/
structure Atom where
  k : ℕ
  m : ℤ
  y0 : ℚ
  s : ℚ
  hs : s ≠ 0
deriving DecidableEq

namespace Atom

variable (a : Atom)

/-- left endpoint `m 2^{-k}` of the support -/
def left : ℚ := a.m / 2 ^ a.k
/-- right endpoint `(m+1) 2^{-k}` of the support -/
def right : ℚ := (a.m + 1) / 2 ^ a.k
/-- center `x_{k,m} = (m + 1/2) 2^{-k}` -/
def x0 : ℚ := (a.m + 1 / 2) / 2 ^ a.k
/-- the affine function `y₀ + s (x - x₀)` (rational version) -/
def evalQ (x : ℚ) : ℚ := a.y0 + a.s * (x - a.x0)
/-- the affine function `y₀ + s (x - x₀)` (real version) -/
def eval (x : ℝ) : ℝ := (a.y0 : ℝ) + (a.s : ℝ) * (x - (a.x0 : ℝ))
/-- value at the left endpoint -/
def lval : ℚ := a.evalQ a.left
/-- value at the right endpoint -/
def rval : ℚ := a.evalQ a.right

/-- the height gauge `max{2, k+1, |m|+1, ht y₀, ht s}` (eq. (3.1)) -/
def height : ℕ := max (max (max (max 2 (a.k + 1)) (a.m.natAbs + 1)) (ht a.y0)) (ht a.s)

/-- The arithmetic address `Γ⁻¹(ℓ) = π(π(k, Z⁻¹ m), π(Q⁻¹ y₀, (Q*)⁻¹ s))`. -/
def addr : ℕ := cantorPair (cantorPair a.k (Zinv a.m)) (cantorPair (rankQ a.y0) (rankQs a.s))

/-- the interface `(a, b, [c, d])`: intercept, slope and image of the support. -/
def interface : ℚ × ℚ × ℚ × ℚ :=
  (a.y0 - a.s * a.x0, a.s, min a.lval a.rval, max a.lval a.rval)

lemma eval_eq (x : ℚ) : a.eval x = a.evalQ x := by
  simp [eval, evalQ]

lemma two_le_height : 2 ≤ a.height := by unfold height; omega
lemma k_lt_height : a.k + 1 ≤ a.height := by unfold height; omega
lemma m_lt_height : a.m.natAbs + 1 ≤ a.height := by unfold height; omega
lemma ht_y0_le_height : ht a.y0 ≤ a.height := by unfold height; omega
lemma ht_s_le_height : ht a.s ≤ a.height := by unfold height; omega

lemma height_le_iff {H : ℕ} : a.height ≤ H ↔
    2 ≤ H ∧ a.k + 1 ≤ H ∧ a.m.natAbs + 1 ≤ H ∧ ht a.y0 ≤ H ∧ ht a.s ≤ H := by
  unfold height; omega

lemma lval_eq : a.lval = a.y0 - a.s / 2 ^ (a.k + 1) := by
  simp only [lval, evalQ, left, x0, pow_succ]; field_simp; ring

lemma rval_eq : a.rval = a.y0 + a.s / 2 ^ (a.k + 1) := by
  simp only [rval, evalQ, right, x0, pow_succ]; field_simp; ring

lemma lval_ne_rval : a.lval ≠ a.rval := by
  rw [lval_eq, rval_eq]; intro h
  have : a.s / 2 ^ (a.k + 1) = 0 := by linarith
  rcases div_eq_zero_iff.mp this with h | h
  · exact a.hs h
  · exact absurd h (by positivity)

lemma y0_eq : a.y0 = (a.lval + a.rval) / 2 := by
  rw [lval_eq, rval_eq]; ring

lemma s_eq : a.s = 2 ^ a.k * (a.rval - a.lval) := by
  rw [lval_eq, rval_eq, pow_succ]; field_simp; ring

end Atom

/-- An atom is determined by its parameters. -/
lemma Atom.ext' {a b : Atom} (hk : a.k = b.k) (hm : a.m = b.m) (hy : a.y0 = b.y0) (hs : a.s = b.s) :
    a = b := by
  cases a; cases b; simp_all

/-- the atom determined by cell and endpoint values (requires `u ≠ v`). -/
def Atom.ofEndpoints (k : ℕ) (m : ℤ) (u v : ℚ) (h : u ≠ v) : Atom :=
  ⟨k, m, (u + v) / 2, 2 ^ k * (v - u), mul_ne_zero (by positivity) (sub_ne_zero.mpr h.symm)⟩

lemma Atom.ofEndpoints_lval (k : ℕ) (m : ℤ) (u v : ℚ) (h : u ≠ v) :
    (Atom.ofEndpoints k m u v h).lval = u := by
  rw [Atom.lval_eq]; simp only [Atom.ofEndpoints, pow_succ]; field_simp; ring

lemma Atom.ofEndpoints_rval (k : ℕ) (m : ℤ) (u v : ℚ) (h : u ≠ v) :
    (Atom.ofEndpoints k m u v h).rval = v := by
  rw [Atom.rval_eq]; simp only [Atom.ofEndpoints, pow_succ]; field_simp; ring

lemma Atom.eq_ofEndpoints (a : Atom) :
    a = Atom.ofEndpoints a.k a.m a.lval a.rval a.lval_ne_rval := by
  refine Atom.ext' rfl rfl ?_ ?_
  · simp [Atom.ofEndpoints, a.y0_eq]
  · simp [Atom.ofEndpoints, a.s_eq]

/-! ## Definition 2.2: the address is unique (cell recovery) -/

/-- **Definition 2.2 (cell recovery)**: the interface `(a, b, [c,d])` determines the atom,
so the address is unique. -/
theorem Atom.interface_injective : Function.Injective Atom.interface := by
  intro a b h
  simp only [Atom.interface, Prod.mk.injEq] at h
  obtain ⟨hint, hs, hmin, hmax⟩ := h
  -- the line `x ↦ A + s x`
  have hlin : ∀ (c : Atom) (x : ℚ), c.evalQ x = (c.y0 - c.s * c.x0) + c.s * x := by
    intro c x; simp [Atom.evalQ]; ring
  -- recover endpoints
  have hl : a.left = b.left ∧ a.right = b.right := by
    have hla : a.lval = (a.y0 - a.s * a.x0) + a.s * a.left := hlin a _
    have hra : a.rval = (a.y0 - a.s * a.x0) + a.s * a.right := hlin a _
    have hlb : b.lval = (b.y0 - b.s * b.x0) + b.s * b.left := hlin b _
    have hrb : b.rval = (b.y0 - b.s * b.x0) + b.s * b.right := hlin b _
    rw [hint, hs] at hla hra
    have hsb := b.hs
    rcases lt_or_gt_of_ne hsb with hneg | hpos
    · -- decreasing: lval > rval
      have hlr : ∀ c : Atom, c.s < 0 → c.rval < c.lval := by
        intro c hc; rw [c.lval_eq, c.rval_eq]
        have : c.s / 2 ^ (c.k + 1) < 0 := div_neg_of_neg_of_pos hc (by positivity)
        linarith
      have ha' := hlr a (hs ▸ hneg)
      have hb' := hlr b hneg
      rw [min_eq_right ha'.le, min_eq_right hb'.le] at hmin
      rw [max_eq_left ha'.le, max_eq_left hb'.le] at hmax
      constructor
      · have : b.s * a.left = b.s * b.left := by linarith
        exact mul_left_cancel₀ hsb this
      · have : b.s * a.right = b.s * b.right := by linarith
        exact mul_left_cancel₀ hsb this
    · have hlr : ∀ c : Atom, 0 < c.s → c.lval < c.rval := by
        intro c hc; rw [c.lval_eq, c.rval_eq]
        have : 0 < c.s / 2 ^ (c.k + 1) := div_pos hc (by positivity)
        linarith
      have ha' := hlr a (hs ▸ hpos)
      have hb' := hlr b hpos
      rw [min_eq_left ha'.le, min_eq_left hb'.le] at hmin
      rw [max_eq_right ha'.le, max_eq_right hb'.le] at hmax
      constructor
      · have : b.s * a.left = b.s * b.left := by linarith
        exact mul_left_cancel₀ hsb this
      · have : b.s * a.right = b.s * b.right := by linarith
        exact mul_left_cancel₀ hsb this
  obtain ⟨hL, hR⟩ := hl
  -- the length determines `k`
  have hlen : (1 : ℚ) / 2 ^ a.k = 1 / 2 ^ b.k := by
    have e1 : a.right - a.left = 1 / 2 ^ a.k := by simp only [Atom.right, Atom.left]; field_simp; ring
    have e2 : b.right - b.left = 1 / 2 ^ b.k := by simp only [Atom.right, Atom.left]; field_simp; ring
    rw [← e1, ← e2, hL, hR]
  have hk : a.k = b.k := by
    have : (2 : ℚ) ^ a.k = 2 ^ b.k := by
      have := hlen; field_simp at this; linarith
    exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this)
  have hm : a.m = b.m := by
    have : (a.m : ℚ) / 2 ^ a.k = b.m / 2 ^ b.k := hL
    rw [hk] at this
    have := (div_left_inj' (by positivity : (2 : ℚ) ^ b.k ≠ 0)).mp this
    exact_mod_cast this
  have hx : a.x0 = b.x0 := by simp only [Atom.x0, hk, hm]
  have hy : a.y0 = b.y0 := by rw [hx, hs] at hint; linarith
  exact Atom.ext' hk hm hy hs

/-- **Definition 2.2**: the address `Γ⁻¹` is injective. -/
theorem Atom.addr_injective : Function.Injective Atom.addr := by
  intro a b h
  have h1 := @cantorPair_injective (cantorPair a.k (Zinv a.m), cantorPair (rankQ a.y0) (rankQs a.s))
    (cantorPair b.k (Zinv b.m), cantorPair (rankQ b.y0) (rankQs b.s)) h
  simp only [Prod.mk.injEq] at h1
  have h2 := @cantorPair_injective (a.k, Zinv a.m) (b.k, Zinv b.m) h1.1
  have h3 := @cantorPair_injective (rankQ a.y0, rankQs a.s) (rankQ b.y0, rankQs b.s) h1.2
  simp only [Prod.mk.injEq] at h2 h3
  have hm := Zinv_injective h2.2
  have hy := rankQ_injective h3.1
  have hs : a.s = b.s := by
    have := @rankQs_injective ⟨a.s, a.hs⟩ ⟨b.s, b.hs⟩ h3.2
    exact congrArg Subtype.val this
  exact Atom.ext' h2.1 hm hy hs

/-! ## The exhaustion `𝓛_H` -/

/-- `𝓛_H`: the (finite, computable) set of atoms of height at most `H`. -/
def LH (H : ℕ) : Finset Atom :=
  ((((range H) ×ˢ (Icc (-(H : ℤ) + 1) ((H : ℤ) - 1))) ×ˢ ((QH H) ×ˢ (QsH H).attach)).image
    (fun x => (⟨x.1.1, x.1.2, x.2.1, x.2.2.1, (mem_QsH.mp x.2.2.2).1⟩ : Atom))).filter
    (fun a => a.height ≤ H)

lemma mem_LH {H : ℕ} {a : Atom} : a ∈ LH H ↔ a.height ≤ H := by
  unfold LH
  simp only [mem_filter, mem_image, mem_product, mem_range, mem_Icc, mem_attach, and_true,
    Prod.exists, Subtype.exists]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    have := (Atom.height_le_iff a).mp h
    refine ⟨⟨a.k, a.m, a.y0, a.s, mem_QsH.mpr ⟨a.hs, this.2.2.2.2⟩, ⟨⟨by omega, by omega, by omega⟩,
      mem_QH.mpr this.2.2.2.1⟩, rfl⟩, h⟩

lemma LH_mono {H H' : ℕ} (h : H ≤ H') : LH H ⊆ LH H' := by
  intro a; simp only [mem_LH]; omega

/-- exact cardinality: `|𝓛_H| = H (2H-1) |𝒬_H| (|𝒬_H| - 1)` for `H ≥ 2`. -/
lemma card_LH {H : ℕ} (hH : 2 ≤ H) :
    (LH H).card = H * (2 * H - 1) * ((QH H).card * ((QH H).card - 1)) := by
  unfold LH
  rw [filter_true_of_mem]
  · rw [card_image_of_injective]
    · rw [card_product, card_product, card_product, card_attach, card_range, Int.card_Icc]
      have h1 : ((H : ℤ) - 1 + 1 - (-(H : ℤ) + 1)).toNat = 2 * H - 1 := by omega
      have h2 : (QsH H).card = (QH H).card - 1 := by
        rw [QsH, card_erase_of_mem (zero_mem_QH (by omega))]
      rw [h1, h2]
    · rintro ⟨⟨k, m⟩, y, s, hs⟩ ⟨⟨k', m'⟩, y', s', hs'⟩ h
      simp only [Atom.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
  · intro a ha
    simp only [mem_image, mem_product, mem_range, mem_Icc, mem_attach, and_true, Prod.exists,
      Subtype.exists] at ha
    obtain ⟨k, m, y, s, hs, ⟨⟨hk, hm1, hm2⟩, hy⟩, rfl⟩ := ha
    rw [Atom.height_le_iff]
    simp only
    refine ⟨hH, by omega, by omega, mem_QH.mp hy, (mem_QsH.mp hs).2⟩

/-- **Lemma 3.2 (upper bound)**: `|𝓛_H| ≤ 18 H^6` for `H ≥ 2`. -/
theorem card_LH_le {H : ℕ} (hH : 2 ≤ H) : (LH H).card ≤ 18 * H ^ 6 := by
  rw [card_LH hH]
  have hq := card_QH_le H
  have h1 : (QH H).card - 1 ≤ 3 * H ^ 2 := by omega
  have h2 : 2 * H - 1 ≤ 2 * H := by omega
  calc H * (2 * H - 1) * ((QH H).card * ((QH H).card - 1))
      ≤ H * (2 * H) * ((3 * H ^ 2) * (3 * H ^ 2)) := by gcongr
    _ = 18 * H ^ 6 := by ring

lemma card_LH_ge_nat {H : ℕ} (hH : 2 ≤ H) : H ^ 6 ≤ 8 * (LH H).card := by
  rw [card_LH hH]
  have hq := card_QH_ge_half H
  set q := (QH H).card
  have hq2 : 2 ≤ q := by nlinarith
  have h1 : q ≤ 2 * (q - 1) := by omega
  have h2 : H ≤ 2 * H - 1 := by omega
  have h3 : H ^ 4 ≤ 4 * (q * q) := by nlinarith
  have h4 : H * H * (q * q) ≤ 2 * (H * (2 * H - 1) * (q * (q - 1))) := by
    have : H * H ≤ H * (2 * H - 1) := Nat.mul_le_mul_left _ h2
    have : q * q ≤ 2 * (q * (q - 1)) := by nlinarith
    nlinarith
  nlinarith

/-- **Lemma 3.2 (lower bound)**: there are `c_𝓛 > 0` and `H₁ ≥ 2` with `|𝓛_H| ≥ c_𝓛 H^6`
for all `H ≥ H₁`. (One can take `c_𝓛 = 1/8`, `H₁ = 2`.) -/
theorem card_LH_ge : ∃ c : ℝ, 0 < c ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁, c * (H : ℝ) ^ 6 ≤ (LH H).card := by
  refine ⟨1 / 8, by norm_num, 2, le_refl _, fun H hH => ?_⟩
  have := card_LH_ge_nat hH
  have h : ((H ^ 6 : ℕ) : ℝ) ≤ ((8 * (LH H).card : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h
  linarith

/-- **Lemma 3.2**: `|𝓛_H| = Θ(H^6)`. -/
theorem card_LH_theta : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ H : ℕ, 2 ≤ H →
    c * (H : ℝ) ^ 6 ≤ (LH H).card ∧ ((LH H).card : ℝ) ≤ C * (H : ℝ) ^ 6 := by
  refine ⟨1 / 8, 18, by norm_num, by norm_num, fun H hH => ⟨?_, ?_⟩⟩
  · have := card_LH_ge_nat hH
    have h : ((H ^ 6 : ℕ) : ℝ) ≤ ((8 * (LH H).card : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h; linarith
  · have := card_LH_le hH
    have h : (((LH H).card : ℕ) : ℝ) ≤ ((18 * H ^ 6 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h; linarith

/-- **Dependence of the exponent on the gauge**: with decoupled budgets,
`|𝓛_{K₀,M₀,Y,S}| = (K₀+1)(2M₀+1)|𝒬_Y|(|𝒬_S|-1)`. -/
def LDecoupled (K₀ M₀ Y S : ℕ) : Finset Atom :=
  (((range (K₀ + 1)) ×ˢ (Icc (-(M₀ : ℤ)) M₀)) ×ˢ ((QH Y) ×ˢ (QsH S).attach)).image
    (fun x => (⟨x.1.1, x.1.2, x.2.1, x.2.2.1, (mem_QsH.mp x.2.2.2).1⟩ : Atom))

lemma mem_LDecoupled {K₀ M₀ Y S : ℕ} {a : Atom} :
    a ∈ LDecoupled K₀ M₀ Y S ↔ a.k ≤ K₀ ∧ a.m.natAbs ≤ M₀ ∧ ht a.y0 ≤ Y ∧ ht a.s ≤ S := by
  unfold LDecoupled
  simp only [mem_image, mem_product, mem_range, mem_Icc, mem_attach, and_true, Prod.exists,
    Subtype.exists]
  constructor
  · rintro ⟨k, m, y, s, hs, ⟨⟨hk, hm1, hm2⟩, hy⟩, rfl⟩
    exact ⟨by dsimp only; omega, by dsimp only; omega, mem_QH.mp hy, (mem_QsH.mp hs).2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨a.k, a.m, a.y0, a.s, mem_QsH.mpr ⟨a.hs, h4⟩, ⟨⟨by omega, by omega, by omega⟩,
      mem_QH.mpr h3⟩, rfl⟩

theorem card_LDecoupled (K₀ M₀ Y S : ℕ) (hS : 1 ≤ S) :
    (LDecoupled K₀ M₀ Y S).card = (K₀ + 1) * (2 * M₀ + 1) * (QH Y).card * ((QH S).card - 1) := by
  unfold LDecoupled
  rw [card_image_of_injective]
  · rw [card_product, card_product, card_product, card_attach, card_range, Int.card_Icc]
    have h1 : ((M₀ : ℤ) + 1 - -(M₀ : ℤ)).toNat = 2 * M₀ + 1 := by omega
    have h2 : (QsH S).card = (QH S).card - 1 := by
      rw [QsH, card_erase_of_mem (zero_mem_QH hS)]
    rw [h1, h2]; ring
  · rintro ⟨⟨k, m⟩, y, s, hs⟩ ⟨⟨k', m'⟩, y', s', hs'⟩ h
    simp only [Atom.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl

end Artigo
