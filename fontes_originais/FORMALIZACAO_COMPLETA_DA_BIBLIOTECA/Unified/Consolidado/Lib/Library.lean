module
public import Unified.Consolidado.Lib.Indexing
@[expose] public section

/-!
# Section 3: dyadic cells, atoms and the generator `Γ`

An atom is described by its parameters `(k, m, y₀, s) ∈ ℕ × ℤ × ℚ × ℚ^*`: the dyadic cell
`J_{k,m} = [m 2^{-k}, (m+1) 2^{-k}]`, the anchored value `y₀` at the centre
`x₀ = (2m+1)/2^{k+1}`, and the nonzero slope `s`.  The arithmetic generator
`Γ : ℕ → ℝ × ℝ × Set ℝ` sends an address `n` to the global triple `(a_n, b_n, [c_n, d_n])`.
-/

open Finset

namespace Dyadic.Lib

/-- The parameters `(k, m, y₀, s)` of an atom (Definition 3.3 / Theorem 3.6). -/
@[ext]
structure Atom where
  k : ℕ
  m : ℤ
  y0 : ℚ
  s : ℚ
  hs : s ≠ 0
deriving DecidableEq

instance : Infinite Atom :=
  Infinite.of_injective (fun n : ℕ => (⟨n, 0, 0, 1, one_ne_zero⟩ : Atom))
    (fun a b h => by simpa using congrArg Atom.k h)

namespace Atom

variable (a : Atom)

/-- Left endpoint `m 2^{-k}` of the cell. -/
def left : ℚ := a.m / 2 ^ a.k
/-- Right endpoint `(m+1) 2^{-k}` of the cell. -/
def right : ℚ := (a.m + 1) / 2 ^ a.k
/-- Centre `x₀(k,m) = (2m+1)/2^{k+1}` (eq. (10)). -/
def center : ℚ := (2 * a.m + 1) / 2 ^ (a.k + 1)
/-- The closed cell `J_{k,m}` (eq. (09)). -/
def cell : Set ℝ := Set.Icc (a.left : ℝ) a.right
/-- The anchored line `ℓ(x) = y₀ + s (x - x₀)` (eq. (12)). -/
def line (x : ℝ) : ℝ := a.y0 + a.s * (x - a.center)
/-- The global intercept `a = y₀ - s x₀` (eq. (15)). -/
def intercept : ℚ := a.y0 - a.s * a.center

/-- The height of an atom, eq. (46): `max{2, k+1, |m|+1, ht(y₀), ht(s)}`. -/
def height : ℕ := max (max 2 (a.k + 1)) (max (a.m.natAbs + 1) (max (ratHeight a.y0) (ratHeight a.s)))

lemma line_eq (x : ℝ) : a.line x = a.intercept + a.s * x := by
  simp only [line, intercept]; push_cast; ring

lemma right_sub_left : a.right - a.left = 1 / 2 ^ a.k := by
  simp only [right, left]; field_simp; ring

lemma left_lt_right : a.left < a.right := by
  have := a.right_sub_left
  have : (0 : ℚ) < 1 / 2 ^ a.k := by positivity
  linarith

lemma center_eq : a.center = (a.left + a.right) / 2 := by
  simp only [center, left, right]; rw [pow_succ]; field_simp; ring

lemma two_le_height : 2 ≤ a.height := by unfold height; omega
lemma k_lt_height : a.k + 1 ≤ a.height := by unfold height; omega
lemma m_lt_height : a.m.natAbs + 1 ≤ a.height := by unfold height; omega
lemma y0_le_height : ratHeight a.y0 ≤ a.height := by unfold height; omega
lemma s_le_height : ratHeight a.s ≤ a.height := by unfold height; omega

lemma height_le_iff {H : ℕ} : a.height ≤ H ↔
    2 ≤ H ∧ a.k + 1 ≤ H ∧ a.m.natAbs + 1 ≤ H ∧ ratHeight a.y0 ≤ H ∧ ratHeight a.s ≤ H := by
  unfold height; omega

end Atom

/-! ### Addresses -/

/-- The address `n = π(π(k, Z⁻¹ m), π(rank_Q y₀, rank_{Q^*} s))` of an atom (inverse of eqs.
(13)–(14)). -/
noncomputable def encode (a : Atom) : ℕ :=
  cantorPair (cantorPair a.k (zEncode a.m)) (cantorPair (rankQ a.y0) (rankQstar ⟨a.s, a.hs⟩))

/-- Lemma 3.2 together with Lemmas 2.1, 2.2, 2.4: the address map is a bijection. -/
theorem encode_bijective : Function.Bijective encode := by
  constructor
  · intro a b h
    unfold encode at h
    obtain ⟨h1, h2⟩ := cantorPair_injective h
    obtain ⟨hk, hm⟩ := cantorPair_injective h1
    obtain ⟨hy, hs⟩ := cantorPair_injective h2
    have hm' := zEncode_injective hm
    have hy' := rankQ_bijective.1 hy
    have hs' := congrArg Subtype.val (rankQstar_bijective.1 hs)
    ext <;> simp_all
  · intro n
    obtain ⟨⟨u, v⟩, huv⟩ := cantorPair_bijective.2 n
    obtain ⟨⟨k, μ⟩, hkμ⟩ := cantorPair_bijective.2 u
    obtain ⟨⟨r, t⟩, hrt⟩ := cantorPair_bijective.2 v
    obtain ⟨y, hy⟩ := rankQ_bijective.2 r
    obtain ⟨s, hs⟩ := rankQstar_bijective.2 t
    refine ⟨⟨k, zDecode μ, y, s.1, s.2⟩, ?_⟩
    simp only at huv hkμ hrt
    simp only [encode, zEncode_zDecode, hy, hs, hkμ, hrt, huv]

/-- The decoding `n ↦ (k, m, y₀, s)` (eqs. (13)–(14)). -/
noncomputable def decode : ℕ ≃ Atom := (Equiv.ofBijective encode encode_bijective).symm

@[simp] lemma encode_decode (n : ℕ) : encode (decode n) = n :=
  (Equiv.ofBijective encode encode_bijective).apply_symm_apply n

@[simp] lemma decode_encode (a : Atom) : decode (encode a) = a :=
  (Equiv.ofBijective encode encode_bijective).symm_apply_apply a

/-! ### The global interface `Γ` -/

/-- The global triple `(a, b, [c, d])` of an atom (eqs. (15)–(17)). -/
noncomputable def Atom.toTriple (a : Atom) : ℝ × ℝ × Set ℝ :=
  (a.intercept, a.s, Set.Icc (min (a.line a.left) (a.line a.right))
    (max (a.line a.left) (a.line a.right)))

/-- The generator `Γ : ℕ → ℝ × (ℝ ∖ {0}) × 𝓘` (eq. (17)). -/
noncomputable def Gamma (n : ℕ) : ℝ × ℝ × Set ℝ := (decode n).toTriple

/-- The library `𝓛 = Γ(ℕ)`. -/
def Library : Set (ℝ × ℝ × Set ℝ) := Set.range Gamma

/-- The spatial preimage `I_n^x` of eq. (18). -/
noncomputable def spatialPreimage (t : ℝ × ℝ × Set ℝ) (c d : ℝ) : Set ℝ :=
  Set.Icc (min ((c - t.1) / t.2.1) ((d - t.1) / t.2.1)) (max ((c - t.1) / t.2.1) ((d - t.1) / t.2.1))

/-- Lemma 3.4 (exact spatial validity): the preimage of `[c_n, d_n]` by `ℓ_n` is the cell. -/
theorem Atom.preimage_eq_cell (a : Atom) :
    (fun x => a.line x) ⁻¹' (a.toTriple.2.2) = a.cell := by
  have hs : (a.s : ℝ) ≠ 0 := by exact_mod_cast a.hs
  have hlr : (a.left : ℝ) < a.right := by exact_mod_cast a.left_lt_right
  ext x
  simp only [Set.mem_preimage, Atom.toTriple, Atom.cell, Set.mem_Icc, Atom.line_eq]
  rcases lt_or_gt_of_ne hs with h | h
  · have e1 : a.intercept + (a.s : ℝ) * a.right ≤ a.intercept + a.s * a.left := by nlinarith
    rw [min_eq_right e1, max_eq_left e1]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · have e1 : a.intercept + (a.s : ℝ) * a.left ≤ a.intercept + a.s * a.right := by nlinarith
    rw [min_eq_left e1, max_eq_right e1]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith
    · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- The explicit quotient formula (18) recovers the cell. -/
theorem Atom.spatialPreimage_eq_cell (a : Atom) :
    spatialPreimage a.toTriple (min (a.line a.left) (a.line a.right))
      (max (a.line a.left) (a.line a.right)) = a.cell := by
  have hs : (a.s : ℝ) ≠ 0 := by exact_mod_cast a.hs
  have hlr : (a.left : ℝ) < a.right := by exact_mod_cast a.left_lt_right
  have hq : ∀ x : ℝ, (a.line x - a.intercept) / a.s = x := by
    intro x; rw [Atom.line_eq]; field_simp; ring
  simp only [spatialPreimage, Atom.toTriple, Atom.cell]
  rcases le_total (a.line a.left) (a.line a.right) with h | h
  · rw [min_eq_left h, max_eq_right h, hq, hq, min_eq_left hlr.le, max_eq_right hlr.le]
  · rw [min_eq_right h, max_eq_left h, hq, hq, min_eq_right hlr.le, max_eq_left hlr.le]

lemma Atom.k_eq_of_width {a b : Atom} (h : (a.right : ℝ) - a.left = b.right - b.left) :
    a.k = b.k := by
  have ha := a.right_sub_left
  have hb := b.right_sub_left
  have h' : (1 : ℚ) / 2 ^ a.k = 1 / 2 ^ b.k := by
    rw [← ha, ← hb]; exact_mod_cast h
  have : (2 : ℚ) ^ a.k = 2 ^ b.k := by
    have := congrArg (fun x : ℚ => 1 / x) h'
    simpa using this
  exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this)

/-- Theorem 3.5 (uniqueness of the address), atom form: the global triple determines the atom. -/
theorem Atom.toTriple_injective : Function.Injective Atom.toTriple := by
  intro a b h
  simp only [Atom.toTriple, Prod.mk.injEq] at h
  obtain ⟨hi, hs, hI⟩ := h
  have hs' : a.s = b.s := by exact_mod_cast hs
  have hi' : a.intercept = b.intercept := by exact_mod_cast hi
  have hline : ∀ x, a.line x = b.line x := by
    intro x; rw [Atom.line_eq, Atom.line_eq, hi, hs]
  have hcell : a.cell = b.cell := by
    rw [← a.preimage_eq_cell, ← b.preimage_eq_cell]
    simp only [Atom.toTriple]
    rw [hI]
    ext x; simp [hline]
  have hla : (a.left : ℝ) < a.right := by exact_mod_cast a.left_lt_right
  obtain ⟨hL, hR⟩ := (Set.Icc_eq_Icc_iff hla.le).1 hcell
  have hk := Atom.k_eq_of_width (a := a) (b := b) (by rw [hL, hR])
  have hL' : a.left = b.left := by exact_mod_cast hL
  have hm : a.m = b.m := by
    have h2 := hL'
    simp only [Atom.left] at h2
    rw [hk] at h2
    have hpos : (2 : ℚ) ^ b.k ≠ 0 := by positivity
    have : (a.m : ℚ) = b.m := by rwa [div_left_inj' hpos] at h2
    exact_mod_cast this
  have hc : a.center = b.center := by unfold Atom.center; rw [hk, hm]
  have hy : a.y0 = b.y0 := by
    have : a.y0 = a.intercept + a.s * a.center := by simp [Atom.intercept]
    have h2 : b.y0 = b.intercept + b.s * b.center := by simp [Atom.intercept]
    rw [this, h2, hi', hs', hc]
  exact Atom.ext hk hm hy hs'

/-- Theorem 3.5: `Γ` is injective, hence a bijection of `ℕ` onto `𝓛`. -/
theorem Gamma_injective : Function.Injective Gamma :=
  Atom.toTriple_injective.comp decode.injective

/-- The bijection between atoms (parameter quadruples) and the library `𝓛`. -/
noncomputable def atomEquivLibrary : Atom ≃ Library :=
  Equiv.ofBijective (fun a => ⟨a.toTriple, encode a, by simp [Gamma]⟩)
    ⟨fun a b h => Atom.toTriple_injective (congrArg Subtype.val h),
     fun ⟨t, n, hn⟩ => ⟨decode n, Subtype.ext (by simpa [Gamma] using hn)⟩⟩

/-! ### Height shells `𝓛_H` -/

/-- Nonzero rationals of height `≤ H`. -/
def ratsStarUpTo (H : ℕ) : Finset {s : ℚ // s ≠ 0} := (ratsUpTo H).subtype (fun s => s ≠ 0)

lemma mem_ratsStarUpTo {H : ℕ} {s : {s : ℚ // s ≠ 0}} :
    s ∈ ratsStarUpTo H ↔ ratHeight s.1 ≤ H := by
  simp [ratsStarUpTo, mem_ratsUpTo]

lemma card_ratsStarUpTo {H : ℕ} (hH : 1 ≤ H) :
    (ratsStarUpTo H).card = (ratsUpTo H).card - 1 := by
  simp only [ratsStarUpTo, card_subtype]
  rw [Finset.filter_ne' , card_erase_of_mem (zero_mem_ratsUpTo hH)]

/-- Equivalence between atoms and parameter quadruples. -/
def Atom.equivProd : Atom ≃ ℕ × ℤ × ℚ × {s : ℚ // s ≠ 0} where
  toFun a := (a.k, a.m, a.y0, ⟨a.s, a.hs⟩)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv a := rfl
  right_inv p := rfl

/-- The finite set `𝓛_H` of atoms of height at most `H`. -/
def atomsUpTo (H : ℕ) : Finset Atom :=
  if 2 ≤ H then
    ((Finset.range H ×ˢ Finset.Icc (-(H : ℤ) + 1) (H - 1) ×ˢ ratsUpTo H ×ˢ ratsStarUpTo H).map
      Atom.equivProd.symm.toEmbedding)
  else ∅

lemma mem_atomsUpTo {H : ℕ} {a : Atom} : a ∈ atomsUpTo H ↔ a.height ≤ H := by
  rw [a.height_le_iff]
  unfold atomsUpTo
  split_ifs with h
  · simp only [mem_map_equiv, Equiv.symm_symm, mem_product, mem_range, mem_Icc, mem_ratsUpTo,
      mem_ratsStarUpTo]
    simp only [Atom.equivProd, Equiv.coe_fn_mk]
    omega
  · simp; omega

/-- Exact cardinality of `𝓛_H` for `H ≥ 2`. -/
theorem card_atomsUpTo {H : ℕ} (hH : 2 ≤ H) :
    (atomsUpTo H).card = H * (2 * H - 1) * ((ratsUpTo H).card * ((ratsUpTo H).card - 1)) := by
  unfold atomsUpTo
  rw [if_pos hH, card_map]
  simp only [card_product, card_range, Int.card_Icc, card_ratsStarUpTo (by omega : 1 ≤ H)]
  rw [show ((H : ℤ) - 1 + 1 - (-(H : ℤ) + 1)).toNat = 2 * H - 1 by omega]
  ring

end Dyadic.Lib
