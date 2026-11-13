module
public import RequestProject.Sec7.Bits
public import RequestProject.Sec7.Address
public import RequestProject.Lib.Assembly
@[expose] public section

/-!
# Theorem 7.9: conditioned serialization of assemblies

The stream is `γ(N) γ(H)` followed by the `N` leaf addresses, each written as a block of a fixed
width depending only on `H`.  With the minimax enumeration `Γ^♯` the width is
`b_H = ⌈log₂(18 H⁶)⌉`; with the arithmetic generator `Γ` it is the least width able to carry every
address of `𝓛_H`, namely `⌈log₂(M_Γ(H) + 1)⌉`, which is `8 log₂ H + O(1)`.
-/

open Finset

namespace Dyadic.Lib

/-- Generic leaf-address stream: `γ(N) γ(H)` followed by the addresses `A(a)` of the leaves (in
increasing order), each as a block of `w H` bits. -/
noncomputable def serWith (A : Atom → ℕ) (w : ℕ → ℕ) (Λ : Finset Atom) : List Bool :=
  eliasGamma Λ.card ++ eliasGamma (maxHeight Λ) ++
    (((Λ.image A).sort (· ≤ ·)).map (toBits (w (maxHeight Λ)))).flatten

/-- Generic decoder: reads `N`, then `H`, then `N` blocks of width `w H`, and maps each block back
to an atom with `D`.  It needs no prior knowledge of `N` or `H`. -/
noncomputable def deserWith (D : ℕ → Atom) (w : ℕ → ℕ) (l : List Bool) :
    Option (Finset Atom × List Bool) :=
  (gammaDec l).bind fun p => (gammaDec p.2).bind fun q =>
    (decMany (fixedDec (w q.1)) p.1 q.2).map fun r => ((r.1.map D).toFinset, r.2)

lemma length_serWith (A : Atom → ℕ) (hA : Function.Injective A) (w : ℕ → ℕ) (Λ : Finset Atom) :
    (serWith A w Λ).length = (2 * Nat.log 2 Λ.card + 1) + (2 * Nat.log 2 (maxHeight Λ) + 1)
      + Λ.card * w (maxHeight Λ) := by
  unfold serWith
  simp only [List.length_append, length_eliasGamma, List.length_flatten, List.map_map]
  have : ∀ l : List ℕ, (l.map (List.length ∘ toBits (w (maxHeight Λ)))).sum =
      l.length * w (maxHeight Λ) := by
    intro l; induction l with
    | nil => simp
    | cons x l ih => simp [ih]; ring
  rw [this, Finset.length_sort, card_image_of_injective _ hA]

lemma deserWith_serWith (A : Atom → ℕ) (D : ℕ → Atom) (hDA : ∀ a, D (A a) = a) (w : ℕ → ℕ)
    (Λ : Finset Atom) (hne : Λ.Nonempty) (hw : ∀ a ∈ Λ, A a < 2 ^ w (maxHeight Λ))
    (r : List Bool) : deserWith D w (serWith A w Λ ++ r) = some (Λ, r) := by
  have hAi : Function.Injective A := fun a b h => by rw [← hDA a, ← hDA b, h]
  have hN : 1 ≤ Λ.card := card_pos.2 hne
  obtain ⟨a0, ha0⟩ := hne
  have hH : 1 ≤ maxHeight Λ :=
    le_trans (by have := a0.two_le_height; omega) (le_sup (f := Atom.height) ha0)
  set L := (Λ.image A).sort (· ≤ ·)
  have hL : L.length = Λ.card := by rw [Finset.length_sort, card_image_of_injective _ hAi]
  unfold deserWith serWith
  simp only [List.append_assoc]
  rw [gammaDec_eliasGamma hN, Option.bind_some, gammaDec_eliasGamma hH, Option.bind_some]
  simp only
  rw [← hL, decMany_flatten _ _ L (fun x hx r => fixedDec_toBits (by
    rw [Finset.mem_sort, mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hw a ha) r)]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  ext a
  simp only [List.mem_toFinset, List.mem_map, L, Finset.mem_sort, mem_image]
  constructor
  · rintro ⟨n, ⟨b, hb, rfl⟩, rfl⟩; rwa [hDA]
  · intro ha; exact ⟨A a, ⟨a, ha, rfl⟩, hDA a⟩

/-- An assembly representation determines the function on `K`. -/
lemma IsAssemblyRep.eqOn {K : Set ℝ} {g g' : ℝ → ℝ} {Λ : Finset Atom} (hg : IsAssemblyRep K g Λ)
    (hg' : IsAssemblyRep K g' Λ) : ∀ x ∈ K, g' x = g x := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hg.2.1 hx)
  rw [hg.2.2.1 a ha x ⟨hxa, hx⟩, hg'.2.2.1 a ha x ⟨hxa, hx⟩]

/-! ### The two concrete streams -/

/-- Block width for `Γ^♯`: `b_H = ⌈log₂(18 H⁶)⌉`. -/
def widthSharp (H : ℕ) : ℕ := Nat.clog 2 (18 * H ^ 6)

/-- Block width for `Γ`: least width carrying every `Γ`-address of `𝓛_H`,
`⌈log₂(M_Γ(H) + 1)⌉`. -/
noncomputable def widthGamma (H : ℕ) : ℕ := Nat.clog 2 (worstAddress H + 1)

/-- The `Γ^♯` stream of Theorem 7.9. -/
noncomputable def serSharp (Λ : Finset Atom) : List Bool := serWith addrSharp widthSharp Λ
/-- Its decoder. -/
noncomputable def deserSharp (l : List Bool) : Option (Finset Atom × List Bool) :=
  deserWith GammaSharp widthSharp l
/-- The `Γ` stream of Theorem 7.9. -/
noncomputable def serGamma (Λ : Finset Atom) : List Bool := serWith encode widthGamma Λ
/-- Its decoder. -/
noncomputable def deserGamma (l : List Bool) : Option (Finset Atom × List Bool) :=
  deserWith decode widthGamma l

lemma GammaSharp_addrSharp (a : Atom) : GammaSharp (addrSharp a) = a :=
  (Equiv.ofBijective addrSharp addrSharp_bijective).symm_apply_apply a

lemma addrSharp_lt_width {H : ℕ} (hH : 2 ≤ H) {a : Atom} (ha : a.height ≤ H) :
    addrSharp a < 2 ^ widthSharp H := by
  have h1 : addrSharp a ≤ (atomsUpTo H).sup addrSharp := le_sup (mem_atomsUpTo.2 ha)
  rw [(addrSharp_minimax.2 H hH).1] at h1
  have h2 := card_atomsUpTo_le hH
  have h3 : 1 ≤ (atomsUpTo H).card := card_pos.2 ⟨a, mem_atomsUpTo.2 ha⟩
  have h4 := Nat.le_pow_clog (b := 2) (by norm_num) (18 * H ^ 6)
  unfold widthSharp; omega

lemma encode_lt_width {H : ℕ} {a : Atom} (ha : a.height ≤ H) : encode a < 2 ^ widthGamma H := by
  have h1 : encode a ≤ worstAddress H := le_sup (mem_atomsUpTo.2 ha)
  have h4 := Nat.le_pow_clog (b := 2) (by norm_num) (worstAddress H + 1)
  unfold widthGamma; omega

/-- `b_H = ⌈log₂(18 H⁶)⌉ ≤ 6 log₂ H + 6`. -/
lemma widthSharp_le {H : ℕ} (hH : 2 ≤ H) : (widthSharp H : ℝ) ≤ 6 * Real.logb 2 H + 6 := by
  unfold widthSharp
  have hpos : (0 : ℝ) < H := by positivity
  refine (clog_le_logb_add_one (Nat.one_le_iff_ne_zero.mpr (by positivity))).trans ?_
  push_cast
  rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow]
  have : Real.logb 2 18 ≤ 5 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
  push_cast; linarith

/-- **Theorem 7.9** (conditioned serialization of assemblies).  Let `g ∈ 𝒜(K)` be represented by a
nonempty finite family `Λ` of `N = |Λ|` atoms (the leaves of its dyadic tree), and let
`H = max_{a ∈ Λ} ht(a) ≥ 2`.  The stream `serSharp Λ` is self-delimiting and decodable without
prior knowledge of `N` or `H` (the decoder `deserSharp` reads it from the front of any longer bit
string and returns exactly `Λ` and the unread rest); the decoded leaves determine `g` on `K`;
and its length satisfies eq. (55):
`L(g | K) = (2⌊log₂ N⌋ + 1) + (2⌊log₂ H⌋ + 1) + N ⌈log₂(18 H⁶)⌉`
`         ≤ N (6 log₂ H + C) + C (log₂ N + log₂ H)` with a universal `C`. -/
theorem serialization_sharp :
    (∀ (K : Set ℝ) (g : ℝ → ℝ) (Λ : Finset Atom), g ∈ Asm K → IsAssemblyRep K g Λ →
      Λ.Nonempty →
      (∀ r : List Bool, deserSharp (serSharp Λ ++ r) = some (Λ, r)) ∧
      (∀ g' : ℝ → ℝ, IsAssemblyRep K g' Λ → ∀ x ∈ K, g' x = g x) ∧
      2 ≤ maxHeight Λ ∧
      ((serSharp Λ).length : ℝ) = (2 * ⌊Real.logb 2 Λ.card⌋₊ + 1) +
        (2 * ⌊Real.logb 2 (maxHeight Λ)⌋₊ + 1) +
        Λ.card * ⌈Real.logb 2 (18 * (maxHeight Λ : ℝ) ^ 6)⌉₊) ∧
    ∃ C : ℝ, ∀ Λ : Finset Atom, Λ.Nonempty →
      ((serSharp Λ).length : ℝ) ≤ Λ.card * (6 * Real.logb 2 (maxHeight Λ) + C) +
        C * (Real.logb 2 Λ.card + Real.logb 2 (maxHeight Λ)) := by
  have hH2 : ∀ Λ : Finset Atom, Λ.Nonempty → 2 ≤ maxHeight Λ := by
    rintro Λ ⟨a, ha⟩; exact a.two_le_height.trans (le_sup (f := Atom.height) ha)
  refine ⟨fun K g Λ _ hrep hne => ⟨fun r => ?_, fun g' hg' => hg'.eqOn hrep |> fun h x hx =>
    (hrep.eqOn hg' x hx), hH2 Λ hne, ?_⟩, 6, fun Λ hne => ?_⟩
  · exact deserWith_serWith addrSharp GammaSharp GammaSharp_addrSharp widthSharp Λ hne
      (fun a ha => addrSharp_lt_width (hH2 Λ hne) (le_sup (f := Atom.height) ha)) r
  · rw [serSharp, length_serWith _ addrSharp_bijective.1]
    have e1 := Real.natFloor_logb_natCast 2 Λ.card
    have e2 := Real.natFloor_logb_natCast 2 (maxHeight Λ)
    have e3 := Real.natCeil_logb_natCast 2 (18 * (maxHeight Λ) ^ 6)
    push_cast at e1 e2 e3
    rw [e1, e2, e3]; push_cast; rfl
  · rw [serSharp, length_serWith _ addrSharp_bijective.1]
    set H := maxHeight Λ
    set N := Λ.card
    have hH := hH2 Λ hne
    have hw := widthSharp_le hH
    have h1 := natLog_le_logb N
    have h2 := natLog_le_logb H
    have hl := one_le_logb_of_two_le hH
    have hlN := logb_nonneg_nat N
    push_cast
    have : (N : ℝ) * widthSharp H ≤ N * (6 * Real.logb 2 H + 6) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    nlinarith

/-- **Theorem 7.9**, arithmetic generator `Γ`: the same stream built with `Γ`-addresses and blocks of
the least width `⌈log₂(M_Γ(H)+1)⌉` able to carry every address of `𝓛_H` is self-delimiting and
exactly decodable; its per-leaf block is `8 log₂ H + O(1)` bits (two-sided), so its length is
`N (8 log₂ H + O(1)) + O(log N + log H)`. -/
theorem serialization_gamma :
    (∀ Λ : Finset Atom, Λ.Nonempty →
      ∀ r : List Bool, deserGamma (serGamma Λ ++ r) = some (Λ, r)) ∧
    (∃ C : ℝ, ∃ H₀ : ℕ, ∀ H ≥ H₀, |(widthGamma H : ℝ) - 8 * Real.logb 2 H| ≤ C) ∧
    ∃ C : ℝ, ∀ Λ : Finset Atom, Λ.Nonempty →
      ((serGamma Λ).length : ℝ) ≤ Λ.card * (8 * Real.logb 2 (maxHeight Λ) + C) +
        C * (Real.logb 2 Λ.card + Real.logb 2 (maxHeight Λ)) := by
  have hH2 : ∀ Λ : Finset Atom, Λ.Nonempty → 2 ≤ maxHeight Λ := by
    rintro Λ ⟨a, ha⟩; exact a.two_le_height.trans (le_sup (f := Atom.height) ha)
  obtain ⟨C₀, H₀, hC₀⟩ := worstAddress_theta.2
  -- upper bound on the width valid for every `H ≥ 2`
  have hwu : ∀ H : ℕ, 2 ≤ H → (widthGamma H : ℝ) ≤ 8 * Real.logb 2 H + 13 := by
    intro H hH
    have hpos : (0 : ℝ) < H := by positivity
    unfold widthGamma
    refine (clog_le_logb_add_one (by omega)).trans ?_
    push_cast
    have h1 : ((worstAddress H + 1 : ℕ) : ℝ) ≤ 2117 * (H : ℝ) ^ 8 := by
      have := worstAddress_le (H := H)
      have : (1 : ℝ) ≤ (H : ℝ) ^ 8 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ H))
      push_cast; linarith
    have h2 : Real.logb 2 ((worstAddress H + 1 : ℕ) : ℝ) ≤ Real.logb 2 (2117 * (H : ℝ) ^ 8) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow] at h2
    have : Real.logb 2 2117 ≤ 12 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num
    push_cast at h2 ⊢; linarith
  refine ⟨fun Λ hne r => deserWith_serWith encode decode decode_encode widthGamma Λ hne
      (fun a ha => encode_lt_width (le_sup (f := Atom.height) ha)) r,
    ⟨max C₀ 13, max H₀ 2, fun H hH => ?_⟩, 13, fun Λ hne => ?_⟩
  · have hHH : 2 ≤ H := le_trans (le_max_right _ _) hH
    have hlo := hC₀ H (le_trans (le_max_left _ _) hH)
    have h1 : Real.logb 2 ((worstAddress H : ℝ) + 1) ≤ widthGamma H := by
      have := logb_le_clog (x := worstAddress H + 1); push_cast at this; exact this
    have h2 := hwu H hHH
    rw [abs_le] at hlo ⊢
    constructor
    · have := le_max_left C₀ 13; linarith
    · have := le_max_right C₀ 13; linarith
  · rw [serGamma, length_serWith _ encode_bijective.1]
    set H := maxHeight Λ
    set N := Λ.card
    have hH := hH2 Λ hne
    have hw := hwu H hH
    have h1 := natLog_le_logb N
    have h2 := natLog_le_logb H
    have hl := one_le_logb_of_two_le hH
    have hlN := logb_nonneg_nat N
    push_cast
    have : (N : ℝ) * widthGamma H ≤ N * (8 * Real.logb 2 H + 13) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    nlinarith

end Dyadic.Lib
