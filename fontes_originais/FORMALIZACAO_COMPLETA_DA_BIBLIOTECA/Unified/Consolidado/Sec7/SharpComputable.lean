module
public import Unified.Consolidado.Sec7.Address
@[expose] public section

/-!
# Theorem 7.7: two-way computability of `Γ^♯`

The enumeration `Γ^♯ : ℕ → 𝓛` and its inverse `n^♯ : 𝓛 → ℕ` of Definition 7.6 are realised by
executable programs (definitions without `noncomputable`, compiled by Lean), proved to coincide
with them.  The inverse counts the atoms of the finite shell `𝓛_{ht(a)}` whose key is smaller; the
direct map finds the least `H` with `n < |𝓛_H|` and selects the unique atom of `𝓛_H` with address
`n` — exactly the procedure of the proof of Theorem 7.7 (finite, explicitly enumerable shells).
-/

open Finset

namespace Dyadic.Lib

/-- With an injective key, the rank of `a` is the number of elements of any finite set containing
every element of smaller key whose key is smaller. -/
lemma keyRank_eq_card {α : Type*} {e : α → ℕ} (he : Function.Injective e) (a : α) (S : Finset α)
    (hS : ∀ b, e b < e a → b ∈ S) : keyRank e a = (S.filter (fun b => e b < e a)).card := by
  classical
  unfold keyRank
  rw [Nat.count_eq_card_filter_range, ← card_image_of_injective _ he]
  congr 1
  ext n
  simp only [mem_filter, mem_range, Set.mem_range, mem_image]
  constructor
  · rintro ⟨hn, b, rfl⟩; exact ⟨b, ⟨hS b hn, hn⟩, rfl⟩
  · rintro ⟨b, ⟨-, hb⟩, rfl⟩; exact ⟨hb, b, rfl⟩

/-- Executable rank in the height enumeration `Q` of `ℚ`. -/
def rankQc (r : ℚ) : ℕ := ((ratsUpTo (ratHeight r)).filter (fun r' => ratKey r' < ratKey r)).card

lemma rankQc_eq (r : ℚ) : rankQc r = rankQ r :=
  (keyRank_eq_card ratKey_injective r _
    (fun _ hb => mem_ratsUpTo.2 (height_le_of_ratKey_lt hb))).symm

/-- Executable rank in the height enumeration `Q^*` of `ℚ^*`. -/
def rankQstarc (s : {s : ℚ // s ≠ 0}) : ℕ :=
  ((ratsStarUpTo (ratHeight s.1)).filter (fun s' => ratKey s'.1 < ratKey s.1)).card

lemma rankQstarc_eq (s : {s : ℚ // s ≠ 0}) : rankQstarc s = rankQstar s :=
  (keyRank_eq_card (e := fun s : {s : ℚ // s ≠ 0} => ratKey s.1)
    (fun _ _ h => Subtype.ext (ratKey_injective h)) s _
    (fun _ hb => mem_ratsStarUpTo.2 (height_le_of_ratKey_lt hb))).symm

/-- Executable version of the key of Definition 7.6. -/
def sharpKeyc (a : Atom) : ℕ :=
  64 * a.height ^ 7 +
    (((a.k * (2 * a.height + 1) + zEncode a.m) * (3 * a.height ^ 2) + rankQc a.y0) *
      (3 * a.height ^ 2) + rankQstarc ⟨a.s, a.hs⟩)

lemma sharpKeyc_eq (a : Atom) : sharpKeyc a = sharpKey a := by
  simp [sharpKeyc, sharpKey, rankQc_eq, rankQstarc_eq]

/-- Executable inverse `n^♯ = (Γ^♯)⁻¹`: the number of atoms of the shell `𝓛_{ht(a)}` that precede
`a` in the order of Definition 7.6. -/
def addrSharpc (a : Atom) : ℕ :=
  ((atomsUpTo a.height).filter (fun b => sharpKeyc b < sharpKeyc a)).card

theorem addrSharpc_eq (a : Atom) : addrSharpc a = addrSharp a := by
  unfold addrSharpc addrSharp
  simp only [sharpKeyc_eq]
  exact (keyRank_eq_card sharpKey_injective a _
    (fun b hb => mem_atomsUpTo.2 (height_le_of_sharpKey_lt hb))).symm

lemma GammaSharp_spec (n : ℕ) : addrSharp (GammaSharp n) = n :=
  (Equiv.ofBijective addrSharp addrSharp_bijective).apply_symm_apply n

lemma lt_card_shell (n : ℕ) : ∃ H, n < (atomsUpTo H).card := by
  refine ⟨(GammaSharp n).height, ?_⟩
  have h2 := (GammaSharp n).two_le_height
  have h1 : addrSharp (GammaSharp n) ≤ (atomsUpTo (GammaSharp n).height).sup addrSharp :=
    le_sup (mem_atomsUpTo.2 le_rfl)
  rw [(addrSharp_minimax.2 _ h2).1, GammaSharp_spec] at h1
  have : 0 < (atomsUpTo (GammaSharp n).height).card := card_pos.2 ⟨_, mem_atomsUpTo.2 le_rfl⟩
  omega

/-- The shell containing the `n`-th atom: the least `H` with `n < |𝓛_H|`. -/
def shellOf (n : ℕ) : ℕ := Nat.find (lt_card_shell n)

lemma existsUnique_shell (n : ℕ) :
    ∃! a, a ∈ atomsUpTo (shellOf n) ∧ addrSharpc a = n := by
  refine ⟨GammaSharp n, ⟨?_, by rw [addrSharpc_eq, GammaSharp_spec]⟩, ?_⟩
  · rw [mem_atomsUpTo]
    by_contra hlt
    push_neg at hlt
    have hspec : n < (atomsUpTo (shellOf n)).card := Nat.find_spec (lt_card_shell n)
    -- every atom of the shell `𝓛_{shellOf n}` precedes `Γ^♯ n`
    have hsub : atomsUpTo (shellOf n) ⊆ (atomsUpTo (GammaSharp n).height).filter
        (fun b => sharpKey b < sharpKey (GammaSharp n)) := by
      intro b hb
      have hb' := mem_atomsUpTo.1 hb
      refine mem_filter.2 ⟨mem_atomsUpTo.2 (by omega), ?_⟩
      rw [sharpKey_lt_iff]
      left; omega
    have hrank := keyRank_eq_card sharpKey_injective (GammaSharp n)
      (atomsUpTo (GammaSharp n).height)
      (fun b hb => mem_atomsUpTo.2 (height_le_of_sharpKey_lt hb))
    have h1 := card_le_card hsub
    rw [← hrank] at h1
    have h2 : keyRank sharpKey (GammaSharp n) = n := GammaSharp_spec n
    omega
  · rintro b ⟨-, hb⟩
    apply addrSharp_bijective.1
    rw [← addrSharpc_eq, hb, GammaSharp_spec]

/-- Executable enumeration `Γ^♯ : ℕ → 𝓛`. -/
def gammaSharpc (n : ℕ) : Atom :=
  (atomsUpTo (shellOf n)).choose (fun a => addrSharpc a = n) (existsUnique_shell n)

theorem gammaSharpc_eq (n : ℕ) : gammaSharpc n = GammaSharp n := by
  have h := Finset.choose_property (fun a => addrSharpc a = n) (atomsUpTo (shellOf n))
    (existsUnique_shell n)
  apply addrSharp_bijective.1
  rw [GammaSharp_spec, ← addrSharpc_eq]
  exact h

/-- **Theorem 7.7**, computability: `Γ^♯` is computable in both directions — the executable
programs `gammaSharpc : ℕ → 𝓛` and `addrSharpc : 𝓛 → ℕ` coincide with `Γ^♯` and its inverse
`n^♯`, and are mutually inverse. -/
theorem GammaSharp_computable :
    (∀ n, gammaSharpc n = GammaSharp n) ∧ (∀ a, addrSharpc a = addrSharp a) ∧
    (∀ n, addrSharpc (gammaSharpc n) = n) ∧ (∀ a, gammaSharpc (addrSharpc a) = a) := by
  refine ⟨gammaSharpc_eq, addrSharpc_eq, fun n => ?_, fun a => ?_⟩
  · rw [addrSharpc_eq, gammaSharpc_eq, GammaSharp_spec]
  · rw [gammaSharpc_eq, addrSharpc_eq]
    exact (Equiv.ofBijective addrSharp addrSharp_bijective).symm_apply_apply a

end Dyadic.Lib
