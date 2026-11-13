module
public import Mathlib
@[expose] public section

/-!
# Section 7.6: codecs and the informational limit

Definition 7.19 (resources of a codec) and Proposition 7.20.
-/

namespace Dyadic.Lib

variable {X : Type*} [PseudoMetricSpace X]

/-- The covering number `𝒩_ε(𝓕)`: least number of closed balls of radius `ε` covering `𝓕`. -/
noncomputable def coveringNumber (F : Set X) (ε : ℝ) : ℕ :=
  sInf {n | ∃ C : Finset X, C.card = n ∧ ∀ f ∈ F, ∃ c ∈ C, dist f c ≤ ε}

/-- The metric entropy `ℋ_ε(𝓕) = log₂ 𝒩_ε(𝓕)`. -/
noncomputable def metricEntropy (F : Set X) (ε : ℝ) : ℝ := Real.logb 2 (coveringNumber F ε)

/-- A set of binary words is prefix-free. -/
def PrefixFree (W : Finset (List Bool)) : Prop :=
  ∀ w ∈ W, ∀ w' ∈ W, w <+: w' → w = w'

/-- **Definition 7.19**: an `ε`-codec `(W, Enc, Dec)` for `𝓕`. -/
structure Codec (F : Set X) (ε : ℝ) where
  W : Finset (List Bool)
  enc : X → List Bool
  dec : List Bool → X
  enc_mem : ∀ f ∈ F, enc f ∈ W
  distortion : ∀ f ∈ F, dist f (dec (enc f)) ≤ ε

/-- Maximal word length of a codec. -/
def Codec.maxLen {F : Set X} {ε : ℝ} (c : Codec F ε) : ℕ := c.W.sup List.length

/-- `L^dec_ε(𝓕)`: least maximal word length of a prefix-free `ε`-codec. -/
noncomputable def decLength (F : Set X) (ε : ℝ) : ℕ :=
  sInf {ℓ | ∃ c : Codec F ε, PrefixFree c.W ∧ c.maxLen = ℓ}

lemma coveringNumber_le_card {F : Set X} {ε : ℝ} (c : Codec F ε) :
    coveringNumber F ε ≤ c.W.card := by
  classical
  have hmem : (c.W.image c.dec).card ∈
      {n | ∃ C : Finset X, C.card = n ∧ ∀ f ∈ F, ∃ c ∈ C, dist f c ≤ ε} :=
    ⟨c.W.image c.dec, rfl, fun f hf => ⟨c.dec (c.enc f),
      Finset.mem_image_of_mem _ (c.enc_mem f hf), c.distortion f hf⟩⟩
  exact (Nat.sInf_le hmem).trans Finset.card_image_le

/-- Padding words to length `ℓ` is injective on a prefix-free set. -/
lemma card_le_two_pow_of_prefixFree (W : Finset (List Bool)) (hW : PrefixFree W) (ℓ : ℕ)
    (hlen : ∀ w ∈ W, w.length ≤ ℓ) : W.card ≤ 2 ^ ℓ := by
  classical
  let pad : List Bool → List Bool := fun w => (w ++ List.replicate (ℓ - w.length) false).take ℓ
  have hpad_len : ∀ w ∈ W, (pad w).length = ℓ := by
    intro w hw; simp [pad]; have := hlen w hw; omega
  have hpre : ∀ w ∈ W, w <+: pad w := by
    intro w hw
    have := hlen w hw
    simp only [pad]
    rw [List.take_of_length_le (by simp; omega)]
    exact List.prefix_append _ _
  have hinj : Set.InjOn pad W := by
    intro w hw w' hw' h
    have h1 := hpre w hw
    have h2 := hpre w' hw'
    rw [h] at h1
    rcases le_total w.length w'.length with hl | hl
    · exact hW w hw w' hw' (List.prefix_of_prefix_length_le h1 h2 hl)
    · exact (hW w' hw' w hw (List.prefix_of_prefix_length_le h2 h1 hl)).symm
  let S : Finset (List Bool) := W.image pad
  have hS : S.card = W.card := Finset.card_image_of_injOn hinj
  let V : Finset (List.Vector Bool ℓ) := S.attach.image (fun w => ⟨w.1, by
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.1 w.2
    rw [← hvw]; exact hpad_len v hv⟩)
  have hV : V.card = S.card := by
    rw [Finset.card_image_of_injective _ (fun a b h => by
      apply Subtype.ext; simpa using congrArg Subtype.val h), Finset.card_attach]
  have := Finset.card_le_univ V
  rw [card_vector, Fintype.card_bool] at this
  omega

/-- **Proposition 7.20** (informational limit): every `ε`-codec whose words all have length `ℓ`, or
which is prefix-free with maximal word length `ℓ`, satisfies `ℓ ≥ ⌈ℋ_ε(𝓕)⌉`. In particular
`L^dec_ε(𝓕) ≥ ⌈ℋ_ε(𝓕)⌉`. -/
theorem informational_limit (F : Set X) (ε : ℝ) :
    (∀ (c : Codec F ε) (ℓ : ℕ), (∀ w ∈ c.W, w.length = ℓ) →
        ⌈metricEntropy F ε⌉ ≤ ℓ) ∧
    (∀ (c : Codec F ε) (ℓ : ℕ), PrefixFree c.W → (∀ w ∈ c.W, w.length ≤ ℓ) →
        ⌈metricEntropy F ε⌉ ≤ ℓ) ∧
    ((∃ c : Codec F ε, PrefixFree c.W) → ⌈metricEntropy F ε⌉ ≤ decLength F ε) := by
  have key : ∀ (c : Codec F ε) (ℓ : ℕ), c.W.card ≤ 2 ^ ℓ → ⌈metricEntropy F ε⌉ ≤ ℓ := by
    intro c ℓ hcard
    have hN : (coveringNumber F ε : ℝ) ≤ 2 ^ ℓ := by
      exact_mod_cast (coveringNumber_le_card c).trans hcard
    rw [Int.ceil_le]
    unfold metricEntropy
    rcases Nat.eq_zero_or_pos (coveringNumber F ε) with h0 | hpos
    · rw [h0]; simp
    · have : Real.logb 2 (coveringNumber F ε) ≤ Real.logb 2 (2 ^ ℓ) :=
        Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) hN
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
      simpa using this
  have hpf : ∀ (c : Codec F ε) (ℓ : ℕ), PrefixFree c.W → (∀ w ∈ c.W, w.length ≤ ℓ) →
      ⌈metricEntropy F ε⌉ ≤ ℓ :=
    fun c ℓ hW hlen => key c ℓ (card_le_two_pow_of_prefixFree c.W hW ℓ hlen)
  refine ⟨fun c ℓ hlen => ?_, hpf, fun ⟨c, hc⟩ => ?_⟩
  · -- words of equal length form a prefix-free set
    apply hpf c ℓ _ (fun w hw => (hlen w hw).le)
    intro w hw w' hw' hpre
    exact hpre.eq_of_length (by rw [hlen w hw, hlen w' hw'])
  · have hne : {ℓ | ∃ c : Codec F ε, PrefixFree c.W ∧ c.maxLen = ℓ}.Nonempty := ⟨_, c, hc, rfl⟩
    obtain ⟨c', hc', hmax⟩ := Nat.sInf_mem hne
    unfold decLength
    rw [← hmax]
    exact hpf c' _ hc' (fun w hw => Finset.le_sup (f := List.length) hw)

end Dyadic.Lib
