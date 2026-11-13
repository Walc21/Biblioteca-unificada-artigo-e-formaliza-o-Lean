import RequestProject.Entropy

/-!
# Definition 3.15 (recursos de um codec) and Proposition 3.16
(limite informacional para representação decodificável)

The ambient metric space is the space of functions `ℝ → ℝ` with the uniform distance on
`[0,1]`, as in Theorem 3.14.  The time costs `T^enc_ε`, `T^dec_ε` of Definition 3.15 are, as the
article stresses, not mathematical quantities until a model of computation is fixed; they are
not formalized.
-/

namespace Artigo

open Set LTree

/-! ## Definition 3.15 -/

/-- an `ε`-codec `(𝒲, Enc, Dec)` for `F`: a finite set of binary words, an encoder into it and a
(shared) decoder with distortion at most `ε` on `[0,1]` -/
structure EpsCodec (ε : ℝ) (F : Set (ℝ → ℝ)) where
  W : Finset (List Bool)
  enc : (ℝ → ℝ) → List Bool
  dec : List Bool → (ℝ → ℝ)
  enc_mem : ∀ f ∈ F, enc f ∈ W
  distortion : ∀ f ∈ F, ∀ x ∈ Icc (0 : ℝ) 1, |f x - dec (enc f) x| ≤ ε

/-- the word set is prefix-free -/
def PrefixFreeSet (W : Finset (List Bool)) : Prop := ∀ u ∈ W, ∀ v ∈ W, u <+: v → u = v

/-- the maximal word length `max_{w ∈ 𝒲} |w|` -/
def maxLen (W : Finset (List Bool)) : ℕ := W.sup List.length

/-- `L^dec_ε(F)`: least maximal length of a prefix-free `ε`-codec (`+∞` if none exists) -/
noncomputable def Ldec (ε : ℝ) (F : Set (ℝ → ℝ)) : ℕ∞ :=
  ⨅ (c : EpsCodec ε F) (_ : PrefixFreeSet c.W), (maxLen c.W : ℕ∞)

/-- `L^global_ε(𝒞) = ⌈log₂ |𝒞|⌉`: fixed-length index into a shared codebook -/
def Lglobal {α : Type*} (CB : Finset α) : ℕ := Nat.clog 2 CB.card

/-- `L^folhas(g | K)`: length of the leaf-by-leaf serialization of Theorem 3.6 (the header
`γ(N)γ(H)` plays the role of `L_arv`, the address blocks that of `Σ L_addr`) -/
def Lfolhas (T : LTree) : ℕ := (serGen nSharp (fun H => Nat.clog 2 (18 * H ^ 6)) T).length

/-- `L^folhas_ε(𝒞 | K) = max_{g ∈ 𝒞} L^folhas(g | K)` -/
def LfolhasCB (CB : Finset LTree) : ℕ := CB.sup Lfolhas

/-! ## Counting words -/

lemma card_le_of_fixed_length (W : Finset (List Bool)) (ℓ : ℕ) (h : ∀ w ∈ W, w.length = ℓ) :
    W.card ≤ 2 ^ ℓ := by
  classical
  let g : List Bool → List.Vector Bool ℓ := fun w =>
    if hw : w.length = ℓ then ⟨w, hw⟩ else ⟨List.replicate ℓ false, by simp⟩
  have hinj : Set.InjOn g W := by
    intro u hu v hv huv
    simp only [g, dif_pos (h u hu), dif_pos (h v hv)] at huv
    exact congrArg Subtype.val huv
  calc W.card ≤ (Finset.univ : Finset (List.Vector Bool ℓ)).card :=
        Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _) hinj
    _ = 2 ^ ℓ := by rw [Finset.card_univ, card_vector]; simp

/-- padding to length `ℓ` -/
def padTo (ℓ : ℕ) (w : List Bool) : List Bool := w ++ List.replicate (ℓ - w.length) false

lemma card_le_of_prefixFree (W : Finset (List Bool)) (ℓ : ℕ) (hpf : PrefixFreeSet W)
    (h : ∀ w ∈ W, w.length ≤ ℓ) : W.card ≤ 2 ^ ℓ := by
  classical
  have hinj : Set.InjOn (padTo ℓ) W := by
    intro u hu v hv huv
    simp only [padTo] at huv
    rcases le_total u.length v.length with hl | hl
    · have : u <+: v := List.prefix_of_prefix_length_le
        (l₃ := v ++ List.replicate (ℓ - v.length) false)
        (by rw [← huv]; exact List.prefix_append _ _) (List.prefix_append _ _) hl
      exact hpf u hu v hv this
    · have : v <+: u := List.prefix_of_prefix_length_le
        (l₃ := u ++ List.replicate (ℓ - u.length) false)
        (by rw [huv]; exact List.prefix_append _ _) (List.prefix_append _ _) hl
      exact (hpf v hv u hu this).symm
  calc W.card = (W.image (padTo ℓ)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ 2 ^ ℓ := card_le_of_fixed_length _ ℓ (by
        intro w hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
        have := h u hu
        simp only [padTo, List.length_append, List.length_replicate]; omega)

/-- the reconstructions of a codec form an `ε`-cover, so `N_ε(F) ≤ |𝒲|` -/
lemma coverNum_le_codec {ε : ℝ} {F : Set (ℝ → ℝ)} (c : EpsCodec ε F) : coverNum ε F ≤ c.W.card := by
  classical
  refine (coverNum_le (s := c.W.image c.dec) ?_).trans Finset.card_image_le
  intro f hf
  exact ⟨_, Finset.mem_image_of_mem _ (c.enc_mem f hf), c.distortion f hf⟩

lemma ceil_entropy_le {ε : ℝ} {F : Set (ℝ → ℝ)} {ℓ : ℕ} (h : coverNum ε F ≤ 2 ^ ℓ) :
    ⌈entropyH ε F⌉ ≤ ℓ := by
  rw [Int.ceil_le]
  unfold entropyH
  rcases Nat.eq_zero_or_pos (coverNum ε F) with h0 | h0
  · rw [h0]; simp
  · calc Real.logb 2 (coverNum ε F) ≤ Real.logb 2 ((2 : ℝ) ^ ℓ) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h0) (by exact_mod_cast h)
      _ = ℓ := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
      _ = ((ℓ : ℤ) : ℝ) := by simp

lemma entropyH_nonneg (ε : ℝ) (F : Set (ℝ → ℝ)) : 0 ≤ entropyH ε F := by
  unfold entropyH
  rcases Nat.eq_zero_or_pos (coverNum ε F) with h0 | h0
  · rw [h0]; simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h0)

/-! ## Proposition 3.16 -/

/-- **Proposition 3.16 (limite informacional para representação decodificável)**:
(i) every fixed-length `ε`-codec of length `ℓ` has `ℓ ≥ ⌈𝓗_ε(F)⌉`;
(ii) the same holds for a prefix-free codec whose maximal word length is `ℓ`;
(iii) hence `L^dec_ε(F) ≥ ⌈𝓗_ε(F)⌉`. -/
theorem description_lower (ε : ℝ) (F : Set (ℝ → ℝ)) :
    (∀ (c : EpsCodec ε F) (ℓ : ℕ), (∀ w ∈ c.W, w.length = ℓ) → ⌈entropyH ε F⌉ ≤ ℓ) ∧
    (∀ (c : EpsCodec ε F), PrefixFreeSet c.W → ⌈entropyH ε F⌉ ≤ maxLen c.W) ∧
    ((⌈entropyH ε F⌉.toNat : ℕ∞) ≤ Ldec ε F) := by
  have hpf : ∀ (c : EpsCodec ε F), PrefixFreeSet c.W → ⌈entropyH ε F⌉ ≤ maxLen c.W := by
    intro c hc
    exact ceil_entropy_le ((coverNum_le_codec c).trans
      (card_le_of_prefixFree _ _ hc fun w hw => Finset.le_sup (f := List.length) hw))
  refine ⟨fun c ℓ h => ceil_entropy_le ((coverNum_le_codec c).trans
    (card_le_of_fixed_length _ _ h)), hpf, ?_⟩
  refine le_iInf₂ fun c hc => ?_
  have := hpf c hc
  have h0 : 0 ≤ ⌈entropyH ε F⌉ := Int.ceil_nonneg (entropyH_nonneg ε F)
  exact_mod_cast (show ⌈entropyH ε F⌉.toNat ≤ maxLen c.W by omega)

/-! ## The complexity chain (after Proposition 3.16) -/

/-- from a codebook of assemblies, the fixed-length index codec -/
lemma Ldec_le_Lglobal {ε : ℝ} {F : Set (ℝ → ℝ)} (CB : Finset LTree)
    (h : ∀ f ∈ F, ∃ T ∈ CB, supDist f T ≤ ENNReal.ofReal ε) (hε : 0 ≤ ε) :
    Ldec ε F ≤ Lglobal CB := by
  classical
  set L := Nat.clog 2 CB.card
  set lst := CB.toList
  have hlen : lst.length = CB.card := Finset.length_toList CB
  have hcard : CB.card ≤ 2 ^ L := Nat.le_pow_clog (by norm_num) _
  let pick : (ℝ → ℝ) → LTree := fun f => if hf : f ∈ F then Classical.choose (h f hf) else LTree.leaf ⟨0, 0, 0, 1, one_ne_zero⟩
  have hpick : ∀ f ∈ F, pick f ∈ CB ∧ supDist f (pick f) ≤ ENNReal.ofReal ε := by
    intro f hf
    simp only [pick, dif_pos hf]
    exact Classical.choose_spec (h f hf)
  let c : EpsCodec ε F :=
    { W := (Finset.range CB.card).image (toBits L)
      enc := fun f => toBits L (lst.idxOf (pick f))
      dec := fun w => (lst.getD (ofBits w) (LTree.leaf ⟨0, 0, 0, 1, one_ne_zero⟩)).eval 0 0
      enc_mem := by
        intro f hf
        refine Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr ?_, rfl⟩
        rw [← hlen]
        exact List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr (hpick f hf).1)
      distortion := by
        intro f hf x hx
        have hi : lst.idxOf (pick f) < lst.length :=
          List.idxOf_lt_length_iff.mpr (Finset.mem_toList.mpr (hpick f hf).1)
        have hi2 : lst.idxOf (pick f) < 2 ^ L := by omega
        rw [ofBits_toBits _ _ hi2, List.getD_eq_getElem _ _ hi, List.getElem_idxOf hi]
        exact (supDist_le_iff hε).mp (hpick f hf).2 x hx }
  have hpfc : PrefixFreeSet c.W := by
    intro u hu v hv huv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hv
    exact huv.eq_of_length (by simp)
  have hmax : maxLen c.W ≤ L := by
    apply Finset.sup_le
    intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    simp
  calc Ldec ε F ≤ (maxLen c.W : ℕ∞) := iInf₂_le c hpfc
    _ ≤ Lglobal CB := by exact_mod_cast hmax

/-- **The chain (eq. complexity-chain)**: `𝓗_ε(𝓕_{R,M}) ≤ L^dec_ε(𝓕_{R,M}) ≤ L^global_ε(𝒞_ε)
= O(ε^{-1/2})`. -/
theorem complexity_chain (R M : ℝ) (hR : 0 < R) (hM : 0 < M) :
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ CB : Finset LTree,
      (∀ T ∈ CB, WF 0 0 T) ∧ (∀ f ∈ FRM R M, ∃ T ∈ CB, supDist f T ≤ ENNReal.ofReal ε) ∧
      (⌈entropyH ε (FRM R M)⌉.toNat : ℕ∞) ≤ Ldec ε (FRM R M) ∧
      Ldec ε (FRM R M) ≤ Lglobal CB ∧ (Lglobal CB : ℝ) ≤ C₁ / Real.sqrt ε := by
  obtain ⟨ε₀, c, C, C₁, hε₀, -, -, hC₁, hmain⟩ := entropy_codebook R M hR hM
  refine ⟨ε₀, C₁, hε₀, hC₁, fun ε hε hε0 => ?_⟩
  obtain ⟨-, -, CB, hWF, hcov, hlog⟩ := hmain ε hε hε0
  exact ⟨CB, hWF, hcov, (description_lower ε (FRM R M)).2.2, Ldec_le_Lglobal CB hcov hε.le, hlog⟩

end Artigo
