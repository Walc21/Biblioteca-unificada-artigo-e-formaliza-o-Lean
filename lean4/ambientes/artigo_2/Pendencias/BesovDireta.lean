import Pendencias.Arvores
import Pendencias.Jackson

/-!
# V.6.3 — estimativa direta na escala de Besov

-- ITEM: V.6.3

Para uma célula `K = J_{k₀,m₀}`, `L = |K|`:

* `σ_N^{dia}(f)_∞ = Edia f k₀ m₀ N` (eq. sigma-dyadic do complemento, como em V.6.1);
* `bsemi k₀ m₀ s f = |f|_{B^s_{∞,∞}(K)} = sup_{0 < t ≤ |K|} t^{-s} ω₂(f,t)_{∞,K}`
  (eq. besov-seminorm), em `ENNReal`, com `ω₂ = omega2K` (`Jackson.lean`).

`besov_direct_whitney`: com qualquer constante de Whitney `C_W`,
`σ_N^{dia}(f) ≤ 2^{s+1} C_W L^s |f|_{B^s_{∞,∞}(K)} N^{-s}` (a constante `C_s = 2^{s+1}C_W` da
prova do texto). `besov_direct`: o enunciado do teorema, com `C_s = 2^{s+1}` (`C_W = 1`,
`whitney_one`) e a racionalização.
-/

namespace Pendencias.Jackson

open Set Artigo Pendencias

/-- `|f|_{B^s_{∞,∞}(K)} = sup_{0 < t ≤ |K|} t^{-s} ω₂(f,t)_{∞,K}` (eq. besov-seminorm) -/
noncomputable def bsemi (k0 : ℕ) (m0 : ℤ) (s : ℝ) (f : ℝ → ℝ) : ENNReal :=
  ⨆ t : ℝ, ⨆ (_ : 0 < t ∧ t ≤ cR k0 m0 - cL k0 m0),
    ENNReal.ofReal (t ^ (-s)) * omega2K k0 m0 f t

lemma omega2K_le_bsemi {k0 : ℕ} {m0 : ℤ} {s : ℝ} {f : ℝ → ℝ} (hfin : bsemi k0 m0 s f < ⊤)
    {t : ℝ} (ht : 0 < t ∧ t ≤ cR k0 m0 - cL k0 m0) :
    omega2K k0 m0 f t ≠ ⊤ ∧
      (omega2K k0 m0 f t).toReal ≤ t ^ s * (bsemi k0 m0 s f).toReal := by
  have h1 : ENNReal.ofReal (t ^ (-s)) * omega2K k0 m0 f t ≤ bsemi k0 m0 s f :=
    le_iSup₂_of_le t ht le_rfl
  have hpos : 0 < t ^ (-s) := Real.rpow_pos_of_pos ht.1 _
  have hne : omega2K k0 m0 f t ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hpos).ne'] at h1
    exact (lt_of_le_of_lt h1 hfin).ne rfl
  refine ⟨hne, ?_⟩
  have h2 := ENNReal.toReal_mono hfin.ne h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos.le] at h2
  have e : t ^ s * t ^ (-s) = 1 := by
    rw [← Real.rpow_add ht.1, add_neg_cancel, Real.rpow_zero]
  calc (omega2K k0 m0 f t).toReal = t ^ s * (t ^ (-s) * (omega2K k0 m0 f t).toReal) := by
        rw [← mul_assoc, e, one_mul]
    _ ≤ t ^ s * (bsemi k0 m0 s f).toReal :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht.1.le s)

/-- estimativa local: `‖f - P_J f‖_{∞,J} ≤ 2 C_W |J|^s |f|_{B^s_{∞,∞}(K)}` para `J ⊆ K` -/
lemma locErr_le_besov {CW : ℝ} (hW : IsWhitney CW) {s : ℝ} {k0 : ℕ} {m0 : ℤ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (cellIcc k0 m0)) (hfin : bsemi k0 m0 s f < ⊤) {k : ℕ} {m : ℤ}
    (hsub : cellIcc k m ⊆ cellIcc k0 m0) :
    locErr f k m ≤ 2 * CW * ((cR k m - cL k m) ^ s * (bsemi k0 m0 s f).toReal) := by
  have hab := cL_lt_cR k m
  have hab0 := cL_lt_cR k0 m0
  have hsub' : cL k0 m0 ≤ cL k m ∧ cR k m ≤ cR k0 m0 := (Icc_subset_Icc_iff hab.le).mp hsub
  have hfJ : ContinuousOn f (Icc (cL k m) (cR k m)) := hf.mono hsub
  have ht : 0 < cR k m - cL k m ∧ cR k m - cL k m ≤ cR k0 m0 - cL k0 m0 :=
    ⟨by linarith, by linarith [hsub'.1, hsub'.2]⟩
  obtain ⟨hne, hb⟩ := omega2K_le_bsemi hfin ht
  have hmono : (omega2On (cL k m) (cR k m) f (cR k m - cL k m)).toReal ≤
      (omega2K k0 m0 f (cR k m - cL k m)).toReal :=
    ENNReal.toReal_mono hne (omega2On_mono hsub'.1 hsub'.2 le_rfl f)
  have hCW := hW.1
  refine (locErr_le_iff (hf.mono hsub)).mpr fun x hx => ?_
  calc |f x - linInterp f (cL k m) (cR k m) x|
      ≤ 2 * CW * (omega2On (cL k m) (cR k m) f (cR k m - cL k m)).toReal :=
        interp_le_whitney hW hab hfJ hx
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmono.trans hb) (by positivity)

/-- a malha uniforme de `r = ⌊log₂ N⌋` níveis -/
lemma uniform_treeErr_le_besov {CW : ℝ} (hW : IsWhitney CW) {s : ℝ} (hs : 0 < s) {k0 : ℕ}
    {m0 : ℤ} {f : ℝ → ℝ} (hf : ContinuousOn f (cellIcc k0 m0)) (hfin : bsemi k0 m0 s f < ⊤)
    {N : ℕ} (hN : 2 ≤ N) :
    (DShape.uniform (Nat.log 2 N)).treeErr f k0 m0 ≤
      2 ^ (s + 1) * CW * (cR k0 m0 - cL k0 m0) ^ s * (bsemi k0 m0 s f).toReal *
        (N : ℝ) ^ (-s) := by
  have hL : 0 < cR k0 m0 - cL k0 m0 := sub_pos.mpr (cL_lt_cR k0 m0)
  have hS : 0 ≤ (bsemi k0 m0 s f).toReal := ENNReal.toReal_nonneg
  have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h2' : (N : ℝ) < 2 * 2 ^ Nat.log 2 N := by rw [← pow_succ']; exact_mod_cast h2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine treeErr_uniform_le _ k0 m0 fun i hi => ?_
  have hsub : cellIcc (k0 + Nat.log 2 N) (m0 * 2 ^ Nat.log 2 N + i) ⊆ cellIcc k0 m0 :=
    cell_sub_of_desc (by omega) (by
      rw [show k0 + Nat.log 2 N - k0 = Nat.log 2 N by omega]; exact desc_index m0 _ i hi)
  refine (locErr_le_besov hW hf hfin hsub).trans ?_
  rw [cell_len_desc k0 _ m0]
  have hpow : ((cR k0 m0 - cL k0 m0) / 2 ^ Nat.log 2 N) ^ s ≤
      2 ^ s * (cR k0 m0 - cL k0 m0) ^ s * (N : ℝ) ^ (-s) := by
    have hle : (cR k0 m0 - cL k0 m0) / 2 ^ Nat.log 2 N ≤ 2 * (cR k0 m0 - cL k0 m0) / N := by
      rw [div_le_div_iff₀ (by positivity) hN0]; nlinarith
    calc ((cR k0 m0 - cL k0 m0) / 2 ^ Nat.log 2 N) ^ s
        ≤ (2 * (cR k0 m0 - cL k0 m0) / N) ^ s := Real.rpow_le_rpow (by positivity) hle hs.le
      _ = _ := by
          rw [Real.div_rpow (by positivity) hN0.le, Real.mul_rpow (by norm_num) hL.le,
            Real.rpow_neg hN0.le, div_eq_mul_inv]
  have hCW := hW.1
  calc 2 * CW * (((cR k0 m0 - cL k0 m0) / 2 ^ Nat.log 2 N) ^ s * (bsemi k0 m0 s f).toReal)
      ≤ 2 * CW * (2 ^ s * (cR k0 m0 - cL k0 m0) ^ s * (N : ℝ) ^ (-s) *
          (bsemi k0 m0 s f).toReal) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hS) (by positivity)
    _ = _ := by rw [Real.rpow_add_one (by norm_num)]; ring

/-- **Teorema V.6.3**, cota com constante de Whitney explícita:
`σ_N^{dia}(f)_∞ ≤ 2^{s+1} C_W L^s |f|_{B^s_{∞,∞}(K)} N^{-s}`. -/
theorem besov_direct_whitney {CW : ℝ} (hW : IsWhitney CW) {s : ℝ} (hs : 0 < s) {k0 : ℕ}
    {m0 : ℤ} {f : ℝ → ℝ} (hf : ContinuousOn f (cellIcc k0 m0)) (hfin : bsemi k0 m0 s f < ⊤)
    {N : ℕ} (hN : 2 ≤ N) :
    Edia f k0 m0 N ≤ 2 ^ (s + 1) * CW * (cR k0 m0 - cL k0 m0) ^ s *
      (bsemi k0 m0 s f).toReal * (N : ℝ) ^ (-s) :=
  (Edia_le_treeErr (by
    rw [DShape.numLeaves_uniform]; exact Nat.pow_log_le_self 2 (by omega))).trans
    (uniform_treeErr_le_besov hW hs hf hfin hN)

lemma numLeaves_shapeL : ∀ R : LTree, (shapeL R).numLeaves = R.numLeaves
  | .leaf _ => by simp [shapeL, DShape.numLeaves, LTree.numLeaves, LTree.leaves]
  | .node l r => by
      simp only [shapeL, DShape.numLeaves, LTree.numLeaves_node, numLeaves_shapeL l,
        numLeaves_shapeL r]

/-- **Teorema V.6.3 (estimativa direta).** Se `0 < s < 2`, `|K| = L`, `f ∈ C(K)` e o seminorma
`|f|_{B^s_{∞,∞}(K)}` é finito, então, para `N ≥ 2`,
`σ_N^{dia}(f)_∞ ≤ C_s L^s |f|_{B^s_{∞,∞}(K)} N^{-s}`, com `C_s` (aqui `2^{s+1}`) independente
de `f` e de `N`. Para todo `δ > 0`, uma montagem racional com no máximo `N` folhas alcança o
lado direito acrescido de `δ`. -/
theorem besov_direct {s : ℝ} (hs : 0 < s) (_hs2 : s < 2) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (k0 : ℕ) (m0 : ℤ) (f : ℝ → ℝ), ContinuousOn f (cellIcc k0 m0) →
      bsemi k0 m0 s f < ⊤ → ∀ N : ℕ, 2 ≤ N →
      Edia f k0 m0 N ≤ Cs * (cR k0 m0 - cL k0 m0) ^ s * (bsemi k0 m0 s f).toReal *
        (N : ℝ) ^ (-s) ∧
      ∀ δ : ℝ, 0 < δ → ∃ R : LTree, LTree.WF k0 m0 R ∧ R.numLeaves ≤ N ∧
        ∀ x ∈ cellIcc k0 m0, |f x - R.eval k0 m0 x| <
          Cs * (cR k0 m0 - cL k0 m0) ^ s * (bsemi k0 m0 s f).toReal * (N : ℝ) ^ (-s) + δ := by
  refine ⟨2 ^ (s + 1), by positivity, fun k0 m0 f hf hfin N hN => ⟨?_, fun δ hδ => ?_⟩⟩
  · have := besov_direct_whitney whitney_one hs hf hfin hN
    rwa [mul_one] at this
  · have hT := uniform_treeErr_le_besov whitney_one hs hf hfin hN
    rw [mul_one] at hT
    obtain ⟨R, hWF, hsh, herr⟩ := tree_rationalization hf (DShape.uniform (Nat.log 2 N)) hδ
    refine ⟨R, hWF, ?_, fun x hx => lt_of_lt_of_le (herr x hx) (by linarith)⟩
    rw [← numLeaves_shapeL, hsh, DShape.numLeaves_uniform]
    exact Nat.pow_log_le_self 2 (by omega)

end Pendencias.Jackson
