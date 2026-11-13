import RequestProject.Entropy
import RequestProject.JointBudget
import RequestProject.DyadicEnvelope
import Pendencias.Extensao
import Pendencias.LeiExata

/-!
# Ponte de regularidade: III.3.15–III.3.18, III.11.2, III.11.3

Os teoremas do `RequestProject` usam `f ∈ C²(ℝ)` (`ContDiff ℝ 2 f`, `deriv (deriv f)`).
O volume pede `f ∈ C²` só no intervalo. Aqui:

* `FRMIcc R M` é a classe `𝓕_{R,M}` do texto: `ContDiffOn ℝ 2 f [0,1]`, `|f| ≤ R` e
  `|f''| ≤ M` em `[0,1]`, com `f''` a segunda derivada unilateral (`derivWithin`);
* `FRM R M ⊆ FRMIcc R M` e, para `f ∈ FRMIcc R M`, `extF f 0 1 ∈ FRM R M` coincide com `f`
  em `[0,1]`;
* erro uniforme, `E_{N,H}`, `H_{ε,N}`, coberturas, `e_f(J)`, `ω_{f''}`, `I(f)`, `E_N^{dia}`,
  `n_f(ε)` e a árvore `uniformTree (jvals f r)` só dependem dos valores em `[0,1]`
  (resp. em `K`), e cada teorema global se transporta por restrição.
-/

namespace Pendencias

open Set Filter Topology Artigo LTree

/-! ## Lemas gerais -/

/-- para `f ∈ C²(ℝ)`, a segunda derivada unilateral em `[a,b]` é `f''` -/
lemma derivWithin2_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b : ℝ} (hab : a < b) {x : ℝ}
    (hx : x ∈ Icc a b) : derivWithin (derivWithin f (Icc a b)) (Icc a b) x = deriv (deriv f) x := by
  have hu := uniqueDiffOn_Icc hab
  have h1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv f) := by
    have : ContDiff ℝ 1 (deriv f) := hf.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  have e : EqOn (derivWithin f (Icc a b)) (deriv f) (Icc a b) := fun y hy =>
    (h1 y).derivWithin (hu y hy)
  rw [derivWithin_congr e (e hx)]
  exact (h2 x).derivWithin (hu x hx)

lemma extF1_of_mem {f : ℝ → ℝ} {α β x : ℝ} (hx : x ∈ Icc α β) : extF1 f α β x = d1 f α β x := by
  unfold extF1; rw [if_neg (not_lt.2 hx.1), if_pos hx.2]

/-- `extF'' = f''` (unilateral) em `[α,β]` -/
lemma deriv2_extF_of_mem {f : ℝ → ℝ} {α β : ℝ} (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β))
    {x : ℝ} (hx : x ∈ Icc α β) : deriv (deriv (extF f α β)) x = d2 f α β x := by
  rw [deriv2_extF hαβ hf, extF2_eq_comp hαβ, clamp_of_mem hx]

/-! ## A classe `𝓕_{R,M}` do texto -/

/-- `𝓕_{R,M} = {f ∈ C²[0,1] : ‖f‖_∞ ≤ R, ‖f''‖_∞ ≤ M}` com `f''` unilateral nos extremos -/
def FRMIcc (R M : ℝ) : Set (ℝ → ℝ) :=
  {f | ContDiffOn ℝ 2 f (Icc 0 1) ∧ (∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ R) ∧
    ∀ x ∈ Icc (0 : ℝ) 1, |derivWithin (derivWithin f (Icc 0 1)) (Icc 0 1) x| ≤ M}

lemma FRM_subset_FRMIcc (R M : ℝ) : FRM R M ⊆ FRMIcc R M := fun f hf =>
  ⟨hf.1.contDiffOn, hf.2.1, fun x hx => by rw [derivWithin2_eq hf.1 one_pos hx]; exact hf.2.2 x hx⟩

lemma extF_mem_FRM {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRMIcc R M) : extF f 0 1 ∈ FRM R M :=
  ⟨extF_contDiff one_pos hf.1, fun x hx => by rw [extF_of_mem hx]; exact hf.2.1 x hx,
    fun x hx => by rw [deriv2_extF_of_mem one_pos hf.1 hx]; exact hf.2.2 x hx⟩

lemma extF_eqOn01 (f : ℝ → ℝ) : EqOn (extF f 0 1) f (Icc 0 1) := fun _ hx => extF_of_mem hx

/-! ## Congruência em `[0,1]` -/

section congr01

variable {f g : ℝ → ℝ}

lemma supDist_congr (h : EqOn f g (Icc 0 1)) (T : LTree) : supDist f T = supDist g T := by
  unfold supDist
  exact iSup_congr fun x => iSup_congr fun hx => by rw [h hx]

lemma jointErr_congr (h : EqOn f g (Icc 0 1)) (N H : ℕ) : jointErr N H f = jointErr N H g := by
  unfold jointErr
  simp_rw [supDist_congr h]

lemma heightFor_congr (h : EqOn f g (Icc 0 1)) (ε : ℝ) (N : ℕ) :
    heightFor ε N f = heightFor ε N g := by
  unfold heightFor
  simp_rw [jointErr_congr h]

lemma jvals_congr {r : ℕ} {j : ℤ} (h : f (cL r j) = g (cL r j)) : jvals f r j = jvals g r j := by
  unfold jvals bnum; rw [h]

lemma interpAtom_congr {V W : ℤ → ℚ} {k : ℕ} {n : ℤ} (h1 : V n = W n) (h2 : V (n + 1) = W (n + 1)) :
    interpAtom V k n = interpAtom W k n := by
  unfold interpAtom; simp only [h1, h2]

/-- `uniformTree V r k m` só usa `V n` para `2^r m ≤ n ≤ 2^r (m+1)` -/
lemma uniformTree_congr' {V W : ℤ → ℚ} : ∀ (r k : ℕ) (m : ℤ),
    (∀ n : ℤ, 2 ^ r * m ≤ n → n ≤ 2 ^ r * (m + 1) → V n = W n) →
    uniformTree V r k m = uniformTree W r k m
  | 0, k, m, h => by
      simp only [uniformTree]
      exact congrArg leaf (interpAtom_congr (h m (by simp) (by simp)) (h (m + 1) (by simp) (by simp)))
  | r + 1, k, m, h => by
      have hP0 : (0 : ℤ) ≤ 2 ^ r := by positivity
      have hP : (2 : ℤ) ^ (r + 1) = 2 * 2 ^ r := by ring
      simp only [uniformTree]
      rw [uniformTree_congr' r (k + 1) (2 * m) (fun n h1 h2 => h n (by rw [hP]; linarith)
          (by rw [hP]; nlinarith)),
        uniformTree_congr' r (k + 1) (2 * m + 1) (fun n h1 h2 => h n (by rw [hP]; nlinarith)
          (by rw [hP]; linarith))]

lemma uniformTree_jvals_congr (h : EqOn f g (Icc 0 1)) (r : ℕ) :
    uniformTree (jvals f r) r 0 0 = uniformTree (jvals g r) r 0 0 :=
  uniformTree_congr' r 0 0 fun n h1 h2 => jvals_congr (h (cL_mem01 (by simpa using h1)
    (by simpa using h2)))

lemma isCover_iff {R M ε : ℝ} {s : Finset (ℝ → ℝ)} :
    IsCover ε (FRMIcc R M) s ↔ IsCover ε (FRM R M) s := by
  constructor
  · exact fun h f hf => h f (FRM_subset_FRMIcc R M hf)
  · intro h f hf
    obtain ⟨g, hg, hx⟩ := h _ (extF_mem_FRM hf)
    exact ⟨g, hg, fun x hx' => by have := hx x hx'; rwa [extF_of_mem hx'] at this⟩

lemma entropyH_FRMIcc (R M ε : ℝ) : entropyH ε (FRMIcc R M) = entropyH ε (FRM R M) := by
  unfold entropyH coverNum
  simp_rw [isCover_iff]

end congr01

/-! ## III.3.15 – III.3.18 -/

/-- **Lema III.3.15** para `f ∈ C²[0,1]`: `‖f'‖_∞ ≤ C₀ = 4R + M/2` (derivada unilateral). -/
theorem derivative_control_Icc {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRMIcc R M) :
    ∀ x ∈ Icc (0 : ℝ) 1, |derivWithin f (Icc 0 1) x| ≤ 4 * R + M / 2 := by
  intro x hx
  have := derivative_control (extF_mem_FRM hf) x hx
  rw [deriv_extF one_pos hf.1, extF1_of_mem hx] at this
  exact this

/-- **Teorema III.3.16** para `f ∈ C²[0,1]` (mesma árvore determinística `uniformTree (jvals f r)`). -/
theorem joint_budget_Icc (R M : ℝ) : ∃ Cb : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ f ∈ FRMIcc R M,
    ∃ T : LTree, T = uniformTree (jvals f r) r 0 0 ∧
      WF 0 0 T ∧ T.numLeaves = 2 ^ r ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |f x - T.eval 0 0 x| ≤ (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2)) ∧
      (T.maxHeight : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 ∧
      Latom T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) ∧
      Lstr T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) ∧
      Lrat T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) := by
  obtain ⟨Cb, hCb⟩ := joint_budget R M
  refine ⟨Cb, fun r hr f hf => ?_⟩
  obtain ⟨T, hT, hw, hn, herr, hh, h1, h2, h3⟩ := hCb r hr _ (extF_mem_FRM hf)
  refine ⟨T, ?_, hw, hn, fun x hx => ?_, hh, h1, h2, h3⟩
  · rw [hT]; exact uniformTree_jvals_congr (extF_eqOn01 f) r
  · have := herr x hx; rwa [extF_of_mem hx] at this

/-- **Teorema III.3.16**, consequência: `E_{N,⌈C_H N²⌉}(f)_∞ < (M+4)/(2N²)` para `N ≥ 2`. -/
theorem joint_all_N_Icc {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRMIcc R M) (N : ℕ) (hN : 2 ≤ N) :
    jointErr N ⌈CH R M * (N : ℝ) ^ 2⌉₊ f < ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2)) := by
  rw [← jointErr_congr (extF_eqOn01 f)]
  exact joint_all_N (extF_mem_FRM hf) N hN

/-- **Corolário III.3.17** para `f ∈ C²[0,1]`. -/
theorem height_for_epsilon_Icc (R M : ℝ) :
    (∀ f ∈ FRMIcc R M, ∀ ε : ℝ, 0 < ε →
      jointErr (nEps M ε) (HEps R M ε) f ≤ ENNReal.ofReal ε ∧
      heightFor ε (nEps M ε) f ≤ HEps R M ε) ∧
    ∃ C : ℝ, ∀ f ∈ FRMIcc R M, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (nEps M ε : ℝ) ≤ C / Real.sqrt ε ∧ (HEps R M ε : ℝ) ≤ C / ε ∧
      ∃ T : LTree, AdmNH (nEps M ε) (HEps R M ε) T ∧ supDist f T ≤ ENNReal.ofReal ε ∧
        (Latom T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) ∧
        (Lstr T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) ∧
        (Lrat T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) := by
  obtain ⟨hA, C, hC⟩ := height_for_epsilon R M
  refine ⟨fun f hf ε hε => ?_, C, fun f hf ε hε hε1 => ?_⟩
  · have := hA _ (extF_mem_FRM hf) ε hε
    rwa [jointErr_congr (extF_eqOn01 f), heightFor_congr (extF_eqOn01 f)] at this
  · obtain ⟨h1, h2, T, hT, hd, hl⟩ := hC _ (extF_mem_FRM hf) ε hε hε1
    rw [supDist_congr (extF_eqOn01 f)] at hd
    exact ⟨h1, h2, T, hT, hd, hl⟩

/-- **Teorema III.3.18** para `𝓕_{R,M} ⊆ C²[0,1]`. -/
theorem entropy_codebook_Icc (R M : ℝ) (hR : 0 < R) (hM : 0 < M) :
    ∃ ε₀ c C C₁ : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 < C ∧ 0 < C₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      c / Real.sqrt ε ≤ entropyH ε (FRMIcc R M) ∧ entropyH ε (FRMIcc R M) ≤ C / Real.sqrt ε ∧
      ∃ CB : Finset LTree, (∀ T ∈ CB, WF 0 0 T) ∧
        (∀ f ∈ FRMIcc R M, ∃ T ∈ CB, supDist f T ≤ ENNReal.ofReal ε) ∧
        (Nat.clog 2 CB.card : ℝ) ≤ C₁ / Real.sqrt ε := by
  obtain ⟨ε₀, c, C, C₁, h0, hc, hC, hC1, h⟩ := entropy_codebook R M hR hM
  refine ⟨ε₀, c, C, C₁, h0, hc, hC, hC1, fun ε hε hε0 => ?_⟩
  obtain ⟨hl, hu, CB, hw, hcov, hcard⟩ := h ε hε hε0
  simp only [entropyH_FRMIcc]
  refine ⟨hl, hu, CB, hw, fun f hf => ?_, hcard⟩
  obtain ⟨T, hT, hd⟩ := hcov _ (extF_mem_FRM hf)
  rw [supDist_congr (extF_eqOn01 f)] at hd
  exact ⟨T, hT, hd⟩

/-! ## III.11.2 e III.11.3 (célula `K = J_{k₀,m₀}`) -/

lemma modCont_congr {g g' : ℝ → ℝ} {S : Set ℝ} (h : EqOn g g' S) (t : ℝ) :
    modCont g S t = modCont g' S t := by
  unfold modCont
  congr 1
  ext d
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, hx, y, hy, hxy, by rw [h hx, h hy]⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, hx, y, hy, hxy, by rw [h hx, h hy]⟩

/-- `I(f) = ∫_K |f''|^{1/2}` com `f''` unilateral em `K` -/
noncomputable def curvIOn (f : ℝ → ℝ) (k : ℕ) (m : ℤ) : ℝ :=
  ∫ x in cL k m..cR k m, Real.sqrt |derivWithin (derivWithin f (cellIcc k m)) (cellIcc k m) x|

section cell

variable {f : ℝ → ℝ} {k₀ : ℕ} {m₀ : ℤ}

lemma eqOn_cell (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) :
    EqOn (extF f (cL k₀ m₀) (cR k₀ m₀)) f (cellIcc k₀ m₀) := fun _ hx => extF_of_mem hx

lemma eqOn_cell_d2 (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    EqOn (deriv (deriv (extF f (cL k₀ m₀) (cR k₀ m₀))))
      (derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀)) (cellIcc k₀ m₀) :=
  fun _ hx => deriv2_extF_of_mem (cL_lt_cR k₀ m₀) hf hx

lemma curvI_extF (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    curvI (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ = curvIOn f k₀ m₀ := by
  unfold curvI curvIOn
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le (cL_lt_cR k₀ m₀).le] at hy
  rw [eqOn_cell_d2 hf hy]

/-- **Lema III.11.2** com `f ∈ C²(K)` (`ContDiffOn`), `f''` e `ω_{f''}` unilaterais em `K`. -/
theorem local_asymptotic_error_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {k : ℕ} {m : ℤ}
    (hJ : cellIcc k m ⊆ cellIcc k₀ m₀) {x : ℝ} (hx : x ∈ cellIcc k m) :
    |locErr f k m -
        |derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀) x| / 8 * (cR k m - cL k m) ^ 2| ≤
      modCont (derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀)) (cellIcc k₀ m₀)
        (cR k m - cL k m) / 8 * (cR k m - cL k m) ^ 2 := by
  have := local_asymptotic_error (extF_contDiff (cL_lt_cR k₀ m₀) hf) hJ hx
  rwa [locErr_congr ((eqOn_cell f k₀ m₀).mono hJ), eqOn_cell_d2 hf (hJ hx),
    modCont_congr (eqOn_cell_d2 hf)] at this

/-- **Teorema III.11.3** com `f ∈ C²(K)`, forma `∀ δ > 0` eventual. -/
theorem general_dyadic_envelope_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hI : 0 < curvIOn f k₀ m₀) :
    (∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      curvIOn f k₀ m₀ / Real.sqrt 8 - δ ≤ Real.sqrt ε * nThr f ε k₀ m₀ ∧
      Real.sqrt ε * nThr f ε k₀ m₀ ≤ curvIOn f k₀ m₀ / Real.sqrt 2 + δ) ∧
    (∀ δ > 0, ∀ᶠ N : ℕ in atTop,
      curvIOn f k₀ m₀ ^ 2 / 8 - δ ≤ (N : ℝ) ^ 2 * Edia f k₀ m₀ N ∧
      (N : ℝ) ^ 2 * Edia f k₀ m₀ N ≤ curvIOn f k₀ m₀ ^ 2 / 2 + δ) := by
  have h := general_dyadic_envelope (extF_contDiff (cL_lt_cR k₀ m₀) hf)
    (k₀ := k₀) (m₀ := m₀) (by rw [curvI_extF hf]; exact hI)
  simp only [curvI_extF hf, nThr_congr (eqOn_cell f k₀ m₀),
    Edia_congr (eqOn_cell f k₀ m₀)] at h
  exact h

/-- **Teorema III.11.3**, forma `liminf`/`limsup`, com `f ∈ C²(K)`. -/
theorem general_dyadic_envelope_liminf_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hI : 0 < curvIOn f k₀ m₀) :
    curvIOn f k₀ m₀ / Real.sqrt 8 ≤
      liminf (fun ε => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] (0 : ℝ)) ∧
    limsup (fun ε => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] (0 : ℝ)) ≤
      curvIOn f k₀ m₀ / Real.sqrt 2 ∧
    curvIOn f k₀ m₀ ^ 2 / 8 ≤ liminf (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop ∧
    limsup (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop ≤ curvIOn f k₀ m₀ ^ 2 / 2 := by
  have h := general_dyadic_envelope_liminf (extF_contDiff (cL_lt_cR k₀ m₀) hf)
    (k₀ := k₀) (m₀ := m₀) (by rw [curvI_extF hf]; exact hI)
  simp only [curvI_extF hf, nThr_congr (eqOn_cell f k₀ m₀),
    Edia_congr (eqOn_cell f k₀ m₀)] at h
  exact h

/-- **Teorema III.11.3**, caso degenerado `I(f) = 0`, com `f ∈ C²(K)`. -/
theorem general_dyadic_envelope_zero_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hI : curvIOn f k₀ m₀ = 0) :
    (∃ α β : ℝ, ∀ x ∈ cellIcc k₀ m₀, f x = α + β * x) ∧
    (∀ ε > 0, nThr f ε k₀ m₀ = 1) ∧ (∀ N : ℕ, 1 ≤ N → Edia f k₀ m₀ N = 0) := by
  obtain ⟨⟨α, β, hαβ⟩, h2, h3⟩ := general_dyadic_envelope_zero
    (extF_contDiff (cL_lt_cR k₀ m₀) hf) (k₀ := k₀) (m₀ := m₀) (by rw [curvI_extF hf]; exact hI)
  simp only [nThr_congr (eqOn_cell f k₀ m₀), Edia_congr (eqOn_cell f k₀ m₀)] at h2 h3
  exact ⟨⟨α, β, fun x hx => by rw [← eqOn_cell f k₀ m₀ hx]; exact hαβ x hx⟩, h2, h3⟩

end cell

end Pendencias
