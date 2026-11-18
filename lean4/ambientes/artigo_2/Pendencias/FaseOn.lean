import Pendencias.FaseExtremos
import Pendencias.Ponte
import Pendencias.FaseContagem

/-!
# III.12.5–12.8 com `f ∈ C²(K)` (`ContDiffOn`), derivadas unilaterais em `K`

`PsiFOn`/`PsiPOn` usam `f''` = `derivWithin (derivWithin f K) K`. As versões abaixo seguem das
versões em `ℝ` aplicadas à extensão `extF f` (de classe `C²` em `ℝ`, igual a `f` em `K`).
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

/-- `f''` unilateral em `K = J_{k₀,m₀}` -/
noncomputable def d2On (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (x : ℝ) : ℝ :=
  derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀) x

/-- `Ψ_f` com `f ∈ C²(K)` -/
noncomputable def PsiFOn (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : ℝ :=
  ∫ x in cL k₀ m₀..cR k₀ m₀, Real.sqrt (|d2On f k₀ m₀ x| / 8) *
    gC (t + Real.logb 4 ((cR k₀ m₀ - cL k₀ m₀) ^ 2 * |d2On f k₀ m₀ x| / 8))

/-- `Ψ_f⁺` com `f ∈ C²(K)` -/
noncomputable def PsiPOn (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : ℝ :=
  ∫ x in cL k₀ m₀..cR k₀ m₀, Real.sqrt (|d2On f k₀ m₀ x| / 8) *
    gP (t + Real.logb 4 ((cR k₀ m₀ - cL k₀ m₀) ^ 2 * |d2On f k₀ m₀ x| / 8))

/-- fases atômicas de `μ_f` (via a extensão `C²`) -/
def IsAtomPhaseOn (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (t : ℝ) : Prop :=
  IsAtomPhase (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ t

/-- `|f''| ∈ c₀ 4^ℤ` q.t.p. em `{f'' ≠ 0}` (com `f''` unilateral) -/
def FourPowersOn (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᵐ x ∂(volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))),
    d2On f k₀ m₀ x ≠ 0 → ∃ z : ℤ, |d2On f k₀ m₀ x| = c₀ * (4 : ℝ) ^ z

section on

variable {f : ℝ → ℝ} {k₀ : ℕ} {m₀ : ℤ}

lemma d2On_eq (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {x : ℝ} (hx : x ∈ cellIcc k₀ m₀) :
    deriv (deriv (extF f (cL k₀ m₀) (cR k₀ m₀))) x = d2On f k₀ m₀ x :=
  eqOn_cell_d2 hf hx

lemma extF_cell_contDiff (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    ContDiff ℝ 2 (extF f (cL k₀ m₀) (cR k₀ m₀)) := extF_contDiff (cL_lt_cR k₀ m₀) hf

lemma psiFOn_eq (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    PsiF (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ t = PsiFOn f k₀ m₀ t := by
  unfold PsiF PsiFOn wPh aPh
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le (cL_lt_cR k₀ m₀).le] at hy
  rw [d2On_eq hf hy]

lemma psiPOn_eq (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    PsiP (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ t = PsiPOn f k₀ m₀ t := by
  unfold PsiP PsiPOn wPh aPh
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le (cL_lt_cR k₀ m₀).le] at hy
  rw [d2On_eq hf hy]

lemma psiFOn_funext (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    PsiF (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ = PsiFOn f k₀ m₀ := funext (psiFOn_eq hf)

lemma psiPOn_funext (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    PsiP (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ = PsiPOn f k₀ m₀ := funext (psiPOn_eq hf)

/-- limites inferior/superior de `Ψ` -/
theorem psiFOn_ge (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    curvIOn f k₀ m₀ / Real.sqrt 8 ≤ PsiFOn f k₀ m₀ t := by
  have := psiF_ge (extF_cell_contDiff hf) k₀ m₀ t
  rwa [curvI_extF hf, psiFOn_eq hf] at this

theorem psiFOn_le_psiPOn (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    PsiFOn f k₀ m₀ t ≤ PsiPOn f k₀ m₀ t := by
  have := psiF_le_psiP (extF_cell_contDiff hf) k₀ m₀ t
  rwa [psiFOn_eq hf, psiPOn_eq hf] at this

theorem psiPOn_le (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    PsiPOn f k₀ m₀ t ≤ 2 * (curvIOn f k₀ m₀ / Real.sqrt 8) := by
  have := psiP_le (extF_cell_contDiff hf) k₀ m₀ t
  rwa [curvI_extF hf, psiPOn_eq hf] at this

theorem psiFOn_periodic (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    PsiFOn f k₀ m₀ (t + 1) = PsiFOn f k₀ m₀ t := by
  rw [← psiFOn_eq hf, ← psiFOn_eq hf]; exact psiF_periodic k₀ m₀ t

theorem psiPOn_periodic (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    PsiPOn f k₀ m₀ (t + 1) = PsiPOn f k₀ m₀ t := by
  rw [← psiPOn_eq hf, ← psiPOn_eq hf]; exact psiP_periodic k₀ m₀ t

theorem exists_min_psiFOn (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    ∃ t₀, ∀ t, PsiFOn f k₀ m₀ t₀ ≤ PsiFOn f k₀ m₀ t := by
  have := exists_min_psiF (extF_cell_contDiff hf) k₀ m₀
  rwa [psiFOn_funext hf] at this

theorem exists_max_psiPOn (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    ∃ t₁, ∀ t, PsiPOn f k₀ m₀ t ≤ PsiPOn f k₀ m₀ t₁ := by
  have := exists_max_psiP (extF_cell_contDiff hf) k₀ m₀
  rwa [psiPOn_funext hf] at this

theorem psiFOn_lsc (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    LowerSemicontinuous (PsiFOn f k₀ m₀) := by
  have := psiF_lsc (extF_cell_contDiff hf) k₀ m₀
  rwa [psiFOn_funext hf] at this

theorem psiPOn_usc (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    UpperSemicontinuous (PsiPOn f k₀ m₀) := by
  have := psiP_usc (extF_cell_contDiff hf) k₀ m₀
  rwa [psiPOn_funext hf] at this

theorem psiFOn_tendsto_left (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    Tendsto (PsiFOn f k₀ m₀) (𝓝[<] t) (𝓝 (PsiFOn f k₀ m₀ t)) := by
  have := psiF_tendsto_left (extF_cell_contDiff hf) k₀ m₀ t
  rwa [psiFOn_funext hf] at this

theorem psiFOn_tendsto_right (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    Tendsto (PsiFOn f k₀ m₀) (𝓝[>] t) (𝓝 (PsiPOn f k₀ m₀ t)) := by
  have := psiF_tendsto_right (extF_cell_contDiff hf) k₀ m₀ t
  rwa [psiFOn_funext hf, psiPOn_eq hf] at this

theorem psiPOn_tendsto_left (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    Tendsto (PsiPOn f k₀ m₀) (𝓝[<] t) (𝓝 (PsiFOn f k₀ m₀ t)) := by
  have := psiP_tendsto_left (extF_cell_contDiff hf) k₀ m₀ t
  rwa [psiPOn_funext hf, psiFOn_eq hf] at this

theorem psiPOn_tendsto_right (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) (t : ℝ) :
    Tendsto (PsiPOn f k₀ m₀) (𝓝[>] t) (𝓝 (PsiPOn f k₀ m₀ t)) := by
  have := psiP_tendsto_right (extF_cell_contDiff hf) k₀ m₀ t
  rwa [psiPOn_funext hf] at this

/-- **III.12.5(iii)**, média -/
theorem integral_psiFOn (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    ∫ t in (0 : ℝ)..1, PsiFOn f k₀ m₀ t = curvIOn f k₀ m₀ / (Real.sqrt 8 * Real.log 2) := by
  have := integral_psiF (extF_cell_contDiff hf) k₀ m₀
  rwa [curvI_extF hf, psiFOn_funext hf] at this

/-- **III.12.7(i)** -/
theorem phase_law_nonatom_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {ε : ℕ → ℝ}
    (hε0 : ∀ j, 0 < ε j) (hε : Tendsto ε atTop (𝓝 0)) {z : ℕ → ℤ} {τ : ℝ}
    (hτ : ¬ IsAtomPhaseOn f k₀ m₀ τ)
    (hz : Tendsto (fun j => -Real.logb 4 (ε j) - z j) atTop (𝓝 τ)) :
    Tendsto (fun j => Real.sqrt (ε j) * nThr f (ε j) k₀ m₀) atTop (𝓝 (PsiFOn f k₀ m₀ τ)) := by
  have := phase_law_nonatom (extF_cell_contDiff hf) k₀ m₀ hε0 hε hτ hz
  simpa only [nThr_congr (eqOn_cell f k₀ m₀), psiFOn_eq hf] using this

/-- **III.12.7(ii)** -/
theorem phase_law_uniform_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hno : ∀ t, ¬ IsAtomPhaseOn f k₀ m₀ t) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      |Real.sqrt ε * nThr f ε k₀ m₀ - PsiFOn f k₀ m₀ (-Real.logb 4 ε)| < δ := by
  have := phase_law_uniform (extF_cell_contDiff hf) k₀ m₀ hno
  simpa only [nThr_congr (eqOn_cell f k₀ m₀), psiFOn_eq hf] using this

/-- **III.12.7(iii)**: cota inferior -/
theorem phase_liminf_ge_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {m : ℝ}
    (hm : ∀ t, m ≤ PsiFOn f k₀ m₀ t) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), m - δ < Real.sqrt ε * nThr f ε k₀ m₀ := by
  have := phase_liminf_ge (extF_cell_contDiff hf) k₀ m₀ (m := m)
    (fun t => by rw [psiFOn_eq hf]; exact hm t)
  simpa only [nThr_congr (eqOn_cell f k₀ m₀)] using this

/-- **III.12.7(iii)**: cota superior -/
theorem phase_limsup_le_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {M : ℝ}
    (hM : ∀ t, PsiPOn f k₀ m₀ t ≤ M) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sqrt ε * nThr f ε k₀ m₀ < M + δ := by
  have := phase_limsup_le (extF_cell_contDiff hf) k₀ m₀ (M := M)
    (fun t => by rw [psiPOn_eq hf]; exact hM t)
  simpa only [nThr_congr (eqOn_cell f k₀ m₀)] using this

/-- **III.12.8(a)** -/
theorem phase_cluster_set_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {t₀ t₁ : ℝ}
    (h0 : ∀ t, PsiFOn f k₀ m₀ t₀ ≤ PsiFOn f k₀ m₀ t)
    (h1 : ∀ t, PsiPOn f k₀ m₀ t ≤ PsiPOn f k₀ m₀ t₁) :
    {c : ℝ | MapClusterPt c atTop (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N)} =
      Icc (PsiFOn f k₀ m₀ t₀ ^ 2) (PsiPOn f k₀ m₀ t₁ ^ 2) := by
  have := phase_cluster_set (extF_cell_contDiff hf) k₀ m₀ (t₀ := t₀) (t₁ := t₁)
    (fun t => by rw [psiFOn_eq hf, psiFOn_eq hf]; exact h0 t)
    (fun t => by rw [psiPOn_eq hf, psiPOn_eq hf]; exact h1 t)
  simpa only [Edia_congr (eqOn_cell f k₀ m₀), psiFOn_eq hf, psiPOn_eq hf] using this

/-- **III.12.8(b)**: limite existe ⟺ `Ψ_f` constante -/
theorem limit_iff_const_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    (∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop (𝓝 L)) ↔
      ∃ c : ℝ, ∀ t, PsiFOn f k₀ m₀ t = c := by
  have := limit_iff_const (extF_cell_contDiff hf) k₀ m₀
  simpa only [Edia_congr (eqOn_cell f k₀ m₀), psiFOn_eq hf] using this

/-- **III.12.8(b)**: valores sob `Ψ` constante -/
theorem limit_of_const_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {c : ℝ}
    (hc : ∀ t, PsiFOn f k₀ m₀ t = c) :
    c = curvIOn f k₀ m₀ / (Real.sqrt 8 * Real.log 2) ∧
    Tendsto (fun ε : ℝ => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] 0) (𝓝 c) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop (𝓝 (c ^ 2)) := by
  have hc' : ∀ t, PsiF (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ t = c := fun t => by
    rw [psiFOn_eq hf]; exact hc t
  have h1 := const_value (extF_cell_contDiff hf) k₀ m₀ hc'
  have h2 := limit_of_const (extF_cell_contDiff hf) k₀ m₀ hc'
  rw [curvI_extF hf] at h1
  simp only [nThr_congr (eqOn_cell f k₀ m₀), Edia_congr (eqOn_cell f k₀ m₀)] at h2
  exact ⟨h1, h2⟩

/-- **III.12.8(c)**: média universal de fase -/
theorem phase_average_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    Tendsto (fun T : ℝ => ∫ t in T..T + 1, (2 : ℝ) ^ (-t) * nThr f ((4 : ℝ) ^ (-t)) k₀ m₀)
      atTop (𝓝 (curvIOn f k₀ m₀ / (Real.sqrt 8 * Real.log 2))) := by
  have := phase_average (extF_cell_contDiff hf) k₀ m₀
  simpa only [nThr_congr (eqOn_cell f k₀ m₀), curvI_extF hf] using this

lemma fourPowers_iff_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) :
    FourPowers (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ ↔ FourPowersOn f k₀ m₀ := by
  have hae : ∀ᵐ x ∂(volume.restrict (Ioc (cL k₀ m₀) (cR k₀ m₀))),
      deriv (deriv (extF f (cL k₀ m₀) (cR k₀ m₀))) x = d2On f k₀ m₀ x := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun x hx => d2On_eq hf (Ioc_subset_Icc_self (by simpa using hx))
  unfold FourPowers FourPowersOn
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [h, hae] with x hx he hne
    rw [← he] at hne ⊢
    exact hx hne
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    filter_upwards [h, hae] with x hx he hne
    rw [he] at hne ⊢
    exact hx hne

/-- **III.12.8(d)** -/
theorem extremes_iff_fourPowers_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {t₀ t₁ : ℝ}
    (h0 : ∀ t, PsiFOn f k₀ m₀ t₀ ≤ PsiFOn f k₀ m₀ t)
    (h1 : ∀ t, PsiPOn f k₀ m₀ t ≤ PsiPOn f k₀ m₀ t₁) :
    (PsiFOn f k₀ m₀ t₀ = curvIOn f k₀ m₀ / Real.sqrt 8 ↔ FourPowersOn f k₀ m₀) ∧
    (PsiPOn f k₀ m₀ t₁ = 2 * (curvIOn f k₀ m₀ / Real.sqrt 8) ↔ FourPowersOn f k₀ m₀) := by
  have := extremes_iff_fourPowers (extF_cell_contDiff hf) k₀ m₀ (t₀ := t₀) (t₁ := t₁)
    (fun t => by rw [psiFOn_eq hf, psiFOn_eq hf]; exact h0 t)
    (fun t => by rw [psiPOn_eq hf, psiPOn_eq hf]; exact h1 t)
  simpa only [curvI_extF hf, psiFOn_eq hf, psiPOn_eq hf, fourPowers_iff_on hf] using this

end on

/-- sub-células: `J_{k',m'} ⊆ J_{k,m}` quando `m' / 2^(k'-k) = m` -/
lemma cellIcc_sub_of_div {k k' : ℕ} {m m' : ℤ} (hkk : k ≤ k') (h : m' / 2 ^ (k' - k) = m) :
    cellIcc k' m' ⊆ cellIcc k m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkk
  rw [Nat.add_sub_cancel_left] at h
  have h1 : m * 2 ^ n ≤ m' := by
    have := Int.ediv_mul_le m' (pow_ne_zero n (by norm_num : (2:ℤ) ≠ 0))
    rw [h] at this; exact this
  have h2 : m' < (m + 1) * 2 ^ n := by
    have := Int.lt_ediv_add_one_mul_self m' (pow_pos (by norm_num : (0:ℤ) < 2) n)
    rw [h] at this; linarith
  have hR1 : (m : ℝ) * 2 ^ n ≤ m' := by exact_mod_cast h1
  have hR2 : (m' : ℝ) + 1 ≤ ((m : ℝ) + 1) * 2 ^ n := by
    have : m' + 1 ≤ (m + 1) * 2 ^ n := h2
    exact_mod_cast this
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  rintro x ⟨hx1, hx2⟩
  unfold cellIcc at *
  rw [Set.mem_Icc]
  constructor
  · refine le_trans ?_ hx1
    rw [div_le_div_iff₀ hk (by positivity), pow_add]
    nlinarith [mul_le_mul_of_nonneg_right hR1 hk.le]
  · refine le_trans hx2 ?_
    rw [div_le_div_iff₀ (by positivity) hk, pow_add]
    nlinarith [mul_le_mul_of_nonneg_right hR2 hk.le]

section countOn

variable {f : ℝ → ℝ} {k₀ : ℕ} {m₀ : ℤ}

/-- **III.12.6(a), `C²(K)`**: cota superior com tetos -/
theorem upper_count_pow_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {d : ℕ}
    {Mv : ℤ → ℝ} (hM0 : ∀ j, 0 ≤ Mv j)
    (hM : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j, |d2On f k₀ m₀ y| ≤ Mv j)
    {ε : ℝ} (hε : 0 < ε) :
    (nThr f ε k₀ m₀ : ℝ) ≤ ∑ i ∈ Finset.range (2 ^ d),
      (2 : ℝ) ^ thrDepth (Mv (m₀ * 2 ^ d + i) * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8) ε := by
  have hsub : ∀ j : ℤ, j / 2 ^ d = m₀ → cellIcc (k₀ + d) j ⊆ cellIcc k₀ m₀ := fun j hj =>
    cellIcc_sub_of_div (Nat.le_add_right k₀ d) (by rwa [Nat.add_sub_cancel_left])
  have hup := upper_count_pow (extF_cell_contDiff hf) hM0 (fun j hj y hy => by
    rw [d2On_eq hf (hsub j hj hy)]; exact hM j hj y hy) hε
  rw [nThr_congr (eqOn_cell f k₀ m₀) ε] at hup
  exact hup

/-- **III.12.6(b), `C²(K)`**: cota inferior com tetos -/
theorem lower_count_pow_on (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀)) {d : ℕ} {μ : ℤ → ℝ}
    (hμ : ∀ j : ℤ, j / 2 ^ d = m₀ → ∀ y ∈ cellIcc (k₀ + d) j, μ j ≤ |d2On f k₀ m₀ y|)
    {ε : ℝ} (hε : 0 < ε)
    (hanc : ∀ k' : ℕ, k₀ ≤ k' → k' < k₀ + d → ∀ i : ℕ, i < 2 ^ d → 0 < μ (m₀ * 2 ^ d + i) →
      ε < locErr f k' ((m₀ * 2 ^ d + i) / 2 ^ (k₀ + d - k')))
    {T : DShape} (hT : T.treeErr f k₀ m₀ ≤ ε) :
    ∑ i ∈ Finset.range (2 ^ d), (if 0 < μ (m₀ * 2 ^ d + i) then
        (2 : ℝ) ^ (⌈Real.logb 4 (μ (m₀ * 2 ^ d + i) * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉)
      else 0) ≤ T.numLeaves := by
  have hsub : ∀ j : ℤ, j / 2 ^ d = m₀ → cellIcc (k₀ + d) j ⊆ cellIcc k₀ m₀ := fun j hj =>
    cellIcc_sub_of_div (Nat.le_add_right k₀ d) (by rwa [Nat.add_sub_cancel_left])
  have hanc' : ∀ k' : ℕ, k₀ ≤ k' → k' < k₀ + d → ∀ i : ℕ, i < 2 ^ d → 0 < μ (m₀ * 2 ^ d + i) →
      ε < locErr (extF f (cL k₀ m₀) (cR k₀ m₀)) k' ((m₀ * 2 ^ d + i) / 2 ^ (k₀ + d - k')) := by
    intro k' h1 h2 i hi hpos
    have hdiv : ((m₀ * 2 ^ d + i) / 2 ^ (k₀ + d - k')) / 2 ^ (k' - k₀) = m₀ := by
      have hd : (k₀ + d - k') + (k' - k₀) = d := by omega
      have hi' : (0 : ℤ) ≤ i := by positivity
      have hi2 : (i : ℤ) < 2 ^ d := by exact_mod_cast hi
      rw [Int.ediv_ediv_of_nonneg (by positivity), ← pow_add, hd, add_comm,
        Int.add_mul_ediv_right _ _ (by positivity), Int.ediv_eq_zero_of_lt hi' hi2, zero_add]
    have hs := cellIcc_sub_of_div h1 hdiv
    rw [locErr_congr ((eqOn_cell f k₀ m₀).mono hs)]
    exact hanc k' h1 h2 i hi hpos
  have hT' : T.treeErr (extF f (cL k₀ m₀) (cR k₀ m₀)) k₀ m₀ ≤ ε := by
    rw [treeErr_congr T k₀ m₀ (eqOn_cell f k₀ m₀)]; exact hT
  exact lower_count_pow (extF_cell_contDiff hf) (μ := μ) (fun j hj y hy => by
    rw [d2On_eq hf (hsub j hj hy)]; exact hμ j hj y hy) hε hanc' hT'

end countOn

end Pendencias
