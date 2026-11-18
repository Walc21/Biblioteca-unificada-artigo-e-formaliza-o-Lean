import RequestProject.DyadicEnvelope
import Pendencias.FaseNucleo
import Pendencias.FaseFuncao
import Pendencias.FaseContagem
import Pendencias.FaseFatou
import Pendencias.FasePontual

/-!
# III.12.7 — a lei de fase para curvatura variável

Esta parte monta o teorema de fase a partir dos lemas de contagem (III.12.6), das propriedades
de `gC`/`gP` (III.12.5) e do lema de Fatou eventual: dada uma sequência `ε_j ↓ 0` cuja fase
`-log₄ ε_j` é congruente, módulo inteiros, a uma sequência que converge a `τ`,

* `∀ δ > 0, ∀ᶠ j, Ψ_f(τ) - δ < √ε_j · n_f(ε_j)` e
* `∀ δ > 0, ∀ᶠ j, √ε_j · n_f(ε_j) < Ψ_f⁺(τ) + δ`.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo DShape

/-- índice da célula de nível `q` que contém `x` (célula semi-aberta à esquerda) -/
noncomputable def cidx (q : ℕ) (x : ℝ) : ℤ := ⌈x * 2 ^ q⌉ - 1

lemma cidx_eq_iff (q : ℕ) (j : ℤ) (x : ℝ) : cidx q x = j ↔ x ∈ Ioc (cL q j) (cR q j) := by
  unfold cidx cL cR
  have hP : (0 : ℝ) < 2 ^ q := by positivity
  rw [show ⌈x * 2 ^ q⌉ - 1 = j ↔ ⌈x * 2 ^ q⌉ = j + 1 by omega, Int.ceil_eq_iff]
  simp only [mem_Ioc, div_lt_iff₀ hP, le_div_iff₀ hP]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

lemma measurable_cidx (q : ℕ) : Measurable (cidx q) :=
  (Int.measurable_ceil.comp (measurable_id.mul_const _)).sub_const 1

lemma measurable_step (q : ℕ) (G : ℤ → ℝ) : Measurable (fun x => G (cidx q x)) :=
  (measurable_from_top (f := G)).comp (measurable_cidx q)

/-- para `x` em `K`, o índice da célula de `x` é `m₀ 2^d + i` com `i < 2^d` -/
lemma cidx_mem {k₀ : ℕ} {m₀ : ℤ} {d : ℕ} {x : ℝ} (hx : x ∈ Ioc (cL k₀ m₀) (cR k₀ m₀)) :
    cidx (k₀ + d) x / 2 ^ d = m₀ := by
  set j := cidx (k₀ + d) x with hj
  have hmem := (cidx_eq_iff (k₀ + d) j x).mp rfl
  have hP : (0 : ℝ) < 2 ^ (k₀ + d) := by positivity
  have hk : (2 : ℝ) ^ (k₀ + d) = 2 ^ k₀ * 2 ^ d := by rw [pow_add]
  have h2k : (0 : ℝ) < 2 ^ k₀ := by positivity
  unfold cL cR at hmem hx
  have h1 : (m₀ : ℝ) * 2 ^ d < j + 1 := by
    have := hx.1
    have h3 := hmem.2
    rw [div_lt_iff₀ h2k] at this
    rw [le_div_iff₀ hP, hk] at h3
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) d]
  have h2 : (j : ℝ) < (m₀ + 1) * 2 ^ d := by
    have := hx.2
    have h3 := hmem.1
    rw [le_div_iff₀ h2k] at this
    rw [div_lt_iff₀ hP, hk] at h3
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) d]
  have h1' : m₀ * 2 ^ d ≤ j := by
    have : m₀ * 2 ^ d < j + 1 := by exact_mod_cast h1
    omega
  have h2' : j < (m₀ + 1) * 2 ^ d := by exact_mod_cast h2
  obtain ⟨i, hi, hji⟩ : ∃ i : ℕ, i < 2 ^ d ∧ j = m₀ * 2 ^ d + i := by
    refine ⟨(j - m₀ * 2 ^ d).toNat, ?_, ?_⟩
    · have : j - m₀ * 2 ^ d < 2 ^ d := by linarith
      have h3 : ((j - m₀ * 2 ^ d).toNat : ℤ) < ((2 ^ d : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by linarith)]; push_cast; exact this
      exact_mod_cast h3
    · rw [Int.toNat_of_nonneg (by linarith)]; ring
  rw [hji]; exact desc_index m₀ d i hi

lemma cidx_index {k₀ : ℕ} {m₀ : ℤ} {d : ℕ} {x : ℝ} (hx : x ∈ Ioc (cL k₀ m₀) (cR k₀ m₀)) :
    ∃ i : ℕ, i < 2 ^ d ∧ cidx (k₀ + d) x = m₀ * 2 ^ d + i :=
  exists_index_of_div (cidx_mem hx)

/-- uma função em degraus sobre `K` é integrável -/
lemma step_intervalIntegrable (k₀ : ℕ) (m₀ : ℤ) (d : ℕ) (G : ℤ → ℝ) :
    IntervalIntegrable (fun x => G (cidx (k₀ + d) x)) volume (cL k₀ m₀) (cR k₀ m₀) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (cL_lt_cR k₀ m₀).le]
  refine Measure.integrableOn_of_bounded (M := ∑ i ∈ Finset.range (2 ^ d), |G (m₀ * 2 ^ d + i)|)
    (by simp) (measurable_step _ G).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun x hx => ?_
  obtain ⟨i, hi, hxi⟩ := cidx_index (d := d) hx
  rw [Real.norm_eq_abs, hxi]
  exact Finset.single_le_sum (f := fun i : ℕ => |G (m₀ * 2 ^ d + i)|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr hi)

/-- a integral de uma função em degraus é a soma de Riemann correspondente -/
lemma step_integral (k₀ : ℕ) (m₀ : ℤ) (d : ℕ) (G : ℤ → ℝ) :
    ∫ x in cL k₀ m₀..cR k₀ m₀, G (cidx (k₀ + d) x) =
      ∑ i ∈ Finset.range (2 ^ d), G (m₀ * 2 ^ d + i) / 2 ^ (k₀ + d) := by
  set q := k₀ + d
  set a : ℕ → ℝ := fun i => cL q (m₀ * 2 ^ d + i) with ha
  have hpt : ∀ i : ℕ, ∀ x ∈ Ioc (a i) (a (i + 1)), cidx q x = m₀ * 2 ^ d + i := by
    intro i x hx
    rw [cidx_eq_iff]
    have : a (i + 1) = cR q (m₀ * 2 ^ d + i) := cL_desc_succ q _ i
    rwa [this] at hx
  have hint : ∀ i : ℕ, i < 2 ^ d → IntervalIntegrable (fun x => G (cidx q x)) volume
      (a i) (a (i + 1)) := by
    intro i hi
    have hle : a i ≤ a (i + 1) := by
      have := cL_lt_cR q (m₀ * 2 ^ d + i)
      rw [show a (i + 1) = cR q (m₀ * 2 ^ d + i) from cL_desc_succ q _ i]; exact this.le
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    exact (integrableOn_const (by simp) (by simp)).congr_fun
      (fun x hx => (by rw [hpt i x hx]))  measurableSet_Ioc
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := fun x => G (cidx q x))
    (μ := volume) (a := a) (n := 2 ^ d) hint
  have h0 : a 0 = cL k₀ m₀ := by simp [a, q, cL_desc_zero]
  have h1 : a (2 ^ d) = cR k₀ m₀ := cL_desc_top k₀ d m₀
  rw [h0, h1] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hlen : a (i + 1) - a i = 1 / 2 ^ q := by
    rw [show a (i + 1) = cR q (m₀ * 2 ^ d + i) from cL_desc_succ q _ i]
    simp only [a]; rw [cell_len]; simp
  have hle : a i ≤ a (i + 1) := by linarith [show (0 : ℝ) < 1 / 2 ^ q by positivity]
  rw [intervalIntegral.integral_of_le hle,
    setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [hpt i x hx]),
    setIntegral_const, Real.volume_real_Ioc_of_le hle, hlen, smul_eq_mul]
  ring

/-- identidade por célula: `√ε · 2^{⌈log₄(A/ε)⌉} = ℓ (s/√8) gC(t + α)` -/
lemma cell_term_eq (k₀ d : ℕ) {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    Real.sqrt ε * (2 : ℝ) ^ (⌈Real.logb 4 (s ^ 2 * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 / ε)⌉) =
      ((2 : ℝ) ^ (k₀ + d))⁻¹ * (s / Real.sqrt 8) *
        gC (-Real.logb 4 ε + Real.logb 4 (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * s ^ 2 / 8)) := by
  set A : ℝ := s ^ 2 * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 with hA
  have hApos : 0 < A := by positivity
  set u := Real.logb 4 (A / ε) with hu
  have hAε : 0 < A / ε := by positivity
  -- `2^{⌈u⌉} = 2^u · gC u`
  have h1 : (2 : ℝ) ^ (⌈u⌉ : ℤ) = (2 : ℝ) ^ u * gC u := by
    unfold gC
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_intCast]
    congr 1; ring
  have h2 : (2 : ℝ) ^ u = Real.sqrt (A / ε) := two_rpow_logb_four hAε
  -- `gC u = gC (t + α)`
  have h3 : gC u = gC (-Real.logb 4 ε + Real.logb 4 (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * s ^ 2 / 8)) := by
    have hX : 0 < ((2 : ℝ) ^ k₀)⁻¹ ^ 2 * s ^ 2 / 8 := by positivity
    have hAd : A = (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * s ^ 2 / 8) / 4 ^ d := by
      simp only [hA]
      rw [pow_add, mul_inv, mul_pow, show (4 : ℝ) ^ d = (2 ^ d) ^ 2 by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      field_simp
    have hlA : Real.logb 4 A = Real.logb 4 (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * s ^ 2 / 8) - d := by
      rw [hAd, Real.logb_div hX.ne' (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      simp
    have hu' : u = (-Real.logb 4 ε + Real.logb 4 (((2 : ℝ) ^ k₀)⁻¹ ^ 2 * s ^ 2 / 8)) + ((-d : ℤ) : ℝ) := by
      rw [hu, Real.logb_div hApos.ne' hε.ne', hlA]; push_cast; ring
    rw [hu', gC_add_int]
  rw [h1, h2, h3]
  have h4 : Real.sqrt ε * Real.sqrt (A / ε) = Real.sqrt A := by
    rw [← Real.sqrt_mul hε.le, mul_div_cancel₀ _ hε.ne']
  have h5 : Real.sqrt A = ((2 : ℝ) ^ (k₀ + d))⁻¹ * (s / Real.sqrt 8) := by
    have hq : (0 : ℝ) < ((2 : ℝ) ^ (k₀ + d))⁻¹ := by positivity
    rw [hA, show s ^ 2 * ((2 : ℝ) ^ (k₀ + d))⁻¹ ^ 2 / 8 = (((2 : ℝ) ^ (k₀ + d))⁻¹ * s) ^ 2 / 8 by ring,
      Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
    ring
  calc Real.sqrt ε * (Real.sqrt (A / ε) * gC _) = (Real.sqrt ε * Real.sqrt (A / ε)) * gC _ := by ring
    _ = _ := by rw [h4, h5]

end Pendencias
