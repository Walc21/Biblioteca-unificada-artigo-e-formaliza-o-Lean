import Pendencias.Interpolacao
import RequestProject.Dyadic

/-!
# V.6.2 — cota assintótica com nós livres

-- ITEM: V.6.2

* `FreeKnots α β N`: partições `α = x₀ < x₁ < ⋯ < x_N = β` de `[α,β]` em `N` subintervalos com
  nós arbitrários;
* `knotErr f x N = max_j ‖f - P_{[x_j,x_{j+1}]} f‖_∞`: erro do interpolante linear por partes
  (`linInterp` em cada subintervalo), em `ENNReal`;
* `Elv f α β N = E_N^{lv}(f)`: o menor erro de interpolação linear com `N` subintervalos e nós
  arbitrários (ínfimo sobre `FreeKnots`).

`free_knots`: para `f ∈ C²[α,β]` (`ContDiffOn`, com `f''` unilateral nos extremos),
`limsup_N N² E_N^{lv}(f) ≤ (1/8)(∫_α^β |f''|^{1/2})²`.
-/

namespace Pendencias.NosLivres

open Set Artigo Filter Topology MeasureTheory Pendencias

/-- partições de `[α,β]` em `N` subintervalos: `α = x₀ < x₁ < ⋯ < x_N = β` -/
def FreeKnots (α β : ℝ) (N : ℕ) : Set (ℕ → ℝ) :=
  {x | x 0 = α ∧ x N = β ∧ ∀ j, j < N → x j < x (j + 1)}

/-- erro uniforme do interpolante linear nos nós `x₀ < ⋯ < x_N` -/
noncomputable def knotErr (f : ℝ → ℝ) (x : ℕ → ℝ) (N : ℕ) : ENNReal :=
  ⨆ j ∈ Finset.range N, ⨆ t ∈ Icc (x j) (x (j + 1)),
    ENNReal.ofReal |f t - linInterp f (x j) (x (j + 1)) t|

/-- `E_N^{lv}(f)`: menor erro de interpolação linear com `N` subintervalos e nós arbitrários -/
noncomputable def Elv (f : ℝ → ℝ) (α β : ℝ) (N : ℕ) : ENNReal :=
  ⨅ x ∈ FreeKnots α β N, knotErr f x N

lemma integral_ge_const {ρ : ℝ → ℝ} (hρ : Continuous ρ) {a b c : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Icc a b, c ≤ ρ t) : c * (b - a) ≤ ∫ t in a..b, ρ t := by
  have h1 : ∫ _t in a..b, c = (b - a) * c := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have h2 := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (μ := volume))
    (hρ.intervalIntegrable a b) h
  rw [h1] at h2
  linarith

/-- equidistribuição: nós com `∫_{x_j}^{x_{j+1}} ρ = (∫_α^β ρ)/N` -/
lemma knots_exist {α β : ℝ} (hab : α < β) {ρ : ℝ → ℝ} (hρc : Continuous ρ) {ρ0 : ℝ}
    (hρ0 : 0 < ρ0) (hρ : ∀ x, ρ0 ≤ ρ x) {N : ℕ} (hN : 1 ≤ N) :
    ∃ x : ℕ → ℝ, x ∈ FreeKnots α β N ∧ (∀ j, x j ∈ Icc α β) ∧
      ∀ j, j < N → ∫ t in (x j)..(x (j + 1)), ρ t = (∫ t in α..β, ρ t) / N := by
  have hint : ∀ a b, IntervalIntegrable ρ volume a b := fun a b => hρc.intervalIntegrable a b
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, ∀ y, G y = ∫ t in α..y, ρ t := ⟨_, fun _ => rfl⟩
  have hGc : Continuous G := by
    have : G = fun y => ∫ t in α..y, ρ t := funext hGdef
    rw [this]; exact intervalIntegral.continuous_primitive hint α
  have hsub : ∀ y z, G z - G y = ∫ t in y..z, ρ t := fun y z => by
    rw [hGdef, hGdef]; exact intervalIntegral.integral_interval_sub_left (hint α z) (hint α y)
  have hGmono : StrictMono G := by
    intro y z hyz
    have h1 := integral_ge_const hρc hyz.le (fun t _ => hρ t)
    have h2 := hsub y z
    have h3 := mul_pos hρ0 (sub_pos.mpr hyz)
    linarith
  have hG0 : G α = 0 := by rw [hGdef]; exact intervalIntegral.integral_same
  have hI : 0 < G β := by have := hGmono hab; rwa [hG0] at this
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hex : ∀ j : ℕ, ∃ y ∈ Icc α β, G y = ((min j N : ℕ) : ℝ) * G β / N := by
    intro j
    have hmem : ((min j N : ℕ) : ℝ) * G β / N ∈ Icc (G α) (G β) := by
      rw [hG0]
      have h1 : ((min j N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right j N
      constructor
      · positivity
      · rw [div_le_iff₀ hN0]; nlinarith
    exact intermediate_value_Icc hab.le hGc.continuousOn hmem
  choose x hxmem hxG using hex
  have hG_j : ∀ j, j ≤ N → G (x j) = (j : ℝ) * G β / N := fun j hj => by
    rw [hxG, min_eq_left hj]
  refine ⟨x, ⟨?_, ?_, ?_⟩, hxmem, fun j hj => ?_⟩
  · apply hGmono.injective; rw [hG_j 0 (Nat.zero_le _), hG0]; simp
  · apply hGmono.injective; rw [hG_j N le_rfl]; field_simp
  · intro j hj
    apply hGmono.lt_iff_lt.mp
    rw [hG_j j hj.le, hG_j (j + 1) hj]
    push_cast
    apply div_lt_div_of_pos_right _ hN0
    nlinarith
  · rw [← hsub, hG_j j hj.le, hG_j (j + 1) hj, ← hGdef β]; push_cast; ring

/-- erro em um subintervalo com `∫_a^b ρ = c`, `|F''| ≤ ρ²` e oscilação relativa `≤ 1 + ε` -/
lemma interp_knot_le {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {ρ : ℝ → ℝ} (hρc : Continuous ρ)
    (hρn : ∀ u, 0 ≤ ρ u) (hρ2 : ∀ u, |deriv (deriv F) u| ≤ ρ u ^ 2) {a b c ε : ℝ} (hab : a < b)
    (hε : 0 < ε) (hc : ∫ t in a..b, ρ t = c)
    (hosc : ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, ρ u ≤ (1 + ε) * ρ t) :
    ∀ x ∈ Icc a b, |F x - linInterp F a b x| ≤ (1 + ε) ^ 2 * c ^ 2 / 8 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hbound : ∀ u ∈ Icc a b, |deriv (deriv F) u| ≤ ((1 + ε) * c / (b - a)) ^ 2 := by
    intro u hu
    have h1 : ρ u / (1 + ε) * (b - a) ≤ ∫ t in a..b, ρ t :=
      integral_ge_const hρc hab.le (fun t ht => by
        rw [div_le_iff₀ (by linarith)]; rw [mul_comm]; exact hosc t ht u hu)
    rw [hc] at h1
    have hρu : ρ u ≤ (1 + ε) * c / (b - a) := by
      rw [le_div_iff₀ hba]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h1
      linarith
    exact (hρ2 u).trans (pow_le_pow_left₀ (hρn u) hρu 2)
  intro x hx
  have := interp_remainder_C2 hF hab hbound x hx
  calc |F x - linInterp F a b x| ≤ (b - a) ^ 2 / 8 * ((1 + ε) * c / (b - a)) ^ 2 := this
    _ = (1 + ε) ^ 2 * c ^ 2 / 8 := by field_simp

lemma sqrt_add_sq_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    Real.sqrt (a + t ^ 2) ≤ Real.sqrt a + t := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sqrt_nonneg a
  nlinarith

/-- **Teorema V.6.2 (cota assintótica com nós livres).** Para `f ∈ C²[α,β]`,
`limsup_{N→∞} N² E_N^{lv}(f) ≤ (1/8)(∫_α^β |f''(x)|^{1/2} dx)²`. -/
theorem free_knots {f : ℝ → ℝ} {α β : ℝ} (hab : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β)) :
    limsup (fun N : ℕ => ENNReal.ofReal ((N : ℝ) ^ 2) * Elv f α β N) atTop ≤
      ENNReal.ofReal (1 / 8 *
        (∫ x in α..β, Real.sqrt |derivWithin (derivWithin f (Icc α β)) (Icc α β) x|) ^ 2) := by
  obtain ⟨F, hFdef⟩ : ∃ F, F = extF f α β := ⟨_, rfl⟩
  have hF : ContDiff ℝ 2 F := by rw [hFdef]; exact extF_contDiff hab hf
  have hg : deriv (deriv F) = extF2 f α β := by rw [hFdef]; exact deriv2_extF hab hf
  have hgc : Continuous (deriv (deriv F)) := by rw [hg]; exact continuous_extF2 hab hf
  have hFf : ∀ x ∈ Icc α β, F x = f x := fun x hx => by rw [hFdef]; exact extF_of_mem hx
  have hI0eq : (∫ x in α..β,
      Real.sqrt |derivWithin (derivWithin f (Icc α β)) (Icc α β) x|) =
      ∫ x in α..β, Real.sqrt |deriv (deriv F) x| := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab.le] at hx
    show Real.sqrt |derivWithin (derivWithin f (Icc α β)) (Icc α β) x| =
      Real.sqrt |deriv (deriv F) x|
    rw [hg, extF2_eq_comp hab, clamp_of_mem hx]; rfl
  rw [hI0eq]
  obtain ⟨I0, hI0⟩ : ∃ I0, I0 = ∫ x in α..β, Real.sqrt |deriv (deriv F) x| := ⟨_, rfl⟩
  rw [← hI0]
  have hsc : Continuous fun x => Real.sqrt |deriv (deriv F) x| :=
    Real.continuous_sqrt.comp hgc.abs
  have hI0n : 0 ≤ I0 := by
    rw [hI0]
    exact intervalIntegral.integral_nonneg hab.le (fun x _ => Real.sqrt_nonneg _)
  have key : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) →
      limsup (fun N : ℕ => ENNReal.ofReal ((N : ℝ) ^ 2) * Elv f α β N) atTop ≤
        ENNReal.ofReal (1 / 8 * ((1 + t) * (I0 + t * (β - α))) ^ 2) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ → ℝ, ∀ x, ρ x = Real.sqrt (|deriv (deriv F) x| + t ^ 2) :=
      ⟨_, fun _ => rfl⟩
    have hρc : Continuous ρ := by
      have : ρ = fun x => Real.sqrt (|deriv (deriv F) x| + t ^ 2) := funext hρdef
      rw [this]; exact Real.continuous_sqrt.comp (hgc.abs.add continuous_const)
    have hρn : ∀ u, 0 ≤ ρ u := fun u => by rw [hρdef]; exact Real.sqrt_nonneg _
    have hρt : ∀ u, t ≤ ρ u := fun u => by
      rw [hρdef]
      calc t = Real.sqrt (t ^ 2) := (Real.sqrt_sq ht0.le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by linarith [abs_nonneg (deriv (deriv F) u)])
    have hρ2 : ∀ u, |deriv (deriv F) u| ≤ ρ u ^ 2 := fun u => by
      rw [hρdef, Real.sq_sqrt (by positivity)]; nlinarith
    have hρle : ∀ u, ρ u ≤ Real.sqrt |deriv (deriv F) u| + t := fun u => by
      rw [hρdef]; exact sqrt_add_sq_le (abs_nonneg _) ht0.le
    obtain ⟨I, hIdef⟩ : ∃ I, I = ∫ x in α..β, ρ x := ⟨_, rfl⟩
    have hIle : I ≤ I0 + t * (β - α) := by
      have h1 := intervalIntegral.integral_mono_on (μ := volume) hab.le (hρc.intervalIntegrable α β)
        ((hsc.add continuous_const).intervalIntegrable α β) (fun x _ => hρle x)
      simp only [Pi.add_apply] at h1
      rw [intervalIntegral.integral_add (hsc.intervalIntegrable α β)
          (intervalIntegrable_const (μ := volume)),
        intervalIntegral.integral_const, smul_eq_mul] at h1
      rw [hIdef, hI0]; linarith
    have hIpos : 0 < I := by
      have h1 := integral_ge_const hρc hab.le (fun x _ => hρt x)
      rw [hIdef]
      exact lt_of_lt_of_le (mul_pos ht0 (sub_pos.mpr hab)) h1
    -- continuidade uniforme de `ρ` em `[α,β]`
    have huc := (isCompact_Icc (a := α) (b := β)).uniformContinuousOn_of_continuous
      hρc.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, hδρ⟩ := huc (t * t) (mul_pos ht0 ht0)
    refine limsup_le_of_le (h := eventually_atTop.mpr ⟨max 1 (⌈I / (t * δ)⌉₊ + 1), fun N hN => ?_⟩)
    have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNbig : I / (t * δ) < N := by
      have h1 : ⌈I / (t * δ)⌉₊ + 1 ≤ N := (le_max_right _ _).trans hN
      have h2 : ((⌈I / (t * δ)⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
      push_cast at h2
      linarith [Nat.le_ceil (I / (t * δ))]
    obtain ⟨x, hxK, hxmem, hxint⟩ := knots_exist hab hρc ht0 hρt hN1
    have hbound : knotErr f x N ≤ ENNReal.ofReal ((1 + t) ^ 2 * (I / N) ^ 2 / 8) := by
      refine iSup₂_le fun j hj => iSup₂_le fun y hy => ENNReal.ofReal_le_ofReal ?_
      have hjN : j < N := Finset.mem_range.mp hj
      have hlt := hxK.2.2 j hjN
      have ha := hxmem j
      have hb := hxmem (j + 1)
      have hint := hxint j hjN
      rw [← hIdef] at hint
      have hlen : x (j + 1) - x j < δ := by
        have h1 := integral_ge_const hρc hlt.le (fun u _ => hρt u)
        rw [hint] at h1
        rw [div_lt_iff₀ (mul_pos ht0 hδ)] at hNbig
        have h2 : t * (x (j + 1) - x j) * N ≤ I := by
          rw [le_div_iff₀ hN0] at h1; exact h1
        by_contra hcon
        push_neg at hcon
        have h3 : t * δ * N ≤ t * (x (j + 1) - x j) * N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcon ht0.le) hN0.le
        nlinarith
      have hosc : ∀ u ∈ Icc (x j) (x (j + 1)), ∀ v ∈ Icc (x j) (x (j + 1)),
          ρ v ≤ (1 + t) * ρ u := by
        intro u hu v hv
        have hu' : u ∈ Icc α β := ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
        have hv' : v ∈ Icc α β := ⟨ha.1.trans hv.1, hv.2.trans hb.2⟩
        have hd : dist v u < δ := by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]
        have := hδρ v hv' u hu' hd
        rw [Real.dist_eq, abs_lt] at this
        nlinarith [hρt u, this.2]
      have hy' : y ∈ Icc α β := ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩
      have hmain := interp_knot_le hF hρc hρn hρ2 hlt ht0 hint hosc y hy
      unfold linInterp at hmain ⊢
      rw [hFf y hy', hFf _ ha, hFf _ hb] at hmain
      exact hmain
    have hElv : Elv f α β N ≤ ENNReal.ofReal ((1 + t) ^ 2 * (I / N) ^ 2 / 8) :=
      (iInf₂_le x hxK).trans hbound
    calc ENNReal.ofReal ((N : ℝ) ^ 2) * Elv f α β N
        ≤ ENNReal.ofReal ((N : ℝ) ^ 2) * ENNReal.ofReal ((1 + t) ^ 2 * (I / N) ^ 2 / 8) :=
          mul_le_mul_right hElv _
      _ = ENNReal.ofReal (1 / 8 * ((1 + t) * I) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : (1 + t) * I ≤ (1 + t) * (I0 + t * (β - α)) :=
            mul_le_mul_of_nonneg_left hIle (by linarith)
          have h2 : 0 ≤ (1 + t) * I := by positivity
          nlinarith [pow_le_pow_left₀ h2 h1 2]
  have htend : Tendsto (fun t : ℝ => ENNReal.ofReal (1 / 8 * ((1 + t) * (I0 + t * (β - α))) ^ 2))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (1 / 8 * I0 ^ 2))) := by
    have hc : Continuous (fun t : ℝ =>
        ENNReal.ofReal (1 / 8 * ((1 + t) * (I0 + t * (β - α))) ^ 2)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have := hc.tendsto 0
    simp only [add_zero, zero_mul, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall key)

end Pendencias.NosLivres
