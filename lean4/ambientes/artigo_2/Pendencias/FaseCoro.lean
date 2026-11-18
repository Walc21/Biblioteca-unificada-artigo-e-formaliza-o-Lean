import Pendencias.FaseMedia

/-!
# III.12.8(b) — o limite existe se, e somente se, `Ψ_f` é constante
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

/-- unicidade do ponto de acumulação de uma sequência convergente -/
lemma mapClusterPt_eq_of_tendsto {u : ℕ → ℝ} {c L : ℝ} (hc : MapClusterPt c atTop u)
    (hL : Tendsto u atTop (𝓝 L)) : c = L := by
  by_contra hne
  obtain ⟨U, V, hU, hV, hcU, hLV, hUV⟩ := t2_separation hne
  have h1 := (mapClusterPt_iff_frequently.mp hc) U (hU.mem_nhds hcU)
  have h2 := hL.eventually (hV.mem_nhds hLV)
  obtain ⟨N, hN1, hN2⟩ := (h1.and_eventually h2).exists
  exact (disjoint_left.mp hUV hN1) hN2

section coro

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
/-- se `Ψ_f ≡ c`, então `Ψ_f⁺ ≡ c` -/
lemma psiP_eq_of_const {c : ℝ} (hc : ∀ t, PsiF f k₀ m₀ t = c) (t : ℝ) : PsiP f k₀ m₀ t = c := by
  have h := psiF_tendsto_right hf k₀ m₀ t
  have h2 : Tendsto (PsiF f k₀ m₀) (𝓝[>] t) (𝓝 c) := by
    have : PsiF f k₀ m₀ = fun _ => c := funext hc
    rw [this]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h h2

include hf in
/-- `Ψ_f ≡ c` implica `c = I/(√8 ln 2)` -/
lemma const_value {c : ℝ} (hc : ∀ t, PsiF f k₀ m₀ t = c) :
    c = curvI f k₀ m₀ / (Real.sqrt 8 * Real.log 2) := by
  rw [← integral_psiF hf k₀ m₀]
  have : PsiF f k₀ m₀ = fun _ => c := funext hc
  rw [this]; simp

include hf in
/-- **III.12.8(b), lei do limite sob `Ψ` constante** -/
theorem limit_of_const {c : ℝ} (hc : ∀ t, PsiF f k₀ m₀ t = c) :
    Tendsto (fun ε : ℝ => Real.sqrt ε * nThr f ε k₀ m₀) (𝓝[>] 0) (𝓝 c) ∧
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop (𝓝 (c ^ 2)) := by
  have hP := psiP_eq_of_const hf k₀ m₀ hc
  have hc0 : 0 ≤ c := by
    have := psiF_ge hf k₀ m₀ 0
    rw [hc] at this
    refine le_trans ?_ this
    refine div_nonneg ?_ (Real.sqrt_nonneg _)
    exact intervalIntegral.integral_nonneg (cL_lt_cR k₀ m₀).le fun x _ => Real.sqrt_nonneg _
  refine ⟨tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩, ?_⟩
  · have := phase_liminf_ge hf k₀ m₀ (m := c) (fun t => (hc t).ge) (c - a) (by linarith)
    filter_upwards [this] with ε h; linarith
  · have := phase_limsup_le hf k₀ m₀ (M := c) (fun t => (hP t).le) (a - c) (by linarith)
    filter_upwards [this] with ε h; linarith
  · have hy : Tendsto (yN f k₀ m₀) atTop (𝓝 c) := by
      refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
      · have := yN_lower hf k₀ m₀ (m := c) (fun t => (hc t).ge) (c - a) (by linarith)
        filter_upwards [this] with N h; linarith
      · have := yN_upper hf k₀ m₀ (M := c) (fun t => (hP t).le) hc0 (a - c) (by linarith)
        filter_upwards [this] with N h; linarith
    have hxy : (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) = fun N => (yN f k₀ m₀ N) ^ 2 := by
      funext N
      unfold yN
      rw [mul_pow, Real.sq_sqrt (Edia_nonneg (f := f) (k := k₀) (m := m₀) N)]
    rw [hxy]
    exact hy.pow 2

include hf in
/-- **III.12.8(b)**: o limite de `N² E_N` existe ⟺ `Ψ_f` é constante -/
theorem limit_iff_const :
    (∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) atTop (𝓝 L)) ↔
      ∃ c : ℝ, ∀ t, PsiF f k₀ m₀ t = c := by
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨t₀, h0⟩ := exists_min_psiF hf k₀ m₀
    obtain ⟨t₁, h1⟩ := exists_max_psiP hf k₀ m₀
    have hset := phase_cluster_set hf k₀ m₀ h0 h1
    have hmem : ∀ c ∈ Icc (PsiF f k₀ m₀ t₀ ^ 2) (PsiP f k₀ m₀ t₁ ^ 2), c = L := by
      intro c hc
      rw [← hset] at hc
      exact mapClusterPt_eq_of_tendsto hc hL
    have hm0 : 0 ≤ PsiF f k₀ m₀ t₀ := by
      refine le_trans ?_ (psiF_ge hf k₀ m₀ t₀)
      refine div_nonneg ?_ (Real.sqrt_nonneg _)
      exact intervalIntegral.integral_nonneg (cL_lt_cR k₀ m₀).le fun x _ => Real.sqrt_nonneg _
    have hmM : PsiF f k₀ m₀ t₀ ≤ PsiP f k₀ m₀ t₁ :=
      (h0 t₁).trans (psiF_le_psiP hf k₀ m₀ t₁)
    have hM0 : 0 ≤ PsiP f k₀ m₀ t₁ := hm0.trans hmM
    have e1 := hmem _ ⟨le_rfl, pow_le_pow_left₀ hm0 hmM 2⟩
    have e2 := hmem _ ⟨pow_le_pow_left₀ hm0 hmM 2, le_rfl⟩
    have heq : PsiF f k₀ m₀ t₀ = PsiP f k₀ m₀ t₁ :=
      (pow_left_inj₀ hm0 hM0 (by norm_num)).mp (e1.trans e2.symm)
    refine ⟨PsiF f k₀ m₀ t₀, fun t => le_antisymm ?_ (h0 t)⟩
    exact (psiF_le_psiP hf k₀ m₀ t).trans ((h1 t).trans heq.ge)
  · rintro ⟨c, hc⟩
    exact ⟨c ^ 2, (limit_of_const hf k₀ m₀ hc).2⟩

end coro

end Pendencias
