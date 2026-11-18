import Pendencias.FaseLei4

/-!
# III.12.7(iii) e III.12.8(a)

* `phase_seq_min`, `phase_seq_max`: sequências `ε_j → 0⁺` com `X(ε_j)` perto de `m_f` / `M_f`;
* `cluster_Icc`: lema abstrato (TVI discreto) — o conjunto de acumulação de `y_N` é `[m, M]`;
* `phase_cluster_set`: o conjunto de acumulação de `N² E_N^{dia}` é exatamente `[m_f², M_f²]`.
-/

namespace Pendencias

open Set Filter Topology MeasureTheory Artigo

section pack5

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

include hf in
lemma phase_seq_min {t₀ : ℝ} (h0 : ∀ t, PsiF f k₀ m₀ t₀ ≤ PsiF f k₀ m₀ t) :
    ∀ δ > 0, ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ j in atTop, Real.sqrt (ε j) * nThr f (ε j) k₀ m₀ < PsiF f k₀ m₀ t₀ + δ := by
  intro δ hδ
  have hev := (psiF_tendsto_left hf k₀ m₀ t₀).eventually
    (gt_mem_nhds (show PsiF f k₀ m₀ t₀ < PsiF f k₀ m₀ t₀ + δ / 2 by linarith))
  obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev
  obtain ⟨τ, hτ, hτ1⟩ := ((countable_atomPhase hf k₀ m₀).dense_compl ℝ).exists_between
    (show l < t₀ from hl)
  obtain ⟨ε, hε0, hεt, hX⟩ := phase_frequently_nonatom hf k₀ m₀ hτ
  have hlt : PsiF f k₀ m₀ τ < PsiF f k₀ m₀ t₀ + δ / 2 := hsub hτ1
  exact ⟨ε, hε0, hεt, hX.eventually (gt_mem_nhds (by linarith))⟩

include hf in
lemma phase_seq_max {t₁ : ℝ} :
    ∀ δ > 0, ∃ ε : ℕ → ℝ, (∀ j, 0 < ε j) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ j in atTop, PsiP f k₀ m₀ t₁ - δ < Real.sqrt (ε j) * nThr f (ε j) k₀ m₀ := by
  intro δ hδ
  have hev := (psiF_tendsto_right hf k₀ m₀ t₁).eventually
    (lt_mem_nhds (show PsiP f k₀ m₀ t₁ - δ / 2 < PsiP f k₀ m₀ t₁ by linarith))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  obtain ⟨τ, hτ, hτ1⟩ := ((countable_atomPhase hf k₀ m₀).dense_compl ℝ).exists_between
    (show t₁ < u from hu)
  obtain ⟨ε, hε0, hεt, hX⟩ := phase_frequently_nonatom hf k₀ m₀ hτ
  have hlt : PsiP f k₀ m₀ t₁ - δ / 2 < PsiF f k₀ m₀ τ := hsub hτ1
  exact ⟨ε, hε0, hεt, hX.eventually (lt_mem_nhds (by linarith))⟩

end pack5

/-- lema abstrato: conjunto de acumulação de uma sequência com passos para cima pequenos -/
lemma cluster_Icc {y : ℕ → ℝ} {m M : ℝ} (hmM : m ≤ M)
    (hup : ∀ δ > 0, ∀ᶠ N in atTop, y N < M + δ)
    (hlo : ∀ δ > 0, ∀ᶠ N in atTop, m - δ < y N)
    (hfm : ∀ δ > 0, ∃ᶠ N in atTop, y N < m + δ)
    (hfM : ∀ δ > 0, ∃ᶠ N in atTop, M - δ < y N)
    (hstep : ∀ δ > 0, ∀ᶠ N in atTop, y (N + 1) < y N + δ) :
    {c | MapClusterPt c atTop y} = Icc m M := by
  ext c
  simp only [mem_setOf_eq, mem_Icc, mapClusterPt_iff_frequently]
  constructor
  · intro h
    constructor
    · by_contra hc
      push_neg at hc
      have hδ : 0 < (m - c) / 2 := by linarith
      obtain ⟨N, hN1, hN2⟩ := ((h _ (Iio_mem_nhds (show c < m - (m - c) / 2 by linarith))).and_eventually
        (hlo _ hδ)).exists
      simp only [mem_Iio] at hN1
      linarith
    · by_contra hc
      push_neg at hc
      have hδ : 0 < (c - M) / 2 := by linarith
      obtain ⟨N, hN1, hN2⟩ := ((h _ (Ioi_mem_nhds (show M + (c - M) / 2 < c by linarith))).and_eventually
        (hup _ hδ)).exists
      simp only [mem_Ioi] at hN1
      linarith
  · rintro ⟨hc1, hc2⟩ s hs
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
    have hρ : 0 < δ / 2 := by linarith
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp ((hlo _ hρ).and ((hup _ hρ).and (hstep _ hρ)))
    rw [frequently_atTop]
    intro N₀
    have hin : ∀ N, |y N - c| < δ → y N ∈ s := fun N h =>
      hball (by rw [Metric.mem_ball, Real.dist_eq]; exact h)
    rcases lt_or_ge c (m + δ / 2) with hA | hA
    · obtain ⟨N, hN, hy⟩ := frequently_atTop.mp (hfm _ hρ) (max N₀ N₁)
      refine ⟨N, (le_max_left _ _).trans hN, hin N (abs_lt.mpr ⟨?_, ?_⟩)⟩
      · have := (hN₁ N ((le_max_right _ _).trans hN)).1; linarith
      · linarith
    rcases lt_or_ge (M - δ / 2) c with hB | hB
    · obtain ⟨N, hN, hy⟩ := frequently_atTop.mp (hfM _ hρ) (max N₀ N₁)
      refine ⟨N, (le_max_left _ _).trans hN, hin N (abs_lt.mpr ⟨?_, ?_⟩)⟩
      · linarith
      · have := (hN₁ N ((le_max_right _ _).trans hN)).2.1; linarith
    · obtain ⟨A, hA1, hA2⟩ := frequently_atTop.mp (hfm _ hρ) (max N₀ N₁)
      obtain ⟨B, hB1, hB2⟩ := frequently_atTop.mp (hfM _ hρ) (A + 1)
      have hex : ∃ N, A < N ∧ c ≤ y N := ⟨B, by omega, by linarith⟩
      classical
      set N' := Nat.find hex with hN'
      have hspec := Nat.find_spec hex
      have hN'A : A < N' := hspec.1
      have hprev : y (N' - 1) < c := by
        by_cases h : A < N' - 1
        · have := Nat.find_min hex (show N' - 1 < N' by omega)
          push_neg at this
          exact this h
        · have : N' - 1 = A := by omega
          rw [this]; linarith
      have hstep' := (hN₁ (N' - 1) (by have := le_max_right N₀ N₁; omega)).2.2
      rw [show N' - 1 + 1 = N' by omega] at hstep'
      refine ⟨N', by have := le_max_left N₀ N₁; omega, hin N' (abs_lt.mpr ⟨?_, ?_⟩)⟩
      · linarith [hspec.2]
      · linarith

section pack6

variable {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (k₀ : ℕ) (m₀ : ℤ)

/-- `y_N = N √(E_N^{dia})` -/
noncomputable def yN (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (N : ℕ) : ℝ :=
  (N : ℝ) * Real.sqrt (Edia f k₀ m₀ N)

include hf in
lemma edia_le_iff {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε) :
    Edia f k₀ m₀ N ≤ ε ↔ nThr f ε k₀ m₀ ≤ N :=
  (threshold_optimality hf.continuous.continuousOn hε).2.2.2.2.2 N hN

include hf in
lemma edia_lt_eventually {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ᶠ N : ℕ in atTop, Edia f k₀ m₀ N < ε₀ := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (nThr f (ε₀ / 2) k₀ m₀)]
    with N h1 h2
  have := (edia_le_iff hf k₀ m₀ h1 (half_pos hε₀)).mpr h2
  linarith

include hf in
lemma edia_succ_le {N : ℕ} (hN : 1 ≤ N) : Edia f k₀ m₀ (N + 1) ≤ Edia f k₀ m₀ N := by
  obtain ⟨T, hT, hTe⟩ := exists_Edia_eq (f := f) (k := k₀) (m := m₀) hN
  rw [← hTe]
  exact Edia_le_treeErr (by omega)

include hf in
lemma yN_lower {m : ℝ} (hm : ∀ t, m ≤ PsiF f k₀ m₀ t) :
    ∀ δ > 0, ∀ᶠ N : ℕ in atTop, m - δ < yN f k₀ m₀ N := by
  intro δ hδ
  have h1 := phase_liminf_ge hf k₀ m₀ hm (δ / 2) (by linarith)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp h1
  filter_upwards [eventually_ge_atTop 1, edia_lt_eventually hf k₀ m₀ (show (0:ℝ) < u from hu)]
    with N hN hEN
  by_contra hcon
  push_neg at hcon
  have hcont : ContinuousAt (fun ε : ℝ => Real.sqrt ε * N) (Edia f k₀ m₀ N) :=
    (Real.continuous_sqrt.mul continuous_const).continuousAt
  have hlt : ∀ᶠ ε in 𝓝 (Edia f k₀ m₀ N), Real.sqrt ε * N < m - δ / 2 := by
    refine hcont.eventually (gt_mem_nhds ?_)
    unfold yN at hcon
    show Real.sqrt (Edia f k₀ m₀ N) * N < m - δ / 2
    linarith
  have h2 : ∀ᶠ ε in 𝓝[>] (Edia f k₀ m₀ N), Real.sqrt ε * N < m - δ / 2 ∧ ε < u :=
    eventually_nhdsWithin_of_eventually_nhds (hlt.and (Iio_mem_nhds hEN))
  obtain ⟨ε, ⟨hε1, hε2⟩, hε3⟩ := (h2.and eventually_mem_nhdsWithin).exists
  have hε3' : Edia f k₀ m₀ N < ε := hε3
  have hε0 : 0 < ε := lt_of_le_of_lt (Edia_nonneg (f := f) (k := k₀) (m := m₀) N) hε3'
  have hX : m - δ / 2 < Real.sqrt ε * nThr f ε k₀ m₀ := hsub ⟨hε0, hε2⟩
  have hn : nThr f ε k₀ m₀ ≤ N := (edia_le_iff hf k₀ m₀ hN hε0).mp hε3'.le
  have : Real.sqrt ε * nThr f ε k₀ m₀ ≤ Real.sqrt ε * N :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (Real.sqrt_nonneg _)
  linarith

include hf in
lemma yN_upper {M : ℝ} (hM : ∀ t, PsiP f k₀ m₀ t ≤ M) (hM0 : 0 ≤ M) :
    ∀ δ > 0, ∀ᶠ N : ℕ in atTop, yN f k₀ m₀ N < M + δ := by
  intro δ hδ
  have h1 := phase_limsup_le hf k₀ m₀ hM (δ / 2) (by linarith)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp h1
  filter_upwards [eventually_ge_atTop 1, edia_lt_eventually hf k₀ m₀ (show (0:ℝ) < u from hu)]
    with N hN hEN
  rcases (Edia_nonneg (f := f) (k := k₀) (m := m₀) N).eq_or_lt with h0 | hpos
  · unfold yN; rw [← h0]; simp; linarith
  · by_contra hcon
    push_neg at hcon
    have hcont : ContinuousAt (fun ε : ℝ => Real.sqrt ε * N) (Edia f k₀ m₀ N) :=
      (Real.continuous_sqrt.mul continuous_const).continuousAt
    have hgt : ∀ᶠ ε in 𝓝 (Edia f k₀ m₀ N), M + δ / 2 < Real.sqrt ε * N := by
      refine hcont.eventually (lt_mem_nhds ?_)
      unfold yN at hcon
      show M + δ / 2 < Real.sqrt (Edia f k₀ m₀ N) * N
      linarith
    have h2 : ∀ᶠ ε in 𝓝[<] (Edia f k₀ m₀ N), M + δ / 2 < Real.sqrt ε * N ∧ 0 < ε :=
      eventually_nhdsWithin_of_eventually_nhds (hgt.and (Ioi_mem_nhds hpos))
    obtain ⟨ε, ⟨hε1, hε0⟩, hε3⟩ := (h2.and eventually_mem_nhdsWithin).exists
    have hε3' : ε < Edia f k₀ m₀ N := hε3
    have hX : Real.sqrt ε * nThr f ε k₀ m₀ < M + δ / 2 := hsub ⟨hε0, hε3'.trans hEN⟩
    have hn : ¬ nThr f ε k₀ m₀ ≤ N := fun h =>
      absurd ((edia_le_iff hf k₀ m₀ hN hε0).mpr h) (not_le.mpr hε3')
    have hn' : (N : ℝ) ≤ nThr f ε k₀ m₀ := by exact_mod_cast (not_le.mp hn).le
    have : Real.sqrt ε * N ≤ Real.sqrt ε * nThr f ε k₀ m₀ :=
      mul_le_mul_of_nonneg_left hn' (Real.sqrt_nonneg _)
    linarith

include hf in
lemma yN_step : ∀ δ > 0, ∀ᶠ N : ℕ in atTop, yN f k₀ m₀ (N + 1) < yN f k₀ m₀ N + δ := by
  intro δ hδ
  filter_upwards [eventually_ge_atTop 1, edia_lt_eventually hf k₀ m₀ (show 0 < δ ^ 2 by positivity)]
    with N hN hEN
  have h1 := edia_succ_le hf k₀ m₀ hN
  have h2 : Real.sqrt (Edia f k₀ m₀ (N + 1)) ≤ Real.sqrt (Edia f k₀ m₀ N) := Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt (Edia f k₀ m₀ N) < δ := by
    rw [Real.sqrt_lt' hδ]; exact hEN
  unfold yN
  push_cast
  nlinarith [Real.sqrt_nonneg (Edia f k₀ m₀ (N + 1)), Nat.cast_nonneg (α := ℝ) N]

include hf in
lemma yN_freq_min {t₀ : ℝ} (h0 : ∀ t, PsiF f k₀ m₀ t₀ ≤ PsiF f k₀ m₀ t)
    (hm0 : 0 ≤ PsiF f k₀ m₀ t₀) :
    ∀ δ > 0, ∃ᶠ N : ℕ in atTop, yN f k₀ m₀ N < PsiF f k₀ m₀ t₀ + δ := by
  intro δ hδ
  obtain ⟨ε, hε0, hεt, hlt⟩ := phase_seq_min hf k₀ m₀ h0 δ hδ
  rw [frequently_atTop]
  intro N₀
  set N₁ := max N₀ 1 with hN₁
  have hN₁1 : 1 ≤ N₁ := le_max_right _ _
  rcases (Edia_nonneg (f := f) (k := k₀) (m := m₀) N₁).eq_or_lt with h00 | hpos
  · refine ⟨N₁, le_max_left _ _, ?_⟩
    unfold yN; rw [← h00]; simp; linarith
  · have hev : ∀ᶠ j in atTop, ε j < Edia f k₀ m₀ N₁ := hεt.eventually (gt_mem_nhds hpos)
    obtain ⟨j, hj1, hj2⟩ := (hev.and hlt).exists
    have hn : N₁ < nThr f (ε j) k₀ m₀ := by
      by_contra hc
      push_neg at hc
      have := (edia_le_iff hf k₀ m₀ hN₁1 (hε0 j)).mpr hc
      linarith
    set Nj := nThr f (ε j) k₀ m₀
    have hE : Edia f k₀ m₀ Nj ≤ ε j :=
      (edia_le_iff hf k₀ m₀ (by omega) (hε0 j)).mpr le_rfl
    refine ⟨Nj, by have := le_max_left N₀ 1; omega, ?_⟩
    have := Real.sqrt_le_sqrt hE
    unfold yN
    nlinarith [Nat.cast_nonneg (α := ℝ) Nj]

include hf in
lemma yN_freq_max {t₁ : ℝ} (hM0 : 0 ≤ PsiP f k₀ m₀ t₁) :
    ∀ δ > 0, ∃ᶠ N : ℕ in atTop, PsiP f k₀ m₀ t₁ - δ < yN f k₀ m₀ N := by
  intro δ hδ
  obtain ⟨ε, hε0, hεt, hlt⟩ := phase_seq_max hf k₀ m₀ (t₁ := t₁) (δ / 2) (by linarith)
  have hsq : Tendsto (fun j => Real.sqrt (ε j)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp hεt
  rw [frequently_atTop]
  intro N₀
  set N₁ := max N₀ 1 with hN₁
  have hN₁1 : 1 ≤ N₁ := le_max_right _ _
  have hsmall : ∀ᶠ j in atTop, Real.sqrt (ε j) < δ / 2 :=
    hsq.eventually (gt_mem_nhds (by linarith))
  rcases (Edia_nonneg (f := f) (k := k₀) (m := m₀) N₁).eq_or_lt with h00 | hpos
  · have hsmall2 : ∀ᶠ j in atTop, Real.sqrt (ε j) * N₁ < δ / 2 := by
      have := hsq.mul_const (N₁ : ℝ)
      rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds (by linarith))
    obtain ⟨j, hj1, hj2⟩ := (hlt.and hsmall2).exists
    have hn : nThr f (ε j) k₀ m₀ ≤ N₁ :=
      (edia_le_iff hf k₀ m₀ hN₁1 (hε0 j)).mp (by rw [← h00]; exact (hε0 j).le)
    have : Real.sqrt (ε j) * nThr f (ε j) k₀ m₀ ≤ Real.sqrt (ε j) * N₁ :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (Real.sqrt_nonneg _)
    refine ⟨N₁, le_max_left _ _, ?_⟩
    unfold yN; rw [← h00]; simp; linarith
  · have hev : ∀ᶠ j in atTop, ε j < Edia f k₀ m₀ N₁ := hεt.eventually (gt_mem_nhds hpos)
    obtain ⟨j, ⟨hj1, hj2⟩, hj3⟩ := ((hev.and hlt).and hsmall).exists
    have hn : N₁ < nThr f (ε j) k₀ m₀ := by
      by_contra hc
      push_neg at hc
      have := (edia_le_iff hf k₀ m₀ hN₁1 (hε0 j)).mpr hc
      linarith
    set n := nThr f (ε j) k₀ m₀ with hndef
    set N := n - 1 with hNdef
    have hNn : N + 1 = n := by omega
    have hNlt : ε j < Edia f k₀ m₀ N := by
      by_contra hc
      push_neg at hc
      have := (edia_le_iff hf k₀ m₀ (by omega) (hε0 j)).mp hc
      omega
    refine ⟨N, by have := le_max_left N₀ 1; omega, ?_⟩
    have hs := Real.sqrt_le_sqrt hNlt.le
    have hcast : (N : ℝ) + 1 = n := by exact_mod_cast hNn
    unfold yN
    nlinarith [Nat.cast_nonneg (α := ℝ) N, Real.sqrt_nonneg (ε j)]

include hf in
/-- **III.12.8(a)**: o conjunto de acumulação de `N² E_N^{dia}` é `[m_f², M_f²]` -/
theorem phase_cluster_set {t₀ t₁ : ℝ} (h0 : ∀ t, PsiF f k₀ m₀ t₀ ≤ PsiF f k₀ m₀ t)
    (h1 : ∀ t, PsiP f k₀ m₀ t ≤ PsiP f k₀ m₀ t₁) :
    {c : ℝ | MapClusterPt c atTop (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N)} =
      Icc (PsiF f k₀ m₀ t₀ ^ 2) (PsiP f k₀ m₀ t₁ ^ 2) := by
  have hc0 : 0 ≤ curvI f k₀ m₀ / Real.sqrt 8 := by
    refine div_nonneg ?_ (Real.sqrt_nonneg _)
    exact intervalIntegral.integral_nonneg (cL_lt_cR k₀ m₀).le fun x _ => Real.sqrt_nonneg _
  have hm0 : 0 ≤ PsiF f k₀ m₀ t₀ := hc0.trans (psiF_ge hf k₀ m₀ t₀)
  have hmM : PsiF f k₀ m₀ t₀ ≤ PsiP f k₀ m₀ t₁ :=
    (h0 t₁).trans (psiF_le_psiP hf k₀ m₀ t₁)
  have hM0 : 0 ≤ PsiP f k₀ m₀ t₁ := hm0.trans hmM
  have hy := cluster_Icc (y := yN f k₀ m₀) hmM (yN_upper hf k₀ m₀ h1 hM0)
    (yN_lower hf k₀ m₀ h0) (yN_freq_min hf k₀ m₀ h0 hm0) (yN_freq_max hf k₀ m₀ hM0)
    (yN_step hf k₀ m₀)
  have hxy : (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) = fun N => (yN f k₀ m₀ N) ^ 2 := by
    funext N
    unfold yN
    rw [mul_pow, Real.sq_sqrt (Edia_nonneg (f := f) (k := k₀) (m := m₀) N)]
  have hyx : yN f k₀ m₀ = Real.sqrt ∘ (fun N : ℕ => (N : ℝ) ^ 2 * Edia f k₀ m₀ N) := by
    funext N
    simp only [Function.comp]
    unfold yN
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  ext c
  simp only [mem_setOf_eq, mem_Icc]
  constructor
  · intro hc
    have hcnn : 0 ≤ c := by
      by_contra hneg
      push_neg at hneg
      obtain ⟨N, hN⟩ := ((mapClusterPt_iff_frequently.mp hc) (Iio 0) (Iio_mem_nhds hneg)).exists
      have := mul_nonneg (sq_nonneg (N : ℝ)) (Edia_nonneg (f := f) (k := k₀) (m := m₀) N)
      simp only [mem_Iio] at hN
      linarith
    have hs : MapClusterPt (Real.sqrt c) atTop (yN f k₀ m₀) := by
      rw [hyx]
      exact hc.continuousAt_comp Real.continuous_sqrt.continuousAt
    have hmem : Real.sqrt c ∈ Icc (PsiF f k₀ m₀ t₀) (PsiP f k₀ m₀ t₁) := by
      rw [← hy]; exact hs
    obtain ⟨a, b⟩ := hmem
    constructor
    · calc PsiF f k₀ m₀ t₀ ^ 2 ≤ Real.sqrt c ^ 2 := pow_le_pow_left₀ hm0 a 2
        _ = c := Real.sq_sqrt hcnn
    · calc c = Real.sqrt c ^ 2 := (Real.sq_sqrt hcnn).symm
        _ ≤ PsiP f k₀ m₀ t₁ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) b 2
  · rintro ⟨a, b⟩
    have hcnn : 0 ≤ c := le_trans (sq_nonneg _) a
    have hmem : Real.sqrt c ∈ Icc (PsiF f k₀ m₀ t₀) (PsiP f k₀ m₀ t₁) := by
      constructor
      · calc PsiF f k₀ m₀ t₀ = Real.sqrt (PsiF f k₀ m₀ t₀ ^ 2) := (Real.sqrt_sq hm0).symm
          _ ≤ Real.sqrt c := Real.sqrt_le_sqrt a
      · calc Real.sqrt c ≤ Real.sqrt (PsiP f k₀ m₀ t₁ ^ 2) := Real.sqrt_le_sqrt b
          _ = PsiP f k₀ m₀ t₁ := Real.sqrt_sq hM0
    rw [← hy] at hmem
    have := hmem.continuousAt_comp (continuous_pow 2).continuousAt
    rw [hxy]
    simpa [Real.sq_sqrt hcnn] using this

end pack6

end Pendencias
