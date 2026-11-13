import Pendencias.ReLUReal

/-!
# Condições necessárias para uma realização marcada

Os parâmetros da rede permanecem reais. As condições aritméticas são conclusões
obtidas de uma montagem que realiza a função em `[0,1]`, não hipóteses de contrato.
-/

noncomputable section

namespace Pendencias.Marcada

open Artigo Set Filter Classical
open scoped Topology

lemma isDyadic_div_pow (m : ℤ) (k : ℕ) : IsDyadic ((m : ℚ) / 2 ^ k) := by
  have hd : (((m : ℚ) / 2 ^ k).den : ℤ) ∣ (2 : ℤ) ^ k := by
    simpa only [Rat.divInt_eq_div, Int.cast_pow, Int.cast_ofNat] using
      Rat.den_dvd m ((2 : ℤ) ^ k)
  have hn : ((m : ℚ) / 2 ^ k).den ∣ 2 ^ k := by exact_mod_cast hd
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  exact ⟨j, hj⟩

namespace MTree

/-- Fronteiras introduzidas pelos nós internos da montagem: cada nó subdivide a célula
no seu ponto médio diádico. É a partição estrutural do TeX, incluindo fronteiras onde
as inclinações dos dois lados possam coincidir. -/
def cuts : MTree → ℕ → ℤ → Finset ℚ
  | .leaf _, _, _ => ∅
  | .node l r, k, m => insert (splitPoint k m)
      (cuts l (k + 1) (2 * m) ∪ cuts r (k + 1) (2 * m + 1))

lemma cuts_dyadic (T : MTree) : ∀ (k : ℕ) (m : ℤ) (t : ℚ), t ∈ T.cuts k m → IsDyadic t := by
  induction T with
  | leaf a => simp [cuts]
  | node l r ihl ihr =>
      intro k m t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact isDyadic_div_pow (2 * m + 1) (k + 1)
      · rcases Finset.mem_union.mp ht with ht | ht
        · exact ihl _ _ _ ht
        · exact ihr _ _ _ ht

/-- Fora das fronteiras estruturais, uma montagem tem derivada racional. A prova segue
a avaliação da árvore e usa a inclinação do átomo da folha alcançada. -/
theorem exists_hasDerivAt (T : MTree) : ∀ (k : ℕ) (m : ℤ) (x : ℝ),
    (∀ t ∈ T.cuts k m, x ≠ (t : ℝ)) →
      ∃ s : ℚ, HasDerivAt (MTree.eval k m T) (s : ℝ) x := by
  induction T with
  | leaf a =>
      intro k m x _
      refine ⟨a.s, ?_⟩
      simpa only [MTree.eval, MAtom.eval, mul_one] using
        (((hasDerivAt_id x).sub_const (a.x0 : ℝ)).const_mul (a.s : ℝ)).const_add (a.y0 : ℝ)
  | node l r ihl ihr =>
      intro k m x hx
      have hmid : x ≠ cL (k + 1) (2 * m + 1) := by
        rw [← splitPoint_cast]
        exact hx _ (Finset.mem_insert_self _ _)
      by_cases hlt : x < cL (k + 1) (2 * m + 1)
      · obtain ⟨s, hs⟩ := ihl (k + 1) (2 * m) x (fun t ht ↦ hx t
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ ht)))
        refine ⟨s, hs.congr_of_eventuallyEq ?_⟩
        filter_upwards [Iio_mem_nhds hlt] with y hy
        exact if_pos hy
      · have hgt : cL (k + 1) (2 * m + 1) < x :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hmid)
        obtain ⟨s, hs⟩ := ihr (k + 1) (2 * m + 1) x (fun t ht ↦ hx t
          (Finset.mem_insert_of_mem (Finset.mem_union_right _ ht)))
        refine ⟨s, hs.congr_of_eventuallyEq ?_⟩
        filter_upwards [Ioi_mem_nhds hgt] with y hy
        exact if_neg (not_lt.mpr hy.le)

end MTree

namespace RealReLU

lemma eval_zero {M : ℕ} (R : RealReLU M) (hR : R.Reduced) : R.eval 0 = R.c := by
  have hs : ∑ i, R.a i * max 0 (0 - R.τ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [max_eq_left (by linarith [(hR.2.1 i).1] : 0 - R.τ i ≤ 0), mul_zero]
  simp only [eval, mul_zero, add_zero, hs]

/-- Toda quebra efetiva de uma rede realizada por uma montagem é uma fronteira da
árvore. Uma quebra no interior de uma folha contradiz a diferenciabilidade afim. -/
theorem breaks_mem_cuts {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (T : MTree)
    (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) (i : Fin M) :
    ∃ t ∈ T.cuts 0 0, R.τ i = (t : ℝ) := by
  by_contra h
  push_neg at h
  obtain ⟨s, hs⟩ := T.exists_hasDerivAt 0 0 (R.τ i) h
  apply R.not_differentiableAt_break hR i
  apply hs.differentiableAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (hR.2.1 i).1 (hR.2.1 i).2] with x hx
  exact (he ⟨hx.1.le, hx.2.le⟩).symm

theorem breaks_dyadic {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (T : MTree)
    (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) (i : Fin M) :
    ∃ t : ℚ, IsDyadic t ∧ R.τ i = (t : ℝ) := by
  obtain ⟨t, ht, heq⟩ := R.breaks_mem_cuts hR T he i
  exact ⟨t, T.cuts_dyadic 0 0 t ht, heq⟩

theorem intercept_rational {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (T : MTree)
    (hw : MTree.MWF 0 0 T) (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) :
    ∃ c : ℚ, R.c = (c : ℝ) := by
  refine ⟨T.lval, ?_⟩
  have ht := MTree.eval_at_left hw
  have ht' : MTree.eval 0 0 T 0 = (T.lval : ℝ) := by
    simpa only [cL, Int.cast_zero, zero_div] using ht
  have hz := he (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
  simpa only [R.eval_zero hR] using hz.symm.trans ht'

theorem slope_rational_at {M : ℕ} (R : RealReLU M) (T : MTree)
    (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) {x : ℝ} (hx : x ∈ Ioo 0 1)
    (hknots : ∀ i, x ≠ R.τ i) (hcuts : ∀ t ∈ T.cuts 0 0, x ≠ (t : ℝ)) :
    ∃ s : ℚ, R.slope x = (s : ℝ) := by
  obtain ⟨s, hs⟩ := T.exists_hasDerivAt 0 0 x hcuts
  refine ⟨s, (R.hasDerivAt_eval hknots).unique (hs.congr_of_eventuallyEq ?_)⟩
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact (he ⟨hy.1.le, hy.2.le⟩).symm

/-- Inclinações locais `σ_n = q + ∑_{j≤n} a_j` de (reverse-local-slopes), usando índices
`Fin M` a partir de zero: a região `n` inclui exatamente os índices menores que `n`. -/
def sigma {M : ℕ} (R : RealReLU M) (n : ℕ) : ℝ :=
  R.q + ∑ i, if i.val < n then R.a i else 0

lemma exists_region {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (n : ℕ) (hn : n ≤ M) :
    ∃ l r : ℝ, 0 ≤ l ∧ l < r ∧ r ≤ 1 ∧
      ∀ x ∈ Ioo l r, ∀ i, if i.val < n then R.τ i < x else x < R.τ i := by
  by_cases hn0 : n = 0
  · subst n
    by_cases hM : M = 0
    · subst M
      exact ⟨0, 1, le_rfl, zero_lt_one, le_rfl, fun _ _ i ↦ Fin.elim0 i⟩
    · let j : Fin M := ⟨0, by omega⟩
      refine ⟨0, R.τ j, le_rfl, (hR.2.1 j).1, (hR.2.1 j).2.le, ?_⟩
      intro x hx i
      simp only [Nat.not_lt_zero, ↓reduceIte]
      exact hx.2.trans_le (hR.1.monotone (show j ≤ i from Nat.zero_le _))
  · let j : Fin M := ⟨n - 1, by omega⟩
    by_cases hnM : n = M
    · refine ⟨R.τ j, 1, (hR.2.1 j).1.le, (hR.2.1 j).2, le_rfl, ?_⟩
      intro x hx i
      rw [if_pos (by omega : i.val < n)]
      exact (hR.1.monotone (show i ≤ j by change i.val ≤ n - 1; omega)).trans_lt hx.1
    · let k : Fin M := ⟨n, by omega⟩
      refine ⟨R.τ j, R.τ k, (hR.2.1 j).1.le,
        hR.1 (show j < k by change n - 1 < n; omega), (hR.2.1 k).2.le, ?_⟩
      intro x hx i
      by_cases hi : i.val < n
      · rw [if_pos hi]
        exact (hR.1.monotone (show i ≤ j by change i.val ≤ n - 1; omega)).trans_lt hx.1
      · rw [if_neg hi]
        exact hx.2.trans_le (hR.1.monotone (show k ≤ i by change n ≤ i.val; omega))

/-- Cada região afim não vazia contém um ponto fora das fronteiras finitas da montagem.
A derivada nesse ponto força a inclinação local da rede a ser racional. -/
theorem sigma_rational {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (T : MTree)
    (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) (n : ℕ) (hn : n ≤ M) :
    ∃ s : ℚ, R.sigma n = (s : ℝ) := by
  obtain ⟨l, r, hl, hlr, hr, hregion⟩ := R.exists_region hR n hn
  obtain ⟨x, hx, hnot⟩ := (Ioo_infinite hlr).exists_notMem_finset
    ((T.cuts 0 0).image fun t : ℚ ↦ (t : ℝ))
  have hknots : ∀ i, x ≠ R.τ i := by
    intro i
    have hi := hregion x hx i
    split_ifs at hi with h
    · exact ne_of_gt hi
    · exact ne_of_lt hi
  have hcuts : ∀ t ∈ T.cuts 0 0, x ≠ (t : ℝ) := by
    intro t ht heq
    exact hnot (Finset.mem_image.mpr ⟨t, ht, heq.symm⟩)
  have hslope : R.slope x = R.sigma n := by
    unfold slope sigma
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := hregion x hx i
    by_cases hin : i.val < n
    · rw [if_pos hin] at hi
      simp only [if_pos hin, if_pos hi]
    · rw [if_neg hin] at hi
      simp only [if_neg hin, if_neg (not_lt.mpr hi.le)]
  obtain ⟨s, hs⟩ := R.slope_rational_at T he ⟨hl.trans_lt hx.1, hx.2.trans_le hr⟩ hknots hcuts
  exact ⟨s, hslope.symm.trans hs⟩

lemma sigma_succ_sub {M : ℕ} (R : RealReLU M) (i : Fin M) :
    R.sigma (i.val + 1) - R.sigma i.val = R.a i := by
  unfold sigma
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin M, if j = i then R.a i else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · have hv : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
        by_cases hj : j.val < i.val
        · simp only [if_pos hj, if_pos (by omega : j.val < i.val + 1), if_neg hji, sub_self]
        · simp only [if_neg hj, if_neg (by omega : ¬ j.val < i.val + 1), if_neg hji, sub_zero]
    _ = _ := by simp

theorem coefficients_rational {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (T : MTree)
    (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) :
    (∃ q : ℚ, R.q = (q : ℝ)) ∧ ∀ i, ∃ a : ℚ, R.a i = (a : ℝ) := by
  constructor
  · simpa [sigma] using R.sigma_rational hR T he 0 (Nat.zero_le _)
  · intro i
    obtain ⟨p, hp⟩ := R.sigma_rational hR T he (i.val + 1) (by omega)
    obtain ⟨q, hq⟩ := R.sigma_rational hR T he i.val (by omega)
    refine ⟨p - q, ?_⟩
    rw [← R.sigma_succ_sub i, hp, hq, Rat.cast_sub]

/-- Necessidade das condições aritméticas, mantendo todos os parâmetros da rede reais
na hipótese: intercepto, inclinação inicial e saltos são racionais, e as quebras são
diádicas. Nenhuma dessas condições foi acrescentada como hipótese. -/
theorem parameters_necessary {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (T : MTree)
    (hw : MTree.MWF 0 0 T) (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) :
    (∃ c : ℚ, R.c = (c : ℝ)) ∧ (∃ q : ℚ, R.q = (q : ℝ)) ∧
      (∀ i, ∃ a : ℚ, R.a i = (a : ℝ)) ∧
        ∀ i, ∃ t : ℚ, IsDyadic t ∧ R.τ i = (t : ℝ) := by
  obtain ⟨hq, ha⟩ := R.coefficients_rational hR T he
  exact ⟨R.intercept_rational hR T hw he, hq, ha, R.breaks_dyadic hR T he⟩

end RealReLU

end Pendencias.Marcada
