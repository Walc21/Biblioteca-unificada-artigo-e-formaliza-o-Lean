import Pendencias.ReversaoExata

/-!
# Condição sem regiões planas para a biblioteca original

A marca pode ser retirada exatamente quando todas as inclinações locais são não
nulas. As hipóteses de racionalidade continuam sendo as condições do TeX.
-/

noncomputable section

namespace Pendencias.Marcada

open Artigo Set Filter Classical
open scoped Topology

lemma toM_WF_iff (T : LTree) : ∀ (k : ℕ) (m : ℤ),
    MTree.MWF k m T.toM ↔ LTree.WF k m T := by
  induction T with
  | leaf a => intro k m; rfl
  | node l r ihl ihr =>
      intro k m
      simp only [LTree.toM, MTree.MWF, LTree.WF, ihl, ihr, toM_rval, toM_lval]

lemma MTree.exists_original (T : MTree) (hn : ∀ a ∈ T.leaves, a.s ≠ 0) :
    ∃ U : LTree, U.toM = T := by
  induction T with
  | leaf a =>
      exact ⟨.leaf ⟨a.k, a.m, a.y0, a.s, hn a (by simp [leaves])⟩, rfl⟩
  | node l r ihl ihr =>
      obtain ⟨u, hu⟩ := ihl (fun a ha ↦ hn a (List.mem_append_left _ ha))
      obtain ⟨v, hv⟩ := ihr (fun a ha ↦ hn a (List.mem_append_right _ ha))
      exact ⟨.node u v, by simp only [LTree.toM, hu, hv]⟩

theorem _root_.Artigo.LTree.exists_hasDerivAt_nonzero (T : LTree) :
    ∀ (k : ℕ) (m : ℤ) (x : ℝ),
    (∀ t ∈ T.toM.cuts k m, x ≠ (t : ℝ)) →
      ∃ s : ℚ, s ≠ 0 ∧ HasDerivAt (LTree.eval k m T) (s : ℝ) x := by
  induction T with
  | leaf a =>
      intro k m x _
      refine ⟨a.s, a.hs, ?_⟩
      simpa only [LTree.eval, Artigo.Atom.eval, mul_one] using
        (((hasDerivAt_id x).sub_const (a.x0 : ℝ)).const_mul (a.s : ℝ)).const_add (a.y0 : ℝ)
  | node l r ihl ihr =>
      intro k m x hx
      have hmid : x ≠ cL (k + 1) (2 * m + 1) := by
        rw [← splitPoint_cast]
        exact hx _ (Finset.mem_insert_self _ _)
      by_cases hlt : x < cL (k + 1) (2 * m + 1)
      · obtain ⟨s, hs0, hs⟩ := ihl (k + 1) (2 * m) x (fun t ht ↦ hx t
          (Finset.mem_insert_of_mem (Finset.mem_union_left _ ht)))
        refine ⟨s, hs0, hs.congr_of_eventuallyEq ?_⟩
        filter_upwards [Iio_mem_nhds hlt] with y hy
        exact if_pos hy
      · have hgt : cL (k + 1) (2 * m + 1) < x :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hmid)
        obtain ⟨s, hs0, hs⟩ := ihr (k + 1) (2 * m + 1) x (fun t ht ↦ hx t
          (Finset.mem_insert_of_mem (Finset.mem_union_right _ ht)))
        refine ⟨s, hs0, hs.congr_of_eventuallyEq ?_⟩
        filter_upwards [Ioi_mem_nhds hgt] with y hy
        exact if_neg (not_lt.mpr hy.le)

namespace RealReLU

/-- Pertinência à biblioteca original do TeX em `[0,1]`: realização por uma árvore
de átomos `Artigo.Atom`, cuja própria estrutura exige inclinação não nula. -/
def OriginalRealizable {M : ℕ} (R : RealReLU M) : Prop :=
  ∃ T : LTree, LTree.WF 0 0 T ∧ EqOn (LTree.eval 0 0 T) R.eval (Icc 0 1)

lemma original_marked {M : ℕ} (R : RealReLU M) (h : R.OriginalRealizable) :
    R.MarkedRealizable := by
  obtain ⟨T, hw, he⟩ := h
  refine ⟨T.toM, toM_WF hw, ?_⟩
  simpa only [toM_eval] using he

lemma exists_sigma_le {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (x : ℝ) :
    ∃ n ≤ M, R.q + (∑ i, if R.τ i ≤ x then R.a i else 0) = R.sigma n := by
  let S : Finset (Fin M) := Finset.univ.filter fun i ↦ R.τ i ≤ x
  rcases S.eq_empty_or_nonempty with he | hne
  · refine ⟨0, Nat.zero_le _, ?_⟩
    have hn : ∀ i, ¬ R.τ i ≤ x := by
      intro i hi
      have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [he] at hm
      exact Finset.notMem_empty i hm
    simp [sigma, hn]
  · let j := S.max' hne
    have hj : R.τ j ≤ x := (Finset.mem_filter.mp (S.max'_mem hne)).2
    refine ⟨j.val + 1, by omega, ?_⟩
    unfold sigma
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hiff : R.τ i ≤ x ↔ i.val < j.val + 1 := by
      constructor
      · intro hi
        have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hij : i ≤ j := S.le_max' i hm
        change i.val ≤ j.val at hij
        omega
      · intro hi
        exact (hR.1.monotone (show i ≤ j by change i.val ≤ j.val; omega)).trans hj
    simp only [hiff]

private lemma sum_filter_map {α : Type*} (L : List α) (p : α → Bool) (f : α → ℚ) :
    ((L.filter p).map f).sum = (L.map fun a ↦ if p a then f a else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      by_cases h : p a = true <;> simp [h, ih]

lemma rationalData_slopeAt {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) (x : ℚ) :
    ((R.rationalData h).slopeAt x : ℝ) =
      R.q + ∑ i, if R.τ i ≤ (x : ℝ) then R.a i else 0 := by
  unfold RedReLU.slopeAt
  rw [sum_filter_map]
  simp only [rationalData, List.map_ofFn, Function.comp_apply, List.sum_ofFn,
    Rat.cast_add, Rat.cast_sum]
  rw [← h.2.1.choose_spec]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : (h.2.2.2 i).choose ≤ x
  · have ht' : R.τ i ≤ (x : ℝ) := by
      rw [(h.2.2.2 i).choose_spec.2]
      exact_mod_cast ht
    simp only [decide_eq_true_eq, if_pos ht, if_pos ht']
    exact (h.2.2.1 i).choose_spec.symm
  · have ht' : ¬ R.τ i ≤ (x : ℝ) := by
      rw [(h.2.2.2 i).choose_spec.2]
      exact_mod_cast ht
    simp only [decide_eq_true_eq, if_neg ht, if_neg ht', Rat.cast_zero]

theorem original_of_arithmetic {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.Arithmetic) (hn : ∀ n ≤ M, R.sigma n ≠ 0) : R.OriginalRealizable := by
  have hslopes : ∀ k m, ((R.rationalData h).atomAt k m).s ≠ 0 := by
    intro k m
    change (R.rationalData h).slopeAt ((m : ℚ) / 2 ^ k) ≠ 0
    have hs : ((R.rationalData h).slopeAt ((m : ℚ) / 2 ^ k) : ℝ) ≠ 0 := by
      rw [R.rationalData_slopeAt h]
      obtain ⟨n, hnm, heq⟩ := R.exists_sigma_le hR ((((m : ℚ) / 2 ^ k : ℚ) : ℝ))
      rw [heq]
      exact hn n hnm
    exact_mod_cast hs
  have hleaves : ∀ (D : DShape) (k : ℕ) (m : ℤ),
      ∀ a ∈ ((R.rationalData h).canonTree D k m).leaves, a.s ≠ 0 := by
    intro D
    induction D with
    | leaf => intro k m a ha; simp only [RedReLU.canonTree, MTree.leaves,
        List.mem_singleton] at ha; subst a; exact hslopes k m
    | node l r ihl ihr =>
        intro k m a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact ihl _ _ a ha
        · exact ihr _ _ a ha
  obtain ⟨T, hT⟩ := (R.canonicalTree h).exists_original (hleaves _ 0 0)
  obtain ⟨hw, he, _, _⟩ := R.canonicalTree_spec hR h
  rw [← hT] at hw he
  refine ⟨T, (toM_WF_iff T 0 0).mp hw, ?_⟩
  simpa only [toM_eval] using he

theorem original_sigma_nonzero {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.OriginalRealizable) : ∀ n ≤ M, R.sigma n ≠ 0 := by
  obtain ⟨T, _, he⟩ := h
  intro n hn
  obtain ⟨l, r, hl, hlr, hr, hregion⟩ := R.exists_region hR n hn
  obtain ⟨x, hx, hnot⟩ := (Ioo_infinite hlr).exists_notMem_finset
    ((T.toM.cuts 0 0).image fun t : ℚ ↦ (t : ℝ))
  have hcuts : ∀ t ∈ T.toM.cuts 0 0, x ≠ (t : ℝ) := by
    intro t ht heq
    exact hnot (Finset.mem_image.mpr ⟨t, ht, heq.symm⟩)
  obtain ⟨s, hs0, hs⟩ := T.exists_hasDerivAt_nonzero 0 0 x hcuts
  have hknots : ∀ i, x ≠ R.τ i := by
    intro i
    have hi := hregion x hx i
    split_ifs at hi with h
    · exact ne_of_gt hi
    · exact ne_of_lt hi
  have hderiv : HasDerivAt R.eval (s : ℝ) x := by
    apply hs.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (hl.trans_lt hx.1) (hx.2.trans_le hr)] with y hy
    exact (he ⟨hy.1.le, hy.2.le⟩).symm
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
  have heq : R.sigma n = (s : ℝ) := hslope.symm.trans ((R.hasDerivAt_eval hknots).unique hderiv)
  rw [heq]
  exact_mod_cast hs0

theorem original_realizable_iff {M : ℕ} (R : RealReLU M) (hR : R.Reduced) :
    R.OriginalRealizable ↔ R.Arithmetic ∧ ∀ n ≤ M, R.sigma n ≠ 0 := by
  constructor
  · intro h
    exact ⟨(R.marked_realizable_iff hR).mp (R.original_marked h), R.original_sigma_nonzero hR h⟩
  · rintro ⟨ha, hn⟩
    exact R.original_of_arithmetic hR ha hn

lemma dyadicDepth_spec {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) (i : Fin M) :
    ((h.2.2.2 i).choose).den = 2 ^ R.dyadicDepth h i := by
  obtain ⟨d, hd⟩ := (h.2.2.2 i).choose_spec.1
  unfold dyadicDepth
  rw [hd, Nat.log_pow (by norm_num)]

/-- **Teorema IV.5.2 (reversibilidade rasa exata)**, com todas as afirmações do TeX.
Para uma forma reduzida com parâmetros reais: realização marcada se e somente se os
coeficientes são racionais e as quebras diádicas; a árvore canônica é a única menos
refinada que realiza a função; `M+1 ≤ N_can ≤ 1+∑d_j`; realização na biblioteca
original se e somente se, além das condições aritméticas, todas as `σ_i` são não nulas.
As realizações são igualdades de funções em `[0,1]`, o domínio do enunciado. -/
theorem exact_shallow_reversal {M : ℕ} (R : RealReLU M) (hR : R.Reduced) :
    (R.MarkedRealizable ↔ R.Arithmetic) ∧
      (∀ h : R.Arithmetic,
        MTree.MWF 0 0 (R.canonicalTree h) ∧
        EqOn (MTree.eval 0 0 (R.canonicalTree h)) R.eval (Icc 0 1) ∧
        (∀ T : MTree, MTree.MWF 0 0 T →
          EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1) → T.shape.Refines (R.canonicalTree h).shape) ∧
        (∀ T : MTree, MTree.MWF 0 0 T → EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1) →
          (∀ U : MTree, MTree.MWF 0 0 U → EqOn (MTree.eval 0 0 U) R.eval (Icc 0 1) →
            U.shape.Refines T.shape) → T = R.canonicalTree h) ∧
        M + 1 ≤ (R.canonicalTree h).numLeaves ∧
        (R.canonicalTree h).numLeaves ≤ 1 + ∑ i, R.dyadicDepth h i) ∧
      (R.OriginalRealizable ↔ R.Arithmetic ∧ ∀ n ≤ M, R.sigma n ≠ 0) := by
  refine ⟨R.marked_realizable_iff hR, ?_, R.original_realizable_iff hR⟩
  intro h
  obtain ⟨hw, he, hlo, hhi⟩ := R.canonicalTree_spec hR h
  exact ⟨hw, he, fun T _ hT ↦ R.realizes_refines_canonical hR h T hT,
    fun T hwT hT hleast ↦ R.canonicalTree_unique_least_labeled hR h T hwT hT hleast, hlo, hhi⟩

end RealReLU

end Pendencias.Marcada
