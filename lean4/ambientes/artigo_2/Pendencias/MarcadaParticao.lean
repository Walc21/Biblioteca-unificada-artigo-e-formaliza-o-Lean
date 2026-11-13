import Pendencias.ReversaoNecessidade

/-!
# Partição estrutural de uma árvore marcada

As fronteiras dos nós não entram no interior de suas folhas. Esta propriedade liga
as quebras efetivas de uma função à ordem de refinamento da árvore canônica.
-/

noncomputable section

namespace Pendencias.Marcada

open Artigo Set

namespace MTree

/-- Forma diádica da montagem, apagando somente os rótulos atômicos. É a árvore
da partição por células usada na definição de `𝒯(S)` e no número de folhas do TeX. -/
def shape : MTree → DShape
  | .leaf _ => .leaf
  | .node l r => .node l.shape r.shape

lemma numLeaves_shape (T : MTree) : T.shape.numLeaves = T.numLeaves := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr =>
      simp only [shape, DShape.numLeaves, MTree.numLeaves, leaves, List.length_append]
      exact congrArg₂ (· + ·) ihl ihr

lemma cuts_interior (T : MTree) : ∀ (k : ℕ) (m : ℤ) (t : ℚ), t ∈ T.cuts k m →
    cL k m < t ∧ (t : ℝ) < cR k m := by
  induction T with
  | leaf a => simp [cuts]
  | node l r ihl ihr =>
      intro k m t ht
      have hml : cL k m < cL (k + 1) (2 * m + 1) := by
        simpa only [cL_child_left, cR_child_left] using cL_lt_cR (k + 1) (2 * m)
      have hmr : cL (k + 1) (2 * m + 1) < cR k m := by
        simpa only [cR_child_right] using cL_lt_cR (k + 1) (2 * m + 1)
      rcases Finset.mem_insert.mp ht with rfl | ht
      · simpa only [splitPoint_cast] using And.intro hml hmr
      · rcases Finset.mem_union.mp ht with ht | ht
        · have hi := ihl (k + 1) (2 * m) t ht
          rw [cL_child_left, cR_child_left] at hi
          exact ⟨hi.1, hi.2.trans hmr⟩
        · have hi := ihr (k + 1) (2 * m + 1) t ht
          rw [cR_child_right] at hi
          exact ⟨hml.trans hi.1, hi.2⟩

end MTree

lemma cellsOf_sub (T : DShape) : ∀ (k : ℕ) (m : ℤ) (J : ℕ × ℤ), J ∈ cellsOf T k m →
    cellIcc J.1 J.2 ⊆ cellIcc k m := by
  induction T with
  | leaf =>
      intro k m J hJ
      simp only [cellsOf, List.mem_singleton] at hJ
      subst J
      exact Set.Subset.rfl
  | node l r ihl ihr =>
      intro k m J hJ
      rcases List.mem_append.mp hJ with hJ | hJ
      · exact (ihl _ _ _ hJ).trans (cell_child_left_sub k m)
      · exact (ihr _ _ _ hJ).trans (cell_child_right_sub k m)

lemma cellsOf_bounds (T : DShape) (k : ℕ) (m : ℤ) (J : ℕ × ℤ) (hJ : J ∈ cellsOf T k m) :
    cL k m ≤ cL J.1 J.2 ∧ cR J.1 J.2 ≤ cR k m := by
  have hs := cellsOf_sub T k m J hJ
  exact ⟨(hs (show cL J.1 J.2 ∈ cellIcc J.1 J.2 from
    ⟨le_rfl, (cL_lt_cR _ _).le⟩)).1,
    (hs (show cR J.1 J.2 ∈ cellIcc J.1 J.2 from
      ⟨(cL_lt_cR _ _).le, le_rfl⟩)).2⟩

lemma leavesAvoid_mono {S U : Finset ℚ} {T : DShape} {k : ℕ} {m : ℤ}
    (hsub : S ⊆ U) (h : LeavesAvoid U T k m) : LeavesAvoid S T k m :=
  fun J hJ t ht ↦ h J hJ t (hsub ht)

/-- Nenhuma fronteira estrutural da montagem está no interior de uma célula-folha.
Vale também para fronteiras onde as duas inclinações coincidem. -/
theorem MTree.leavesAvoid_cuts (T : MTree) :
    ∀ (k : ℕ) (m : ℤ), LeavesAvoid (T.cuts k m) T.shape k m := by
  induction T with
  | leaf a => simp [LeavesAvoid, cuts, shape]
  | node l r ihl ihr =>
      intro k m
      apply (leavesAvoid_node _ _ _ k m).mpr
      constructor
      · intro J hJ t ht hi
        have hb := cellsOf_bounds l.shape (k + 1) (2 * m) J hJ
        rw [cR_child_left] at hb
        rcases Finset.mem_insert.mp ht with rfl | ht
        · rw [splitPoint_cast] at hi
          linarith [hi.2, hb.2]
        · rcases Finset.mem_union.mp ht with ht | ht
          · exact ihl _ _ J hJ t ht hi
          · have hit := (r.cuts_interior (k + 1) (2 * m + 1) t ht).1
            linarith [hi.2, hb.2]
      · intro J hJ t ht hi
        have hb := cellsOf_bounds r.shape (k + 1) (2 * m + 1) J hJ
        rcases Finset.mem_insert.mp ht with rfl | ht
        · rw [splitPoint_cast] at hi
          linarith [hi.1, hb.1]
        · rcases Finset.mem_union.mp ht with ht | ht
          · have hit := (l.cuts_interior (k + 1) (2 * m) t ht).2
            rw [cR_child_left] at hit
            linarith [hi.1, hb.1]
          · exact ihr _ _ J hJ t ht hi

lemma RedReLU.canonTree_shape (R : RedReLU) (T : DShape) (k : ℕ) (m : ℤ) :
    (R.canonTree T k m).shape = T := by
  induction T generalizing k m with
  | leaf => rfl
  | node l r ihl ihr => simp only [canonTree, MTree.shape, ihl, ihr]

lemma MTree.eval_child_left {k : ℕ} {m : ℤ} {l r : MTree}
    (hw : MTree.MWF k m (.node l r)) {x : ℝ}
    (hx : x ∈ cellIcc (k + 1) (2 * m)) :
    MTree.eval k m (.node l r) x = MTree.eval (k + 1) (2 * m) l x := by
  simp only [MTree.eval]
  split_ifs with hlt
  · rfl
  · have hxe : x = cL (k + 1) (2 * m + 1) := by
      have hxr : x ≤ cR (k + 1) (2 * m) := hx.2
      rw [cR_child_left] at hxr
      exact le_antisymm hxr (not_lt.mp hlt)
    rw [hxe, MTree.eval_at_left hw.2.1, ← cR_child_left, MTree.eval_at_right hw.1]
    exact congrArg (fun q : ℚ ↦ (q : ℝ)) hw.2.2.symm

lemma MTree.eval_child_right {k : ℕ} {m : ℤ} (l r : MTree) {x : ℝ}
    (hx : x ∈ cellIcc (k + 1) (2 * m + 1)) :
    MTree.eval k m (.node l r) x = MTree.eval (k + 1) (2 * m + 1) r x := by
  exact if_neg (not_lt.mpr hx.1)

lemma MAtom.eq_of_cell_eqOn (a b : MAtom) (k : ℕ) (m : ℤ)
    (ha : a.k = k ∧ a.m = m) (hb : b.k = k ∧ b.m = m)
    (he : EqOn a.eval b.eval (cellIcc k m)) : a = b := by
  have hk : a.k = b.k := ha.1.trans hb.1.symm
  have hm : a.m = b.m := ha.2.trans hb.2.symm
  have hz : a.x0 = b.x0 := by simp only [MAtom.x0, hk, hm]
  have hL := he (show cL k m ∈ cellIcc k m from ⟨le_rfl, (cL_lt_cR _ _).le⟩)
  have hR := he (show cR k m ∈ cellIcc k m from ⟨(cL_lt_cR _ _).le, le_rfl⟩)
  simp only [MAtom.eval, hz] at hL hR
  have hdiff : (a.s : ℝ) * (cR k m - cL k m) = (b.s : ℝ) * (cR k m - cL k m) := by
    linear_combination hR - hL
  have hs : a.s = b.s := Rat.cast_injective
    (mul_right_cancel₀ (sub_ne_zero.mpr (cL_lt_cR k m).ne') hdiff)
  rw [hs] at hL
  have hy : a.y0 = b.y0 := by
    apply Rat.cast_injective (α := ℝ)
    exact add_right_cancel hL
  cases a
  cases b
  simp_all only [MAtom.mk.injEq]

/-- Uma forma de árvore e a função realizada determinam todos os rótulos marcados:
dois átomos afins que coincidem em uma célula não degenerada têm os mesmos dados. -/
theorem MTree.eq_of_shape_eval (T : MTree) : ∀ (U : MTree) (k : ℕ) (m : ℤ),
    MTree.MWF k m T → MTree.MWF k m U → T.shape = U.shape →
      EqOn (MTree.eval k m T) (MTree.eval k m U) (cellIcc k m) → T = U := by
  induction T with
  | leaf a =>
      intro U k m hw hU hs he
      cases U with
      | leaf b => exact congrArg MTree.leaf (a.eq_of_cell_eqOn b k m hw hU he)
      | node l r => cases hs
  | node l r ihl ihr =>
      intro U k m hw hU hs he
      cases U with
      | leaf a => cases hs
      | node u v =>
          obtain ⟨hsl, hsr⟩ := DShape.node.inj hs
          have hel : EqOn (MTree.eval (k + 1) (2 * m) l)
              (MTree.eval (k + 1) (2 * m) u) (cellIcc (k + 1) (2 * m)) := by
            intro x hx
            calc
              _ = MTree.eval k m (.node l r) x := (MTree.eval_child_left hw hx).symm
              _ = MTree.eval k m (.node u v) x := he (cell_child_left_sub k m hx)
              _ = _ := MTree.eval_child_left hU hx
          have her : EqOn (MTree.eval (k + 1) (2 * m + 1) r)
              (MTree.eval (k + 1) (2 * m + 1) v) (cellIcc (k + 1) (2 * m + 1)) := by
            intro x hx
            calc
              _ = MTree.eval k m (.node l r) x := (MTree.eval_child_right l r hx).symm
              _ = MTree.eval k m (.node u v) x := he (cell_child_right_sub k m hx)
              _ = _ := MTree.eval_child_right u v hx
          exact congrArg₂ MTree.node (ihl u _ _ hw.1 hU.1 hsl hel)
            (ihr v _ _ hw.2.1 hU.2.1 hsr her)

end Pendencias.Marcada
