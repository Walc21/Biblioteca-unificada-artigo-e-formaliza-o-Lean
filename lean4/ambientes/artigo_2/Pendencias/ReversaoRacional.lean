import Pendencias.CanonicaContagem

/-!
# Realização canônica de uma forma hinge racional

Construção da direção racional da reversibilidade rasa. O item completo continua
dependendo da necessidade para parâmetros reais e da condição de inclinação não nula.
-/

noncomputable section

namespace Pendencias.Marcada

open Artigo Set

namespace MAtom

lemma eval_eq (a : MAtom) (x : ℚ) : a.eval x = a.evalQ x := by
  simp [eval, evalQ]

lemma eval_left (a : MAtom) : a.eval (cL a.k a.m) = a.lval := by
  rw [show cL a.k a.m = (((a.m : ℚ) / 2 ^ a.k : ℚ) : ℝ) by simp [cL]]
  exact a.eval_eq _

lemma eval_right (a : MAtom) : a.eval (cR a.k a.m) = a.rval := by
  rw [show cR a.k a.m = ((((a.m : ℚ) + 1) / 2 ^ a.k : ℚ) : ℝ) by simp [cR]]
  exact a.eval_eq _

end MAtom

namespace MTree

lemma eval_at_left : ∀ {k : ℕ} {m : ℤ} {T : MTree},
    MWF k m T → T.eval k m (cL k m) = T.lval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp only [eval, lval]; rw [← h.1, ← h.2]; exact a.eval_left
  | node l r ihl _ =>
      intro h
      simp only [eval, lval]
      have hmid : cL k m < cL (k + 1) (2 * m + 1) := by
        rw [← cR_child_left, ← cL_child_left]; exact cL_lt_cR _ _
      rw [if_pos hmid, ← cL_child_left]
      exact ihl h.1

lemma eval_at_right : ∀ {k : ℕ} {m : ℤ} {T : MTree},
    MWF k m T → T.eval k m (cR k m) = T.rval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp only [eval, rval]; rw [← h.1, ← h.2]; exact a.eval_right
  | node l r _ ihr =>
      intro h
      simp only [eval, rval]
      have hmid : ¬ cR k m < cL (k + 1) (2 * m + 1) := by
        rw [← cR_child_right]; exact not_lt.mpr (cL_lt_cR _ _).le
      rw [if_neg hmid, ← cR_child_right]
      exact ihr h.2.1

end MTree

namespace RedReLU

/-- Avaliação real da fórmula (reduced-relu-reverse) do TeX para os dados racionais
de `RedReLU`: os mesmos coeficientes e quebras são incluídos em `ℝ`, sem restrição
adicional. A soma é a mesma de `evalQ`, como certifica `eval_cast` abaixo. -/
def eval (R : RedReLU) (x : ℝ) : ℝ :=
  R.c + R.q * x + (R.data.map fun p ↦ (p.1 : ℝ) * max 0 (x - p.2)).sum

lemma eval_cast (R : RedReLU) (x : ℚ) : R.eval x = R.evalQ x := by
  simp [eval, evalQ, Function.comp_def, Rat.cast_max]

private lemma hinge_difference (a τ ℓ r : ℚ) (x y : ℝ)
    (hx : (ℓ : ℝ) ≤ x ∧ x ≤ r) (hy : (ℓ : ℝ) ≤ y ∧ y ≤ r)
    (hf : ¬ ((ℓ : ℝ) < τ ∧ (τ : ℝ) < r)) :
    (a : ℝ) * max 0 (x - τ) - a * max 0 (y - τ) =
      if τ ≤ ℓ then (a : ℝ) * (x - y) else 0 := by
  by_cases ht : τ ≤ ℓ
  · have ht' : (τ : ℝ) ≤ ℓ := by exact_mod_cast ht
    rw [if_pos ht, max_eq_right (by linarith : 0 ≤ x - (τ : ℝ)),
      max_eq_right (by linarith : 0 ≤ y - (τ : ℝ))]
    ring
  · have ht' : (ℓ : ℝ) < τ := by exact_mod_cast lt_of_not_ge ht
    have hr : (r : ℝ) ≤ τ := le_of_not_gt (fun h ↦ hf ⟨ht', h⟩)
    rw [if_neg ht, max_eq_left (by linarith : x - (τ : ℝ) ≤ 0),
      max_eq_left (by linarith : y - (τ : ℝ) ≤ 0)]
    ring

private lemma hinges_difference (L : List (ℚ × ℚ)) (ℓ r : ℚ) (x y : ℝ)
    (hx : (ℓ : ℝ) ≤ x ∧ x ≤ r) (hy : (ℓ : ℝ) ≤ y ∧ y ≤ r)
    (hf : ∀ p ∈ L, ¬ ((ℓ : ℝ) < p.2 ∧ (p.2 : ℝ) < r)) :
    (L.map (fun p ↦ (p.1 : ℝ) * max 0 (x - p.2))).sum -
        (L.map (fun p ↦ (p.1 : ℝ) * max 0 (y - p.2))).sum =
      (((L.filter fun p ↦ p.2 ≤ ℓ).map Prod.fst).sum : ℚ) * (x - y) := by
  induction L with
  | nil => simp
  | cons p L ih =>
      have hp := hinge_difference p.1 p.2 ℓ r x y hx hy (hf p (by simp))
      have hL := ih (fun q hq ↦ hf q (by simp [hq]))
      by_cases ht : p.2 ≤ ℓ
      · rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using ht)]
        simp only [List.map_cons, List.sum_cons, Rat.cast_add]
        rw [if_pos ht] at hp
        linear_combination hp + hL
      · rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using ht)]
        simp only [List.map_cons, List.sum_cons]
        rw [if_neg ht] at hp
        linear_combination hp + hL

lemma eval_difference (R : RedReLU) (ℓ r : ℚ) (x y : ℝ)
    (hx : (ℓ : ℝ) ≤ x ∧ x ≤ r) (hy : (ℓ : ℝ) ≤ y ∧ y ≤ r)
    (hf : ∀ τ ∈ R.breaks, ¬ ((ℓ : ℝ) < τ ∧ (τ : ℝ) < r)) :
    R.eval x - R.eval y = (R.slopeAt ℓ : ℝ) * (x - y) := by
  have h := hinges_difference R.data ℓ r x y hx hy (fun p hp ↦
    hf p.2 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)))
  simp only [eval, slopeAt, Rat.cast_add]
  linear_combination h

/-- Em uma célula sem quebra interior, o átomo canônico usa exatamente o valor no
centro e a inclinação local da forma hinge, portanto coincide com ela na célula fechada. -/
theorem atomAt_eval (R : RedReLU) (k : ℕ) (m : ℤ)
    (hf : ∀ τ ∈ R.breaks, ¬ (cL k m < τ ∧ (τ : ℝ) < cR k m))
    (x : ℝ) (hx : x ∈ cellIcc k m) : (R.atomAt k m).eval x = R.eval x := by
  let ℓ : ℚ := (m : ℚ) / 2 ^ k
  let r : ℚ := ((m : ℚ) + 1) / 2 ^ k
  let z : ℚ := ((m : ℚ) + 1 / 2) / 2 ^ k
  have hℓ : (ℓ : ℝ) = cL k m := by simp [ℓ, cL]
  have hr : (r : ℝ) = cR k m := by simp [r, cR]
  have hz : (z : ℝ) = (cL k m + cR k m) / 2 := by
    simp only [z, Rat.cast_div, Rat.cast_add, Rat.cast_intCast, Rat.cast_one,
      Rat.cast_ofNat, Rat.cast_pow]
    unfold cL cR
    ring
  have hab := cL_lt_cR k m
  have hzI : (ℓ : ℝ) ≤ z ∧ (z : ℝ) ≤ r := by rw [hℓ, hr, hz]; constructor <;> linarith
  have hxI : (ℓ : ℝ) ≤ x ∧ x ≤ r := by simpa only [hℓ, hr] using hx
  have hfree : ∀ τ ∈ R.breaks, ¬ ((ℓ : ℝ) < τ ∧ (τ : ℝ) < r) := by
    simpa only [hℓ, hr] using hf
  have hd := R.eval_difference ℓ r x z hxI hzI hfree
  rw [R.eval_cast z] at hd
  change (R.evalQ z : ℝ) + (R.slopeAt ℓ : ℝ) * (x - (z : ℝ)) = R.eval x
  linarith

/-- A montagem canônica de uma árvore que separa as quebras é bem formada e realiza
a fórmula racional em toda a célula raiz, inclusive nas fronteiras compartilhadas. -/
theorem canonTree_realizes (R : RedReLU) (T : DShape) :
    ∀ (k : ℕ) (m : ℤ), LeavesAvoid R.breaks T k m →
      MTree.MWF k m (R.canonTree T k m) ∧
        EqOn (MTree.eval k m (R.canonTree T k m)) R.eval (cellIcc k m) := by
  induction T with
  | leaf =>
      intro k m h
      exact ⟨⟨rfl, rfl⟩, fun x hx ↦ R.atomAt_eval k m
        ((leavesAvoid_leaf R.breaks k m).mp h) x hx⟩
  | node l r ihl ihr =>
      intro k m h
      obtain ⟨hl, hr⟩ := (leavesAvoid_node R.breaks l r k m).mp h
      obtain ⟨hwl, hel⟩ := ihl (k + 1) (2 * m) hl
      obtain ⟨hwr, her⟩ := ihr (k + 1) (2 * m + 1) hr
      have hjoin : (R.canonTree l (k + 1) (2 * m)).rval =
          (R.canonTree r (k + 1) (2 * m + 1)).lval := by
        apply Rat.cast_injective (α := ℝ)
        rw [← MTree.eval_at_right hwl, ← MTree.eval_at_left hwr]
        calc
          _ = R.eval (cR (k + 1) (2 * m)) := hel
            (show cR (k + 1) (2 * m) ∈ cellIcc (k + 1) (2 * m) from
              ⟨(cL_lt_cR _ _).le, le_rfl⟩)
          _ = R.eval (cL (k + 1) (2 * m + 1)) := by rw [cR_child_left]
          _ = _ := (her
            (show cL (k + 1) (2 * m + 1) ∈ cellIcc (k + 1) (2 * m + 1) from
              ⟨le_rfl, (cL_lt_cR _ _).le⟩)).symm
      refine ⟨⟨hwl, hwr, hjoin⟩, fun x hx ↦ ?_⟩
      change (if x < cL (k + 1) (2 * m + 1) then _ else _) = _
      split_ifs with hlt
      · apply hel
        rw [cellIcc_eq, cL_child_left, cR_child_left]
        exact ⟨hx.1, hlt.le⟩
      · apply her
        rw [cellIcc_eq, cR_child_right]
        exact ⟨not_lt.mp hlt, hx.2⟩

lemma canonTree_numLeaves (R : RedReLU) (T : DShape) (k : ℕ) (m : ℤ) :
    (R.canonTree T k m).numLeaves = T.numLeaves := by
  induction T generalizing k m with
  | leaf => rfl
  | node l r ihl ihr =>
      simp only [canonTree, MTree.numLeaves, MTree.leaves, List.length_append, DShape.numLeaves]
      exact congrArg₂ (· + ·) (ihl (k + 1) (2 * m)) (ihr (k + 1) (2 * m + 1))

/-- Direção construtiva racional e orçamento de folhas: com quebras diádicas em `(0,1)`,
a montagem canônica realiza a fórmula no domínio do TeX e satisfaz as duas cotas.
O conjunto de quebras é usado para admitir também listas com repetições ou saltos zero;
para uma forma reduzida, sua cardinalidade é o número `M` de hinges. -/
theorem canonTree_representation_bounds (R : RedReLU)
    (hdy : ∀ τ ∈ R.breaks, IsDyadic τ)
    (hi : ∀ τ ∈ R.breaks, (0 : ℝ) < τ ∧ (τ : ℝ) < 1) :
    let T := R.canonTree (canonShape R.breaks R.depth 0 0) 0 0
    MTree.MWF 0 0 T ∧ EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1) ∧
      R.breaks.card + 1 ≤ T.numLeaves ∧
        T.numLeaves ≤ 1 + ∑ τ ∈ R.breaks, Nat.log 2 τ.den := by
  obtain ⟨hw, he⟩ := R.canonTree_realizes _ 0 0 (R.canon_leaves_free hdy)
  have hb := canonShape_leaf_bounds R.breaks hdy hi
  refine ⟨hw, ?_, ?_, ?_⟩
  · simpa [cellIcc] using he
  · simpa only [canonTree_numLeaves] using hb.1
  · simpa only [canonTree_numLeaves] using hb.2

end RedReLU

end Pendencias.Marcada
