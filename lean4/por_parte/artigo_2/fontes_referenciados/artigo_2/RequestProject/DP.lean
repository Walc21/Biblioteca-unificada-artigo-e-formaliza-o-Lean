import RequestProject.DPBase

/-!
# Sections 6–7 — Dynamic programming on a fixed tree and with a variable tree

* Definition 7.1 / Theorem 7.2 (Bellman recursion with variable tree: exactness, existence,
  determinism),
* Definition 6.1 / Theorem 6.2 (recursion and correctness on a fixed tree),
* Corollary 7.3 (compatibility with the enumeration of shapes).
-/

namespace Artigo

open Set LTree

namespace Setup

variable (S : Setup)

/-! ## Section 7: variable tree -/

/-- **Definition 7.1**: `C_0(J;u,v) = Φ_H(J;u,v)` and
`C_d(J;u,v) = min {Φ_H(J;u,v), λ_bits + λ_split + min_w [C_{d-1}(J_L;u,w) + C_{d-1}(J_R;w,v)]}` -/
noncomputable def Cvar : ℕ → ℕ → ℤ → ℚ → ℚ → WithTop ℚ
  | 0, k, m, u, v => S.Phi k m u v
  | d + 1, k, m, u, v => min (S.Phi k m u v)
      (((S.lb + S.ls : ℚ) : WithTop ℚ) +
        S.V.inf fun w => Cvar d (k + 1) (2 * m) u w + Cvar d (k + 1) (2 * m + 1) w v)

/-- inf over the glued pairs -/
lemma inf_glue' (s t : Finset LTree) :
    ((s ×ˢ t).image fun p => node p.1 p.2).inf S.costW =
      ((S.lb + S.ls : ℚ) : WithTop ℚ) + (s.inf S.costW + t.inf S.costW) := by
  classical
  rw [Finset.inf_image]
  have : (S.costW ∘ fun p : LTree × LTree => node p.1 p.2) =
      fun p => ((S.lb + S.ls : ℚ) : WithTop ℚ) + (S.costW p.1 + S.costW p.2) := by
    funext p; simp only [Function.comp, S.costW_node]; rw [add_comm]
  rw [this, ← const_add_inf, inf_prod_add]

/-- **Theorem 7.2 (exatidão)**: for a descendant `J` of `K` at relative depth `r` and `d ≤ D - r`,
`C_d(J;u,v) = min_{R ∈ 𝔑_{d,H}(J;u,v)} cost(R)` (`+∞` if empty). -/
theorem variable_correctness (hH : 2 ≤ S.H) : ∀ (d k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + d ≤ S.D → S.Cvar d k m u v = (S.Rset d k m u v).inf S.costW := by
  classical
  intro d
  induction d with
  | zero => intro k r m u v _ _; rw [Cvar, S.Rset_zero_inf hH]
  | succ d ih =>
    intro k r m u v hd hdD
    rw [S.Rset_succ hH hd hdD, Finset.inf_union, S.Rset_zero_inf hH, Finset.inf_biUnion, Cvar]
    congr 1
    simp only [inf_glue']
    rw [← const_add_inf]
    congr 1
    congr 1; funext w
    rw [ih (k + 1) (r + 1) (2 * m) u w hd.left (by omega),
      ih (k + 1) (r + 1) (2 * m + 1) w v hd.right (by omega)]

/-- `C⋆_{D,H}(K) = min_{u,v ∈ 𝒱} C_D(K;u,v)` -/
noncomputable def Cstar : WithTop ℚ := (S.V ×ˢ S.V).inf fun p => S.Cvar S.D S.k₀ S.m₀ p.1 p.2

/-- **Theorem 7.2 (global value, existence, determinism)**: `C⋆_{D,H}(K)` equals the minimum of
the objective over `𝔑_{D,H}(K)`; it is finite when `H ≥ max {2, k₀+1, |m₀|+1}`, in which case it
is attained; and the total tie key `κ` selects a unique representation, independently of any
enumeration order. -/
theorem variable_global (hH : 2 ≤ S.H) :
    S.Cstar = (RepCat S.H S.D S.k₀ S.m₀).inf S.costW ∧
    (HK S.k₀ S.m₀ ≤ S.H → S.Cstar ≠ ⊤ ∧
      ∃ R ∈ RepCat S.H S.D S.k₀ S.m₀, S.costW R = S.Cstar) ∧
    (HK S.k₀ S.m₀ ≤ S.H → ∃! R, R ∈ RepCat S.H S.D S.k₀ S.m₀ ∧
      ∀ R' ∈ RepCat S.H S.D S.k₀ S.m₀, S.kappa R ≤ S.kappa R') := by
  classical
  have hglob : S.Cstar = (RepCat S.H S.D S.k₀ S.m₀).inf S.costW := by
    rw [S.RepCat_eq_biUnion hH, Finset.inf_biUnion, Cstar]
    congr 1; funext p
    exact S.variable_correctness hH S.D S.k₀ 0 S.m₀ p.1 p.2 (IsDesc.root _ _) (by omega)
  refine ⟨hglob, fun hK => ?_, fun hK => ?_⟩
  · have hne : (RepCat S.H S.D S.k₀ S.m₀).Nonempty := ⟨_, rootLeaf_mem hK⟩
    obtain ⟨R, hR, hmin⟩ := (RepCat S.H S.D S.k₀ S.m₀).exists_min_image S.costW hne
    have heq : S.Cstar = S.costW R := by
      rw [hglob]
      exact le_antisymm (Finset.inf_le hR) (Finset.le_inf hmin)
    exact ⟨by rw [heq]; exact WithTop.coe_ne_top, R, hR, heq.symm⟩
  · have hne : (RepCat S.H S.D S.k₀ S.m₀).Nonempty := ⟨_, rootLeaf_mem hK⟩
    obtain ⟨R, hR, hmin⟩ := (RepCat S.H S.D S.k₀ S.m₀).exists_min_image S.kappa hne
    exact ⟨R, ⟨hR, hmin⟩, fun R' hR' => S.kappa_injective
      (le_antisymm (hR'.2 R hR) (hmin R' hR'.1))⟩

/-! ## Section 6: fixed tree -/

/-- unlabelled ordered tree shapes -/
inductive Shape
  | leaf
  | node (l r : Shape)
deriving DecidableEq

/-- the shape of a labelled tree -/
def shapeOf : LTree → Shape
  | LTree.leaf _ => Shape.leaf
  | LTree.node l r => Shape.node (shapeOf l) (shapeOf r)

/-- depth of a shape -/
def Shape.depth : Shape → ℕ
  | Shape.leaf => 0
  | Shape.node l r => max l.depth r.depth + 1

lemma depth_shapeOf (R : LTree) : (shapeOf R).depth = R.depth := by
  induction R with
  | leaf a => rfl
  | node l r ihl ihr => simp [shapeOf, Shape.depth, LTree.depth, ihl, ihr]

/-- **Definition 6.1**: the recursion on a fixed tree `T` -/
noncomputable def Cfix : Shape → ℕ → ℤ → ℚ → ℚ → WithTop ℚ
  | Shape.leaf, k, m, u, v => S.Phi k m u v
  | Shape.node TL TR, k, m, u, v => ((S.lb + S.ls : ℚ) : WithTop ℚ) +
      S.V.inf fun w => Cfix TL (k + 1) (2 * m) u w + Cfix TR (k + 1) (2 * m + 1) w v

open Classical in
/-- `𝔑_H(T_J;u,v)`: continuous labellings of the fixed shape `T` rooted at `J` -/
noncomputable def RsetS (T : Shape) (k : ℕ) (m : ℤ) (u v : ℚ) : Finset LTree :=
  (S.Rset T.depth k m u v).filter fun R => shapeOf R = T

lemma mem_RsetS {T : Shape} {k : ℕ} {m : ℤ} {u v : ℚ} {R : LTree} :
    R ∈ S.RsetS T k m u v ↔ shapeOf R = T ∧ R.maxHeight ≤ S.H ∧ WF k m R ∧ R.lval = u ∧ R.rval = v := by
  classical
  unfold RsetS
  rw [Finset.mem_filter, mem_Rset]
  constructor
  · rintro ⟨⟨-, h1, h2, h3, h4⟩, h5⟩; exact ⟨h5, h1, h2, h3, h4⟩
  · rintro ⟨h5, h1, h2, h3, h4⟩; exact ⟨⟨by rw [← h5, depth_shapeOf], h1, h2, h3, h4⟩, h5⟩

lemma RsetS_leaf (k : ℕ) (m : ℤ) (u v : ℚ) : S.RsetS Shape.leaf k m u v = S.Rset 0 k m u v := by
  ext R
  rw [mem_RsetS, mem_Rset]
  cases R with
  | leaf a => simp [shapeOf, LTree.depth]
  | node l r => simp [shapeOf, LTree.depth]

lemma RsetS_node (hH : 2 ≤ S.H) {TL TR : Shape} {k r : ℕ} {m : ℤ} (hd : IsDesc S.k₀ S.m₀ k m r)
    (hdD : r + (Shape.node TL TR).depth ≤ S.D) (u v : ℚ) :
    S.RsetS (Shape.node TL TR) k m u v = S.V.biUnion fun w =>
      (S.RsetS TL (k + 1) (2 * m) u w ×ˢ S.RsetS TR (k + 1) (2 * m + 1) w v).image
        fun p => node p.1 p.2 := by
  classical
  ext R
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.exists, mem_RsetS]
  cases R with
  | leaf a => simp [shapeOf]
  | node l r' =>
    simp only [shapeOf, Shape.node.injEq, node.injEq, maxHeight_node, WF, LTree.lval, LTree.rval]
    simp only [Shape.depth] at hdD
    constructor
    · rintro ⟨⟨hl, hr⟩, ⟨hhl, hhr⟩, ⟨hWl, hWr, hlr⟩, hu, hv⟩
      refine ⟨l.rval, ?_, l, r', ⟨⟨hl, hhl, hWl, hu, rfl⟩, hr, hhr, hWr, hlr.symm, hv⟩, rfl, rfl⟩
      refine (rootvals_mem hH hd.left hWl ?_ hhl).2
      rw [← depth_shapeOf, hl]; omega
    · rintro ⟨w, -, l', r'', ⟨⟨hl, hhl, hWl, hu, hw⟩, hr, hhr, hWr, hw', hv⟩, rfl, rfl⟩
      exact ⟨⟨hl, hr⟩, ⟨hhl, hhr⟩, ⟨hWl, hWr, hw.trans hw'.symm⟩, hu, hv⟩

/-- **Theorem 6.2 (correção para árvore fixa)**: for every node `J` of the fixed tree (a
descendant of `K` at relative depth `r`, with `r + depth(T) ≤ D`) and every pair of states,
`C_T(J;u,v) = min_{R ∈ 𝔑_H(T_J;u,v)} cost(R)` (`+∞` if empty). -/
theorem fixed_correctness (hH : 2 ≤ S.H) : ∀ (T : Shape) (k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + T.depth ≤ S.D →
      S.Cfix T k m u v = (S.RsetS T k m u v).inf S.costW := by
  classical
  intro T
  induction T with
  | leaf => intro k r m u v _ _; rw [Cfix, RsetS_leaf, S.Rset_zero_inf hH]
  | node TL TR ihl ihr =>
    intro k r m u v hd hdD
    rw [S.RsetS_node hH hd hdD, Finset.inf_biUnion, Cfix]
    simp only [inf_glue']
    rw [← const_add_inf]
    congr 1
    refine Finset.inf_congr rfl (fun w _ => ?_)
    simp only [Shape.depth] at hdD
    rw [ihl (k + 1) (r + 1) (2 * m) u w hd.left (by omega),
      ihr (k + 1) (r + 1) (2 * m + 1) w v hd.right (by omega)]

open Classical in
/-- the representations of `𝔑_{D,H}(K)` with shape `T` -/
noncomputable def RepShape (T : Shape) : Finset LTree :=
  (RepCat S.H S.D S.k₀ S.m₀).filter fun R => shapeOf R = T

/-- **Theorem 6.2 (global form)**: `min_{u,v ∈ 𝒱} C_T(K;u,v) = min_{R ∈ 𝔑_H(T)} cost(R)`, and the
`κ`-least labelling of `T` is unique. -/
theorem fixed_global (hH : 2 ≤ S.H) (T : Shape) (hT : T.depth ≤ S.D) :
    (S.V ×ˢ S.V).inf (fun p => S.Cfix T S.k₀ S.m₀ p.1 p.2) = (S.RepShape T).inf S.costW ∧
    ((S.RepShape T).Nonempty → ∃! R, R ∈ S.RepShape T ∧ ∀ R' ∈ S.RepShape T, S.kappa R ≤ S.kappa R') := by
  classical
  have hset : S.RepShape T = (S.V ×ˢ S.V).biUnion fun p => S.RsetS T S.k₀ S.m₀ p.1 p.2 := by
    ext R
    simp only [RepShape, Finset.mem_filter, mem_RepCat, Finset.mem_biUnion, Finset.mem_product,
      Prod.exists, mem_RsetS]
    constructor
    · rintro ⟨⟨hW, hd, hh⟩, hs⟩
      have := rootvals_mem (D := S.D) hH (IsDesc.root S.k₀ S.m₀) hW (by omega) hh
      exact ⟨R.lval, R.rval, ⟨this.1, this.2⟩, hs, hh, hW, rfl, rfl⟩
    · rintro ⟨u, v, -, hs, hh, hW, -, -⟩
      exact ⟨⟨hW, by rw [← depth_shapeOf, hs]; exact hT, hh⟩, hs⟩
  refine ⟨?_, fun hne => ?_⟩
  · rw [hset, Finset.inf_biUnion]
    congr 1; funext p
    exact S.fixed_correctness hH T S.k₀ 0 S.m₀ p.1 p.2 (IsDesc.root _ _) (by omega)
  · obtain ⟨R, hR, hmin⟩ := (S.RepShape T).exists_min_image S.kappa hne
    exact ⟨R, ⟨hR, hmin⟩, fun R' hR' => S.kappa_injective (le_antisymm (hR'.2 R hR) (hmin R' hR'.1))⟩

/-- all shapes of depth `≤ D` -/
def allShapes : ℕ → Finset Shape
  | 0 => {Shape.leaf}
  | D + 1 => insert Shape.leaf (((allShapes D) ×ˢ (allShapes D)).image fun p => Shape.node p.1 p.2)

lemma mem_allShapes : ∀ (D : ℕ) (T : Shape), T ∈ allShapes D ↔ T.depth ≤ D := by
  intro D
  induction D with
  | zero => intro T; cases T <;> simp [allShapes, Shape.depth]
  | succ D ih =>
    intro T
    cases T with
    | leaf => simp [allShapes, Shape.depth]
    | node l r =>
      simp only [allShapes, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_image,
        Finset.mem_product, Prod.exists, Shape.node.injEq, Shape.depth]
      constructor
      · rintro ⟨l', r', ⟨hl, hr⟩, rfl, rfl⟩
        rw [ih] at hl hr; omega
      · intro h
        exact ⟨l, r, ⟨(ih l).mpr (by omega), (ih r).mpr (by omega)⟩, rfl, rfl⟩

/-- **Corollary 7.3 (compatibilidade com a enumeração de formas)**:
`C⋆_{D,H}(K) = min_{T ∈ 𝔗_D(K)} min_{u,v ∈ 𝒱} C_T(K;u,v)`; the same canonical representation wins
on both sides (it is `κ`-least in its shape class). -/
theorem shape_enumeration (hH : 2 ≤ S.H) :
    S.Cstar = (allShapes S.D).inf (fun T => (S.V ×ˢ S.V).inf fun p => S.Cfix T S.k₀ S.m₀ p.1 p.2) ∧
    ∀ R ∈ RepCat S.H S.D S.k₀ S.m₀, (∀ R' ∈ RepCat S.H S.D S.k₀ S.m₀, S.kappa R ≤ S.kappa R') →
      shapeOf R ∈ allShapes S.D ∧ ∀ R' ∈ S.RepShape (shapeOf R), S.kappa R ≤ S.kappa R' := by
  classical
  refine ⟨?_, fun R hR hmin => ⟨?_, fun R' hR' => hmin R' (Finset.mem_filter.mp hR').1⟩⟩
  · have hset : RepCat S.H S.D S.k₀ S.m₀ = (allShapes S.D).biUnion S.RepShape := by
      ext R
      simp only [Finset.mem_biUnion, RepShape, Finset.mem_filter]
      constructor
      · intro hR
        refine ⟨shapeOf R, (mem_allShapes _ _).mpr ?_, hR, rfl⟩
        rw [depth_shapeOf]; exact (mem_RepCat.mp hR).2.1
      · rintro ⟨T, -, hR, -⟩; exact hR
    rw [(S.variable_global hH).1, hset, Finset.inf_biUnion]
    exact Finset.inf_congr rfl (fun T hT => (S.fixed_global hH T ((mem_allShapes _ _).mp hT)).1.symm)
  · rw [mem_allShapes, depth_shapeOf]; exact (mem_RepCat.mp hR).2.1

end Setup

end Artigo
