import RequestProject.Atoms
import RequestProject.Interp

/-!
# Dyadic trees labelled by atoms: assemblies (Definition 2.2)

A *represented assembly* rooted at the dyadic cell `J_{k,m}` is a full binary tree whose
leaves carry atoms supported exactly on the corresponding leaf cells, with matching values
at every shared boundary (continuity).  Its evaluation is the resulting continuous
piecewise-affine function.
-/

namespace Artigo

open Finset Set

/-- the closed dyadic cell `J_{k,m} = [m 2^{-k}, (m+1) 2^{-k}]` -/
def cellIcc (k : ℕ) (m : ℤ) : Set ℝ := Icc ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k)

/-- left endpoint (real) -/
noncomputable def cL (k : ℕ) (m : ℤ) : ℝ := (m : ℝ) / 2 ^ k
/-- right endpoint (real) -/
noncomputable def cR (k : ℕ) (m : ℤ) : ℝ := ((m : ℝ) + 1) / 2 ^ k

lemma cL_lt_cR (k : ℕ) (m : ℤ) : cL k m < cR k m := by
  unfold cL cR; apply div_lt_div_of_pos_right (by linarith) (by positivity)

lemma cL_child_left (k : ℕ) (m : ℤ) : cL (k + 1) (2 * m) = cL k m := by
  unfold cL; push_cast; rw [pow_succ]; field_simp

lemma cR_child_right (k : ℕ) (m : ℤ) : cR (k + 1) (2 * m + 1) = cR k m := by
  unfold cR; push_cast; rw [pow_succ]; field_simp; ring

lemma cR_child_left (k : ℕ) (m : ℤ) : cR (k + 1) (2 * m) = cL (k + 1) (2 * m + 1) := by
  unfold cR cL; push_cast; ring

lemma cellIcc_eq (k : ℕ) (m : ℤ) : cellIcc k m = Icc (cL k m) (cR k m) := rfl

lemma Atom.left_cast (a : Atom) : ((a.left : ℚ) : ℝ) = cL a.k a.m := by
  simp [Atom.left, cL]

lemma Atom.right_cast (a : Atom) : ((a.right : ℚ) : ℝ) = cR a.k a.m := by
  simp [Atom.right, cR]

lemma Atom.eval_left (a : Atom) : a.eval (cL a.k a.m) = a.lval := by
  rw [← a.left_cast, a.eval_eq]; rfl

lemma Atom.eval_right (a : Atom) : a.eval (cR a.k a.m) = a.rval := by
  rw [← a.right_cast, a.eval_eq]; rfl

/-- every atom is the linear interpolant of its endpoint values -/
lemma Atom.eval_interp (a : Atom) (x : ℝ) :
    a.eval x = (a.lval : ℝ) + ((a.rval : ℝ) - a.lval) * 2 ^ a.k * (x - cL a.k a.m) := by
  have hs : (a.s : ℝ) = 2 ^ a.k * ((a.rval : ℝ) - a.lval) := by
    rw [a.s_eq]; push_cast; ring
  have h1 : a.eval x = a.eval (cL a.k a.m) + a.s * (x - cL a.k a.m) := by
    simp only [Atom.eval]; ring
  rw [h1, a.eval_left, hs]; ring

/-- Labelled dyadic trees (representations). -/
inductive LTree
  | leaf (a : Atom)
  | node (l r : LTree)
deriving DecidableEq

namespace LTree

/-- leaves in spatial order -/
def leaves : LTree → List Atom
  | leaf a => [a]
  | node l r => l.leaves ++ r.leaves

/-- relative depth -/
def depth : LTree → ℕ
  | leaf _ => 0
  | node l r => max l.depth r.depth + 1

/-- number of internal nodes `I(R)` -/
def numInternal : LTree → ℕ
  | leaf _ => 0
  | node l r => l.numInternal + r.numInternal + 1

/-- number of leaves `|Λ(R)|` -/
def numLeaves (T : LTree) : ℕ := T.leaves.length

/-- value at the left end -/
def lval : LTree → ℚ
  | leaf a => a.lval
  | node l _ => l.lval

/-- value at the right end -/
def rval : LTree → ℚ
  | leaf a => a.rval
  | node _ r => r.rval

/-- well-formedness at the dyadic cell `J_{k,m}`: each leaf atom is supported exactly on its
leaf cell, and values agree at shared boundaries (continuity). -/
def WF : ℕ → ℤ → LTree → Prop
  | k, m, leaf a => a.k = k ∧ a.m = m
  | k, m, node l r => WF (k + 1) (2 * m) l ∧ WF (k + 1) (2 * m + 1) r ∧ l.rval = r.lval

/-- evaluation of a represented assembly rooted at `J_{k,m}` (half-open ownership: the
midpoint belongs to the right child). -/
noncomputable def eval : ℕ → ℤ → LTree → ℝ → ℝ
  | _, _, leaf a, x => a.eval x
  | k, m, node l r, x => if x < cL (k + 1) (2 * m + 1) then eval (k + 1) (2 * m) l x
      else eval (k + 1) (2 * m + 1) r x

/-- the maximal atomic height `ht_max(R)` -/
def maxHeight (T : LTree) : ℕ := T.leaves.foldr (fun a h => max a.height h) 0

lemma numLeaves_node (l r : LTree) : (node l r).numLeaves = l.numLeaves + r.numLeaves := by
  simp [numLeaves, leaves]

lemma numLeaves_pos (T : LTree) : 0 < T.numLeaves := by
  induction T with
  | leaf a => simp [numLeaves, leaves]
  | node l r ihl _ => rw [numLeaves_node]; omega

lemma numInternal_eq (T : LTree) : T.numInternal + 1 = T.numLeaves := by
  induction T with
  | leaf a => simp [numInternal, numLeaves, leaves]
  | node l r ihl ihr => rw [numLeaves_node]; simp only [numInternal]; omega

lemma numLeaves_le_pow_depth (T : LTree) : T.numLeaves ≤ 2 ^ T.depth := by
  induction T with
  | leaf a => simp [numLeaves, leaves, depth]
  | node l r ihl ihr =>
    rw [numLeaves_node]; simp only [depth, pow_succ]
    have h1 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (le_max_left l.depth r.depth)
    have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (le_max_right l.depth r.depth)
    omega

lemma maxHeight_le_iff {T : LTree} {H : ℕ} : T.maxHeight ≤ H ↔ ∀ a ∈ T.leaves, a.height ≤ H := by
  unfold maxHeight
  induction T.leaves with
  | nil => simp
  | cons a L ih => simp [ih]

lemma le_maxHeight {T : LTree} {a : Atom} (ha : a ∈ T.leaves) : a.height ≤ T.maxHeight :=
  (maxHeight_le_iff.mp le_rfl) a ha

/-! ### Basic properties of well-formed trees -/

lemma leaves_cell_sub : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → ∀ a ∈ T.leaves,
    cellIcc a.k a.m ⊆ cellIcc k m := by
  intro k m T
  induction T generalizing k m with
  | leaf a =>
    intro h b hb
    simp [leaves] at hb; subst hb; rw [h.1, h.2]
  | node l r ihl ihr =>
    intro h b hb
    simp only [leaves, List.mem_append] at hb
    rcases hb with hb | hb
    · refine (ihl h.1 b hb).trans ?_
      rw [cellIcc_eq, cellIcc_eq, cL_child_left, cR_child_left]
      exact Icc_subset_Icc le_rfl (le_trans (le_of_lt (cL_lt_cR _ _)) (by rw [cR_child_right]))
    · refine (ihr h.2.1 b hb).trans ?_
      rw [cellIcc_eq, cellIcc_eq, cR_child_right, ← cR_child_left]
      exact Icc_subset_Icc (by rw [← cL_child_left]; exact (cL_lt_cR _ _).le) le_rfl

lemma eval_at_left : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → T.eval k m (cL k m) = T.lval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp only [eval, lval]; rw [← h.1, ← h.2]; exact a.eval_left
  | node l r ihl _ =>
    intro h
    simp only [eval, lval]
    have : cL k m < cL (k + 1) (2 * m + 1) := by
      rw [← cR_child_left, ← cL_child_left]; exact cL_lt_cR _ _
    rw [if_pos this, ← cL_child_left]; exact ihl h.1

lemma eval_at_right : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → T.eval k m (cR k m) = T.rval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp only [eval, rval]; rw [← h.1, ← h.2]; exact a.eval_right
  | node l r _ ihr =>
    intro h
    simp only [eval, rval]
    have : ¬ cR k m < cL (k + 1) (2 * m + 1) := by
      rw [← cR_child_right]; exact not_lt.mpr (cL_lt_cR _ _).le
    rw [if_neg this, ← cR_child_right]; exact ihr h.2.1

/-- On every leaf cell (closed), the assembly coincides with the leaf atom. -/
lemma eval_leaf : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → ∀ a ∈ T.leaves,
    ∀ x ∈ cellIcc a.k a.m, T.eval k m x = a.eval x := by
  intro k m T
  induction T generalizing k m with
  | leaf a =>
    intro _ b hb x _
    simp [leaves] at hb; subst hb; rfl
  | node l r ihl ihr =>
    intro h b hb x hx
    simp only [leaves, List.mem_append] at hb
    simp only [eval]
    rcases hb with hb | hb
    · have hxl := leaves_cell_sub h.1 b hb hx
      rw [cellIcc_eq, cR_child_left] at hxl
      split_ifs with hlt
      · exact ihl h.1 b hb x hx
      · have hxe : x = cL (k + 1) (2 * m + 1) := le_antisymm hxl.2 (not_lt.mp hlt)
        rw [← ihl h.1 b hb x hx, hxe, eval_at_left h.2.1]
        have := eval_at_right h.1
        rw [cR_child_left] at this
        rw [this, h.2.2]
    · have hxr := leaves_cell_sub h.2.1 b hb hx
      rw [cellIcc_eq] at hxr
      rw [if_neg (not_lt.mpr hxr.1)]
      exact ihr h.2.1 b hb x hx

/-- Every point of the root cell lies in some leaf cell. -/
lemma exists_leaf_mem : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → ∀ x ∈ cellIcc k m,
    ∃ a ∈ T.leaves, x ∈ cellIcc a.k a.m := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h x hx; exact ⟨a, by simp [leaves], by rw [h.1, h.2]; exact hx⟩
  | node l r ihl ihr =>
    intro h x hx
    rw [cellIcc_eq] at hx
    by_cases hlt : x < cL (k + 1) (2 * m + 1)
    · obtain ⟨a, ha, hxa⟩ := ihl h.1 x (by
        rw [cellIcc_eq, cL_child_left, cR_child_left]; exact ⟨hx.1, hlt.le⟩)
      exact ⟨a, by simp [leaves, ha], hxa⟩
    · obtain ⟨a, ha, hxa⟩ := ihr h.2.1 x (by
        rw [cellIcc_eq, cR_child_right]; exact ⟨not_lt.mp hlt, hx.2⟩)
      exact ⟨a, by simp [leaves, ha], hxa⟩

/-- first leaf of a tree -/
def firstLeaf : LTree → Atom
  | leaf a => a
  | node l _ => l.firstLeaf

/-- last leaf of a tree -/
def lastLeaf : LTree → Atom
  | leaf a => a
  | node _ r => r.lastLeaf

lemma leaves_eq_cons (T : LTree) : ∃ L, T.leaves = T.firstLeaf :: L := by
  induction T with
  | leaf a => exact ⟨[], rfl⟩
  | node l r ihl _ =>
    obtain ⟨L, hL⟩ := ihl
    exact ⟨L ++ r.leaves, by simp [leaves, firstLeaf, hL]⟩

lemma leaves_getLast (T : LTree) : T.leaves.getLast? = some T.lastLeaf := by
  induction T with
  | leaf a => rfl
  | node l r _ ihr =>
    simp only [leaves, lastLeaf]
    rw [List.getLast?_append, ihr]; rfl

lemma firstLeaf_left : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T →
    cL T.firstLeaf.k T.firstLeaf.m = cL k m ∧ T.firstLeaf.lval = T.lval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp [firstLeaf, lval, h.1, h.2]
  | node l r ihl _ =>
    intro h
    obtain ⟨h1, h2⟩ := ihl h.1
    simp only [firstLeaf, lval]; rw [h1, cL_child_left]; exact ⟨rfl, h2⟩

lemma lastLeaf_right : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T →
    cR T.lastLeaf.k T.lastLeaf.m = cR k m ∧ T.lastLeaf.rval = T.rval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp [lastLeaf, rval, h.1, h.2]
  | node l r _ ihr =>
    intro h
    obtain ⟨h1, h2⟩ := ihr h.2.1
    simp only [lastLeaf, rval]; rw [h1, cR_child_right]; exact ⟨rfl, h2⟩

/-! ### Contiguity of the leaves and the ReLU form -/

/-- two atoms are contiguous: the first ends where the second begins, with equal values. -/
def Contig (a b : Atom) : Prop := cR a.k a.m = cL b.k b.m ∧ a.rval = b.lval

lemma leaves_isChain : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → List.IsChain Contig T.leaves := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro _; simp [leaves]
  | node l r ihl ihr =>
    intro h
    simp only [leaves]
    rw [List.isChain_append]
    refine ⟨ihl h.1, ihr h.2.1, ?_⟩
    intro x hx y hy
    rw [leaves_getLast] at hx
    obtain ⟨L, hL⟩ := leaves_eq_cons r
    rw [hL] at hy
    simp at hx hy; subst hx; subst hy
    obtain ⟨e1, e2⟩ := lastLeaf_right h.1
    obtain ⟨f1, f2⟩ := firstLeaf_left h.2.1
    refine ⟨?_, ?_⟩
    · rw [e1, f1, cR_child_left]
    · rw [e2, f2, h.2.2]

/-- `ρ(z) = max{0, z}` -/
noncomputable def relu (z : ℝ) : ℝ := max 0 z

/-- the hinge sum `∑_{j ≥ 1} (s_j - s_{j-1}) ρ(x - t_j)` over consecutive leaves -/
noncomputable def hingeSum (L : List Atom) (x : ℝ) : ℝ :=
  ((L.zip L.tail).map (fun p => ((p.2.s : ℝ) - p.1.s) * relu (x - cL p.2.k p.2.m))).sum

lemma hingeSum_cons_cons (a b : Atom) (L : List Atom) (x : ℝ) :
    hingeSum (a :: b :: L) x = ((b.s : ℝ) - a.s) * relu (x - cL b.k b.m) + hingeSum (b :: L) x := by
  simp [hingeSum, List.zip_cons_cons]

lemma hingeSum_zero_of_le : ∀ (L : List Atom) (x : ℝ), List.IsChain Contig L →
    ∀ b ∈ L.head?, x ≤ cR b.k b.m → hingeSum L x = 0 := by
  intro L
  induction L with
  | nil => intros; simp [hingeSum]
  | cons a L ih =>
    intro x hc b hb hx
    have hb' : a = b := by simpa using hb
    subst hb'
    cases L with
    | nil => simp [hingeSum]
    | cons c L' =>
      rw [hingeSum_cons_cons]
      have hac : Contig a c := (List.isChain_cons_cons.mp hc).1
      have hrest : List.IsChain Contig (c :: L') := (List.isChain_cons_cons.mp hc).2
      have h1 : relu (x - cL c.k c.m) = 0 := by
        unfold relu; rw [max_eq_left]; rw [← hac.1]; linarith
      rw [h1, mul_zero, zero_add]
      exact ih x hrest c (by simp) (le_trans hx (by rw [hac.1]; exact (cL_lt_cR _ _).le))

/-- In a contiguous chain, `a₀(x) + ∑ (s_j - s_{j-1}) ρ(x - t_j)` agrees with the atom whose
cell contains `x`. -/
lemma chain_relu : ∀ (L : List Atom), List.IsChain Contig L → ∀ a₀ ∈ L.head?,
    ∀ a ∈ L, ∀ x ∈ cellIcc a.k a.m, a₀.eval x + hingeSum L x = a.eval x := by
  intro L
  induction L with
  | nil => intros; simp_all
  | cons b L ih =>
    intro hc a₀ ha₀ a ha x hx
    have ha₀' : b = a₀ := by simpa using ha₀
    subst ha₀'
    cases L with
    | nil =>
      simp at ha; subst ha; simp [hingeSum]
    | cons c L' =>
      have hbc : Contig b c := (List.isChain_cons_cons.mp hc).1
      have hrest : List.IsChain Contig (c :: L') := (List.isChain_cons_cons.mp hc).2
      rw [hingeSum_cons_cons]
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · -- `x` in the first cell: all hinges vanish
        rw [cellIcc_eq] at hx
        have h1 : relu (x - cL c.k c.m) = 0 := by
          unfold relu; rw [max_eq_left]; rw [← hbc.1]; linarith [hx.2]
        rw [h1, mul_zero, zero_add, hingeSum_zero_of_le (c :: L') x hrest c (by simp)
          (le_trans hx.2 (by rw [hbc.1]; exact (cL_lt_cR _ _).le)), add_zero]
      · -- `x` beyond the first knot
        have hge : cL c.k c.m ≤ x := by
          have key : ∀ (L : List Atom), List.IsChain Contig L → ∀ c ∈ L.head?, ∀ d ∈ L,
              cL c.k c.m ≤ cL d.k d.m := by
            intro L
            induction L with
            | nil => intros; simp_all
            | cons e L ih2 =>
              intro hc' c' hc'' d hd
              have hc3 : e = c' := by simpa using hc''
              subst hc3
              simp only [List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact le_rfl
              · cases L with
                | nil => simp at hd
                | cons f L'' =>
                  have hef : Contig e f := (List.isChain_cons_cons.mp hc').1
                  have := ih2 (List.isChain_cons_cons.mp hc').2 f (by simp) d hd
                  refine le_trans ?_ this
                  rw [← hef.1]; exact (cL_lt_cR _ _).le
          have := key (c :: L') hrest c (by simp) a (List.mem_cons.mpr ha)
          rw [cellIcc_eq] at hx
          linarith [hx.1]
        have h1 : relu (x - cL c.k c.m) = x - cL c.k c.m := by
          unfold relu; rw [max_eq_right]; linarith
        rw [h1, ← ih hrest c (by simp) a (List.mem_cons.mpr ha) x hx]
        -- a₀(x) + (s_c - s_{a₀}) (x - t) = c(x)
        have e1 : b.eval x = b.rval + b.s * (x - cR b.k b.m) := by
          rw [← b.eval_right]; simp only [Atom.eval]; ring
        have e2 : c.eval x = c.lval + c.s * (x - cL c.k c.m) := by
          rw [← c.eval_left]; simp only [Atom.eval]; ring
        rw [e1, e2, hbc.1, hbc.2]; ring

/-- **Proposition 2.3 (ReLU form)**: an assembly with knots `t₀ < ⋯ < t_N` and slopes `s_j`
satisfies, on its root cell,
`g(x) = g(t₀) + s₀ (x - t₀) + ∑_{j=1}^{N-1} (s_j - s_{j-1}) ρ(x - t_j)`. -/
theorem eval_relu_form {k : ℕ} {m : ℤ} {T : LTree} (h : WF k m T) :
    ∀ x ∈ cellIcc k m, T.eval k m x =
      T.eval k m (cL k m) + (T.firstLeaf.s : ℝ) * (x - cL k m) + hingeSum T.leaves x := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := exists_leaf_mem h x hx
  rw [eval_leaf h a ha x hxa]
  obtain ⟨L, hL⟩ := leaves_eq_cons T
  have hchain := leaves_isChain h
  have := chain_relu T.leaves hchain T.firstLeaf (by rw [hL]; simp) a ha x hxa
  rw [← this, eval_at_left h]
  obtain ⟨f1, f2⟩ := firstLeaf_left h
  have : T.firstLeaf.eval x = T.firstLeaf.lval + T.firstLeaf.s * (x - cL T.firstLeaf.k T.firstLeaf.m) := by
    rw [← T.firstLeaf.eval_left]; simp only [Atom.eval]; ring
  rw [this, f1, f2]

/-! ### Assemblies -/

/-- the class `𝒜(K)` of assemblies on the root `K = J_{k₀,m₀}` -/
def Assemblies (k₀ : ℕ) (m₀ : ℤ) : Set (ℝ → ℝ) := {g | ∃ T, WF k₀ m₀ T ∧ g = T.eval k₀ m₀}

end LTree

end Artigo
