module
public import RequestProject.Sec7.Bits
public import RequestProject.Sec7.Address
public import RequestProject.Lib.Assembly
@[expose] public section

/-!
# Section 7.7: truncated catalogues (Definition 7.22, Theorem 7.23, Proposition 7.24)

A represented assembly over the dyadic root `K = J_{k₀,m₀}` is a full binary tree whose leaves
carry atoms (equivalently their addresses, by the bijection of Theorem 3.6); the atom of a leaf has
exactly the support prescribed by the position of the leaf, and the lines agree at the shared
boundary points.
-/

open Finset

namespace Dyadic.Lib

/-! ### Continuity of assemblies on closed sets -/

/-- An assembly representation on a closed set yields continuity on that set. -/
lemma IsAssemblyRep.continuousOn {K : Set ℝ} {g : ℝ → ℝ} {Λ : Finset Atom} (hK : IsClosed K)
    (h : IsAssemblyRep K g Λ) : ContinuousOn g K := by
  let F : Λ → Set ℝ := fun a => a.1.cell ∩ K
  have hU : (⋃ a, F a) = K := by
    ext x; constructor
    · intro hx; obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx; exact ha.2
    · intro hx
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (h.2.1 hx)
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, hxa, hx⟩
  rw [← hU]
  refine (locallyFinite_of_finite F).continuousOn_iUnion (fun a => isClosed_Icc.inter hK)
    (fun a => ?_)
  have hl : ContinuousOn (fun x => a.1.line x) (F a) := by
    unfold Atom.line; fun_prop
  exact hl.congr (fun x hx => h.2.2.1 a.1 a.2 x hx)

/-! ### Labelled dyadic trees -/

/-- A full binary tree whose leaves carry atoms. -/
inductive LTree
  | leaf (a : Atom)
  | node (l r : LTree)
  deriving DecidableEq

namespace LTree

/-- Depth (relative to the root). -/
def depth : LTree → ℕ
  | leaf _ => 0
  | node l r => max l.depth r.depth + 1

/-- Leaves in spatial (left-to-right) order. -/
def leaves : LTree → List Atom
  | leaf a => [a]
  | node l r => l.leaves ++ r.leaves

/-- Support condition: placed at the cell `J_{k,m}`, every leaf carries an atom whose support is
exactly the cell of its position (children of `J_{k,m}` are `J_{k+1,2m}` and `J_{k+1,2m+1}`). -/
def Fits : LTree → ℕ → ℤ → Prop
  | leaf a, k, m => a.k = k ∧ a.m = m
  | node l r, k, m => l.Fits (k + 1) (2 * m) ∧ r.Fits (k + 1) (2 * m + 1)

/-- Pre-order skeleton: `0` for an internal node, `1` for a leaf. -/
def pre : LTree → List Bool
  | leaf _ => [true]
  | node l r => false :: (l.pre ++ r.pre)

end LTree

/-- The dyadic cell `J_{k,m}` as a subset of `ℝ`. -/
def cellK (k : ℕ) (m : ℤ) : Set ℝ := Set.Icc ((m : ℝ) / 2 ^ k) ((m + 1) / 2 ^ k)

lemma cellK_split (k : ℕ) (m : ℤ) : cellK k m = cellK (k + 1) (2 * m) ∪ cellK (k + 1) (2 * m + 1) := by
  unfold cellK
  have e1 : ((2 * m : ℤ) : ℝ) / 2 ^ (k + 1) = m / 2 ^ k := by push_cast; rw [pow_succ]; field_simp
  have e2 : ((2 * m : ℤ) : ℝ) + 1 = ((2 * m + 1 : ℤ) : ℝ) := by push_cast; ring
  have e3 : ((2 * m + 1 : ℤ) : ℝ) + 1 = (m + 1) * 2 := by push_cast; ring
  rw [e1, e2, e3, show ((m : ℝ) + 1) * 2 / 2 ^ (k + 1) = (m + 1) / 2 ^ k by
    rw [pow_succ]; field_simp]
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  rw [Set.Icc_union_Icc_eq_Icc]
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; push_cast; rw [pow_succ]; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; push_cast; rw [pow_succ]; nlinarith

lemma cellK_interior_disjoint (k : ℕ) (m : ℤ) :
    Disjoint (interior (cellK (k + 1) (2 * m))) (interior (cellK (k + 1) (2 * m + 1))) := by
  unfold cellK
  rw [interior_Icc, interior_Icc]
  apply Set.disjoint_left.2
  intro x hx hx'
  have : ((2 * m : ℤ) : ℝ) + 1 = ((2 * m + 1 : ℤ) : ℝ) := by push_cast; ring
  rw [this] at hx
  linarith [hx.2, hx'.1]

lemma Atom.cell_eq_cellK (a : Atom) : a.cell = cellK a.k a.m := by
  simp [Atom.cell, cellK, Atom.left, Atom.right]

lemma interior_mono_disjoint {A B A' B' : Set ℝ} (hA : A ⊆ A') (hB : B ⊆ B')
    (h : Disjoint (interior A') (interior B')) : Disjoint (interior A) (interior B) :=
  h.mono (interior_mono hA) (interior_mono hB)

namespace LTree

lemma leaf_cell_subset : ∀ (t : LTree) (k : ℕ) (m : ℤ), t.Fits k m → ∀ a ∈ t.leaves,
    a.cell ⊆ cellK k m
  | leaf b, k, m, h, a, ha => by
    simp only [leaves, List.mem_singleton] at ha; subst ha
    rw [Atom.cell_eq_cellK, h.1, h.2]
  | node l r, k, m, h, a, ha => by
    simp only [leaves, List.mem_append] at ha
    rw [cellK_split]
    rcases ha with ha | ha
    · exact (leaf_cell_subset l _ _ h.1 a ha).trans Set.subset_union_left
    · exact (leaf_cell_subset r _ _ h.2 a ha).trans Set.subset_union_right

lemma cover : ∀ (t : LTree) (k : ℕ) (m : ℤ), t.Fits k m → cellK k m ⊆ ⋃ a ∈ t.leaves, a.cell
  | leaf b, k, m, h => by
    intro x hx; simp only [leaves, List.mem_singleton, Set.iUnion_iUnion_eq_left]
    rwa [Atom.cell_eq_cellK, h.1, h.2]
  | node l r, k, m, h => by
    rw [cellK_split]
    rintro x (hx | hx)
    · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (cover l _ _ h.1 hx)
      exact Set.mem_iUnion₂.2 ⟨a, by simp [leaves, ha], hxa⟩
    · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (cover r _ _ h.2 hx)
      exact Set.mem_iUnion₂.2 ⟨a, by simp [leaves, ha], hxa⟩

lemma disjoint_leaves : ∀ (t : LTree) (k : ℕ) (m : ℤ), t.Fits k m → ∀ a ∈ t.leaves,
    ∀ b ∈ t.leaves, a ≠ b → Disjoint (interior a.cell) (interior b.cell)
  | leaf c, k, m, _, a, ha, b, hb, hab => by
    simp only [leaves, List.mem_singleton] at ha hb; subst ha; subst hb; exact absurd rfl hab
  | node l r, k, m, h, a, ha, b, hb, hab => by
    simp only [leaves, List.mem_append] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact disjoint_leaves l _ _ h.1 a ha b hb hab
    · exact interior_mono_disjoint (leaf_cell_subset l _ _ h.1 a ha)
        (leaf_cell_subset r _ _ h.2 b hb) (cellK_interior_disjoint k m)
    · exact (interior_mono_disjoint (leaf_cell_subset l _ _ h.1 b hb)
        (leaf_cell_subset r _ _ h.2 a ha) (cellK_interior_disjoint k m)).symm
    · exact disjoint_leaves r _ _ h.2 a ha b hb hab

end LTree

/-! ### Represented assemblies and catalogues (Definition 7.22) -/

/-- Boundary agreement of the leaf lines. -/
def Agree (t : LTree) : Prop :=
  ∀ a ∈ t.leaves, ∀ b ∈ t.leaves, ∀ x ∈ a.cell ∩ b.cell, a.line x = b.line x

/-- `Eval(𝓡)`: the function of a represented assembly (`0` outside the leaves). -/
noncomputable def evalRep (t : LTree) (x : ℝ) : ℝ :=
  open Classical in
  if h : ∃ a ∈ t.leaves, x ∈ a.cell then (Classical.choose h).line x else 0

lemma evalRep_eq {t : LTree} (ht : Agree t) {a : Atom} (ha : a ∈ t.leaves) {x : ℝ}
    (hx : x ∈ a.cell) : evalRep t x = a.line x := by
  have h : ∃ a ∈ t.leaves, x ∈ a.cell := ⟨a, ha, hx⟩
  unfold evalRep
  rw [dif_pos h]
  obtain ⟨hb, hxb⟩ := Classical.choose_spec h
  exact ht _ hb a ha x ⟨hxb, hx⟩

/-- The maximal height `ht_max(𝓡)` of a represented assembly. -/
def htMax (t : LTree) : ℕ := (t.leaves.map Atom.height).foldr max 0

/-- The root threshold `H_K = max{2, k₀+1, |m₀|+1}`. -/
def HK (k0 : ℕ) (m0 : ℤ) : ℕ := max 2 (max (k0 + 1) (m0.natAbs + 1))

/-- **Definition 7.22**, eq. (91): the representations `𝓡^𝓛_{D,H}(K)` over `K = J_{k₀,m₀}`:
trees of relative depth `≤ D` with leaves of exact support, agreeing at the boundaries, all of
whose atoms have height `≤ H`. -/
def RR (k0 : ℕ) (m0 : ℤ) (D H : ℕ) : Set LTree :=
  {t | t.Fits k0 m0 ∧ t.depth ≤ D ∧ Agree t ∧ htMax t ≤ H}

/-- **Definition 7.22**, eq. (92): the catalogue `Σ^𝓛_{D,H}(K) = Eval(𝓡^𝓛_{D,H}(K))`. -/
def Cat (k0 : ℕ) (m0 : ℤ) (D H : ℕ) : Set (ℝ → ℝ) := evalRep '' RR k0 m0 D H

lemma htMax_le_iff {t : LTree} {H : ℕ} : htMax t ≤ H ↔ ∀ a ∈ t.leaves, a.height ≤ H := by
  unfold htMax
  induction t.leaves with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Eq. (92): every catalogue element is a continuous assembly on `K`. -/
theorem Cat_subset_Asm (k0 : ℕ) (m0 : ℤ) (D H : ℕ) : Cat k0 m0 D H ⊆ Asm (cellK k0 m0) := by
  rintro g ⟨t, ⟨hfit, -, hag, -⟩, rfl⟩
  have hrep : IsAssemblyRep (cellK k0 m0) (evalRep t) t.leaves.toFinset := by
    refine ⟨fun a ha b hb hab => ?_, fun x hx => ?_, fun a ha x hx => ?_, fun a ha b hb x hx => ?_⟩
    · exact t.disjoint_leaves k0 m0 hfit a (List.mem_toFinset.1 ha) b (List.mem_toFinset.1 hb) hab
    · obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (t.cover k0 m0 hfit hx)
      exact Set.mem_iUnion₂.2 ⟨a, List.mem_toFinset.2 ha, hxa⟩
    · exact evalRep_eq hag (List.mem_toFinset.1 ha) hx.1
    · exact hag a (List.mem_toFinset.1 ha) b (List.mem_toFinset.1 hb) x hx
  exact ⟨hrep.continuousOn isClosed_Icc, _, hrep⟩

/-! ### Counting -/

/-- `T₀ = 1`, `T_{d+1} = 1 + T_d²`: the number of tree shapes of depth `≤ d`. -/
def Tshape : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + Tshape d ^ 2

/-- All labelled trees of depth `≤ d` with labels in `S`. -/
def allTrees (S : Finset Atom) : ℕ → Finset LTree
  | 0 => S.image LTree.leaf
  | d + 1 => S.image LTree.leaf ∪
      (allTrees S d ×ˢ allTrees S d).image (fun p => LTree.node p.1 p.2)

lemma mem_allTrees (S : Finset Atom) : ∀ (d : ℕ) (t : LTree),
    t ∈ allTrees S d ↔ t.depth ≤ d ∧ ∀ a ∈ t.leaves, a ∈ S
  | 0, LTree.leaf a => by simp [allTrees, LTree.depth, LTree.leaves]
  | 0, LTree.node l r => by simp [allTrees, LTree.depth]
  | d + 1, LTree.leaf a => by simp [allTrees, LTree.depth, LTree.leaves]
  | d + 1, LTree.node l r => by
    simp only [allTrees, mem_union, mem_image, mem_product, LTree.depth, LTree.leaves,
      List.mem_append]
    constructor
    · rintro (⟨a, -, h⟩ | ⟨⟨l', r'⟩, ⟨hl, hr⟩, h⟩)
      · cases h
      · simp only [LTree.node.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [mem_allTrees S d] at hl hr
        dsimp only at hl hr ⊢
        refine ⟨by omega, fun a ha => ?_⟩
        rcases ha with ha | ha
        · exact hl.2 a ha
        · exact hr.2 a ha
    · rintro ⟨hd, hS⟩
      exact Or.inr ⟨⟨l, r⟩, ⟨(mem_allTrees S d l).2 ⟨by omega, fun a ha => hS a (Or.inl ha)⟩,
        (mem_allTrees S d r).2 ⟨by omega, fun a ha => hS a (Or.inr ha)⟩⟩, rfl⟩

lemma card_allTrees_le (S : Finset Atom) (hS : 1 ≤ S.card) :
    ∀ d, (allTrees S d).card ≤ Tshape d * S.card ^ (2 ^ d)
  | 0 => by simp [allTrees, Tshape]; exact card_image_le
  | d + 1 => by
    have ih := card_allTrees_le S hS d
    simp only [allTrees, Tshape]
    have h1 : (S.image LTree.leaf).card ≤ S.card := card_image_le
    have h2 : ((allTrees S d ×ˢ allTrees S d).image (fun p => LTree.node p.1 p.2)).card ≤
        (allTrees S d).card ^ 2 := by
      refine card_image_le.trans ?_; rw [card_product, sq]
    have h3 : S.card ≤ S.card ^ (2 ^ (d + 1)) := by
      calc S.card = S.card ^ 1 := (pow_one _).symm
        _ ≤ S.card ^ (2 ^ (d + 1)) := Nat.pow_le_pow_right hS Nat.one_le_two_pow
    have h4 : (allTrees S d).card ^ 2 ≤ (Tshape d * S.card ^ (2 ^ d)) ^ 2 :=
      Nat.pow_le_pow_left ih 2
    have e : (Tshape d * S.card ^ (2 ^ d)) ^ 2 = Tshape d ^ 2 * S.card ^ (2 ^ (d + 1)) := by
      rw [mul_pow, ← pow_mul, show 2 ^ d * 2 = 2 ^ (d + 1) from (pow_succ 2 d).symm]
    calc _ ≤ (S.image LTree.leaf).card +
          ((allTrees S d ×ˢ allTrees S d).image (fun p => LTree.node p.1 p.2)).card :=
          card_union_le _ _
      _ ≤ S.card ^ (2 ^ (d + 1)) + Tshape d ^ 2 * S.card ^ (2 ^ (d + 1)) := by omega
      _ = (1 + Tshape d ^ 2) * S.card ^ (2 ^ (d + 1)) := by ring

lemma RR_subset_allTrees (k0 : ℕ) (m0 : ℤ) (D H : ℕ) :
    RR k0 m0 D H ⊆ ↑(allTrees (atomsUpTo H) D) := by
  rintro t ⟨-, hd, -, hh⟩
  rw [mem_coe, mem_allTrees]
  exact ⟨hd, fun a ha => mem_atomsUpTo.2 (htMax_le_iff.1 hh a ha)⟩

/-- The root leaf `(k₀, m₀, 0, 1)`. -/
def rootLeaf (k0 : ℕ) (m0 : ℤ) : LTree := LTree.leaf ⟨k0, m0, 0, 1, one_ne_zero⟩

lemma rootLeaf_mem {k0 : ℕ} {m0 : ℤ} {D H : ℕ} (hH : HK k0 m0 ≤ H) :
    rootLeaf k0 m0 ∈ RR k0 m0 D H := by
  refine ⟨⟨rfl, rfl⟩, by simp [rootLeaf, LTree.depth], ?_, ?_⟩
  · intro a ha b hb x _
    simp only [rootLeaf, LTree.leaves, List.mem_singleton] at ha hb; rw [ha, hb]
  · rw [htMax_le_iff]
    intro a ha
    simp only [rootLeaf, LTree.leaves, List.mem_singleton] at ha
    subst ha
    rw [Atom.height_le_iff]
    unfold HK at hH
    simp only [ratHeight, Rat.num_zero, Int.natAbs_zero, Rat.den_zero, Rat.num_one,
      Int.natAbs_one, Rat.den_one]
    omega

/-! ### Serialization and the shortlex order -/

/-- The stream `ser^♯(𝓡)`: the pre-order skeleton, then `γ(n^♯(J) + 1)` for the leaves in spatial
order. -/
noncomputable def serRep (t : LTree) : List Bool :=
  t.pre ++ (t.leaves.map fun a => eliasGamma (addrSharp a + 1)).flatten

/-- Shortlex key: first the length, then the lexicographic order. -/
def shortlex (w : List Bool) : ℕ ×ₗ List Bool := toLex (w.length, w)

lemma shortlex_injective : Function.Injective shortlex := by
  intro w w' h
  simp only [shortlex, toLex_inj, Prod.mk.injEq] at h
  exact h.2

namespace LTree

lemma pre_append_inj : ∀ (t t' : LTree) (x y : List Bool), t.pre ++ x = t'.pre ++ y →
    t.pre = t'.pre ∧ x = y
  | leaf a, leaf b, x, y, h => by simpa [pre] using h
  | leaf a, node l r, x, y, h => by simp [pre] at h
  | node l r, leaf b, x, y, h => by simp [pre] at h
  | node l r, node l' r', x, y, h => by
    simp only [pre, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨h1, h2⟩ := pre_append_inj l l' _ _ h
    obtain ⟨h3, h4⟩ := pre_append_inj r r' _ _ h2
    exact ⟨by simp [pre, h1, h3], h4⟩

lemma count_pre : ∀ t : LTree, t.pre.count true = t.leaves.length
  | leaf a => by simp [pre, leaves]
  | node l r => by simp [pre, leaves, List.count_append, count_pre l, count_pre r]

lemma eq_of_pre_leaves : ∀ (t t' : LTree), t.pre = t'.pre → t.leaves = t'.leaves → t = t'
  | leaf a, leaf b, _, h => by simpa [leaves] using h
  | leaf a, node l r, h, _ => by simp [pre] at h
  | node l r, leaf b, h, _ => by simp [pre] at h
  | node l r, node l' r', h1, h2 => by
    simp only [pre, List.cons.injEq, true_and] at h1
    obtain ⟨hl, hr⟩ := pre_append_inj l l' _ _ h1
    have hlen : l.leaves.length = l'.leaves.length := by rw [← count_pre, ← count_pre, hl]
    simp only [leaves] at h2
    obtain ⟨e1, e2⟩ := List.append_inj h2 hlen
    rw [eq_of_pre_leaves l l' hl e1, eq_of_pre_leaves r r' hr e2]

end LTree

lemma serRep_injective : Function.Injective serRep := by
  intro t t' h
  unfold serRep at h
  obtain ⟨hpre, hrest⟩ := LTree.pre_append_inj t t' _ _ h
  have hlen : t.leaves.length = t'.leaves.length := by
    rw [← LTree.count_pre, ← LTree.count_pre, hpre]
  -- decode the gamma part
  set A : List ℕ := t.leaves.map (fun a => addrSharp a + 1)
  set A' : List ℕ := t'.leaves.map (fun a => addrSharp a + 1)
  have hA : (t.leaves.map fun a => eliasGamma (addrSharp a + 1)).flatten =
      (A.map eliasGamma).flatten := by simp [A, Function.comp_def]
  have hA' : (t'.leaves.map fun a => eliasGamma (addrSharp a + 1)).flatten =
      (A'.map eliasGamma).flatten := by simp [A', Function.comp_def]
  rw [hA, hA'] at hrest
  have d1 := decMany_flatten gammaDec eliasGamma A (fun n hn r => gammaDec_eliasGamma (by
    simp only [A, List.mem_map] at hn; obtain ⟨a, -, rfl⟩ := hn; omega) r) []
  have d2 := decMany_flatten gammaDec eliasGamma A' (fun n hn r => gammaDec_eliasGamma (by
    simp only [A', List.mem_map] at hn; obtain ⟨a, -, rfl⟩ := hn; omega) r) []
  have hlA : A.length = A'.length := by simp [A, A', hlen]
  rw [hrest, hlA, d2] at d1
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at d1
  have hinj : Function.Injective (fun a => addrSharp a + 1) :=
    fun a b h => addrSharp_bijective.1 (by simpa using h)
  exact LTree.eq_of_pre_leaves t t' hpre ((List.map_injective_iff.2 hinj) d1.symm)

/-! ### Theorem 7.23 -/

/-- `g` minimises `J` over the catalogue `Σ_{D,H}(K)`. -/
def IsCatMin (k0 : ℕ) (m0 : ℤ) (D H : ℕ) (J : (ℝ → ℝ) → ℝ) (g : ℝ → ℝ) : Prop :=
  g ∈ Cat k0 m0 D H ∧ ∀ g' ∈ Cat k0 m0 D H, J g ≤ J g'

/-- `t` is the canonical representation selected in `Σ_{D,H}(K)`: it represents a minimiser and
its stream is shortlex-least among the representations of minimisers. -/
def IsCanonical (k0 : ℕ) (m0 : ℤ) (D H : ℕ) (J : (ℝ → ℝ) → ℝ) (t : LTree) : Prop :=
  t ∈ RR k0 m0 D H ∧ IsCatMin k0 m0 D H J (evalRep t) ∧
    ∀ t' ∈ RR k0 m0 D H, IsCatMin k0 m0 D H J (evalRep t') →
      shortlex (serRep t) ≤ shortlex (serRep t')

/-- **Theorem 7.23** (finiteness, existence and canonical tie-break).  For `H ≥ H_K`:
`1 ≤ |Σ_{D,H}(K)| ≤ |𝓡_{D,H}(K)| ≤ T_D |𝓛_H|^{2^D} < ∞` (93); every functional attains its
minimum on the catalogue (94) (a functional on `Σ_{D,H}(K)` is given here as a functional on all
functions, of which only the values on the catalogue matter); and among all minimisers the
shortlex-least stream selects a unique representation (hence a unique function). -/
theorem catalog_finite_canonical (k0 : ℕ) (m0 : ℤ) (D H : ℕ) (hH : HK k0 m0 ≤ H) :
    (RR k0 m0 D H).Finite ∧ (Cat k0 m0 D H).Finite ∧
    1 ≤ (Cat k0 m0 D H).ncard ∧ (Cat k0 m0 D H).ncard ≤ (RR k0 m0 D H).ncard ∧
    (RR k0 m0 D H).ncard ≤ Tshape D * (atomsUpTo H).card ^ (2 ^ D) ∧
    (∀ J : (ℝ → ℝ) → ℝ, ∃ g, IsCatMin k0 m0 D H J g) ∧
    (∀ J : (ℝ → ℝ) → ℝ, ∃! t, IsCanonical k0 m0 D H J t) := by
  have hfinR : (RR k0 m0 D H).Finite :=
    (allTrees (atomsUpTo H) D).finite_toSet.subset (RR_subset_allTrees k0 m0 D H)
  have hfinC : (Cat k0 m0 D H).Finite := hfinR.image _
  have hneR : (RR k0 m0 D H).Nonempty := ⟨_, rootLeaf_mem hH⟩
  have hneC : (Cat k0 m0 D H).Nonempty := hneR.image _
  have hS : 1 ≤ (atomsUpTo H).card := by
    have := (rootLeaf_mem (D := D) hH).2.2.2
    rw [htMax_le_iff] at this
    exact card_pos.2 ⟨_, mem_atomsUpTo.2 (this ⟨k0, m0, 0, 1, one_ne_zero⟩
      (by simp [rootLeaf, LTree.leaves]))⟩
  have hmin : ∀ J : (ℝ → ℝ) → ℝ, ∃ g, IsCatMin k0 m0 D H J g := by
    intro J
    obtain ⟨g, hg, hmin⟩ := Set.exists_min_image _ J hfinC hneC
    exact ⟨g, hg, hmin⟩
  refine ⟨hfinR, hfinC, (Set.ncard_pos hfinC).2 hneC, Set.ncard_image_le hfinR,
    (Set.ncard_le_ncard (RR_subset_allTrees k0 m0 D H) (allTrees _ D).finite_toSet).trans
      (by rw [Set.ncard_coe_finset]; exact card_allTrees_le _ hS D), hmin, fun J => ?_⟩
  -- the minimisers' representations form a finite nonempty set
  obtain ⟨g, hg⟩ := hmin J
  set Mset := {t | t ∈ RR k0 m0 D H ∧ IsCatMin k0 m0 D H J (evalRep t)}
  have hfinM : Mset.Finite := hfinR.subset (fun t ht => ht.1)
  have hneM : Mset.Nonempty := by
    obtain ⟨t, ht, rfl⟩ := hg.1
    exact ⟨t, ht, hg⟩
  obtain ⟨t, ht, htmin⟩ := Set.exists_min_image _ (fun t => shortlex (serRep t)) hfinM hneM
  refine ⟨t, ⟨ht.1, ht.2, fun t' ht' hmin' => htmin t' ⟨ht', hmin'⟩⟩, fun t' ht' => ?_⟩
  have h1 := ht'.2.2 t ht.1 ht.2
  have h2 := htmin t' ⟨ht'.1, ht'.2.1⟩
  exact serRep_injective (shortlex_injective (le_antisymm h1 h2))

/-! ### Proposition 7.24 -/

lemma RR_mono {k0 : ℕ} {m0 : ℤ} {D D' H H' : ℕ} (hD : D ≤ D') (hH : H ≤ H') :
    RR k0 m0 D H ⊆ RR k0 m0 D' H' :=
  fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2.trans hD, h3, h4.trans hH⟩

/-- **Proposition 7.24** (consistency under truncation).  (95) the catalogues increase with `D`
and `H`; the minimal values are non-increasing; and if a functional has a global minimiser on the
union of the catalogues, then the shortlex-least representation of a global minimiser exists,
belongs to some finite catalogue, and from that pair of truncations on it is the canonical
selection of every larger catalogue. -/
theorem catalog_truncation (k0 : ℕ) (m0 : ℤ) :
    (∀ D D' H H' : ℕ, D ≤ D' → H ≤ H' → Cat k0 m0 D H ⊆ Cat k0 m0 D' H') ∧
    (∀ (J : (ℝ → ℝ) → ℝ) (D D' H H' : ℕ) (g g' : ℝ → ℝ), D ≤ D' → H ≤ H' →
      IsCatMin k0 m0 D H J g → IsCatMin k0 m0 D' H' J g' → J g' ≤ J g) ∧
    (∀ J : (ℝ → ℝ) → ℝ,
      (∃ g ∈ ⋃ D, ⋃ H, Cat k0 m0 D H, ∀ g' ∈ ⋃ D, ⋃ H, Cat k0 m0 D H, J g ≤ J g') →
      ∃ (tstar : LTree) (D₀ H₀ : ℕ), tstar ∈ RR k0 m0 D₀ H₀ ∧
        (∀ g' ∈ ⋃ D, ⋃ H, Cat k0 m0 D H, J (evalRep tstar) ≤ J g') ∧
        (∀ (t : LTree) (D H : ℕ), t ∈ RR k0 m0 D H →
          (∀ g' ∈ ⋃ D, ⋃ H, Cat k0 m0 D H, J (evalRep t) ≤ J g') →
          shortlex (serRep tstar) ≤ shortlex (serRep t)) ∧
        ∀ D H : ℕ, D₀ ≤ D → H₀ ≤ H → IsCanonical k0 m0 D H J tstar) := by
  have hmono : ∀ D D' H H' : ℕ, D ≤ D' → H ≤ H' → Cat k0 m0 D H ⊆ Cat k0 m0 D' H' :=
    fun D D' H H' hD hH => Set.image_mono (RR_mono hD hH)
  refine ⟨hmono, fun J D D' H H' g g' hD hH hg hg' => hg'.2 g (hmono D D' H H' hD hH hg.1),
    fun J ⟨g, hgU, hgmin⟩ => ?_⟩
  set U := ⋃ D, ⋃ H, Cat k0 m0 D H
  -- representations of global minimisers
  set A := {t : LTree | (∃ D H, t ∈ RR k0 m0 D H) ∧ ∀ g' ∈ U, J (evalRep t) ≤ J g'}
  have hneA : A.Nonempty := by
    obtain ⟨D, hD⟩ := Set.mem_iUnion.1 hgU
    obtain ⟨H, hH⟩ := Set.mem_iUnion.1 hD
    obtain ⟨t, ht, rfl⟩ := hH
    exact ⟨t, ⟨D, H, ht⟩, hgmin⟩
  -- least length, then finitely many candidates of that length
  classical
  have hex : ∃ L, ∃ t ∈ A, (serRep t).length = L := by
    obtain ⟨t, ht⟩ := hneA; exact ⟨_, t, ht, rfl⟩
  set L0 := Nat.find hex
  obtain ⟨t0, ht0, hL0⟩ := Nat.find_spec hex
  set A0 := {t ∈ A | (serRep t).length = L0}
  have hfin0 : A0.Finite := by
    have : A0 ⊆ serRep ⁻¹' {w | w.length = L0} := fun t ht => ht.2
    exact ((List.finite_length_eq Bool L0).preimage serRep_injective.injOn).subset this
  obtain ⟨tstar, hts, htsmin⟩ := Set.exists_min_image _ (fun t => shortlex (serRep t)) hfin0
    ⟨t0, ht0, hL0⟩
  have hleast : ∀ t ∈ A, shortlex (serRep tstar) ≤ shortlex (serRep t) := by
    intro t ht
    have hle : L0 ≤ (serRep t).length := Nat.find_min' hex ⟨t, ht, rfl⟩
    rcases Nat.lt_or_ge L0 (serRep t).length with hlt | hge
    · apply le_of_lt
      simp only [shortlex]
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl (by rw [hts.2]; exact hlt)
    · exact htsmin t ⟨ht, le_antisymm (by omega) hle⟩
  obtain ⟨⟨D₀, H₀, hmem⟩, hglob⟩ := hts.1
  refine ⟨tstar, D₀, H₀, hmem, hglob, fun t D H ht hmin => hleast t ⟨⟨D, H, ht⟩, hmin⟩,
    fun D H hD hH => ⟨RR_mono hD hH hmem, ⟨⟨tstar, RR_mono hD hH hmem, rfl⟩,
      fun g' hg' => hglob g' (Set.mem_iUnion.2 ⟨D, Set.mem_iUnion.2 ⟨H, hg'⟩⟩)⟩,
      fun t' ht' hmin' => hleast t' ⟨⟨D, H, ht'⟩, fun g' hg' => ?_⟩⟩⟩
  -- a catalogue minimiser in a catalogue containing `tstar` is a global minimiser
  exact (hmin'.2 _ ⟨tstar, RR_mono hD hH hmem, rfl⟩).trans (hglob g' hg')

end Dyadic.Lib
