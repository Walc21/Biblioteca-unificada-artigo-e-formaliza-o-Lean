import RequestProject.Trees

/-!
# Section 11 — Optimal interpolation error on strictly dyadic trees

* `locErr f k m` is the local interpolation error `e_f(J) = ‖f - P_J f‖_{∞,J}` on the dyadic cell
  `J = J_{k,m}`;
* `DShape` are the (unlabelled) finite dyadic trees, `DShape.treeErr` is
  `max_{J ∈ Λ} e_f(J)`, and `Edia f k m N` is `E_N^{dia}(f)_∞` (root `K = J_{k,m}`);
* `IsThr f ε k m T` characterises the threshold tree `T_ε(f)`, `thrTree` is the tree itself and
  `nThr f ε k m = n_f(ε)` its number of leaves;
* Theorem 11.1 (minimalidade exata do limiar) and Lemma 11.2 (expansão local uniforme).
-/

namespace Artigo

open Set

/-! ## Cells -/

lemma cell_len (k : ℕ) (m : ℤ) : cR k m - cL k m = ((2 : ℝ) ^ k)⁻¹ := by
  unfold cR cL; field_simp; ring

lemma cell_child_left_sub (k : ℕ) (m : ℤ) : cellIcc (k + 1) (2 * m) ⊆ cellIcc k m := by
  rw [cellIcc_eq, cellIcc_eq, cL_child_left, cR_child_left]
  exact Icc_subset_Icc le_rfl (le_trans (le_of_lt (cL_lt_cR _ _)) (by rw [cR_child_right]))

lemma cell_child_right_sub (k : ℕ) (m : ℤ) : cellIcc (k + 1) (2 * m + 1) ⊆ cellIcc k m := by
  rw [cellIcc_eq, cellIcc_eq, cR_child_right, ← cR_child_left]
  exact Icc_subset_Icc (by rw [← cL_child_left]; exact (cL_lt_cR _ _).le) le_rfl

/-! ## The local interpolation error -/

/-- the local interpolation error `e_f(J) = ‖f - P_J f‖_{∞,J}` on `J = J_{k,m}` -/
noncomputable def locErr (f : ℝ → ℝ) (k : ℕ) (m : ℤ) : ℝ :=
  sSup ((fun x => |f x - linInterp f (cL k m) (cR k m) x|) '' cellIcc k m)

section locErr

variable {f : ℝ → ℝ} {k : ℕ} {m : ℤ}

lemma locErr_nonneg : 0 ≤ locErr f k m :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact abs_nonneg _)

lemma interpErr_continuousOn {S : Set ℝ} (hf : ContinuousOn f S) (a b : ℝ) :
    ContinuousOn (fun x => |f x - linInterp f a b x|) S := by
  unfold linInterp
  exact (hf.sub (continuousOn_const.add (continuousOn_const.mul
    (continuousOn_id.sub continuousOn_const)))).abs

lemma locErr_bdd (hf : ContinuousOn f (cellIcc k m)) :
    BddAbove ((fun x => |f x - linInterp f (cL k m) (cR k m) x|) '' cellIcc k m) :=
  isCompact_Icc.bddAbove_image (interpErr_continuousOn hf _ _)

lemma le_locErr (hf : ContinuousOn f (cellIcc k m)) {x : ℝ} (hx : x ∈ cellIcc k m) :
    |f x - linInterp f (cL k m) (cR k m) x| ≤ locErr f k m :=
  le_csSup (locErr_bdd hf) (mem_image_of_mem _ hx)

lemma locErr_le_iff (hf : ContinuousOn f (cellIcc k m)) {B : ℝ} :
    locErr f k m ≤ B ↔ ∀ x ∈ cellIcc k m, |f x - linInterp f (cL k m) (cR k m) x| ≤ B := by
  unfold locErr
  rw [csSup_le_iff (locErr_bdd hf) ((nonempty_Icc.mpr (cL_lt_cR k m).le).image _)]
  simp

/-- the local error is attained -/
lemma exists_locErr_eq (hf : ContinuousOn f (cellIcc k m)) :
    ∃ x ∈ cellIcc k m, |f x - linInterp f (cL k m) (cR k m) x| = locErr f k m := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (cL_lt_cR k m).le)
    (interpErr_continuousOn hf (cL k m) (cR k m))
  refine ⟨x, hx, le_antisymm (le_locErr hf hx) ?_⟩
  exact (locErr_le_iff hf).mpr fun y hy => hmax hy

end locErr

/-- convex-combination form of the interpolation error -/
lemma sub_linInterp_eq (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (x : ℝ) :
    f x - linInterp f a b x =
      (1 - (x - a) / (b - a)) * (f x - f a) + (x - a) / (b - a) * (f x - f b) := by
  unfold linInterp
  have : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  field_simp
  ring

/-- `e_f(J) ≤ ω_f(|J|)`: if `f` oscillates by at most `η` on `J`, then `e_f(J) ≤ η`. -/
lemma locErr_le_of_osc {f : ℝ → ℝ} {k : ℕ} {m : ℤ} (hf : ContinuousOn f (cellIcc k m)) {η : ℝ}
    (hosc : ∀ x ∈ cellIcc k m, ∀ y ∈ cellIcc k m, |f x - f y| ≤ η) : locErr f k m ≤ η := by
  rw [locErr_le_iff hf]
  intro x hx
  have hab := cL_lt_cR k m
  rw [sub_linInterp_eq f hab]
  have hx' := hx
  rw [cellIcc_eq] at hx'
  have h0 : 0 ≤ (x - cL k m) / (cR k m - cL k m) := div_nonneg (by linarith [hx'.1]) (by linarith)
  have h1 : (x - cL k m) / (cR k m - cL k m) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith [hx'.2]
  have ha : cL k m ∈ cellIcc k m := by rw [cellIcc_eq]; exact left_mem_Icc.mpr hab.le
  have hb : cR k m ∈ cellIcc k m := by rw [cellIcc_eq]; exact right_mem_Icc.mpr hab.le
  calc _ ≤ |(1 - (x - cL k m) / (cR k m - cL k m)) * (f x - f (cL k m))| +
        |(x - cL k m) / (cR k m - cL k m) * (f x - f (cR k m))| := abs_add_le _ _
    _ = (1 - (x - cL k m) / (cR k m - cL k m)) * |f x - f (cL k m)| +
        (x - cL k m) / (cR k m - cL k m) * |f x - f (cR k m)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg h0]
    _ ≤ (1 - (x - cL k m) / (cR k m - cL k m)) * η + (x - cL k m) / (cR k m - cL k m) * η := by
          gcongr
          · linarith
          · exact hosc x hx _ ha
          · exact hosc x hx _ hb
    _ = η := by ring

/-! ## Dyadic trees -/

/-- finite (ordered, full) dyadic trees, unlabelled -/
inductive DShape
  | leaf
  | node (l r : DShape)
deriving DecidableEq

namespace DShape

/-- number of leaves `|Λ|` -/
def numLeaves : DShape → ℕ
  | leaf => 1
  | node l r => l.numLeaves + r.numLeaves

/-- depth -/
def depth : DShape → ℕ
  | leaf => 0
  | node l r => max l.depth r.depth + 1

/-- `max_{J ∈ Λ} e_f(J)`, the uniform error `‖f - P_Λ f‖_{∞,K}` of the interpolant on the tree
rooted at `K = J_{k,m}` -/
noncomputable def treeErr (f : ℝ → ℝ) : DShape → ℕ → ℤ → ℝ
  | leaf, k, m => locErr f k m
  | node l r, k, m => max (treeErr f l (k + 1) (2 * m)) (treeErr f r (k + 1) (2 * m + 1))

/-- `T'.Refines T`: every leaf of `T` is subdivided (or kept) in `T'` -/
def Refines : DShape → DShape → Prop
  | _, leaf => True
  | leaf, node _ _ => False
  | node l' r', node l r => Refines l' l ∧ Refines r' r

/-- the complete dyadic tree of depth `r` -/
def uniform : ℕ → DShape
  | 0 => leaf
  | r + 1 => node (uniform r) (uniform r)

lemma numLeaves_pos (T : DShape) : 0 < T.numLeaves := by
  induction T with
  | leaf => simp [numLeaves]
  | node l r ihl _ => simp only [numLeaves]; omega

lemma depth_lt_numLeaves (T : DShape) : T.depth < T.numLeaves := by
  induction T with
  | leaf => simp [numLeaves, depth]
  | node l r ihl ihr =>
    simp only [numLeaves, depth]
    have := l.numLeaves_pos; have := r.numLeaves_pos
    rcases le_total l.depth r.depth with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega

lemma numLeaves_uniform (r : ℕ) : (uniform r).numLeaves = 2 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [uniform, numLeaves, ih]; ring

lemma treeErr_nonneg (f : ℝ → ℝ) : ∀ (T : DShape) (k : ℕ) (m : ℤ), 0 ≤ T.treeErr f k m
  | leaf, _, _ => locErr_nonneg
  | node l _, k, m => le_max_of_le_left (treeErr_nonneg f l (k + 1) (2 * m))

lemma refines_refl : ∀ T : DShape, T.Refines T
  | leaf => trivial
  | node l r => ⟨refines_refl l, refines_refl r⟩

lemma Refines.numLeaves_le : ∀ {T' T : DShape}, T'.Refines T → T.numLeaves ≤ T'.numLeaves
  | T', leaf, _ => by simpa [numLeaves] using T'.numLeaves_pos
  | leaf, node _ _, h => h.elim
  | node _ _, node _ _, h => by
      simp only [numLeaves]; exact Nat.add_le_add h.1.numLeaves_le h.2.numLeaves_le

lemma Refines.antisymm : ∀ {T' T : DShape}, T'.Refines T → T.Refines T' → T' = T
  | leaf, leaf, _, _ => rfl
  | node _ _, leaf, _, h => h.elim
  | leaf, node _ _, h, _ => h.elim
  | node _ _, node _ _, h1, h2 => by rw [h1.1.antisymm h2.1, h1.2.antisymm h2.2]

/-- all trees of depth `≤ D` -/
def allOfDepth : ℕ → Finset DShape
  | 0 => {leaf}
  | D + 1 => insert leaf (((allOfDepth D) ×ˢ (allOfDepth D)).image fun p => node p.1 p.2)

lemma mem_allOfDepth : ∀ (D : ℕ) (T : DShape), T ∈ allOfDepth D ↔ T.depth ≤ D := by
  intro D
  induction D with
  | zero => intro T; cases T <;> simp [allOfDepth, depth]
  | succ D ih =>
    intro T
    cases T with
    | leaf => simp [allOfDepth, depth]
    | node l r =>
      simp only [allOfDepth, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_image,
        Finset.mem_product, Prod.exists, node.injEq, depth]
      constructor
      · rintro ⟨l', r', ⟨hl, hr⟩, rfl, rfl⟩
        rw [ih] at hl hr; omega
      · intro h
        exact ⟨l, r, ⟨(ih l).mpr (by omega), (ih r).mpr (by omega)⟩, rfl, rfl⟩

end DShape

open DShape

/-- `E_N^{dia}(f)_∞`: the least uniform interpolation error over dyadic trees rooted at
`K = J_{k,m}` with at most `N` leaves -/
noncomputable def Edia (f : ℝ → ℝ) (k : ℕ) (m : ℤ) (N : ℕ) : ℝ :=
  sInf {e | ∃ T : DShape, T.numLeaves ≤ N ∧ T.treeErr f k m = e}

section Edia

variable {f : ℝ → ℝ} {k : ℕ} {m : ℤ}

lemma Edia_set_finite (N : ℕ) :
    {e | ∃ T : DShape, T.numLeaves ≤ N ∧ T.treeErr f k m = e}.Finite := by
  refine ((allOfDepth N).image (fun T => T.treeErr f k m)).finite_toSet.subset ?_
  rintro _ ⟨T, hT, rfl⟩
  simp only [Finset.coe_image, mem_image, Finset.mem_coe]
  exact ⟨T, (mem_allOfDepth _ _).mpr (by have := T.depth_lt_numLeaves; omega), rfl⟩

/-- the minimum defining `E_N^{dia}` exists -/
lemma exists_Edia_eq {N : ℕ} (hN : 1 ≤ N) :
    ∃ T : DShape, T.numLeaves ≤ N ∧ T.treeErr f k m = Edia f k m N :=
  Set.Nonempty.csInf_mem (s := {e | ∃ T : DShape, T.numLeaves ≤ N ∧ T.treeErr f k m = e})
    ⟨_, leaf, by simpa [numLeaves] using hN, rfl⟩ (Edia_set_finite N)

lemma Edia_le_treeErr {N : ℕ} {T : DShape} (hT : T.numLeaves ≤ N) :
    Edia f k m N ≤ T.treeErr f k m :=
  csInf_le ⟨0, by rintro _ ⟨T, -, rfl⟩; exact T.treeErr_nonneg f k m⟩ ⟨T, hT, rfl⟩

lemma Edia_nonneg (N : ℕ) : 0 ≤ Edia f k m N :=
  Real.sInf_nonneg (by rintro _ ⟨T, -, rfl⟩; exact T.treeErr_nonneg f k m)

end Edia

/-! ## The threshold tree -/

/-- `IsThr f ε k m T`: `T` is the threshold tree `T_ε(f)` rooted at `J_{k,m}`: a cell is kept
as a leaf when `e_f(J) ≤ ε`, and replaced by its two children when `e_f(J) > ε`. -/
inductive IsThr (f : ℝ → ℝ) (ε : ℝ) : ℕ → ℤ → DShape → Prop
  | leaf {k : ℕ} {m : ℤ} : locErr f k m ≤ ε → IsThr f ε k m DShape.leaf
  | node {k : ℕ} {m : ℤ} {l r : DShape} : ε < locErr f k m → IsThr f ε (k + 1) (2 * m) l →
      IsThr f ε (k + 1) (2 * m + 1) r → IsThr f ε k m (DShape.node l r)

open Classical in
/-- the threshold tree `T_ε(f)` (a leaf, by convention, if the recursion does not terminate) -/
noncomputable def thrTree (f : ℝ → ℝ) (ε : ℝ) (k : ℕ) (m : ℤ) : DShape :=
  if h : ∃ T, IsThr f ε k m T then h.choose else DShape.leaf

/-- `n_f(ε) = |Λ(T_ε(f))|` -/
noncomputable def nThr (f : ℝ → ℝ) (ε : ℝ) (k : ℕ) (m : ℤ) : ℕ := (thrTree f ε k m).numLeaves

section Thr

variable {f : ℝ → ℝ} {ε : ℝ}

lemma IsThr.unique {k : ℕ} {m : ℤ} {T T' : DShape} (h : IsThr f ε k m T)
    (h' : IsThr f ε k m T') : T = T' := by
  induction h generalizing T' with
  | leaf hle =>
    cases h' with
    | leaf _ => rfl
    | node hlt _ _ => exact absurd hle (not_le.mpr hlt)
  | node hlt _ _ ihl ihr =>
    cases h' with
    | leaf hle => exact absurd hle (not_le.mpr hlt)
    | node _ hl hr => rw [ihl hl, ihr hr]

lemma IsThr.treeErr_le {k : ℕ} {m : ℤ} {T : DShape} (h : IsThr f ε k m T) :
    T.treeErr f k m ≤ ε := by
  induction h with
  | leaf hle => exact hle
  | node _ _ _ ihl ihr => exact max_le ihl ihr

lemma IsThr.refines {k : ℕ} {m : ℤ} {T : DShape} (h : IsThr f ε k m T) :
    ∀ T' : DShape, T'.treeErr f k m ≤ ε → T'.Refines T := by
  induction h with
  | leaf _ => intro T' _; cases T' <;> trivial
  | node hlt _ _ ihl ihr =>
    intro T' hT'
    cases T' with
    | leaf => simp only [treeErr] at hT'; linarith
    | node l' r' => exact ⟨ihl l' (le_of_max_le_left hT'), ihr r' (le_of_max_le_right hT')⟩

lemma thrTree_spec {k : ℕ} {m : ℤ} (h : ∃ T, IsThr f ε k m T) : IsThr f ε k m (thrTree f ε k m) := by
  unfold thrTree; rw [dif_pos h]; exact h.choose_spec

/-- termination of the threshold recursion for continuous `f` -/
lemma exists_isThr {k₀ : ℕ} {m₀ : ℤ} (hf : ContinuousOn f (cellIcc k₀ m₀)) (hε : 0 < ε) :
    ∃ T, IsThr f ε k₀ m₀ T := by
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨kδ, hkδ⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  have hsmall : ∀ (k : ℕ) (m : ℤ), cellIcc k m ⊆ cellIcc k₀ m₀ → kδ ≤ k → locErr f k m ≤ ε := by
    intro k m hsub hk
    apply locErr_le_of_osc (hf.mono hsub)
    intro x hx y hy
    have hlen : |x - y| < δ := by
      rw [cellIcc_eq] at hx hy
      have h1 : cR k m - cL k m < δ := by
        rw [cell_len]
        calc ((2 : ℝ) ^ k)⁻¹ = (1 / 2) ^ k := by rw [one_div, inv_pow]
          _ ≤ (1 / 2) ^ kδ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
          _ < δ := hkδ
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    exact (hU x (hsub hx) y (hsub hy) (by rw [Real.dist_eq]; exact hlen)).le.trans_eq'
      (Real.dist_eq _ _).symm
  have key : ∀ (n k : ℕ) (m : ℤ), cellIcc k m ⊆ cellIcc k₀ m₀ → kδ ≤ k + n →
      ∃ T, IsThr f ε k m T := by
    intro n
    induction n with
    | zero => intro k m hsub hk; exact ⟨_, IsThr.leaf (hsmall k m hsub (by omega))⟩
    | succ n ih =>
      intro k m hsub hk
      by_cases hle : locErr f k m ≤ ε
      · exact ⟨_, IsThr.leaf hle⟩
      · obtain ⟨l, hl⟩ := ih (k + 1) (2 * m) ((cell_child_left_sub k m).trans hsub) (by omega)
        obtain ⟨r, hr⟩ := ih (k + 1) (2 * m + 1) ((cell_child_right_sub k m).trans hsub)
          (by omega)
        exact ⟨_, IsThr.node (not_le.mp hle) hl hr⟩
  exact key kδ k₀ m₀ subset_rfl (by omega)

end Thr

/-- **Theorem 11.1 (minimalidade exata do limiar)**: for `f ∈ C(K)` and `ε > 0`, the threshold
recursion terminates in a unique finite tree `T_ε(f)`; it is feasible, every feasible tree refines
it (so it is the unique coarsest feasible tree), it has the fewest leaves among feasible trees, and
`E_N^{dia}(f)_∞ ≤ ε ⟺ n_f(ε) ≤ N` (for every budget `N ≥ 1`). -/
theorem threshold_optimality {f : ℝ → ℝ} {k : ℕ} {m : ℤ} (hf : ContinuousOn f (cellIcc k m))
    {ε : ℝ} (hε : 0 < ε) :
    (∃! T, IsThr f ε k m T) ∧
    (thrTree f ε k m).treeErr f k m ≤ ε ∧
    (∀ T : DShape, T.treeErr f k m ≤ ε → T.Refines (thrTree f ε k m)) ∧
    (∀ T : DShape, T.treeErr f k m ≤ ε →
      (∀ T' : DShape, T'.treeErr f k m ≤ ε → T'.Refines T) → T = thrTree f ε k m) ∧
    (∀ T : DShape, T.treeErr f k m ≤ ε → nThr f ε k m ≤ T.numLeaves) ∧
    (∀ N : ℕ, 1 ≤ N → (Edia f k m N ≤ ε ↔ nThr f ε k m ≤ N)) := by
  have hex := exists_isThr hf hε
  have hT := thrTree_spec hex
  have href := hT.refines
  refine ⟨⟨_, hT, fun T h => h.unique hT⟩, hT.treeErr_le, href, ?_, ?_, ?_⟩
  · intro T hTf hcoarse
    exact (hcoarse _ hT.treeErr_le).antisymm (href T hTf) |>.symm
  · intro T hTf
    exact (href T hTf).numLeaves_le
  · intro N hN
    constructor
    · intro hE
      obtain ⟨T, hTN, hTe⟩ := exists_Edia_eq (f := f) (k := k) (m := m) hN
      exact ((href T (hTe ▸ hE)).numLeaves_le).trans hTN
    · intro hn
      exact (Edia_le_treeErr hn).trans hT.treeErr_le

/-- **Theorem 11.1 (inversion)**: `E_N^{dia}(f)_∞ = inf {ε > 0 : n_f(ε) ≤ N}` for `N ≥ 1`. -/
theorem Edia_eq_sInf_nThr {f : ℝ → ℝ} {k : ℕ} {m : ℤ} (hf : ContinuousOn f (cellIcc k m))
    {N : ℕ} (hN : 1 ≤ N) :
    Edia f k m N = sInf {ε : ℝ | 0 < ε ∧ nThr f ε k m ≤ N} := by
  have hset : {ε : ℝ | 0 < ε ∧ nThr f ε k m ≤ N} = {ε : ℝ | 0 < ε ∧ Edia f k m N ≤ ε} := by
    ext ε
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hε, h⟩; exact ⟨hε, ((threshold_optimality hf hε).2.2.2.2.2 N hN).mpr h⟩
    · rintro ⟨hε, h⟩; exact ⟨hε, ((threshold_optimality hf hε).2.2.2.2.2 N hN).mp h⟩
  rw [hset]
  rcases (Edia_nonneg (f := f) (k := k) (m := m) N).eq_or_lt with h0 | hpos
  · have : {ε : ℝ | 0 < ε ∧ Edia f k m N ≤ ε} = Ioi 0 := by
      ext ε; simp only [mem_setOf_eq, mem_Ioi, ← h0]; constructor
      · exact fun h => h.1
      · exact fun h => ⟨h, h.le⟩
    rw [this, csInf_Ioi, ← h0]
  · have : {ε : ℝ | 0 < ε ∧ Edia f k m N ≤ ε} = Ici (Edia f k m N) := by
      ext ε; simp only [mem_setOf_eq, mem_Ici]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨hpos.trans_le h, h⟩
    rw [this, csInf_Ici]

/-! ## Local estimates for `C²` functions and Lemma 11.2 -/

lemma C2_hasDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (∀ x, HasDerivAt f (deriv f x) x) ∧ ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x := by
  have h1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h2 : Differentiable ℝ (deriv f) := by
    have : ContDiff ℝ 1 (deriv f) := hf.iterate_deriv' 1 1
    exact this.differentiable (by norm_num)
  exact ⟨fun x => (h1 x).hasDerivAt, fun x => (h2 x).hasDerivAt⟩

lemma C2_continuous_deriv2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (deriv (deriv f)) := by
  have := hf.iterate_deriv' 0 2
  simpa [Function.iterate_succ] using this.continuous

/-- **two-sided local estimate**: if `|f'' - c| ≤ w` on `J`, then
`|e_f(J) - |c| |J|²/8| ≤ w |J|²/8`. -/
lemma locErr_near {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k : ℕ} {m : ℤ} {c w : ℝ}
    (h : ∀ y ∈ cellIcc k m, |deriv (deriv f) y - c| ≤ w) :
    |locErr f k m - |c| / 8 * (cR k m - cL k m) ^ 2| ≤ w / 8 * (cR k m - cL k m) ^ 2 := by
  have hab := cL_lt_cR k m
  obtain ⟨hd, hd2⟩ := C2_hasDeriv hf
  have hcont : ContinuousOn f (cellIcc k m) := hf.continuous.continuousOn
  have two := interp_two_sided hab hd hd2 (c₁ := c - w) (c₂ := c + w)
    (fun y hy => by have := abs_le.mp (h y hy); linarith)
    (fun y hy => by have := abs_le.mp (h y hy); linarith)
  have hw : 0 ≤ w := le_trans (abs_nonneg _)
    (h _ (by rw [cellIcc_eq]; exact left_mem_Icc.mpr hab.le))
  set a := cL k m
  set b := cR k m
  have hup : locErr f k m ≤ (|c| + w) / 8 * (b - a) ^ 2 := by
    rw [locErr_le_iff hcont]
    intro y hy
    have hy' : y ∈ Icc a b := hy
    obtain ⟨p0, p1⟩ := prod_bound hy'
    obtain ⟨t1, t2⟩ := two y hy'
    have e : (y - a) * (y - b) = -((y - a) * (b - y)) := by ring
    rw [e] at t1 t2
    rw [abs_le]
    constructor <;> nlinarith [abs_nonneg c, le_abs_self c, neg_abs_le c]
  have hmid : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hlo : (|c| - w) / 8 * (b - a) ^ 2 ≤ locErr f k m := by
    refine le_trans ?_ (le_locErr hcont hmid)
    obtain ⟨t1, t2⟩ := two _ hmid
    have e : ((a + b) / 2 - a) * ((a + b) / 2 - b) = -((b - a) ^ 2 / 4) := by ring
    rw [e] at t1 t2
    rcases le_total 0 c with hc | hc
    · rw [abs_of_nonneg hc]
      refine le_trans ?_ (neg_le_abs _)
      nlinarith
    · rw [abs_of_nonpos hc]
      refine le_trans ?_ (le_abs_self _)
      nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- the modulus of continuity `ω_g(t) = sup_{x,y ∈ S, |x-y| ≤ t} |g x - g y|` on `S` -/
noncomputable def modCont (g : ℝ → ℝ) (S : Set ℝ) (t : ℝ) : ℝ :=
  sSup {d | ∃ x ∈ S, ∃ y ∈ S, |x - y| ≤ t ∧ d = |g x - g y|}

lemma le_modCont {g : ℝ → ℝ} {S : Set ℝ} (hS : IsCompact S) (hg : ContinuousOn g S) {t : ℝ}
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : |x - y| ≤ t) : |g x - g y| ≤ modCont g S t := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hg
  refine le_csSup ⟨2 * B, ?_⟩ ⟨x, hx, y, hy, hxy, rfl⟩
  rintro _ ⟨x', hx', y', hy', -, rfl⟩
  have h1 := hB x' hx'; have h2 := hB y' hy'
  rw [Real.norm_eq_abs] at h1 h2
  linarith [abs_sub (g x') (g y')]

/-- **Lemma 11.2 (expansão local uniforme)**: for `f ∈ C²(K)`, every dyadic cell `J ⊆ K` and
every `x ∈ J`, `|e_f(J) - |f''(x)| |J|²/8| ≤ ω_{f''}(|J|) |J|²/8`. -/
theorem local_asymptotic_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {k₀ : ℕ} {m₀ : ℤ} {k : ℕ}
    {m : ℤ} (hJ : cellIcc k m ⊆ cellIcc k₀ m₀) {x : ℝ} (hx : x ∈ cellIcc k m) :
    |locErr f k m - |deriv (deriv f) x| / 8 * (cR k m - cL k m) ^ 2| ≤
      modCont (deriv (deriv f)) (cellIcc k₀ m₀) (cR k m - cL k m) / 8 * (cR k m - cL k m) ^ 2 := by
  apply locErr_near hf
  intro y hy
  have hx' := hx; have hy' := hy
  rw [cellIcc_eq] at hx' hy'
  exact le_modCont isCompact_Icc (C2_continuous_deriv2 hf).continuousOn (hJ hy) (hJ hx)
    (by rw [abs_le]; constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2])

end Artigo
