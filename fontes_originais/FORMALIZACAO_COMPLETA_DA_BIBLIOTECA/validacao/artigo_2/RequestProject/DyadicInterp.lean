import RequestProject.Dyadic

/-!
# The tree interpolant `P_Λ f` and its uniform error (Section 11)

For a dyadic tree `Λ` rooted at `K = J_{k,m}`, the leaf interpolants `P_J f` agree at shared
nodes and define the interpolant `P_Λ f`; its uniform error on `K` is `max_{J ∈ Λ} e_f(J)`.
-/

namespace Artigo

open Set

namespace DShape

/-- the interpolant `P_Λ f` on the tree `T` rooted at `J_{k,m}` (a midpoint is evaluated in the
right child; both children give the same value there) -/
noncomputable def interp (f : ℝ → ℝ) : DShape → ℕ → ℤ → ℝ → ℝ
  | leaf, k, m, x => linInterp f (cL k m) (cR k m) x
  | node l r, k, m, x => if x < cL (k + 1) (2 * m + 1) then interp f l (k + 1) (2 * m) x
      else interp f r (k + 1) (2 * m + 1) x

lemma interp_left (f : ℝ → ℝ) : ∀ (T : DShape) (k : ℕ) (m : ℤ),
    T.interp f k m (cL k m) = f (cL k m)
  | leaf, k, m => linInterp_left f
  | node l _, k, m => by
      have : cL k m < cL (k + 1) (2 * m + 1) := by
        rw [← cR_child_left, ← cL_child_left]; exact cL_lt_cR _ _
      simp only [interp, if_pos this]
      rw [← cL_child_left]; exact interp_left f l _ _

lemma interp_right (f : ℝ → ℝ) : ∀ (T : DShape) (k : ℕ) (m : ℤ),
    T.interp f k m (cR k m) = f (cR k m)
  | leaf, k, m => linInterp_right f (cL_lt_cR k m)
  | node _ r, k, m => by
      have : ¬ cR k m < cL (k + 1) (2 * m + 1) := by
        rw [← cR_child_right]; exact not_lt.mpr (cL_lt_cR _ _).le
      simp only [interp, if_neg this]
      rw [← cR_child_right]; exact interp_right f r _ _

lemma isLUB_treeErr {f : ℝ → ℝ} : ∀ (T : DShape) (k : ℕ) (m : ℤ),
    ContinuousOn f (cellIcc k m) →
    IsLUB ((fun x => |f x - T.interp f k m x|) '' cellIcc k m) (T.treeErr f k m)
  | leaf, k, m, hf =>
      isLUB_csSup ((nonempty_Icc.mpr (cL_lt_cR k m).le).image _) (locErr_bdd hf)
  | node l r, k, m, hf => by
      have hl := isLUB_treeErr l (k + 1) (2 * m) (hf.mono (cell_child_left_sub k m))
      have hr := isLUB_treeErr r (k + 1) (2 * m + 1) (hf.mono (cell_child_right_sub k m))
      have hK : cellIcc k m = cellIcc (k + 1) (2 * m) ∪ cellIcc (k + 1) (2 * m + 1) := by
        rw [cellIcc_eq, cellIcc_eq, cellIcc_eq, cL_child_left, cR_child_right, cR_child_left]
        exact (Icc_union_Icc_eq_Icc
          (by rw [← cR_child_left, ← cL_child_left]; exact (cL_lt_cR _ _).le)
          (by rw [← cR_child_right]; exact (cL_lt_cR _ _).le)).symm
      have hEqL : EqOn (fun x => |f x - (node l r).interp f k m x|)
          (fun x => |f x - l.interp f (k + 1) (2 * m) x|) (cellIcc (k + 1) (2 * m)) := by
        intro x hx
        rw [cellIcc_eq, cR_child_left] at hx
        simp only [interp]
        split_ifs with h
        · rfl
        · have hxe : x = cL (k + 1) (2 * m + 1) := le_antisymm hx.2 (not_lt.mp h)
          rw [hxe, interp_left, ← cR_child_left, interp_right]
      have hEqR : EqOn (fun x => |f x - (node l r).interp f k m x|)
          (fun x => |f x - r.interp f (k + 1) (2 * m + 1) x|) (cellIcc (k + 1) (2 * m + 1)) := by
        intro x hx
        rw [cellIcc_eq] at hx
        simp only [interp, if_neg (not_lt.mpr hx.1)]
      rw [hK, image_union, hEqL.image_eq, hEqR.image_eq]
      exact hl.union hr

/-- the uniform error of the tree interpolant is the largest local error:
`‖f - P_Λ f‖_{∞,K} = max_{J ∈ Λ} e_f(J)` -/
theorem treeErr_eq_sSup {f : ℝ → ℝ} {k : ℕ} {m : ℤ} (hf : ContinuousOn f (cellIcc k m))
    (T : DShape) :
    T.treeErr f k m = sSup ((fun x => |f x - T.interp f k m x|) '' cellIcc k m) :=
  ((isLUB_treeErr T k m hf).csSup_eq ((nonempty_Icc.mpr (cL_lt_cR k m).le).image _)).symm

end DShape

end Artigo
