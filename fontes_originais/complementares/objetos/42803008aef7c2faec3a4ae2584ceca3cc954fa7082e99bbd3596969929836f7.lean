module
public import RequestProject.Lib.Library
@[expose] public section

/-!
# Section 7.7: finite catalogues — non-attainment in the infinite library (Proposition 7.21)
-/

namespace Dyadic.Lib

lemma Atom.line_rat (a : Atom) (x : ℚ) : a.line x = ((a.y0 + a.s * (x - a.center) : ℚ) : ℝ) := by
  simp [Atom.line]

/-- **Proposition 7.21**: for `x = 1/4` and `y = √2`,
`inf {|y - ℓ_n(x)| : n ∈ ℕ, x ∈ I_n^x} = 0`, but no atom attains the infimum. -/
theorem sqrt_two_inf_not_attained :
    sInf {e : ℝ | ∃ n : ℕ, (1 / 4 : ℝ) ∈ (decode n).cell ∧
        e = |Real.sqrt 2 - (decode n).line (1 / 4)|} = 0 ∧
    ∀ n : ℕ, (1 / 4 : ℝ) ∈ (decode n).cell → |Real.sqrt 2 - (decode n).line (1 / 4)| ≠ 0 := by
  have hnot : ∀ a : Atom, |Real.sqrt 2 - a.line (1 / 4)| ≠ 0 := by
    intro a h
    have h' : Real.sqrt 2 = a.line ((1 / 4 : ℚ) : ℝ) := by
      push_cast; linarith [abs_eq_zero.1 h]
    rw [Atom.line_rat] at h'
    exact irrational_sqrt_two.ne_rat _ h'
  refine ⟨?_, fun n _ => hnot _⟩
  set S := {e : ℝ | ∃ n : ℕ, (1 / 4 : ℝ) ∈ (decode n).cell ∧
        e = |Real.sqrt 2 - (decode n).line (1 / 4)|}
  have hwit : ∀ q : ℚ, |Real.sqrt 2 - q| ∈ S := by
    intro q
    let a : Atom := ⟨2, 1, q + 1 / 8, 1, one_ne_zero⟩
    refine ⟨encode a, ?_, ?_⟩
    · rw [decode_encode]
      simp only [Atom.cell, Atom.left, Atom.right, a]
      norm_num
    · rw [decode_encode]
      simp only [Atom.line, Atom.center, a]
      norm_num
  have hlb : ∀ e ∈ S, 0 ≤ e := by
    rintro e ⟨n, -, rfl⟩; exact abs_nonneg _
  apply le_antisymm _ (le_csInf ⟨_, hwit 0⟩ hlb)
  by_contra hpos
  push_neg at hpos
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Real.sqrt 2 - sInf S / 2 < Real.sqrt 2 by linarith)
  have hmem := hwit q
  have : sInf S ≤ |Real.sqrt 2 - q| := csInf_le ⟨0, hlb⟩ hmem
  rw [abs_of_pos (by linarith)] at this
  linarith

end Dyadic.Lib
