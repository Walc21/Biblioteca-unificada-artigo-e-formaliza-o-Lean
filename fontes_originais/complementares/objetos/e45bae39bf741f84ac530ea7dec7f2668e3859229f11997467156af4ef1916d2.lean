import Mathlib

/-!
# Dyadic cells: addressing and uniqueness (provisional)

`artigo_fase1.tex` only contains the preamble of the article; its mathematical content lives in
`secoes/02_indexacao.tex` and `secoes/03_biblioteca.tex`, which were not uploaded.  This file
formalizes only the standard basic notions suggested by the title ("rational affine segments on
dyadic cells: addressing and uniqueness").  It is a provisional formalization, not a
transcription of the article's own definitions.
-/

namespace DyadicCells

/-- The dyadic cell of level `n` and index `k`: the half-open interval `[k/2^n, (k+1)/2^n)`. -/
def cell (n : ℕ) (k : ℤ) : Set ℝ :=
  Set.Ico ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)

/-- The address of a real number at level `n`: the index `⌊2^n x⌋`. -/
noncomputable def address (n : ℕ) (x : ℝ) : ℤ := ⌊(2 : ℝ) ^ n * x⌋

lemma mem_cell_iff (n : ℕ) (k : ℤ) (x : ℝ) : x ∈ cell n k ↔ address n x = k := by
  have h : (0 : ℝ) < 2 ^ n := by positivity
  simp only [cell, address, Set.mem_Ico, Int.floor_eq_iff, div_le_iff₀ h, lt_div_iff₀ h]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Addressing: every real number lies in its addressed cell. -/
theorem mem_cell_address (n : ℕ) (x : ℝ) : x ∈ cell n (address n x) :=
  (mem_cell_iff n _ x).2 rfl

/-- Uniqueness of the address: at a fixed level, each real number lies in exactly one cell. -/
theorem existsUnique_cell (n : ℕ) (x : ℝ) : ∃! k : ℤ, x ∈ cell n k :=
  ⟨address n x, mem_cell_address n x, fun k hk => ((mem_cell_iff n k x).1 hk).symm⟩

/-- Cells of `[0,1)`: the address of `x ∈ [0,1)` at level `n` lies in `{0, …, 2^n - 1}`. -/
theorem address_mem_range (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    0 ≤ address n x ∧ address n x < 2 ^ n := by
  have h : (0 : ℝ) < 2 ^ n := by positivity
  obtain ⟨h0, h1⟩ := hx
  refine ⟨Int.floor_nonneg.2 (by positivity), ?_⟩
  rw [address, Int.floor_lt]
  push_cast
  nlinarith

/-- A rational affine segment `x ↦ a x + b` with `a b : ℚ`. -/
structure AffineSeg where
  a : ℚ
  b : ℚ

/-- Evaluation of a rational affine segment at a real point. -/
def AffineSeg.eval (s : AffineSeg) (x : ℝ) : ℝ := (s.a : ℝ) * x + s.b

/-- Uniqueness of the affine representation on a cell: two rational affine segments that agree
on a dyadic cell have the same coefficients. -/
theorem AffineSeg.eq_of_eqOn_cell (n : ℕ) (k : ℤ) (s t : AffineSeg)
    (h : Set.EqOn s.eval t.eval (cell n k)) : s = t := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  set x₀ : ℝ := (k : ℝ) / 2 ^ n
  set x₁ : ℝ := ((k : ℝ) + 1 / 2) / 2 ^ n
  have hx₀ : x₀ ∈ cell n k :=
    ⟨le_rfl, div_lt_div_of_pos_right (by linarith) hp⟩
  have hx₁ : x₁ ∈ cell n k :=
    ⟨div_le_div_of_nonneg_right (by linarith) hp.le, div_lt_div_of_pos_right (by linarith) hp⟩
  have hne : x₀ ≠ x₁ := by
    intro he
    have := (div_left_inj' hp.ne').1 he
    linarith
  have e₀ := h hx₀
  have e₁ := h hx₁
  simp only [AffineSeg.eval] at e₀ e₁
  have ha : (s.a : ℝ) = t.a := by
    have : ((s.a : ℝ) - t.a) * (x₀ - x₁) = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · exact absurd (sub_eq_zero.1 h') hne
  have hb : (s.b : ℝ) = t.b := by rw [ha] at e₀; linarith
  cases s; cases t
  simp only [AffineSeg.mk.injEq]
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

end DyadicCells
