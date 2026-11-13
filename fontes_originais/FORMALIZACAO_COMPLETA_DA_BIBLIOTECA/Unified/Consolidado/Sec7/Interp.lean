module
public import Unified.Consolidado.Sec7.Chain
public import Unified.Consolidado.Sec7.JointError
@[expose] public section

/-!
# Dyadic interpolants with rational nodal values

For `n = 2^r` and rational nodal values `v 0, v 1, …` with `v (j+1) ≠ v j`, the leaf on
`J_{r,j} = [j/n, (j+1)/n]` through `(j/n, v j)` and `((j+1)/n, v (j+1))` is an atom; the leaves
`j < n` form an assembly on `[0,1]` with exactly `n` leaves.  We also record the deterministic
nearest-point rule on the alternating grids (ties broken towards the smaller point) and the
interpolation error estimate.
-/

open Set Finset

namespace Dyadic.Lib

/-! ### Nearest point of an alternating grid -/

/-- The integer `b ≡ p (mod 2)` nearest to the real `y`, ties broken towards the smaller one:
`b = 2 ⌈(y - p)/2 - 1/2⌉ + p`. -/
noncomputable def gridNum (y : ℝ) (p : ℕ) : ℤ := 2 * ⌈(y - p) / 2 - 1 / 2⌉ + p

lemma gridNum_mod (y : ℝ) (p : ℕ) : gridNum y p ≡ p [ZMOD 2] := by
  unfold gridNum
  exact (Int.modEq_iff_dvd.2 ⟨-⌈(y - p) / 2 - 1 / 2⌉, by ring⟩)

lemma gridNum_sub_le (y : ℝ) (p : ℕ) : |(gridNum y p : ℝ) - y| ≤ 1 := by
  unfold gridNum
  have h1 := Int.le_ceil ((y - p) / 2 - 1 / 2)
  have h2 := Int.ceil_lt_add_one ((y - p) / 2 - 1 / 2)
  push_cast
  rw [abs_le]; constructor <;> linarith

/-- Optimality and tie-breaking of `gridNum`: among the integers `b ≡ p (mod 2)` it minimises
`|b - y|`, and in case of a tie it is the smaller one. -/
lemma gridNum_optimal (y : ℝ) (p : ℕ) (b : ℤ) (hb : b ≡ p [ZMOD 2]) :
    |(gridNum y p : ℝ) - y| ≤ |(b : ℝ) - y| ∧
      (|(gridNum y p : ℝ) - y| = |(b : ℝ) - y| → gridNum y p ≤ b) := by
  obtain ⟨w, hw⟩ : ∃ w : ℤ, b = 2 * w + p := by
    have := Int.ModEq.dvd hb.symm
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by linarith⟩
  subst hw
  set z := ⌈(y - p) / 2 - 1 / 2⌉ with hz
  have h1 := Int.le_ceil ((y - p) / 2 - 1 / 2)
  have h2 := Int.ceil_lt_add_one ((y - p) / 2 - 1 / 2)
  rw [← hz] at h1 h2
  unfold gridNum
  rw [← hz]
  push_cast
  rcases lt_trichotomy w z with h | h | h
  · have hw : (w : ℝ) ≤ z - 1 := by exact_mod_cast (show w ≤ z - 1 by omega)
    have e1 : |2 * (z : ℝ) + p - y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have e2 : 1 < |2 * (w : ℝ) + p - y| := by
      rw [abs_of_neg (by linarith)]; linarith
    exact ⟨by linarith, fun h' => by linarith⟩
  · subst h; exact ⟨le_rfl, fun _ => le_rfl⟩
  · have hw : (z : ℝ) + 1 ≤ w := by exact_mod_cast (show z + 1 ≤ w by omega)
    refine ⟨?_, fun _ => by omega⟩
    have e2 : |2 * (w : ℝ) + p - y| = 2 * w + p - y := abs_of_nonneg (by linarith)
    rw [e2, abs_le]; constructor <;> linarith

/-! ### Interpolating atoms -/

lemma interp_slope_ne (r : ℕ) {v : ℕ → ℚ} (hv : ∀ j, v (j + 1) ≠ v j) (j : ℕ) :
    (v (j + 1) - v j) * 2 ^ r ≠ 0 :=
  mul_ne_zero (sub_ne_zero.2 (hv j)) (by positivity)

/-- The leaf on `J_{r,j}` interpolating `(j/2^r, v j)` and `((j+1)/2^r, v (j+1))`: central value
`(v j + v (j+1))/2` and slope `(v (j+1) - v j) 2^r`. -/
def interpAtom (r : ℕ) (v : ℕ → ℚ) (hv : ∀ j, v (j + 1) ≠ v j) (j : ℕ) : Atom :=
  ⟨r, j, (v j + v (j + 1)) / 2, (v (j + 1) - v j) * 2 ^ r, interp_slope_ne r hv j⟩

section

variable {r : ℕ} {v : ℕ → ℚ} {hv : ∀ j, v (j + 1) ≠ v j}

lemma interpAtom_left (j : ℕ) : ((interpAtom r v hv j).left : ℝ) = j / 2 ^ r := by
  simp [interpAtom, Atom.left]

lemma interpAtom_right (j : ℕ) : ((interpAtom r v hv j).right : ℝ) = (j + 1) / 2 ^ r := by
  simp [interpAtom, Atom.right]

lemma interpAtom_line (j : ℕ) (x : ℝ) :
    (interpAtom r v hv j).line x = v j + ((v (j + 1) : ℝ) - v j) * 2 ^ r * (x - j / 2 ^ r) := by
  simp only [interpAtom, Atom.line, Atom.center]
  push_cast
  field_simp
  ring

lemma interpAtom_cons (j : ℕ) : (interpAtom r v hv j).right = (interpAtom r v hv (j + 1)).left := by
  simp [interpAtom, Atom.right, Atom.left]

lemma interpAtom_match (j : ℕ) :
    (interpAtom r v hv j).line (interpAtom r v hv j).right =
      (interpAtom r v hv (j + 1)).line (interpAtom r v hv (j + 1)).left := by
  rw [interpAtom_right, interpAtom_left, interpAtom_line, interpAtom_line]
  push_cast
  field_simp
  ring

lemma interp_domain :
    Set.Icc ((interpAtom r v hv 0).left : ℝ) ((interpAtom r v hv (2 ^ r - 1)).right) =
      Set.Icc 0 1 := by
  rw [interpAtom_left, interpAtom_right]
  have : ((2 ^ r - 1 : ℕ) : ℝ) + 1 = 2 ^ r := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [this]; simp

/-- The interpolating leaves `j < 2^r` form an assembly on `[0,1]` with exactly `2^r` leaves. -/
theorem interp_isAssemblyRep :
    IsAssemblyRep (Set.Icc 0 1) (chainFun (interpAtom r v hv) (2 ^ r))
      ((Finset.range (2 ^ r)).image (interpAtom r v hv)) ∧
    ((Finset.range (2 ^ r)).image (interpAtom r v hv)).card = 2 ^ r ∧
    chainFun (interpAtom r v hv) (2 ^ r) ∈ Asm (Set.Icc 0 1) := by
  have hcons : ∀ j, j + 1 < 2 ^ r → (interpAtom r v hv j).right =
      (interpAtom r v hv (j + 1)).left := fun j _ => interpAtom_cons j
  have hmatch : ∀ j, j + 1 < 2 ^ r → (interpAtom r v hv j).line (interpAtom r v hv j).right =
      (interpAtom r v hv (j + 1)).line (interpAtom r v hv (j + 1)).left :=
    fun j _ => interpAtom_match j
  have h := chain_isAssemblyRep Nat.one_le_two_pow hcons hmatch
  have h2 := chain_mem_Asm Nat.one_le_two_pow hcons hmatch
  rw [interp_domain] at h h2
  exact ⟨h, chain_card hcons, h2⟩

/-- On `[0,1]` the interpolant is, on some cell `[j/n, (j+1)/n]`, the affine interpolant of
`v j` and `v (j+1)`. -/
lemma interp_eval {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : ℕ, j < 2 ^ r ∧ x ∈ Set.Icc ((j : ℝ) / 2 ^ r) ((j + 1) / 2 ^ r) ∧
      chainFun (interpAtom r v hv) (2 ^ r) x =
        (((j + 1) / 2 ^ r - x) * v j + (x - j / 2 ^ r) * v (j + 1)) /
          ((j + 1) / 2 ^ r - j / 2 ^ r) := by
  have hcons : ∀ j, j + 1 < 2 ^ r → (interpAtom r v hv j).right =
      (interpAtom r v hv (j + 1)).left := fun j _ => interpAtom_cons j
  have hmatch : ∀ j, j + 1 < 2 ^ r → (interpAtom r v hv j).line (interpAtom r v hv j).right =
      (interpAtom r v hv (j + 1)).line (interpAtom r v hv (j + 1)).left :=
    fun j _ => interpAtom_match j
  rw [← interp_domain (hv := hv)] at hx
  obtain ⟨j, hj, hxj⟩ := chain_cover Nat.one_le_two_pow hcons hx
  have hcell : x ∈ Set.Icc ((j : ℝ) / 2 ^ r) ((j + 1) / 2 ^ r) := by
    have := hxj; simp only [Atom.cell] at this; rwa [interpAtom_left, interpAtom_right] at this
  refine ⟨j, hj, hcell, ?_⟩
  rw [chainFun_eq_line hcons hmatch j hj x hxj, interpAtom_line]
  field_simp
  ring

/-- Interpolation error: if `f` has `C²` bound `M ≥ 0` on every subinterval of `[0,1]` and the
nodal values are within `η` of `f`, then `|f - g| ≤ M/(8n²) + η` on `[0,1]` (`n = 2^r`). -/
theorem interp_error {f : ℝ → ℝ} {M η : ℝ} (hM : 0 ≤ M)
    (hC2 : ∀ p q : ℝ, 0 ≤ p → q ≤ 1 → C2Bound f p q M)
    (hη : ∀ j : ℕ, j ≤ 2 ^ r → |(v j : ℝ) - f (j / 2 ^ r)| ≤ η) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x - chainFun (interpAtom r v hv) (2 ^ r) x| ≤
      M / (8 * ((2 : ℝ) ^ r) ^ 2) + η := by
  intro x hx
  obtain ⟨j, hj, hxj, heq⟩ := interp_eval (hv := hv) hx
  rw [heq]
  set p : ℝ := j / 2 ^ r
  set q : ℝ := (j + 1) / 2 ^ r
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have hqp : q - p = 1 / 2 ^ r := by simp only [p, q]; field_simp; ring
  have hpq : p < q := by rw [← sub_pos, hqp]; positivity
  have hp0 : 0 ≤ p := by positivity
  have hq1 : q ≤ 1 := by
    simp only [q]; rw [div_le_one h2r]; exact_mod_cast (show j + 1 ≤ 2 ^ r by omega)
  have hI := interp_error_bound hpq (hC2 p q hp0 hq1) hxj
  have hsq := mul_le_sq_div_four p q x
  have hfp := hη j hj.le
  have hfq : |(v (j + 1) : ℝ) - f q| ≤ η := by
    have := hη (j + 1) (by omega); push_cast at this; exact this
  have ha : 0 ≤ q - x := by linarith [hxj.2]
  have hb : 0 ≤ x - p := by linarith [hxj.1]
  have hqp' : 0 < q - p := by linarith
  -- error of the perturbation of the nodal values
  have hpert : |((q - x) * f p + (x - p) * f q) / (q - p) -
      ((q - x) * v j + (x - p) * v (j + 1)) / (q - p)| ≤ η := by
    rw [← sub_div, abs_div, abs_of_pos hqp', div_le_iff₀ hqp']
    have e : (q - x) * f p + (x - p) * f q - ((q - x) * v j + (x - p) * v (j + 1)) =
        (q - x) * (f p - v j) + (x - p) * (f q - v (j + 1)) := by ring
    rw [e]
    calc |(q - x) * (f p - v j) + (x - p) * (f q - v (j + 1))|
        ≤ |(q - x) * (f p - v j)| + |(x - p) * (f q - v (j + 1))| := abs_add_le _ _
      _ = (q - x) * |f p - v j| + (x - p) * |f q - v (j + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ (q - x) * η + (x - p) * η := by
          rw [abs_sub_comm] at hfp hfq
          exact add_le_add (mul_le_mul_of_nonneg_left hfp ha) (mul_le_mul_of_nonneg_left hfq hb)
      _ = η * (q - p) := by ring
  have hfin : M / 2 * ((x - p) * (q - x)) ≤ M / (8 * ((2 : ℝ) ^ r) ^ 2) := by
    have : (q - p) ^ 2 = 1 / ((2 : ℝ) ^ r) ^ 2 := by rw [hqp]; ring
    calc M / 2 * ((x - p) * (q - x)) ≤ M / 2 * ((q - p) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
      _ = M / (8 * ((2 : ℝ) ^ r) ^ 2) := by rw [this]; field_simp; ring
  calc |f x - ((q - x) * v j + (x - p) * v (j + 1)) / (q - p)|
      = |(f x - ((q - x) * f p + (x - p) * f q) / (q - p)) +
          (((q - x) * f p + (x - p) * f q) / (q - p) -
            ((q - x) * v j + (x - p) * v (j + 1)) / (q - p))| := by ring_nf
    _ ≤ |f x - ((q - x) * f p + (x - p) * f q) / (q - p)| +
          |((q - x) * f p + (x - p) * f q) / (q - p) -
            ((q - x) * v j + (x - p) * v (j + 1)) / (q - p)| := abs_add_le _ _
    _ ≤ M / (8 * ((2 : ℝ) ^ r) ^ 2) + η := add_le_add (hI.trans hfin) hpert

end

end Dyadic.Lib
