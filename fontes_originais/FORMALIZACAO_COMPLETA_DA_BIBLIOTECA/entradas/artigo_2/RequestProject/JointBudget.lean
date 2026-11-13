import RequestProject.Uniform
import RequestProject.Formats
import RequestProject.Serialization

/-!
# Section 3.4 — Joint error under leaf and height budgets

* Definition 3.9 (`jointErr`, `heightFor`), Proposition 3.10 (monotonicity),
* Theorem 3.12 (simultaneous control of error, leaves, height and bits),
* Corollary 3.13 (height sufficient for a prescribed accuracy).

The domain is `K = [0,1] = J_{0,0}`.
-/

namespace Artigo

open LTree Set Filter Topology

/-! ## Definition 3.9 -/

/-- uniform distance `‖f - g‖_{∞,[0,1]}` between `f` and the assembly represented by `T`
(rooted at `J_{0,0} = [0,1]`), as an extended real. -/
noncomputable def supDist (f : ℝ → ℝ) (T : LTree) : ENNReal :=
  ⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x - T.eval 0 0 x|

/-- representations admissible for `𝒜_{N,H}([0,1])`: at most `N` leaves, all atoms in `𝓛_H` -/
def AdmNH (N H : ℕ) (T : LTree) : Prop := WF 0 0 T ∧ T.numLeaves ≤ N ∧ T.maxHeight ≤ H

/-- the joint error `E_{N,H}(f)_∞ = inf_{g ∈ 𝒜_{N,H}} ‖f - g‖_∞` (`inf ∅ = +∞`). -/
noncomputable def jointErr (N H : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ (T : LTree) (_ : AdmNH N H T), supDist f T

/-- the leaf-only error `E_N(f)_∞` -/
noncomputable def leafErr (N : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ (T : LTree) (_ : WF 0 0 T ∧ T.numLeaves ≤ N), supDist f T

/-- `H_{ε,N}(f) = min {H ≥ 2 : E_{N,H}(f)_∞ ≤ ε}` -/
noncomputable def heightFor (ε : ℝ) (N : ℕ) (f : ℝ → ℝ) : ℕ :=
  sInf {H | 2 ≤ H ∧ jointErr N H f ≤ ENNReal.ofReal ε}

lemma supDist_le {f : ℝ → ℝ} {T : LTree} {e : ℝ}
    (h : ∀ x ∈ Icc (0 : ℝ) 1, |f x - T.eval 0 0 x| ≤ e) : supDist f T ≤ ENNReal.ofReal e :=
  iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (h x hx)

lemma jointErr_le {N H : ℕ} {f : ℝ → ℝ} {T : LTree} (hT : AdmNH N H T) :
    jointErr N H f ≤ supDist f T := iInf₂_le T hT

lemma heightFor_le {ε : ℝ} {N H : ℕ} {f : ℝ → ℝ} (hH : 2 ≤ H)
    (h : jointErr N H f ≤ ENNReal.ofReal ε) : heightFor ε N f ≤ H :=
  Nat.sInf_le ⟨hH, h⟩

/-! ## Proposition 3.10 -/

/-- **Proposition 3.10** (first inequality): `E_{N+1,H} ≤ E_{N,H}`. -/
theorem jointErr_succ_N_le (N H : ℕ) (f : ℝ → ℝ) : jointErr (N + 1) H f ≤ jointErr N H f :=
  le_iInf₂ fun T h => iInf₂_le T ⟨h.1, by have := h.2.1; omega, h.2.2⟩

/-- **Proposition 3.10** (second inequality): `E_{N,H+1} ≤ E_{N,H}`. -/
theorem jointErr_succ_H_le (N H : ℕ) (f : ℝ → ℝ) : jointErr N (H + 1) f ≤ jointErr N H f :=
  le_iInf₂ fun T h => iInf₂_le T ⟨h.1, h.2.1, by have := h.2.2; omega⟩

lemma jointErr_antitone (N : ℕ) (f : ℝ → ℝ) : Antitone (fun H => jointErr N H f) :=
  antitone_nat_of_succ_le fun H => jointErr_succ_H_le N H f

lemma iInf_jointErr (N : ℕ) (f : ℝ → ℝ) : ⨅ H, jointErr N H f = leafErr N f := by
  apply le_antisymm
  · refine le_iInf fun T => le_iInf fun h => ?_
    exact iInf_le_of_le T.maxHeight (iInf₂_le T ⟨h.1, h.2, le_rfl⟩)
  · exact le_iInf fun H => le_iInf fun T => le_iInf fun h => iInf₂_le T ⟨h.1, h.2.1⟩

/-- **Proposition 3.10** (limit): `E_{N,H}(f)_∞ ↓ E_N(f)_∞` as `H → ∞`. -/
theorem jointErr_tendsto (N : ℕ) (f : ℝ → ℝ) :
    Antitone (fun H => jointErr N H f) ∧
      Tendsto (fun H => jointErr N H f) atTop (𝓝 (leafErr N f)) := by
  refine ⟨jointErr_antitone N f, ?_⟩
  rw [← iInf_jointErr]
  exact tendsto_atTop_iInf (jointErr_antitone N f)

/-! ## The alternating-grid nodal values of Theorem 3.12 -/

/-- parity `j mod 2` as a real -/
noncomputable def parR (j : ℤ) : ℝ := ((j % 2 : ℤ) : ℝ)

/-- the integer numerator `b_j` of the nodal value `v_j = b_j / (2 n²)`, `n = 2^r`: the point
of the grid `n^{-2}(ℤ + (j mod 2)/2)` nearest to `f(t_j)`, ties broken downward. -/
noncomputable def bnum (f : ℝ → ℝ) (r : ℕ) (j : ℤ) : ℤ :=
  2 * ⌈(2 : ℝ) ^ (2 * r) * f (cL r j) - parR j / 2 - 1 / 2⌉ + j % 2

/-- the nodal values `v_j` -/
noncomputable def jvals (f : ℝ → ℝ) (r : ℕ) (j : ℤ) : ℚ := (bnum f r j : ℚ) / (2 * 2 ^ (2 * r))

lemma jvals_cast (f : ℝ → ℝ) (r : ℕ) (j : ℤ) :
    ((jvals f r j : ℚ) : ℝ) = (bnum f r j : ℝ) / (2 * 2 ^ (2 * r)) := by
  simp [jvals]

lemma bnum_mod (f : ℝ → ℝ) (r : ℕ) (j : ℤ) : bnum f r j % 2 = j % 2 := by
  unfold bnum; omega

lemma jvals_ne (f : ℝ → ℝ) (r : ℕ) (j : ℤ) : jvals f r j ≠ jvals f r (j + 1) := by
  intro h
  unfold jvals at h
  have h2 : (bnum f r j : ℚ) = bnum f r (j + 1) := by
    have : (2 * 2 ^ (2 * r) : ℚ) ≠ 0 := by positivity
    field_simp at h; exact_mod_cast h
  have h3 : bnum f r j = bnum f r (j + 1) := by exact_mod_cast h2
  have := bnum_mod f r j; have := bnum_mod f r (j + 1)
  omega

lemma jvals_good (f : ℝ → ℝ) (r r' : ℕ) (m : ℤ) : GoodVals (jvals f r) r' m :=
  fun n _ _ => jvals_ne f r n

/-- key identity: `v_j = (c + p/2)/n²` -/
lemma jvals_eq (f : ℝ → ℝ) (r : ℕ) (j : ℤ) :
    ((jvals f r j : ℚ) : ℝ) = ((⌈(2 : ℝ) ^ (2 * r) * f (cL r j) - parR j / 2 - 1 / 2⌉ : ℤ) + parR j / 2)
      / 2 ^ (2 * r) := by
  rw [jvals_cast]; unfold bnum parR; push_cast; field_simp

/-- the quantization error is at most `Δ/2 = 1/(2n²)` -/
lemma jvals_err (f : ℝ → ℝ) (r : ℕ) (j : ℤ) :
    |f (cL r j) - jvals f r j| ≤ 1 / (2 * 2 ^ (2 * r)) := by
  rw [jvals_eq]
  set z := (2 : ℝ) ^ (2 * r) * f (cL r j) - parR j / 2
  set c := ⌈z - 1 / 2⌉
  have h1 := Int.le_ceil (z - 1 / 2)
  have h2 := Int.ceil_lt_add_one (z - 1 / 2)
  have hn : (0 : ℝ) < 2 ^ (2 * r) := by positivity
  have e : f (cL r j) - ((c : ℝ) + parR j / 2) / 2 ^ (2 * r) = (z - c) / 2 ^ (2 * r) := by
    simp only [z]; field_simp; ring
  rw [e, abs_div, abs_of_pos hn, div_le_div_iff₀ hn (by positivity)]
  have : |z - c| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  nlinarith

/-- **determinism of the construction**: `v_j` is a point of the alternating grid
`n^{-2}(ℤ + (j mod 2)/2)` nearest to `f(t_j)`, and in case of a tie it is the smaller one. -/
theorem jvals_nearest (f : ℝ → ℝ) (r : ℕ) (j : ℤ) (c' : ℤ) :
    let v' : ℝ := ((c' : ℝ) + parR j / 2) / 2 ^ (2 * r)
    |f (cL r j) - jvals f r j| ≤ |f (cL r j) - v'| ∧
      (|f (cL r j) - jvals f r j| = |f (cL r j) - v'| → ((jvals f r j : ℚ) : ℝ) ≤ v') := by
  intro v'
  rw [jvals_eq]
  set z := (2 : ℝ) ^ (2 * r) * f (cL r j) - parR j / 2
  set c := ⌈z - 1 / 2⌉
  have h1 := Int.le_ceil (z - 1 / 2)
  have h2 := Int.ceil_lt_add_one (z - 1 / 2)
  have hn : (0 : ℝ) < 2 ^ (2 * r) := by positivity
  have e : ∀ d : ℝ, f (cL r j) - (d + parR j / 2) / 2 ^ (2 * r) = (z - d) / 2 ^ (2 * r) := by
    intro d; simp only [z]; field_simp; ring
  simp only [v']
  rw [e, e, abs_div, abs_div, abs_of_pos hn]
  have hc' : c = c' ∨ c + 1 ≤ c' ∨ c' + 1 ≤ c := by omega
  have key : |z - c| ≤ |z - c'| ∧ (|z - c| = |z - c'| → (c : ℝ) ≤ c') := by
    rcases hc' with hc' | hc' | hc'
    · subst hc'; exact ⟨le_rfl, fun _ => le_rfl⟩
    · have : (c : ℝ) + 1 ≤ c' := by exact_mod_cast hc'
      refine ⟨?_, fun _ => by linarith⟩
      rw [abs_of_neg (by linarith : z - (c' : ℝ) < 0)]
      rw [abs_le]; constructor <;> linarith
    · have hc'' : (c' : ℝ) + 1 ≤ c := by exact_mod_cast hc'
      have : z - c' > 1 / 2 := by linarith
      refine ⟨?_, fun h => ?_⟩
      · rw [abs_of_pos (by linarith : (0:ℝ) < z - c')]
        rw [abs_le]; constructor <;> linarith
      · exfalso
        rw [abs_of_pos (by linarith : (0:ℝ) < z - c')] at h
        cases abs_cases (z - c) <;> linarith
  refine ⟨div_le_div_of_nonneg_right key.1 hn.le, fun h => ?_⟩
  have h' : |z - c| = |z - c'| := by
    field_simp at h; linarith
  exact div_le_div_of_nonneg_right (by linarith [key.2 h']) hn.le

/-! ## Bounds on the numerators -/

/-- `C₀ = 4R + M/2` -/
noncomputable def C0 (R M : ℝ) : ℝ := 4 * R + M / 2

/-- `C_H = max {4(R+1), 2(C₀+1)}` -/
noncomputable def CH (R M : ℝ) : ℝ := max (4 * (R + 1)) (2 * (C0 R M + 1))

lemma cL_mem01 {r : ℕ} {j : ℤ} (h0 : 0 ≤ j) (h1 : j ≤ 2 ^ r) : cL r j ∈ Icc (0 : ℝ) 1 := by
  unfold cL
  have hp : (0 : ℝ) < 2 ^ r := by positivity
  have : (j : ℝ) ≤ 2 ^ r := by exact_mod_cast h1
  have : (0 : ℝ) ≤ j := by exact_mod_cast h0
  constructor
  · positivity
  · rw [div_le_one hp]; linarith

lemma bnum_cast (f : ℝ → ℝ) (r : ℕ) (j : ℤ) :
    (bnum f r j : ℝ) = 2 * 2 ^ (2 * r) * ((jvals f r j : ℚ) : ℝ) := by
  rw [jvals_cast]; field_simp

/-- `|b_j| ≤ 2Rn² + 1` -/
lemma bnum_abs_le {f : ℝ → ℝ} {R : ℝ} {r : ℕ} {j : ℤ} (hf : |f (cL r j)| ≤ R) :
    |(bnum f r j : ℝ)| ≤ 2 * R * 2 ^ (2 * r) + 1 := by
  have he := jvals_err f r j
  have hn : (0 : ℝ) < 2 ^ (2 * r) := by positivity
  rw [bnum_cast, abs_mul, abs_of_pos (by positivity)]
  have hv : |((jvals f r j : ℚ) : ℝ)| ≤ R + 1 / (2 * 2 ^ (2 * r)) := by
    calc |((jvals f r j : ℚ) : ℝ)| = |f (cL r j) - (f (cL r j) - jvals f r j)| := by ring_nf
      _ ≤ |f (cL r j)| + |f (cL r j) - jvals f r j| := abs_sub _ _
      _ ≤ _ := by linarith
  calc 2 * 2 ^ (2 * r) * |((jvals f r j : ℚ) : ℝ)| ≤ 2 * 2 ^ (2 * r) * (R + 1 / (2 * 2 ^ (2 * r))) := by
        gcongr
    _ = _ := by field_simp

/-- `|b_{j+1} - b_j| ≤ 2C₀n + 2` -/
lemma bnum_diff_le {f : ℝ → ℝ} {C : ℝ} {r : ℕ} {j : ℤ}
    (hf : |f (cL r (j + 1)) - f (cL r j)| ≤ C / 2 ^ r) :
    |(bnum f r (j + 1) : ℝ) - bnum f r j| ≤ 2 * C * 2 ^ r + 2 := by
  have he1 := jvals_err f r j
  have he2 := jvals_err f r (j + 1)
  have hn : (0 : ℝ) < 2 ^ r := by positivity
  have h2r : (2 : ℝ) ^ (2 * r) = 2 ^ r * 2 ^ r := by rw [two_mul, pow_add]
  rw [bnum_cast, bnum_cast, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  have hv : |((jvals f r (j + 1) : ℚ) : ℝ) - jvals f r j| ≤ C / 2 ^ r + 1 / 2 ^ (2 * r) := by
    have e : ((jvals f r (j + 1) : ℚ) : ℝ) - jvals f r j = (f (cL r (j + 1)) - f (cL r j))
        - (f (cL r (j + 1)) - jvals f r (j + 1)) + (f (cL r j) - jvals f r j) := by ring
    rw [e]
    calc _ ≤ |(f (cL r (j + 1)) - f (cL r j)) - (f (cL r (j + 1)) - jvals f r (j + 1))|
          + |f (cL r j) - jvals f r j| := abs_add_le _ _
      _ ≤ |f (cL r (j + 1)) - f (cL r j)| + |f (cL r (j + 1)) - jvals f r (j + 1)|
          + |f (cL r j) - jvals f r j| := by gcongr; exact abs_sub _ _
      _ ≤ C / 2 ^ r + 1 / (2 * 2 ^ (2 * r)) + 1 / (2 * 2 ^ (2 * r)) := by linarith
      _ = _ := by field_simp; ring
  calc 2 * 2 ^ (2 * r) * |((jvals f r (j + 1) : ℚ) : ℝ) - jvals f r j|
      ≤ 2 * 2 ^ (2 * r) * (C / 2 ^ r + 1 / 2 ^ (2 * r)) := by gcongr
    _ = _ := by rw [h2r]; field_simp

/-- Lipschitz bound from Lemma 3.9 -/
lemma FRM_lipschitz {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) : |f y - f x| ≤ C0 R M * |y - x| := by
  have hd : ∀ z ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f z :=
    fun z _ => (hf.1.differentiable (by norm_num)) z
  have := Convex.norm_image_sub_le_of_norm_deriv_le hd
    (fun z hz => by rw [Real.norm_eq_abs]; exact derivative_control hf z hz) (convex_Icc 0 1) hx hy
  simpa [Real.norm_eq_abs, C0] using this

lemma FRM_R_nonneg {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) : 0 ≤ R :=
  le_trans (abs_nonneg _) (hf.2.1 0 (by simp))

lemma FRM_M_nonneg {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) : 0 ≤ M :=
  le_trans (abs_nonneg _) (hf.2.2 0 (by simp))

lemma natAbs_cast_le {z : ℤ} {X : ℝ} (h : |(z : ℝ)| ≤ X) : ((z.natAbs : ℕ) : ℝ) ≤ X := by
  rw [Nat.cast_natAbs, Int.cast_abs]; exact h

lemma ht_cast_le_of {p : ℤ} {q : ℕ} (hq : 0 < q) {X : ℝ} (hp : |(p : ℝ)| ≤ X) (hqX : (q : ℝ) ≤ X) :
    (ht ((p : ℚ) / q) : ℝ) ≤ X := by
  have := ht_div_le p q hq
  have h2 : ((max p.natAbs q : ℕ) : ℝ) ≤ X := by
    rw [Nat.cast_max]; exact max_le (natAbs_cast_le hp) hqX
  exact le_trans (by exact_mod_cast this) h2

set_option maxHeartbeats 1000000 in
/-- heights of the atoms of the construction (and of their left endpoints and left values) -/
lemma joint_atom_bounds {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {r : ℕ} (hr : 1 ≤ r) {j : ℤ}
    (h0 : 0 ≤ j) (h1 : j < 2 ^ r) :
    ((interpAtom (jvals f r) r j).height : ℝ) ≤ CH R M * (2 ^ r) ^ 2 ∧
    (ht (interpAtom (jvals f r) r j).left : ℝ) ≤ CH R M * (2 ^ r) ^ 2 ∧
    (ht (interpAtom (jvals f r) r j).lval : ℝ) ≤ CH R M * (2 ^ r) ^ 2 := by
  have hR := FRM_R_nonneg hf
  have hM := FRM_M_nonneg hf
  have hC0 : 0 ≤ C0 R M := by unfold C0; positivity
  have hCH1 : 4 * (R + 1) ≤ CH R M := le_max_left _ _
  have hCH2 : 2 * (C0 R M + 1) ≤ CH R M := le_max_right _ _
  set n : ℝ := 2 ^ r with hn_def
  have hn2 : (2 : ℝ) ≤ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have h2r : (2 : ℝ) ^ (2 * r) = n ^ 2 := by rw [hn_def, ← pow_mul, mul_comm]
  have hfj : |f (cL r j)| ≤ R := hf.2.1 _ (cL_mem01 h0 h1.le)
  have hfj1 : |f (cL r (j + 1))| ≤ R := hf.2.1 _ (cL_mem01 (r := r) (j := j + 1) (by omega) (by omega))
  have hb0 := bnum_abs_le (r := r) hfj
  have hb1 := bnum_abs_le (r := r) hfj1
  have hlip : |f (cL r (j + 1)) - f (cL r j)| ≤ C0 R M / 2 ^ r := by
    have := FRM_lipschitz hf (cL_mem01 h0 h1.le) (cL_mem01 (r := r) (j := j + 1) (by omega) (by omega))
    have e : cL r (j + 1) - cL r j = 1 / 2 ^ r := by unfold cL; push_cast; field_simp; ring
    rw [e, abs_of_pos (a := (1 : ℝ) / 2 ^ r) (by positivity)] at this
    calc _ ≤ C0 R M * (1 / 2 ^ r) := this
      _ = _ := by ring
  have hd := bnum_diff_le hlip
  rw [h2r] at hb0 hb1
  have hne := jvals_ne f r j
  have hA : interpAtom (jvals f r) r j = Atom.ofEndpoints r j (jvals f r j) (jvals f r (j + 1)) hne := by
    simp [interpAtom, hne]
  -- y₀ and s as fractions
  have hy0 : (interpAtom (jvals f r) r j).y0 =
      ((bnum f r j + bnum f r (j + 1) : ℤ) : ℚ) / ((4 * 2 ^ (2 * r) : ℕ) : ℚ) := by
    rw [hA]; simp only [Atom.ofEndpoints, jvals]; push_cast; field_simp; ring
  have hs : (interpAtom (jvals f r) r j).s =
      ((bnum f r (j + 1) - bnum f r j : ℤ) : ℚ) / ((2 * 2 ^ r : ℕ) : ℚ) := by
    rw [hA]; simp only [Atom.ofEndpoints, jvals]; push_cast
    rw [show 2 * r = r + r by ring, pow_add]; field_simp
  have hlv : (interpAtom (jvals f r) r j).lval = ((bnum f r j : ℤ) : ℚ) / ((2 * 2 ^ (2 * r) : ℕ) : ℚ) := by
    rw [interpAtom_lval hne]; simp [jvals]
  have hcast4 : (((4 * 2 ^ (2 * r) : ℕ) : ℝ)) = 4 * n ^ 2 := by push_cast; rw [h2r]
  have hcast2 : (((2 * 2 ^ (2 * r) : ℕ) : ℝ)) = 2 * n ^ 2 := by push_cast; rw [h2r]
  have hcast2' : (((2 * 2 ^ r : ℕ) : ℝ)) = 2 * n := by push_cast; rfl
  have hn1 : 1 ≤ n := by linarith
  have hnn : n ≤ n ^ 2 := by nlinarith
  have hCHn : n ^ 2 ≤ CH R M * n ^ 2 :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  have h2n : (2 : ℝ) ≤ n ^ 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- atom height
    have hk : ((r + 1 : ℕ) : ℝ) ≤ n := by
      have : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
      rw [hn_def]; exact_mod_cast this
    have hm : ((j.natAbs + 1 : ℕ) : ℝ) ≤ n := by
      have : (j.natAbs : ℤ) + 1 ≤ 2 ^ r := by omega
      rw [hn_def]; exact_mod_cast this
    have hy : (ht (interpAtom (jvals f r) r j).y0 : ℝ) ≤ CH R M * n ^ 2 := by
      rw [hy0]
      apply ht_cast_le_of (by positivity)
      · push_cast
        calc |(bnum f r j : ℝ) + bnum f r (j + 1)| ≤ |(bnum f r j : ℝ)| + |(bnum f r (j + 1) : ℝ)| :=
              abs_add_le _ _
          _ ≤ 4 * (R + 1) * n ^ 2 := by nlinarith
          _ ≤ _ := by gcongr
      · rw [hcast4]; nlinarith
    have hsl : (ht (interpAtom (jvals f r) r j).s : ℝ) ≤ CH R M * n ^ 2 := by
      rw [hs]
      apply ht_cast_le_of (by positivity)
      · push_cast
        calc |(bnum f r (j + 1) : ℝ) - bnum f r j| ≤ 2 * C0 R M * 2 ^ r + 2 := hd
          _ ≤ 2 * (C0 R M + 1) * n := by rw [← hn_def]; nlinarith
          _ ≤ CH R M * n ^ 2 := by
            have : 0 ≤ CH R M := by linarith
            nlinarith
      · rw [hcast2']; nlinarith
    have hfl : ∀ c : ℕ, (c : ℝ) ≤ CH R M * n ^ 2 → c ≤ ⌊CH R M * n ^ 2⌋₊ :=
      fun c hc => Nat.le_floor hc
    have hmain : (interpAtom (jvals f r) r j).height ≤ ⌊CH R M * n ^ 2⌋₊ := by
      rw [Atom.height_le_iff]
      simp only [interpAtom_k, interpAtom_m]
      refine ⟨hfl 2 (by push_cast; linarith), hfl _ (by linarith), hfl _ (by linarith),
        hfl _ hy, hfl _ hsl⟩
    exact le_trans (by exact_mod_cast hmain) (Nat.floor_le (by linarith))
  · -- left endpoint j / 2^r
    have := ht_dyadic_le j r
    have hl : (interpAtom (jvals f r) r j).left = (j : ℚ) / 2 ^ r := by simp [Atom.left]
    rw [hl]
    have h2 : ((max j.natAbs (2 ^ r) : ℕ) : ℝ) ≤ CH R M * n ^ 2 := by
      rw [Nat.cast_max]
      apply max_le
      · have : (j.natAbs : ℤ) ≤ 2 ^ r := by omega
        have : ((j.natAbs : ℕ) : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast this
        linarith
      · push_cast; rw [← hn_def]; linarith
    exact le_trans (by exact_mod_cast this) h2
  · -- left value v_j
    rw [hlv]
    apply ht_cast_le_of (by positivity)
    · calc |(bnum f r j : ℝ)| ≤ 2 * R * n ^ 2 + 1 := hb0
        _ ≤ 4 * (R + 1) * n ^ 2 := by nlinarith
        _ ≤ _ := by gcongr
    · rw [hcast2]; nlinarith [hCH1]

/-- refined bound on `L_{ReLU,rat}` when the knots and the left values have height `≤ H` -/
lemma Lrat_le_log {L : List Atom} {H : ℕ} (hH : 2 ≤ H) (hL : L ≠ []) (hh : ∀ a ∈ L, a.height ≤ H)
    (hk : ∀ a ∈ L, ht a.left ≤ H ∧ ht a.lval ≤ H) :
    Lrat L ≤ 100 * L.length * (Nat.log 2 H + 1) := by
  obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  have ha := hh a (by simp)
  obtain ⟨hka, hla⟩ := hk a (by simp)
  unfold Lrat ratReluCodec reluCodec
  simp only [ratParams, List.length_append, Codec.prod]
  rw [Codec.encList_length]
  try dsimp only
  have hint : ht (a.y0 - a.s * a.x0) ≤ 2 ^ 1 * H ^ 3 := by
    rw [← Atom.lval_sub]
    calc ht (a.lval - a.s * a.left) ≤ 2 * ht a.lval * ht (a.s * a.left) := ht_sub_le _ _
      _ ≤ 2 * H * (H * H) := by
        gcongr
        exact le_trans (ht_mul_le _ _) (Nat.mul_le_mul (le_trans a.ht_s_le_height ha) hka)
      _ = 2 ^ 1 * H ^ 3 := by ring
  have e1 := ratCodec_length_le_ht (a := 1) (e := 3) (H := H) (by omega) hint
  have e2 := ratCodec_length_le (A := H) (by omega) (le_trans a.ht_s_le_height ha)
  have hp := sum_map_le (reluPairs (a :: L')) (fun q => (ratCodec.enc q.1 ++ ratCodec.enc q.2).length)
    (12 * Nat.log 2 H + 26) (by
      intro q hq
      obtain ⟨_, _, _, h4⟩ := pair_heights hh q hq
      have h3 : ht q.1 ≤ H := by
        simp only [reluPairs, List.mem_map] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        exact (hk p.2 (List.mem_of_mem_tail (List.of_mem_zip hp).2)).1
      simp only [List.length_append]
      have f1 := ratCodec_length_le (A := H) (by omega) h3
      have f2 := ratCodec_length_le_ht (a := 1) (e := 2) (H := H) (by omega) (by simpa using h4)
      omega)
  have hlen := reluPairs_length a L'
  have hg := gamma_length_le_self (N := (reluPairs (a :: L')).length + 1)
  simp only [List.length_cons] at hlen ⊢
  nlinarith

lemma cellIcc_zero : cellIcc 0 0 = Icc (0 : ℝ) 1 := by simp [cellIcc]

/-- error of the construction: `‖f - g_n‖_∞ ≤ (M+4)/(8n²)` -/
lemma joint_error {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) (r : ℕ) :
    ∀ x ∈ Icc (0 : ℝ) 1, |f x - (uniformTree (jvals f r) r 0 0).eval 0 0 x| ≤
      (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2) := by
  intro x hx
  rw [← cellIcc_zero] at hx
  obtain ⟨n, -, -, hxn, hsub, herr⟩ := uniformTree_error (jvals_good f r r 0) f
    (η := 1 / (2 * 2 ^ (2 * r))) (fun n _ _ => by rw [zero_add]; exact jvals_err f r n) x hx
  rw [zero_add] at hxn hsub herr
  have hsub' : Icc (cL r n) (cR r n) ⊆ Icc (0 : ℝ) 1 := by rw [← cellIcc_eq, ← cellIcc_zero]; exact hsub
  have hint := interp_remainder_C2 hf.1 (cL_lt_cR r n) (M := M)
    (fun y hy => hf.2.2 y (hsub' hy)) x (by rw [← cellIcc_eq]; exact hxn)
  have hlen : cR r n - cL r n = 1 / 2 ^ r := by unfold cR cL; field_simp; ring
  rw [hlen] at hint
  have h2r : (2 : ℝ) ^ (2 * r) = ((2 : ℝ) ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [h2r] at herr
  calc _ ≤ _ := herr
    _ ≤ (1 / 2 ^ r) ^ 2 / 8 * M + 1 / (2 * ((2 : ℝ) ^ r) ^ 2) := by gcongr
    _ = _ := by field_simp; ring

/-- **Theorem 3.12 (controle simultâneo de erro, folhas, altura e bits)**.  There is a constant
`C_b` (depending only on `R, M`) such that for every dyadic power `n = 2^r ≥ 2` and every
`f ∈ 𝓕_{R,M}`, the (deterministic) assembly `g_n` interpolating the alternating-grid nodal
values `v_j` (see `jvals`, `jvals_nearest`) has exactly `n` leaves and satisfies
`‖f - g_n‖_∞ ≤ (M+4)/(8n²)`, `ht_max(g_n) ≤ C_H n²`, and its three code lengths are
`≤ C_b n log₂(2n)`. -/
theorem joint_budget (R M : ℝ) : ∃ Cb : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ f ∈ FRM R M,
    ∃ T : LTree, T = uniformTree (jvals f r) r 0 0 ∧
      WF 0 0 T ∧ T.numLeaves = 2 ^ r ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |f x - T.eval 0 0 x| ≤ (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2)) ∧
      (T.maxHeight : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 ∧
      Latom T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) ∧
      Lstr T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) ∧
      Lrat T.leaves ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) := by
  set K := ⌈CH R M⌉₊
  refine ⟨100 * (Nat.log 2 K + 5), fun r hr f hf => ⟨_, rfl, uniformTree_WF _ r 0 0 (jvals_good f r r 0),
    uniformTree_numLeaves _ r 0 0, joint_error hf r, ?_⟩⟩
  have hR := FRM_R_nonneg hf
  have hCH4 : 4 ≤ CH R M := le_trans (by linarith) (le_max_left _ _)
  have hK : CH R M ≤ K := Nat.le_ceil _
  have hK4 : 4 ≤ K := by exact_mod_cast (show (4 : ℝ) ≤ K by linarith)
  set T := uniformTree (jvals f r) r 0 0
  have hn2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  -- all leaves are construction atoms
  have hleaf : ∀ a ∈ T.leaves, (a.height : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 ∧
      (ht a.left : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 ∧ (ht a.lval : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 := by
    intro a ha
    obtain ⟨j, h1, h2, rfl⟩ := uniformTree_leaves _ r 0 0 a ha
    simp only [mul_zero, zero_add, mul_one] at h1 h2
    rw [zero_add]
    exact joint_atom_bounds hf hr h1 h2
  set Hn := K * (2 ^ r) ^ 2
  have hHnR : CH R M * ((2 : ℝ) ^ r) ^ 2 ≤ (Hn : ℝ) := by
    simp only [Hn]; push_cast; gcongr
  have toNat : ∀ c : ℕ, (c : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 → c ≤ Hn := fun c hc => by
    exact_mod_cast hc.trans hHnR
  have hHn2 : 2 ≤ Hn := by
    simp only [Hn]; nlinarith [Nat.one_le_two_pow (n := r)]
  have hhH : ∀ a ∈ T.leaves, a.height ≤ Hn := fun a ha => toNat _ (hleaf a ha).1
  have hkH : ∀ a ∈ T.leaves, ht a.left ≤ Hn ∧ ht a.lval ≤ Hn :=
    fun a ha => ⟨toNat _ (hleaf a ha).2.1, toNat _ (hleaf a ha).2.2⟩
  have hne : T.leaves ≠ [] := by
    intro h; have := uniformTree_numLeaves (jvals f r) r 0 0; simp [numLeaves, T, h] at this
    have := Nat.one_le_two_pow (n := r); omega
  have hlen : T.leaves.length = 2 ^ r := uniformTree_numLeaves _ r 0 0
  -- logarithms
  have hlog2n : Nat.log 2 (2 * 2 ^ r) = r + 1 := by
    rw [← pow_succ', Nat.log_pow (by norm_num)]
  have hlogHn : Nat.log 2 Hn + 1 ≤ (Nat.log 2 K + 5) * (r + 1) := by
    have hKlt : K ≤ 2 ^ (Nat.log 2 K + 1) := (Nat.lt_pow_succ_log_self (by norm_num) K).le
    have := nlog_le (n := Hn) (a := Nat.log 2 K + 1) (e := 2) (H := 2 ^ r) (by omega)
      (by simp only [Hn]; gcongr)
    rw [Nat.log_pow (by norm_num)] at this
    nlinarith
  -- maximal height
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hfl : T.maxHeight ≤ ⌊CH R M * ((2 : ℝ) ^ r) ^ 2⌋₊ :=
      maxHeight_le_iff.mpr fun a ha => Nat.le_floor (hleaf a ha).1
    exact le_trans (by exact_mod_cast hfl) (Nat.floor_le (by positivity))
  · have h := Latom_le hHn2 hne hhH
    rw [hlen, hlog2n] at *
    calc Latom T.leaves ≤ 35 * 2 ^ r * Nat.log 2 Hn := h
      _ ≤ 100 * 2 ^ r * (Nat.log 2 Hn + 1) := by gcongr <;> omega
      _ ≤ 100 * 2 ^ r * ((Nat.log 2 K + 5) * (r + 1)) := by gcongr
      _ = _ := by ring
  · have h := Lstr_le hHn2 hne hhH
    rw [hlen, hlog2n] at *
    calc Lstr T.leaves ≤ 100 * 2 ^ r * Nat.log 2 Hn := h
      _ ≤ 100 * 2 ^ r * (Nat.log 2 Hn + 1) := by gcongr; omega
      _ ≤ 100 * 2 ^ r * ((Nat.log 2 K + 5) * (r + 1)) := by gcongr
      _ = _ := by ring
  · have h := Lrat_le_log hHn2 hne hhH hkH
    rw [hlen, hlog2n] at *
    calc Lrat T.leaves ≤ 100 * 2 ^ r * (Nat.log 2 Hn + 1) := h
      _ ≤ 100 * 2 ^ r * ((Nat.log 2 K + 5) * (r + 1)) := by gcongr
      _ = _ := by ring

/-- the assembly of Theorem 3.12 is admissible for `𝒜_{N,H}` -/
lemma joint_adm {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {r : ℕ} (hr : 1 ≤ r) {N H : ℕ}
    (hN : 2 ^ r ≤ N) (hH : CH R M * ((2 : ℝ) ^ r) ^ 2 ≤ H) :
    AdmNH N H (uniformTree (jvals f r) r 0 0) ∧
      supDist f (uniformTree (jvals f r) r 0 0) ≤ ENNReal.ofReal ((M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2)) := by
  obtain ⟨Cb, hCb⟩ := joint_budget R M
  obtain ⟨T, rfl, hWF, hnum, herr, hht, -⟩ := hCb r hr f hf
  refine ⟨⟨hWF, hnum ▸ hN, ?_⟩, supDist_le herr⟩
  exact_mod_cast hht.trans hH

/-- **Theorem 3.12**, consequence (eq. joint-all-N): for every integer `N ≥ 2`,
`E_{N,⌈C_H N²⌉}(f)_∞ < (M+4)/(2N²)`. -/
theorem joint_all_N {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) (N : ℕ) (hN : 2 ≤ N) :
    jointErr N ⌈CH R M * (N : ℝ) ^ 2⌉₊ f < ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2)) := by
  have hM := FRM_M_nonneg hf
  have hR := FRM_R_nonneg hf
  have hCH : 0 ≤ CH R M := le_trans (by linarith) (le_max_left _ _)
  set r := Nat.log 2 N
  have hr : 1 ≤ r := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have h1 : 2 ^ r ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : N < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h1' : ((2 : ℝ) ^ r) ≤ N := by exact_mod_cast h1
  have h2' : (N : ℝ) < 2 * 2 ^ r := by rw [← pow_succ']; exact_mod_cast h2
  have hpos : (0 : ℝ) < 2 ^ r := by positivity
  obtain ⟨hadm, hsup⟩ := joint_adm hf hr h1 (H := ⌈CH R M * (N : ℝ) ^ 2⌉₊)
    (le_trans (by gcongr) (Nat.le_ceil _))
  refine lt_of_le_of_lt (jointErr_le hadm) (lt_of_le_of_lt hsup ?_)
  have hN0 : (0 : ℝ) < N := by positivity
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : (N : ℝ) ^ 2 < 4 * ((2 : ℝ) ^ r) ^ 2 := by nlinarith
  nlinarith

/-! ## Corollary 3.13 -/

/-- `X_ε = max {2, √((M+4)/(8ε))}` -/
noncomputable def Xeps (M ε : ℝ) : ℝ := max 2 (Real.sqrt ((M + 4) / (8 * ε)))

/-- `r_ε = ⌈log₂ X_ε⌉`, so that `n_ε = 2^{r_ε}` -/
noncomputable def rEps (M ε : ℝ) : ℕ := ⌈Real.logb 2 (Xeps M ε)⌉₊

/-- `n_ε = 2^{⌈log₂ max{2, √((M+4)/(8ε))}⌉}` -/
noncomputable def nEps (M ε : ℝ) : ℕ := 2 ^ rEps M ε

/-- `H_ε = ⌈C_H n_ε²⌉` -/
noncomputable def HEps (R M ε : ℝ) : ℕ := ⌈CH R M * ((nEps M ε : ℕ) : ℝ) ^ 2⌉₊

lemma Xeps_ge (M ε : ℝ) : 2 ≤ Xeps M ε := le_max_left _ _

lemma logb_Xeps_ge (M ε : ℝ) : 1 ≤ Real.logb 2 (Xeps M ε) := by
  rw [← Real.logb_self_eq_one (b := 2) (by norm_num)]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (Xeps_ge M ε)

lemma rEps_ge (M ε : ℝ) : 1 ≤ rEps M ε := by
  unfold rEps
  have := logb_Xeps_ge M ε
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)

lemma nEps_cast (M ε : ℝ) : ((nEps M ε : ℕ) : ℝ) = (2 : ℝ) ^ rEps M ε := by simp [nEps]

lemma Xeps_le_nEps (M ε : ℝ) : Xeps M ε ≤ (nEps M ε : ℝ) := by
  rw [nEps_cast]
  have hX : 0 < Xeps M ε := by linarith [Xeps_ge M ε]
  calc Xeps M ε = (2 : ℝ) ^ Real.logb 2 (Xeps M ε) := (Real.rpow_logb (by norm_num) (by norm_num) hX).symm
    _ ≤ (2 : ℝ) ^ ((rEps M ε : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = _ := Real.rpow_natCast _ _

lemma nEps_lt (M ε : ℝ) : (nEps M ε : ℝ) < 2 * Xeps M ε := by
  rw [nEps_cast]
  have hX : 0 < Xeps M ε := by linarith [Xeps_ge M ε]
  have hl := logb_Xeps_ge M ε
  calc (2 : ℝ) ^ rEps M ε = (2 : ℝ) ^ ((rEps M ε : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ < (2 : ℝ) ^ (Real.logb 2 (Xeps M ε) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (Nat.ceil_lt_add_one (by linarith))
    _ = 2 * Xeps M ε := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hX]; ring

lemma Xeps_le {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Xeps M ε ≤ (2 + Real.sqrt ((M + 4) / 8)) / Real.sqrt ε := by
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  have e : Real.sqrt ((M + 4) / (8 * ε)) = Real.sqrt ((M + 4) / 8) / Real.sqrt ε := by
    rw [← Real.sqrt_div' _ hε.le]; congr 1; field_simp
  unfold Xeps
  rw [e]
  apply max_le
  · rw [le_div_iff₀ hs]; nlinarith [Real.sqrt_nonneg ((M + 4) / 8)]
  · exact div_le_div_of_nonneg_right (by linarith) hs.le

/-- the corollary's accuracy statement for the explicit construction -/
lemma eps_construction {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {ε : ℝ} (hε : 0 < ε) :
    AdmNH (nEps M ε) (HEps R M ε) (uniformTree (jvals f (rEps M ε)) (rEps M ε) 0 0) ∧
      supDist f (uniformTree (jvals f (rEps M ε)) (rEps M ε) 0 0) ≤ ENNReal.ofReal ε := by
  have hM := FRM_M_nonneg hf
  obtain ⟨hadm, hsup⟩ := joint_adm hf (rEps_ge M ε) (N := nEps M ε) (H := HEps R M ε) le_rfl
    (by unfold HEps; rw [nEps_cast]; exact Nat.le_ceil _)
  refine ⟨hadm, hsup.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hX := Xeps_le_nEps M ε
  rw [nEps_cast] at hX
  have hsq : (M + 4) / (8 * ε) ≤ Xeps M ε ^ 2 := by
    have : Real.sqrt ((M + 4) / (8 * ε)) ≤ Xeps M ε := le_max_right _ _
    calc (M + 4) / (8 * ε) = Real.sqrt ((M + 4) / (8 * ε)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ _ := by gcongr
  have hX2 : (M + 4) / (8 * ε) ≤ ((2 : ℝ) ^ rEps M ε) ^ 2 :=
    hsq.trans (by gcongr; linarith [Xeps_ge M ε])
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hX2
  nlinarith

lemma bits_eps_aux {Cb : ℕ} {C2 ε : ℝ} (hC2 : 2 ≤ C2) (hε : 0 < ε) (hε1 : ε ≤ 1) {r : ℕ}
    (h2r : (2 : ℝ) ^ r ≤ 2 * C2 / Real.sqrt ε) {Lx : ℕ}
    (hLx : Lx ≤ Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r)) :
    (Lx : ℝ) ≤ (Cb : ℝ) * (2 * C2) * ((2 + Real.log C2 / Real.log 2) / Real.log 2 + 1 / Real.log 2
      + 2 / Real.log 2) / Real.sqrt ε * Real.log (2 / ε) := by
  set L2 := Real.log 2
  have hL2 : 0 < L2 := Real.log_pos (by norm_num)
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hlogC2 : 0 ≤ Real.log C2 := Real.log_nonneg (by linarith)
  have hlog2e : L2 ≤ Real.log (2 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have hlog0 : 0 ≤ Real.log (2 / ε) := hL2.le.trans hlog2e
  have hlog : Nat.log 2 (2 * 2 ^ r) = r + 1 := by rw [← pow_succ', Nat.log_pow (by norm_num)]
  rw [hlog] at hLx
  have hLx' : (Lx : ℝ) ≤ Cb * 2 ^ r * ((r : ℝ) + 1) := by exact_mod_cast hLx
  have hlr : (r : ℝ) * L2 ≤ Real.log (2 * C2 / Real.sqrt ε) := by
    have := Real.log_le_log (by positivity) h2r
    rwa [Real.log_pow] at this
  have hlsq : Real.log (2 * C2 / Real.sqrt ε) = L2 + Real.log C2 + (Real.log (1 / ε)) / 2 := by
    rw [Real.log_div (by positivity) hs.ne', Real.log_mul (by norm_num) (by linarith),
      Real.log_sqrt hε.le, one_div, Real.log_inv]
    ring
  have h1e : Real.log (1 / ε) ≤ Real.log (2 / ε) :=
    Real.log_le_log (by positivity) (by gcongr; norm_num)
  have hr : (r : ℝ) ≤ 1 + Real.log C2 / L2 + Real.log (2 / ε) / (2 * L2) := by
    rw [hlsq] at hlr
    have hlr' : (r : ℝ) ≤ (L2 + Real.log C2 + Real.log (1 / ε) / 2) / L2 := by
      rw [le_div_iff₀ hL2]; exact hlr
    calc (r : ℝ) ≤ (L2 + Real.log C2 + Real.log (1 / ε) / 2) / L2 := hlr'
      _ ≤ (L2 + Real.log C2 + Real.log (2 / ε) / 2) / L2 := by gcongr
      _ = _ := by field_simp
  have h3 : Real.log (2 / ε) / (2 * L2) ≤ (1 / L2 + 2 / L2) * Real.log (2 / ε) := by
    rw [div_le_iff₀ (by positivity)]
    have e : (1 / L2 + 2 / L2) * Real.log (2 / ε) * (2 * L2) = 6 * Real.log (2 / ε) := by
      field_simp; ring
    rw [e]; linarith
  have hA : (2 + Real.log C2 / L2) ≤ ((2 + Real.log C2 / L2) / L2) * Real.log (2 / ε) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL2]
    have : 0 ≤ 2 + Real.log C2 / L2 := by positivity
    nlinarith
  have hr1' : ((r : ℝ) + 1) ≤ ((2 + Real.log C2 / L2) / L2 + 1 / L2 + 2 / L2) * Real.log (2 / ε) := by
    have e : ((2 + Real.log C2 / L2) / L2 + 1 / L2 + 2 / L2) * Real.log (2 / ε) =
        ((2 + Real.log C2 / L2) / L2) * Real.log (2 / ε) + (1 / L2 + 2 / L2) * Real.log (2 / ε) := by
      ring
    rw [e]; linarith
  calc (Lx : ℝ) ≤ Cb * 2 ^ r * ((r : ℝ) + 1) := hLx'
    _ ≤ Cb * (2 * C2 / Real.sqrt ε) *
        (((2 + Real.log C2 / L2) / L2 + 1 / L2 + 2 / L2) * Real.log (2 / ε)) := by
        gcongr
    _ = _ := by ring

/-- **Corollary 3.13 (altura suficiente para precisão prescrita)**.  Uniformly for
`f ∈ 𝓕_{R,M}`: `E_{n_ε,H_ε}(f)_∞ ≤ ε` and `H_{ε,n_ε}(f) ≤ H_ε`; moreover, for `0 < ε ≤ 1`,
`n_ε = O(ε^{-1/2})`, `H_ε = O(ε^{-1})`, and the three code lengths of the certifying assembly
are `O(ε^{-1/2} log(2/ε))`, with constants depending only on `R, M`. -/
theorem height_for_epsilon (R M : ℝ) :
    (∀ f ∈ FRM R M, ∀ ε : ℝ, 0 < ε →
      jointErr (nEps M ε) (HEps R M ε) f ≤ ENNReal.ofReal ε ∧
      heightFor ε (nEps M ε) f ≤ HEps R M ε) ∧
    ∃ C : ℝ, ∀ f ∈ FRM R M, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (nEps M ε : ℝ) ≤ C / Real.sqrt ε ∧ (HEps R M ε : ℝ) ≤ C / ε ∧
      ∃ T : LTree, AdmNH (nEps M ε) (HEps R M ε) T ∧ supDist f T ≤ ENNReal.ofReal ε ∧
        (Latom T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) ∧
        (Lstr T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) ∧
        (Lrat T.leaves : ℝ) ≤ C / Real.sqrt ε * Real.log (2 / ε) := by
  refine ⟨fun f hf ε hε => ?_, ?_⟩
  · obtain ⟨hadm, hsup⟩ := eps_construction hf hε
    have hE := (jointErr_le hadm).trans hsup
    refine ⟨hE, heightFor_le ?_ hE⟩
    have h := hadm.2.2
    have := le_trans (two_le_maxHeight _) h
    exact this
  · obtain ⟨Cb, hCb⟩ := joint_budget R M
    set C2 := 2 + Real.sqrt ((M + 4) / 8)
    set L2 := Real.log 2
    have hL2 : 0 < L2 := Real.log_pos (by norm_num)
    by_cases hFR : ∃ f, f ∈ FRM R M
    swap
    · exact ⟨0, fun f hf => absurd ⟨f, hf⟩ hFR⟩
    obtain ⟨f0, hf0⟩ := hFR
    have hM := FRM_M_nonneg hf0
    have hR := FRM_R_nonneg hf0
    have hCH : 0 ≤ CH R M := le_trans (by linarith) (le_max_left _ _)
    have hC2 : 2 ≤ C2 := by have := Real.sqrt_nonneg ((M + 4) / 8); linarith
    have hlogC2 : 0 ≤ Real.log C2 := Real.log_nonneg (by linarith)
    set Cbits := (Cb : ℝ) * (2 * C2) * ((2 + Real.log C2 / L2) / L2 + 1 / L2 + 2 / L2)
    refine ⟨2 * C2 + (CH R M * (2 * C2) ^ 2 + 1) + Cbits, fun f hf ε hε hε1 => ?_⟩
    have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    have hXle := Xeps_le hM hε hε1
    have hn : (nEps M ε : ℝ) ≤ 2 * C2 / Real.sqrt ε := by
      have := nEps_lt M ε
      rw [mul_div_assoc]; linarith
    have hpos1 : 0 ≤ CH R M * (2 * C2) ^ 2 + 1 := by positivity
    have hCbits : 0 ≤ Cbits := by positivity
    have hlog2e : L2 ≤ Real.log (2 / ε) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
    have hlog0 : 0 ≤ Real.log (2 / ε) := hL2.le.trans hlog2e
    -- height bound
    have hH : (HEps R M ε : ℝ) ≤ (CH R M * (2 * C2) ^ 2 + 1) / ε := by
      unfold HEps
      have h1 := (Nat.ceil_lt_add_one (show 0 ≤ CH R M * ((nEps M ε : ℕ) : ℝ) ^ 2 by positivity)).le
      have h2 : ((nEps M ε : ℕ) : ℝ) ^ 2 ≤ (2 * C2) ^ 2 / ε := by
        have : ((nEps M ε : ℕ) : ℝ) ^ 2 ≤ (2 * C2 / Real.sqrt ε) ^ 2 := by
          gcongr
        rwa [div_pow, Real.sq_sqrt hε.le] at this
      calc _ ≤ CH R M * ((nEps M ε : ℕ) : ℝ) ^ 2 + 1 := h1
        _ ≤ CH R M * ((2 * C2) ^ 2 / ε) + 1 / ε := by
            gcongr; rw [le_div_iff₀ hε]; linarith
        _ = _ := by field_simp
    refine ⟨?_, ?_, ?_⟩
    · calc (nEps M ε : ℝ) ≤ 2 * C2 / Real.sqrt ε := hn
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hs.le
    · calc (HEps R M ε : ℝ) ≤ (CH R M * (2 * C2) ^ 2 + 1) / ε := hH
        _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hε.le
    · obtain ⟨hadm, hsup⟩ := eps_construction hf hε
      refine ⟨_, hadm, hsup, ?_⟩
      obtain ⟨T, hT, -, -, -, -, hLa, hLs, hLr⟩ := hCb (rEps M ε) (rEps_ge M ε) f hf
      rw [← hT]
      have h2r : (2 : ℝ) ^ rEps M ε ≤ 2 * C2 / Real.sqrt ε := by rw [← nEps_cast]; exact hn
      have hmain : ∀ Lx : ℕ, Lx ≤ Cb * 2 ^ rEps M ε * Nat.log 2 (2 * 2 ^ rEps M ε) →
          (Lx : ℝ) ≤ (2 * C2 + (CH R M * (2 * C2) ^ 2 + 1) + Cbits) / Real.sqrt ε * Real.log (2 / ε) := by
        intro Lx hLx
        refine (bits_eps_aux hC2 hε hε1 h2r hLx).trans ?_
        gcongr
        have : 0 ≤ 2 * C2 := by linarith
        linarith
      exact ⟨hmain _ hLa, hmain _ hLs, hmain _ hLr⟩

end Artigo
