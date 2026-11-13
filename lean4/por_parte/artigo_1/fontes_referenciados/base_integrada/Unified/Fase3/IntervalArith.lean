module
public import Unified.Fase3.Transcendental
public import Unified.Fase3.Assembly

/-!
# Proposition 6.2: correctness of the interval majorant

A concrete model of the routine `BoundSecondDerivative(E, J; P, d)` of equation (36):

* `Expr` is the class `𝓔` of expressions (variable, rational constants, `+`, `-`, `×`,
  reciprocal, `exp`, `sin`, `cos`); composition is syntactic substitution and therefore needs no
  separate constructor;
* intervals have rational endpoints (`Iv`);
* `exp` is enclosed with argument reduction and the Taylor bound (37), `sin`/`cos` by interval
  evaluation of the Maclaurin polynomial inflated by the Lagrange remainder (38) and intersected
  with `[-1, 1]`; `P` is the Taylor order;
* 2-jets `(E, E', E'')` are propagated with the rules of Section 6.1; a reciprocal whose
  denominator interval contains `0` makes the routine fail (`none`);
* `d` levels of bisection are performed and the results are joined by convex hull.

The main theorem `boundSecondDerivative_correct` proves (39).
-/

@[expose] public section

namespace Fase3

open Finset
open scoped Nat

/-! ## Expressions and their (symbolic) 2-jets -/

/-- The expression class `𝓔`. -/
inductive Expr where
  | var : Expr
  | const : ℚ → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | inv : Expr → Expr
  | exp : Expr → Expr
  | sin : Expr → Expr
  | cos : Expr → Expr

namespace Expr

/-- The function defined by an expression. -/
noncomputable def eval : Expr → ℝ → ℝ
  | var, x => x
  | const q, _ => q
  | add a b, x => eval a x + eval b x
  | sub a b, x => eval a x - eval b x
  | mul a b, x => eval a x * eval b x
  | inv a, x => (eval a x)⁻¹
  | exp a, x => Real.exp (eval a x)
  | sin a, x => Real.sin (eval a x)
  | cos a, x => Real.cos (eval a x)

/-- Admissibility: every reciprocal has a nonzero denominator at `x`. -/
def WD : Expr → ℝ → Prop
  | var, _ => True
  | const _, _ => True
  | add a b, x => WD a x ∧ WD b x
  | sub a b, x => WD a x ∧ WD b x
  | mul a b, x => WD a x ∧ WD b x
  | inv a, x => WD a x ∧ eval a x ≠ 0
  | exp a, x => WD a x
  | sin a, x => WD a x
  | cos a, x => WD a x

/-- First derivative given by the jet rules. -/
noncomputable def eval1 : Expr → ℝ → ℝ
  | var, _ => 1
  | const _, _ => 0
  | add a b, x => eval1 a x + eval1 b x
  | sub a b, x => eval1 a x - eval1 b x
  | mul a b, x => eval1 a x * eval b x + eval a x * eval1 b x
  | inv a, x => -(eval1 a x * ((eval a x)⁻¹ * (eval a x)⁻¹))
  | exp a, x => Real.exp (eval a x) * eval1 a x
  | sin a, x => Real.cos (eval a x) * eval1 a x
  | cos a, x => -(Real.sin (eval a x) * eval1 a x)

/-- Second derivative given by the 2-jet rules of Section 6.1. -/
noncomputable def eval2 : Expr → ℝ → ℝ
  | var, _ => 0
  | const _, _ => 0
  | add a b, x => eval2 a x + eval2 b x
  | sub a b, x => eval2 a x - eval2 b x
  | mul a b, x => eval2 a x * eval b x + 2 * (eval1 a x * eval1 b x) + eval a x * eval2 b x
  | inv a, x => 2 * ((eval1 a x * eval1 a x) * ((eval a x)⁻¹ * ((eval a x)⁻¹ * (eval a x)⁻¹)))
      - eval2 a x * ((eval a x)⁻¹ * (eval a x)⁻¹)
  | exp a, x => Real.exp (eval a x) * (eval1 a x * eval1 a x + eval2 a x)
  | sin a, x => -(Real.sin (eval a x) * (eval1 a x * eval1 a x)) + Real.cos (eval a x) * eval2 a x
  | cos a, x => -(Real.cos (eval a x) * (eval1 a x * eval1 a x)) - Real.sin (eval a x) * eval2 a x

theorem hasDerivAt_eval : ∀ (E : Expr) {x : ℝ}, WD E x →
    HasDerivAt (eval E) (eval1 E x) x ∧ HasDerivAt (eval1 E) (eval2 E x) x
  | var, x, _ => ⟨hasDerivAt_id x, hasDerivAt_const x (1 : ℝ)⟩
  | const q, x, _ => ⟨hasDerivAt_const x _, hasDerivAt_const x (0 : ℝ)⟩
  | add a b, x, h => by
    obtain ⟨a0, a1⟩ := hasDerivAt_eval a h.1
    obtain ⟨b0, b1⟩ := hasDerivAt_eval b h.2
    exact ⟨a0.add b0, a1.add b1⟩
  | sub a b, x, h => by
    obtain ⟨a0, a1⟩ := hasDerivAt_eval a h.1
    obtain ⟨b0, b1⟩ := hasDerivAt_eval b h.2
    exact ⟨a0.sub b0, a1.sub b1⟩
  | mul a b, x, h => by
    obtain ⟨a0, a1⟩ := hasDerivAt_eval a h.1
    obtain ⟨b0, b1⟩ := hasDerivAt_eval b h.2
    refine ⟨a0.mul b0, ?_⟩
    have := (a1.mul b0).add (a0.mul b1)
    convert this using 1
    simp only [eval2]; ring
  | inv a, x, h => by
    obtain ⟨a0, a1⟩ := hasDerivAt_eval a h.1
    have hne := h.2
    have hinv := a0.inv hne
    constructor
    · convert hinv using 1
      simp only [eval1]; field_simp
    · have := (a1.mul (hinv.mul hinv)).neg
      convert this using 1
      simp only [eval2, Pi.mul_apply, Pi.inv_apply]; field_simp; ring
  | exp a, x, h => by
    obtain ⟨a0, a1⟩ := hasDerivAt_eval a h
    have he := (Real.hasDerivAt_exp (eval a x)).comp x a0
    refine ⟨he, ?_⟩
    have := he.mul a1
    convert this using 1
    simp only [eval2, Function.comp_apply]; ring
  | sin a, x, h => by
    obtain ⟨a0, a1⟩ := hasDerivAt_eval a h
    have hs := (Real.hasDerivAt_sin (eval a x)).comp x a0
    have hc := (Real.hasDerivAt_cos (eval a x)).comp x a0
    refine ⟨hs, ?_⟩
    have := hc.mul a1
    convert this using 1
    simp only [eval2, Function.comp_apply]; ring
  | cos a, x, h => by
    obtain ⟨a0, a1⟩ := hasDerivAt_eval a h
    have hs := (Real.hasDerivAt_sin (eval a x)).comp x a0
    have hc := (Real.hasDerivAt_cos (eval a x)).comp x a0
    refine ⟨by convert hc using 1; simp only [eval1]; ring, ?_⟩
    have := (hs.mul a1).neg
    convert this using 1
    simp only [eval2, Function.comp_apply]; ring

theorem isOpen_WD : ∀ E : Expr, IsOpen {x | WD E x}
  | var => by simp [WD]
  | const _ => by simp [WD]
  | add a b => by simpa [WD, Set.setOf_and] using (isOpen_WD a).inter (isOpen_WD b)
  | sub a b => by simpa [WD, Set.setOf_and] using (isOpen_WD a).inter (isOpen_WD b)
  | mul a b => by simpa [WD, Set.setOf_and] using (isOpen_WD a).inter (isOpen_WD b)
  | inv a => by
    have hc : ContinuousOn (eval a) {x | WD a x} :=
      fun x hx => (hasDerivAt_eval a hx).1.continuousAt.continuousWithinAt
    have := hc.isOpen_inter_preimage (isOpen_WD a) (isOpen_compl_singleton (x := (0 : ℝ)))
    simpa [WD, Set.setOf_and] using this
  | exp a => by simpa [WD] using isOpen_WD a
  | sin a => by simpa [WD] using isOpen_WD a
  | cos a => by simpa [WD] using isOpen_WD a

theorem contDiffAt_eval : ∀ (E : Expr) {x : ℝ}, WD E x → ContDiffAt ℝ 2 (eval E) x
  | var, _, _ => contDiffAt_id
  | const _, _, _ => contDiffAt_const
  | add a b, _, h => (contDiffAt_eval a h.1).add (contDiffAt_eval b h.2)
  | sub a b, _, h => (contDiffAt_eval a h.1).sub (contDiffAt_eval b h.2)
  | mul a b, _, h => (contDiffAt_eval a h.1).mul (contDiffAt_eval b h.2)
  | inv a, _, h => (contDiffAt_eval a h.1).inv h.2
  | exp a, x, h => Real.contDiff_exp.contDiffAt.comp x (contDiffAt_eval a h)
  | sin a, x, h => Real.contDiff_sin.contDiffAt.comp x (contDiffAt_eval a h)
  | cos a, x, h => Real.contDiff_cos.contDiffAt.comp x (contDiffAt_eval a h)

/-- At an admissible point, `E''` is the second derivative of the function defined by `E`. -/
theorem deriv2_eval (E : Expr) {x : ℝ} (hx : WD E x) :
    deriv (deriv (eval E)) x = eval2 E x := by
  have hev : ∀ᶠ y in nhds x, WD E y := (isOpen_WD E).mem_nhds hx
  have h : deriv (eval E) =ᶠ[nhds x] eval1 E := hev.mono fun y hy => (hasDerivAt_eval E hy).1.deriv
  rw [h.deriv_eq]
  exact (hasDerivAt_eval E hx).2.deriv

end Expr

/-! ## Rational intervals -/

/-- A closed interval with rational endpoints. -/
structure Iv where
  lo : ℚ
  hi : ℚ

namespace Iv

/-- Membership of a real number. -/
def Mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def point (q : ℚ) : Iv := ⟨q, q⟩
def add (A B : Iv) : Iv := ⟨A.lo + B.lo, A.hi + B.hi⟩
def neg (A : Iv) : Iv := ⟨-A.hi, -A.lo⟩
def sub (A B : Iv) : Iv := add A (neg B)
def mul (A B : Iv) : Iv :=
  ⟨min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)),
   max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))⟩
/-- Reciprocal; fails when the interval contains `0`. -/
def inv (A : Iv) : Option Iv := if 0 < A.lo ∨ A.hi < 0 then some ⟨1 / A.hi, 1 / A.lo⟩ else none
/-- Convex hull. -/
def hull (A B : Iv) : Iv := ⟨min A.lo B.lo, max A.hi B.hi⟩
/-- Left half. -/
def leftHalf (A : Iv) : Iv := ⟨A.lo, (A.lo + A.hi) / 2⟩
/-- Right half. -/
def rightHalf (A : Iv) : Iv := ⟨(A.lo + A.hi) / 2, A.hi⟩
/-- `max(|lo|, |hi|)`. -/
def mag (A : Iv) : ℚ := max |A.lo| |A.hi|

lemma point_mem (q : ℚ) : (point q).Mem q := ⟨le_rfl, le_rfl⟩

lemma add_mem {A B : Iv} {x y : ℝ} (hx : A.Mem x) (hy : B.Mem y) : (add A B).Mem (x + y) := by
  unfold Mem add at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma neg_mem {A : Iv} {x : ℝ} (hx : A.Mem x) : (neg A).Mem (-x) := by
  unfold Mem neg at *; push_cast; constructor <;> linarith [hx.1, hx.2]

lemma sub_mem {A B : Iv} {x y : ℝ} (hx : A.Mem x) (hy : B.Mem y) : (sub A B).Mem (x - y) := by
  rw [sub_eq_add_neg]; exact add_mem hx (neg_mem hy)

lemma lin_bounds {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right h1 hy),
      le_trans (mul_le_mul_of_nonneg_right h2 hy) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right h2 hy),
      le_trans (mul_le_mul_of_nonpos_right h1 hy) (le_max_left _ _)⟩

lemma lin_bounds' {a b y c : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) :
    min (c * a) (c * b) ≤ c * y ∧ c * y ≤ max (c * a) (c * b) := by
  have := lin_bounds (y := c) h1 h2
  simpa only [mul_comm c] using this

lemma mul_mem {A B : Iv} {x y : ℝ} (hx : A.Mem x) (hy : B.Mem y) : (mul A B).Mem (x * y) := by
  unfold Mem mul at *
  push_cast
  obtain ⟨h1, h2⟩ := lin_bounds (y := y) hx.1 hx.2
  have ha := lin_bounds' (c := (A.lo : ℝ)) hy.1 hy.2
  have hb := lin_bounds' (c := (A.hi : ℝ)) hy.1 hy.2
  constructor
  · refine le_trans ?_ h1
    rcases min_choice ((A.lo : ℝ) * y) (A.hi * y) with h | h <;> rw [h]
    · exact le_trans (min_le_left _ _) ha.1
    · exact le_trans (min_le_right _ _) hb.1
  · refine le_trans h2 ?_
    rcases max_choice ((A.lo : ℝ) * y) (A.hi * y) with h | h <;> rw [h]
    · exact le_trans ha.2 (le_max_left _ _)
    · exact le_trans hb.2 (le_max_right _ _)

lemma inv_mem {A V : Iv} (h : inv A = some V) {x : ℝ} (hx : A.Mem x) :
    x ≠ 0 ∧ V.Mem x⁻¹ := by
  unfold inv at h
  split_ifs at h with hc
  · simp only [Option.some.injEq] at h
    subst h
    unfold Mem at *
    push_cast
    rcases hc with hc | hc
    · have hlo : (0 : ℝ) < A.lo := by exact_mod_cast hc
      have hx0 : 0 < x := lt_of_lt_of_le hlo hx.1
      refine ⟨hx0.ne', ?_, ?_⟩
      · rw [← one_div]; exact one_div_le_one_div_of_le hx0 hx.2
      · rw [← one_div]; exact one_div_le_one_div_of_le hlo hx.1
    · have hhi : (A.hi : ℝ) < 0 := by exact_mod_cast hc
      have hx0 : x < 0 := lt_of_le_of_lt hx.2 hhi
      refine ⟨hx0.ne, ?_, ?_⟩
      · rw [← one_div]; exact one_div_le_one_div_of_neg_of_le hhi hx.2
      · rw [← one_div]; exact one_div_le_one_div_of_neg_of_le hx0 hx.1

/-- The reciprocal fails exactly when the denominator interval contains `0`. -/
theorem inv_eq_none_iff (A : Iv) : inv A = none ↔ A.lo ≤ 0 ∧ 0 ≤ A.hi := by
  unfold inv
  split_ifs with h
  · simp only [false_iff, not_and, not_le]
    intro h1; rcases h with h | h <;> [exact absurd h (not_lt.2 h1); exact h]
  · push_neg at h; simp [h]

lemma hull_mem_left {A B : Iv} {x : ℝ} (hx : A.Mem x) : (hull A B).Mem x := by
  unfold Mem hull at *; push_cast
  exact ⟨le_trans (min_le_left _ _) hx.1, le_trans hx.2 (le_max_left _ _)⟩

lemma hull_mem_right {A B : Iv} {x : ℝ} (hx : B.Mem x) : (hull A B).Mem x := by
  unfold Mem hull at *; push_cast
  exact ⟨le_trans (min_le_right _ _) hx.1, le_trans hx.2 (le_max_right _ _)⟩

lemma mem_halves {A : Iv} {x : ℝ} (hx : A.Mem x) : (leftHalf A).Mem x ∨ (rightHalf A).Mem x := by
  unfold Mem leftHalf rightHalf at *
  push_cast
  rcases le_total x (((A.lo : ℝ) + A.hi) / 2) with h | h
  · exact Or.inl ⟨hx.1, h⟩
  · exact Or.inr ⟨h, hx.2⟩

lemma abs_le_mag {A : Iv} {x : ℝ} (hx : A.Mem x) : |x| ≤ (mag A : ℝ) := by
  unfold Mem mag at *
  push_cast
  rw [abs_le]; constructor
  · have := neg_abs_le (A.lo : ℝ); have := le_max_left |(A.lo : ℝ)| |(A.hi : ℝ)|; linarith [hx.1]
  · have := le_abs_self (A.hi : ℝ); have := le_max_right |(A.lo : ℝ)| |(A.hi : ℝ)|; linarith [hx.2]

/-- Integer powers of an interval by repeated multiplication. -/
def pow (A : Iv) : ℕ → Iv
  | 0 => point 1
  | k + 1 => mul (pow A k) A

lemma pow_mem {A : Iv} {x : ℝ} (hx : A.Mem x) (k : ℕ) : (pow A k).Mem (x ^ k) := by
  induction k with
  | zero => simpa [pow] using point_mem 1
  | succ k ih => rw [pow_succ]; exact mul_mem ih hx

end Iv

/-! ## Rational enclosures of `exp`, `sin`, `cos` (Lemma 6.1 as routines) -/

/-- Rational Taylor sum `∑_{j≤P} z^j/j!`. -/
def expTaylorQ (P : ℕ) (z : ℚ) : ℚ := ∑ j ∈ range (P + 1), z ^ j / (j ! : ℚ)

/-- Rational geometric remainder of (37). -/
def expRemQ (P : ℕ) (z : ℚ) : ℚ := z ^ (P + 1) / ((P + 1)! : ℚ) * (1 / (1 - z / (P + 2)))

/-- Argument reduction exponent `r` with `|x| / 2^r ≤ 1/2`. -/
def redExp (x : ℚ) : ℕ := ⌈2 * |x|⌉.toNat

/-- Rational lower bound for `e^x`. -/
def expLoQ (P : ℕ) (x : ℚ) : ℚ :=
  if 0 ≤ x then expTaylorQ P (|x| / 2 ^ redExp x) ^ (2 ^ redExp x)
  else 1 / (expTaylorQ P (|x| / 2 ^ redExp x) + expRemQ P (|x| / 2 ^ redExp x)) ^ (2 ^ redExp x)

/-- Rational upper bound for `e^x`. -/
def expHiQ (P : ℕ) (x : ℚ) : ℚ :=
  if 0 ≤ x then (expTaylorQ P (|x| / 2 ^ redExp x) + expRemQ P (|x| / 2 ^ redExp x)) ^ (2 ^ redExp x)
  else 1 / expTaylorQ P (|x| / 2 ^ redExp x) ^ (2 ^ redExp x)

lemma expTaylorQ_cast (P : ℕ) (z : ℚ) : ((expTaylorQ P z : ℚ) : ℝ) = expPoly P z := by
  unfold expTaylorQ expPoly; push_cast; rfl

lemma expRemQ_cast (P : ℕ) (z : ℚ) : ((expRemQ P z : ℚ) : ℝ) =
    (z : ℝ) ^ (P + 1) / ((P + 1)! : ℝ) * (1 / (1 - (z : ℝ) / (P + 2))) := by
  unfold expRemQ; push_cast; ring

lemma one_le_expPoly (P : ℕ) {z : ℝ} (hz : 0 ≤ z) : 1 ≤ expPoly P z := by
  unfold expPoly
  have := Finset.single_le_sum (f := fun j => z ^ j / (j ! : ℝ)) (fun j _ => by positivity)
    (Finset.mem_range.2 (Nat.succ_pos P))
  simpa using this

/-- Soundness of the rational exponential enclosure. -/
theorem expQ_sound (P : ℕ) (x : ℚ) :
    ((expLoQ P x : ℚ) : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ ((expHiQ P x : ℚ) : ℝ) := by
  unfold expLoQ expHiQ
  set r := redExp x with hrdef
  set zq : ℚ := |x| / 2 ^ r with hzq
  have hz : (zq : ℝ) = |(x : ℝ)| / 2 ^ r := by simp [zq]
  have hr : 2 * |(x : ℝ)| ≤ 2 ^ r := by
    have h1 : (2 * |x| : ℚ) ≤ (r : ℚ) := by
      have := Int.le_ceil (2 * |x|)
      have h2 : (⌈2 * |x|⌉ : ℚ) ≤ ((⌈2 * |x|⌉.toNat : ℤ) : ℚ) := by exact_mod_cast Int.self_le_toNat _
      rw [hrdef, redExp]
      push_cast at h2 ⊢; linarith
    have h3 : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self).le
    have : (2 * |(x : ℝ)| : ℝ) ≤ (r : ℝ) := by exact_mod_cast h1
    linarith
  have hz0 : 0 ≤ (zq : ℝ) := by rw [hz]; positivity
  have hz1 : (zq : ℝ) ≤ 1 / 2 := by
    rw [hz, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨b1, b2⟩ := exp_sub_expPoly_bounds hz0 hz1 P
  have hT1 : 1 ≤ expPoly P zq := one_le_expPoly P hz0
  have hred : Real.exp |(x : ℝ)| = Real.exp zq ^ (2 ^ r) := by
    rw [hz]; exact exp_reduction _ r
  have hlo : expPoly P zq ^ (2 ^ r) ≤ Real.exp |(x : ℝ)| := by
    rw [hred]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hhi : Real.exp |(x : ℝ)| ≤ (expPoly P zq + (zq : ℝ) ^ (P + 1) / ((P + 1)! : ℝ) *
      (1 / (1 - (zq : ℝ) / (P + 2)))) ^ (2 ^ r) := by
    rw [hred]; exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) _
  have hTpos : 0 < expPoly P zq ^ (2 ^ r) := by positivity
  split_ifs with hx
  · have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
    rw [abs_of_nonneg hx'] at hlo hhi
    push_cast [expTaylorQ_cast, expRemQ_cast]
    exact ⟨hlo, hhi⟩
  · have hx' : (x : ℝ) < 0 := by exact_mod_cast (not_le.1 hx)
    rw [abs_of_neg hx'] at hlo hhi
    have he : Real.exp (x : ℝ) = 1 / Real.exp (-(x : ℝ)) := exp_neg_reciprocal _
    push_cast [expTaylorQ_cast, expRemQ_cast]
    rw [he]
    have hpos := Real.exp_pos (-(x : ℝ))
    exact ⟨one_div_le_one_div_of_le hpos hhi, one_div_le_one_div_of_le hTpos hlo⟩

namespace Iv

/-- Interval enclosure of `exp` (monotone: lower bound at `lo`, upper bound at `hi`). -/
def expEncl (P : ℕ) (A : Iv) : Iv := ⟨expLoQ P A.lo, expHiQ P A.hi⟩

lemma expEncl_mem (P : ℕ) {A : Iv} {x : ℝ} (hx : A.Mem x) : (expEncl P A).Mem (Real.exp x) :=
  ⟨le_trans (expQ_sound P A.lo).1 (Real.exp_le_exp.2 hx.1),
    le_trans (Real.exp_le_exp.2 hx.2) (expQ_sound P A.hi).2⟩

/-- Interval evaluation of `P_n^{sin}`. -/
def sinPolyIv (A : Iv) : ℕ → Iv
  | 0 => mul (point 1) (pow A 1)
  | n + 1 => add (sinPolyIv A n)
      (mul (point ((-1) ^ (n + 1) / ((2 * (n + 1) + 1)! : ℚ))) (pow A (2 * (n + 1) + 1)))

/-- Interval evaluation of `P_n^{cos}`. -/
def cosPolyIv (A : Iv) : ℕ → Iv
  | 0 => point 1
  | n + 1 => add (cosPolyIv A n)
      (mul (point ((-1) ^ (n + 1) / ((2 * (n + 1))! : ℚ))) (pow A (2 * (n + 1))))

lemma sinPolyIv_mem {A : Iv} {x : ℝ} (hx : A.Mem x) (n : ℕ) : (sinPolyIv A n).Mem (sinPoly n x) := by
  induction n with
  | zero =>
    have := mul_mem (point_mem 1) (pow_mem hx 1)
    simpa [sinPolyIv, sinPoly] using this
  | succ n ih =>
    have := add_mem ih (mul_mem (point_mem ((-1) ^ (n + 1) / ((2 * (n + 1) + 1)! : ℚ)))
      (pow_mem hx (2 * (n + 1) + 1)))
    have e : sinPoly (n + 1) x = sinPoly n x +
        (((-1) ^ (n + 1) / ((2 * (n + 1) + 1)! : ℚ) : ℚ) : ℝ) * x ^ (2 * (n + 1) + 1) := by
      unfold sinPoly; rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]; exact this

lemma cosPolyIv_mem {A : Iv} {x : ℝ} (hx : A.Mem x) (n : ℕ) : (cosPolyIv A n).Mem (cosPoly n x) := by
  induction n with
  | zero => simpa [cosPolyIv, cosPoly] using point_mem 1
  | succ n ih =>
    have := add_mem ih (mul_mem (point_mem ((-1) ^ (n + 1) / ((2 * (n + 1))! : ℚ)))
      (pow_mem hx (2 * (n + 1))))
    have e : cosPoly (n + 1) x = cosPoly n x +
        (((-1) ^ (n + 1) / ((2 * (n + 1))! : ℚ) : ℚ) : ℝ) * x ^ (2 * (n + 1)) := by
      unfold cosPoly; rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]; exact this

/-- Enclosure of `sin`: polynomial, inflated by the remainder, intersected with `[-1,1]`. -/
def sinEncl (P : ℕ) (A : Iv) : Iv :=
  ⟨max (-1) ((sinPolyIv A P).lo - mag A ^ (2 * P + 2) / ((2 * P + 2)! : ℚ)),
   min 1 ((sinPolyIv A P).hi + mag A ^ (2 * P + 2) / ((2 * P + 2)! : ℚ))⟩

/-- Enclosure of `cos`. -/
def cosEncl (P : ℕ) (A : Iv) : Iv :=
  ⟨max (-1) ((cosPolyIv A P).lo - mag A ^ (2 * P + 1) / ((2 * P + 1)! : ℚ)),
   min 1 ((cosPolyIv A P).hi + mag A ^ (2 * P + 1) / ((2 * P + 1)! : ℚ))⟩

lemma sinEncl_mem (P : ℕ) {A : Iv} {x : ℝ} (hx : A.Mem x) : (sinEncl P A).Mem (Real.sin x) := by
  have h := sin_mem_inflated P (a := A.lo) (b := A.hi) hx (sinPolyIv_mem hx P)
  unfold Mem sinEncl mag
  push_cast
  exact h

lemma cosEncl_mem (P : ℕ) {A : Iv} {x : ℝ} (hx : A.Mem x) : (cosEncl P A).Mem (Real.cos x) := by
  have h := cos_mem_inflated P (a := A.lo) (b := A.hi) hx (cosPolyIv_mem hx P)
  unfold Mem cosEncl mag
  push_cast
  exact h

end Iv

/-! ## Propagation of interval 2-jets -/

/-- An interval 2-jet: enclosures of `(E, E', E'')`. -/
structure IvJet where
  v : Iv
  d1 : Iv
  d2 : Iv

open Iv in
/-- Interval 2-jet propagation on an input interval `X`, with transcendental precision `P`. -/
def ivJet (P : ℕ) : Expr → Iv → Option IvJet
  | .var, X => some ⟨X, point 1, point 0⟩
  | .const q, _ => some ⟨point q, point 0, point 0⟩
  | .add a b, X => do
      let A ← ivJet P a X
      let B ← ivJet P b X
      pure ⟨add A.v B.v, add A.d1 B.d1, add A.d2 B.d2⟩
  | .sub a b, X => do
      let A ← ivJet P a X
      let B ← ivJet P b X
      pure ⟨sub A.v B.v, sub A.d1 B.d1, sub A.d2 B.d2⟩
  | .mul a b, X => do
      let A ← ivJet P a X
      let B ← ivJet P b X
      pure ⟨mul A.v B.v, add (mul A.d1 B.v) (mul A.v B.d1),
        add (add (mul A.d2 B.v) (mul (point 2) (mul A.d1 B.d1))) (mul A.v B.d2)⟩
  | .inv a, X => do
      let A ← ivJet P a X
      let V ← Iv.inv A.v
      pure ⟨V, neg (mul A.d1 (mul V V)),
        sub (mul (point 2) (mul (mul A.d1 A.d1) (mul V (mul V V)))) (mul A.d2 (mul V V))⟩
  | .exp a, X => do
      let A ← ivJet P a X
      let E := expEncl P A.v
      pure ⟨E, mul E A.d1, mul E (add (mul A.d1 A.d1) A.d2)⟩
  | .sin a, X => do
      let A ← ivJet P a X
      let S := sinEncl P A.v
      let C := cosEncl P A.v
      pure ⟨S, mul C A.d1, add (neg (mul S (mul A.d1 A.d1))) (mul C A.d2)⟩
  | .cos a, X => do
      let A ← ivJet P a X
      let S := sinEncl P A.v
      let C := cosEncl P A.v
      pure ⟨C, neg (mul S A.d1), sub (neg (mul C (mul A.d1 A.d1))) (mul S A.d2)⟩

open Iv in
theorem ivJet_sound (P : ℕ) : ∀ (E : Expr) (X : Iv) (J : IvJet), ivJet P E X = some J →
    ∀ x : ℝ, X.Mem x → E.WD x ∧ J.v.Mem (E.eval x) ∧ J.d1.Mem (E.eval1 x) ∧ J.d2.Mem (E.eval2 x)
  | .var, X, J, h, x, hx => by
    simp only [ivJet, Option.some.injEq] at h; subst h
    refine ⟨trivial, hx, ?_, ?_⟩
    · simpa [Expr.eval1] using point_mem 1
    · simpa [Expr.eval2] using point_mem 0
  | .const q, X, J, h, x, hx => by
    simp only [ivJet, Option.some.injEq] at h; subst h
    refine ⟨trivial, point_mem q, ?_, ?_⟩
    · simpa [Expr.eval1] using point_mem 0
    · simpa [Expr.eval2] using point_mem 0
  | .add a b, X, J, h, x, hx => by
    simp only [ivJet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    obtain ⟨wa, a0, a1, a2⟩ := ivJet_sound P a X A hA x hx
    obtain ⟨wb, b0, b1, b2⟩ := ivJet_sound P b X B hB x hx
    exact ⟨⟨wa, wb⟩, add_mem a0 b0, add_mem a1 b1, add_mem a2 b2⟩
  | .sub a b, X, J, h, x, hx => by
    simp only [ivJet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    obtain ⟨wa, a0, a1, a2⟩ := ivJet_sound P a X A hA x hx
    obtain ⟨wb, b0, b1, b2⟩ := ivJet_sound P b X B hB x hx
    exact ⟨⟨wa, wb⟩, sub_mem a0 b0, sub_mem a1 b1, sub_mem a2 b2⟩
  | .mul a b, X, J, h, x, hx => by
    simp only [ivJet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    obtain ⟨wa, a0, a1, a2⟩ := ivJet_sound P a X A hA x hx
    obtain ⟨wb, b0, b1, b2⟩ := ivJet_sound P b X B hB x hx
    refine ⟨⟨wa, wb⟩, mul_mem a0 b0, add_mem (mul_mem a1 b0) (mul_mem a0 b1), ?_⟩
    have := add_mem (add_mem (mul_mem a2 b0) (mul_mem (point_mem 2) (mul_mem a1 b1))) (mul_mem a0 b2)
    simpa [Expr.eval2] using this
  | .inv a, X, J, h, x, hx => by
    simp only [ivJet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A, hA, V, hV, rfl⟩ := h
    obtain ⟨wa, a0, a1, a2⟩ := ivJet_sound P a X A hA x hx
    obtain ⟨hne, hv⟩ := inv_mem hV a0
    refine ⟨⟨wa, hne⟩, hv, neg_mem (mul_mem a1 (mul_mem hv hv)), ?_⟩
    have := sub_mem (mul_mem (point_mem 2) (mul_mem (mul_mem a1 a1) (mul_mem hv (mul_mem hv hv))))
      (mul_mem a2 (mul_mem hv hv))
    simpa [Expr.eval2] using this
  | .exp a, X, J, h, x, hx => by
    simp only [ivJet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A, hA, rfl⟩ := h
    obtain ⟨wa, a0, a1, a2⟩ := ivJet_sound P a X A hA x hx
    have he := expEncl_mem P a0
    exact ⟨wa, he, mul_mem he a1, mul_mem he (add_mem (mul_mem a1 a1) a2)⟩
  | .sin a, X, J, h, x, hx => by
    simp only [ivJet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A, hA, rfl⟩ := h
    obtain ⟨wa, a0, a1, a2⟩ := ivJet_sound P a X A hA x hx
    have hs := sinEncl_mem P a0
    have hc := cosEncl_mem P a0
    exact ⟨wa, hs, mul_mem hc a1, add_mem (neg_mem (mul_mem hs (mul_mem a1 a1))) (mul_mem hc a2)⟩
  | .cos a, X, J, h, x, hx => by
    simp only [ivJet, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨A, hA, rfl⟩ := h
    obtain ⟨wa, a0, a1, a2⟩ := ivJet_sound P a X A hA x hx
    have hs := sinEncl_mem P a0
    have hc := cosEncl_mem P a0
    exact ⟨wa, hc, neg_mem (mul_mem hs a1), sub_mem (neg_mem (mul_mem hc (mul_mem a1 a1))) (mul_mem hs a2)⟩

/-! ## The routine `BoundSecondDerivative` and Proposition 6.2 -/

/-- `d` levels of bisection; the `E''` enclosures of the pieces are joined by convex hull. -/
def bsdAux (P : ℕ) (E : Expr) : ℕ → Iv → Option Iv
  | 0, X => (ivJet P E X).map IvJet.d2
  | d + 1, X =>
    match bsdAux P E d X.leftHalf, bsdAux P E d X.rightHalf with
    | some l, some r => some (Iv.hull l r)
    | _, _ => none

/-- The routine `BoundSecondDerivative(E, J; P, d) = [m_J, M_J]` of equation (36);
`none` signals failure. -/
def boundSecondDerivative (E : Expr) (J : Iv) (P d : ℕ) : Option Iv := bsdAux P E d J

/-- `M_int(J) = max(|m_J|, |M_J|)`. -/
def Mint (I : Iv) : ℚ := Iv.mag I

lemma bsdAux_sound (P : ℕ) (E : Expr) : ∀ (d : ℕ) (X I : Iv), bsdAux P E d X = some I →
    ∀ x : ℝ, X.Mem x → E.WD x ∧ I.Mem (E.eval2 x)
  | 0, X, I, h, x, hx => by
    simp only [bsdAux, Option.map_eq_some_iff] at h
    obtain ⟨J, hJ, rfl⟩ := h
    obtain ⟨w, -, -, h2⟩ := ivJet_sound P E X J hJ x hx
    exact ⟨w, h2⟩
  | d + 1, X, I, h, x, hx => by
    simp only [bsdAux] at h
    split at h
    · rename_i l r hl hr
      simp only [Option.some.injEq] at h
      subst h
      rcases Iv.mem_halves hx with h' | h'
      · obtain ⟨w, hm⟩ := bsdAux_sound P E d _ l hl x h'
        exact ⟨w, Iv.hull_mem_left hm⟩
      · obtain ⟨w, hm⟩ := bsdAux_sound P E d _ r hr x h'
        exact ⟨w, Iv.hull_mem_right hm⟩
    · simp at h

/-- **Proposition 6.2 (correctness of the interval majorant).** If
`BoundSecondDerivative(E, J; P, d)` succeeds with `[m_J, M_J]`, then for every `x ∈ J` the
function defined by `E` is `C²` near `x` (so the hypothesis "E defines a C² function on J" is
automatically satisfied), `E''(x) ∈ [m_J, M_J]` and `|E''(x)| ≤ M_int(J)` (equation (39)). -/
theorem boundSecondDerivative_correct (E : Expr) (J : Iv) (P d : ℕ) (I : Iv)
    (h : boundSecondDerivative E J P d = some I) (x : ℝ) (hx : J.Mem x) :
    ContDiffAt ℝ 2 E.eval x ∧
      deriv (deriv E.eval) x ∈ Set.Icc (I.lo : ℝ) I.hi ∧
      |deriv (deriv E.eval) x| ≤ (Mint I : ℝ) := by
  obtain ⟨w, hm⟩ := bsdAux_sound P E d J I h x hx
  rw [Expr.deriv2_eval E w]
  exact ⟨Expr.contDiffAt_eval E w, hm, Iv.abs_le_mag hm⟩

/-- **Proposition 6.2, equation (39) in norm form:** `M_int(J) ≥ ‖E''‖_{∞,J}`. -/
theorem Mint_ge_supNorm (E : Expr) (J : Iv) (P d : ℕ) (I : Iv)
    (h : boundSecondDerivative E J P d = some I) (hJ : J.lo ≤ J.hi) :
    supNormOn (Set.Icc (J.lo : ℝ) J.hi) (deriv (deriv E.eval)) ≤ (Mint I : ℝ) :=
  supNormOn_le ⟨J.lo, le_rfl, by exact_mod_cast hJ⟩
    fun x hx => (boundSecondDerivative_correct E J P d I h x hx).2.2

/-- **Proposition 6.2, failure rule.** A reciprocal whose denominator interval contains `0`
makes the propagation fail, so no certificate is produced. -/
theorem ivJet_inv_fail (P : ℕ) (a : Expr) (X : Iv) (A : IvJet) (hA : ivJet P a X = some A)
    (h0 : A.v.lo ≤ 0 ∧ 0 ≤ A.v.hi) : ivJet P (.inv a) X = none := by
  have : Iv.inv A.v = none := (Iv.inv_eq_none_iff A.v).2 h0
  simp [ivJet, hA, this]

end Fase3
