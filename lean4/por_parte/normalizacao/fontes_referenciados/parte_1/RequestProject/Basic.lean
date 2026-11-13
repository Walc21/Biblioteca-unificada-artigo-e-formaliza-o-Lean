module
public import Mathlib

/-!
# Seções 1 e 2: base de tipos, racionais, células e átomos

Formalização das Seções 1 (`sec:base`) e 2 (`sec:objects`) do documento
"Equivalência das montagens locais e consolidadas".
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

/-! ## Domínio -/

/-- O conjunto `K = {x : ℝ | α ≤ x ≤ β}`. -/
def K (α β : ℝ) : Set ℝ := Set.Icc α β

/-- O tipo `C_K` das funções contínuas `K → ℝ` (na topologia de subtipo). -/
abbrev CK (α β : ℝ) : Type := C(Set.Icc α β, ℝ)

/-- O intervalo aberto `K° = (α, β)`. -/
def Kint (α β : ℝ) : Set ℝ := Set.Ioo α β

/-- O domínio é não vazio, compacto e igual ao fecho de `K°`. -/
theorem K_props {α β : ℝ} (hK : α < β) :
    (K α β).Nonempty ∧ IsCompact (K α β) ∧ K α β = closure (Kint α β) := by
  refine ⟨⟨α, le_refl α, hK.le⟩, isCompact_Icc, ?_⟩
  simp [K, Kint, closure_Ioo hK.ne]

/-! ## Racional reduzido e altura -/

/-- Altura `ht(r) = max {|p(r)|, q(r)}`. -/
def ht (r : ℚ) : ℕ := max r.num.natAbs r.den

/-- O tipo `ℚ^×` dos racionais não nulos. -/
abbrev Qstar : Type := {r : ℚ // r ≠ 0}

theorem ht_props (r : ℚ) : 1 ≤ ht r ∧ r.num.natAbs ≤ ht r ∧ r.den ≤ ht r := by
  refine ⟨?_, le_max_left _ _, le_max_right _ _⟩
  exact le_trans r.den_pos (le_max_right _ _)

/-! ## Células -/

/-- O tipo de índices de células `Cell = ℕ × ℤ`. -/
abbrev Cell : Type := ℕ × ℤ

/-- Extremo esquerdo racional `m / 2^k`. -/
def LQ (c : Cell) : ℚ := (c.2 : ℚ) / 2 ^ c.1
/-- Extremo direito racional `(m+1) / 2^k`. -/
def RQ (c : Cell) : ℚ := ((c.2 : ℚ) + 1) / 2 ^ c.1
/-- Centro racional `(2m+1) / 2^(k+1)`. -/
def XQ (c : Cell) : ℚ := (2 * (c.2 : ℚ) + 1) / 2 ^ (c.1 + 1)

/-- Versão real do extremo esquerdo. -/
def L (c : Cell) : ℝ := ((LQ c : ℚ) : ℝ)
/-- Versão real do extremo direito. -/
def R (c : Cell) : ℝ := ((RQ c : ℚ) : ℝ)
/-- Versão real do centro. -/
def X (c : Cell) : ℝ := ((XQ c : ℚ) : ℝ)

/-- Suporte fechado `J(c) = [L(c), R(c)]`. -/
def J (c : Cell) : Set ℝ := Set.Icc (L c) (R c)
/-- Interior `O(c) = (L(c), R(c))`. -/
def O (c : Cell) : Set ℝ := Set.Ioo (L c) (R c)
/-- Convenção de posse semiaberta `P(c) = [L(c), R(c))`. -/
def P (c : Cell) : Set ℝ := Set.Ico (L c) (R c)

/-- Os diádicos `𝔻 = {↑(m / 2^k) : (k, m) ∈ Cell}`. -/
def Dy : Set ℝ := {x | ∃ c : Cell, x = (((c.2 : ℚ) / 2 ^ c.1 : ℚ) : ℝ)}

theorem O_eq_interior_J (c : Cell) : O c = interior (J c) := by
  simp [O, J]

/-- Lema `lem:geometry` (geometria elementar). -/
theorem geometry (c : Cell) :
    RQ c - LQ c = ((2 : ℚ) ^ c.1)⁻¹ ∧ 0 < RQ c - LQ c ∧
    XQ c = (LQ c + RQ c) / 2 ∧
    IsClosed (J c) ∧ L c < R c ∧ (O c).Nonempty ∧
    L c < X c ∧ X c < R c ∧
    L c ∈ Dy ∧ R c ∈ Dy ∧ X c ∈ Dy ∧
    (∀ d : Cell, J c = J d → c = d) := by
  obtain ⟨k, m⟩ := c
  have h1 : RQ (k, m) - LQ (k, m) = ((2 : ℚ) ^ k)⁻¹ := by
    simp only [RQ, LQ]; field_simp; ring
  have h2 : XQ (k,m) = (LQ (k,m) + RQ (k,m)) / 2 := by
    simp only [XQ, RQ, LQ]; field_simp; ring
  have hp : (0:ℚ) < ((2 : ℚ) ^ k)⁻¹ := by positivity
  have hLR : LQ (k,m) < RQ (k,m) := by linarith
  have hLX : LQ (k,m) < XQ (k,m) := by rw [h2]; linarith
  have hXR : XQ (k,m) < RQ (k,m) := by rw [h2]; linarith
  refine ⟨h1, by linarith, h2, isClosed_Icc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [L, R]; exact_mod_cast hLR
  · exact Set.nonempty_Ioo.2 (by simp only [L, R]; exact_mod_cast hLR)
  · simp only [L, X]; exact_mod_cast hLX
  · simp only [X, R]; exact_mod_cast hXR
  · exact ⟨(k, m), rfl⟩
  · refine ⟨(k, m+1), ?_⟩; simp [R, RQ]
  · refine ⟨(k+1, 2*m+1), ?_⟩; simp [X, XQ]
  · rintro ⟨k', m'⟩ hJ
    have hLR' : L (k',m') < R (k',m') := by
      simp only [L, R]; exact_mod_cast (show LQ (k',m') < RQ (k',m') by
        have : RQ (k', m') - LQ (k', m') = ((2 : ℚ) ^ k')⁻¹ := by
          simp only [RQ, LQ]; field_simp; ring
        have : (0:ℚ) < ((2 : ℚ) ^ k')⁻¹ := by positivity
        linarith)
    have hLR0 : L (k,m) < R (k,m) := by simp only [L, R]; exact_mod_cast hLR
    obtain ⟨hl, hr⟩ := (Set.Icc_eq_Icc_iff hLR0.le).1 hJ
    simp only [L, R, Rat.cast_inj] at hl hr
    have hw : ((2 : ℚ) ^ k)⁻¹ = ((2 : ℚ) ^ k')⁻¹ := by
      rw [← h1, hl, hr]; simp only [RQ, LQ]; field_simp; ring
    have hk : k = k' := by
      have := inv_injective hw
      exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this)
    subst hk
    simp only [LQ] at hl
    have : (m:ℚ) = m' := by
      have h2k : (2:ℚ)^k ≠ 0 := by positivity
      field_simp at hl; linarith
    simp_all

/-! ## Átomos -/

/-- Um átomo: campos `k : ℕ`, `m : ℤ`, `y : ℚ`, `s : ℚ` e `hs : s ≠ 0`. -/
@[ext]
structure Atom where
  k : ℕ
  m : ℤ
  y : ℚ
  s : ℚ
  hs : s ≠ 0

namespace Atom

/-- A célula `C(a) = (a.k, a.m)`. -/
def C (a : Atom) : Cell := (a.k, a.m)
/-- `J_a = J(C(a))`. -/
def Ja (a : Atom) : Set ℝ := J a.C
/-- `O_a = O(C(a))`. -/
def Oa (a : Atom) : Set ℝ := O a.C
/-- `L_a = L(C(a))`. -/
def La (a : Atom) : ℝ := L a.C
/-- `R_a = R(C(a))`. -/
def Ra (a : Atom) : ℝ := R a.C
/-- `X_a = X(C(a))`. -/
def Xa (a : Atom) : ℝ := X a.C
/-- Inclinação `b(a) = a.s`. -/
def b (a : Atom) : ℚ := a.s
/-- Intercepto `u(a) = a.y - a.s · X_ℚ(C(a))`. -/
def u (a : Atom) : ℚ := a.y - a.s * XQ a.C
/-- A reta `ℓ_a(x) = ↑a.y + ↑a.s (x - X_a)`. -/
def line (a : Atom) (x : ℝ) : ℝ := (a.y : ℝ) + (a.s : ℝ) * (x - a.Xa)
/-- Altura `h(a) = max {2, a.k+1, |a.m|+1, ht(a.y), ht(a.s)}`. -/
def height (a : Atom) : ℕ :=
  max 2 (max (a.k + 1) (max (a.m.natAbs + 1) (max (ht a.y) (ht a.s))))

end Atom

/-- O átomo de valor padrão `a† = (0, 0, 0, 1, 1 ≠ 0)`. -/
def atomDefault : Atom := ⟨0, 0, 0, 1, one_ne_zero⟩

/-- Lema `lem:line` (formas da reta). -/
theorem line_forms (a : Atom) :
    (∀ x : ℝ, a.line x = (a.u : ℝ) + (a.b : ℝ) * x) ∧
    a.line a.Xa = (a.y : ℝ) ∧
    Continuous a.line ∧ (a.b : ℝ) ≠ 0 := by
  refine ⟨fun x => ?_, ?_, ?_, ?_⟩
  · simp only [Atom.line, Atom.u, Atom.b, Atom.Xa, X]; push_cast; ring
  · simp [Atom.line]
  · unfold Atom.line; fun_prop
  · simp [Atom.b, a.hs]

theorem line_eq_of_fields (a a' : Atom) (hC : a.C = a'.C) (hy : a.y = a'.y)
    (hs : a.s = a'.s) : a = a' ∧ a.Ja = a'.Ja ∧ a.line = a'.line := by
  have : a = a' := by
    simp only [Atom.C, Prod.mk.injEq] at hC
    exact Atom.ext hC.1 hC.2 hy hs
  subst this; exact ⟨rfl, rfl, rfl⟩

end Montagens

end
