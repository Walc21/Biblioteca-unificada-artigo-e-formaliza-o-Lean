module

public import Unified.Fase3.IntervalArith

/-!
# Proposição 6.2, regra de falha

O texto (Proposição 6.2) afirma: se algum intervalo de denominador contém zero, mesmo após a
subdivisão permitida, a rotina `BoundSecondDerivative` devolve falha e nenhum certificado é
aceito. Aqui `boundSecondDerivative E J P d = none` é caracterizada exatamente:

`boundSecondDerivative E J P d = none` ⇔ existe um pedaço `Y` obtido de `J` por `d` bissecções
e uma subexpressão `inv a` de `E` cujo argumento tem intervalo `A.v` contendo `0` em `Y`.
-/

namespace Fase3

open Iv

/-- `InvArg a E`: `inv a` ocorre como nó de `E` (com argumento `a`). -/
public def InvArg (a : Expr) : Expr → Prop
  | .var => False
  | .const _ => False
  | .add x y => InvArg a x ∨ InvArg a y
  | .sub x y => InvArg a x ∨ InvArg a y
  | .mul x y => InvArg a x ∨ InvArg a y
  | .inv b => b = a ∨ InvArg a b
  | .exp x => InvArg a x
  | .sin x => InvArg a x
  | .cos x => InvArg a x

/-- `Piece d X Y`: `Y` é um dos `2^d` pedaços de `X` após `d` bissecções. -/
public def Piece : ℕ → Iv → Iv → Prop
  | 0, X, Y => Y = X
  | d + 1, X, Y => Piece d X.leftHalf Y ∨ Piece d X.rightHalf Y

/-- Testemunha de falha de `ivJet`: se a propagação falha, algum denominador encerra `0`. -/
public lemma ivJet_none_witness (P : ℕ) (E : Expr) (X : Iv) (h : ivJet P E X = none) :
    ∃ a A, InvArg a E ∧ ivJet P a X = some A ∧ A.v.lo ≤ 0 ∧ 0 ≤ A.v.hi := by
  induction E generalizing X with
  | var => simp [ivJet] at h
  | const q => simp [ivJet] at h
  | add x y ihx ihy | sub x y ihx ihy | mul x y ihx ihy =>
    -- o nó falha se algum dos filhos falha
    rcases hx : ivJet P x X with _ | A
    · obtain ⟨a, A, h1, h2, h3, h4⟩ := ihx X hx
      exact ⟨a, A, by simp [InvArg, h1], h2, h3, h4⟩
    · rcases hy : ivJet P y X with _ | B
      · obtain ⟨a, B', h1, h2, h3, h4⟩ := ihy X hy
        exact ⟨a, B', by simp [InvArg, h1], h2, h3, h4⟩
      · simp [ivJet, hx, hy] at h
  | inv b ih =>
    rcases hb : ivJet P b X with _ | A
    · obtain ⟨a, A', h1, h2, h3, h4⟩ := ih X hb
      exact ⟨a, A', by simp [InvArg, h1], h2, h3, h4⟩
    · -- o argumento está definido; a falha é do próprio `inv`
      have h' : Iv.inv A.v = none := by
        rcases hi : Iv.inv A.v with _ | V
        · rfl
        · simp [ivJet, hb, hi] at h
      have hz : A.v.lo ≤ 0 ∧ 0 ≤ A.v.hi := (Iv.inv_eq_none_iff A.v).1 h'
      exact ⟨b, A, by simp [InvArg], hb, hz⟩
  | exp x ih =>
    rcases hx : ivJet P x X with _ | A
    · obtain ⟨a, A', h1, h2, h3, h4⟩ := ih X hx
      exact ⟨a, A', h1, h2, h3, h4⟩
    · simp [ivJet, hx] at h
  | sin x ih =>
    rcases hx : ivJet P x X with _ | A
    · obtain ⟨a, A', h1, h2, h3, h4⟩ := ih X hx
      exact ⟨a, A', h1, h2, h3, h4⟩
    · simp [ivJet, hx] at h
  | cos x ih =>
    rcases hx : ivJet P x X with _ | A
    · obtain ⟨a, A', h1, h2, h3, h4⟩ := ih X hx
      exact ⟨a, A', h1, h2, h3, h4⟩
    · simp [ivJet, hx] at h

/-- Recíproca: um denominador que contém `0` faz a propagação de `E` falhar. -/
public lemma ivJet_of_bad (P : ℕ) (a : Expr) (E : Expr) (X : Iv) (A : IvJet)
    (hI : InvArg a E) (hA : ivJet P a X = some A) (h0 : A.v.lo ≤ 0 ∧ 0 ≤ A.v.hi) :
    ivJet P E X = none := by
  induction E generalizing X with
  | var => exact False.elim hI
  | const q => exact False.elim hI
  | add x y ihx ihy | sub x y ihx ihy | mul x y ihx ihy =>
    rcases hI with hx | hy
    · have := ihx X hx hA; simp [ivJet, this]
    · have := ihy X hy hA
      rcases hx' : ivJet P x X with _ | B
      · simp [ivJet, hx']
      · simp [ivJet, hx', this]
  | inv b ih =>
    rcases hI with hb | hb
    · subst hb
      exact ivJet_inv_fail _ _ _ A hA h0
    · have := ih X hb hA
      simp [ivJet, this]
  | exp x ih => simp [ivJet, ih X hI hA]
  | sin x ih => simp [ivJet, ih X hI hA]
  | cos x ih => simp [ivJet, ih X hI hA]

public lemma bsdAux_succ_none_of_left {P : ℕ} {E : Expr} {d : ℕ} {X : Iv}
    (h : bsdAux P E d X.leftHalf = none) : bsdAux P E (d + 1) X = none := by
  simp [bsdAux, h]

public lemma bsdAux_succ_none_of_right {P : ℕ} {E : Expr} {d : ℕ} {X : Iv}
    (h : bsdAux P E d X.rightHalf = none) : bsdAux P E (d + 1) X = none := by
  simp [bsdAux, h]

public lemma bsdAux_succ_some {P : ℕ} {E : Expr} {d : ℕ} {X : Iv} {l r : Iv}
    (hl : bsdAux P E d X.leftHalf = some l) (hr : bsdAux P E d X.rightHalf = some r) :
    bsdAux P E (d + 1) X = some (Iv.hull l r) := by
  simp [bsdAux, hl, hr]

/-- Subdivisão: `bsdAux` falha exatamente quando algum pedaço (depois de `d` bissecções) falha. -/
public lemma bsdAux_none_iff (P : ℕ) (E : Expr) : ∀ (d : ℕ) (X : Iv),
    bsdAux P E d X = none ↔ ∃ Y, Piece d X Y ∧ ivJet P E Y = none
  | 0, X => by
    simp only [bsdAux, Option.map_eq_none_iff]
    constructor
    · intro h; exact ⟨X, rfl, h⟩
    · rintro ⟨Y, hY, h⟩; subst hY; exact h
  | d + 1, X => by
    have hL := bsdAux_none_iff P E d X.leftHalf
    have hR := bsdAux_none_iff P E d X.rightHalf
    constructor
    · intro h
      rcases hl : bsdAux P E d X.leftHalf with _ | l
      · obtain ⟨Y, hY, hY'⟩ := hL.mp hl
        exact ⟨Y, Or.inl hY, hY'⟩
      · rcases hr : bsdAux P E d X.rightHalf with _ | r
        · obtain ⟨Y, hY, hY'⟩ := hR.mp hr
          exact ⟨Y, Or.inr hY, hY'⟩
        · rw [bsdAux_succ_some hl hr] at h
          exact absurd h (by simp)
    · rintro ⟨Y, hY, h⟩
      rcases hY with hY | hY
      · exact bsdAux_succ_none_of_left (hL.mpr ⟨Y, hY, h⟩)
      · exact bsdAux_succ_none_of_right (hR.mpr ⟨Y, hY, h⟩)

/-- **Proposição 6.2, regra de falha (caracterização exata).** `BoundSecondDerivative` falha
se, e somente se, após `d` bissecções de `J` algum pedaço `Y` tem uma subexpressão `inv a` de `E`
cujo denominador `A.v` contém `0`. -/
public theorem boundSecondDerivative_fail_iff (E : Expr) (J : Iv) (P d : ℕ) :
    boundSecondDerivative E J P d = none ↔
      ∃ Y, Piece d J Y ∧ ∃ a A, InvArg a E ∧ ivJet P a Y = some A ∧
        A.v.lo ≤ 0 ∧ 0 ≤ A.v.hi := by
  unfold boundSecondDerivative
  rw [bsdAux_none_iff]
  constructor
  · rintro ⟨Y, hY, h⟩
    obtain ⟨a, A, h1, h2, h3, h4⟩ := ivJet_none_witness P E Y h
    exact ⟨Y, hY, a, A, h1, h2, h3, h4⟩
  · rintro ⟨Y, hY, a, A, h1, h2, h3, h4⟩
    exact ⟨Y, hY, ivJet_of_bad P a E Y A h1 h2 ⟨h3, h4⟩⟩

end Fase3
