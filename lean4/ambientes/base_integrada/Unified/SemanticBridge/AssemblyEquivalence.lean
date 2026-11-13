module
public import Unified.SemanticBridge.Errors
@[expose] public section

/-!
# Caracterização exata da diferença entre montagens locais e fortes

A compatibilidade de valores dentro de K é consequência da representação por
uma ÚNICA função g. A definição consolidada acrescenta a concordância de
retas nos pontos das interseções que estão FORA de K.

Este arquivo demonstra o critério necessário e suficiente sem postular
falsamente que as classes sejam iguais sem normalização das coberturas.
-/

namespace SemanticBridge

open Set

/-- Os três requisitos nucleares: interiores disjuntos, cobertura e acordo com g em K. -/
def AssemblyCore (K : Set ℝ) (g : ℝ → ℝ)
    (Λ : Finset Dyadic.Lib.Atom) : Prop :=
  (∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b →
    Disjoint (interior a.cell) (interior b.cell)) ∧
  K ⊆ ⋃ a ∈ Λ, a.cell ∧
  (∀ a ∈ Λ, ∀ x ∈ a.cell ∩ K, g x = a.line x)

/-- Fora do domínio, quaisquer duas retas incidentes devem concordar.
    A hipótese é exigida inclusive em interseções degeneradas, mas para
    a = b a igualdade é automática. -/
def OutsideAgreement (K : Set ℝ) (Λ : Finset Dyadic.Lib.Atom) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ a.cell ∩ b.cell,
    x ∉ K → a.line x = b.line x

/-- A concordância em K é automática: ambas as retas têm valor g(x). -/
theorem agreement_inside_from_core {K : Set ℝ} {g : ℝ → ℝ}
    {Λ : Finset Dyadic.Lib.Atom} (h : AssemblyCore K g Λ) :
    ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ (a.cell ∩ b.cell) ∩ K,
      a.line x = b.line x := by
  intro a ha b hb x hx
  exact (h.2.2 a ha x ⟨hx.1.1, hx.2⟩).symm.trans
    (h.2.2 b hb x ⟨hx.1.2, hx.2⟩)

/-- A quarta cláusula da representação local é redundante. -/
theorem local_iff_core (K : Set ℝ) (g : ℝ → ℝ)
    (Λ : Finset Dyadic.Lib.Atom) :
    IsAssemblyRepOn K g Λ ↔ AssemblyCore K g Λ := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2, agreement_inside_from_core h⟩

/-- CRITÉRIO EXATO: a representação consolidada corresponde à local se,
    e somente se, há concordância também nas interseções externas a K. -/
theorem strong_iff_local_and_outside (K : Set ℝ) (g : ℝ → ℝ)
    (Λ : Finset Dyadic.Lib.Atom) :
    Dyadic.Lib.IsAssemblyRep K g Λ ↔
      IsAssemblyRepOn K g Λ ∧ OutsideAgreement K Λ := by
  constructor
  · intro h
    constructor
    · exact strong_rep_implies_local K g Λ h
    · intro a ha b hb x hx _
      exact h.2.2.2 a ha b hb x hx
  · rintro ⟨hloc, hout⟩
    have hcore := (local_iff_core K g Λ).mp hloc
    refine ⟨hcore.1, hcore.2.1, hcore.2.2, ?_⟩
    intro a ha b hb x hx
    by_cases hxK : x ∈ K
    · exact hloc.2.2.2 a ha b hb x ⟨hx, hxK⟩
    · exact hout a ha b hb x hx hxK

/-- Quando todos os encontros de células distintas estão em K, as
    representações local e consolidada são equivalentes sem hipóteses
    adicionais sobre os valores das retas fora de K. -/
def IntersectionsInside (K : Set ℝ) (Λ : Finset Dyadic.Lib.Atom) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → a.cell ∩ b.cell ⊆ K

theorem intersections_inside_imply_outside (K : Set ℝ)
    (Λ : Finset Dyadic.Lib.Atom) (h : IntersectionsInside K Λ) :
    OutsideAgreement K Λ := by
  intro a ha b hb x hx hxNot
  by_cases hab : a = b
  · subst b
    rfl
  · exact False.elim (hxNot (h a ha b hb hab hx))

theorem strong_iff_local_of_intersections_inside
    (K : Set ℝ) (g : ℝ → ℝ) (Λ : Finset Dyadic.Lib.Atom)
    (h : IntersectionsInside K Λ) :
    Dyadic.Lib.IsAssemblyRep K g Λ ↔ IsAssemblyRepOn K g Λ := by
  constructor
  · exact strong_rep_implies_local K g Λ
  · intro hloc
    exact (strong_iff_local_and_outside K g Λ).mpr
      ⟨hloc, intersections_inside_imply_outside K Λ h⟩

/-- Critério exato no nível da CLASSE consolidada, preservando o testemunho Λ. -/
theorem strong_asm_iff_local_with_external_witness
    (K : Set ℝ) (g : ℝ → ℝ) :
    g ∈ Dyadic.Lib.Asm K ↔
      ContinuousOn g K ∧
      ∃ Λ : Finset Dyadic.Lib.Atom,
        IsAssemblyRepOn K g Λ ∧ OutsideAgreement K Λ := by
  constructor
  · rintro ⟨hc, Λ, hrep⟩
    exact ⟨hc, Λ, (strong_iff_local_and_outside K g Λ).mp hrep⟩
  · rintro ⟨hc, Λ, hloc, hout⟩
    exact ⟨hc, Λ, (strong_iff_local_and_outside K g Λ).mpr ⟨hloc, hout⟩⟩

/-- Todos os átomos podem ser representados sobre uma única célula sem
    requerer igualdade literal de endereços em fases distintas. -/
theorem local_rep_implies_core {K : Set ℝ} {g : ℝ → ℝ}
    {Λ : Finset Dyadic.Lib.Atom} (h : IsAssemblyRepOn K g Λ) :
    AssemblyCore K g Λ := (local_iff_core K g Λ).mp h

end SemanticBridge
