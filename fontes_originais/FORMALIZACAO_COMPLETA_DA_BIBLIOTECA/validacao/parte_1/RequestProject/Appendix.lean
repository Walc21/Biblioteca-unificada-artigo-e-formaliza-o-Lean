module
public import RequestProject.Normalization

/-!
# Apêndice A: predicados auxiliares

Formalização dos predicados auxiliares do Apêndice A (`sec:adapters`).
A identificação com os nomes de um pacote Lean externo não pode ser feita aqui,
pois esse pacote não faz parte do projeto; formalizamos as definições e as
implicações matemáticas enunciadas no apêndice.
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

open Atom

variable {α β : ℝ}

/-- `InnerAgree_K(Λ)`: as retas coincidem nos encontros dentro de `K`. -/
def InnerAgree (α β : ℝ) (Λ : Finset Atom) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ a.Ja ∩ b.Ja ∩ K α β, a.line x = b.line x

/-- `IntersectionsInside_K(Λ)`: encontros de átomos distintos estão em `K`. -/
def IntersectionsInside (α β : ℝ) (Λ : Finset Atom) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → a.Ja ∩ b.Ja ⊆ K α β

/-- O predicado local com concordância interna redundante:
`LocalRep^G_K(G, Λ) ∧ InnerAgree_K(Λ)`. -/
def LocalRepInner (α β : ℝ) (G : ℝ → ℝ) (Λ : Finset Atom) : Prop :=
  LocalRepG α β G Λ ∧ InnerAgree α β Λ

/-- A concordância interna deriva de `Match^G`. -/
theorem innerAgree_of_matchG {G : ℝ → ℝ} {Λ : Finset Atom} (h : MatchG α β G Λ) :
    InnerAgree α β Λ := by
  rintro a ha b hb x ⟨⟨hxa, hxb⟩, hxK⟩
  rw [← h a ha x ⟨hxa, hxK⟩, h b hb x ⟨hxb, hxK⟩]

/-- A concordância interna redundante não altera o predicado local. -/
theorem localRepInner_iff {G : ℝ → ℝ} {Λ : Finset Atom} :
    LocalRepInner α β G Λ ↔ LocalRepG α β G Λ :=
  ⟨fun h => h.1, fun h => ⟨h, innerAgree_of_matchG h.2.2⟩⟩

/-- Sob `IntersectionsInside_K(Λ)`, a concordância interna implica `Agree(Λ)`. -/
theorem agree_of_innerAgree {Λ : Finset Atom} (hI : IntersectionsInside α β Λ)
    (h : InnerAgree α β Λ) : Agree Λ := by
  intro a ha b hb x hx
  by_cases hab : a = b
  · subst hab; rfl
  · exact h a ha b hb x ⟨hx, hI a ha b hb hab hx⟩

/-- Conversão local para consolidada sob o critério de interseções internas. -/
theorem strong_iff_local_of_intersections_inside {G : ℝ → ℝ} {Λ : Finset Atom}
    (hI : IntersectionsInside α β Λ) : StrongRepG α β G Λ ↔ LocalRepG α β G Λ :=
  ⟨fun h => h.1, fun h => ⟨h, agree_of_innerAgree hI (innerAgree_of_matchG h.2.2)⟩⟩

/-- A terceira conclusão do Teorema `thm:norm` implica `IntersectionsInside`. -/
theorem intersectionsInside_of_inside {Λ : Finset Atom}
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → a.Ja ∩ b.Ja ⊆ Kint α β) :
    IntersectionsInside α β Λ :=
  fun a ha b hb hab _ hx => ⟨(h a ha b hb hab hx).1.le, (h a ha b hb hab hx).2.le⟩

end Montagens

end
