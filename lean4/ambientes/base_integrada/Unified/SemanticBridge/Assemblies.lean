module
public import Unified.SemanticBridge.Addresses
@[expose] public section

/-!
# Ponte lógica de montagens: condição forte e condição local

`Dyadic.Lib.IsAssemblyRep` exige coincidência de retas em TODA interseção
espacial de átomos da representação, inclusive fora de K. A formulação
local abaixo impõe essa coincidência apenas dentro de K.

A implicação forte -> local é teorema. A recíproca NÃO é afirmada;
ela exigirá normalização da cobertura ou hipóteses adicionais demonstradas.
-/

namespace SemanticBridge

open Set

/-- Concordância local de montagens em K, sobre átomos canônicos. -/
def IsAssemblyRepOn (K : Set ℝ) (g : ℝ → ℝ)
    (Λ : Finset Dyadic.Lib.Atom) : Prop :=
  (∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b →
    Disjoint (interior a.cell) (interior b.cell)) ∧
  K ⊆ ⋃ a ∈ Λ, a.cell ∧
  (∀ a ∈ Λ, ∀ x ∈ a.cell ∩ K, g x = a.line x) ∧
  (∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ (a.cell ∩ b.cell) ∩ K,
    a.line x = b.line x)

/-- A representação consolidada satisfaz também a condição restrita a K. -/
theorem strong_rep_implies_local (K : Set ℝ) (g : ℝ → ℝ)
    (Λ : Finset Dyadic.Lib.Atom)
    (h : Dyadic.Lib.IsAssemblyRep K g Λ) :
    IsAssemblyRepOn K g Λ := by
  rcases h with ⟨hd, hc, ha, hb⟩
  refine ⟨hd, hc, ha, ?_⟩
  intro a ha' b hb' x hx
  exact hb a ha' b hb' x hx.1

/-- Conjunto de montagens sob o contrato de concordância local. -/
def AsmOn (K : Set ℝ) : Set (ℝ → ℝ) :=
  {g | ContinuousOn g K ∧ ∃ Λ : Finset Dyadic.Lib.Atom,
    IsAssemblyRepOn K g Λ}

/-- Uma montagem no sentido consolidado satisfaz o contrato local. -/
theorem strong_asm_subset_local (K : Set ℝ) :
    Dyadic.Lib.Asm K ⊆ AsmOn K := by
  intro g hg
  rcases hg with ⟨hc, Λ, hΛ⟩
  exact ⟨hc, Λ, strong_rep_implies_local K g Λ hΛ⟩

end SemanticBridge
