module
public import Unified.Consolidado.Sec7.Heights
@[expose] public section

/-!
# Section 4: continuous assemblies

Definition 4.1 (continuous assembly `𝒜(K)`) and the leaf/height-budgeted classes
`𝒜_{N,H}(K)` of Definition 7.13.
-/

open Finset

namespace Dyadic.Lib

/-- A representation of `g` on `K` by a finite family `Λ` of atoms (Definition 4.1): the cells
have pairwise disjoint interiors, their union contains `K`, `g` coincides with the line of each
atom on `J ∩ K`, and the lines of two atoms coincide on shared boundary points. -/
def IsAssemblyRep (K : Set ℝ) (g : ℝ → ℝ) (Λ : Finset Atom) : Prop :=
  (∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → Disjoint (interior a.cell) (interior b.cell)) ∧
  K ⊆ ⋃ a ∈ Λ, a.cell ∧
  (∀ a ∈ Λ, ∀ x ∈ a.cell ∩ K, g x = a.line x) ∧
  (∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ a.cell ∩ b.cell, a.line x = b.line x)

/-- **Definition 4.1**: the set `𝒜(K)` of continuous assemblies on `K`. -/
def Asm (K : Set ℝ) : Set (ℝ → ℝ) :=
  {g | ContinuousOn g K ∧ ∃ Λ : Finset Atom, IsAssemblyRep K g Λ}

/-- **Definition 7.13**: `𝒜_{N,H}(K)`, assemblies admitting a representation with at most `N`
leaves, all atoms in `𝓛_H`. -/
def AsmNH (K : Set ℝ) (N H : ℕ) : Set (ℝ → ℝ) :=
  {g | ContinuousOn g K ∧ ∃ Λ : Finset Atom, IsAssemblyRep K g Λ ∧ Λ.card ≤ N ∧
    ∀ a ∈ Λ, a.height ≤ H}

lemma AsmNH_subset_Asm (K : Set ℝ) (N H : ℕ) : AsmNH K N H ⊆ Asm K :=
  fun _ ⟨hc, Λ, hΛ, _⟩ => ⟨hc, Λ, hΛ⟩

/-- The ReLU activation `ρ(z) = max{0, z}`. -/
def relu (z : ℝ) : ℝ := max 0 z

/-- Uniform distance `‖f - g‖_{∞,K}` (as an extended nonnegative real). -/
noncomputable def supDist (K : Set ℝ) (f g : ℝ → ℝ) : ENNReal :=
  ⨆ x ∈ K, ENNReal.ofReal |f x - g x|

lemma supDist_le_iff {K : Set ℝ} {f g : ℝ → ℝ} {ε : ℝ} (hε : 0 ≤ ε) :
    supDist K f g ≤ ENNReal.ofReal ε ↔ ∀ x ∈ K, |f x - g x| ≤ ε := by
  unfold supDist
  simp only [iSup_le_iff]
  constructor
  · intro h x hx
    exact (ENNReal.ofReal_le_ofReal_iff hε).1 (h x hx)
  · intro h x hx
    exact ENNReal.ofReal_le_ofReal (h x hx)

end Dyadic.Lib
