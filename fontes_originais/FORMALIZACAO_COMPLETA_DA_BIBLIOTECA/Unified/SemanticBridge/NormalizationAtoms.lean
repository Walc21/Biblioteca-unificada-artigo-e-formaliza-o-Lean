module
public import Unified.SemanticBridge.CanonicalAtoms
public import RequestProject.Bridge
public import RequestProject.Error
public import RequestProject.ReLU
public import RequestProject.Appendix
@[expose] public section

/-!
# Identificação dos átomos da normalização com os átomos da biblioteca

O pacote recebido é importado sem editar seus fontes. A equivalência abaixo
preserva cada campo geométrico e a altura; não identifica endereços de
enumerações diferentes.
-/

noncomputable section

namespace SemanticBridge

/-- Identificação pelos quatro dados do átomo, incluindo a inclinação não nula. -/
def normalizationAtomEquiv : Dyadic.Lib.Atom ≃ Montagens.Atom where
  toFun a := ⟨a.k, a.m, a.y0, a.s, a.hs⟩
  invFun a := ⟨a.k, a.m, a.y, a.s, a.hs⟩
  left_inv a := by cases a; rfl
  right_inv a := by cases a; rfl

@[simp] theorem normalization_atom_cell (a : Dyadic.Lib.Atom) :
    (normalizationAtomEquiv a).Ja = a.cell := rfl

@[simp] theorem normalization_atom_interior (a : Dyadic.Lib.Atom) :
    (normalizationAtomEquiv a).Oa = interior a.cell := by
  simp [Montagens.Atom.Oa, Montagens.O, Dyadic.Lib.Atom.cell,
    Montagens.Atom.C, Montagens.L, Montagens.R, Montagens.LQ, Montagens.RQ,
    Dyadic.Lib.Atom.left, Dyadic.Lib.Atom.right, normalizationAtomEquiv]

@[simp] theorem normalization_atom_line (a : Dyadic.Lib.Atom) :
    (normalizationAtomEquiv a).line = a.line := rfl

@[simp] theorem normalization_atom_height (a : Dyadic.Lib.Atom) :
    (normalizationAtomEquiv a).height = a.height := by
  simp [Montagens.Atom.height, Dyadic.Lib.Atom.height, normalizationAtomEquiv,
    Montagens.ht, Dyadic.Lib.ratHeight, max_assoc]

/-- Transporte de uma família finita, sem acrescentar ou identificar átomos. -/
def normalizationAtoms (Λ : Finset Dyadic.Lib.Atom) : Finset Montagens.Atom :=
  Λ.image normalizationAtomEquiv

/-- Transporte inverso de uma família finita do pacote recebido. -/
def canonicalAtoms (Λ : Finset Montagens.Atom) : Finset Dyadic.Lib.Atom :=
  Λ.image normalizationAtomEquiv.symm

@[simp] theorem mem_normalizationAtoms (a : Dyadic.Lib.Atom)
    (Λ : Finset Dyadic.Lib.Atom) :
    normalizationAtomEquiv a ∈ normalizationAtoms Λ ↔ a ∈ Λ := by
  simp [normalizationAtoms]

@[simp] theorem canonical_normalization_atoms (Λ : Finset Dyadic.Lib.Atom) :
    canonicalAtoms (normalizationAtoms Λ) = Λ := by
  simp [canonicalAtoms, normalizationAtoms, Finset.image_image]

@[simp] theorem normalization_canonical_atoms (Λ : Finset Montagens.Atom) :
    normalizationAtoms (canonicalAtoms Λ) = Λ := by
  simp [canonicalAtoms, normalizationAtoms, Finset.image_image]

@[simp] theorem card_normalizationAtoms (Λ : Finset Dyadic.Lib.Atom) :
    (normalizationAtoms Λ).card = Λ.card :=
  Finset.card_image_of_injective Λ normalizationAtomEquiv.injective

@[simp] theorem card_canonicalAtoms (Λ : Finset Montagens.Atom) :
    (canonicalAtoms Λ).card = Λ.card :=
  Finset.card_image_of_injective Λ normalizationAtomEquiv.symm.injective

/-- A separação de interiores coincide nos dois tipos concretos de átomo. -/
theorem normalization_sep_iff (Λ : Finset Dyadic.Lib.Atom) :
    Montagens.Sep (normalizationAtoms Λ) ↔
      ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → Disjoint (interior a.cell) (interior b.cell) := by
  simp only [Montagens.Sep, normalizationAtoms, Finset.forall_mem_image,
    normalizationAtomEquiv.injective.ne_iff, normalization_atom_interior,
    Set.disjoint_iff_inter_eq_empty]

/-- O transporte conserva exatamente a cobertura de qualquer domínio. -/
theorem normalization_cover_iff (K : Set ℝ) (Λ : Finset Dyadic.Lib.Atom) :
    Montagens.Cover K (normalizationAtoms Λ) ↔ K ⊆ ⋃ a ∈ Λ, a.cell := by
  simp [Montagens.Cover, normalizationAtoms, Set.subset_def]

end SemanticBridge
