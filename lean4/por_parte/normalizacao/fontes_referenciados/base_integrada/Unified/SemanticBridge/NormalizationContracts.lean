module
public import Unified.SemanticBridge.NormalizationAtoms
@[expose] public section

/-!
# Normalização dos contratos concretos da v2

Os resultados preservam a mesma função global, o domínio fechado e os
orçamentos N e H. A passagem do contrato local ao forte filtra apenas átomos
inativos; não assume concordância externa antes dessa normalização.
-/

noncomputable section

namespace SemanticBridge

theorem normalization_local_iff (α β : ℝ) (g : ℝ → ℝ)
    (Λ : Finset Dyadic.Lib.Atom) :
    Montagens.LocalRepG α β g (normalizationAtoms Λ) ↔ AssemblyCore (Set.Icc α β) g Λ := by
  unfold Montagens.LocalRepG AssemblyCore
  rw [normalization_sep_iff, normalization_cover_iff]
  simp [Montagens.MatchG, normalizationAtoms, Montagens.K]

theorem normalization_agree_iff (Λ : Finset Dyadic.Lib.Atom) :
    Montagens.Agree (normalizationAtoms Λ) ↔
      ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ a.cell ∩ b.cell, a.line x = b.line x := by
  simp [Montagens.Agree, normalizationAtoms]

theorem normalization_strong_iff (α β : ℝ) (g : ℝ → ℝ)
    (Λ : Finset Dyadic.Lib.Atom) :
    Montagens.StrongRepG α β g (normalizationAtoms Λ) ↔
      Dyadic.Lib.IsAssemblyRep (Set.Icc α β) g Λ := by
  rw [Montagens.StrongRepG, normalization_local_iff, normalization_agree_iff]
  unfold AssemblyCore Dyadic.Lib.IsAssemblyRep
  tauto

theorem normalization_budget_iff (N H : ℕ) (Λ : Finset Dyadic.Lib.Atom) :
    Montagens.Budget N H (normalizationAtoms Λ) ↔
      Λ.card ≤ N ∧ ∀ a ∈ Λ, a.height ≤ H := by
  unfold Montagens.Budget
  rw [card_normalizationAtoms]
  simp [normalizationAtoms]

@[simp] theorem mem_canonicalAtoms_iff (a : Dyadic.Lib.Atom) (Λ : Finset Montagens.Atom) :
    a ∈ canonicalAtoms Λ ↔ normalizationAtomEquiv a ∈ Λ := by
  constructor
  · rintro ha
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    rw [← hba]
    simpa using hb
  · intro ha
    exact Finset.mem_image.mpr ⟨normalizationAtomEquiv a, ha,
      normalizationAtomEquiv.symm_apply_apply a⟩

/-- Normalização recebida transportada ao tipo concreto da biblioteca. -/
def normalizeAtoms (α β : ℝ) (Λ : Finset Dyadic.Lib.Atom) : Finset Dyadic.Lib.Atom :=
  canonicalAtoms (Montagens.NormK α β (normalizationAtoms Λ))

@[simp] theorem normalization_normalizeAtoms (α β : ℝ) (Λ : Finset Dyadic.Lib.Atom) :
    normalizationAtoms (normalizeAtoms α β Λ) =
      Montagens.NormK α β (normalizationAtoms Λ) := by
  simp [normalizeAtoms]

theorem normalizeAtoms_subset (α β : ℝ) (Λ : Finset Dyadic.Lib.Atom) :
    normalizeAtoms α β Λ ⊆ Λ := by
  intro a ha
  have ha' := (mem_canonicalAtoms_iff a _).mp ha
  exact (mem_normalizationAtoms a Λ).mp (Montagens.mem_NormK.mp ha').1

theorem normalizeAtoms_card_le (α β : ℝ) (Λ : Finset Dyadic.Lib.Atom) :
    (normalizeAtoms α β Λ).card ≤ Λ.card :=
  Finset.card_le_card (normalizeAtoms_subset α β Λ)

@[simp] theorem normalizeAtoms_idem (α β : ℝ) (Λ : Finset Dyadic.Lib.Atom) :
    normalizeAtoms α β (normalizeAtoms α β Λ) = normalizeAtoms α β Λ := by
  simp [normalizeAtoms, Montagens.norm_idem]

/-- O contrato local da mesma função torna-se forte sem aumentar recursos. -/
theorem normalizeAtoms_strong {α β : ℝ} (hK : α < β) {g : ℝ → ℝ}
    {Λ : Finset Dyadic.Lib.Atom} (h : AssemblyCore (Set.Icc α β) g Λ) :
    Dyadic.Lib.IsAssemblyRep (Set.Icc α β) g (normalizeAtoms α β Λ) := by
  have hm := (normalization_local_iff α β g Λ).mpr h
  have hs := (Montagens.normalizationG hK hm).2.2.2.1
  exact (normalization_strong_iff α β g _).mp (by simpa only [normalization_normalizeAtoms] using hs)

/-- As classes globais local e consolidada são iguais em intervalos não degenerados. -/
theorem local_asm_eq_strong {α β : ℝ} (hK : α < β) :
    AsmOn (Set.Icc α β) = Dyadic.Lib.Asm (Set.Icc α β) := by
  ext g
  constructor
  · rintro ⟨hc, Λ, hΛ⟩
    exact ⟨hc, normalizeAtoms α β Λ,
      normalizeAtoms_strong hK ((local_iff_core _ _ _).mp hΛ)⟩
  · intro hg
    exact strong_asm_subset_local _ hg

/-- Classe local com os mesmos orçamentos da classe `Dyadic.Lib.AsmNH`. -/
def AsmOnNH (K : Set ℝ) (N H : ℕ) : Set (ℝ → ℝ) :=
  {g | ContinuousOn g K ∧ ∃ Λ : Finset Dyadic.Lib.Atom,
    IsAssemblyRepOn K g Λ ∧ Λ.card ≤ N ∧ ∀ a ∈ Λ, a.height ≤ H}

/-- A normalização preserva a função e os dois orçamentos, inclusive na classe vazia. -/
theorem local_budgeted_eq_strong {α β : ℝ} (hK : α < β) (N H : ℕ) :
    AsmOnNH (Set.Icc α β) N H = Dyadic.Lib.AsmNH (Set.Icc α β) N H := by
  ext g
  constructor
  · rintro ⟨hc, Λ, hΛ, hN, hH⟩
    refine ⟨hc, normalizeAtoms α β Λ,
      normalizeAtoms_strong hK ((local_iff_core _ _ _).mp hΛ),
      (normalizeAtoms_card_le α β Λ).trans hN, ?_⟩
    intro a ha
    exact hH a (normalizeAtoms_subset α β Λ ha)
  · rintro ⟨hc, Λ, hΛ, hN, hH⟩
    exact ⟨hc, Λ, strong_rep_implies_local _ _ _ hΛ, hN, hH⟩

/-- Melhor erro sob o contrato local, no mesmo codomínio completo da v2. -/
def localJointError (K : Set ℝ) (N H : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ AsmOnNH K N H, Dyadic.Lib.supDist K f g

theorem local_jointError_eq {α β : ℝ} (hK : α < β) (N H : ℕ) (f : ℝ → ℝ) :
    localJointError (Set.Icc α β) N H f = Dyadic.Lib.jointError (Set.Icc α β) N H f := by
  simp only [localJointError, Dyadic.Lib.jointError, local_budgeted_eq_strong hK]

/-- Os conjuntos de alturas suficientes e seus ínfimos são literalmente iguais. -/
theorem local_height_conditions_eq {α β : ℝ} (hK : α < β) (N : ℕ)
    (f : ℝ → ℝ) (ε : ℝ) :
    {H : ℕ | 2 ≤ H ∧ localJointError (Set.Icc α β) N H f ≤ ENNReal.ofReal ε} =
      {H : ℕ | 2 ≤ H ∧ Dyadic.Lib.jointError (Set.Icc α β) N H f ≤ ENNReal.ofReal ε} ∧
    sInf {H : ℕ | 2 ≤ H ∧ localJointError (Set.Icc α β) N H f ≤ ENNReal.ofReal ε} =
      Dyadic.Lib.minHeight (Set.Icc α β) ε N f := by
  simp only [local_jointError_eq hK, Dyadic.Lib.minHeight, and_self]

end SemanticBridge
