module
public import Unified.SemanticBridge.NormalizationClasses
@[expose] public section

/-!
# Erros tipados e orçamentos da normalização na v2

O ínfimo sobre funções contínuas no subtipo fechado é identificado com o
ínfimo global da biblioteca. A distância só usa valores no domínio, e a
classe vazia mantém o valor +∞ em ENNReal.
-/

noncomputable section

namespace SemanticBridge

theorem normalization_typed_budget_iff {α β : ℝ} (g : Montagens.CK α β)
    (G : ℝ → ℝ) (hG : ContinuousOn G (Set.Icc α β))
    (hgg : ∀ z : Set.Icc α β, g z = G z) (N H : ℕ) :
    g ∈ Montagens.AstrNH α β N H ↔ G ∈ Dyadic.Lib.AsmNH (Set.Icc α β) N H := by
  constructor
  · rintro ⟨Λ, hs, hb⟩
    have hsg := (Montagens.strongRep_iff_strongRepG hgg Λ).mp hs
    have hsb : Montagens.StrongRepG α β G (normalizationAtoms (canonicalAtoms Λ)) := by
      simpa only [normalization_canonical_atoms] using hsg
    have hbb : Montagens.Budget N H (normalizationAtoms (canonicalAtoms Λ)) := by
      simpa only [normalization_canonical_atoms] using hb
    obtain ⟨hN, hH⟩ := (normalization_budget_iff N H _).mp hbb
    exact ⟨hG, canonicalAtoms Λ, (normalization_strong_iff α β G _).mp hsb, hN, hH⟩
  · rintro ⟨_, Λ, hs, hN, hH⟩
    refine ⟨normalizationAtoms Λ, ?_, (normalization_budget_iff N H Λ).mpr ⟨hN, hH⟩⟩
    exact (Montagens.strongRep_iff_strongRepG hgg _).mpr
      ((normalization_strong_iff α β G Λ).mpr hs)

theorem normalization_distance {α β : ℝ} (hK : α < β) (f g : Montagens.CK α β)
    (F G : ℝ → ℝ) (hf : ∀ z : Set.Icc α β, f z = F z)
    (hg : ∀ z : Set.Icc α β, g z = G z) :
    ENNReal.ofReal (Montagens.dK f g) = Dyadic.Lib.supDist (Set.Icc α β) F G := by
  obtain ⟨z, hz, hmax⟩ := (Montagens.dK_isMax hK f g).1
  rw [hz]
  apply le_antisymm
  · apply le_iSup_of_le (z : ℝ)
    apply le_iSup_of_le z.2
    rw [← hf z, ← hg z]
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply ENNReal.ofReal_le_ofReal
    rw [← hf ⟨x, hx⟩, ← hg ⟨x, hx⟩]
    exact hmax ⟨x, hx⟩

/-- Erro consolidado no tipo contínuo igual ao erro global da biblioteca. -/
theorem normalization_Econ_eq_jointError {α β : ℝ} (hK : α < β)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc α β)) (N H : ℕ) :
    Montagens.Econ N H (Montagens.Res f ((normalization_contOn_iff α β f).mpr hf)) =
      Dyadic.Lib.jointError (Set.Icc α β) N H f := by
  let fK := Montagens.Res f ((normalization_contOn_iff α β f).mpr hf)
  have hff : ∀ z : Set.Icc α β, fK z = f z := fun _ ↦ rfl
  change Montagens.Err fK (Montagens.AstrNH α β N H) = _
  unfold Montagens.Err Dyadic.Lib.jointError
  apply le_antisymm
  · apply le_iInf
    intro G
    apply le_iInf
    intro hG
    let gK := Montagens.Res G ((normalization_contOn_iff α β G).mpr hG.1)
    have hgg : ∀ z : Set.Icc α β, gK z = G z := fun _ ↦ rfl
    have hg := (normalization_typed_budget_iff gK G hG.1 hgg N H).mpr hG
    exact iInf_le_of_le gK (iInf_le_of_le hg
      (le_of_eq (normalization_distance hK fK gK f G hff hgg)))
  · apply le_iInf
    intro gK
    apply le_iInf
    intro hg
    let G : ℝ → ℝ := Montagens.E0 hK.le gK
    have hgg : ∀ z : Set.Icc α β, gK z = G z :=
      fun z ↦ (Montagens.E0_apply_mem hK.le gK z).symm
    have hGcont : ContinuousOn G (Set.Icc α β) :=
      (Montagens.E0 hK.le gK).continuous.continuousOn
    have hG := (normalization_typed_budget_iff gK G hGcont hgg N H).mp hg
    exact iInf_le_of_le G (iInf_le_of_le hG
      (le_of_eq (normalization_distance hK fK gK f G hff hgg).symm))

/-- O erro local recebido usa exatamente os recursos e o erro da v2. -/
theorem normalization_Eloc_eq_jointError {α β : ℝ} (hK : α < β)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc α β)) (N H : ℕ) :
    Montagens.Eloc N H (Montagens.Res f ((normalization_contOn_iff α β f).mpr hf)) =
      Dyadic.Lib.jointError (Set.Icc α β) N H f := by
  rw [Montagens.errors_eq hK]
  exact normalization_Econ_eq_jointError hK f hf N H

end SemanticBridge
