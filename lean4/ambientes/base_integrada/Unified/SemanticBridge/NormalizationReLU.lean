module
public import Unified.SemanticBridge.NormalizationErrors
@[expose] public section

/-!
# Extensão ReLU no tipo de montagens original da Fase 2

O operador recebido é transportado à classe concreta da biblioteca. Sua
restrição é a função original e a escolha de uma representação não altera
a extensão normalizada.
-/

noncomputable section

namespace SemanticBridge

theorem fase2_mem_normalization_local {α β : ℝ} {g : Montagens.CK α β}
    (hg : g ∈ Dyadic2.Asm α β) : g ∈ Montagens.Aloc α β := by
  have hm := (normalization_B2_iff α β g).mpr hg
  simpa only [Montagens.B2_eq_Aloc] using hm

/-- Extensão contínua ReLU das montagens no tipo efetivo da Fase 2. -/
def fase2ReLUExtension {α β : ℝ} (hK : α < β)
    (g : {g : Montagens.CK α β // g ∈ Dyadic2.Asm α β}) : C(ℝ, ℝ) :=
  Montagens.extOp hK ⟨g.1, fase2_mem_normalization_local g.2⟩

theorem fase2_relu_extension_agrees {α β : ℝ} (hK : α < β)
    (g : {g : Montagens.CK α β // g ∈ Dyadic2.Asm α β}) (z : Set.Icc α β) :
    fase2ReLUExtension hK g z = g.1 z := by
  have hr := Montagens.Res_extOp hK ⟨g.1, fase2_mem_normalization_local g.2⟩
    (Montagens.contOn_of_continuous (fase2ReLUExtension hK g).continuous)
  exact congrArg (fun f : Montagens.CK α β ↦ f z) hr

theorem fase2_relu_extension_is_consolidated {α β : ℝ} (hK : α < β)
    (g : {g : Montagens.CK α β // g ∈ Dyadic2.Asm α β}) :
    (fase2ReLUExtension hK g : ℝ → ℝ) ∈ Dyadic.Lib.Asm (Set.Icc α β) := by
  have hs : g.1 ∈ Montagens.Astr α β := by
    rw [← Montagens.Aloc_eq_Astr hK]
    exact fase2_mem_normalization_local g.2
  obtain ⟨Λ, hΛ⟩ := hs
  apply (normalization_Bcon_iff α β _).mp
  refine ⟨Montagens.contOn_of_continuous (fase2ReLUExtension hK g).continuous, Λ, ?_⟩
  exact (Montagens.strongRep_iff_strongRepG
    (fun z ↦ (fase2_relu_extension_agrees hK g z).symm) Λ).mp hΛ

/-- A extensão independe da representação local e da cadeia escolhidas. -/
theorem fase2_relu_extension_eq {α β : ℝ} (hK : α < β)
    (g : {g : Montagens.CK α β // g ∈ Dyadic2.Asm α β})
    {Λ : Finset Montagens.Atom} (h : Montagens.LocalRep α β g.1 Λ)
    (q : Montagens.NormChain α β Λ) :
    (fase2ReLUExtension hK g : ℝ → ℝ) = q.Rext :=
  Montagens.extOp_eq hK ⟨g.1, fase2_mem_normalization_local g.2⟩ h q

end SemanticBridge
