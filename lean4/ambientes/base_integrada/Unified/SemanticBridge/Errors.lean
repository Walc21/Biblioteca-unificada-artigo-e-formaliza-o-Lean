module
public import Unified.SemanticBridge.Assemblies
@[expose] public section

/-!
# Equivalência dos critérios uniformes de erro

A Fase 3 usa `sSup` com valores reais; a Consolidação usa o supremo em
`ENNReal`. O resultado abaixo prova a equivalência das desigualdades
com erro ε não negativo sobre K não vazio e diferença uniformemente limitada.
-/

namespace SemanticBridge

open Set

/-- Os critérios de erro uniformes das Fases 3 e Consolidado são equivalentes. -/
theorem uniform_error_bounds_iff {K : Set ℝ} {f g : ℝ → ℝ} {ε : ℝ}
    (hK : K.Nonempty)
    (hbounded : ∃ B : ℝ, ∀ x ∈ K, |f x - g x| ≤ B)
    (hε : 0 ≤ ε) :
    Fase3.supNormOn K (fun x => f x - g x) ≤ ε ↔
      Dyadic.Lib.supDist K f g ≤ ENNReal.ofReal ε := by
  rw [Dyadic.Lib.supDist_le_iff hε]
  constructor
  · intro hs x hx
    obtain ⟨B, hB⟩ := hbounded
    exact (Fase3.le_supNormOn (K := K) (u := fun t => f t - g t)
      (c := B) hB hx).trans hs
  · intro hs
    exact Fase3.supNormOn_le hK hs

end SemanticBridge
