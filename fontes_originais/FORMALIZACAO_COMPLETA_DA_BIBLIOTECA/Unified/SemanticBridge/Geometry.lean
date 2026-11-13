module
public import Unified
@[expose] public section

/-!
# Ponte geométrica entre as fases

Estas igualdades dizem respeito a células e centros com os **mesmos** parâmetros
`(k,m)`. Não identificam os índices naturais de diferentes enumerações.
-/

namespace SemanticBridge

/-- As células fechadas das fases 1 e 2 são literalmente a mesma definição. -/
theorem cell_fase1_fase2 (k : ℕ) (m : ℤ) :
    Fase1.J k m = Dyadic2.cellJ k m := rfl

/-- As células com posse semiaberta das fases 1 e 2 coincidem. -/
theorem owned_fase1_fase2 (k : ℕ) (m : ℤ) :
    Fase1.Jown k m = Dyadic2.cellOwn k m := rfl

/-- A célula usada para interpolação na Fase 3 é a célula da Fase 1. -/
theorem cell_fase1_fase3 (k : ℕ) (m : ℤ) :
    Fase1.J k m = Fase3.cell k m := rfl

/-- A convenção semiaberta é a mesma na Fase 3. -/
theorem owned_fase1_fase3 (k : ℕ) (m : ℤ) :
    Fase1.Jown k m = Fase3.cellOwn k m := rfl

/-- Os centros diádicos das Fases 1 e 2 coincidem. -/
theorem center_fase1_fase2 (k : ℕ) (m : ℤ) :
    Fase1.x0 k m = Dyadic2.center k m := by
  simpa only [Fase1.x0] using (Dyadic2.center_eq k m).symm

/-- Os centros diádicos das Fases 1 e 3 coincidem. -/
theorem center_fase1_fase3 (k : ℕ) (m : ℤ) :
    Fase1.x0 k m = Fase3.center k m := rfl

end SemanticBridge
