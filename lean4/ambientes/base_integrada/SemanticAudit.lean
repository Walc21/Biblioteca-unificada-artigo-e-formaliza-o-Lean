module
public import Unified.SemanticBridge.CanonicalAtoms
public import Unified.SemanticBridge.NormalizationReLU
@[expose] public section

/-! Auditoria de integração: as seis pontes independentes são importadas e
compiladas conjuntamente. Não altera a biblioteca original. -/
namespace SemanticBridge

def auditLoaded : Bool := true

end SemanticBridge
