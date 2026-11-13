import Lean
import SemanticAudit

/-!
Audita a união das dependências axiomáticas de todas as declarações próprias.
Usa o coletor oficial do Lean com o estado de visita compartilhado entre raízes.
Isso evita percorrer repetidamente os mesmos termos de prova da Mathlib.
-/

open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut roots : Array Name := #[]
  let mut theoremCount : Nat := 0
  let mut modules : NameSet := {}
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[idx]!
    unless moduleName.toString.startsWith "RequestProject." ||
      moduleName.toString.startsWith "Unified." || moduleName == `SemanticAudit do continue
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | _ => "other"
    if kind == "other" then continue
    roots := roots.push name
    modules := modules.insert moduleName
    if kind == "theorem" then theoremCount := theoremCount + 1
    IO.println s!"DECL\t{name}\t{kind}\t{moduleName}"
  let (_, state) := ((roots.forM CollectAxioms.collect).run env).run {}
  let unexpected := state.axioms.filter (fun name ↦ !allowed.contains name)
  let report := Json.mkObj [
    ("declarations", toJson roots.size),
    ("theorems", toJson theoremCount),
    ("modules_with_declarations", toJson (modules.toList.map Name.toString)),
    ("axioms_union", toJson (state.axioms.map Name.toString)),
    ("unexpected_axioms", toJson (unexpected.map Name.toString)),
    ("dependency_constants_visited", toJson state.visited.size)]
  IO.println s!"AUDIT_JSON {report.compress}"
  if roots.isEmpty then throwError "Nenhuma declaração própria foi auditada."
  unless unexpected.isEmpty do
    throwError "Dependências axiomáticas não permitidas: {unexpected}"
