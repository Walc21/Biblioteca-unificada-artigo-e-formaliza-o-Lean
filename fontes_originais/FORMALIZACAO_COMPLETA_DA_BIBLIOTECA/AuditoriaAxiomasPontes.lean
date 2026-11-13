import Lean
import SemanticAudit

/-!
Auditoria das dependencias axiomaticas das declaracoes dos modulos da Biblioteca + pontes
Unified.*. Nao modifica as demonstracoes.

Executar a partir da raiz do projeto:
    lake env lean AuditoriaAxiomasPontes.lean 2>&1 | tee auditoria_axiomas.txt
-/

open Lean Meta

#eval show MetaM Unit from do
  let env ← getEnv
  let permitidos : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut verificados : Nat := 0
  let mut teoremas : Nat := 0
  let mut irregularidades : Nat := 0

  for (nome, info) in env.constants.toList do
    let moduloProprio := match env.getModuleIdxFor? nome with
      | some idx => (env.header.moduleNames[idx]!).toString.startsWith "Unified."
      | none => false
    unless moduloProprio do continue

    let verificar := match info with
      | .thmInfo _ => true
      | .defnInfo _ => true
      | .opaqueInfo _ => true
      | .axiomInfo _ => true
      | _ => false
    unless verificar do continue

    if let .thmInfo _ := info then teoremas := teoremas + 1
    verificados := verificados + 1
    let axiomas ← collectAxioms nome
    let inesperados := axiomas.filter (fun ax => !permitidos.contains ax)
    IO.println s!"{nome}: {axiomas.toList}"
    unless inesperados.isEmpty do
      irregularidades := irregularidades + 1
      IO.println s!"*** AXIOMAS NAO PERMITIDOS em {nome}: {inesperados.toList}"

  IO.println s!"RESUMO: {verificados} declaracoes analisadas; {teoremas} teoremas; {irregularidades} com axiomas fora da lista."
  if verificados == 0 then
    throwError "Nenhuma declaracao do projeto foi encontrada: auditoria invalida."
  if irregularidades > 0 then
    throwError "Auditoria encontrou axiomas fora da lista permitida."
