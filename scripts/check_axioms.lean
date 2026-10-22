-- Legacy import mode loads private proof bodies transitively for the audit.
import Lean
import Math

open Lean Elab Command

structure AuditTarget where
  name : String
  module : String
  obligation : String
  deriving FromJson

structure AuditRequest where
  modules : Array String
  targets : Array AuditTarget
  deriving FromJson

private def moduleOf (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => some env.mainModule

run_cmd do
  let raw ← IO.FS.readFile ".lake/rudin-check/request.json"
  let json ← match Json.parse raw with
    | .ok value => pure value
    | .error message => throwError "Invalid audit request: {message}"
  let request : AuditRequest ← match fromJson? json with
    | .ok value => pure value
    | .error message => throwError "Invalid audit schema: {message}"
  let env := (← getEnv).setExporting false
  for mod in request.modules do
    unless (env.getModuleIdx? mod.toName).isSome || env.mainModule == mod.toName do
      throwError "Delivered module is not imported by Math: {mod}"
  for target in request.targets do
    let name := target.name.toName
    let some info := env.find? name
      | throwError "Missing declaration for {target.obligation}: {name}"
    unless moduleOf env name == some target.module.toName do
      throwError "Wrong origin module for {target.obligation}: {name}"
    unless info matches .thmInfo _ do
      throwError "Delivery must name a proved theorem: {name}"
    logInfo m!"{target.obligation}: {name} : {info.type}"
  let declarations := env.constants.fold (init := #[]) fun acc name info =>
    match moduleOf env name with
    | some mod =>
      if mod == `Math.Rudin || "Math.Rudin.".isPrefixOf mod.toString then
        acc.push (name, info)
      else acc
    | none => acc
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (name, info) in declarations do
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial declaration in delivery: {name}"
    if info matches .axiomInfo _ then
      throwError "Custom axiom in delivery: {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom dependency: {name} depends on {axiomName}"
  logInfo m!"Axiom audit passed for {declarations.size} local declarations and {request.targets.size} delivered references."
