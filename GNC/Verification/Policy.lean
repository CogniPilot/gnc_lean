import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Compiler.Old
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Data.Json.FromToJson

/-! Build tooling, not an additional mathematical axiom or proof oracle.
Audit source modules as well as namespaces: moving a declaration outside the
GNC namespace must not evade the check. The dependency traversal uses Lean's
checked kernel environment and shares its visited set across declarations.
-/
namespace Verification.Policy
open Lean

def isProject (name : Name) : Bool :=
  (`GNC).isPrefixOf name

def origin (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.modules[idx.toNat]!.module
  | none => env.mainModule

/-- Lean generates partial runtime companions for total recursive definitions.
The total kernel definition remains the object used by theorems. These
companions are counted separately; the Lean compiler is a runtime trust
boundary, not a proved part of this library. -/
def isRuntimeCompanion (env : Environment) (info : ConstantInfo) : Bool :=
  if !info.isPartial then false else
  match Compiler.isUnsafeRecName? info.name with
  | none => false
  | some parent =>
    match env.checked.get.find? parent with
    | some (.defnInfo value) =>
      value.safety == .safe && value.type == info.type &&
        origin env parent == origin env info.name
    | _ => false

structure Report where
  declarations : Nat := 0
  libraryDeclarations : Nat := 0
  libraryTheorems : Nat := 0
  applicationDeclarations : Nat := 0
  applicationTheorems : Nat := 0
  namespaceOnlyDeclarations : Nat := 0
  runtimeCompanions : Nat := 0
  axioms : Array Name := #[]
  sourceModules : Array Name := #[]

def audit (env : Environment) : Except String Report := do
  let mut names : Array Name := #[]
  -- Inspect Lean's loaded modules, including modules without declarations.
  -- A textual import scan alone cannot establish complete audit coverage.
  let modules := (env.header.modules.map (·.module)).filter isProject
  let modules := if isProject env.mainModule then modules.push env.mainModule else modules
  let mut report : Report := { sourceModules := modules }
  for (name, info) in env.constants.toList do
    let source := origin env name
    if isProject source || isProject ((privateToUserName? name).getD name) then
      if (env.checked.get.find? name).isNone then
        throw s!"Project declaration is absent from the checked environment: {name}"
      let companion := isRuntimeCompanion env info
      if info.isUnsafe || (info.isPartial && !companion) then
        throw s!"Unsafe or partial project declaration: {name}"
      if (Compiler.getImplementedBy? env name).isSome || (getExternAttrData? env name).isSome then
        throw s!"Unchecked project runtime replacement: {name}"
      if info.isAxiom then
        throw s!"Unproved project axiom: {name}"
      names := names.push name
      report := { report with declarations := report.declarations + 1 }
      if companion then
        report := { report with runtimeCompanions := report.runtimeCompanions + 1 }
      let theoremCount := match info with | .thmInfo _ => 1 | _ => 0
      if (`GNC).isPrefixOf source then
        report := { report with
          libraryDeclarations := report.libraryDeclarations + 1
          libraryTheorems := report.libraryTheorems + theoremCount }
        if (`GNC.Applications).isPrefixOf source then
          report := { report with
            applicationDeclarations := report.applicationDeclarations + 1
            applicationTheorems := report.applicationTheorems + theoremCount }
      else
        report := { report with namespaceOnlyDeclarations := report.namespaceOnlyDeclarations + 1 }
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for axiomName in state.axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throw s!"Project depends on forbidden axiom {axiomName}"
  return { report with axioms := state.axioms }

def Report.json (report : Report) : Json :=
  Json.mkObj [
    ("project_declarations", toJson report.declarations),
    ("library_declarations", toJson report.libraryDeclarations),
    ("library_theorem_declarations", toJson report.libraryTheorems),
    ("application_declarations", toJson report.applicationDeclarations),
    ("application_theorem_declarations", toJson report.applicationTheorems),
    ("namespace_only_declarations", toJson report.namespaceOnlyDeclarations),
    ("compiler_runtime_companions", toJson report.runtimeCompanions),
    ("axioms", toJson ((report.axioms.toList.map toString).mergeSort)),
    ("source_modules", toJson ((report.sourceModules.toList.map toString).mergeSort))]

/-- Emit a machine-readable record only after the environment audit succeeds. -/
def emitJson : Elab.Command.CommandElabM Unit := do
  match audit (← getEnv) with
  | .error message => throwError "{message}"
  | .ok report => liftM (m := IO) <| IO.println report.json.pretty

def check : Elab.Command.CommandElabM Unit := do
  match audit (← getEnv) with
  | .error message => throwError "{message}"
  | .ok report =>
    logInfo m!"Axiom audit passed for {report.declarations} project declarations.\n\
      GNC source modules: {report.libraryDeclarations} declarations, \
      {report.libraryTheorems} theorem declarations.\n\
      Included application modules: {report.applicationDeclarations} declarations, \
      {report.applicationTheorems} theorem declarations.\n\
      Additional project-namespace declarations: {report.namespaceOnlyDeclarations}.\n\
      Lean-generated runtime companions: {report.runtimeCompanions} (compiler trust boundary).\n\
      Allowed foundations only: propext, Classical.choice, Quot.sound."

end Verification.Policy
