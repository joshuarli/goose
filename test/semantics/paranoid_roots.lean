import Lean
import Goose.Audit

open Lean

namespace GooseParanoidAudit

def decodeName (text : String) : IO Name := do
  let some name := Syntax.decodeNameLit ("`" ++ text)
    | throw (IO.userError s!"invalid declaration name: {text}")
  return name

def collect (env : Environment) (roots : Array Name) : IO NameSet := do
  let mut pending := roots
  let mut visited : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    let some info := env.find? name
      | throw (IO.userError s!"missing dependency: {name}")
    visited := visited.insert name
    pending := pending ++ info.getUsedConstantsAsSet.toArray
    match info with
    | .inductInfo val => pending := pending ++ val.all.toArray ++ val.ctors.toArray
    | .ctorInfo val => pending := pending.push val.induct
    | .recInfo val =>
      pending := pending ++ val.all.toArray
      for rule in val.rules do pending := pending ++ rule.rhs.getUsedConstants
    | _ => pure ()
  return visited

def validateProofs (env : Environment) (roots : Array Name) : IO NameSet := do
  for name in roots do
    unless (env.find? name).any (·.isTheorem) do
      throw (IO.userError s!"audit root is not a theorem: {name}")
  let names ← collect env roots
  for name in names do
    let info := (env.find? name).get!
    if info.isUnsafe || info.isPartial then
      throw (IO.userError s!"unsafe or partial proof dependency: {name}")
    if let .axiomInfo _ := info then
      unless Goose.Audit.allowedAxioms.contains name.toString do
        throw (IO.userError s!"disallowed axiom: {name}")
  return names

def verifyCoverage (expected actual : NameSet) : IO Unit := do
  for name in expected do
    unless actual.contains name do
      throw (IO.userError s!"missing exported dependency: {name}")

def owner (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.allImportedModuleNames[index.toNat]!
  | none => Name.anonymous

def sorted (names : NameSet) : Array Name :=
  names.toArray.qsort (fun a b => a.toString < b.toString)

def jsonField [FromJson α] (json : Json) (field : String) : IO α := do
  match json.getObjValAs? α field with
  | .ok value => return value
  | .error message => throw (IO.userError message)

def exportedNames (path : System.FilePath) : IO NameSet := do
  let handle ← IO.FS.Handle.mk path .read
  let mut names : Std.HashMap Nat Name := { (0, .anonymous) }
  let mut declared : NameSet := {}
  repeat
    let line ← handle.getLine
    if line.isEmpty then break
    let json ← match Json.parse line with
      | .ok json => pure json
      | .error message => throw (IO.userError message)
    if let .ok (index : Nat) := json.getObjValAs? Nat "in" then
      if names.contains index then throw (IO.userError s!"duplicate name index: {index}")
      let pair : Nat × Sum String Nat ← match json.getObjVal? "str" with
        | .ok value => pure (← jsonField value "pre", Sum.inl (← jsonField value "str"))
        | .error _ =>
          let value ← jsonField json "num"
          pure (← jsonField value "pre", Sum.inr (← jsonField value "i"))
      let (parentIndex, component) := pair
      let some parent := names[parentIndex]?
        | throw (IO.userError s!"missing name index: {parentIndex}")
      let name := match component with
        | .inl text => Name.str parent text
        | .inr number => Name.num parent number
      names := names.insert index name
    let mut declarations : Array Json := #[]
    for field in ["axiom", "def", "thm", "opaque", "quot"] do
      if let .ok value := json.getObjVal? field then declarations := declarations.push value
    if let .ok value := json.getObjVal? "inductive" then
      for field in ["types", "ctors", "recs"] do
        declarations := declarations ++ (← jsonField value field : Array Json)
    for declaration in declarations do
      let index : Nat ← jsonField declaration "name"
      let some name := names[index]?
        | throw (IO.userError s!"missing declaration name index: {index}")
      if declared.contains name then throw (IO.userError s!"duplicate exported declaration: {name}")
      declared := declared.insert name
  return declared

def run (args : List String) : IO Unit := do
  unless Lean.versionString == Goose.Audit.expectedLeanVersion do
    throw (IO.userError s!"expected Lean {Goose.Audit.expectedLeanVersion}, found {Lean.versionString}")
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `Main}] {}
  let proofRoots ← Goose.Audit.registry.toArray.mapM (decodeName ·.theoremName)
  let proofNames ← validateProofs env proofRoots
  let runtimeNames ← collect env #[`main]
  let names := proofNames ++ runtimeNames
  let stderr ← IO.getStderr
  stderr.putStrLn s!"theorem_roots={proofRoots.size} theorem_dependencies={proofNames.size} main_dependencies={runtimeNames.size} combined_dependencies={names.size}"
  match args with
  | ["roots"] =>
    for name in proofRoots.push `main do IO.println s!"{owner env name}\t{name}"
  | ["closure"] =>
    for name in sorted names do
      IO.println s!"{owner env name}\t{name}\tclaim={proofNames.contains name}\tmain={runtimeNames.contains name}"
  | "verify" :: exports =>
    if exports.isEmpty then throw (IO.userError "verify requires official NDJSON exports")
    let mut exportedUnion : NameSet := {}
    for exportPath in exports do
      for name in (← exportedNames exportPath) do
        unless env.contains name do
          throw (IO.userError s!"export contains a declaration absent from source: {name}")
        exportedUnion := exportedUnion.insert name
    verifyCoverage names exportedUnion
    IO.println s!"verified {proofRoots.size} theorem roots and main, {names.size} dependencies in {exportedUnion.size} exported constants"
  | _ => throw (IO.userError "expected roots, closure, or verify EXPORT...")

end GooseParanoidAudit

def main (args : List String) : IO Unit := GooseParanoidAudit.run args
