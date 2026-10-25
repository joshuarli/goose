import Goose.Audit
import Goose.Core.Run
import Goose.Construct.Eval
import Goose.Construct.Run
import Goose.Construct.Validate
import Goose.Construct.GIR.Json
import Goose.Construct.GIR.Run
import Goose.Construct.GIR.Validate
import Goose.Construct.TraceJson
import Goose.Share.Cli
import Goose.Lower.Commands

/-- Reserved subcommands: named so scripts can already refer to them. -/
def reserved : List String := []

def usage : String :=
  "usage: goose-semantics audit\n" ++
  "       goose-semantics run MODULE.json [--numeric release|debug] [--fuel N] [--no-validate]\n" ++
  "       goose-semantics validate MODULE.json\n" ++
  "       goose-semantics share UNSHARED.json SHARED.json\n" ++
  "       goose-semantics share --propose UNSHARED.json\n" ++
  "       goose-semantics lower CORE.json\n" ++
  "       goose-semantics gir-validate GIR.json\n" ++
  "       goose-semantics gir-reencode GIR.json\n" ++
  "       goose-semantics gir-run GIR.json [--numeric release|debug] [--fuel N] [--no-validate]\n" ++
  "       goose-semantics agree CORE.json GIR.json [--numeric release|debug] [--fuel N]"

/-- Prints one JSON line per audited theorem; fails on a wrong Lean version. -/
def runAudit : IO UInt32 := do
  if Lean.versionString != Goose.Audit.expectedLeanVersion then
    IO.eprintln s!"goose-semantics: built with Lean {Lean.versionString}, expected {Goose.Audit.expectedLeanVersion}"
    return 1
  for e in Goose.Audit.registry do
    let axs := ",".intercalate (e.axioms.map fun a => s!"\"{a}\"")
    IO.println s!"[\"{e.theoremName}\",[{axs}]]"
  return 0

/-- A command-line mistake, as opposed to a bad module: nothing on stdout. -/
def usageError (msg : String) : IO UInt32 := do
  IO.eprintln s!"goose-semantics: {msg}"
  IO.eprintln usage
  return 64

def parseRunOptions (settings : Goose.Core.Run.Settings) :
    List String → Except String Goose.Core.Run.Settings
  | [] => .ok settings
  | "--no-validate" :: rest => parseRunOptions { settings with validate := false } rest
  | "--numeric" :: v :: rest =>
    match v with
    | "release" => parseRunOptions { settings with profile := .release } rest
    | "debug" => parseRunOptions { settings with profile := .debug } rest
    | _ => .error s!"--numeric takes release or debug, not {v}"
  | "--fuel" :: v :: rest =>
    match v.toNat? with
    | some n => parseRunOptions { settings with fuel := n } rest
    | none => .error s!"--fuel takes a natural number, not {v}"
  | opt :: _ => .error s!"unexpected argument {opt}"

/-- Print the single JSON line a command produces and return its status. -/
def withModule (path : String) (go : ByteArray → String × UInt32) : IO UInt32 := do
  let (line, status) ←
    match (← Goose.Core.Run.readModule path) with
    | .error msg => pure (Goose.Core.Run.malformed msg)
    | .ok bs => pure (go bs)
  IO.println line
  return status

/-- Print the single JSON line of a command over a Core module and a GIR module. -/
def withTwoModules (corePath girPath : String) (go : ByteArray → ByteArray → String × UInt32) :
    IO UInt32 := do
  let (line, status) ←
    match (← Goose.Core.Run.readModule corePath), (← Goose.Core.Run.readModule girPath) with
    | .error msg, _ => pure (Goose.Core.Run.malformed msg)
    | _, .error msg => pure (Goose.Core.Run.malformed msg)
    | .ok c, .ok g => pure (go c g)
  IO.println line
  return status

private def moduleSchemaProfile? (bytes : ByteArray) : Option (String × String) := do
  Goose.Core.Decode.scan bytes |>.toOption
  let text ← String.fromUTF8? bytes
  let json ← (Lean.Json.parse text).toOption
  let .arr fields := json | none
  match fields[0]?, fields[1]?, fields[2]? with
  | some (Lean.Json.str kind), some (Lean.Json.str schema), some (Lean.Json.str profile) =>
      if kind == "module" then some (schema, profile) else none
  | _, _, _ => none

private def isConstructionCore (bytes : ByteArray) : Bool :=
  match moduleSchemaProfile? bytes with
  | some (schema, profile) =>
      schema == Goose.Construct.Decode.schemaName && profile == "core-construction"
  | none => false

private def isConstructionGir (bytes : ByteArray) : Bool :=
  match moduleSchemaProfile? bytes with
  | some (schema, profile) =>
      schema == Goose.Construct.GIR.Decode.schemaName && profile == "core-construction"
  | none => false

private def runCoreBytes (settings : Goose.Core.Run.Settings) (bytes : ByteArray) : String × UInt32 :=
  if isConstructionCore bytes then Goose.Construct.Run.runBytes settings bytes
  else Goose.Core.Run.runBytes settings bytes

private def validateCoreBytes (bytes : ByteArray) : String × UInt32 :=
  if isConstructionCore bytes then Goose.Construct.Run.validateBytes bytes
  else Goose.Core.Run.validateBytes bytes

private def constructionGirRejected (violation : Goose.Construct.GIR.Violation) : String × UInt32 :=
  (s!"[\"rejected\",{Goose.Core.Run.quote violation.code.tag},{Goose.Core.Run.quote violation.message}]", 5)

private def constructionGirLineOf (module : Goose.Construct.GIR.Module) (origin : Goose.Core.OriginId) : Nat :=
  match module.origins[origin]? with
  | some source => source.line
  | none => 0

private def constructionGirOutcome (module : Goose.Construct.GIR.Module) : Goose.Core.Outcome → String
  | .returned => "[\"returned\"]"
  | .aborted kind origin =>
      s!"[\"aborted\",{Goose.Core.Run.quote kind.tag},{constructionGirLineOf module origin}]"
  | .exited code => s!"[\"exited\",{code}]"

private def constructionGirBytes (bytes : ByteArray) : String :=
  Goose.Core.Writer.arr (bytes.data.toList.map fun byte => Goose.Core.Writer.nat byte.toNat)

private def constructionGirEvents (events : List Goose.Core.ConstructionEvent) : String :=
  Goose.Core.Writer.arr (events.map Goose.Construct.TraceJson.event)

private def renderConstructionGir (module : Goose.Construct.GIR.Module)
    (result : Goose.Construct.ExecutionResult) : String × UInt32 :=
  match result with
  | .done outcome stdout events =>
      (s!"[\"done\",{constructionGirOutcome module outcome},{constructionGirBytes stdout},{constructionGirEvents events}]", 0)
  | .timeout stdout events =>
      (s!"[\"timeout\",{constructionGirBytes stdout},{constructionGirEvents events}]", 3)
  | .fault kind => (s!"[\"fault\",{Goose.Core.Run.quote kind.tag}]", 4)

private def constructionGirRunBytes (settings : Goose.Core.Run.Settings) (bytes : ByteArray) : String × UInt32 :=
  match Goose.Construct.GIR.Decode.decodeBytes bytes with
  | .error message => Goose.Core.Run.malformed message
  | .ok module =>
      match (if settings.validate then Goose.Construct.GIR.Validate.validate module else .ok ()) with
      | .error violation => constructionGirRejected violation
      | .ok () => renderConstructionGir module
          (Goose.Construct.GIR.Run.run settings.fuel settings.profile module)

private def constructionGirValidateBytes (bytes : ByteArray) : String × UInt32 :=
  match Goose.Construct.GIR.Decode.decodeBytes bytes with
  | .error message => Goose.Core.Run.malformed message
  | .ok module =>
      match Goose.Construct.GIR.Validate.validate module with
      | .error violation => constructionGirRejected violation
      | .ok () => ("[\"ok\"]", 0)

private def constructionGirReencodeBytes (bytes : ByteArray) : String × UInt32 :=
  match Goose.Construct.GIR.Decode.decodeBytes bytes with
  | .error message => Goose.Core.Run.malformed message
  | .ok module => ((Goose.Construct.GIR.Writer.write module).dropEnd 1 |>.toString, 0)

private def constructionAgreeBytes (settings : Goose.Core.Run.Settings)
    (coreBytes girBytes : ByteArray) : String × UInt32 :=
  match Goose.Construct.Decode.decodeBytes coreBytes, Goose.Construct.GIR.Decode.decodeBytes girBytes with
  | .error message, _ => Goose.Core.Run.malformed s!"core module: {message}"
  | _, .error message => Goose.Core.Run.malformed s!"gir module: {message}"
  | .ok core, .ok gir =>
      match (if settings.validate then Goose.Construct.validate core else .ok ()) with
      | .error rejection => Goose.Core.Run.rejected rejection
      | .ok () =>
          match (if settings.validate then Goose.Construct.GIR.Validate.validate gir else .ok ()) with
          | .error violation => constructionGirRejected violation
          | .ok () =>
              let coreResult := Goose.Construct.eval settings.fuel settings.profile core
              let girResult := Goose.Construct.GIR.Run.run
                (settings.fuel * Goose.Lower.Commands.girFuelFactor) settings.profile gir
              match coreResult, girResult with
              | .timeout _ _, _ | _, .timeout _ _ => ("[\"inconclusive\"]", 3)
              | _, _ =>
                  let (coreLine, coreStatus) := Goose.Construct.Run.render core coreResult
                  let (girLine, girStatus) := renderConstructionGir gir girResult
                  if coreStatus == 0 && girStatus == 0 && coreLine == girLine then
                    (s!"[\"agree\",{coreLine}]", 0)
                  else (s!"[\"disagree\",{coreLine},{girLine}]", 6)

def main (args : List String) : IO UInt32 :=
  match args with
  | ["audit"] => runAudit
  | "run" :: path :: opts =>
    match parseRunOptions {} opts with
    | .error msg => usageError msg
    | .ok settings => withModule path (runCoreBytes settings)
  | ["validate", path] => withModule path validateCoreBytes
  | ["share", "--propose", path] => withModule path Goose.Share.Cli.proposeBytes
  | ["share", unshared, shared] => do
    let (line, status) ←
      match (← Goose.Core.Run.readModule unshared), (← Goose.Core.Run.readModule shared) with
      | .error msg, _ | _, .error msg => pure (Goose.Core.Run.malformed msg)
      | .ok a, .ok b => pure (Goose.Share.Cli.checkBytes a b)
    IO.println line
    return status
  | ["lower", path] => withModule path Goose.Lower.Commands.lowerBytes
  | ["gir-reencode", path] => withModule path (fun bytes =>
      if isConstructionGir bytes then constructionGirReencodeBytes bytes
      else Goose.Lower.Commands.girReencodeBytes bytes)
  | ["gir-validate", path] => withModule path (fun bytes =>
      if isConstructionGir bytes then constructionGirValidateBytes bytes
      else Goose.Lower.Commands.girValidateBytes bytes)
  | "gir-run" :: path :: opts =>
    -- Fuel counts executed instructions here, so the default budget is larger
    -- than Core's by the factor `agree` uses.
    let base : Goose.Core.Run.Settings :=
      if opts.contains "--fuel" then {}
      else { fuel := Goose.Lower.Commands.girFuelFactor * ({} : Goose.Core.Run.Settings).fuel }
    match parseRunOptions base opts with
    | .error msg => usageError msg
    | .ok settings => withModule path (fun bytes =>
        if isConstructionGir bytes then constructionGirRunBytes settings bytes
        else Goose.Lower.Commands.girRunBytes settings bytes)
  | "agree" :: corePath :: girPath :: opts =>
    match parseRunOptions {} opts with
    | .error msg => usageError msg
    | .ok settings => withTwoModules corePath girPath (fun core gir =>
        if isConstructionCore core && isConstructionGir gir then
          constructionAgreeBytes settings core gir
        else Goose.Lower.Commands.agreeBytes settings core gir)
  | [cmd] =>
    if reserved.contains cmd then do
      IO.eprintln s!"goose-semantics {cmd}: not implemented"
      return 2
    else usageError s!"unknown command {cmd}"
  | _ => usageError "unrecognized arguments"
