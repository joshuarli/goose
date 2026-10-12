import Goose.Audit
import Goose.Core.Run
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

def main (args : List String) : IO UInt32 :=
  match args with
  | ["audit"] => runAudit
  | "run" :: path :: opts =>
    match parseRunOptions {} opts with
    | .error msg => usageError msg
    | .ok settings => withModule path (Goose.Core.Run.runBytes settings)
  | ["validate", path] => withModule path Goose.Core.Run.validateBytes
  | ["share", "--propose", path] => withModule path Goose.Share.Cli.proposeBytes
  | ["share", unshared, shared] => do
    let (line, status) ←
      match (← Goose.Core.Run.readModule unshared), (← Goose.Core.Run.readModule shared) with
      | .error msg, _ | _, .error msg => pure (Goose.Core.Run.malformed msg)
      | .ok a, .ok b => pure (Goose.Share.Cli.checkBytes a b)
    IO.println line
    return status
  | ["lower", path] => withModule path Goose.Lower.Commands.lowerBytes
  | ["gir-validate", path] => withModule path Goose.Lower.Commands.girValidateBytes
  | "gir-run" :: path :: opts =>
    match parseRunOptions {} opts with
    | .error msg => usageError msg
    | .ok settings => withModule path (Goose.Lower.Commands.girRunBytes settings)
  | "agree" :: corePath :: girPath :: opts =>
    match parseRunOptions {} opts with
    | .error msg => usageError msg
    | .ok settings => withTwoModules corePath girPath (Goose.Lower.Commands.agreeBytes settings)
  | [cmd] =>
    if reserved.contains cmd then do
      IO.eprintln s!"goose-semantics {cmd}: not implemented"
      return 2
    else usageError s!"unknown command {cmd}"
  | _ => usageError "unrecognized arguments"
