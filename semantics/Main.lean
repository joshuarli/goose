import Goose.Audit

/-- Reserved subcommands: named so scripts can already refer to them. -/
def reserved : List String := ["run", "validate", "share"]

def usage : String := "usage: goose-semantics audit"

/-- Prints one JSON line per audited theorem; fails on a wrong Lean version. -/
def runAudit : IO UInt32 := do
  if Lean.versionString != Goose.Audit.expectedLeanVersion then
    IO.eprintln s!"goose-semantics: built with Lean {Lean.versionString}, expected {Goose.Audit.expectedLeanVersion}"
    return 1
  for e in Goose.Audit.registry do
    let axs := ",".intercalate (e.axioms.map fun a => s!"\"{a}\"")
    IO.println s!"[\"{e.theoremName}\",[{axs}]]"
  return 0

def main (args : List String) : IO UInt32 :=
  match args with
  | ["audit"] => runAudit
  | [cmd] =>
    if reserved.contains cmd then do
      IO.eprintln s!"goose-semantics {cmd}: not implemented"
      return 2
    else do
      IO.eprintln usage
      return 2
  | _ => do
    IO.eprintln usage
    return 2
