import Lean
import Goose.Proofs.Num

/-!
Axiom audit for the theorems the semantics claims.

`#audit thm` fails elaboration unless `thm` is a theorem whose transitive
axioms are all in `allowedAxioms`. It is an allowlist because `bv_decide` and
`native_decide` introduce a fresh axiom per theorem and `sorry` introduces
`sorryAx`; none of those can be named in a denylist.

Each `#audit` also defines a constant under `Goose.Audit.entry`, and
`#audit_registry` collects those constants into `Goose.Audit.registry` so the
`goose-semantics audit` executable can print what was audited. A theorem that
is not named by `#audit` is not audited.
-/

namespace Goose.Audit

/-- The Lean release the semantics is built and audited with. -/
def expectedLeanVersion : String := "4.34.1"

structure Entry where
  theoremName : String
  axioms : List String

/-- The only axioms a listed theorem may depend on. -/
def allowedAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

open Lean Elab Command

/-- Sorted names of the axioms `declName` depends on, transitively. -/
def axiomsOf (declName : Name) : CommandElabM (List String) := do
  let axs ← liftCoreM (collectAxioms declName)
  return (axs.toList.map toString).mergeSort (· ≤ ·)

/-- `#audit thm` checks that `thm` is a theorem using only allowed axioms. -/
syntax (name := auditCmd) "#audit " ident : command

@[command_elab auditCmd]
def elabAudit : CommandElab
  | `(#audit $id:ident) => do
    let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    match (← getEnv).find? declName with
    | some (.thmInfo _) => pure ()
    | some _ => throwErrorAt id "#audit: {declName} is not a theorem"
    | none => throwErrorAt id "#audit: unknown constant {declName}"
    let axs ← axiomsOf declName
    let bad := axs.filter (fun a => !allowedAxioms.contains a)
    unless bad.isEmpty do
      throwErrorAt id
        "#audit: {declName} depends on disallowed axiom(s): {", ".intercalate bad}"
    let entryName := `Goose.Audit.entry ++ declName
    let entryId := mkIdent entryName
    let nameLit := Syntax.mkStrLit (toString declName)
    let axLits := axs.map Syntax.mkStrLit |>.toArray
    elabCommand (← `(def $entryId : Goose.Audit.Entry :=
      { theoremName := $nameLit, axioms := [$axLits,*] }))
  | _ => throwUnsupportedSyntax

/-- `#audit_registry` defines `Goose.Audit.registry` from every `#audit` so far. -/
syntax (name := auditRegistryCmd) "#audit_registry" : command

@[command_elab auditRegistryCmd]
def elabAuditRegistry : CommandElab
  | `(#audit_registry) => do
    let entries := (← getEnv).constants.map₂.foldl
      (fun acc n _ => if `Goose.Audit.entry |>.isPrefixOf n then n :: acc else acc) []
    let sorted := entries.mergeSort (fun a b => toString a ≤ toString b)
    let ids := sorted.map mkIdent |>.toArray
    let registryId := mkIdent `Goose.Audit.registry
    elabCommand (← `(def $registryId : List Goose.Audit.Entry := [$ids,*]))
  | _ => throwUnsupportedSyntax

end Goose.Audit

#audit Goose.Proofs.Num.emod_range

#audit_registry
