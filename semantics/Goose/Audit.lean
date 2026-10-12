import Lean
import Goose.Proofs.Num
import Goose.Proofs.Share
import Goose.Reuse.Model

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

#audit Goose.Proofs.Num.wrap_inRange
#audit Goose.Proofs.Num.wrap_congr
#audit Goose.Proofs.Num.wrap_of_inRange
#audit Goose.Proofs.Num.checked_release
#audit Goose.Proofs.Num.checked_unsigned
#audit Goose.Proofs.Num.checked_debug_signed
#audit Goose.Proofs.Num.checked_inRange
#audit Goose.Proofs.Num.add_release
#audit Goose.Proofs.Num.sub_release
#audit Goose.Proofs.Num.mul_release
#audit Goose.Proofs.Num.neg_release
#audit Goose.Proofs.Num.add_unsigned
#audit Goose.Proofs.Num.sub_unsigned
#audit Goose.Proofs.Num.mul_unsigned
#audit Goose.Proofs.Num.neg_unsigned
#audit Goose.Proofs.Num.add_debug_signed
#audit Goose.Proofs.Num.sub_debug_signed
#audit Goose.Proofs.Num.mul_debug_signed
#audit Goose.Proofs.Num.neg_debug_signed
#audit Goose.Proofs.Num.div_zero
#audit Goose.Proofs.Num.div_inRange
#audit Goose.Proofs.Num.div_i64_min
#audit Goose.Proofs.Num.div_narrow_min_debug
#audit Goose.Proofs.Num.div_narrow_min_release
#audit Goose.Proofs.Num.mod_zero
#audit Goose.Proofs.Num.mod_spec
#audit Goose.Proofs.Num.mod_inRange
#audit Goose.Proofs.Num.shl_eq
#audit Goose.Proofs.Num.shr_eq
#audit Goose.Proofs.Num.shift_count_only
#audit Goose.Proofs.Num.shr_inRange
#audit Goose.Proofs.Num.ofBits_inRange
#audit Goose.Proofs.Num.bitwise_inRange
#audit Goose.Proofs.Num.bitnot_inRange
#audit Goose.Proofs.Num.widen_id
#audit Goose.Proofs.Num.asUnchecked_wrap
#audit Goose.Proofs.Num.as_release_wrap
#audit Goose.Proofs.Num.as_debug
#audit Goose.Proofs.Num.evalUn_inRange
#audit Goose.Proofs.Num.evalBin_inRange
#audit Goose.Proofs.Num.evalConv_inRange

#audit Goose.Proofs.Share.eval_erase_roots
#audit Goose.Proofs.Share.eval_eraseRoots
#audit Goose.Proofs.Share.eval_simulates
#audit Goose.Proofs.Share.share_eval
#audit Goose.Proofs.Share.quotient_of_implwise
#audit Goose.Proofs.Share.share_never_faults
#audit Goose.Proofs.Share.share_validated_never_faults
#audit Goose.Proofs.Share.checkQuotient_sound
#audit Goose.Proofs.Share.eqImpl_sound

#audit Goose.Reuse.cachedRun_result
#audit Goose.Reuse.cachedRun_consistent
#audit Goose.Reuse.cachedRuns_agree
#audit Goose.Reuse.cachedRuns_agree_from
#audit Goose.Reuse.cachedRun₂_result
#audit Goose.Reuse.cachedRuns₂_agree
#audit Goose.Reuse.wrong_answer_without_key_determination
#audit Goose.Reuse.key_omission_example

#audit_registry
