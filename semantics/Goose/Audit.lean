import Lean
import Goose.Proofs.Num
import Goose.Proofs.Share
import Goose.Reuse.Model
import Goose.Proofs.Lower
import Goose.Lower.Loops
import Goose.Lower.While
import Goose.Lower.Prefix
import Goose.GIR.Sound
import Goose.Proofs.Fuel
import Goose.Proofs.GIRFuel
import Goose.Proofs.Bounds
import Goose.Proofs.Memory
import Goose.Proofs.Core
import Goose.Proofs.Safety
import Goose.Lower.Bindings
import Goose.Lower.Lifetime
import Goose.Lower.Unwind
import Goose.Evidence.Provenance
import Goose.Evidence.SSA
import Goose.Evidence.Simulation
import Goose.Evidence.SimulationChecks
import Goose.Proofs.Construct
import Goose.Proofs.Exit

/-!
Axiom audit for the theorems the semantics claims.

`#audit thm` fails elaboration unless `thm` is a theorem whose transitive
axioms are all in `allowedAxioms`. It is an allowlist because `bv_decide` and
`native_decide` introduce a fresh axiom per theorem and `sorry` introduces
`sorryAx`; none of those can be named in a denylist.

Each `#audit` also defines a constant under `Goose.Audit.entry`, and
`#audit Goose.Evidence.RuntimePoint.typed
#audit Goose.Evidence.validated_true_cmp_fact
#audit Goose.Proofs.Bounds.validated_trueComparisonFacts
#audit Goose.Proofs.Bounds.checked_fuel
#audit Goose.Proofs.Bounds.checked_initGlobals
#audit Goose.Proofs.Bounds.SimulationChecks.fixture_run_replacement

#audit_registry` collects those constants into `Goose.Audit.registry` so the
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

/-- `#audit Goose.Evidence.RuntimePoint.typed
#audit Goose.Evidence.validated_true_cmp_fact
#audit Goose.Proofs.Bounds.validated_trueComparisonFacts
#audit Goose.Proofs.Bounds.checked_fuel
#audit Goose.Proofs.Bounds.checked_initGlobals
#audit Goose.Proofs.Bounds.SimulationChecks.fixture_run_replacement

#audit_registry` defines `Goose.Audit.registry` from every `#audit` so far. -/
syntax (name := auditRegistryCmd) "#audit Goose.Evidence.RuntimePoint.typed
#audit Goose.Evidence.validated_true_cmp_fact
#audit Goose.Proofs.Bounds.validated_trueComparisonFacts
#audit Goose.Proofs.Bounds.checked_fuel
#audit Goose.Proofs.Bounds.checked_initGlobals
#audit Goose.Proofs.Bounds.SimulationChecks.fixture_run_replacement

#audit_registry" : command

@[command_elab auditRegistryCmd]
def elabAuditRegistry : CommandElab
  | `(#audit Goose.Evidence.RuntimePoint.typed
#audit Goose.Evidence.validated_true_cmp_fact
#audit Goose.Proofs.Bounds.validated_trueComparisonFacts
#audit Goose.Proofs.Bounds.checked_fuel
#audit Goose.Proofs.Bounds.checked_initGlobals
#audit Goose.Proofs.Bounds.SimulationChecks.fixture_run_replacement

#audit_registry) => do
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
#audit Goose.Proofs.Fuel.eval_fuel_mono
#audit Goose.Proofs.GIRFuel.run_nonTimeout_fuel_mono

#audit Goose.Proofs.Memory.fields_get
#audit Goose.Proofs.Memory.FieldPath.get
#audit Goose.Proofs.Memory.FieldPath.append
#audit Goose.Proofs.Memory.LocTy.fieldPath
#audit Goose.Proofs.Memory.fields_set
#audit Goose.Proofs.Memory.flat_record_set
#audit Goose.Proofs.Memory.fields_swap
#audit Goose.Proofs.Memory.fields_refines
#audit Goose.Proofs.Memory.get_record
#audit Goose.Proofs.Memory.get_cons_children
#audit Goose.Proofs.Memory.modifyAt_cons_held
#audit Goose.Core.Sound.LocOk.fieldPath
#audit Goose.Core.Sound.structDef_ok
#audit Goose.Core.Sound.structField_ok
#audit Goose.Core.Sound.struct_exprs_spec
#audit Goose.Core.Sound.step_place
#audit Goose.Core.Sound.step_expr_b

#audit Goose.Proofs.Memory.th_mem_01
#audit Goose.Proofs.Memory.append_le
#audit Goose.Proofs.Memory.write_le

#audit Goose.Proofs.Memory.liveRefs_write
#audit Goose.Proofs.Memory.liveRefs_append
#audit Goose.Proofs.Memory.liveRefs_introduce
#audit Goose.Proofs.Memory.liveRefs_release
#audit Goose.Proofs.Memory.releaseScope_roots
#audit Goose.Proofs.Memory.storeLe_release

#audit Goose.Proofs.Core.validate_entry_shape
#audit Goose.Proofs.Core.initial_liveRefs

#audit Goose.Proofs.Lower.lower_correct_ctl
#audit Goose.Lower.claims
#audit Goose.Lower.blockPreClaim
#audit Goose.Lower.stmt_while_sim
#audit Goose.Lower.while_sim
#audit Goose.Lower.range_sim
#audit Goose.Lower.range_reentry_keeps_prefix
#audit Goose.Lower.range_reentry_changes_counter
#audit Goose.Lower.lowerBlock_v001_symbolRun
#audit Goose.Lower.lowerExpr_ifE_v001_symbolRunAt
#audit Goose.GIR.validate_sound
#audit Goose.GIR.validated_scalar_safe
#audit Goose.Proofs.Bounds.checkEvidence_sound
#audit Goose.Proofs.Bounds.f_const_sound
#audit Goose.Proofs.Bounds.f_len_sound
#audit Goose.Proofs.Bounds.f_snap_sound
#audit Goose.Proofs.Bounds.f_cmp_sound
#audit Goose.Proofs.Bounds.provesIndex_sound
#audit Goose.Proofs.Bounds.indexProven_eq_checked_of_facts
#audit Goose.Proofs.Bounds.exec_indexProven_eq_checked

#audit Goose.Core.Sound.validate_modOk
#audit Goose.Core.Sound.specs_all
#audit Goose.Proofs.Safety.validated_context_sound
#audit Goose.Proofs.Safety.validated_steps_keep_invariant
#audit Goose.Proofs.Safety.validated_run_keeps_globals_typed
#audit Goose.Core.Sound.noReturn_sound
#audit Goose.Proofs.Safety.validated_never_faults
#audit Goose.Proofs.Safety.validated_faultFree

#audit Goose.Lower.stmt_range_sim
#audit Goose.Lower.tyStmt_range_scope
#audit Goose.Lower.tyStmt_range_children
#audit Goose.Lower.stmt_range_sim_of_typed
#audit Goose.Lower.RetainedOperandsAt.retained
#audit Goose.Lower.Rel.demanded_slot_read
#audit Goose.Lower.RunAliasAt.read_safe
#audit Goose.Lower.leaveAll_sim
#audit Goose.Lower.leaveTo_sim
#audit Goose.Lower.releaseScopes_repeat_subset
#audit Goose.Evidence.RuntimePoint.cell_source
#audit Goose.Evidence.RuntimePoint.def_cell_sample
#audit Goose.Evidence.RuntimeStepsAvoid.protect
#audit Goose.Evidence.validated_cmp_operand_types
#audit Goose.Evidence.validated_cmp_distinct
#audit Goose.GIR.validated_definitions_nodup
#audit Goose.GIR.validated_defOp_not_param
#audit Goose.GIR.validated_instAt_defOp_eq
#audit Goose.Proofs.Bounds.transfer_def_sound
#audit Goose.Proofs.Bounds.transfer_effect_sound
#audit Goose.Proofs.Bounds.cmp_true_facts
#audit Goose.Proofs.Bounds.reachable_facts
#audit Goose.Proofs.Bounds.reachable_index
#audit Goose.Proofs.Bounds.checked_runModule
#audit Goose.Proofs.Bounds.checked_run

#audit Goose.Proofs.Exit.plan_nearest
#audit Goose.Proofs.Exit.unwind_frame
#audit Goose.Proofs.Exit.unwind_removes
#audit Goose.Proofs.Exit.unwind_preserves_output
#audit Goose.Proofs.Construct.landing_preserves_prefix
#audit Goose.Proofs.Construct.landing_preserves_payload
#audit Goose.Proofs.Construct.landing_top
#audit Goose.Proofs.Construct.terminal_keeps_prefix
#audit Goose.Proofs.Construct.terminal_skips_remaining
#audit Goose.Evidence.validated_cell_definition

#audit Goose.Evidence.RuntimePoint.typed
#audit Goose.Evidence.validated_true_cmp_fact
#audit Goose.Proofs.Bounds.validated_trueComparisonFacts
#audit Goose.Proofs.Bounds.checked_fuel
#audit Goose.Proofs.Bounds.checked_initGlobals
#audit Goose.Proofs.Bounds.SimulationChecks.fixture_run_replacement

#audit_registry
