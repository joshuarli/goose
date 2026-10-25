import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlActions
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl

open Goose.Core Goose.Core.Sound Goose.GIR ReturnFrames

def blockSetup (scope : ScopeId) (bindings : List (SlotId × ValueId × OriginId)) : B Unit := do
  emitEffect (.enter scope)
  pushScope scope
  initSlots bindings

theorem block_origin {sourceEnv : TEnv} {typedPre : List (VarId × Ty)} {scope : ScopeId}
    {statements : List Stmt} {value : Option Expr} {type : Ty} {start finish : Nat}
    {env : LEnv} {initial final : LS} {result : ValueId} {values : List ValueId} {origin : Option OriginId}
    (loop : Option LoopCtx) (bindings : List (SlotId × ValueId × OriginId)) (want : Bool)
    (source : Core.tyBlock sourceEnv typedPre (.mk scope statements value) start = .ok (type, finish))
    (run : lowerBlock loop bindings want (.mk scope statements value) env initial = (result, final))
    (member : .term (.ret values origin) ∈ final.insts) :
    Nonempty (ReturnCheckpoint (blockSetup scope bindings) (fun _ => lowerStmts loop statements)
      env initial values origin) := by
  obtain ⟨_, _, _, _, _, _, _, typedValue⟩ := tyBlock_ok sourceEnv typedPre scope statements value start type finish source
  have free : ReturnFreeValue value := by
    cases value with
    | none => trivial
    | some expression => exact tyExpr_returnFree expression typedValue
  exact ReturnCheckpoint.of_suffix (head := blockSetup scope bindings)
    (child := fun _ => lowerStmts loop statements)
    (suffix := fun _ _ => do
      let returned ← lowerBlockValue want value
      emitEffect (.leave scope)
      popScope
      pure returned)
    (fun _ _ => frame _ (fun _ =>
      ReturnAbsentRun.bind (returnAbsent_lowerBlockValue want value free) fun _ =>
      ReturnAbsentRun.bind (returnAbsent_emitEffect _) fun _ =>
      ReturnAbsentRun.bind (ReturnAbsentRun.of_blocks (fun env state => by rw [popScope_run])) fun _ => returnAbsent_pure _))
    (by simpa only [lowerBlock, blockSetup, inScope, bind_run, pure_run] using run) member

end Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl
