import Goose.Lower.Validation.SummaryPreservationReturnLedgerControlSetups

namespace Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl

open Goose.Core Goose.GIR

def eachElementSetup (x : VarId) (index : Option VarId) (byRef : Bool) (origin : OriginId)
    (arguments : ValueId × ValueId × BlockId × Nat × BlockId) : B (List (SlotId × ValueId × OriginId)) := do
  let element ← emitDef (.refElem arguments.1 arguments.2.1)
  let value ← eachElemValue x byRef element
  pure ((x, value, origin) :: (match index with
    | some slot => [(slot, arguments.2.1, origin)]
    | none => []))

theorem each_body_checkpoint {x : VarId} {index : Option VarId} {byRef : Bool}
    {body : Core.Block} {sourceOrigin : OriginId} {view : View}
    {env : LEnv} {initial : LS} {values : List ValueId} {origin : Option OriginId}
    (checkpoint : ActiveReturnCheckpoint (eachSetup view) (eachBody x index byRef body sourceOrigin) env initial values origin) :
    ∃ bodyCheckpoint : ReturnCheckpoint (eachElementSetup x index byRef sourceOrigin checkpoint.argument)
      (fun bindings => lowerBlock
        (some ⟨checkpoint.argument.2.2.2.1, checkpoint.argument.2.2.2.2,
          .next checkpoint.argument.2.2.1 .i64 checkpoint.argument.2.1⟩)
        bindings false body) env checkpoint.before values origin, bodyCheckpoint.after = checkpoint.after := by
  have run := checkpoint.childRun
  simp only [eachBody, bind_eq] at run
  obtain ⟨element, elementState, elementRun, value, valueState, valueRun, blockRun⟩ := run
  refine ⟨⟨_, valueState, checkpoint.value, checkpoint.after, ?_, blockRun, checkpoint.member⟩, rfl⟩
  simp only [eachElementSetup, bind_run, elementRun, valueRun, pure_run]
  rfl

end Goose.Lower.Validation.SummaryPreservation.ReturnLedgerControl
