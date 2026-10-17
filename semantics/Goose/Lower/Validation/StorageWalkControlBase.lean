import Goose.Lower.Validation.StorageWalkActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkAction.whenLive {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (default : α) {body : BlockId → B α}
    (bodyAction : ∀ block, StorageWalkAction slots stack loop (body block)) :
    StorageWalkAction slots stack loop (Goose.Lower.whenLive default body) := by
  unfold Goose.Lower.whenLive
  apply (StorageWalkAction.curBlock slots stack loop).bind
  intro current
  cases current with
  | none => exact .pure slots stack loop default
  | some block => exact bodyAction block

end Goose.Lower.Validation
