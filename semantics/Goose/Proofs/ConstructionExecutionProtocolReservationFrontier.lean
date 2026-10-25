import Goose.Proofs.ConstructionExecutionProtocolExitFrames
import Lean

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

open Lean Elab Term Meta in
elab "exit_frontier_head" : term => do
  let declaration ← getConstInfo ``Goose.Construct.exitFrontier_open
  forallTelescope declaration.type fun _ body => do
    let arguments := body.getAppArgs
    unless body.getAppFn.isConstOf ``Eq && arguments.size == 3 do
      throwError "expected an exit frontier result equation"
    return arguments[1]!.getAppFn

abbrev exitFrontierAction : Nat → DestinationId → ConstructionM DestinationId := exit_frontier_head

private abbrev lookupStep (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

theorem exitFrontierAction_zero (id : DestinationId) :
    exitFrontierAction 0 id = ConstructionM.fail .ownership := rfl

theorem exitFrontierAction_succ (fuel : Nat) (id : DestinationId) :
    exitFrontierAction (fuel + 1) id = (do
      let destination ← lookupStep id
      match destination.progress with
      | .exiting _ replacement =>
          let selected ← lookupStep replacement
          if selected.use != .replacement id then ConstructionM.fail .ownership
          exitFrontierAction fuel replacement
      | _ => pure id) := rfl

private theorem lookupStep_finalState (id : DestinationId) (state : ConstructionState) :
    (lookupStep id state).finalState = state := by
  simp only [lookupStep, lookupDestination_result]
  cases state.destinations[id]? <;> rfl

private theorem query_bind (action : ConstructionM α) (next : α → ConstructionM β)
    (first : ∀ state, (action state).finalState = state)
    (remaining : ∀ value state, (next value state).finalState = state)
    (state : ConstructionState) : ((action >>= next) state).finalState = state := by
  have frame := first state
  cases evaluated : action state with
  | fault reason final => simpa only [evaluated, bind, ConstructionResult.finalState] using frame
  | ok value final =>
      simp only [evaluated, ConstructionResult.finalState] at frame
      subst final
      simpa only [evaluated, bind] using remaining value state

theorem exitFrontierAction_finalState (fuel : Nat) (id : DestinationId) (state : ConstructionState) :
    (exitFrontierAction fuel id state).finalState = state := by
  induction fuel generalizing id state with
  | zero => rfl
  | succ fuel ih =>
      rw [exitFrontierAction_succ]
      apply query_bind
      · exact lookupStep_finalState id
      · intro destination current
        cases destination.progress <;> try rfl
        rename_i count replacement
        apply query_bind
        · exact lookupStep_finalState replacement
        · intro selected after
          split
          · rfl
          · exact ih replacement after

end Goose.Proofs.ConstructionExecutionProtocol
