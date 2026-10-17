import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsCleanup

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem neverJumps_restoreOwnerRow (snapshot : PendingDestination) :
    NeverJumps (do
      let state ← EvalM.get
      EvalM.set { state with construction := { state.construction with
        destinations := state.construction.destinations.set! snapshot.capability.id snapshot } }) := by
  intro state target kind after impossible
  cases impossible

local elab "noJump_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``NeverJumps do throwError "expected jump exclusion"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply neverJumps_conditional))

local elab "noJump_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

local elab "noJump_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``NeverJumps do throwError "expected jump exclusion"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet do throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

local macro "copy_noJump_step" : tactic => `(tactic|
  first
    | exact neverJumps_restoreOwnerRow _
    | exact neverJumps_pure _
    | exact neverJumps_stop _
    | exact neverJumps_get
    | exact neverJumps_getDestination _
    | exact neverJumps_getStorage _
    | exact neverJumps_receivingLayout _ _
    | exact neverJumps_liftExcept _
    | exact neverJumps_liftLayout _
    | (with_reducible apply neverJumps_lift)
    | exact neverJumps_writeLoc _ _ _ _
    | exact neverJumps_newDestination _ _ _ _ _ _ _
    | exact neverJumps_completedDestination _
    | exact neverJumps_publishCarriers _ _
    | exact neverJumps_readLoc _ _ _
    | exact neverJumps_sampledStored _
    | exact neverJumps_storedPathRun _
    | exact neverJumps_completedReceivingDestination _
    | exact neverJumps_storedDestination _
    | (with_reducible apply neverJumps_arrayForIn)
    | (with_reducible apply neverJumps_rangeForIn)
    | (with_reducible apply neverJumps_bind)
    | (with_reducible apply neverJumps_forIn)
    | (with_reducible apply neverJumps_listMapM)
    | noJump_conditional
    | noJump_zeta
    | noJump_intro
    | split
    | unfold receivingDestination)

local macro "copy_noJump" : tactic => `(tactic| repeat' copy_noJump_step)

theorem neverJumps_restoreCompletedOwner (snapshot : PendingDestination) (incoming : Goose.Core.DestinationId)
    (carried : List Goose.Core.DestinationId) :
    NeverJumps (restoreCompletedOwner snapshot incoming carried) := by
  unfold restoreCompletedOwner
  copy_noJump

theorem neverJumps_withOwnerExtension (stored : StoredValue) (allocate : EvalM Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) (allocation : NeverJumps allocate)
    (body : ∀ destination, NeverJumps (action destination)) :
    NeverJumps (withOwnerExtension stored allocate action) := by
  let guarded (snapshot : Option PendingDestination) (destination : Goose.Core.DestinationId) : EvalM α := fun state =>
    let finish := fun (carriers : List Carrier) (result : ExecutionState → ExecutionStep α) (state' : ExecutionState) =>
      match snapshot with
      | none => result state'
      | some parent =>
          match restoreCompletedOwner parent destination
              (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) state' with
          | .ok () final => result final
          | .stop reason final => .stop reason final
          | .escape target carriers final => .escape target carriers final
          | .jump target kind final => .jump target kind final
    match action destination state with
    | .escape target carriers state' => finish carriers (.escape target carriers) state'
    | .jump target kind state' =>
        finish (match kind with | .breakValue carriers => carriers | .continueLoop => [])
          (.jump target kind) state'
    | result => result
  have guardExclusion : ∀ snapshot destination, NeverJumps (guarded snapshot destination) := by
    intro snapshot destination state target kind after impossible
    dsimp only [guarded] at impossible
    cases evaluated : action destination state with
    | ok value middle => simp only [evaluated] at impossible; cases impossible
    | stop reason middle => simp only [evaluated] at impossible; cases impossible
    | escape address carriers middle =>
        cases snapshot with
        | none => simp only [evaluated] at impossible; cases impossible
        | some parent =>
            cases restored : restoreCompletedOwner parent destination
                (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) middle <;>
              simp only [evaluated, restored] at impossible <;> try cases impossible
            exact neverJumps_restoreCompletedOwner _ _ _ _ _ _ _ restored
    | jump target kind middle => exact body destination state target kind middle evaluated
  change NeverJumps (do
    let snapshot ← match stored.destination with
      | none => pure none
      | some id => do
          let parent ← getDestination id
          pure (match parent.progress with | .built _ => some parent | _ => none)
    let destination ← allocate
    guarded snapshot destination)
  repeat' first
    | exact allocation
    | exact guardExclusion _ _
    | copy_noJump_step

#print axioms neverJumps_restoreCompletedOwner
#print axioms neverJumps_withOwnerExtension

end Goose.Proofs.ConstructionDelivery
