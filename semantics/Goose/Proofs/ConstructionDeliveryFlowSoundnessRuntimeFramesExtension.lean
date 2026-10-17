import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesOwners

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem breakFrame_restoreOwnerRow (snapshot : PendingDestination) :
    BreakFrameAction (do
      let state ← EvalM.get
      EvalM.set { state with construction := { state.construction with
        destinations := state.construction.destinations.set! snapshot.capability.id snapshot } }) := by
  intro state _
  exact ⟨Nat.le_refl _, rfl⟩

private theorem breakFrame_conditional (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (left : BreakFrameAction yes) (right : BreakFrameAction no) :
    BreakFrameAction (if condition then yes else no) := by
  split <;> assumption

local elab "frame_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``BreakFrameAction do throwError "expected break frame"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_conditional))

local elab "frame_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

local elab "frame_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``BreakFrameAction do throwError "expected break frame"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet do throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

local macro "copy_frame_step" : tactic => `(tactic|
  first
    | exact breakFrame_restoreOwnerRow _
    | exact breakFrame_pure _
    | exact breakFrame_stop _
    | exact breakFrame_get
    | exact breakFrame_getDestination _
    | exact breakFrame_getStorage _
    | exact breakFrame_receivingLayout _ _
    | exact breakFrame_liftExcept _
    | exact breakFrame_liftLayout _
    | (with_reducible apply breakFrame_liftConstruction)
    | exact breakFrame_writeLoc _ _ _ _
    | exact breakFrame_newDestination _ _ _ _ _ _ _
    | exact breakFrame_completedDestination _
    | exact breakFrame_publishCarriers _ _
    | exact breakFrame_readLoc _ _ _
    | exact breakFrame_sampledStored _
    | exact breakFrame_storedPathRun _
    | exact breakFrame_completedReceivingDestination _
    | exact breakFrame_storedDestination _
    | (with_reducible apply breakFrame_arrayForIn)
    | (with_reducible apply breakFrame_rangeForIn)
    | (with_reducible apply breakFrame_bind)
    | (with_reducible apply breakFrame_listForIn)
    | (with_reducible apply breakFrame_listMapM)
    | frame_conditional
    | frame_zeta
    | frame_intro
    | split
    | unfold receivingDestination)

local macro "copy_frame" : tactic => `(tactic| repeat' copy_frame_step)

theorem breakFrame_restoreCompletedOwner (snapshot : PendingDestination) (incoming : Goose.Core.DestinationId)
    (carried : List Goose.Core.DestinationId) :
    BreakFrameAction (restoreCompletedOwner snapshot incoming carried) := by
  unfold restoreCompletedOwner
  copy_frame

def ownerExtensionGuard (snapshot : Option PendingDestination) (destination : Goose.Core.DestinationId)
    (action : EvalM α) : EvalM α := fun state =>
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
  match action state with
  | .escape target carriers state' => finish carriers (.escape target carriers) state'
  | .jump target kind state' =>
      finish (match kind with | .breakValue carriers => carriers | .continueLoop => [])
        (.jump target kind) state'
  | result => result

theorem breakFrame_ownerExtensionGuard (snapshot : Option PendingDestination) (destination : Goose.Core.DestinationId)
    (action : EvalM α) (body : BreakFrameAction action) : BreakFrameAction (ownerExtensionGuard snapshot destination action) := by
  intro state bounded
  have checked := body state bounded
  cases evaluated : action state with
  | ok value middle =>
      simpa only [ownerExtensionGuard, evaluated] using checked
  | stop reason middle =>
      simpa only [ownerExtensionGuard, evaluated] using checked
  | escape address carriers middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      cases snapshot with
      | none =>
          simp only [ownerExtensionGuard, evaluated]
          change BreakStackFrame state middle
          exact checked
      | some parent =>
          have restoredFrame := breakFrame_restoreCompletedOwner parent destination
            (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none)
            middle (checked.bounded bounded)
          cases restored : restoreCompletedOwner parent destination
              (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) middle <;>
            simp only [restored] at restoredFrame
          all_goals change BreakStackFrame middle _ at restoredFrame
          all_goals simp only [ownerExtensionGuard, evaluated, restored]
          all_goals change BreakStackFrame state _
          all_goals exact checked.trans restoredFrame
  | jump target kind middle =>
      simp only [evaluated] at checked
      change BreakStackFrame state middle at checked
      cases snapshot with
      | none =>
          simp only [ownerExtensionGuard, evaluated]
          change BreakStackFrame state middle
          exact checked
      | some parent =>
          cases kind with
          | breakValue carriers =>
              have restoredFrame := breakFrame_restoreCompletedOwner parent destination
                (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none)
                middle (checked.bounded bounded)
              cases restored : restoreCompletedOwner parent destination
                  (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none) middle <;>
                simp only [restored] at restoredFrame
              all_goals change BreakStackFrame middle _ at restoredFrame
              all_goals simp only [ownerExtensionGuard, evaluated, restored]
              all_goals change BreakStackFrame state _
              all_goals exact checked.trans restoredFrame
          | continueLoop =>
              have restoredFrame := breakFrame_restoreCompletedOwner parent destination
                (([] : List Carrier).filterMap fun carrier => match carrier with | .completed id => some id | _ => none)
                middle (checked.bounded bounded)
              cases restored : restoreCompletedOwner parent destination
                  (([] : List Carrier).filterMap fun carrier => match carrier with | .completed id => some id | _ => none) middle <;>
                simp only [restored] at restoredFrame
              all_goals change BreakStackFrame middle _ at restoredFrame
              all_goals simp only [ownerExtensionGuard, evaluated, restored]
              all_goals change BreakStackFrame state _
              all_goals exact checked.trans restoredFrame

theorem breakFrame_withOwnerExtension (stored : StoredValue) (allocate : EvalM Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) (allocation : BreakFrameAction allocate)
    (body : ∀ destination, BreakFrameAction (action destination)) :
    BreakFrameAction (withOwnerExtension stored allocate action) := by
  change BreakFrameAction (do
    let snapshot ← match stored.destination with
      | none => pure none
      | some id => do
          let parent ← getDestination id
          pure (match parent.progress with | .built _ => some parent | _ => none)
    let destination ← allocate
    ownerExtensionGuard snapshot destination (action destination))
  repeat' first
    | exact allocation
    | apply breakFrame_ownerExtensionGuard; exact body _
    | copy_frame_step

#print axioms breakFrame_restoreCompletedOwner
#print axioms breakFrame_withOwnerExtension

end Goose.Proofs.ConstructionDelivery
