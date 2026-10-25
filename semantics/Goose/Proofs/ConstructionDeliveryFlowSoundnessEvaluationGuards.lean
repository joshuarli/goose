import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValuesHelpers
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesCleanup
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesExtension

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem controlFlow_cleanup (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (before middle : ExecutionState) (cleanup : EvalM Unit) (resume : ExecutionState → ExecutionStep α)
    (resumed : ∀ after, ControlFlowOutcome activation before allowed resultFlow (resume after))
    (noJump : NeverJumps cleanup) :
    ControlFlowOutcome activation before allowed resultFlow (match cleanup middle with
      | .ok () after => resume after
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers after
      | .jump target kind after => .jump target kind after) := by
  cases result : cleanup middle with
  | ok value after => cases value; exact resumed after
  | stop reason after => trivial
  | escape address carriers after => trivial
  | jump id kind after => exact False.elim (noJump middle id kind after result)

theorem controlFlow_protectDestination (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId)
    (allowed : List StaticFlow) (resultFlow : α → StaticFlow) (action : EvalM α)
    (body : ControlFlowAction activation allowed resultFlow action) :
    ControlFlowAction activation allowed resultFlow (protectDestination origin id action) := by
  refine ⟨breakFrame_protectDestination origin id action body.frame, ?_⟩
  intro before bounded
  have reached := body.outcome before bounded
  cases evaluated : action before with
  | ok value after => simpa only [protectDestination, evaluated, ControlFlowOutcome] using reached
  | stop reason after => simp only [protectDestination, evaluated, ControlFlowOutcome]
  | escape address carriers middle =>
      simp only [protectDestination, evaluated]
      apply controlFlow_cleanup
      · intro after; trivial
      · exact neverJumps_cleanupReceivingDestination _ _ _
  | jump id kind middle =>
      simp only [evaluated, ControlFlowOutcome] at reached
      cases kind <;> simp only [protectDestination, evaluated]
      all_goals apply controlFlow_cleanup
      all_goals first
        | (intro after; exact reached)
        | exact neverJumps_cleanupReceivingDestination _ _ _

theorem controlFlow_ownerExtensionGuard (snapshot : Option PendingDestination) (destination : Goose.Core.DestinationId)
    (allowed : List StaticFlow) (resultFlow : α → StaticFlow) (action : EvalM α)
    (body : ControlFlowAction activation allowed resultFlow action) :
    ControlFlowAction activation allowed resultFlow (ownerExtensionGuard snapshot destination action) := by
  refine ⟨breakFrame_ownerExtensionGuard snapshot destination action body.frame, ?_⟩
  intro before bounded
  have reached := body.outcome before bounded
  cases evaluated : action before with
  | ok value after => simpa only [ownerExtensionGuard, evaluated, ControlFlowOutcome] using reached
  | stop reason after => simp only [ownerExtensionGuard, evaluated, ControlFlowOutcome]
  | escape address carriers middle =>
      cases snapshot with
      | none => simp only [ownerExtensionGuard, evaluated, ControlFlowOutcome]
      | some parent =>
        simp only [ownerExtensionGuard, evaluated]
        apply controlFlow_cleanup
        · intro after; trivial
        · exact neverJumps_restoreCompletedOwner _ _ _
  | jump id kind middle =>
      simp only [evaluated, ControlFlowOutcome] at reached
      cases snapshot with
      | none => simpa only [ownerExtensionGuard, evaluated, ControlFlowOutcome] using reached
      | some parent =>
        simp only [ownerExtensionGuard, evaluated]
        apply controlFlow_cleanup
        · intro after; exact reached
        · exact neverJumps_restoreCompletedOwner _ _ _

theorem controlFlow_withOwnerExtension (stored : StoredValue) (allocate : EvalM Goose.Core.DestinationId)
    (action : Goose.Core.DestinationId → EvalM α) (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (allocation : ControlFlowAction activation [normalFlow] (fun _ => normalFlow) allocate)
    (body : ∀ destination, ControlFlowAction activation allowed resultFlow (action destination)) :
    ControlFlowAction activation allowed resultFlow (withOwnerExtension stored allocate action) := by
  change ControlFlowAction activation allowed resultFlow (do
    let snapshot ← match stored.destination with
      | none => pure none
      | some id => do
          let parent ← getDestination id
          pure (match parent.progress with | .built _ => some parent | _ => none)
    let destination ← allocate
    ownerExtensionGuard snapshot destination (action destination))
  have finish (snapshot : Option PendingDestination) :
      ControlFlowAction activation allowed resultFlow (do
        let destination ← allocate
        ownerExtensionGuard snapshot destination (action destination)) := by
    apply controlFlow_prefix
    · exact allocation
    · intro destination
      exact controlFlow_ownerExtensionGuard snapshot destination allowed resultFlow _ (body destination)
  repeat' first
    | exact finish _
    | (solve | evaluation_values_leaf)
    | apply controlFlow_prefix
    | evaluation_values_intro
    | split
    | dsimp only

#print axioms controlFlow_protectDestination
#print axioms controlFlow_ownerExtensionGuard
#print axioms controlFlow_withOwnerExtension

end Goose.Proofs.ConstructionDelivery
