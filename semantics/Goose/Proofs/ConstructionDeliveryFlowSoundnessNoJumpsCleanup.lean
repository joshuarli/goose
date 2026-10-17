import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumpsOwners

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem neverJumps_protectDestination (origin : Goose.Core.OriginId) (id : Goose.Core.DestinationId)
    (action : EvalM α) (body : NeverJumps action) :
    NeverJumps (protectDestination origin id action) := by
  intro state target kind after impossible
  cases evaluated : action state with
  | ok value middle => simp only [protectDestination, evaluated] at impossible; cases impossible
  | stop reason middle => simp only [protectDestination, evaluated] at impossible; cases impossible
  | escape address carriers middle =>
      cases cleaned : cleanupReceivingDestination origin id carriers middle <;>
        simp only [protectDestination, evaluated, cleaned] at impossible <;> try cases impossible
      exact neverJumps_cleanupReceivingDestination origin id carriers _ _ _ _ cleaned
  | jump target kind middle => exact body state target kind middle evaluated

theorem neverJumps_releaseScope (environment : RuntimeActivation) (scope scopeInst : Nat) :
    NeverJumps (releaseScope environment scope scopeInst) := by
  unfold releaseScope
  apply neverJumps_bind
  · exact neverJumps_get
  · intro state; exact neverJumps_set _

theorem neverJumps_withScope (environment : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (body : NeverJumps action) :
    NeverJumps (withScope environment scope scopeInst action) := by
  intro state target kind after impossible
  cases evaluated : action state with
  | ok value middle =>
      cases cleaned : releaseScope environment scope scopeInst middle <;>
        simp only [withScope, evaluated, cleaned] at impossible <;> try cases impossible
      exact neverJumps_releaseScope environment scope scopeInst _ _ _ _ cleaned
  | stop reason middle => simp only [withScope, evaluated] at impossible; cases impossible
  | escape address carriers middle =>
      cases cleaned : releaseScope environment scope scopeInst middle <;>
        simp only [withScope, evaluated, cleaned] at impossible <;> try cases impossible
      exact neverJumps_releaseScope environment scope scopeInst _ _ _ _ cleaned
  | jump target kind middle => exact body state target kind middle evaluated

#print axioms neverJumps_protectDestination
#print axioms neverJumps_releaseScope
#print axioms neverJumps_withScope

end Goose.Proofs.ConstructionDelivery
