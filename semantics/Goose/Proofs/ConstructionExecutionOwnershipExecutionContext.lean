import Goose.Proofs.ConstructionExecutionOwnershipEvaluationReceivingFrames
import Goose.Proofs.OwnershipRuntimeIdentitiesScopes

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnership
open Goose.Construct

structure OwnershipExecutionContext (state : ExecutionState) (ambient : OwnershipAmbient) : Prop where
  source : OwnershipSourceState state.construction
  retention : OwnershipAmbientInvariant state.construction ambient
  runtime : OwnershipRuntimeFrames state ambient
  reservations : OwnershipReservationFrames state.construction ambient
  receiving : OwnershipCapturedReceivingFrames state.construction ambient
  bounds : OwnershipCapturedReceivingBounds state.construction ambient
  identities : OwnershipRuntimeIdentities state

def OwnershipExecutionOutcome (ambient : OwnershipAmbient) (shape : OwnershipResultShape α) : ExecutionStep α → Prop
  | .ok value state => OwnershipExecutionContext state (.returned (shape.retainedCarriers value) :: ambient)
  | .escape _ carriers state | .jump _ (.breakValue carriers) state =>
      OwnershipExecutionContext state (.returned carriers :: ambient)
  | .jump _ .continueLoop state => OwnershipExecutionContext state ambient
  | .stop _ state => OwnershipSourceState state.construction ∧ OwnershipRuntimeIdentities state

theorem initial_ownershipExecutionContext : OwnershipExecutionContext .initial [] :=
  ⟨initial_ownershipSourceState, initial_ownershipAmbientInvariant, initial_ownershipRuntimeFrames,
    initial_ownershipReservationFrames, initial_ownershipCapturedReceivingFrames, initial_ownershipCapturedReceivingBounds, initial_ownershipRuntimeIdentities⟩

theorem ownershipExecutionContext_input (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext state ambient) : OwnershipEvaluationInput state ambient :=
  ⟨⟨valid.retention, valid.source.structural.2.1, valid.source.structural.2.2⟩, valid.runtime, valid.reservations⟩

theorem ownershipExecutionContext_environment (state : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipExecutionContext state ambient) (environment : RuntimeActivation)
    (present : environment ∈ state.activations) :
    OwnershipEnvironmentReceiving state.construction ambient environment :=
  ownershipEnvironmentReceiving_activation state ambient environment valid.runtime valid.receiving present

theorem ownershipExecutionContext_receiving (state : ExecutionState) (ambient inner outer : OwnershipAmbient)
    (capture : OwnershipReceivingCapture) (carriers : List Construct.Carrier)
    (valid : OwnershipExecutionContext state ambient)
    (present : ambient = inner ++ .receivingScope capture carriers :: outer) :
    capture.incoming < state.construction.destinations.size ∧
      OwnershipChannelReceivingWithinFrames state.construction outer (.construct capture.incoming) := by
  refine ⟨?_, ownershipCapturedReceivingFrames_receiving state.construction ambient inner outer
    capture carriers valid.receiving present⟩
  apply ownershipCapturedReceivingBounds_receiving state.construction inner outer capture carriers
  simpa only [present] using valid.bounds

theorem ownershipExecutionContext_receiving_push (state : ExecutionState) (ambient : OwnershipAmbient)
    (capture : OwnershipReceivingCapture) (valid : OwnershipExecutionContext state ambient)
    (bound : capture.incoming < state.construction.destinations.size)
    (receiving : OwnershipChannelReceivingWithinFrames state.construction ambient (.construct capture.incoming)) :
    OwnershipExecutionContext state (.receivingScope capture [] :: ambient) := by
  refine ⟨valid.source, ?_, ?_, ?_,
    ownershipCapturedReceivingFrames_receiving_push state.construction ambient capture valid.receiving receiving,
    ownershipCapturedReceivingBounds_receiving_push state.construction ambient capture valid.bounds bound, valid.identities⟩
  · refine ⟨valid.retention.structural, ?_, ?_⟩
    · simpa only [OwnershipAmbient.retained, List.flatMap_cons, OwnershipAmbientFrame.carriers,
        List.nil_append] using valid.retention.anchors
    · refine ⟨?_, valid.retention.boundaries⟩
      intro token incoming reserved selected snapshot member
      simp only [OwnershipAmbientFrame.tickets, List.not_mem_nil] at member
  · exact ⟨valid.runtime.activations, valid.runtime.breaks⟩
  · intro token reservation present needs
    obtain ⟨frame, member, owned⟩ := valid.reservations token reservation present needs
    exact ⟨frame, List.mem_cons_of_mem _ member, owned⟩

theorem ownershipExecutionContext_returned (state : ExecutionState) (ambient : OwnershipAmbient)
    (carriers : List Construct.Carrier) (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionContext state (.returned carriers :: ambient) :=
  ⟨valid.source, ownershipAmbientInvariant_returned state.construction ambient carriers valid.retention,
    (ownershipRuntimeFrames_returned state ambient carriers).mpr valid.runtime,
    (ownershipReservationFrames_returned state.construction ambient carriers).mpr valid.reservations,
    (ownershipCapturedReceivingFrames_returned state.construction ambient carriers).mpr valid.receiving,
    (ownershipCapturedReceivingBounds_returned state.construction ambient carriers).mpr valid.bounds, valid.identities⟩

theorem ownershipExecutionContext_returned_nil (state : ExecutionState) (ambient : OwnershipAmbient) :
    OwnershipExecutionContext state (.returned [] :: ambient) ↔ OwnershipExecutionContext state ambient := by
  constructor
  · intro valid
    exact ⟨valid.source, (ownershipAmbientInvariant_returned_nil state.construction ambient).mp valid.retention,
      (ownershipRuntimeFrames_returned state ambient []).mp valid.runtime,
      (ownershipReservationFrames_returned state.construction ambient []).mp valid.reservations,
      (ownershipCapturedReceivingFrames_returned state.construction ambient []).mp valid.receiving,
      (ownershipCapturedReceivingBounds_returned state.construction ambient []).mp valid.bounds, valid.identities⟩
  · exact ownershipExecutionContext_returned state ambient []

theorem ownershipExecutionOutcome_source (ambient : OwnershipAmbient) (shape : OwnershipResultShape α)
    (result : ExecutionStep α) (valid : OwnershipExecutionOutcome ambient shape result) :
    OwnershipSourceState (Goose.Proofs.Exit.stepState result).construction := by
  cases result with
  | ok value state | escape address carriers state => exact valid.source
  | stop reason state => exact valid.1
  | jump target kind state => cases kind <;> exact valid.source

theorem ownershipExecutionOutcome_identities (ambient : OwnershipAmbient) (shape : OwnershipResultShape α)
    (result : ExecutionStep α) (valid : OwnershipExecutionOutcome ambient shape result) :
    OwnershipRuntimeIdentities (Goose.Proofs.Exit.stepState result) := by
  cases result with
  | ok value state | escape address carriers state => exact valid.identities
  | stop reason state => exact valid.2
  | jump target kind state => cases kind <;> exact valid.identities

theorem ownershipExecution_pure (state : ExecutionState) (ambient : OwnershipAmbient)
    (shape : OwnershipResultShape α) (value : α) (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionOutcome ambient shape ((pure value : EvalM α) state) :=
  ownershipExecutionContext_returned state ambient (shape.retainedCarriers value) valid

theorem ownershipExecution_stop (state : ExecutionState) (ambient : OwnershipAmbient)
    (shape : OwnershipResultShape α) (reason : Goose.Core.Stop) (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionOutcome ambient shape (EvalM.stop reason state) := ⟨valid.source, valid.identities⟩

theorem evaluation_zero_execution_ownership (config : EvalConfig) (shape : OwnershipResultShape α)
    (action : EvalM α) (actual : OwnershipEvaluationAction 0 config shape action)
    (state : ExecutionState) (ambient : OwnershipAmbient) (valid : OwnershipExecutionContext state ambient) :
    OwnershipExecutionOutcome ambient shape (action state) := by
  cases actual <;>
    simpa only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands,
      buildExpr, buildElement, evalArguments, invokeCall, enterActivation, execActivationBody,
      execResultBlock, execResultBlockWith, execBlock, execStmts, execStmt, evalPrintArg,
      execWhile, execRange, execEach, loopBody, pushValue, timeout, EvalM.stop,
      OwnershipExecutionOutcome] using (show OwnershipSourceState state.construction ∧ OwnershipRuntimeIdentities state from
        ⟨valid.source, valid.identities⟩)

end Goose.Proofs.ConstructionExecutionOwnership
