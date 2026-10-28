import Goose.Proofs.ConstructionExitByteReservation
import Goose.Proofs.ConstructionExitRuntimeUnwind
import Goose.Proofs.ConstructionExitCapturedRelease

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem bytes_writeLoop_runtime (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    after = { before with construction := after.construction } := by
  induction bytes generalizing before row count with
  | nil => simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed; subst after; rfl
  | cons byte rest ih =>
    have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind] at executed
    cases written : writeElement id ⟨#[byte]⟩ before.construction with
    | fault reason final => simp only [written] at executed; cases executed
    | ok value final =>
      cases value
      simp only [written, pure] at executed
      have extension := writeElement_ownership_source id ⟨#[byte]⟩ before.construction valid.structural.1.1.1
      have nextValid := constructionPrimitive_sourceState_of_sourceExtension (writeElement id ⟨#[byte]⟩)
        (.writeElement id ⟨#[byte]⟩) before.construction valid extension
      rw [written] at nextValid
      have row' := writeElement_success_destination id ⟨#[byte]⟩ before.construction final row count present opened written
      have indexing := writeElement_preserves_indexing id ⟨#[byte]⟩ before.construction
      rw [written] at indexing
      simp only [ConstructionResult.finalState] at indexing
      have current' : destinationCurrent final id = .ok id := by
        rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ before.construction final indexing.1 indexing.2, indexing.1]
        simpa only [destinationCurrent_result] using current
      have next := ih { before with construction := final }
        { row with progress := .open (count + 1), writeEnd := row.writeEnd + (⟨#[byte]⟩ : ByteArray).size } (count + 1)
        nextValid current' row'.1 rfl executed
      exact next

theorem buildExpr_bytes_runtime (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : buildExpr (fuel + 1) config environment id (.bytes ty bytes origin) before = .ok () after) :
    after = { before with construction := after.construction } := by
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  simp only [buildExpr, liftConstruction, renewal, bind] at executed
  have action := protectDestination_success origin id _ before after () executed
  cases loop : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before with
  | stop reason state => simp only [bind] at loop; rw [loop] at action; cases action
  | escape target carriers state => simp only [bind] at loop; rw [loop] at action; cases action
  | jump target kind state => simp only [bind] at loop; rw [loop] at action; cases action
  | ok value middle =>
    cases value
    have loopRuntime := bytes_writeLoop_runtime bytes origin id before middle row count valid current present opened loop
    obtain ⟨source, lifecycle, current', next, n, present', opened'⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle row count valid.structural.1.1.1 current present opened loop
    have renewal' : renewReceivingDestination id middle.construction = .ok id middle.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
        lookupDestination_result, present', opened']
    have loop' := loop
    simp only [bind] at loop'
    rw [loop'] at action
    simp only [receivingAction, liftConstruction, renewal', bind] at action
    cases finished : finishDestination id middle.construction with
    | fault reason final => simp only [finished] at action; cases action
    | ok value final =>
      cases value
      simp only [finished, ExecutionStep.ok.injEq, true_and] at action
      subst after
      rw [loopRuntime]


theorem byte_build_cleanup_outer_frames (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count token incoming : Nat) (snapshot : PendingDestination)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (channels : List Channel) (carriers : List Carrier) (outer : OwnershipAmbient)
    (valid : OwnershipSourceState before.construction)
    (bounds : OwnershipCapturedReceivingBounds before.construction (.exitChannels [token] channels carriers :: outer))
    (receiving : OwnershipCapturedReceivingFrames before.construction (.exitChannels [token] channels carriers :: outer))
    (frames : OwnershipReservationFrames before.construction (.exitChannels [token] channels carriers :: outer))
    (runtime : OwnershipRuntimeFrames before (.exitChannels [token] channels carriers :: outer))
    (identities : OwnershipRuntimeIdentities before)
    (ticket : before.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot))
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after)
    (scope : Nat) (scopeInst : Goose.Core.ScopeInst) :
    ∃ cleaned,
      Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers after = .ok () cleaned ∧
      OwnershipCapturedReceivingBounds (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipCapturedReceivingFrames (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipReservationFrames (releaseScopeState environment scope scopeInst cleaned).construction outer ∧
      OwnershipRuntimeFrames (releaseScopeState environment scope scopeInst cleaned) outer ∧
      OwnershipRuntimeIdentities (releaseScopeState environment scope scopeInst cleaned) := by
  obtain ⟨cleaned, cleanup, capturedBounds, capturedReceiving, reservationFrames⟩ :=
    byte_build_cleanup_captured_outer fuel config environment id count token incoming snapshot bytes origin before after
      channels carriers outer valid bounds receiving frames ticket ready packed request current executed scope scopeInst
  have sameRuntime := buildExpr_bytes_runtime fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid current ready.present ready.opened executed
  have afterRuntime : OwnershipRuntimeFrames after (.exitChannels [token] channels carriers :: outer) := by
    rw [sameRuntime]
    exact ⟨runtime.activations, runtime.breaks⟩
  have afterIdentities : OwnershipRuntimeIdentities after := by
    rw [sameRuntime]
    exact ⟨identities.activations, identities.breaks⟩
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid current ready.present ready.opened executed
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot) := by
    simpa only [tickets] using ticket
  have afterFrames : OwnershipReservationFrames after.construction (.exitChannels [token] channels carriers :: outer) := by
    simpa only [OwnershipReservationFrames, tickets] using frames
  obtain ⟨other, otherCleanup, _, outerRuntime, outerIdentities⟩ :=
    cleanup_exit_frame_runtime_unwind after token incoming id snapshot channels carriers outer origin environment scope scopeInst
      afterTicket afterFrames afterRuntime afterIdentities
  have same := cleanup.symm.trans otherCleanup
  cases same
  exact ⟨cleaned, cleanup, capturedBounds, capturedReceiving, reservationFrames, outerRuntime, outerIdentities⟩

#print axioms byte_build_cleanup_outer_frames
#print axioms buildExpr_bytes_runtime
#print axioms bytes_writeLoop_runtime

end Goose.Proofs.ConstructionAcceptedExecution
