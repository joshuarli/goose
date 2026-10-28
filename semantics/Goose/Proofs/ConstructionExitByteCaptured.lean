import Goose.Proofs.ConstructionExitByteCapability
import Goose.Proofs.ConstructionExitFrameRelease
import Goose.Proofs.ConstructionExitByteReservation
import Goose.Proofs.ConstructionExecutionOwnershipEvaluationReceivingFrames

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem bytes_writeLoop_indexing (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    after.construction.destinations.size = before.construction.destinations.size ∧
      after.construction.destinationSuccessors = before.construction.destinationSuccessors := by
  induction bytes generalizing before row count with
  | nil => simp only [List.forIn_nil, pure, ExecutionStep.ok.injEq, true_and] at executed; subst after; exact ⟨rfl, rfl⟩
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
      exact ⟨next.1.trans indexing.1, next.2.trans indexing.2⟩


theorem finish_packed_byte_indexing (before after : ConstructionState) (id count : Nat)
    (row : PendingDestination) (present : before.destinations[id]? = some row)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (request : row.capability.request = .value)
    (executed : finishDestination id before = .ok () after) :
    after.destinations.size = before.destinations.size ∧ after.destinationSuccessors = before.destinationSuccessors := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  simp only [finishDestination, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before id with
  | false => simp only [allowed] at executed; cases executed
  | true =>
    simp only [allowed, opened, packed, hasPrefix_result, request, beq_self_eq_true,
      Bool.and_self, ↓reduceIte, lookupStorage_result, bind] at executed
    cases stored : before.storage[row.storage]? with
    | none => simp only [stored] at executed; cases executed
    | some storage =>
      have bound := (Array.getElem?_eq_some_iff.mp stored).1
      simp only [stored, replaceStorage_result, replaceDestination_result, bound, inside,
        bind, pure, ↓reduceIte] at executed
      cases executed
      simp only [Array.size_set!, and_self]


theorem build_packed_bytes_indexing (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id count : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (valid : OwnershipSourceState before.construction)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    after.construction.destinations.size = before.construction.destinations.size ∧
      after.construction.destinationSuccessors = before.construction.destinationSuccessors := by
  have renewal : renewReceivingDestination id before.construction = .ok id before.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, ready.present, ready.opened]
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
    obtain ⟨source, lifecycle, current', next, n, present', opened'⟩ :=
      bytes_writeLoop_ownershipSource bytes origin id before middle ready.destination count valid.structural.1.1.1 current ready.present ready.opened loop
    obtain ⟨following, sameLayout, sameCapability, _, _⟩ :=
      bytes_writeLoop_open_backing bytes config.layout origin id count before middle ready current loop
    have same : next = following.destination := Option.some.inj (present'.symm.trans following.present)
    have loopIndexing := bytes_writeLoop_indexing bytes origin id before middle ready.destination count
      valid current ready.present ready.opened loop
    have packed' : next.layout = .packed := by rw [same, sameLayout, packed]
    have request' : next.capability.request = .value := by rw [same, sameCapability, request]
    have renewal' : renewReceivingDestination id middle.construction = .ok id middle.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current', pure,
        lookupDestination_result, present', opened']
    simp only [bind] at loop
    rw [loop] at action
    simp only [receivingAction, liftConstruction, renewal', bind] at action
    cases finished : finishDestination id middle.construction with
    | fault reason final => simp only [finished] at action; cases action
    | ok value final =>
      cases value
      simp only [finished, ExecutionStep.ok.injEq, true_and] at action
      subst after
      have finishIndexing := finish_packed_byte_indexing middle.construction final id n next present' opened' packed' request' finished
      exact ⟨finishIndexing.1.trans loopIndexing.1, finishIndexing.2.trans loopIndexing.2⟩


theorem build_packed_bytes_captured_receiving (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count : Nat) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (ambient : OwnershipAmbient)
    (valid : OwnershipSourceState before.construction)
    (bounds : OwnershipCapturedReceivingBounds before.construction ambient)
    (receiving : OwnershipCapturedReceivingFrames before.construction ambient)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    OwnershipCapturedReceivingBounds after.construction ambient ∧
      OwnershipCapturedReceivingFrames after.construction ambient := by
  have indexing := build_packed_bytes_indexing fuel config environment id count bytes origin before after valid ready packed request current executed
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid current ready.present ready.opened executed
  have source := buildExpr_bytes_sourceState fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid current ready.present ready.opened executed
  have history := (buildExpr_bytes_ownershipSource fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid.structural.1.1.1 current ready.present ready.opened executed).1
  exact ownershipCapturedReceivingFrames_sourceExtension before.construction after.construction ambient valid.structural.1.1
    valid.structural.2.1 source.structural.1.1.1.2.2.2 history indexing.2 (by omega) tickets bounds receiving


theorem build_packed_bytes_release_frame (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (id count token incoming : Nat) (snapshot : PendingDestination)
    (bytes : List UInt8) (origin : Goose.Core.OriginId) (before after : ExecutionState)
    (channels : List Channel) (carriers : List Carrier) (outer : OwnershipAmbient)
    (valid : OwnershipSourceState before.construction)
    (bounds : OwnershipCapturedReceivingBounds before.construction (.exitChannels [token] channels carriers :: outer))
    (receiving : OwnershipCapturedReceivingFrames before.construction (.exitChannels [token] channels carriers :: outer))
    (frames : OwnershipReservationFrames before.construction (.exitChannels [token] channels carriers :: outer))
    (ticket : before.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot))
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) count)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (current : destinationCurrent before.construction id = .ok id)
    (executed : buildExpr (fuel + 1) config environment id (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    OwnershipCapturedReceivingBounds after.construction (.exitChannels [token] channels carriers :: outer) ∧
    OwnershipCapturedReceivingFrames after.construction (.exitChannels [token] channels carriers :: outer) ∧
    ∃ cleaned, Goose.Proofs.ExitExecution.exitChannelCleanupBorrowed origin [] [token] false carriers after = .ok () cleaned ∧
      OwnershipFrameReleased cleaned.construction (.exitChannels [token] channels carriers) ∧
      OwnershipReservationFrames cleaned.construction outer := by
  have captured := build_packed_bytes_captured_receiving fuel config environment id count bytes origin before after
    (.exitChannels [token] channels carriers :: outer) valid bounds receiving ready packed request current executed
  have tickets := buildExpr_bytes_tickets fuel config environment id (.varr (.int .u8)) bytes origin before after
    ready.destination count valid current ready.present ready.opened executed
  have afterTicket : after.construction.exitReservations[token]? = some (.active .fresh incoming id snapshot) := by
    simpa only [tickets] using ticket
  have afterFrames : OwnershipReservationFrames after.construction (.exitChannels [token] channels carriers :: outer) := by
    simpa only [OwnershipReservationFrames, tickets] using frames
  exact ⟨captured.1, captured.2, cleanup_single_exit_frame after token incoming id snapshot channels carriers outer origin afterTicket afterFrames⟩

#print axioms build_packed_bytes_release_frame
#print axioms build_packed_bytes_captured_receiving
#print axioms build_packed_bytes_indexing
#print axioms finish_packed_byte_indexing
#print axioms bytes_writeLoop_indexing

end Goose.Proofs.ConstructionAcceptedExecution
