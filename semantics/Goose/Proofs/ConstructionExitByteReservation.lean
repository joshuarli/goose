import Goose.Proofs.ConstructionExitByteReplacement
import Goose.Proofs.ConstructionExecutionProtocolReservationMetadataWrites
import Goose.Proofs.ConstructionExitReservationPath

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage
open Goose.Proofs.ExitExecution

theorem bytes_writeLoop_tickets (bytes : List UInt8) (origin : Goose.Core.OriginId) (id : Nat)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : ((forIn bytes PUnit.unit fun byte _ => do
      receivingAction origin id (fun destination => writeElement destination ⟨#[byte]⟩)
      pure (.yield PUnit.unit)) : EvalM PUnit) before = .ok PUnit.unit after) :
    after.construction.exitReservations = before.construction.exitReservations := by
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
      have frame := writeElement_reservation_frame id ⟨#[byte]⟩ before.construction valid.structural.1.1.1
      rw [written] at frame
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
      exact next.trans frame.tickets

theorem buildExpr_bytes_tickets (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (id : Nat) (ty : Ty) (bytes : List UInt8) (origin : Goose.Core.OriginId)
    (before after : ExecutionState) (row : PendingDestination) (count : Nat)
    (valid : OwnershipSourceState before.construction)
    (current : destinationCurrent before.construction id = .ok id)
    (present : before.construction.destinations[id]? = some row) (opened : row.progress = .open count)
    (executed : buildExpr (fuel + 1) config environment id (.bytes ty bytes origin) before = .ok () after) :
    after.construction.exitReservations = before.construction.exitReservations := by
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
    have loopTickets := bytes_writeLoop_tickets bytes origin id before middle row count valid current present opened loop
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
      have frame := finishDestination_reservation_frame id middle.construction lifecycle
      rw [finished] at frame
      exact frame.tickets.trans loopTickets


theorem accepted_reserved_bytes_path_after_unwind (fuel : Nat) (config : EvalConfig)
    (initialized : Nat) (reservationBefore reserved : ConstructionState) (incoming token selected : Nat)
    (environment : RuntimeActivation) (before after : ExecutionState) (bytes : List UInt8)
    (origin : Goose.Core.OriginId) (scope : Nat) (scopeInst : Goose.Core.ScopeInst)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (valid : ReservationLifecycleInvariant reservationBefore)
    (reservation : reserveExitDestination incoming .newValue reservationBefore = .ok (token, selected) reserved)
    (construction : before.construction = reserved)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (count : Nat) (openBacking : OpenDestinationBacking config.layout before selected (.varr (.int .u8)) count)
    (different : ∀ snapshot, reserved.exitReservations[token]? = some (.active .fresh incoming selected snapshot) →
      selected ≠ snapshot.capability.id)
    (packed : openBacking.destination.layout = .packed)
    (request : openBacking.destination.capability.request = .value)
    (fits : count + bytes.length < 2 ^ 32)
    (current : destinationCurrent before.construction selected = .ok selected)
    (built : buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) before = .ok () after) :
    let unwound := releaseScopeState environment scope scopeInst after
    ∃ snapshot destination owner,
      unwound.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) ∧
      unwound.construction.destinations[selected]? = some destination ∧
      destination.progress = .built (count + bytes.length) ∧
      unwound.construction.destinations[snapshot.capability.id]? = some owner ∧
      destination.backing = owner.backing ∧
      OwnershipReplacementPath unwound.construction.destinations snapshot.capability.id selected ∧
      CarrierResultBacking config.layout unwound (.completed selected) ∧
      ((∃ n, owner.progress = .exiting n selected) ∨ owner.progress = .abandoned ∨ owner.progress = .cancelled) := by
  obtain ⟨snapshot, initialOwner, _, ticketBefore, _, _, _, _, _⟩ :=
    accepted_fresh_reservation_replacement_path config initialized reservationBefore reserved incoming token selected
      before environment scope scopeInst ambient types live regions pending valid reservation construction world count openBacking different
  have tickets := buildExpr_bytes_tickets fuel config environment selected (.varr (.int .u8)) bytes origin
    before after openBacking.destination count world.ownership.source current openBacking.present openBacking.opened built
  have ticket : after.construction.exitReservations[token]? = some (.active .fresh incoming selected snapshot) := by
    simpa only [tickets, releaseScopeState] using ticketBefore
  have other : selected ≠ snapshot.capability.id := different snapshot (by simpa only [construction, tickets] using ticket)
  have source := buildExpr_bytes_sourceState fuel config environment selected (.varr (.int .u8)) bytes origin
    before after openBacking.destination count world.ownership.source current openBacking.present openBacking.opened built
  obtain ⟨destination, storage, present, _, _, _, _, _, _, progress, _⟩ :=
    buildExpr_byteOwner_geometry fuel config environment bytes origin selected count before after openBacking packed request fits
      world.ownership.source.structural.1.1.1 current built
  have role := source.aliases token incoming selected selected snapshot destination ticket (.refl selected) present
  simp only [if_neg other] at role
  have active : ReplacementSupported after.construction selected :=
    .active selected destination present (by simp only [progress, activeProgress])
  obtain ⟨owner, found, backing, ownerProgress⟩ := source.structural.1.2.2.1
    selected snapshot.capability.id destination present role.1 active
  have backed := accepted_byte_return_carrier_backed fuel config initialized environment bytes origin selected count
    before after ambient types live regions pending world openBacking packed request fits current built
  exact ⟨snapshot, destination, owner, ticket, present, progress, found, backing,
    .step selected snapshot.capability.id snapshot.capability.id destination present role.1 (.refl _),
    carrierBacking_construction_frame config.layout after (releaseScopeState environment scope scopeInst after) rfl _ backed,
    ownerProgress⟩

#print axioms accepted_reserved_bytes_path_after_unwind

#print axioms bytes_writeLoop_tickets
#print axioms buildExpr_bytes_tickets

end Goose.Proofs.ConstructionAcceptedExecution
