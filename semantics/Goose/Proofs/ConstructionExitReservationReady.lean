import Goose.Proofs.ConstructionExitReservationRegions

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem open_packed_replacement_backing (layout : LayoutEnv) (before : ExecutionState)
    (allocated : ConstructionState) (incoming selected count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (packed : receiver.destination.layout = .packed)
    (request : receiver.destination.capability.request = .value)
    (executed : openExitReplacement incoming before.construction = .ok selected allocated) :
    ∃ ready : OpenDestinationBacking layout { before with construction := allocated } selected (.varr (.int .u8)) 0,
      ready.destination.layout = .packed ∧ ready.destination.capability.request = .value := by
  have inside := (Array.getElem?_eq_some_iff.mp receiver.present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp receiver.bytes).1
  have present := receiver.present
  have stored := receiver.bytes
  have opened := receiver.opened
  simp only [openExitReplacement, writableDestination_result, present, bind] at executed
  cases allowed : destinationCanWrite before.construction incoming with
  | false => simp [allowed] at executed
  | true =>
    simp only [allowed, opened, pure, bind, lookupStorage_result, stored, ConstructionM.get,
      ConstructionM.set, replaceDestination_result, replaceStorage_result, emit_result, hasPrefix_result,
      packed, request, beq_self_eq_true, Bool.true_and, Array.size_push, Nat.lt_succ_of_lt inside,
      storageInside, Array.size_setIfInBounds, ↓reduceIte] at executed
    cases executed
    let capability := { receiver.destination.capability with id := before.construction.destinations.size, start := receiver.storage.bytes.size }
    let row : PendingDestination := ⟨capability, receiver.destination.backing, .packed, .replacement incoming, .open 0,
      capability.start + 4, capability.start, none, receiver.destination.adaptation⟩
    let storage : ReceivingStorage := { receiver.storage with bytes := receiver.storage.bytes ++ ⟨#[0, 0, 0, 0]⟩ }
    refine ⟨⟨row, storage, ?_, ?_, ?_, rfl, .int .u8, rfl, 1, ?_, ?_, ?_⟩, rfl, ?_⟩
    all_goals simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne,
      Nat.ne_of_lt inside, Array.getElem?_push, PendingDestination.storage,
      DestinationBacking.writeStorage, destinationPayloadStart, packed, request, elementsEnd,
      ByteArray.size_append, receiver.logicalType, row, storage, capability]
    all_goals simp_all [PendingDestination.storage, DestinationBacking.writeStorage,
      Array.getElem?_setIfInBounds_self_of_lt, ByteArray.size]
    all_goals rfl

#print axioms open_packed_replacement_backing

theorem accepted_packed_reservation_ready (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (packed : receiver.destination.layout = .packed)
    (request : receiver.destination.capability.request = .value)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    ∃ ready : OpenDestinationBacking config.layout { before with construction := reserved } selected (.varr (.int .u8)) 0,
      ready.destination.layout = .packed ∧ ready.destination.capability.request = .value ∧
      destinationCurrent reserved selected = .ok selected := by
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  obtain ⟨ready, isPacked, isValue⟩ := open_packed_replacement_backing config.layout before allocated incoming selected count
    receiver packed request replacement
  let result : OpenDestinationBacking config.layout { before with construction := reserved } selected (.varr (.int .u8)) 0 :=
    ⟨ready.destination, ready.storage, by simpa only [appended] using ready.present,
      by simpa only [appended] using ready.bytes, ready.logicalType, ready.opened, ready.element,
      ready.elementType, ready.fuel, ready.scan, ready.bounded, ready.rollback⟩
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have map := openExitReplacement_successorMap incoming before.construction
  rw [replacement] at map
  simp only [ConstructionResult.finalState] at map
  have noEdge : reserved.destinationSuccessors.lookup selected = none := by
    rw [appended]
    cases edge : allocated.destinationSuccessors.lookup selected with
    | none => rfl
    | some next =>
      have old : before.construction.destinationSuccessors.lookup selected = some next := by simpa only [map] using edge
      obtain ⟨earlier, later⟩ := world.ownership.source.structural.2.1 selected next old
      rw [fresh] at earlier
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans earlier later))
  have inside := (Array.getElem?_eq_some_iff.mp result.present).1
  have resolved : destinationCurrent reserved selected = .ok selected := by
    rw [destinationCurrent_result, destinationCurrentSteps_succ]
    simp [inside, noEdge]
  exact ⟨result, isPacked, isValue, resolved⟩

#print axioms accepted_packed_reservation_ready

theorem accepted_nested_byte_handler_derived_ready (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId incoming selected token count : Nat)
    (bytes : List UInt8) (origin : OriginId) (outerRest innerRest : List Stmt)
    (outerTail innerTail : Option Expr) (contextId : ContextId) (arguments : List Arg)
    (callChannels exitChannels : List Channel)
    (outerInitial outerBound callPrepared innerEntered innerBound after : ExecutionState)
    (outerImpl innerImpl calledImpl : Impl) (calledId : ImplId)
    (reserved : ConstructionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (baseRegion : ReceivingRegion)
    (outerLookup : config.module.impls[outer.implementation]? = some outerImpl)
    (results : outerImpl.results.toList.map (·.ty) = [.varr (.int .u8)])
    (outerChannels : outer.channels = [.construct incoming])
    (outerBinding : bindAll outer.act outerInitial.nextScope outerPre { outerInitial with
      nextScope := outerInitial.nextScope + 1
      activations := outerInitial.activations.map (fun current => if current.act == outer.act then
        { current with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes } else current) } = .ok () outerBound)
    (called : getImplementation config contextId outerBound = .ok (calledId, calledImpl) outerBound)
    (callSetup : channelsFor config.layout outer.act calledImpl.results.toList origin outerBound = .ok callChannels callPrepared)
    (callPrefix : Goose.Proofs.ExitExecution.CallActivationPrefix (fuel + 7) config
      { outer with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes }
      contextId arguments callChannels origin callPrepared inner innerPre
      (.mk innerScope (.returnFrom targetId [.bytes (.varr (.int .u8)) bytes origin] origin :: innerRest) innerTail) innerEntered)
    (innerLookup : config.module.impls[inner.implementation]? = some innerImpl)
    (innerBinding : bindAll inner.act innerEntered.nextScope innerPre { innerEntered with
      nextScope := innerEntered.nextScope + 1
      activations := innerEntered.activations.map (fun current => if current.act == inner.act then
        { current with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes } else current) } = .ok () innerBound)
    (selection : targetActivation config targetId innerBound = .ok outer innerBound)
    (distinct : outer.act ≠ inner.act)
    (receiver : OpenDestinationBacking config.layout innerBound incoming (.varr (.int .u8)) (count + 1))
    (receiverRole : receiver.destination.use = .receiver)
    (receiverAdaptation : receiver.destination.adaptation = none)
    (receiverPhysical : receiver.destination.capability.layout = .varr (.int .u8))
    (receiverCurrent : destinationCurrent innerBound.construction incoming = .ok incoming)
    (world : AcceptedWorld config initialized innerBound ambient types live regions pending)
    (history : ReservationReferencesBounded innerBound.construction ambient)
    (reservation : reserveExitDestination incoming .newValue innerBound.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers)
    (integers : ∀ frame ∈ pending, IntegerRegisterCarriers frame.carriers)
    (other : ∀ region ∈ regions, region.destination ≠ incoming →
      incoming ∈ region.mutableDestinations ∧ region.limit receiver.destination.storage ≤ receiver.storage.bytes.size)
    (baseMember : baseRegion ∈ regions) (baseDestination : baseRegion.destination = incoming)
    (outside : ∀ root, live root → ¬ baseRegion.mutableRoots root)
    (packed : receiver.destination.layout = .packed) (request : receiver.destination.capability.request = .value)
    (fits : bytes.length < 2 ^ 32)
    (built : buildExpr (fuel + 1) config { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes }
      selected (.bytes (.varr (.int .u8)) bytes origin) { innerBound with construction := reserved } = .ok () after) :
    ∃ final, enterActivation (fuel + 13) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
      .ok [.completed selected] final ∧
      final.construction.stdout = after.construction.stdout ∧
      ∀ entry : RootInst × Value,
        (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains entry.1 = false →
        (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains entry.1 = false →
        (entry ∈ final.objects ↔ entry ∈ after.objects) := by
  obtain ⟨ready, selectedPacked, selectedRequest, selectedCurrent⟩ :=
    accepted_packed_reservation_ready config initialized innerBound reserved incoming selected token count receiver packed request
      receiverCurrent ambient types live regions pending world reservation
  exact accepted_nested_byte_handler_regions fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count 0 bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live regions pending baseRegion outerLookup results outerChannels
    outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver receiverRole receiverAdaptation
    receiverPhysical receiverCurrent world history reservation covered integers other baseMember baseDestination outside
    ready selectedPacked selectedRequest (by simpa using fits) selectedCurrent built

#print axioms accepted_nested_byte_handler_derived_ready

end Goose.Proofs.ConstructionAcceptedExecution
