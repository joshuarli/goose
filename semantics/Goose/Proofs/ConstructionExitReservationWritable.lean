import Goose.Proofs.ConstructionExitReservationReady

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol

theorem fresh_replacement_of_receiver_writable (state : ConstructionState) (incoming selected count : Nat)
    (receiver replacement : PendingDestination)
    (parentFound : state.destinations[incoming]? = some receiver)
    (parentUse : receiver.use = .receiver) (parentPhase : receiver.progress = .exiting count selected)
    (selectedFound : state.destinations[selected]? = some replacement)
    (selectedUse : replacement.use = .replacement incoming) (earlier : incoming < selected) :
    destinationCanWrite state selected = true := by
  have selectedBound := (Array.getElem?_eq_some_iff.mp selectedFound).1
  simp only [destinationCanWrite_result, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases size : state.destinations.size with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ n =>
      simp [size, List.range'_succ, selectedFound, selectedUse, parentFound, parentUse, parentPhase, Id.run]
      rfl

theorem accepted_packed_reservation_writable (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (receiverUse : receiver.destination.use = .receiver)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    destinationCanWrite reserved selected = true := by
  have parent := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened current reservation).1
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have earlier : incoming < selected := by rw [fresh]; exact (Array.getElem?_eq_some_iff.mp receiver.present).1
  have roles := accepted_open_reservation_successor_roles config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
  have ticket := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened current reservation).2
  obtain ⟨allocated, replacement, appended, source, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  obtain ⟨row, found, active⟩ := open_replacement_selected_active before.construction allocated incoming selected (count + 1)
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes replacement
  have selectedFound : reserved.destinations[selected]? = some row := by simpa only [appended] using found
  have indexed := world.ownership.source.structural.1.1.1.2.1 incoming receiver.destination receiver.present
  have notSame : selected ≠ receiver.destination.capability.id := by simpa only [indexed] using Nat.ne_of_gt earlier
  have use := (roles token incoming selected selected receiver.destination row ticket (.refl selected) selectedFound)
  simp only [indexed, if_neg (Nat.ne_of_gt earlier)] at use
  exact fresh_replacement_of_receiver_writable reserved incoming selected (count + 1)
    { receiver.destination with progress := .exiting (count + 1) selected } row parent receiverUse rfl selectedFound use.1 earlier

#print axioms fresh_replacement_of_receiver_writable
#print axioms accepted_packed_reservation_writable

theorem packed_replacement_write_success (state : ConstructionState) (id count parent : Nat)
    (row : PendingDestination) (storage : ReceivingStorage) (payload : ByteArray)
    (present : state.destinations[id]? = some row) (stored : state.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .replacement parent)
    (writable : destinationCanWrite state id = true) (fits : count + 1 < 2 ^ 32) :
    ∃ after, writeElement id payload state = .ok () after := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [writeElement, writableDestination_result, present, writable, bind, opened, lookupStorage_result, stored]
  cases backing : row.backing <;>
    simp only [writingAvailable_result, backing, packed, adaptation, Option.map_none, Option.getD_none,
      use, fits, decide_true, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      pure, bind, replaceStorage_result, storageInside, replaceDestination_result, inside, emit_result]
  all_goals exact ⟨_, rfl⟩

#print axioms packed_replacement_write_success

theorem accepted_packed_reservation_first_write (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (receiverUse : receiver.destination.use = .receiver)
    (receiverPacked : receiver.destination.layout = .packed)
    (receiverRequest : receiver.destination.capability.request = .value)
    (receiverAdaptation : receiver.destination.adaptation = none)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (byte : UInt8) :
    ∃ ready : OpenDestinationBacking config.layout { before with construction := reserved } selected (.varr (.int .u8)) 0,
      ∃ written, writeElement selected ⟨#[byte]⟩ reserved = .ok () written ∧
        ready.destination.layout = .packed ∧ ready.destination.capability.request = .value ∧
        destinationCurrent reserved selected = .ok selected := by
  obtain ⟨ready, packed, request, resolved⟩ := accepted_packed_reservation_ready config initialized before reserved incoming selected token count
    receiver receiverPacked receiverRequest current ambient types live regions pending world reservation
  have writable := accepted_packed_reservation_writable config initialized before reserved incoming selected token count
    receiver receiverUse current ambient types live regions pending world reservation
  obtain ⟨metadata, metadataFound, _, adaptation⟩ := reserve_open_replacement_metadata before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
  have same := Option.some.inj (metadataFound.symm.trans ready.present)
  subst metadata
  have unchanged : ready.destination.adaptation = none := adaptation.trans receiverAdaptation
  have indexed := world.ownership.source.structural.1.1.1.2.1 incoming receiver.destination receiver.present
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have distinct : selected ≠ incoming := by rw [fresh]; exact Nat.ne_of_gt (Array.getElem?_eq_some_iff.mp receiver.present).1
  have ticket := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened current reservation).2
  have roles := accepted_open_reservation_successor_roles config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
  have use := roles token incoming selected selected receiver.destination ready.destination ticket (.refl selected) ready.present
  simp only [indexed, if_neg distinct] at use
  obtain ⟨written, write⟩ := packed_replacement_write_success reserved selected 0 incoming ready.destination ready.storage ⟨#[byte]⟩
    ready.present ready.bytes ready.opened packed unchanged use.1 writable (by decide)
  exact ⟨ready, written, write, packed, request, resolved⟩

#print axioms accepted_packed_reservation_first_write

theorem packed_finish_success (state : ConstructionState) (id count : Nat)
    (row : PendingDestination) (storage : ReceivingStorage)
    (present : state.destinations[id]? = some row) (stored : state.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (request : row.capability.request = .value) (writable : destinationCanWrite state id = true) :
    ∃ after, finishDestination id state = .ok () after := by
  have inside := (Array.getElem?_eq_some_iff.mp present).1
  have storageInside := (Array.getElem?_eq_some_iff.mp stored).1
  simp only [finishDestination, writableDestination_result, present, writable, bind, opened, packed,
    hasPrefix_result, request, beq_self_eq_true, Bool.true_and, ↓reduceIte, lookupStorage_result, stored,
    replaceStorage_result, storageInside, replaceDestination_result, inside, pure]
  exact ⟨_, rfl⟩

#print axioms packed_finish_success

theorem accepted_packed_reservation_empty_build (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (receiverUse : receiver.destination.use = .receiver)
    (receiverPacked : receiver.destination.layout = .packed)
    (receiverRequest : receiver.destination.capability.request = .value)
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved) :
    ∃ after, buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) [] origin)
      { before with construction := reserved } = .ok () after := by
  obtain ⟨ready, packed, request, resolved⟩ := accepted_packed_reservation_ready config initialized before reserved incoming selected token count
    receiver receiverPacked receiverRequest current ambient types live regions pending world reservation
  have writable := accepted_packed_reservation_writable config initialized before reserved incoming selected token count
    receiver receiverUse current ambient types live regions pending world reservation
  obtain ⟨finished, finish⟩ := packed_finish_success reserved selected 0 ready.destination ready.storage
    ready.present ready.bytes ready.opened packed request writable
  have renewal : renewReceivingDestination selected reserved = .ok selected reserved := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, resolved, pure,
      lookupDestination_result, ready.present, ready.opened]
  refine ⟨{ before with construction := finished }, ?_⟩
  simp only [buildExpr, liftConstruction, renewal, bind, protectDestination, List.forIn_nil, pure,
    receivingAction, finish]

#print axioms accepted_packed_reservation_empty_build

theorem accepted_nested_empty_handler_derived_build (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId incoming selected token count : Nat)
    (origin : OriginId) (outerRest innerRest : List Stmt)
    (outerTail innerTail : Option Expr) (contextId : ContextId) (arguments : List Arg)
    (callChannels exitChannels : List Channel)
    (outerInitial outerBound callPrepared innerEntered innerBound : ExecutionState)
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
      (.mk innerScope (.returnFrom targetId [.bytes (.varr (.int .u8)) [] origin] origin :: innerRest) innerTail) innerEntered)
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
    :
    ∃ (after final : ExecutionState),
      buildExpr (fuel + 1) config { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes }
        selected (.bytes (.varr (.int .u8)) [] origin) { innerBound with construction := reserved } = .ok () after ∧
      enterActivation (fuel + 13) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
      .ok [.completed selected] final ∧
      final.construction.stdout = after.construction.stdout ∧
      ∀ entry : RootInst × Value,
        (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains entry.1 = false →
        (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains entry.1 = false →
        (entry ∈ final.objects ↔ entry ∈ after.objects) := by
  obtain ⟨after, built⟩ := accepted_packed_reservation_empty_build fuel config initialized
    { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes } origin innerBound reserved
    incoming selected token count receiver receiverRole packed request receiverCurrent ambient types live regions pending world reservation
  obtain ⟨final, result⟩ := accepted_nested_byte_handler_derived_ready fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count [] origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live regions pending baseRegion outerLookup results outerChannels
    outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver receiverRole receiverAdaptation
    receiverPhysical receiverCurrent world history reservation covered integers other baseMember baseDestination outside
    packed request (by decide) built
  exact ⟨after, final, built, result⟩

#print axioms accepted_nested_empty_handler_derived_build

end Goose.Proofs.ConstructionAcceptedExecution
