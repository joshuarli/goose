import Goose.Proofs.ConstructionExitReservationWritable
import Goose.Proofs.ConstructionElementWriteTransition

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionStorage

theorem packed_replacement_write_step (state : ConstructionState) (incoming selected parentCount count : Nat)
    (parent row : PendingDestination) (storage : ReceivingStorage) (byte : UInt8)
    (parentFound : state.destinations[incoming]? = some parent) (parentUse : parent.use = .receiver)
    (parentPhase : parent.progress = .exiting parentCount selected) (earlier : incoming < selected)
    (present : state.destinations[selected]? = some row) (stored : state.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .replacement incoming)
    (current : destinationCurrent state selected = .ok selected) (fits : count + 1 < 2 ^ 32) :
    ∃ after nextStorage,
      writeElement selected ⟨#[byte]⟩ state = .ok () after ∧
      after.destinations[incoming]? = some parent ∧
      after.destinations[selected]? = some { row with progress := .open (count + 1), writeEnd := row.writeEnd + 1 } ∧
      after.storage[row.storage]? = some nextStorage ∧ destinationCurrent after selected = .ok selected := by
  have writable := fresh_replacement_of_receiver_writable state incoming selected parentCount parent row parentFound parentUse parentPhase present use earlier
  obtain ⟨after, write⟩ := packed_replacement_write_success state selected count incoming row storage ⟨#[byte]⟩
    present stored opened packed adaptation use writable fits
  have destination := writeElement_success_destination selected ⟨#[byte]⟩ state after row count present opened write
  have indexing := writeElement_preserves_indexing selected ⟨#[byte]⟩ state
  rw [write] at indexing
  simp only [ConstructionResult.finalState] at indexing
  have currentAfter : destinationCurrent after selected = .ok selected := by
    rw [destinationCurrent_result, destinationCurrentSteps_same_indexing _ state after indexing.1 indexing.2, indexing.1]
    simpa only [destinationCurrent_result] using current
  have transition := writeElement_transition selected ⟨#[byte]⟩ state
  rw [write] at transition
  cases transition with
  | written actual oldStorage actualCount found storageFound phase =>
    have same := Option.some.inj (found.symm.trans present)
    subst actual
    have sameStorage := Option.some.inj (storageFound.symm.trans stored)
    subst oldStorage
    have sameCount := DestinationProgress.open.inj (phase.symm.trans opened)
    subst actualCount
    let nextStorage := { storage with bytes := storage.bytes.extract 0 row.writeEnd ++ (⟨#[byte]⟩ : ByteArray) ++ storage.bytes.extract (row.writeEnd + (⟨#[byte]⟩ : ByteArray).size) storage.bytes.size }
    refine ⟨_, nextStorage, write, ?_, ?_, ?_, currentAfter⟩
    · simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Nat.ne_of_gt earlier)] using parentFound
    · simpa [ByteArray.size] using destination.1
    · exact Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp stored).1

#print axioms packed_replacement_write_step

theorem packed_replacement_byte_loop (bytes : List UInt8) (origin : OriginId)
    (state : ExecutionState) (incoming selected parentCount count : Nat)
    (parent row : PendingDestination) (storage : ReceivingStorage)
    (parentFound : state.construction.destinations[incoming]? = some parent) (parentUse : parent.use = .receiver)
    (parentPhase : parent.progress = .exiting parentCount selected) (earlier : incoming < selected)
    (present : state.construction.destinations[selected]? = some row) (stored : state.construction.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .replacement incoming)
    (request : row.capability.request = .value)
    (current : destinationCurrent state.construction selected = .ok selected) (fits : count + bytes.length < 2 ^ 32) :
    ∃ after finalRow finalStorage,
      ((forIn bytes PUnit.unit fun byte _ => do
        receivingAction origin selected (fun destination => writeElement destination ⟨#[byte]⟩)
        pure (.yield PUnit.unit)) : EvalM PUnit) state = .ok PUnit.unit after ∧
      after.construction.destinations[incoming]? = some parent ∧
      after.construction.destinations[selected]? = some finalRow ∧
      after.construction.storage[finalRow.storage]? = some finalStorage ∧
      finalRow.progress = .open (count + bytes.length) ∧ finalRow.layout = .packed ∧
      finalRow.adaptation = none ∧ finalRow.use = .replacement incoming ∧
      finalRow.capability.request = .value ∧ destinationCurrent after.construction selected = .ok selected := by
  induction bytes generalizing state row storage count with
  | nil =>
    exact ⟨state, row, storage, by simp [pure], parentFound, present, stored, by simpa using opened,
      packed, adaptation, use, request, current⟩
  | cons byte rest ih =>
    have renewal : renewReceivingDestination selected state.construction = .ok selected state.construction := by
      simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
        lookupDestination_result, present, opened]
    have stepFits : count + 1 < 2 ^ 32 := by simp only [List.length_cons] at fits; omega
    obtain ⟨written, nextStorage, write, parentAfter, nextPresent, nextStored, nextCurrent⟩ :=
      packed_replacement_write_step state.construction incoming selected parentCount count parent row storage byte
        parentFound parentUse parentPhase earlier present stored opened packed adaptation use current stepFits
    let nextRow := { row with progress := .open (count + 1), writeEnd := row.writeEnd + 1 }
    have tailFits : (count + 1) + rest.length < 2 ^ 32 := by simp only [List.length_cons] at fits; omega
    obtain ⟨after, finalRow, finalStorage, tail, finalParent, finalFound, finalStored, finalPhase,
      finalPacked, finalAdaptation, finalUse, finalRequest, finalCurrent⟩ :=
      ih { state with construction := written } (count + 1) nextRow nextStorage parentAfter nextPresent nextStored rfl
        packed adaptation use request nextCurrent tailFits
    refine ⟨after, finalRow, finalStorage, ?_, finalParent, finalFound, finalStored, ?_,
      finalPacked, finalAdaptation, finalUse, finalRequest, finalCurrent⟩
    · simp only [List.forIn_cons, receivingAction, liftConstruction, renewal, bind, write, pure]
      exact tail
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using finalPhase

#print axioms packed_replacement_byte_loop

theorem packed_replacement_byte_build (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (bytes : List UInt8) (origin : OriginId) (state : ExecutionState)
    (incoming selected parentCount count : Nat) (parent row : PendingDestination) (storage : ReceivingStorage)
    (parentFound : state.construction.destinations[incoming]? = some parent) (parentUse : parent.use = .receiver)
    (parentPhase : parent.progress = .exiting parentCount selected) (earlier : incoming < selected)
    (present : state.construction.destinations[selected]? = some row) (stored : state.construction.storage[row.storage]? = some storage)
    (opened : row.progress = .open count) (packed : row.layout = .packed)
    (adaptation : row.adaptation = none) (use : row.use = .replacement incoming)
    (request : row.capability.request = .value)
    (current : destinationCurrent state.construction selected = .ok selected) (fits : count + bytes.length < 2 ^ 32) :
    ∃ after, buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin) state = .ok () after := by
  have renewal : renewReceivingDestination selected state.construction = .ok selected state.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, present, opened]
  obtain ⟨middle, finalRow, finalStorage, loop, parentAfter, finalFound, finalStored, finalOpened,
    finalPacked, finalAdaptation, finalUse, finalRequest, finalCurrent⟩ :=
    packed_replacement_byte_loop bytes origin state incoming selected parentCount count parent row storage parentFound parentUse
      parentPhase earlier present stored opened packed adaptation use request current fits
  have writable := fresh_replacement_of_receiver_writable middle.construction incoming selected parentCount parent finalRow
    parentAfter parentUse parentPhase finalFound finalUse earlier
  obtain ⟨finished, finish⟩ := packed_finish_success middle.construction selected (count + bytes.length)
    finalRow finalStorage finalFound finalStored finalOpened finalPacked finalRequest writable
  have finalRenewal : renewReceivingDestination selected middle.construction = .ok selected middle.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, finalCurrent, pure,
      lookupDestination_result, finalFound, finalOpened]
  have body : (do
      for byte in bytes do receivingAction origin selected (fun destination => writeElement destination ⟨#[byte]⟩)
      receivingAction origin selected finishDestination) state = .ok () { middle with construction := finished } := by
    simp only [bind] at loop ⊢
    rw [loop]
    simp only [receivingAction, liftConstruction, finalRenewal, finish, bind, pure]
  refine ⟨{ middle with construction := finished }, ?_⟩
  simp only [buildExpr, liftConstruction, renewal, bind]
  change protectDestination origin selected
    (do
      for byte in bytes do receivingAction origin selected (fun destination => writeElement destination ⟨#[byte]⟩)
      receivingAction origin selected finishDestination) state = _
  simp only [protectDestination, body]

#print axioms packed_replacement_byte_build

theorem accepted_packed_reservation_build (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (bytes : List UInt8) (origin : OriginId)
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
    (fits : bytes.length < 2 ^ 32) :
    ∃ after, buildExpr (fuel + 1) config environment selected (.bytes (.varr (.int .u8)) bytes origin)
      { before with construction := reserved } = .ok () after := by
  obtain ⟨ready, packed, request, resolved⟩ := accepted_packed_reservation_ready config initialized before reserved incoming selected token count
    receiver receiverPacked receiverRequest current ambient types live regions pending world reservation
  obtain ⟨metadata, metadataFound, _, adaptation⟩ := reserve_open_replacement_metadata before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
  have same := Option.some.inj (metadataFound.symm.trans ready.present)
  subst metadata
  have unchanged : ready.destination.adaptation = none := adaptation.trans receiverAdaptation
  have indexed := world.ownership.source.structural.1.1.1.2.1 incoming receiver.destination receiver.present
  have fresh := reserve_open_replacement_fresh before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have earlier : incoming < selected := by rw [fresh]; exact (Array.getElem?_eq_some_iff.mp receiver.present).1
  have ticket := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened current reservation).2
  have roles := accepted_open_reservation_successor_roles config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
  have use := roles token incoming selected selected receiver.destination ready.destination ticket (.refl selected) ready.present
  simp only [indexed, if_neg (Nat.ne_of_gt earlier)] at use
  have parent := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
    receiver.present receiver.opened current reservation).1
  exact packed_replacement_byte_build fuel config environment bytes origin { before with construction := reserved } incoming selected
    (count + 1) 0 { receiver.destination with progress := .exiting (count + 1) selected } ready.destination ready.storage
    parent receiverUse rfl earlier ready.present ready.bytes ready.opened packed unchanged use.1 request resolved (by simpa using fits)

#print axioms accepted_packed_reservation_build

theorem accepted_nested_byte_handler_derived_build (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId incoming selected token count : Nat)
    (bytes : List UInt8) (origin : OriginId) (outerRest innerRest : List Stmt)
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
    (fits : bytes.length < 2 ^ 32) :
    ∃ (after final : ExecutionState),
      buildExpr (fuel + 1) config { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes }
        selected (.bytes (.varr (.int .u8)) bytes origin) { innerBound with construction := reserved } = .ok () after ∧
      enterActivation (fuel + 13) config outer outerPre
      (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
      .ok [.completed selected] final ∧
      final.construction.stdout = after.construction.stdout ∧
      ∀ entry : RootInst × Value,
        (Goose.Proofs.Exit.runtimeScopeRoots inner innerScope innerEntered.nextScope).contains entry.1 = false →
        (Goose.Proofs.Exit.runtimeScopeRoots outer outerScope outerInitial.nextScope).contains entry.1 = false →
        (entry ∈ final.objects ↔ entry ∈ after.objects) := by
  obtain ⟨after, built⟩ := accepted_packed_reservation_build fuel config initialized
    { inner with scopes := (innerScope, innerEntered.nextScope) :: inner.scopes } bytes origin innerBound reserved
    incoming selected token count receiver receiverRole packed request receiverAdaptation receiverCurrent ambient types live regions pending world reservation fits
  obtain ⟨final, result⟩ := accepted_nested_byte_handler_derived_ready fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live regions pending baseRegion outerLookup results outerChannels
    outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver receiverRole receiverAdaptation
    receiverPhysical receiverCurrent world history reservation covered integers other baseMember baseDestination outside
    packed request fits built
  exact ⟨after, final, built, result⟩

#print axioms accepted_nested_byte_handler_derived_build

end Goose.Proofs.ConstructionAcceptedExecution
