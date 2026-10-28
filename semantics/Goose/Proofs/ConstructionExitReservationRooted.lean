import Goose.Proofs.ConstructionExitReservationRegister

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem reserve_open_rooted_backing (layout : LayoutEnv) (before : ExecutionState)
    (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (live : RootInst → Prop) (backing : RootedBackingState layout before live) :
    RootedBackingState layout { before with construction := reserved } live := by
  constructor
  · intro root rootLive value found
    exact reserve_open_any_value_backing layout before reserved incoming selected token count receiver current reservation value
      (backing.values root rootLive value found)
  · exact backing.identities

#print axioms reserve_open_rooted_backing

theorem accepted_world_does_not_imply_pending_coverage (config : EvalConfig)
    (accepted : validate config.module = .ok ()) :
    ∃ ambient,
      AcceptedWorld config 0 .initial ambient (declaredRootTypes config.module) (fun _ => False) [] [] ∧
      ¬ (∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ ([] : List PendingCarrierFrame),
        .completed id ∈ frame.carriers) := by
  let ambient : OwnershipAmbient := [.returned [.completed 0]]
  have initial := initial_acceptedWorld config accepted
  have ownership := ownershipExecutionContext_returned .initial [] [.completed 0] initial.ownership
  have world : AcceptedWorld config 0 .initial ambient (declaredRootTypes config.module) (fun _ => False) [] [] :=
    ⟨{ initial.toAcceptedWorldCore with ownership := ownership }, initial.globalLive⟩
  refine ⟨ambient, world, ?_⟩
  intro coverage
  have member : .completed 0 ∈ ambient.retained := by simp [ambient, OwnershipAmbient.retained, OwnershipAmbientFrame.carriers]
  obtain ⟨frame, member, found⟩ := coverage 0 member
  cases member

#print axioms accepted_world_does_not_imply_pending_coverage

theorem accepted_world_does_not_imply_reference_bounds (config : EvalConfig)
    (accepted : validate config.module = .ok ()) :
    ∃ ambient,
      AcceptedWorld config 0 .initial ambient (declaredRootTypes config.module) (fun _ => False) [] [] ∧
      ¬ ReservationReferencesBounded .initial ambient := by
  let ambient : OwnershipAmbient := [.exitChannels [0] [] []]
  have initial := initial_acceptedWorld config accepted
  have ownership : OwnershipExecutionContext .initial ambient := by
    refine ⟨initial.ownership.source, ?_, ⟨rfl, rfl⟩, ?_, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, initial.ownership.identities⟩
    · refine ⟨initial.ownership.retention.structural, ?_, ?_⟩
      · intro id row present
        simp [ExecutionState.initial, ConstructionState.initial] at present
      · simp [ambient, OwnershipAmbientBoundaries, RetainedOutsideTickets, OwnershipAmbientFrame.tickets,
          OwnershipAmbient.retained, completedCarrierIds, ExecutionState.initial, ConstructionState.initial]
    · intro token reservation present
      simp [ExecutionState.initial, ConstructionState.initial] at present
  have world : AcceptedWorld config 0 .initial ambient (declaredRootTypes config.module) (fun _ => False) [] [] :=
    ⟨{ initial.toAcceptedWorldCore with ownership := ownership }, initial.globalLive⟩
  refine ⟨ambient, world, ?_⟩
  intro bounded
  have invalid := (bounded (.exitChannels [0] [] []) (by simp [ambient])).1 0 (by simp [OwnershipAmbientFrame.tickets])
  simp [ConstructionState.initial] at invalid

#print axioms accepted_world_does_not_imply_reference_bounds

theorem accepted_open_reservation_world_rooted (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : List Channel) (carriers : List Goose.Construct.Carrier)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (history : ReservationReferencesBounded before.construction ambient)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (covered : ∀ id, .completed id ∈ ambient.retained → ∃ frame ∈ pending, .completed id ∈ frame.carriers)
    (other : ∀ region ∈ regions, region.destination ≠ incoming →
      incoming ∈ region.mutableDestinations ∧ region.limit receiver.destination.storage ≤ receiver.storage.bytes.size)
    :
    AcceptedWorld config initialized { before with construction := reserved }
      (.exitChannels [token] channels carriers :: ambient) types live
      (regions.map (reserveReceivingRegion incoming selected)) pending := by
  have context := accepted_open_reservation_execution_context config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world history reservation covered
  have backing := reserve_open_rooted_backing config.layout before reserved incoming selected token count
    receiver current reservation live world.backing
  refine ⟨⟨context, world.globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier,
    world.heap, world.objectsRegistered, world.ordinalsRegistered, backing, ?_, ?_⟩, world.globalLive⟩
  · intro target member
    obtain ⟨region, original, equal⟩ := List.mem_map.mp member
    subst target
    by_cases same : region.destination = incoming
    · simp only [reserveReceivingRegion, same, ↓reduceIte]
      simpa only [same] using (reserve_open_extended_protection config.layout before reserved incoming selected token count receiver current reservation
        live region same (world.protections region original))
    · simp only [reserveReceivingRegion, same, ↓reduceIte]
      obtain ⟨authority, cutoff⟩ := other region original same
      exact reserve_open_other_region_protection config.layout before reserved incoming selected token count receiver current reservation
        live region same authority cutoff (world.protections region original)
  · intro frame member
    exact accepted_reservation_any_carrier_frame config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation frame member

#print axioms accepted_open_reservation_world_rooted

theorem accepted_nested_byte_handler_rooted_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId incoming selected token count : Nat)
    (bytes : List UInt8) (origin : OriginId) (outerRest innerRest : List Stmt)
    (outerTail innerTail : Option Expr) (contextId : ContextId) (arguments : List Arg)
    (callChannels exitChannels : List Channel)
    (outerInitial outerBound callPrepared innerEntered innerBound : ExecutionState)
    (outerImpl innerImpl calledImpl : Impl) (calledId : ImplId)
    (reserved : ConstructionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
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
    (other : ∀ region ∈ regions, region.destination ≠ incoming →
      incoming ∈ region.mutableDestinations ∧ region.limit receiver.destination.storage ≤ receiver.storage.bytes.size)
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
  obtain ⟨ready, selectedPacked, selectedRequest, selectedCurrent⟩ :=
    accepted_packed_reservation_ready config initialized innerBound reserved incoming selected token count receiver packed request
      receiverCurrent ambient types live regions pending world reservation
  have reservedWorld := accepted_open_reservation_world_rooted config initialized innerBound reserved incoming selected token count
    receiver receiverCurrent ambient types live regions pending exitChannels [.completed selected] world history reservation
    covered other
  obtain ⟨final, result⟩ := Goose.Proofs.ExitExecution.accepted_nested_byte_handler fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count 0 bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live (regions.map (reserveReceivingRegion incoming selected)) pending
    outerLookup results outerChannels outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver
    receiverRole receiverAdaptation receiverPhysical receiverCurrent world.ownership.source.structural.1.1 reservation reservedWorld
    ready selectedPacked selectedRequest (by simpa using fits) selectedCurrent built
  exact ⟨after, final, built, result⟩

#print axioms accepted_nested_byte_handler_rooted_world

end Goose.Proofs.ConstructionAcceptedExecution
