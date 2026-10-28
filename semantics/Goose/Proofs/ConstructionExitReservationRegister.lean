import Goose.Proofs.ConstructionExitReservationOverlap

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem reserve_open_any_stored_backing (layout : LayoutEnv) (before : ExecutionState)
    (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (stored : StoredValue) (backed : StoredValueBacking layout before stored) :
    StoredValueBacking layout { before with construction := reserved } stored := by
  by_cases separate : stored.destination ≠ some incoming
  · exact reserve_open_stored_backing layout before reserved incoming selected token count receiver current reservation stored backed separate
  · have named : stored.destination = some incoming := Classical.not_not.mp separate
    have parent := (reserve_open_receiver_snapshot before.construction reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current reservation).1
    let limit : Nat → Nat := fun id => ((before.construction.storage[id]?).map fun storage => storage.bytes.size).getD 0
    have cutoff : limit receiver.destination.storage ≤ receiver.storage.bytes.size := by simp [limit, receiver.bytes]
    have prefixes := reserve_open_storage_prefix before.construction reserved incoming selected token count
      receiver.destination receiver.storage limit receiver.present receiver.opened receiver.bytes cutoff current reservation
    cases backed with
    | detached storage element present detached ty interval => rw [detached] at named; cases named
    | named id storage row oldCount present source binding backing ty start phase element elementType interval =>
      have sameId := Option.some.inj (source.symm.trans named)
      subst id
      have sameRow := Option.some.inj (binding.symm.trans receiver.present)
      subst row
      have sameCount : oldCount = count + 1 := by
        rw [receiver.opened] at phase
        exact (Option.some.inj phase).symm
      subst oldCount
      obtain ⟨updated, updatedFound, published, bytes⟩ := prefixes.lookup _ _ _ stored.storage storage present
      have equalPrefix : BytePrefixEqual storage.bytes updated.bytes storage.bytes.size := by
        apply BytePrefixEqual.of_extract_eq
        · exact Nat.le_refl _
        · simpa only [limit, present, Option.map_some, Option.getD_some] using bytes
      simp only [receiver.opened] at interval backing
      obtain ⟨fuel, finish, scanned, lower, upper⟩ := interval.interval
      have newScan := equalPrefix.elementsEnd fuel layout element
        (storedWrittenRun stored ⟨stored.start + (if receiver.destination.layout == .packed &&
          receiver.destination.capability.request == .value then 4 else 0), count + 1, element⟩).count
        (stored.start + (if receiver.destination.layout == .packed && receiver.destination.capability.request == .value then 4 else 0))
        finish (by simpa only [storedWrittenRun] using scanned) upper
      have newInterval : SampledRunBacking layout updated.bytes
          (storedWrittenRun stored ⟨stored.start + (if receiver.destination.layout == .packed &&
            receiver.destination.capability.request == .value then 4 else 0), count + 1, element⟩) :=
        ⟨fuel, finish, newScan, lower, Nat.le_trans upper equalPrefix.afterBound⟩
      exact .named incoming updated { receiver.destination with progress := .exiting (count + 1) selected } (count + 1)
        updatedFound named parent (by simpa only [PendingDestination.storage] using backing) ty start rfl element elementType
        (by simpa [receiver.opened] using newInterval)

#print axioms reserve_open_any_stored_backing

theorem reserve_open_any_value_backing (layout : LayoutEnv) (before : ExecutionState)
    (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (value : Value) (backed : ValueStorageBacked layout before value) :
    ValueStorageBacked layout { before with construction := reserved } value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | stored value valid =>
    exact .stored value (reserve_open_any_stored_backing layout before reserved incoming selected token count receiver current reservation value valid)
  | array values children ih => exact .array values ih
  | record id values children ih => exact .record id values ih

#print axioms reserve_open_any_value_backing

theorem accepted_reservation_any_carrier_frame (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) :
    CarriersLandingReady { before with construction := reserved } frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { before with construction := reserved } carrier := by
  obtain ⟨priorReady, priorBacking⟩ := world.carriers frame member
  have transfer (carrier : Carrier) (present : carrier ∈ frame.carriers) :
      CarrierResultBacking config.layout { before with construction := reserved } carrier := by
    have backed := priorBacking carrier present
    cases backed with
    | register value valid =>
      exact .register value (reserve_open_any_value_backing config.layout before reserved incoming selected token count receiver current reservation value valid)
    | completed id n row stored found built sampled valid =>
      exact accepted_reservation_unrooted_carrier_backing config initialized before reserved incoming selected token count receiver current
        ambient types live regions pending world reservation (.completed id) (.completed id n row stored found built sampled valid)
        (by intro value impossible; cases impossible)
    | pendingNamed named oldIncoming oldSelected n snapshot row stored ticket found marked phase sampled valid =>
      exact accepted_reservation_unrooted_carrier_backing config initialized before reserved incoming selected token count receiver current
        ambient types live regions pending world reservation (.pendingNamed named)
        (.pendingNamed named oldIncoming oldSelected n snapshot row stored ticket found marked phase sampled valid)
        (by intro value impossible; cases impossible)
  have sourceSeparate (id : Nat) (present : .completed id ∈ frame.carriers) : id ≠ incoming := by
    have backed := priorBacking (.completed id) present
    cases backed with
    | completed id n row stored found built sampled valid =>
      intro same
      subst id
      have equal := Option.some.inj (found.symm.trans receiver.present)
      subst row
      rw [receiver.opened] at built
      cases built
  have tickets := accepted_fresh_reservation_frames config initialized before reserved incoming token selected
    ambient types live regions pending world reservation [] []
  refine ⟨⟨priorReady.lengths, ?_⟩, transfer⟩
  intro channel carrier pair
  have present := (List.of_mem_zip pair).2
  have prior := priorReady.pairs channel carrier pair
  cases prior with
  | register ty value => exact .register ty value
  | pendingNamed named oldIncoming oldSelected snapshot ticket =>
    exact .pendingNamed named oldIncoming oldSelected snapshot (tickets.2.1 named _ ticket).2
  | construct channel id ready =>
    have separate := accepted_completed_landing_separate config initialized before incoming (count + 1) receiver ambient types live
      regions pending world channel id ready (priorBacking (.completed id) present)
    obtain ⟨afterReady⟩ := accepted_reservation_landing_ready config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation channel id ready (sourceSeparate id present) separate
    exact .construct channel id afterReady
  | completion named oldIncoming oldSelected id role snapshot ticket ready =>
    have separate := accepted_completed_landing_separate config initialized before incoming (count + 1) receiver ambient types live
      regions pending world oldSelected id ready (priorBacking (.completed id) present)
    obtain ⟨afterReady⟩ := accepted_reservation_landing_ready config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation oldSelected id ready (sourceSeparate id present) separate
    exact .completion named oldIncoming oldSelected id role snapshot (tickets.2.1 named _ ticket).2 afterReady

#print axioms accepted_reservation_any_carrier_frame

theorem accepted_open_reservation_world_all_carriers (config : EvalConfig) (initialized : Nat)
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
    (base : ReceivingRegion) (baseMember : base ∈ regions) (baseDestination : base.destination = incoming)
    (outside : ∀ root, live root → ¬ base.mutableRoots root) :
    AcceptedWorld config initialized { before with construction := reserved }
      (.exitChannels [token] channels carriers :: ambient) types live
      (regions.map (reserveReceivingRegion incoming selected)) pending := by
  have context := accepted_open_reservation_execution_context config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world history reservation covered
  have backing := accepted_open_reservation_rooted_backing config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation base baseMember baseDestination outside
  refine ⟨⟨context, world.globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier,
    world.heap, world.objectsRegistered, world.ordinalsRegistered, backing.1, ?_, ?_⟩, world.globalLive⟩
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

#print axioms accepted_open_reservation_world_all_carriers

theorem accepted_nested_byte_handler_all_carriers (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
  obtain ⟨ready, selectedPacked, selectedRequest, selectedCurrent⟩ :=
    accepted_packed_reservation_ready config initialized innerBound reserved incoming selected token count receiver packed request
      receiverCurrent ambient types live regions pending world reservation
  have reservedWorld := accepted_open_reservation_world_all_carriers config initialized innerBound reserved incoming selected token count
    receiver receiverCurrent ambient types live regions pending exitChannels [.completed selected] world history reservation
    covered other baseRegion baseMember baseDestination outside
  obtain ⟨final, result⟩ := Goose.Proofs.ExitExecution.accepted_nested_byte_handler fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count 0 bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live (regions.map (reserveReceivingRegion incoming selected)) pending
    outerLookup results outerChannels outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver
    receiverRole receiverAdaptation receiverPhysical receiverCurrent world.ownership.source.structural.1.1 reservation reservedWorld
    ready selectedPacked selectedRequest (by simpa using fits) selectedCurrent built
  exact ⟨after, final, built, result⟩

#print axioms accepted_nested_byte_handler_all_carriers

end Goose.Proofs.ConstructionAcceptedExecution
