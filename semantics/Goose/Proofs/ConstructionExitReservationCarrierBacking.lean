import Goose.Proofs.ConstructionExitReservationLanding

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem reserve_open_stored_backing (layout : LayoutEnv) (before : ExecutionState)
    (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (stored : StoredValue) (backed : StoredValueBacking layout before stored)
    (separate : stored.destination ≠ some incoming) :
    StoredValueBacking layout { before with construction := reserved } stored := by
  let limit : Nat → Nat := fun id => ((before.construction.storage[id]?).map fun storage => storage.bytes.size).getD 0
  have cutoff : limit receiver.destination.storage ≤ receiver.storage.bytes.size := by simp [limit, receiver.bytes]
  have prefixes := reserve_open_storage_prefix before.construction reserved incoming selected token count
    receiver.destination receiver.storage limit receiver.present receiver.opened receiver.bytes cutoff current reservation
  have rows := reserve_open_other_rows before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
  obtain ⟨storage, run, present, sampled, interval⟩ := backed.sampled layout before stored
  obtain ⟨updated, found, published, bytes⟩ := prefixes.lookup _ _ _ stored.storage storage present
  have frame : StoredBackingPrefixFrame before { before with construction := reserved } limit stored := by
    refine ⟨⟨storage, updated, present, found, ?_, published⟩, ?_⟩
    · apply BytePrefixEqual.of_extract_eq
      · simp [limit, present]
      · exact bytes
    · intro id named
      have distinct : id ≠ incoming := by
        intro same
        subst id
        exact separate named
      have oldBound : id < before.construction.destinations.size := by
        cases backed with
        | detached storage element present detached ty interval => rw [detached] at named; cases named
        | named old storage row n present name binding rest =>
          have equal := Option.some.inj (name.symm.trans named)
          subst old
          exact (Array.getElem?_eq_some_iff.mp binding).1
      exact rows.2 id distinct oldBound
  exact backed.prefix_frame layout before { before with construction := reserved } limit stored
    (backed.observation layout before stored) frame

#print axioms reserve_open_stored_backing

theorem reserve_open_value_backing (layout : LayoutEnv) (before : ExecutionState)
    (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (value : Value) (backed : ValueStorageBacked layout before value)
    (separate : ∀ stored, StoredOccurrence value stored → stored.destination ≠ some incoming) :
    ValueStorageBacked layout { before with construction := reserved } value := by
  induction backed with
  | integer ty value => exact .integer ty value
  | boolean value => exact .boolean value
  | unit => exact .unit
  | reference location => exact .reference location
  | slice location start count => exact .slice location start count
  | stored value valid =>
    exact .stored value (reserve_open_stored_backing layout before reserved incoming selected token count receiver current reservation
      value valid (separate value (.stored value)))
  | array values children ih =>
    exact .array values (fun child member => ih child member (fun stored occurrence =>
      separate stored (.array values child stored member occurrence)))
  | record id values children ih =>
    exact .record id values (fun child member => ih child member (fun stored occurrence =>
      separate stored (.record id values child stored member occurrence)))

#print axioms reserve_open_value_backing

theorem stored_destination_same_row (before after : ExecutionState) (id : Nat)
    (row : PendingDestination) (stored : StoredValue)
    (old : before.construction.destinations[id]? = some row)
    (new : after.construction.destinations[id]? = some row)
    (sampled : storedDestination id before = .ok stored before) :
    stored.destination = some id ∧ storedDestination id after = .ok stored after := by
  simp only [storedDestination, getDestination, EvalM.get, bind, old, new, pure] at sampled ⊢
  cases progress : progressCount row.progress with
  | none => simp only [progress, fault, EvalM.stop] at sampled; cases sampled
  | some n =>
    simp only [progress] at sampled ⊢
    cases sampled
    exact ⟨rfl, rfl⟩

theorem accepted_reservation_unrooted_carrier_backing (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (carrier : Carrier) (backed : CarrierResultBacking config.layout before carrier)
    (registerSeparate : ∀ value, carrier = .register value → ∀ stored,
      StoredOccurrence value stored → stored.destination ≠ some incoming) :
    CarrierResultBacking config.layout { before with construction := reserved } carrier := by
  have rows := reserve_open_other_rows before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
  have tickets := accepted_fresh_reservation_frames config initialized before reserved incoming token selected
    ambient types live regions pending world reservation [] []
  cases backed with
  | register value valid =>
    exact .register _ (reserve_open_value_backing config.layout before reserved incoming selected token count receiver current reservation
      value valid (registerSeparate value rfl))
  | completed id n row stored found built sampled valid =>
    have different : id ≠ incoming := by
      intro same
      subst id
      have equal := Option.some.inj (found.symm.trans receiver.present)
      subst row
      rw [receiver.opened] at built
      cases built
    have afterFound : reserved.destinations[id]? = some row := by
      rw [rows.2 id different (Array.getElem?_eq_some_iff.mp found).1]
      exact found
    have sampledFrame := stored_destination_same_row before { before with construction := reserved } id row stored found afterFound sampled
    have separate : stored.destination ≠ some incoming := by
      rw [sampledFrame.1]
      intro equal
      exact different (Option.some.inj equal)
    exact .completed id n row stored afterFound built sampledFrame.2
      (reserve_open_stored_backing config.layout before reserved incoming selected token count receiver current reservation stored valid separate)
  | pendingNamed named oldIncoming oldSelected n snapshot row stored ticket found marked phase sampled valid =>
    have different : oldSelected ≠ incoming := by
      intro same
      subst oldSelected
      have equal := Option.some.inj (found.symm.trans receiver.present)
      subst row
      rcases phase with built | ⟨child, suspended⟩ | ⟨next, exiting⟩ <;>
        rw [receiver.opened] at * <;> contradiction
    have afterFound : reserved.destinations[oldSelected]? = some row := by
      rw [rows.2 oldSelected different (Array.getElem?_eq_some_iff.mp found).1]
      exact found
    have sampledFrame := stored_destination_same_row before { before with construction := reserved } oldSelected row stored found afterFound sampled
    have separate : stored.destination ≠ some incoming := by
      rw [sampledFrame.1]
      intro equal
      exact different (Option.some.inj equal)
    have afterTicket := (tickets.2.1 named _ ticket).2
    exact .pendingNamed named oldIncoming oldSelected n snapshot row stored afterTicket afterFound marked phase sampledFrame.2
      (reserve_open_stored_backing config.layout before reserved incoming selected token count receiver current reservation stored valid separate)

#print axioms accepted_reservation_unrooted_carrier_backing

def SeparatedPending (state : ExecutionState) (incoming : Nat) (frame : PendingCarrierFrame) : Prop :=
  (∀ value, .register value ∈ frame.carriers → ∀ stored,
    StoredOccurrence value stored → stored.destination ≠ some incoming) ∧
  (∀ channel id, (.construct channel, .completed id) ∈ frame.channels.zip frame.carriers →
    ∀ ready : ReceivingCarrierLandingReady state channel id, ready.receiving ≠ incoming) ∧
  (∀ token id role oldIncoming selected snapshot,
    (.completion token, .completed id) ∈ frame.channels.zip frame.carriers →
    state.construction.exitReservations[token]? = some (.active role oldIncoming selected snapshot) →
    ∀ ready : ReceivingCarrierLandingReady state selected id, ready.receiving ≠ incoming)

theorem accepted_reservation_separated_carrier_frame (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) (separated : SeparatedPending before incoming frame) :
    CarriersLandingReady { before with construction := reserved } frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { before with construction := reserved } carrier := by
  obtain ⟨priorReady, priorBacking⟩ := world.carriers frame member
  have transfer (carrier : Carrier) (present : carrier ∈ frame.carriers) :
      CarrierResultBacking config.layout { before with construction := reserved } carrier :=
    accepted_reservation_unrooted_carrier_backing config initialized before reserved incoming selected token count receiver current
      ambient types live regions pending world reservation carrier (priorBacking carrier present) (by
        intro value equal
        subst carrier
        exact separated.1 value present)
  have sourceSeparate (id : Nat) (present : .completed id ∈ frame.carriers) : id ≠ incoming := by
    have backing := priorBacking (.completed id) present
    cases backing with
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
    obtain ⟨afterReady⟩ := accepted_reservation_landing_ready config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation channel id ready (sourceSeparate id present)
      (separated.2.1 channel id pair ready)
    exact .construct channel id afterReady
  | completion named oldIncoming oldSelected id role snapshot ticket ready =>
    obtain ⟨afterReady⟩ := accepted_reservation_landing_ready config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation oldSelected id ready (sourceSeparate id present)
      (separated.2.2 named id role oldIncoming oldSelected snapshot pair ticket ready)
    exact .completion named oldIncoming oldSelected id role snapshot (tickets.2.1 named _ ticket).2 afterReady

#print axioms accepted_reservation_separated_carrier_frame

theorem accepted_open_reservation_world_unrooted (config : EvalConfig) (initialized : Nat)
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
    (separated : ∀ frame ∈ pending, SeparatedPending before incoming frame)
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
    exact accepted_reservation_separated_carrier_frame config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation frame member (separated frame member)

#print axioms accepted_open_reservation_world_unrooted

theorem accepted_nested_byte_handler_unrooted (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
    (separated : ∀ frame ∈ pending, SeparatedPending innerBound incoming frame)
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
  have reservedWorld := accepted_open_reservation_world_unrooted config initialized innerBound reserved incoming selected token count
    receiver receiverCurrent ambient types live regions pending exitChannels [.completed selected] world history reservation
    covered separated other baseRegion baseMember baseDestination outside
  obtain ⟨final, result⟩ := Goose.Proofs.ExitExecution.accepted_nested_byte_handler fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count 0 bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live (regions.map (reserveReceivingRegion incoming selected)) pending
    outerLookup results outerChannels outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver
    receiverRole receiverAdaptation receiverPhysical receiverCurrent world.ownership.source.structural.1.1 reservation reservedWorld
    ready selectedPacked selectedRequest (by simpa using fits) selectedCurrent built
  exact ⟨after, final, built, result⟩

#print axioms accepted_nested_byte_handler_unrooted

end Goose.Proofs.ConstructionAcceptedExecution
