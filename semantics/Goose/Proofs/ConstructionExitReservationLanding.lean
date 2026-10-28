import Goose.Proofs.ConstructionExitReservationCompleted

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem replacement_path_source_extension (before after : ConstructionState)
    (extension : OwnershipSourceExtension before after) (receiving source : Nat)
    (path : OwnershipReplacementPath before.destinations receiving source) :
    OwnershipReplacementPath after.destinations receiving source := by
  induction path with
  | refl => exact .refl _
  | step id parent ancestor row present use tail ih =>
    obtain ⟨updated, found, sameUse, _⟩ := extension id row present
    exact .step id parent ancestor updated found (sameUse.trans use) ih

theorem accepted_reservation_landing_ready (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (channel source : Nat) (ready : ReceivingCarrierLandingReady before channel source)
    (sourceSeparate : source ≠ incoming) (receivingSeparate : ready.receiving ≠ incoming) :
    Nonempty (ReceivingCarrierLandingReady { before with construction := reserved } channel source) := by
  obtain ⟨allocated, replacement, appended, _, _, _⟩ :=
    accepted_open_reservation_allocation config initialized before reserved incoming selected token count receiver.destination
      receiver.present receiver.opened current ambient types live regions pending [] [] world reservation
  have rows := reserve_open_other_rows before.construction reserved incoming selected token count receiver.destination receiver.storage
    receiver.present receiver.opened receiver.bytes current reservation
  have map := openExitReplacement_successorMap incoming before.construction
  rw [replacement] at map
  have successors : reserved.destinationSuccessors = before.construction.destinationSuccessors := by
    simpa only [ConstructionResult.finalState, appended] using map
  have size : before.construction.destinations.size ≤ reserved.destinations.size := by rw [rows.1]; omega
  have extension := openExitReplacement_ownership_source incoming before.construction world.ownership.source.structural.1.1.1
  rw [replacement] at extension
  have extensionAfter : OwnershipSourceExtension before.construction reserved := by
    simpa only [ConstructionResult.finalState, appended, OwnershipSourceExtension] using extension
  have sourceFound : reserved.destinations[source]? = some ready.sourceDestination := by
    rw [rows.2 source sourceSeparate (Array.getElem?_eq_some_iff.mp ready.sourcePresent).1]
    exact ready.sourcePresent
  have receivingFound : reserved.destinations[ready.receiving]? = some ready.receivingDestination := by
    rw [rows.2 ready.receiving receivingSeparate (Array.getElem?_eq_some_iff.mp ready.receivingPresent).1]
    exact ready.receivingPresent
  have parentReady : LandingParentReady reserved ready.receiving ready.receivingDestination := by
    cases ready.parent with
    | receiver use => exact .receiver use
    | child owner n parent use found progress =>
      have separate : owner ≠ incoming := by
        intro same
        subst owner
        have equal := Option.some.inj (found.symm.trans receiver.present)
        subst parent
        rw [receiver.opened] at progress
        cases progress
      have parentAfter : reserved.destinations[owner]? = some parent := by
        rw [rows.2 owner separate (Array.getElem?_eq_some_iff.mp found).1]
        exact found
      exact .child owner n parent use parentAfter progress
    | replacement owner n parent use found progress =>
      have separate : owner ≠ incoming := by
        intro same
        subst owner
        have equal := Option.some.inj (found.symm.trans receiver.present)
        subst parent
        rw [receiver.opened] at progress
        cases progress
      have parentAfter : reserved.destinations[owner]? = some parent := by
        rw [rows.2 owner separate (Array.getElem?_eq_some_iff.mp found).1]
        exact found
      exact .replacement owner n parent use parentAfter progress
  exact ⟨⟨ready.receiving, ready.sourceDestination, ready.receivingDestination,
    destinationCurrent_extension before.construction reserved successors size channel ready.receiving ready.resolved,
    sourceFound, receivingFound, replacement_path_source_extension before.construction reserved extensionAfter _ _ ready.path,
    parentReady, ready.ordered⟩⟩

#print axioms replacement_path_source_extension
#print axioms accepted_reservation_landing_ready

theorem accepted_reservation_rooted_completed_backing (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (region : ReceivingRegion) (member : region ∈ regions) (regionDestination : region.destination = incoming)
    (outside : ∀ root, live root → ¬ region.mutableRoots root)
    (id : Nat) (backed : CarrierResultBacking config.layout before (.completed id))
    (rooted : ∀ stored, storedDestination id before = .ok stored before →
      ∃ root, live root ∧ before.objects.lookup root = some (.stored stored)) :
    id ≠ incoming ∧ CarrierResultBacking config.layout { before with construction := reserved } (.completed id) := by
  have rootBacking := (accepted_open_reservation_rooted_backing config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation region member regionDestination outside).1
  cases backed with
  | completed id n row stored found built sampled prior =>
    have different : id ≠ incoming := by
      intro same
      subst id
      have equal := Option.some.inj (found.symm.trans receiver.present)
      subst row
      rw [receiver.opened] at built
      cases built
    have frames := reserve_open_other_rows before.construction reserved incoming selected token count
      receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
    have foundAfter : reserved.destinations[id]? = some row := by
      rw [frames.2 id different (Array.getElem?_eq_some_iff.mp found).1]
      exact found
    have sampledAfter : storedDestination id { before with construction := reserved } =
        .ok stored { before with construction := reserved } := by
      simp only [storedDestination, getDestination, EvalM.get, bind, found, built, progressCount, pure] at sampled
      cases sampled
      simp only [storedDestination, getDestination, EvalM.get, bind, foundAfter, built, progressCount, pure]
    obtain ⟨root, rootLive, rootFound⟩ := rooted stored sampled
    have valueBacked := rootBacking.values root rootLive (.stored stored) rootFound
    have afterBacking : StoredValueBacking config.layout { before with construction := reserved } stored := by
      cases valueBacked with
      | stored value backing => exact backing
    exact ⟨different, .completed id n row stored foundAfter built sampledAfter afterBacking⟩

#print axioms accepted_reservation_rooted_completed_backing

def RootedSeparatedPending (state : ExecutionState) (live : RootInst → Prop)
    (incoming : Nat) (frame : PendingCarrierFrame) : Prop :=
  (∀ carrier ∈ frame.carriers, match carrier with
    | .register value => ∃ ty integer, value = .int ty integer
    | .completed id => ∀ stored, storedDestination id state = .ok stored state →
        ∃ root, live root ∧ state.objects.lookup root = some (.stored stored)
    | .pendingNamed _ => False) ∧
  (∀ channel id, (.construct channel, .completed id) ∈ frame.channels.zip frame.carriers →
    ∀ ready : ReceivingCarrierLandingReady state channel id, ready.receiving ≠ incoming) ∧
  (∀ token id role oldIncoming selected snapshot,
    (.completion token, .completed id) ∈ frame.channels.zip frame.carriers →
    state.construction.exitReservations[token]? = some (.active role oldIncoming selected snapshot) →
    ∀ ready : ReceivingCarrierLandingReady state selected id, ready.receiving ≠ incoming)

theorem accepted_reservation_separated_pending_frame (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (region : ReceivingRegion) (regionMember : region ∈ regions) (regionDestination : region.destination = incoming)
    (outside : ∀ root, live root → ¬ region.mutableRoots root)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) (separated : RootedSeparatedPending before live incoming frame) :
    CarriersLandingReady { before with construction := reserved } frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { before with construction := reserved } carrier := by
  obtain ⟨priorReady, priorBacking⟩ := world.carriers frame member
  have transfer (carrier : Carrier) (present : carrier ∈ frame.carriers) :
      CarrierResultBacking config.layout { before with construction := reserved } carrier := by
    cases carrier with
    | register value =>
      obtain ⟨ty, integer, same⟩ := separated.1 (.register value) present
      subst value
      exact .register _ (.integer ty integer)
    | pendingNamed named => exact False.elim (separated.1 (.pendingNamed named) present)
    | completed id =>
      exact (accepted_reservation_rooted_completed_backing config initialized before reserved incoming selected token count
        receiver current ambient types live regions pending world reservation region regionMember regionDestination outside id
        (priorBacking (.completed id) present) (separated.1 (.completed id) present)).2
  refine ⟨⟨priorReady.lengths, ?_⟩, transfer⟩
  intro channel carrier pair
  have present := (List.of_mem_zip pair).2
  have prior := priorReady.pairs channel carrier pair
  cases prior with
  | register ty value => exact .register ty value
  | pendingNamed named oldIncoming oldSelected snapshot ticket =>
    exact False.elim (separated.1 (.pendingNamed named) present)
  | construct channel id ready =>
    have backing := accepted_reservation_rooted_completed_backing config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation region regionMember regionDestination outside id
      (priorBacking (.completed id) present) (separated.1 (.completed id) present)
    obtain ⟨afterReady⟩ := accepted_reservation_landing_ready config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation channel id ready backing.1
      (separated.2.1 channel id pair ready)
    exact .construct channel id afterReady
  | completion named oldIncoming oldSelected id role snapshot ticket ready =>
    have backing := accepted_reservation_rooted_completed_backing config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation region regionMember regionDestination outside id
      (priorBacking (.completed id) present) (separated.1 (.completed id) present)
    obtain ⟨afterReady⟩ := accepted_reservation_landing_ready config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation oldSelected id ready backing.1
      (separated.2.2 named id role oldIncoming oldSelected snapshot pair ticket ready)
    have tickets := accepted_fresh_reservation_frames config initialized before reserved incoming token selected
      ambient types live regions pending world reservation [] []
    have retainedTicket := (tickets.2.1 named _ ticket).2
    exact .completion named oldIncoming oldSelected id role snapshot retainedTicket afterReady

#print axioms accepted_reservation_separated_pending_frame

theorem accepted_open_reservation_world_separated_pending (config : EvalConfig) (initialized : Nat)
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
    (rootedPending : ∀ frame ∈ pending, RootedSeparatedPending before live incoming frame)
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
    exact accepted_reservation_separated_pending_frame config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation base baseMember baseDestination outside frame member (rootedPending frame member)

#print axioms accepted_open_reservation_world_separated_pending

theorem accepted_nested_byte_handler_separated_pending (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
    (rootedPending : ∀ frame ∈ pending, RootedSeparatedPending innerBound live incoming frame)
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
  have reservedWorld := accepted_open_reservation_world_separated_pending config initialized innerBound reserved incoming selected token count
    receiver receiverCurrent ambient types live regions pending exitChannels [.completed selected] world history reservation
    covered rootedPending other baseRegion baseMember baseDestination outside
  obtain ⟨final, result⟩ := Goose.Proofs.ExitExecution.accepted_nested_byte_handler fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count 0 bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live (regions.map (reserveReceivingRegion incoming selected)) pending
    outerLookup results outerChannels outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver
    receiverRole receiverAdaptation receiverPhysical receiverCurrent world.ownership.source.structural.1.1 reservation reservedWorld
    ready selectedPacked selectedRequest (by simpa using fits) selectedCurrent built
  exact ⟨after, final, built, result⟩

#print axioms accepted_nested_byte_handler_separated_pending

end Goose.Proofs.ConstructionAcceptedExecution
