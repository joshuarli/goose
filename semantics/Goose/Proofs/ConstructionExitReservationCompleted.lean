import Goose.Proofs.ConstructionExitReservationWriteLoop

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem accepted_reservation_rooted_receiver_carrier (config : EvalConfig) (initialized : Nat)
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
    (receiverUse : ∀ row, before.construction.destinations[id]? = some row → row.use = .receiver)
    (rooted : ∀ stored, storedDestination id before = .ok stored before →
      ∃ root, live root ∧ before.objects.lookup root = some (.stored stored)) :
    CarrierResultBacking config.layout { before with construction := reserved } (.completed id) ∧
      CarrierLandingReady { before with construction := reserved } (.construct id) (.completed id) := by
  have rootBacking := (accepted_open_reservation_rooted_backing config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation region member regionDestination outside).1
  have source := accepted_open_reservation_source config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation
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
    have terminal := destinationSuccessorKeysInactive_built_terminal reserved source.inactiveKeys id row foundAfter n built
    have inside := (Array.getElem?_eq_some_iff.mp foundAfter).1
    have resolved : destinationCurrent reserved id = .ok id := by
      simp only [destinationCurrent_result, destinationCurrentSteps_succ, inside, ↓reduceIte, terminal]
    have ready : ReceivingCarrierLandingReady { before with construction := reserved } id id :=
      ⟨id, row, row, resolved, foundAfter, foundAfter, .refl _, .receiver (receiverUse row found), Nat.le_refl _⟩
    exact ⟨.completed id n row stored foundAfter built sampledAfter afterBacking, .construct id id ready⟩

#print axioms accepted_reservation_rooted_receiver_carrier

def RootedReceiverPending (state : ExecutionState) (live : RootInst → Prop) (frame : PendingCarrierFrame) : Prop :=
  (∀ carrier ∈ frame.carriers, match carrier with
    | .register value => ∃ ty integer, value = .int ty integer
    | .completed id =>
      (∀ row, state.construction.destinations[id]? = some row → row.use = .receiver) ∧
      (∀ stored, storedDestination id state = .ok stored state →
        ∃ root, live root ∧ state.objects.lookup root = some (.stored stored))
    | .pendingNamed _ => False) ∧
  (∀ channel carrier, (channel, carrier) ∈ frame.channels.zip frame.carriers → ∀ id,
    carrier = .completed id → channel = .construct id)

theorem accepted_reservation_rooted_pending_frame (config : EvalConfig) (initialized : Nat)
    (before : ExecutionState) (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking config.layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (region : ReceivingRegion) (regionMember : region ∈ regions) (regionDestination : region.destination = incoming)
    (outside : ∀ root, live root → ¬ region.mutableRoots root)
    (frame : PendingCarrierFrame) (member : frame ∈ pending) (rooted : RootedReceiverPending before live frame) :
    CarriersLandingReady { before with construction := reserved } frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking config.layout { before with construction := reserved } carrier := by
  obtain ⟨priorReady, priorBacking⟩ := world.carriers frame member
  have transfer (carrier : Carrier) (present : carrier ∈ frame.carriers) :
      CarrierResultBacking config.layout { before with construction := reserved } carrier := by
    cases carrier with
    | register value =>
      obtain ⟨ty, integer, same⟩ := rooted.1 (.register value) present
      subst value
      exact .register _ (.integer ty integer)
    | pendingNamed token => exact False.elim (rooted.1 (.pendingNamed token) present)
    | completed id =>
      obtain ⟨receiverUse, rootFound⟩ := rooted.1 (.completed id) present
      exact (accepted_reservation_rooted_receiver_carrier config initialized before reserved incoming selected token count
        receiver current ambient types live regions pending world reservation region regionMember regionDestination outside id
        (priorBacking (.completed id) present) receiverUse rootFound).1
  refine ⟨⟨priorReady.lengths, ?_⟩, transfer⟩
  intro channel carrier pair
  have present := (List.of_mem_zip pair).2
  cases carrier with
  | register value =>
    have prior := priorReady.pairs channel (.register value) pair
    cases prior with
    | register ty value => exact .register ty value
  | pendingNamed token => exact False.elim (rooted.1 (.pendingNamed token) present)
  | completed id =>
    have same := rooted.2 channel (.completed id) pair id rfl
    subst channel
    obtain ⟨receiverUse, rootFound⟩ := rooted.1 (.completed id) present
    exact (accepted_reservation_rooted_receiver_carrier config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation region regionMember regionDestination outside id
      (priorBacking (.completed id) present) receiverUse rootFound).2

#print axioms accepted_reservation_rooted_pending_frame

theorem accepted_open_reservation_world_rooted_pending (config : EvalConfig) (initialized : Nat)
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
    (rootedPending : ∀ frame ∈ pending, RootedReceiverPending before live frame)
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
    exact accepted_reservation_rooted_pending_frame config initialized before reserved incoming selected token count
      receiver current ambient types live regions pending world reservation base baseMember baseDestination outside frame member (rootedPending frame member)

#print axioms accepted_open_reservation_world_rooted_pending

theorem accepted_nested_byte_handler_rooted_pending (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
    (rootedPending : ∀ frame ∈ pending, RootedReceiverPending innerBound live frame)
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
  have reservedWorld := accepted_open_reservation_world_rooted_pending config initialized innerBound reserved incoming selected token count
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

#print axioms accepted_nested_byte_handler_rooted_pending

end Goose.Proofs.ConstructionAcceptedExecution
