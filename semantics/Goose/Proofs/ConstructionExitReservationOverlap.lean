import Goose.Proofs.ConstructionExitReservationCarrierBacking

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem open_anchor_supported_replacement_path (state : ConstructionState) (ancestor source count : Nat)
    (anchor : PendingDestination) (present : state.destinations[ancestor]? = some anchor)
    (opened : anchor.progress = .open count) (authority : SupportedReplacementAuthority state)
    (path : OwnershipReplacementPath state.destinations ancestor source)
    (supported : ReplacementSupported state source) : source = ancestor := by
  induction path with
  | refl => rfl
  | step id parent ancestor row found use path ih =>
    have parentSupported := ReplacementSupported.parent id parent row found use supported
    have equal := ih present parentSupported
    subst parent
    obtain ⟨owner, ownerFound, backing, phase⟩ := authority id ancestor row found use supported
    have same := Option.some.inj (ownerFound.symm.trans present)
    subst owner
    rcases phase with ⟨n, exiting⟩ | abandoned | cancelled <;> rw [opened] at * <;> contradiction

theorem accepted_completed_landing_separate (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (incoming count : Nat)
    (receiver : OpenDestinationBacking config.layout state incoming (.varr (.int .u8)) count)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (channel source : Nat) (ready : ReceivingCarrierLandingReady state channel source)
    (backed : CarrierResultBacking config.layout state (.completed source)) : ready.receiving ≠ incoming := by
  intro overlap
  have authority := world.ownership.source.structural.1.2.2.1
  cases backed with
  | completed source n row stored found built sampled valid =>
    have support : ReplacementSupported state.construction source := .active source row found (by simp [activeProgress, built])
    have path : OwnershipReplacementPath state.construction.destinations incoming source := by simpa only [overlap] using ready.path
    have equal := open_anchor_supported_replacement_path state.construction incoming source count receiver.destination
      receiver.present receiver.opened authority path support
    subst source
    have same := Option.some.inj (found.symm.trans receiver.present)
    subst row
    rw [receiver.opened] at built
    cases built

#print axioms open_anchor_supported_replacement_path
#print axioms accepted_completed_landing_separate

theorem accepted_pending_separated (config : EvalConfig) (initialized : Nat)
    (state : ExecutionState) (incoming count : Nat)
    (receiver : OpenDestinationBacking config.layout state incoming (.varr (.int .u8)) count)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (frame : PendingCarrierFrame) (member : frame ∈ pending)
    (registerSeparate : ∀ value, .register value ∈ frame.carriers → ∀ stored,
      StoredOccurrence value stored → stored.destination ≠ some incoming) :
    SeparatedPending state incoming frame := by
  refine ⟨registerSeparate, ?_, ?_⟩
  · intro channel id pair ready
    have member := (List.of_mem_zip pair).2
    exact accepted_completed_landing_separate config initialized state incoming count receiver ambient types live regions pending
      world channel id ready ((world.carriers frame ‹frame ∈ pending›).2 (.completed id) member)
  · intro named id role oldIncoming selected snapshot pair ticket ready
    have carrierMember := (List.of_mem_zip pair).2
    exact accepted_completed_landing_separate config initialized state incoming count receiver ambient types live regions pending
      world selected id ready ((world.carriers frame member).2 (.completed id) carrierMember)

#print axioms accepted_pending_separated

theorem accepted_open_reservation_world_no_overlap (config : EvalConfig) (initialized : Nat)
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
    (registerSeparate : ∀ frame ∈ pending, ∀ value, .register value ∈ frame.carriers → ∀ stored,
      StoredOccurrence value stored → stored.destination ≠ some incoming)
    (other : ∀ region ∈ regions, region.destination ≠ incoming →
      incoming ∈ region.mutableDestinations ∧ region.limit receiver.destination.storage ≤ receiver.storage.bytes.size)
    (base : ReceivingRegion) (baseMember : base ∈ regions) (baseDestination : base.destination = incoming)
    (outside : ∀ root, live root → ¬ base.mutableRoots root) :
    AcceptedWorld config initialized { before with construction := reserved }
      (.exitChannels [token] channels carriers :: ambient) types live
      (regions.map (reserveReceivingRegion incoming selected)) pending := by
  have separated : ∀ frame ∈ pending, SeparatedPending before incoming frame := by
    intro frame member
    exact accepted_pending_separated config initialized before incoming (count + 1) receiver ambient types live regions pending
      world frame member (registerSeparate frame member)
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

#print axioms accepted_open_reservation_world_no_overlap

theorem accepted_nested_byte_handler_no_overlap (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
    (registerSeparate : ∀ frame ∈ pending, ∀ value, .register value ∈ frame.carriers → ∀ stored,
      StoredOccurrence value stored → stored.destination ≠ some incoming)
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
  have reservedWorld := accepted_open_reservation_world_no_overlap config initialized innerBound reserved incoming selected token count
    receiver receiverCurrent ambient types live regions pending exitChannels [.completed selected] world history reservation
    covered registerSeparate other baseRegion baseMember baseDestination outside
  obtain ⟨final, result⟩ := Goose.Proofs.ExitExecution.accepted_nested_byte_handler fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count 0 bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live (regions.map (reserveReceivingRegion incoming selected)) pending
    outerLookup results outerChannels outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver
    receiverRole receiverAdaptation receiverPhysical receiverCurrent world.ownership.source.structural.1.1 reservation reservedWorld
    ready selectedPacked selectedRequest (by simpa using fits) selectedCurrent built
  exact ⟨after, final, built, result⟩

#print axioms accepted_nested_byte_handler_no_overlap

end Goose.Proofs.ConstructionAcceptedExecution
