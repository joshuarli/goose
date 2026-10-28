import Goose.Proofs.ConstructionExitReservationPending

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

def reserveReceivingRegion (incoming selected : Nat) (region : ReceivingRegion) : ReceivingRegion :=
  if region.destination = incoming then { region with mutableDestinations := selected :: region.mutableDestinations } else region

theorem reserve_open_other_region_protection (layout : LayoutEnv) (before : ExecutionState)
    (reserved : ConstructionState) (incoming selected token count : Nat)
    (receiver : OpenDestinationBacking layout before incoming (.varr (.int .u8)) (count + 1))
    (current : destinationCurrent before.construction incoming = .ok incoming)
    (reservation : reserveExitDestination incoming .newValue before.construction = .ok (token, selected) reserved)
    (live : RootInst → Prop) (region : ReceivingRegion)
    (different : region.destination ≠ incoming) (authority : incoming ∈ region.mutableDestinations)
    (cutoff : region.limit receiver.destination.storage ≤ receiver.storage.bytes.size)
    (protection : ReceivingProtection layout before live region) :
    ReceivingProtection layout { before with construction := reserved } live region := by
  let after : ExecutionState := { before with construction := reserved }
  have frame := reserve_open_other_rows before.construction reserved incoming selected token count
    receiver.destination receiver.storage receiver.present receiver.opened receiver.bytes current reservation
  have prefixes := reserve_open_storage_prefix before.construction reserved incoming selected token count
    receiver.destination receiver.storage region.limit receiver.present receiver.opened receiver.bytes cutoff current reservation
  have rows : ∀ root, live root → ¬ region.mutableRoots root → ∀ value, before.objects.lookup root = some value →
      ∀ stored, StoredOccurrence value stored → ∀ id, stored.destination = some id →
      reserved.destinations[id]? = before.construction.destinations[id]? := by
    intro root active immutable value found stored occurrence id named
    have excluded := protection.names root active immutable value found stored occurrence id named
    have distinct : id ≠ incoming := by
      intro same
      subst id
      exact excluded authority
    have backing := (protection.observations.backing.values root ⟨active, immutable⟩ value found).occurrence_backing
      layout before value stored occurrence
    cases backing with
    | detached storage element present detached ty interval => rw [detached] at named; cases named
    | named old storage row n present name binding rest =>
      have same := Option.some.inj (name.symm.trans named)
      subst old
      exact frame.2 id distinct (Array.getElem?_eq_some_iff.mp binding).1
  obtain ⟨own, ownPresent⟩ := protection.present
  have ownBound := (Array.getElem?_eq_some_iff.mp ownPresent).1
  have ownFrame := frame.2 region.destination different ownBound
  have observations := rootedBackingObservations_storagePrefixes layout before after _ region.limit protection.observations prefixes rfl rfl
    (by intro root kept value found stored occurrence id named; exact rows root kept.1 kept.2 value found stored occurrence id named)
  refine ⟨⟨own, by simpa only [after, ownFrame] using ownPresent⟩, observations, ?_, ?_, protection.authority, ?_, ?_⟩
  · intro row found
    apply protection.cutoff row
    simpa only [after, ownFrame] using found
  · intro row found
    apply protection.landing row
    simpa only [after, ownFrame] using found
  · intro id member
    rw [frame.1]
    exact Nat.lt_trans (protection.authorityBound id member) (Nat.lt_succ_self _)
  · exact protection.names

#print axioms reserve_open_other_region_protection

theorem accepted_open_reservation_world_regions (config : EvalConfig) (initialized : Nat)
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
    (integers : ∀ frame ∈ pending, IntegerRegisterCarriers frame.carriers)
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
    exact integer_register_pending_frame config.layout before { before with construction := reserved } frame
      (world.carriers frame member).1 (integers frame member)

#print axioms accepted_open_reservation_world_regions

theorem accepted_nested_byte_handler_regions (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId incoming selected token count writeCount : Nat)
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
    (ready : OpenDestinationBacking config.layout { innerBound with construction := reserved } selected (.varr (.int .u8)) writeCount)
    (packed : ready.destination.layout = .packed) (request : ready.destination.capability.request = .value)
    (fits : writeCount + bytes.length < 2 ^ 32) (current : destinationCurrent reserved selected = .ok selected)
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
  have reservedWorld := accepted_open_reservation_world_regions config initialized innerBound reserved incoming selected token count
    receiver receiverCurrent ambient types live regions pending exitChannels [.completed selected] world history reservation covered integers other baseRegion baseMember baseDestination outside
  exact Goose.Proofs.ExitExecution.accepted_nested_byte_handler fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count writeCount bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live
    (regions.map (reserveReceivingRegion incoming selected)) pending outerLookup results outerChannels
    outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver receiverRole receiverAdaptation
    receiverPhysical receiverCurrent world.ownership.source.structural.1.1 reservation reservedWorld ready packed request fits current built

#print axioms accepted_nested_byte_handler_regions

end Goose.Proofs.ConstructionAcceptedExecution
