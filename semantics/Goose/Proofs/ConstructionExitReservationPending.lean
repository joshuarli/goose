import Goose.Proofs.ConstructionExitReservationWorld

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst IntTy OriginId ContextId ImplId)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

def IntegerRegisterCarriers (carriers : List Goose.Construct.Carrier) : Prop :=
  ∀ carrier ∈ carriers, ∃ ty value, carrier = .register (.int ty value)

theorem integer_register_pending_frame (layout : LayoutEnv) (before after : ExecutionState)
    (frame : PendingCarrierFrame) (ready : CarriersLandingReady before frame.channels frame.carriers)
    (integers : IntegerRegisterCarriers frame.carriers) :
    CarriersLandingReady after frame.channels frame.carriers ∧
      ∀ carrier ∈ frame.carriers, CarrierResultBacking layout after carrier := by
  refine ⟨⟨ready.lengths, ?_⟩, ?_⟩
  · intro channel carrier member
    have carrierMember := (List.of_mem_zip member).2
    obtain ⟨ty, value, equal⟩ := integers carrier carrierMember
    subst carrier
    have prior := ready.pairs channel (.register (.int ty value)) member
    cases prior with
    | register channelTy value => exact .register channelTy (.int ty value)
  · intro carrier member
    obtain ⟨ty, value, equal⟩ := integers carrier member
    subst carrier
    exact .register _ (.integer ty value)

theorem accepted_open_reservation_world_registers (config : EvalConfig) (initialized : Nat)
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
    (destinations : ∀ region ∈ regions, region.destination = incoming)
    (baseRegion : ReceivingRegion) (baseMember : baseRegion ∈ regions)
    (outside : ∀ root, live root → ¬ baseRegion.mutableRoots root) :
    AcceptedWorld config initialized { before with construction := reserved }
      (.exitChannels [token] channels carriers :: ambient) types live
      (regions.map fun region => { region with mutableDestinations := selected :: region.mutableDestinations }) pending := by
  have context := accepted_open_reservation_execution_context config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending channels carriers world history reservation covered
  have backing := accepted_open_reservation_rooted_backing config initialized before reserved incoming selected token count
    receiver current ambient types live regions pending world reservation baseRegion baseMember (destinations baseRegion baseMember) outside
  refine ⟨⟨context, world.globals, world.globalTypes, world.layouts, world.typeFrontier, world.syntheticFrontier,
    world.heap, world.objectsRegistered, world.ordinalsRegistered, backing.1, ?_, ?_⟩, world.globalLive⟩
  · intro target member
    obtain ⟨region, original, equal⟩ := List.mem_map.mp member
    subst target
    exact reserve_open_extended_protection config.layout before reserved incoming selected token count receiver current reservation
      live region (destinations region original) (world.protections region original)
  · intro frame member
    exact integer_register_pending_frame config.layout before { before with construction := reserved } frame
      (world.carriers frame member).1 (integers frame member)

#print axioms integer_register_pending_frame
#print axioms accepted_open_reservation_world_registers

theorem accepted_nested_byte_handler_register_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
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
    (destinations : ∀ region ∈ regions, region.destination = incoming)
    (baseMember : baseRegion ∈ regions)
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
  have reservedWorld := accepted_open_reservation_world_registers config initialized innerBound reserved incoming selected token count
    receiver receiverCurrent ambient types live regions pending exitChannels [.completed selected] world history reservation covered integers destinations baseRegion baseMember outside
  exact Goose.Proofs.ExitExecution.accepted_nested_byte_handler fuel config initialized outer inner outerPre innerPre
    outerScope innerScope targetId incoming selected token count writeCount bytes origin outerRest innerRest outerTail innerTail
    contextId arguments callChannels exitChannels outerInitial outerBound callPrepared innerEntered innerBound after
    outerImpl innerImpl calledImpl calledId reserved ambient types live
    (regions.map fun region => { region with mutableDestinations := selected :: region.mutableDestinations }) pending outerLookup results outerChannels
    outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver receiverRole receiverAdaptation
    receiverPhysical receiverCurrent world.ownership.source.structural.1.1 reservation reservedWorld ready packed request fits current built

#print axioms accepted_nested_byte_handler_register_world

end Goose.Proofs.ConstructionAcceptedExecution
