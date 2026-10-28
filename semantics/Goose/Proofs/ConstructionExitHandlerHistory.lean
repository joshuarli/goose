import Goose.Proofs.ConstructionExitDirectHandler
import Goose.Proofs.ConstructionExitEvaluationHistoryOutcome

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId ContextId ImplId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem direct_nested_byte_handler_history (fuel : Nat) (config : EvalConfig)
    (outer inner : RuntimeActivation) (outerPre innerPre : List (Goose.Core.VarId × Value))
    (outerScope innerScope targetId id : Nat) (bytes : List UInt8) (origin : OriginId)
    (outerRest innerRest : List Stmt) (outerTail innerTail : Option Expr)
    (contextId : ContextId) (arguments : List Arg) (callChannels : List Channel)
    (outerInitial outerBound callPrepared innerEntered innerBound : ExecutionState)
    (outerImpl innerImpl calledImpl : Impl) (calledId : ImplId)
    (outerLookup : config.module.impls[outer.implementation]? = some outerImpl)
    (results : outerImpl.results.toList.map (·.ty) = [.varr (.int .u8)])
    (outerChannels : outer.channels = [.construct id])
    (outerBinding : bindAll outer.act outerInitial.nextScope outerPre { outerInitial with
      nextScope := outerInitial.nextScope + 1
      activations := outerInitial.activations.map (fun current => if current.act == outer.act then
        { current with scopes := (outerScope, outerInitial.nextScope) :: outer.scopes } else current) } = .ok () outerBound)
    (called : getImplementation config contextId outerBound = .ok (calledId, calledImpl) outerBound)
    (callSetup : channelsFor config.layout outer.act calledImpl.results.toList origin outerBound = .ok callChannels callPrepared)
    (callPrefix : CallActivationPrefix (fuel + 7) config
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
    (receiver : OpenDestinationBacking config.layout innerBound id (.varr (.int .u8)) 0)
    (innerInitialized : Nat) (innerAmbient : OwnershipAmbient) (innerTypes : RootTypes)
    (innerLive : RootInst → Prop) (innerRegions : List ReceivingRegion) (innerPending : List PendingCarrierFrame)
    (innerWorld : AcceptedWorld config innerInitialized innerBound innerAmbient innerTypes innerLive innerRegions innerPending)
    (receiverUse : receiver.destination.use = .receiver)
    (packed : receiver.destination.layout = .packed)
    (adaptation : receiver.destination.adaptation = none)
    (physical : receiver.destination.capability.layout = .varr (.int .u8))
    (request : receiver.destination.capability.request = .value)
    (current : destinationCurrent innerBound.construction id = .ok id)
    (fits : bytes.length < 2 ^ 32)
    (outerInitialized : Nat) (outerAmbient : OwnershipAmbient) (outerTypes : RootTypes)
    (outerLive : RootInst → Prop) (outerRegions : List ReceivingRegion) (outerPending : List PendingCarrierFrame)
    (outerWorld : AcceptedWorld config outerInitialized outerInitial outerAmbient outerTypes outerLive outerRegions outerPending)
    (outerHistory : EvaluationHistoryCoverage outerInitial outerAmbient outerPending) :
    ∃ after final : ExecutionState,
      enterActivation (fuel + 13) config outer outerPre
        (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin outerInitial =
        .ok [.completed id] final ∧
      final.construction.stdout = after.construction.stdout ∧
      EvaluationHistoryLifecycle final (.returned [.completed id] :: outerAmbient)
        (⟨outer.channels, [.completed id]⟩ :: outerPending) := by
  obtain ⟨after, final, executed, output, _⟩ := direct_nested_byte_handler fuel config outer inner outerPre innerPre
    outerScope innerScope targetId id bytes origin outerRest innerRest outerTail innerTail contextId arguments callChannels
    outerInitial outerBound callPrepared innerEntered innerBound outerImpl innerImpl calledImpl calledId outerLookup results
    outerChannels outerBinding called callSetup callPrefix innerLookup innerBinding selection distinct receiver
    innerWorld.ownership.source receiverUse packed adaptation physical request current fits
  have tracked := evaluator_history_outcome (fuel + 13) config .carriers _
    (.activation outer outerPre (.mk outerScope (.expr (.call contextId arguments origin) origin :: outerRest) outerTail) origin)
    outerInitial outerAmbient outerPending outer.channels ⟨outerWorld.ownership.source.structural.1.1, outerHistory⟩
  refine ⟨after, final, executed, output, ?_⟩
  simpa only [executed, EvaluationHistoryLifecycleOutcome, OwnershipResultShape.retainedCarriers] using tracked

#print axioms direct_nested_byte_handler_history

end Goose.Proofs.ConstructionAcceptedExecution
