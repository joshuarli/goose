import Goose.Proofs.ConstructionAcceptedByteBodyFinish
import Goose.Proofs.ConstructionAcceptedByteReturnTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem byteBody_lowFuel_pending (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : activation.channels = [.construct id])
    (world : AcceptedWorld config initialized before (.callChannels activation [] :: ambient) types live regions pending)
    (history : ReservationReferencesBounded before.construction (.callChannels activation [] :: ambient))
    (separated : ∀ retained ∈ completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)),
      destinationDescendant before.construction.destinations id retained = false)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (current : destinationCurrent before.construction id = .ok id) :
    let scopedState := ownershipResultScopeState activation scope before
    let final := { scopedState with construction := { scopedState.construction with
      exitReservations := scopedState.construction.exitReservations.push .released } }
    execActivationBody 0 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout before ∧
    execActivationBody 1 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout scopedState ∧
    execActivationBody 2 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout final ∧
    AcceptedWorld config initialized scopedState (.callChannels activation [] :: ambient) types live regions pending ∧
    AcceptedWorld config initialized final (.returned [] :: .callChannels activation [] :: ambient) types live regions pending := by
  let scopedState := ownershipResultScopeState activation scope before
  let final := { scopedState with construction := { scopedState.construction with
    exitReservations := scopedState.construction.exitReservations.push .released } }
  have scopedWorld := acceptedWorld_resultScope config initialized before (.callChannels activation [] :: ambient)
    types live regions pending activation scope world
  let scopedReady : OpenDestinationBacking config.layout scopedState id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  have timed := withCompletion_byteReceiver_pending_timeouts config initialized
    { activation with scopes := (scope, before.nextScope) :: activation.scopes } id bytes origin scopedState
    (.callChannels activation [] :: ambient) types live regions pending scopedWorld history separated scopedReady current
  have bound : bindAll activation.act before.nextScope [] scopedState = .ok () scopedState := by simp [bindAll, bind, pure]
  have normal : execStmts 1 config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
    [] scopedState = .ok (.normal .unit) scopedState := by simp [execStmts, pure]
  have body := execActivationBody_bound_channelTail 1 config activation [] scope []
    (.bytes (.varr (.int .u8)) bytes origin) before scopedState scopedState bound normal
  simp only [channels, expressionOrigin] at body
  simp only [channels] at timed
  rw [timed.2.1] at body
  refine ⟨?_, ?_, ?_, scopedWorld, timed.2.2⟩
  · simp [execActivationBody, Goose.Construct.timeout, EvalM.stop]
  · simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bindAll,
      withScope, execStmts, Goose.Construct.timeout, EvalM.stop, bind, pure,
      ownershipResultScopeState]
  · simpa [final] using body


theorem byteBody_lowFuel_separated (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (world : AcceptedWorld config initialized before (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded before.construction (.callChannels activation [] :: ambient))
    (separated : ∀ retained ∈ completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)),
      destinationDescendant before.construction.destinations id retained = false)
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (current : destinationCurrent before.construction id = .ok id) :
    let scopedState := ownershipResultScopeState activation scope before
    let final := { scopedState with construction := { scopedState.construction with
      exitReservations := scopedState.construction.exitReservations.push .released } }
    execActivationBody 0 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout before ∧
    execActivationBody 1 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout scopedState ∧
    execActivationBody 2 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout final ∧
    AcceptedWorld config initialized scopedState (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized final (.returned [] :: .callChannels activation [] :: ambient) types live regions [] := by
  exact byteBody_lowFuel_pending config initialized activation scope id bytes origin before ambient types live regions [] channels world history separated ready current

theorem byteBody_lowFuel_world (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope id : Nat) (bytes : List UInt8) (origin : OriginId)
    (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : RootInst → Prop) (regions : List ReceivingRegion)
    (channels : activation.channels = [.construct id])
    (world : AcceptedWorld config initialized before (.callChannels activation [] :: ambient) types live regions [])
    (history : ReservationReferencesBounded before.construction (.callChannels activation [] :: ambient))
    (noRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [])
    (ready : OpenDestinationBacking config.layout before id (.varr (.int .u8)) 0)
    (current : destinationCurrent before.construction id = .ok id) :
    let scopedState := ownershipResultScopeState activation scope before
    let final := { scopedState with construction := { scopedState.construction with
      exitReservations := scopedState.construction.exitReservations.push .released } }
    execActivationBody 0 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout before ∧
    execActivationBody 1 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout scopedState ∧
    execActivationBody 2 config activation [] ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩ before = .stop .timeout final ∧
    AcceptedWorld config initialized scopedState (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized final (.returned [] :: .callChannels activation [] :: ambient) types live regions [] := by
  apply byteBody_lowFuel_separated config initialized activation scope id bytes origin before ambient types live regions
    channels world history ?_ ready current
  intro retained member
  rw [noRetained] at member
  cases member

#print axioms byteBody_lowFuel_pending
#print axioms byteBody_lowFuel_separated
#print axioms byteBody_lowFuel_world
end Goose.Proofs.ConstructionAcceptedExecution
