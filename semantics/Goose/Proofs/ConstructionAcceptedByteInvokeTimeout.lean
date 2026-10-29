import Goose.Proofs.ConstructionAcceptedByteInvokeWorld
import Goose.Proofs.ConstructionAcceptedByteBodyTimeout

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem invokeByteReceiver_lowFuel_pending (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (contextId id scope : Nat) (bytes : List UInt8) (origin : OriginId)
    (context : Context) (helper : Impl) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (history : ReservationReferencesBounded state.construction ambient)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant state.construction.destinations id retained = false)
    (within : ∀ receiving, destinationCurrent state.construction id = .ok receiving →
      OwnershipReceivingWithinSuccessorFrames state.construction ambient receiving)
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver)
    (current : destinationCurrent state.construction id = .ok id)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let scopedState := ownershipResultScopeState activation scope pushed
    let final := { scopedState with construction := { scopedState.construction with
      exitReservations := scopedState.construction.exitReservations.push .released } }
    invokeCall 0 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 1 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 2 config environment contextId [] [.construct id] origin state = .stop .timeout pushed ∧
    invokeCall 3 config environment contextId [] [.construct id] origin state = .stop .timeout scopedState ∧
    invokeCall 4 config environment contextId [] [.construct id] origin state = .stop .timeout final ∧
    AcceptedWorld config initialized pushed (.callChannels activation [] :: ambient) types live regions pending ∧
    AcceptedWorld config initialized scopedState (.callChannels activation [] :: ambient) types live regions pending ∧
    AcceptedWorld config initialized final (.returned [] :: .callChannels activation [] :: ambient) types live regions pending := by
  let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], [.construct id]⟩
  let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let scopedState := ownershipResultScopeState activation scope pushed
  let final := { scopedState with construction := { scopedState.construction with
    exitReservations := scopedState.construction.exitReservations.push .released } }
  have pushedWorld : AcceptedWorld config initialized pushed (.callChannels activation [] :: ambient) types live regions pending :=
    acceptedWorld_pushConstructActivation_withReceiving config initialized state ambient types live regions pending activation id world rfl rfl
      (Array.getElem?_eq_some_iff.mp ready.present).1 within
  have pushedHistory : ReservationReferencesBounded pushed.construction (.callChannels activation [] :: ambient) := by
    intro frame member
    rcases List.mem_cons.mp member with same | old
    · subst frame
      simp [OwnershipAmbientFrame.tickets, activation]
    · exact history frame old
  have pushedSeparated : ∀ retained ∈ completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)),
      destinationDescendant pushed.construction.destinations id retained = false := by
    intro retained member
    apply separated retained
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using member
  let pushedReady : OpenDestinationBacking config.layout pushed id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  have low := byteBody_lowFuel_pending config initialized activation scope id bytes origin pushed ambient types live regions pending
    rfl pushedWorld pushedHistory pushedSeparated pushedReady current
  have renewal : renewReceivingDestination id state.construction = .ok id state.construction := by
    simp only [renewReceivingDestination, ConstructionM.get, bind, current, pure,
      lookupDestination_result, ready.present, ready.opened]
  have adapted := adapt_open_byte_receiver config state id ready receiver
  refine ⟨?_, ?_, ?_, ?_, ?_, pushedWorld, low.2.2.2.1, low.2.2.2.2⟩
  · simp [invokeCall, Goose.Construct.timeout, EvalM.stop]
  · simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments, renewal,
      adapted, liftConstruction, bind, pure, Goose.Construct.timeout, EvalM.stop]
  · simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments, renewal,
      adapted, liftConstruction, bind, pure, freshAct, EvalM.get, EvalM.set, enterActivation,
      Nat.not_le.mpr depth, finishActivation, execActivationBody, Goose.Construct.timeout, EvalM.stop]
  · simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments, renewal,
      adapted, liftConstruction, bind, pure, freshAct, EvalM.get, EvalM.set, enterActivation,
      Nat.not_le.mpr depth, finishActivation, body, low.2.1, activation, pushed]
  · simp [invokeCall, getImplementation, contextAt, helperAt, parameters, results, evalArguments, renewal,
      adapted, liftConstruction, bind, pure, freshAct, EvalM.get, EvalM.set, enterActivation,
      Nat.not_le.mpr depth, finishActivation, body, low.2.2.1, activation, pushed]


theorem invokeByteReceiver_lowFuel_separated (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (contextId id scope : Nat) (bytes : List UInt8) (origin : OriginId)
    (context : Context) (helper : Impl) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized state ambient types live regions [])
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (history : ReservationReferencesBounded state.construction ambient)
    (separated : ∀ retained ∈ completedCarrierIds ambient.retained,
      destinationDescendant state.construction.destinations id retained = false)
    (within : ∀ receiving, destinationCurrent state.construction id = .ok receiving →
      OwnershipReceivingWithinSuccessorFrames state.construction ambient receiving)
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver)
    (current : destinationCurrent state.construction id = .ok id)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let scopedState := ownershipResultScopeState activation scope pushed
    let final := { scopedState with construction := { scopedState.construction with
      exitReservations := scopedState.construction.exitReservations.push .released } }
    invokeCall 0 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 1 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 2 config environment contextId [] [.construct id] origin state = .stop .timeout pushed ∧
    invokeCall 3 config environment contextId [] [.construct id] origin state = .stop .timeout scopedState ∧
    invokeCall 4 config environment contextId [] [.construct id] origin state = .stop .timeout final ∧
    AcceptedWorld config initialized pushed (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized scopedState (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized final (.returned [] :: .callChannels activation [] :: ambient) types live regions [] := by
  exact invokeByteReceiver_lowFuel_pending config initialized environment contextId id scope bytes origin context helper state ambient types live regions [] world
    contextAt helperAt parameters results body history separated within ready receiver current depth

theorem invokeByteReceiver_lowFuel_within (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (contextId id scope : Nat) (bytes : List UInt8) (origin : OriginId)
    (context : Context) (helper : Impl) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized state ambient types live regions [])
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (history : ReservationReferencesBounded state.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (within : ∀ receiving, destinationCurrent state.construction id = .ok receiving →
      OwnershipReceivingWithinSuccessorFrames state.construction ambient receiving)
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver)
    (current : destinationCurrent state.construction id = .ok id)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let scopedState := ownershipResultScopeState activation scope pushed
    let final := { scopedState with construction := { scopedState.construction with
      exitReservations := scopedState.construction.exitReservations.push .released } }
    invokeCall 0 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 1 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 2 config environment contextId [] [.construct id] origin state = .stop .timeout pushed ∧
    invokeCall 3 config environment contextId [] [.construct id] origin state = .stop .timeout scopedState ∧
    invokeCall 4 config environment contextId [] [.construct id] origin state = .stop .timeout final ∧
    AcceptedWorld config initialized pushed (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized scopedState (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized final (.returned [] :: .callChannels activation [] :: ambient) types live regions [] := by
  apply invokeByteReceiver_lowFuel_separated config initialized environment contextId id scope bytes origin context helper state ambient
    types live regions world contextAt helperAt parameters results body history ?_ within ready receiver current depth
  intro retained member
  rw [noRetained] at member
  cases member

theorem invokeByteReceiver_lowFuel_world (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (contextId id scope : Nat) (bytes : List UInt8) (origin : OriginId)
    (context : Context) (helper : Impl) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized state ambient types live regions [])
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (history : ReservationReferencesBounded state.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (receiver : ready.destination.use = .receiver)
    (current : destinationCurrent state.construction id = .ok id)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], [.construct id]⟩
    let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let scopedState := ownershipResultScopeState activation scope pushed
    let final := { scopedState with construction := { scopedState.construction with
      exitReservations := scopedState.construction.exitReservations.push .released } }
    invokeCall 0 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 1 config environment contextId [] [.construct id] origin state = .stop .timeout state ∧
    invokeCall 2 config environment contextId [] [.construct id] origin state = .stop .timeout pushed ∧
    invokeCall 3 config environment contextId [] [.construct id] origin state = .stop .timeout scopedState ∧
    invokeCall 4 config environment contextId [] [.construct id] origin state = .stop .timeout final ∧
    AcceptedWorld config initialized pushed (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized scopedState (.callChannels activation [] :: ambient) types live regions [] ∧
    AcceptedWorld config initialized final (.returned [] :: .callChannels activation [] :: ambient) types live regions [] := by
  apply invokeByteReceiver_lowFuel_within config initialized environment contextId id scope bytes origin context helper state ambient
    types live regions world contextAt helperAt parameters results body history noRetained ?_ ready receiver current depth
  intro receiving resolved frame member token owned
  rw [noTickets frame member] at owned
  cases owned

#print axioms invokeByteReceiver_lowFuel_pending
#print axioms invokeByteReceiver_lowFuel_separated
#print axioms invokeByteReceiver_lowFuel_within
#print axioms invokeByteReceiver_lowFuel_world
end Goose.Proofs.ConstructionAcceptedExecution
