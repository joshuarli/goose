import Goose.Proofs.ConstructionAcceptedByteInvokeEquation
import Goose.Proofs.ConstructionAcceptedByteBodyFinish
import Goose.Proofs.ConstructionAcceptedConstructActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (OriginId RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ExitExecution

theorem invokeByteReceiver_success_observed (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (contextId id scope : Nat) (bytes : List UInt8) (origin : OriginId)
    (context : Context) (helper : Impl) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized state ambient types live regions [])
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (history : ReservationReferencesBounded state.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent state.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    ∃ after, invokeCall (fuel + 5) config environment contextId [] [.construct id] origin state = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] ∧
      after.objects = state.objects ∧ after.objectOrdinals = state.objectOrdinals ∧
      after.nextAct = state.nextAct + 1 ∧ after.nextScope = state.nextScope + 1 := by
  let activation : RuntimeActivation := ⟨context.impl, state.nextAct, helper.vars, [], [.construct id]⟩
  let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  have pushedWorld : AcceptedWorld config initialized pushed (.callChannels activation [] :: ambient) types live regions [] :=
    acceptedWorld_pushConstructActivation config initialized state ambient types live regions [] activation id world rfl rfl
      (Array.getElem?_eq_some_iff.mp ready.present).1 noTickets
  have pushedHistory : ReservationReferencesBounded pushed.construction (.callChannels activation [] :: ambient) := by
    intro frame member
    rcases List.mem_cons.mp member with same | old
    · subst frame
      simp [OwnershipAmbientFrame.tickets, activation]
    · exact history frame old
  have pushedRetained : completedCarrierIds (OwnershipAmbient.retained (.callChannels activation [] :: ambient)) = [] := by
    simpa [OwnershipAmbient.retained, OwnershipAmbientFrame.carriers] using noRetained
  let pushedReady : OpenDestinationBacking config.layout pushed id (.varr (.int .u8)) 0 :=
    { ready with present := ready.present, bytes := ready.bytes }
  obtain ⟨after, done, finalWorld, objects, ordinals, acts, scopes⟩ := byteBody_finish_from_activation_observed fuel (fuel + 4) config initialized activation scope id bytes origin
    pushed ambient types live regions rfl absent pushedWorld pushedHistory pushedRetained pushedReady packed adaptation receiver request
    physical current fits mutable cutoff covered
  have invoked := invokeByteReceiver_body fuel config environment contextId id origin context helper state
    contextAt helperAt parameters results ready receiver current depth
  refine ⟨after, ?_, finalWorld, objects, ordinals, acts, scopes⟩
  rw [body] at invoked
  exact invoked.trans done

theorem invokeByteReceiver_success_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (contextId id scope : Nat) (bytes : List UInt8) (origin : OriginId)
    (context : Context) (helper : Impl) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : RootInst → Prop) (regions : List ReceivingRegion)
    (world : AcceptedWorld config initialized state ambient types live regions [])
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨scope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ descriptor ∈ helper.vars.toList, descriptor.scope ≠ scope)
    (history : ReservationReferencesBounded state.construction ambient)
    (noRetained : completedCarrierIds ambient.retained = [])
    (noTickets : ∀ frame ∈ ambient, frame.tickets = [])
    (ready : OpenDestinationBacking config.layout state id (.varr (.int .u8)) 0)
    (packed : ready.destination.layout = .packed) (adaptation : ready.destination.adaptation = none)
    (receiver : ready.destination.use = .receiver) (request : ready.destination.capability.request = .value)
    (physical : ready.destination.capability.layout = .varr (.int .u8))
    (current : destinationCurrent state.construction id = .ok id) (fits : bytes.length < 2 ^ 32)
    (mutable : ∀ region ∈ regions, id ∈ region.mutableDestinations)
    (cutoff : ∀ region ∈ regions, region.limit ready.destination.storage ≤ ready.destination.capability.start)
    (covered : ∀ root, live root → ∃ region ∈ regions, ¬ region.mutableRoots root)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    ∃ after, invokeCall (fuel + 5) config environment contextId [] [.construct id] origin state = .ok [.completed id] after ∧
      AcceptedWorld config initialized after (.returned [.completed id] :: ambient) types live regions
        [⟨[.construct id], [.completed id]⟩] := by
  obtain ⟨after, executed, finalWorld, objects, ordinals, acts, scopes⟩ := invokeByteReceiver_success_observed fuel config initialized
    environment contextId id scope bytes origin context helper state ambient types live regions world contextAt helperAt parameters results body
    absent history noRetained noTickets ready packed adaptation receiver request physical current fits mutable cutoff covered depth
  exact ⟨after, executed, finalWorld⟩

#print axioms invokeByteReceiver_success_observed
#print axioms invokeByteReceiver_success_world
end Goose.Proofs.ConstructionAcceptedExecution
