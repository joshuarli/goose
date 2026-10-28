import Goose.Proofs.ConstructionAcceptedNestedActivation

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem emptyHelper_call_world (fuel : Nat) (config : EvalConfig) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (environment : RuntimeActivation) (contextId origin : Nat) (context : Context) (helper : Impl)
    (world : AcceptedWorld config initialized state ambient types live regions pending)
    (contextAt : config.module.contexts[contextId]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[]) (results : helper.results = #[]) (variables : helper.vars = #[])
    (body : helper.body = ⟨0, [], none⟩) (depth : state.activations.length < Goose.Core.maxCallDepth)
    (outer : OwnershipAmbient.withoutActivation state.nextAct ambient = ambient) :
    match invokeCall fuel config environment contextId [] [] origin state with
    | .stop _ after => ∃ nextAmbient, AcceptedWorld config initialized after nextAmbient types live regions pending
    | .ok carriers after => carriers = [] ∧ AcceptedWorld config initialized after ambient types live regions pending
    | _ => False := by
  let activation : RuntimeActivation := ⟨context.impl, state.nextAct, #[], [], []⟩
  let pushed := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let scopeState := ownershipResultScopeState activation 0 pushed
  let released := releaseScopeState activation 0 pushed.nextScope scopeState
  let finished := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
  have pushedWorld : AcceptedWorld config initialized pushed (.callChannels activation [] :: ambient) types live regions pending :=
    acceptedWorld_pushEmptyActivation config initialized state ambient types live regions pending activation world rfl rfl
  have scopeWorld : AcceptedWorld config initialized scopeState (.callChannels activation [] :: ambient) types live regions pending :=
    acceptedWorld_resultScope config initialized pushed (.callChannels activation [] :: ambient) types live regions pending activation 0 pushedWorld
  have releasedWorld : AcceptedWorld config initialized released (.callChannels activation [] :: ambient) types live regions pending := by
    have result := scopeWorld.releaseScope config initialized scopeState (.callChannels activation [] :: ambient) types live regions pending
      activation 0 pushed.nextScope
    simpa [activation, Goose.Proofs.Exit.runtimeScopeRoots] using result
  have finishedWorld : AcceptedWorld config initialized finished ambient types live regions pending :=
    releasedWorld.finishEmptyCall config initialized released activation ambient types live regions pending outer
  cases fuel with
  | zero =>
    simp only [invokeCall, timeout, EvalM.stop]
    exact ⟨ambient, world⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, evalArguments,
        timeout, EvalM.stop, bind, pure]
      exact ⟨ambient, world⟩
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, variables, body,
          evalArguments, enterActivation, execActivationBody, finishActivation, freshAct, EvalM.get, EvalM.set, timeout, EvalM.stop,
          bind, pure, Nat.not_le.mpr depth, activation, pushed]
        exact ⟨.callChannels activation [] :: ambient, pushedWorld⟩
      | succ fuel =>
        cases fuel with
        | zero =>
          simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, variables, body,
            evalArguments, enterActivation, execActivationBody, execResultScope, finishActivation, freshAct, freshScope, EvalM.get, EvalM.set,
            withScope, bindAll, execStmts, timeout, EvalM.stop, bind, pure, Nat.not_le.mpr depth,
            activation, pushed, ownershipResultScopeState, scopeState]
          refine ⟨.callChannels activation [] :: ambient, ?_⟩
          simpa [scopeState, ownershipResultScopeState, pushed, activation] using scopeWorld
        | succ fuel =>
          simp [invokeCall, getImplementation, contextAt, implementationAt, parameters, results, variables, body,
            evalArguments, enterActivation, execActivationBody, execResultScope, freshAct, freshScope, EvalM.get, EvalM.set,
            withScope, bindAll, execStmts, releaseScope, finishActivation, finishChannels, landCarriersInto, deliverCarriers,
            bind, pure, Nat.not_le.mpr depth, activation, pushed, ownershipResultScopeState, scopeState, released, finished]
          simpa [activation, pushed, scopeState, released, finished, ownershipResultScopeState, releaseScopeState] using finishedWorld

#print axioms emptyHelper_call_world
end Goose.Proofs.ConstructionAcceptedExecution
