import Goose.Proofs.ConstructionAcceptedEntryCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem entryCallStep (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (state : ExecutionState)
    (context : Context) (implementation : Impl) (originalAt : config.module.contexts[config.module.entry]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    let activation : RuntimeActivation := ⟨context.impl, state.nextAct, implementation.vars, [], []⟩
    let after := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    invokeCall (fuel + 2) config environment config.module.entry [] [] 0 state =
      (enterActivation (fuel + 1) config activation [] implementation.body 0 >>= fun carriers =>
        deliverCarriers (fuel + 1) config.layout [] carriers 0) after := by
  simp only [invokeCall, getImplementation, originalAt, implementationAt, resultsEmpty, parametersEmpty,
    Array.size_empty, Array.toList_empty, List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.mapM_nil, evalArguments, freshAct, EvalM.get, EvalM.set, bind, pure,
    List.map_nil, List.zip_nil_left, Nat.not_le.mpr depth]

theorem acceptedEntryCallSetup (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      frame.interpretation.environment = activation ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  obtain ⟨frame, activation, environmentEq, act, scopes, channels, freshActed, freshScope, finalWorld, finalSource,
    position, phase, parameters, results, original, originalAt, implementationAt, implementationId, variables⟩ :=
    acceptedEntryPushedStatements config accepted state ambient types live regions pending world
  have canonical : activation = ⟨original.impl, state.nextAct, frame.source.impl.vars, [], []⟩ := by
    cases activation with
    | mk impl act' vars scopes' channels' =>
      simp only at implementationId act variables scopes channels
      cases implementationId
      cases act
      cases variables
      cases scopes
      cases channels
      rfl
  have step := entryCallStep (fuel + 1) config environment state original frame.source.impl originalAt implementationAt
    parameters results depth
  simp only [Nat.add_assoc] at step
  rw [← canonical] at step
  have lookup : config.module.impls[activation.implementation]? = some frame.source.impl := by
    rw [implementationId]
    exact implementationAt
  have entry : enterActivation (fuel + 2) config activation [] frame.source.impl.body 0 =
      finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) := by
    funext current
    simp only [enterActivation, lookup, results, Array.toList_empty, List.map_nil]
  rw [entry] at step
  exact ⟨frame, activation, environmentEq, step, finalWorld, finalSource, position, phase, results⟩

theorem zeroGlobals_runModule_entry (fuel : Nat) (config : EvalConfig) (context : Context) (implementation : Impl)
    (noGlobals : config.module.globals.size = 0)
    (found : config.module.contexts[config.module.entry]? = some context)
    (impl : config.module.impls[context.impl]? = some implementation) (resultsEmpty : implementation.results = #[]) :
    runModule fuel config .initial =
      (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers =>
        publishCarriers 0 carriers) .initial := by
  simp only [runModule, noGlobals, List.range_zero, initGlobals, getImplementation, found, impl, resultsEmpty,
    Array.toList_empty, channelsFor, List.mapM_nil, bind, pure]

theorem acceptedZeroGlobalRunEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (noGlobals : config.module.globals.size = 0) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let initial := ExecutionState.initial
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initial with nextAct := initial.nextAct + 1, activations := activation :: initial.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      runModule (fuel + 3) config initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers =>
          publishCarriers 0 carriers) initial ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initial =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      frame.interpretation.environment = activation ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] (declaredRootTypes config.module)
        (fun _ => False) [] [] ∧
      AcceptedFrame config accepted next after (declaredRootTypes config.module) ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  have world : AcceptedWorld config config.module.globals.size .initial [] (declaredRootTypes config.module)
      (fun _ => False) [] [] := by
    simpa only [noGlobals] using initial_acceptedWorld config accepted.accepted
  have depth : ExecutionState.initial.activations.length < Goose.Core.maxCallDepth := by
    simp [ExecutionState.initial, Goose.Core.maxCallDepth]
  obtain ⟨frame, activation, environmentEq, call, finalWorld, finalSource, position, phase, results⟩ :=
    acceptedEntryCallSetup fuel config accepted ⟨0, 0, #[], [], []⟩ .initial [] (declaredRootTypes config.module)
      (fun _ => False) [] [] world depth
  obtain ⟨original, implementation, originalAt, implementationAt, parametersEmpty, resultsEmpty⟩ :=
    validated_entry config.module accepted.accepted
  exact ⟨frame, activation, zeroGlobals_runModule_entry (fuel + 3) config original implementation noGlobals
    originalAt implementationAt resultsEmpty, call, environmentEq, finalWorld, finalSource, position, phase, results⟩

#print axioms entryCallStep
#print axioms acceptedEntryCallSetup
#print axioms zeroGlobals_runModule_entry
#print axioms acceptedZeroGlobalRunEntry

end Goose.Proofs.ConstructionAcceptedExecution
