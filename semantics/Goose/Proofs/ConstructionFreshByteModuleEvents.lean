import Goose.Proofs.ConstructionFreshByteEntryFrames

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem entry_low_events (fuel : Nat) (config : EvalConfig) (state : ExecutionState)
    (original : Context) (implementation : Impl)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (small : fuel < 3) :
    (Goose.Proofs.Exit.stepState ((invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
      fun carriers => publishCarriers 0 carriers) state)).construction.events = state.construction.events := by
  cases fuel with
  | zero => simp [invokeCall, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState]
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [invokeCall, getImplementation, originalAt, implementationAt, resultsEmpty, parametersEmpty,
        evalArguments, timeout, EvalM.stop, bind, pure, Goose.Proofs.Exit.stepState]
    | succ fuel =>
      have zero : fuel = 0 := by omega
      subst fuel
      by_cases depth : state.activations.length ≥ Goose.Core.maxCallDepth <;>
        simp [invokeCall, getImplementation, originalAt, implementationAt, resultsEmpty, parametersEmpty,
          evalArguments, depth, freshAct, EvalM.get, EvalM.set, enterActivation, execActivationBody,
          finishActivation, timeout, EvalM.stop, bind, pure, Goose.Proofs.Exit.stepState]

private theorem entry_high_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState) (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (scope : Nat) (globalDeclarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (globals : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body = .mk scope (declarations.map ByteOwnerDeclaration.statement) none)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ suffix,
      (Goose.Proofs.Exit.stepState ((invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
        fun carriers => publishCarriers 0 carriers) initialized)).construction.events = initialized.construction.events ++ suffix ∧
      ∀ event ∈ suffix, ByteOwnerSequenceEvent event := by
  have globals' : initGlobals ((fuel + 2) + 1) config (List.range config.module.globals.size) .initial = .ok () initialized := by
    simpa only [Nat.add_assoc] using globals
  obtain ⟨globalLive, globalWorld, clear⟩ := initGlobals_byteOwners_initial (fuel + 2) config accepted initialized globalDeclarations globals'
  have depth : initialized.activations.length < Goose.Core.maxCallDepth := by
    have runtime := globalWorld.ownership.runtime.activations
    cases active : initialized.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  obtain ⟨frame, activation, environmentEq, act, scopes, channels, freshActed, freshScope, world, source,
    position, phase, parameters, results, original', originalFound, implementationFound, implementationId, variables⟩ :=
      acceptedEntryPushedStatements config accepted initialized [] (declaredRootTypes config.module) globalLive [] [] globalWorld
  have originalEq : original' = original := Option.some.inj (originalFound.symm.trans originalAt)
  subst original'
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implementationFound.symm.trans implementationAt)
  have canonical : activation = ⟨original.impl, initialized.nextAct, frame.source.impl.vars, [], []⟩ := by
    cases activation with
    | mk impl act' vars scopes' channels' =>
      simp only at implementationId act variables scopes channels
      cases implementationId
      cases act
      cases variables
      cases scopes
      cases channels
      rfl
  let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
  let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  have call := entryCallStep (fuel + 1) config ⟨0, 0, #[], [], []⟩ initialized original frame.source.impl
    originalAt implementationFound parameters results depth
  simp only [Nat.add_assoc, Nat.reduceAdd] at call
  rw [← canonical] at call
  have lookup : config.module.impls[activation.implementation]? = some frame.source.impl := by
    rw [implementationId]
    exact implementationFound
  have enter : enterActivation (fuel + 2) config activation [] frame.source.impl.body 0 =
      finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) := by
    funext current
    simp only [enterActivation, lookup, results, Array.toList_empty, List.map_nil]
  rw [enter] at call
  have body' : frame.source.impl.body = .mk scope (declarations.map ByteOwnerDeclaration.statement) none := by
    rw [implementationEq]; exact body
  have position' : SourcePosition accepted entryFrame (.statements (declarations.map ByteOwnerDeclaration.statement)) := by
    simpa only [body', Block.stmts] using position
  have owners' : ∀ declaration ∈ declarations,
      (entryFrame.typing.variables[declaration.id]?).map (·.ty) = some (.varr (.int .u8)) := by
    intro declaration member
    simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, implementationEq] using owners declaration member
  have unnamed : ∀ declaration ∈ declarations,
      (entryFrame.source.impl.results.toList.zipIdx.find? (fun (result, _) => result.namedLocal == some declaration.id)) = none := by
    intro declaration member
    simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, results,
      Array.toList_empty, List.zipIdx_nil, List.find?_nil]
  obtain ⟨suffix, trace, valid⟩ := execStmts_byteOwners_fresh_events declarations fuel 4094 config accepted entryFrame
    config.module.entry after [.callChannels activation []] (declaredRootTypes config.module) globalLive [] []
    checkFuel rfl world source
    (by simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase)
    position' owners' unnamed
  have env : entryFrame.interpretation.environment =
      { activation with scopes := (scope, activated.nextScope) :: activation.scopes } := by
    simp only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq, body', Block.scope]
  have frameTrace : (Goose.Proofs.Exit.stepState ((invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
      fun carriers => publishCarriers 0 carriers) initialized)).construction.events =
      (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment
        (declarations.map ByteOwnerDeclaration.statement) after)).construction.events := by
    simp only [bind]
    rw [call]
    change (Goose.Proofs.Exit.stepState (((finishActivation config.layout activation [] 0
      (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
        deliverCarriers (fuel + 2) config.layout [] carriers 0) >>= fun carriers => publishCarriers 0 carriers) activated)).construction.events = _
    rw [eval_bind_assoc]
    rw [bind_events_frame]
    · rw [finishActivation_empty_events config.layout activation channels]
      rw [body']
      rw [execActivationBody_byte_events fuel config activation channels scope (declarations.map ByteOwnerDeclaration.statement) activated]
      simpa only [env, after, body', Block.scope]
    · intro carriers current
      exact deliverPublish_empty_events (fuel + 2) config.layout 0 carriers current
  refine ⟨suffix, ?_, valid⟩
  rw [frameTrace, trace]
  rfl

theorem runModule_byteOnly_fresh_events (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl) (scope : Nat)
    (globalDeclarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body = .mk scope (declarations.map ByteOwnerDeclaration.statement) none)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ events,
      (Goose.Proofs.Exit.stepState (runModule fuel config .initial)).construction.events = events ∧
      ∀ event ∈ events, ByteOwnerSequenceEvent event := by
  obtain ⟨globalEvents, globalTrace, globalValid⟩ := initGlobals_acceptedByteOwners_fresh_events fuel config accepted globalDeclarations
  cases globals : initGlobals fuel config (List.range config.module.globals.size) .initial with
  | stop reason after =>
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    refine ⟨globalEvents, ?_, globalValid⟩
    simpa only [runModule, bind, globals, Goose.Proofs.Exit.stepState] using globalTrace
  | escape target carriers after =>
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    refine ⟨globalEvents, ?_, globalValid⟩
    simpa only [runModule, bind, globals, Goose.Proofs.Exit.stepState] using globalTrace
  | jump target kind after =>
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    refine ⟨globalEvents, ?_, globalValid⟩
    simpa only [runModule, bind, globals, Goose.Proofs.Exit.stepState] using globalTrace
  | ok result initialized =>
    cases result
    simp only [globals, Goose.Proofs.Exit.stepState] at globalTrace
    obtain ⟨original', implementation', originalFound, implementationFound, parametersEmpty, resultsEmpty⟩ :=
      validated_entry config.module accepted.accepted
    have originalEq : original' = original := Option.some.inj (originalFound.symm.trans originalAt)
    subst original'
    have implementationEq : implementation' = implementation := Option.some.inj (implementationFound.symm.trans implementationAt)
    subst implementation'
    have run : runModule fuel config .initial =
        (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized := by
      simp only [runModule, bind, globals, getImplementation, originalAt, implementationAt, resultsEmpty,
        Array.toList_empty, channelsFor, List.mapM_nil, pure]
    by_cases small : fuel < 3
    · have trace := entry_low_events fuel config initialized original implementation originalAt implementationAt parametersEmpty resultsEmpty small
      refine ⟨globalEvents, ?_, globalValid⟩
      rw [run, trace, globalTrace]
    · let remaining := fuel - 3
      have fuelEq : fuel = remaining + 3 := by dsimp [remaining]; omega
      have globals' : initGlobals (remaining + 3) config (List.range config.module.globals.size) .initial = .ok () initialized := by
        rw [← fuelEq]; exact globals
      obtain ⟨localEvents, localTrace, localValid⟩ := entry_high_events remaining config accepted initialized declarations original
        implementation scope globalDeclarations globals' originalAt implementationAt body owners checkFuel
      have localTrace' : (Goose.Proofs.Exit.stepState ((invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>=
          fun carriers => publishCarriers 0 carriers) initialized)).construction.events = initialized.construction.events ++ localEvents := by
        rw [fuelEq]; exact localTrace
      refine ⟨globalEvents ++ localEvents, ?_, ?_⟩
      · rw [run, localTrace', globalTrace]
      · intro event member
        simp only [List.mem_append] at member
        rcases member with member | member
        · exact globalValid event member
        · exact localValid event member

#print axioms runModule_byteOnly_fresh_events
#print axioms entry_high_events
#print axioms entry_low_events

end Goose.Proofs.ConstructionAcceptedExecution
