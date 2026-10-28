import Goose.Proofs.ConstructionByteGlobalEntryBody

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedEntryCallSetupWithChannels (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (environment : RuntimeActivation) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config config.module.globals.size state ambient types live regions pending)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation),
      let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      activation.channels = [] ∧ frame.initialized = config.module.globals.size ∧ frame.interpretation.environment = activation ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      AcceptedWorld config next.initialized after (.callChannels activation [] :: ambient) types live regions pending ∧
      AcceptedFrame config accepted next after types ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  obtain ⟨frame, activation, initializedEq, environmentEq, act, scopes, channels, freshActed, freshScope, finalWorld, finalSource,
    position, phase, parameters, results, original, originalAt, implementationAt, implementationId, variables⟩ :=
    acceptedEntryPushedStatements_withInitialized config accepted state ambient types live regions pending world
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
  exact ⟨frame, activation, channels, initializedEq, environmentEq, step, finalWorld, finalSource, position, phase, results⟩

theorem acceptedByteGlobalsEntryWithChannels (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState)
    (declarations : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (globals : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized) :
    ∃ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (live : Goose.Core.RootInst → Prop),
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let after := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let next := entryStatementsFrame config frame activated.nextScope
      runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initialized =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      activation.channels = [] ∧ frame.initialized = config.module.globals.size ∧ frame.interpretation.environment = activation ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] (declaredRootTypes config.module) live [] [] ∧
      AcceptedFrame config accepted next after (declaredRootTypes config.module) ∧
      SourcePosition accepted next (.statements frame.source.impl.body.stmts) ∧
      frame.phase = .implementation config.module.entry ∧ frame.source.impl.results = #[] := by
  have globalRun : initGlobals ((fuel + 2) + 1) config (List.range config.module.globals.size) .initial = .ok () initialized := by
    simpa only [Nat.add_assoc] using globals
  obtain ⟨live, globalWorld, clear⟩ := initGlobals_byteOwners_initial (fuel + 2) config accepted initialized declarations globalRun
  have depth : initialized.activations.length < Goose.Core.maxCallDepth := by
    have runtime := globalWorld.ownership.runtime.activations
    cases active : initialized.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  obtain ⟨frame, activation, channels, initializedEq, environmentEq, call, finalWorld, finalSource, position, phase, results⟩ :=
    acceptedEntryCallSetupWithChannels fuel config accepted ⟨0, 0, #[], [], []⟩ initialized [] (declaredRootTypes config.module)
      live [] [] globalWorld depth
  obtain ⟨original, implementation, originalAt, implementationAt, parametersEmpty, resultsEmpty⟩ :=
    validated_entry config.module accepted.accepted
  have moduleStep : runModule (fuel + 3) config .initial =
      (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers =>
        publishCarriers 0 carriers) initialized := by
    simp only [runModule, globals, bind, getImplementation, originalAt, implementationAt, resultsEmpty,
      Array.toList_empty, channelsFor, List.mapM_nil, pure]
  exact ⟨frame, activation, live, moduleStep, call, channels, initializedEq, environmentEq, finalWorld, finalSource, position, phase, results⟩

theorem acceptedByteGlobalsEntryBodyWithChannels (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (initialized : ExecutionState) (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (initializedRun : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    ∃ (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      let after := Goose.Proofs.Exit.stepState outcome
      runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initialized =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      activation.channels = [] ∧ frame.initialized = config.module.globals.size ∧ frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧ next.initialized = entryFrame.initialized ∧
      RootTypesExtend (declaredRootTypes config.module) types ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] types live regions [] ∧
      AcceptedFrame config accepted next after types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
  obtain ⟨frame, activation, entryLive, moduleStep, callStep, channels, frameInitialized, environmentEq, world, source, position, phase, results⟩ :=
    acceptedByteGlobalsEntryWithChannels fuel config accepted initialized globals initializedRun
  let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  have originFact := source.compatible.origin
  unfold SourceOrigin at originFact
  simp only [entryStatementsFrame, blockStatementsFrame, implementationBodyFrame,
    RootInterpretation.enterScope, phase] at originFact
  obtain ⟨entry, calls, entryAt, implAt, originRest⟩ := originFact
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  obtain ⟨next, types, live, regions, initializedEq, extended, finalWorld, finalSource, finalFlow⟩ :=
    entryByteStatements_accepted_world fuel config accepted frame activation activated before declarations entryLive
      world source position phase results (by simpa only [implementationEq] using body)
      (by simpa only [implementationEq] using owners) checkFuel
  exact ⟨frame, next, activation, types, live, regions, moduleStep, callStep, channels, frameInitialized, implementationEq, environmentEq, initializedEq, extended,
    finalWorld, finalSource, finalFlow⟩

theorem acceptedByteGlobalsEntryBodyOrStopWithChannels (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    (∃ stop after completed live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧ completed < config.module.globals.size ∧
      AcceptedWorld config completed after [] (declaredRootTypes config.module) live regions []) ∨
    ∃ (initialized : ExecutionState) (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
      let environment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      let after := Goose.Proofs.Exit.stepState outcome
      initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial = .ok () initialized ∧
      runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config environment config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized ∧
      invokeCall (fuel + 3) config environment config.module.entry [] [] 0 initialized =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      activation.channels = [] ∧ frame.initialized = config.module.globals.size ∧ frame.source.impl = implementation ∧ frame.interpretation.environment = activation ∧ next.initialized = entryFrame.initialized ∧
      RootTypesExtend (declaredRootTypes config.module) types ∧
      AcceptedWorld config next.initialized after [.callChannels activation []] types live regions [] ∧
      AcceptedFrame config accepted next after types ∧
      (match outcome with | .ok flow _ => flow = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
  rcases acceptedByteGlobalsEntryOrStop fuel config accepted globals with stopped | entry
  · exact Or.inl stopped
  · obtain ⟨initialized, frame, activation, live, initializedRun, rest⟩ := entry
    obtain ⟨bodyFrame, next, bodyActivation, types, bodyLive, regions, moduleStep, callStep, channels, frameInitialized, implementationEq, environmentEq,
      initializedEq, extended, finalWorld, finalSource, finalFlow⟩ :=
      acceptedByteGlobalsEntryBodyWithChannels fuel config accepted initialized declarations original implementation globals initializedRun
        originalAt implementationAt body owners checkFuel
    exact Or.inr ⟨initialized, bodyFrame, next, bodyActivation, types, bodyLive, regions, initializedRun, moduleStep,
      callStep, channels, frameInitialized, implementationEq, environmentEq, initializedEq, extended, finalWorld, finalSource, finalFlow⟩


#print axioms acceptedByteGlobalsEntryBodyOrStopWithChannels
#print axioms acceptedByteGlobalsEntryBodyWithChannels
#print axioms acceptedByteGlobalsEntryWithChannels
#print axioms acceptedEntryCallSetupWithChannels
end Goose.Proofs.ConstructionAcceptedExecution
