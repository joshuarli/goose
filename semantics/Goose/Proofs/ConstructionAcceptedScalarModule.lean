import Goose.Proofs.ConstructionAcceptedScalarControl
import Goose.Proofs.ConstructionByteModuleLowFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

private theorem scalarEntryFrame_fullInitialization (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (context : Nat)
    (phase : frame.phase = .implementation context) (source : AcceptedFrame config accepted frame state types) :
    AcceptedFrame config accepted { frame with initialized := config.module.globals.size } state types := by
  have origin := source.compatible.origin
  have origin' : SourceOrigin accepted { frame with initialized := config.module.globals.size } := by
    simpa only [SourceOrigin, phase] using origin
  refine ⟨⟨source.compatible.module, source.compatible.rootModule, source.compatible.variables,
    source.compatible.sourceVariables, source.compatible.scopes, source.compatible.globalCount,
    source.compatible.globals, Nat.le_refl _, source.compatible.declarations, source.compatible.typingBound,
    source.compatible.visible, source.compatible.initializing, source.compatible.currentScope, origin'⟩,
    source.frontier, source.scopeFrontier, source.initializingBefore, source.aliases, source.locals, source.localTypes,
    source.uninitializedLocals, source.uninitializedTypes, ?_, source.direct, source.contents⟩
  intro id future within
  have lower : frame.initialized ≤ id := Nat.le_trans source.compatible.initialized future
  exact source.futureGlobals id lower within

theorem acceptedScalarEntry_normal_scope (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (state : ExecutionState) (live : Goose.Core.RootInst → Prop)
    (original : Context) (implementation : Impl)
    (world : AcceptedWorld config config.module.globals.size state [] (declaredRootTypes config.module) live [] [])
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : ScalarExpressionStatements implementation.body.stmts)
    (tail : implementation.body.value = none) :
    ∃ (frame next : ConstructionSourceFrame) (activation : RuntimeActivation)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion),
        let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      let outcome := execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before
      activation.channels = [] ∧ frame.source.impl = implementation ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 state =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated ∧
      (match outcome with
      | .ok (.normal .unit) after =>
        execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated =
          .ok [] (releaseScopeState activation frame.source.impl.body.scope activated.nextScope after) ∧
        AcceptedWorld config next.initialized (releaseScopeState activation frame.source.impl.body.scope activated.nextScope after)
          [.callChannels activation []] types
          (fun root => nextLive root ∧ (Goose.Proofs.Exit.runtimeScopeRoots activation frame.source.impl.body.scope activated.nextScope).contains root = false)
          regions []
      | .stop reason after =>
        execActivationBody (fuel + 1) config activation [] frame.source.impl.body activated = .stop reason after ∧
        AcceptedWorld config next.initialized after [.callChannels activation []] types nextLive regions []
      | _ => False) := by
  obtain ⟨frame, activation, environmentEq, act, scopes, channels, freshActed, freshScope, frameWorld, source,
    position, phase, parameters, results, entry, entryAt, implAt, implId, vars⟩ :=
    acceptedEntryPushedStatements config accepted state [] (declaredRootTypes config.module) live [] [] world
  have entryEq : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
  subst entry
  have implementationEq : frame.source.impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
  have depth : state.activations.length < Goose.Core.maxCallDepth := by
    have runtime := world.ownership.runtime.activations
    cases active : state.activations with
    | nil => simp [Goose.Core.maxCallDepth]
    | cons head tail => simp [active, OwnershipAmbient.activations] at runtime
  have canonical : activation = ⟨original.impl, state.nextAct, frame.source.impl.vars, [], []⟩ := by
    cases activation with
    | mk impl act' vars' scopes' channels' =>
      simp only at implId act vars scopes channels
      cases implId
      cases act
      cases vars
      cases scopes
      cases channels
      rfl
  have step := entryCallStep (fuel + 1) config ⟨0, 0, #[], [], []⟩ state original frame.source.impl originalAt implAt
    parameters results depth
  simp only [Nat.add_assoc] at step
  rw [← canonical] at step
  have lookup : config.module.impls[activation.implementation]? = some frame.source.impl := by
    rw [implId]
    exact implAt
  have entryAction : enterActivation (fuel + 2) config activation [] frame.source.impl.body 0 =
      finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) := by
    funext current
    simp only [enterActivation, lookup, results, Array.toList_empty, List.map_nil]
  rw [entryAction] at step
  let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
  let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
  let entryFrame := entryStatementsFrame config frame activated.nextScope
  let full := { entryFrame with initialized := config.module.globals.size }
  let types := declaredRootTypes config.module
  let nextLive := live
  let regions : List ReceivingRegion := []
  have form' : ScalarExpressionStatements frame.source.impl.body.stmts := by rw [implementationEq]; exact form
  have fullSource : AcceptedFrame config accepted full before types :=
    scalarEntryFrame_fullInitialization config accepted entryFrame before types config.module.entry phase source
  have globals : GlobalRepresentations config.module config.module.globals.size before := by
    refine ⟨world.globals.1, ?_⟩
    intro id member
    obtain ⟨descriptor, value, declared, found, represented⟩ := world.globals.2 id member
    exact ⟨descriptor, value, declared, found, represented⟩
  have fullWorld : AcceptedWorld config full.initialized before [.callChannels activation []] types live [] [] := by
    exact ⟨⟨frameWorld.ownership, globals, frameWorld.globalTypes, frameWorld.layouts, frameWorld.typeFrontier,
      frameWorld.syntheticFrontier, frameWorld.heap, frameWorld.objectsRegistered, frameWorld.ordinalsRegistered,
      frameWorld.backing, frameWorld.protections, frameWorld.carriers⟩, world.globalLive⟩
  have fullPosition : SourcePosition accepted full (.statements frame.source.impl.body.stmts) :=
    position.instantiate entryFrame.interpretation config.module.globals.size
  have limit : full.typing.globalLimit ≤ config.module.globals.size := by
    simp [full, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame]
  have initialBound : GlobalEffectTargetsBounded full.rootCursor.eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets, full, entryFrame, entryStatementsFrame,
      blockStatementsFrame, implementationBodyFrame]
  have count : full.interpretation.globalCount = config.module.globals.size := source.compatible.globalCount
  have available : ∀ final, rpStmts full.source frame.source.impl.body.stmts full.rootCursor = .ok ((), final) →
      GlobalEffectsAvailable full.interpretation full.initialized final.eff := by
    intro final rooted
    have bound := form'.effects_bounded config accepted full config.module.globals.size fullPosition limit initialBound final rooted
    change GlobalEffectsAvailable full.interpretation config.module.globals.size final.eff
    rw [← count]
    exact (globalEffectsAvailable_iff_bounded full.interpretation final.eff).2 (by simpa only [count] using bound)
  have result := fullPosition.scalarStatements_complete accepted full frame.source.impl.body.stmts form' available fuel before
    [.callChannels activation []] types live [] [] fullWorld fullSource
  have finalWorld := result.2.2.1
  have complete := result.2.1
  have control := execStmts_scalar_controlFree form' fuel config entryFrame.interpretation.environment
  have finalFlow : (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) := by
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | ok value after =>
      obtain ⟨finalFrame, flow, rest⟩ := complete value after outcome
      exact flow
    | stop reason after => trivial
    | escape address carriers after => exact (control.1 before address carriers after outcome).elim
    | jump target kind after => exact (control.2 before target kind after outcome).elim
  change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at finalFlow
  change AcceptedWorld config full.initialized
    (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
    [.callChannels activation []] types nextLive regions [] at finalWorld
  refine ⟨frame, full, activation, types, nextLive, regions, channels, implementationEq, step, ?_⟩
  change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | .ok (.normal .unit) after => _ | .stop reason after => _ | _ => False)
  cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
  | stop reason after =>
    have stopped : execStmts fuel config
      { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
      frame.source.impl.body.stmts before = .stop reason after := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using outcome
    exact ⟨execActivationBody_statements_stopped fuel config activation frame.source.impl.body activated after reason stopped,
      by simpa only [outcome, Goose.Proofs.Exit.stepState] using finalWorld⟩
  | escape address carriers after | jump target kind after => simp only [outcome] at finalFlow
  | ok flow after =>
    simp only [outcome] at finalFlow
    subst flow
    have normal : execStmts fuel config
      { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
      frame.source.impl.body.stmts before = .ok (.normal .unit) after := by
      simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using outcome
    have finalWorld' : AcceptedWorld config full.initialized after [.callChannels activation []] types nextLive regions [] := by
      simpa only [outcome, Goose.Proofs.Exit.stepState] using finalWorld
    exact ⟨execActivationBody_empty_normal fuel config activation frame.source.impl.body activated after channels
      (by simpa only [implementationEq] using tail) normal,
      finalWorld'.releaseScope config full.initialized after [.callChannels activation []] types nextLive regions []
        activation frame.source.impl.body.scope activated.nextScope⟩


theorem acceptedScalarModule_noTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : ScalarExpressionStatements implementation.body.stmts)
    (tail : implementation.body.value = none) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule (fuel + 3) config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  obtain ⟨completed, initialLive, initialRegions, bound, initialWorld, final⟩ :=
    initGlobals_byteOwners_initial_complete (fuel + 3) config accepted globals
  cases initializedRun : initGlobals (fuel + 3) config (List.range config.module.globals.size) .initial with
  | stop reason after =>
    simp only [initializedRun, Goose.Proofs.Exit.stepState] at initialWorld final
    exact Or.inl ⟨reason, after, completed, [], declaredRootTypes config.module, initialLive, initialRegions, final.2, initialWorld⟩
  | escape address carriers after | jump target kind after => simp only [initializedRun] at final
  | ok value state =>
    cases value
    have initializedWorld : ∃ live, AcceptedWorld config config.module.globals.size state []
        (declaredRootTypes config.module) live [] [] := by
      obtain ⟨live, world, clear⟩ := initGlobals_byteOwners_initial (fuel + 2) config accepted state globals (by
        simpa only [Nat.add_assoc] using initializedRun)
      exact ⟨live, world⟩
    obtain ⟨live, world⟩ := initializedWorld
    obtain ⟨frame, next, activation, types, nextLive, regions, channels, implEq, callStep, bodyResult⟩ :=
      acceptedScalarEntry_normal_scope fuel config accepted state live original implementation world
        originalAt implementationAt form tail
    let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
    let entryFrame := entryStatementsFrame config frame activated.nextScope
    have moduleStep : runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers =>
          publishCarriers 0 carriers) state := by
      have results := validated_entry config.module accepted.accepted
      obtain ⟨entry, impl, entryAt, implAt, params, results⟩ := results
      have sameEntry : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
      subst entry
      have sameImpl : impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
      subst impl
      simp only [runModule, initializedRun, bind, getImplementation, originalAt, implementationAt, results,
        Array.toList_empty, channelsFor, List.mapM_nil, pure]
    change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .ok (.normal .unit) after => _ | .stop reason after => _ | _ => False) at bodyResult
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | escape address carriers after | jump target kind after => simp only [outcome] at bodyResult
    | stop reason after =>
      simp only [outcome] at bodyResult
      obtain ⟨stopped, afterWorld⟩ := bodyResult
      apply Or.inl
      refine ⟨reason, after, next.initialized, [.callChannels activation []], types, nextLive, regions, ?_, afterWorld⟩
      rw [moduleStep]
      simp only [bind, callStep, finishActivation, stopped]
    | ok flow after =>
      simp only [outcome] at bodyResult
      cases flow with
      | breaking value | continuing => cases bodyResult
      | normal value =>
        cases value with
        | unit =>
          obtain ⟨done, afterWorld⟩ := bodyResult
          let released := releaseScopeState activation frame.source.impl.body.scope activated.nextScope after
          let finished := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
          have finishedWorld := afterWorld.finishEntry config next.initialized released activation types _ regions []
          apply Or.inr
          refine ⟨finished, next.initialized, types, _, regions, ?_, finishedWorld⟩
          rw [moduleStep]
          simp [bind, callStep, finishActivation, done, channels, finishChannels, landCarriersInto, deliverCarriers,
            publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
            bind, pure, Except.pure, Except.bind, finished, released, activated]
        | _ => cases bodyResult


theorem acceptedScalarModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : ScalarExpressionStatements implementation.body.stmts)
    (tail : implementation.body.value = none) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  by_cases low : fuel < 3
  · obtain ⟨stop, after, initialized, ambient, types, live, regions, done, world⟩ :=
      acceptedByteModule_lowFuel fuel config accepted globals low
    simp only [done, Goose.Proofs.Exit.stepState]
    exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
  · obtain ⟨remaining, exactFuel⟩ : ∃ remaining, fuel = remaining + 3 := ⟨fuel - 3, by omega⟩
    subst fuel
    rcases acceptedScalarModule_noTail remaining config accepted original implementation globals
        originalAt implementationAt form tail with stopped | done
    · obtain ⟨stop, after, initialized, ambient, types, live, regions, executed, world⟩ := stopped
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
    · obtain ⟨after, initialized, types, live, regions, executed, world⟩ := done
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, [], types, live, regions, world, trivial⟩

#print axioms acceptedScalarModule_allFuel
#print axioms acceptedScalarEntry_normal_scope
#print axioms acceptedScalarModule_noTail
end Goose.Proofs.ConstructionAcceptedExecution
