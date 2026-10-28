import Goose.Proofs.ConstructionAcceptedCheckedSequenceEntry
import Goose.Proofs.ConstructionAcceptedMixedLocalModule
import Goose.Proofs.ConstructionByteEntryScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem acceptedModule_checkedSequence_fromEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (entryTail : implementation.body.value = none)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (sequence : ∀ (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive regions [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts fuel config frame.interpretation.environment implementation.body.stmts before)) :
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
    obtain ⟨live, world, clear⟩ := initGlobals_byteOwners_initial (fuel + 2) config accepted state globals (by
      simpa only [Nat.add_assoc] using initializedRun)
    obtain ⟨frame, activation, channels, implementationEq, environmentEq, frameInitialized, callStep, outcomeWorld⟩ :=
      acceptedEntry_checkedSequence fuel config accepted state live original implementation world originalAt implementationAt sequence
    let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
    let entryFrame := entryStatementsFrame config frame activated.nextScope
    have moduleStep : runModule (fuel + 3) config .initial =
        (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers =>
          publishCarriers 0 carriers) state := by
      obtain ⟨entry, impl, entryAt, implAt, params, entryResults⟩ := validated_entry config.module accepted.accepted
      have sameEntry : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
      subst entry
      have sameImpl : impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
      subst impl
      simp only [runModule, initializedRun, bind, getImplementation, originalAt, implementationAt, entryResults,
        Array.toList_empty, channelsFor, List.mapM_nil, pure]
    change StatementWorldOutcome config accepted entryFrame.initialized [.callChannels activation []] []
      (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before) at outcomeWorld
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | escape address carriers after | jump target kind after => simp only [StatementWorldOutcome, outcome] at outcomeWorld
    | stop reason after =>
      simp only [StatementWorldOutcome, outcome] at outcomeWorld
      obtain ⟨nextAmbient, nextTypes, nextLive, nextRegions, finalWorld⟩ := outcomeWorld
      have moduleStop := byteEntry_statements_stopped_module fuel config state frame activation after reason
        environmentEq moduleStep callStep outcome
      exact Or.inl ⟨reason, after, entryFrame.initialized, nextAmbient, nextTypes, nextLive, nextRegions, moduleStop, finalWorld⟩
    | ok flow after =>
      simp only [StatementWorldOutcome, outcome] at outcomeWorld
      obtain ⟨normal, nextFrame, nextTypes, nextLive, nextRegions, nextInitialized, finalWorld, finalSource⟩ := outcomeWorld
      subst flow
      have normalRun : execStmts fuel config
          { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
          frame.source.impl.body.stmts before = .ok (.normal .unit) after := by
        simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using outcome
      have done := execActivationBody_empty_normal fuel config activation frame.source.impl.body activated after channels
        (by simpa only [implementationEq] using entryTail) normalRun
      let released := releaseScopeState activation frame.source.impl.body.scope activated.nextScope after
      let finished := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
      have releasedWorld := finalWorld.releaseScope config entryFrame.initialized after [.callChannels activation []] nextTypes nextLive nextRegions []
        activation frame.source.impl.body.scope activated.nextScope
      have finishedWorld := releasedWorld.finishEntry config entryFrame.initialized released activation nextTypes _ nextRegions []
      apply Or.inr
      refine ⟨finished, entryFrame.initialized, nextTypes, _, nextRegions, ?_, finishedWorld⟩
      rw [moduleStep]
      simp [bind, callStep, finishActivation, done, channels, finishChannels, landCarriersInto, deliverCarriers,
        publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
        bind, pure, Except.pure, Except.bind, finished, released, activated]

theorem acceptedModule_checkedSequence_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (entryTail : implementation.body.value = none)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (sequence : ∀ (sequenceFuel : Nat) (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (before : ExecutionState)
      (types : RootTypes) (nextLive : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (scopeInst : Nat),
      AcceptedWorld config frame.initialized before [.callChannels activation []] types nextLive regions [] →
      AcceptedFrame config accepted frame before types → frame.phase = .implementation config.module.entry →
      frame.source.impl = implementation →
      frame.interpretation.environment.scopes = (implementation.body.scope, scopeInst) :: activation.scopes →
      SourcePosition accepted frame (.statements implementation.body.stmts) →
      frame.initialized = config.module.globals.size → frame.typing.globalLimit ≤ config.module.globals.size →
      GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
      StatementWorldOutcome config accepted frame.initialized [.callChannels activation []] []
        (execStmts sequenceFuel config frame.interpretation.environment implementation.body.stmts before)) :
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
    rcases acceptedModule_checkedSequence_fromEntry remaining config accepted original implementation globals entryTail
      originalAt implementationAt (sequence remaining) with stopped | done
    · obtain ⟨stop, after, initialized, ambient, types, live, regions, executed, world⟩ := stopped
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, ambient, types, live, regions, world, trivial⟩
    · obtain ⟨after, initialized, types, live, regions, executed, world⟩ := done
      simp only [executed, Goose.Proofs.Exit.stepState]
      exact ⟨initialized, [], types, live, regions, world, trivial⟩

#print axioms acceptedModule_checkedSequence_allFuel
#print axioms acceptedModule_checkedSequence_fromEntry
end Goose.Proofs.ConstructionAcceptedExecution
