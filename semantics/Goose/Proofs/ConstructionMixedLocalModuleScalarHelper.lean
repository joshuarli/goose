import Goose.Proofs.ConstructionMixedLocalEntryReplay
import Goose.Proofs.ConstructionAcceptedParameterPositionInvoke
import Goose.Proofs.ConstructionEntryScalarHelperTail
import Goose.Proofs.ConstructionAcceptedActivationWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedMixedLocalModule_scalarHelperTail_fromEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (parameter : Param) (descriptor : LocalVar) (argument : Expr)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedLocalStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = some (.call helperContextId [.byVal argument] origin))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperParams : helper.params = #[parameter]) (helperResults : helper.results = #[])
    (parameterMode : parameter.mode = .byValue) (parameterDeclared : helper.vars[0]? = some descriptor)
    (parameterScalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (argumentForm : AcceptedBinaryExpression argument)
    (helperForm : MixedLocalStatements helper.body.stmts) (helperTail : helper.body.value = none)
    (helperOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperScalarOwners : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, helper.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
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
    obtain ⟨frame, next, activation, types, nextLive, regions, channels, frameInitialized, implementationEq, environmentEq, callStep, phase, entryCompatible, nextFull, world, flow, finalSource, sourceEq, interpretationEq, phaseEq, limitEq, finalBounded, finalReplay⟩ :=
      acceptedMixedLocalEntry_replayBody fuel config accepted state live original implementation world
        originalAt implementationAt form owners scalarOwners
    let initialized := state
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
    change AcceptedWorld config next.initialized
      (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
      [.callChannels activation []] types nextLive regions [] at world
    change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at flow
    change AcceptedFrame config accepted next (Goose.Proofs.Exit.stepState
      (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before)) types at finalSource
    change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .ok _ _ => typeStatements entryFrame.typingFuel entryFrame.typing frame.source.impl.body.stmts entryFrame.typingCounter =
          .ok (next.typing, next.typingCounter) ∧ rpStmts entryFrame.source frame.source.impl.body.stmts entryFrame.rootCursor =
            .ok ((), next.rootCursor)
      | _ => True) at finalReplay
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | escape address carriers after | jump target kind after => simp only [outcome] at flow
    | stop reason after =>
      have moduleStop := byteEntry_statements_stopped_module fuel config initialized frame activation after reason
        environmentEq moduleStep callStep outcome
      simp only [outcome, Goose.Proofs.Exit.stepState] at world
      exact Or.inl ⟨reason, after, next.initialized, [.callChannels activation []], types, nextLive, regions, moduleStop, world⟩
    | ok result after =>
      simp only [outcome] at flow
      subst result
      cases fuel with
      | zero => simp [execStmts, timeout, EvalM.stop] at outcome
      | succ fuel =>
        simp only [outcome, Goose.Proofs.Exit.stepState] at world
        have valueEq : frame.source.impl.body.value = some (.call helperContextId [.byVal argument] origin) := by
          simpa only [implementationEq] using tail
        have scopeBody : frame.source.impl.body = ⟨frame.source.impl.body.scope, frame.source.impl.body.stmts,
            some (.call helperContextId [.byVal argument] origin)⟩ := by
          cases shape : frame.source.impl.body with
          | mk scope statements value =>
            simp only [shape, Block.value] at valueEq
            subst value
            rfl
        have normal : execStmts (fuel + 1) config
            { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
            frame.source.impl.body.stmts before = .ok (.normal .unit) after := by
          simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope,
            environmentEq] using outcome
        let scopeEnvironment := { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
        have identity := acceptedEntry_callIdentity config next.initialized after activation types nextLive regions [] world
        have initializedFull : next.initialized = config.module.globals.size := nextFull
        have fullWorld : AcceptedWorld config config.module.globals.size after [.callChannels activation []] types nextLive regions [] := initializedFull ▸ world
        simp only [outcome, Goose.Proofs.Exit.stepState] at finalSource finalReplay
        let blockFrame := implementationBodyFrame config entryFrame
        have entryPhase : entryFrame.phase = .implementation config.module.entry := by
          simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using phase
        have blockPosition : SourcePosition accepted blockFrame (.block blockFrame.source.impl.body) := by
          exact .implementationBody entryFrame config.module.entry entryPhase entryCompatible
        have blockBody : blockFrame.source.impl.body = ⟨frame.source.impl.body.scope, frame.source.impl.body.stmts,
            some (.call helperContextId [.byVal argument] origin)⟩ := by
          simpa only [blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using scopeBody
        rw [blockBody] at blockPosition
        have replayTyped : typeStatements 4095 { blockFrame.typing with scope := frame.source.impl.body.scope }
            frame.source.impl.body.stmts blockFrame.typingCounter = .ok (next.typing, next.typingCounter) := by
          simpa only [blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using finalReplay.1
        have replayRooted : rpStmts { blockFrame.source with scopes := frame.source.impl.body.scope :: blockFrame.source.scopes }
            frame.source.impl.body.stmts blockFrame.rootCursor = .ok ((), next.rootCursor) := by
          simpa only [blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using finalReplay.2
        have tailPosition : SourcePosition accepted { next with typingFuel := 4095 }
            (.expression (.call helperContextId [.byVal argument] origin)) := by
          apply blockPosition.blockTail_afterReplay accepted blockFrame next frame.source.impl.body.scope 4095
            frame.source.impl.body.stmts (.call helperContextId [.byVal argument] origin) rfl replayTyped replayRooted
          · simpa only [blockFrame, entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame] using sourceEq
          · simpa only [blockFrame, implementationBodyFrame] using interpretationEq
          · simpa only [blockFrame, implementationBodyFrame, entryFrame, entryStatementsFrame, blockStatementsFrame] using nextFull.trans frameInitialized.symm
          · simpa only [blockFrame, implementationBodyFrame] using phaseEq
        let callFrame := { next with typingFuel := 4095 }
        have callEnvironment : callFrame.interpretation.environment = scopeEnvironment := by
          simp only [callFrame, interpretationEq, entryStatementsFrame, blockStatementsFrame,
            RootInterpretation.enterScope, environmentEq, scopeEnvironment, activated]
        have helperWorld := mixedLocalScalarParameter_position_call_world argumentForm fuel 4093 config accepted callFrame after
          [.callChannels activation []] types nextLive regions [] helperContextId origin helperContext helper parameter descriptor
          helperContextAt helperAt helperParams helperResults parameterMode parameterDeclared parameterScalar nextFull (by simpa only [callFrame, nextFull] using fullWorld)
          (finalSource.withTypingFuel 4095) finalBounded rfl tailPosition helperForm helperTail helperOwners helperScalarOwners identity.1 identity.2
        rw [callEnvironment] at helperWorld
        have shape : match invokeCall fuel config scopeEnvironment helperContextId [.byVal argument] [] origin after with
          | .ok carriers _ => carriers = [] | .stop .. => True | _ => False := by
          cases invoked : invokeCall fuel config scopeEnvironment helperContextId [.byVal argument] [] origin after <;>
            simp only [invoked] at helperWorld ⊢
          exact helperWorld.1
        have execution := execActivationBody_scalarHelperTail fuel config activation frame.source.impl.body.scope
          frame.source.impl.body.stmts helperContextId origin argument activated after channels normal shape
        rw [← scopeBody] at execution
        cases invoked : invokeCall fuel config scopeEnvironment helperContextId [.byVal argument] [] origin after with
        | escape address carriers final | jump target kind final => simp only [invoked] at helperWorld
        | stop reason final =>
          simp only [invoked] at helperWorld
          obtain ⟨nextAmbient, helperTypes, helperLive, helperRegions, finalWorld⟩ := helperWorld
          have stopped : execActivationBody (fuel + 2) config activation [] frame.source.impl.body activated = .stop reason final := by
            simpa only [scopeEnvironment, invoked] using execution
          apply Or.inl
          refine ⟨reason, final, config.module.globals.size, nextAmbient, helperTypes, helperLive, helperRegions, ?_, finalWorld⟩
          rw [moduleStep]
          dsimp only [activated] at stopped
          simp only [bind, callStep, finishActivation, stopped]
        | ok carriers final =>
          simp only [invoked] at helperWorld
          obtain ⟨same, helperTypes, helperLive, helperRegions, finalWorld⟩ := helperWorld
          subst carriers
          let released := releaseScopeState activation frame.source.impl.body.scope activated.nextScope final
          have done : execActivationBody (fuel + 2) config activation [] frame.source.impl.body activated = .ok [] released := by
            simpa only [scopeEnvironment, invoked, released] using execution
          have releasedWorld := finalWorld.releaseScope config config.module.globals.size final [.callChannels activation []] helperTypes helperLive helperRegions []
            activation frame.source.impl.body.scope activated.nextScope
          let finished := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
          have finishedWorld := releasedWorld.finishEntry config config.module.globals.size released activation helperTypes _ helperRegions []
          apply Or.inr
          refine ⟨finished, config.module.globals.size, helperTypes, _, helperRegions, ?_, finishedWorld⟩
          rw [moduleStep]
          simp [bind, callStep, finishActivation, done, channels, finishChannels, landCarriersInto, deliverCarriers,
            publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
            bind, pure, Except.pure, Except.bind, finished, released, activated]

theorem acceptedMixedLocalModule_scalarHelperTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (implementation : Impl) (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (parameter : Param) (descriptor : LocalVar) (argument : Expr)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (form : MixedLocalStatements implementation.body.stmts)
    (owners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ implementation.body.stmts →
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (scalarOwners : ∀ id expression origin, .letS id expression origin ∈ implementation.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, implementation.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (tail : implementation.body.value = some (.call helperContextId [.byVal argument] origin))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperParams : helper.params = #[parameter]) (helperResults : helper.results = #[])
    (parameterMode : parameter.mode = .byValue) (parameterDeclared : helper.vars[0]? = some descriptor)
    (parameterScalar : (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool)
    (argumentForm : AcceptedBinaryExpression argument)
    (helperForm : MixedLocalStatements helper.body.stmts) (helperTail : helper.body.value = none)
    (helperOwners : ∀ declaration : ByteOwnerDeclaration, declaration.statement ∈ helper.body.stmts →
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperScalarOwners : ∀ id expression origin, .letS id expression origin ∈ helper.body.stmts →
      AcceptedBinaryExpression expression → ∀ descriptor, helper.vars[id]? = some descriptor →
        (∃ ty, descriptor.ty = .int ty) ∨ descriptor.ty = .bool) :
    (∃ stop after initialized ambient types live regions,
      runModule fuel config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule fuel config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  cases fuel with
  | zero => exact Or.inl (acceptedByteModule_lowFuel 0 config accepted globals (by omega))
  | succ fuel =>
    cases fuel with
    | zero => exact Or.inl (acceptedByteModule_lowFuel 1 config accepted globals (by omega))
    | succ fuel =>
      cases fuel with
      | zero => exact Or.inl (acceptedByteModule_lowFuel 2 config accepted globals (by omega))
      | succ fuel =>
        have same : fuel + 3 = fuel + 1 + 1 + 1 := by omega
        rw [← same]
        exact acceptedMixedLocalModule_scalarHelperTail_fromEntry fuel config accepted original implementation helperContextId origin
          helperContext helper parameter descriptor argument globals originalAt implementationAt form owners scalarOwners tail helperContextAt helperAt
          helperParams helperResults parameterMode parameterDeclared parameterScalar argumentForm helperForm helperTail helperOwners helperScalarOwners

#print axioms acceptedMixedLocalModule_scalarHelperTail
#print axioms acceptedMixedLocalModule_scalarHelperTail_fromEntry
end Goose.Proofs.ConstructionAcceptedExecution
