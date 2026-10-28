import Goose.Proofs.ConstructionByteEntryScalarOutcome
import Goose.Proofs.ConstructionAcceptedActivationWorld
import Goose.Proofs.ConstructionByteGlobalEntryComplete
import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedByteModule_scalarTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl) (expression : Expr)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (tail : implementation.body.value = some expression)
    (form : AcceptedBinaryExpression expression)
    (enoughFuel : declarations.length + 2 ≤ fuel + 1)
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (checkFuel : declarations.length ≤ 4094) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 4) config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule (fuel + 4) config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  obtain ⟨completed, initialLive, initialRegions, bound, initialWorld, final⟩ :=
    initGlobals_byteOwners_initial_complete (fuel + 4) config accepted globals
  cases initializedRun : initGlobals (fuel + 4) config (List.range config.module.globals.size) .initial with
  | stop reason after =>
    simp only [initializedRun, Goose.Proofs.Exit.stepState] at initialWorld final
    exact Or.inl ⟨reason, after, completed, [], declaredRootTypes config.module, initialLive, initialRegions, final.2, initialWorld⟩
  | escape address carriers after | jump target kind after => simp only [initializedRun] at final
  | ok value state =>
    cases value
    have initializedWorld : ∃ live, AcceptedWorld config config.module.globals.size state []
        (declaredRootTypes config.module) live [] [] := by
      obtain ⟨live, world, clear⟩ := initGlobals_byteOwners_initial (fuel + 3) config accepted state globals (by
        simpa only [Nat.add_assoc] using initializedRun)
      exact ⟨live, world⟩
    obtain ⟨live, world⟩ := initializedWorld
    obtain ⟨frame, next, activation, types, nextLive, regions, channels, implEq, environmentEq, callStep, bodyResult⟩ :=
      acceptedByteEntry_scalarTail_outcome fuel config accepted state live declarations original implementation expression world
        originalAt implementationAt body tail form enoughFuel owners checkFuel
    let activated := { state with nextAct := state.nextAct + 1, activations := activation :: state.activations }
    let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
    let entryFrame := entryStatementsFrame config frame activated.nextScope
    have moduleStep : runModule (fuel + 4) config .initial =
        (invokeCall (fuel + 4) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers =>
          publishCarriers 0 carriers) state := by
      have results := validated_entry config.module accepted.accepted
      obtain ⟨entry, impl, entryAt, implAt, params, results⟩ := results
      have sameEntry : entry = original := Option.some.inj (entryAt.symm.trans originalAt)
      subst entry
      have sameImpl : impl = implementation := Option.some.inj (implAt.symm.trans implementationAt)
      subst impl
      simp only [runModule, initializedRun, bind, getImplementation, originalAt, implementationAt, results,
        Array.toList_empty, channelsFor, List.mapM_nil, pure]
    change (match execStmts (fuel + 1) config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .stop reason after => _ | .ok (.normal .unit) _ => _ | _ => False) at bodyResult
    cases outcome : execStmts (fuel + 1) config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
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
          obtain ⟨tailFrame, tailTypes, tailLive, tailRegions, tailWorld⟩ := bodyResult
          have statementsEq : frame.source.impl.body.stmts = declarations.map ByteOwnerDeclaration.statement := by
            simpa only [implEq] using body
          have valueEq : frame.source.impl.body.value = some expression := by
            simpa only [implEq] using tail
          have scopeBody : frame.source.impl.body = ⟨frame.source.impl.body.scope, declarations.map ByteOwnerDeclaration.statement, some expression⟩ := by
            cases shape : frame.source.impl.body with
            | mk scope statements value =>
              simp only [shape, Block.stmts] at statementsEq
              simp only [shape, Block.value] at valueEq
              subst statements value
              rfl
          have normal : execStmts (fuel + 1) config
              { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
              (declarations.map ByteOwnerDeclaration.statement) before = .ok (.normal .unit) after := by
            simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope,
              environmentEq, statementsEq] using outcome
          have execution := execActivationBody_scalar_tail form fuel config activation frame.source.impl.body.scope
            (declarations.map ByteOwnerDeclaration.statement) activated after channels normal
          rw [← scopeBody] at execution
          let environment := { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
          have control := evalValue_scalar_controlFree form fuel config environment
          change (match execActivationBody (fuel + 2) config activation [] frame.source.impl.body activated with
            | .stop _ final => _ | .ok _ final | .escape _ _ final | .jump _ _ final => _) at tailWorld
          cases evaluated : evalValue fuel config environment expression after with
          | escape address carriers final =>
            exact False.elim (control.1 after address carriers final evaluated)
          | jump target kind final =>
            exact False.elim (control.2 after target kind final evaluated)
          | stop reason final =>
            have stopped : execActivationBody (fuel + 2) config activation [] frame.source.impl.body activated = .stop reason final := by
              simpa only [environment, evaluated] using execution
            simp only [stopped] at tailWorld
            apply Or.inl
            refine ⟨reason, final, tailFrame.initialized, [.callChannels activation []], tailTypes, tailLive, tailRegions, ?_, tailWorld⟩
            dsimp only [activated] at stopped
            rw [moduleStep]
            simp only [bind, callStep, finishActivation, stopped]
          | ok result final =>
            let released := releaseScopeState activation frame.source.impl.body.scope activated.nextScope final
            have done : execActivationBody (fuel + 2) config activation [] frame.source.impl.body activated = .ok [] released := by
              simpa only [environment, evaluated, released] using execution
            simp only [done] at tailWorld
            let finished := { released with activations := released.activations.filter (fun current => current.act != activation.act) }
            have finishedWorld := tailWorld.finishEntry config tailFrame.initialized released activation tailTypes _ tailRegions []
            apply Or.inr
            refine ⟨finished, tailFrame.initialized, tailTypes, _, tailRegions, ?_, finishedWorld⟩
            rw [moduleStep]
            simp [bind, callStep, finishActivation, done, channels, finishChannels, landCarriersInto, deliverCarriers,
              publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
              bind, pure, Except.pure, Except.bind, finished, released, activated]
        | _ => cases bodyResult

#print axioms acceptedByteModule_scalarTail
end Goose.Proofs.ConstructionAcceptedExecution
