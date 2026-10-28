import Goose.Proofs.ConstructionEntryHelperTail
import Goose.Proofs.ConstructionByteHelperCall
import Goose.Proofs.ConstructionEntrySetupChannels
import Goose.Proofs.ConstructionAcceptedActivationWorld
import Goose.Proofs.ConstructionByteModuleLowFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem acceptedByteModule_byteHelperTail_fromEntry (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (helperDeclarations : List ByteOwnerDeclaration)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (tail : implementation.body.value = some (.call helperContextId [] origin))
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperParams : helper.params = #[]) (helperResults : helper.results = #[])
    (helperBody : helper.body.stmts = helperDeclarations.map ByteOwnerDeclaration.statement)
    (helperTail : helper.body.value = none)
    (helperOwners : ∀ declaration ∈ helperDeclarations,
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperCheckFuel : helperDeclarations.length ≤ 4094) (checkFuel : declarations.length ≤ 4094) :
    (∃ stop after initialized ambient types live regions,
      runModule (fuel + 3) config .initial = .stop stop after ∧
      AcceptedWorld config initialized after ambient types live regions []) ∨
    (∃ after initialized types live regions,
      runModule (fuel + 3) config .initial = .ok () after ∧
      AcceptedWorld config initialized after [] types live regions []) := by
  rcases acceptedByteGlobalsEntryBodyOrStopWithChannels fuel config accepted declarations original implementation globals
      originalAt implementationAt body owners checkFuel with stopped | entry
  · obtain ⟨reason, after, initialized, live, regions, moduleStop, bound, world⟩ := stopped
    exact Or.inl ⟨reason, after, initialized, [], declaredRootTypes config.module, live, regions, moduleStop, world⟩
  · obtain ⟨initialized, frame, next, activation, types, live, regions, initializedRun, moduleStep, callStep,
      channels, frameInitialized, implementationEq, environmentEq, initializedEq, extended, world, source, flow⟩ := entry
    let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
    let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
    let entryFrame := entryStatementsFrame config frame activated.nextScope
    change AcceptedWorld config next.initialized
      (Goose.Proofs.Exit.stepState (execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before))
      [.callChannels activation []] types live regions [] at world
    change (match execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
      | .ok result _ => result = .normal .unit | .stop _ _ => True | .escape .. | .jump .. => False) at flow
    cases outcome : execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before with
    | escape address carriers after | jump target kind after => simp only [outcome] at flow
    | stop reason after =>
      have moduleStop := byteEntry_statements_stopped_module fuel config initialized frame activation after reason
        environmentEq moduleStep callStep outcome
      simp only [outcome, Goose.Proofs.Exit.stepState] at world
      exact Or.inl ⟨reason, after, next.initialized, [.callChannels activation []], types, live, regions, moduleStop, world⟩
    | ok result after =>
      simp only [outcome] at flow
      subst result
      cases fuel with
      | zero => simp [execStmts, timeout, EvalM.stop] at outcome
      | succ fuel =>
        simp only [outcome, Goose.Proofs.Exit.stepState] at world
        have statementsEq : frame.source.impl.body.stmts = declarations.map ByteOwnerDeclaration.statement := by
          simpa only [implementationEq] using body
        have valueEq : frame.source.impl.body.value = some (.call helperContextId [] origin) := by
          simpa only [implementationEq] using tail
        have scopeBody : frame.source.impl.body = ⟨frame.source.impl.body.scope, declarations.map ByteOwnerDeclaration.statement,
            some (.call helperContextId [] origin)⟩ := by
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
            environmentEq, implementationEq, body] using outcome
        let scopeEnvironment := { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
        have identity := acceptedEntry_callIdentity config next.initialized after activation types live regions [] world
        have initializedFull : next.initialized = config.module.globals.size := by
          simpa only [entryFrame, entryStatementsFrame, blockStatementsFrame, implementationBodyFrame, frameInitialized] using initializedEq
        have fullWorld : AcceptedWorld config config.module.globals.size after [.callChannels activation []] types live regions [] := initializedFull ▸ world
        have helperWorld := byteHelper_call_world fuel config accepted after [.callChannels activation []] types live regions []
          scopeEnvironment helperContextId origin helperContext helper helperDeclarations fullWorld helperContextAt helperAt helperParams helperResults
          helperBody helperTail helperOwners helperCheckFuel identity.1 identity.2
        have shape : match invokeCall fuel config scopeEnvironment helperContextId [] [] origin after with
          | .ok carriers _ => carriers = [] | .stop .. => True | _ => False := by
          cases invoked : invokeCall fuel config scopeEnvironment helperContextId [] [] origin after <;>
            simp only [invoked] at helperWorld ⊢
          exact helperWorld.1
        have execution := execActivationBody_helperTail fuel config activation frame.source.impl.body.scope
          (declarations.map ByteOwnerDeclaration.statement) helperContextId origin activated after channels normal shape
        rw [← scopeBody] at execution
        cases invoked : invokeCall fuel config scopeEnvironment helperContextId [] [] origin after with
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

theorem acceptedByteModule_byteHelperTail (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (declarations : List ByteOwnerDeclaration) (original : Context) (implementation : Impl)
    (helperContextId origin : Nat) (helperContext : Context) (helper : Impl)
    (helperDeclarations : List ByteOwnerDeclaration)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor bytes bytesOrigin, config.module.globals[id]? = some descriptor ∧
        descriptor.ty = .varr (.int .u8) ∧ descriptor.init = .bytes (.varr (.int .u8)) bytes bytesOrigin)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (implementationAt : config.module.impls[original.impl]? = some implementation)
    (body : implementation.body.stmts = declarations.map ByteOwnerDeclaration.statement)
    (tail : implementation.body.value = some (.call helperContextId [] origin))
    (owners : ∀ declaration ∈ declarations,
      (implementation.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperContextAt : config.module.contexts[helperContextId]? = some helperContext)
    (helperAt : config.module.impls[helperContext.impl]? = some helper)
    (helperParams : helper.params = #[]) (helperResults : helper.results = #[])
    (helperBody : helper.body.stmts = helperDeclarations.map ByteOwnerDeclaration.statement)
    (helperTail : helper.body.value = none)
    (helperOwners : ∀ declaration ∈ helperDeclarations,
      (helper.vars[declaration.id]?).map (·.ty) = some (.varr (.int .u8)))
    (helperCheckFuel : helperDeclarations.length ≤ 4094) (checkFuel : declarations.length ≤ 4094) :
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
        exact acceptedByteModule_byteHelperTail_fromEntry fuel config accepted declarations
          original implementation helperContextId origin helperContext helper helperDeclarations globals originalAt implementationAt body tail owners
          helperContextAt helperAt helperParams helperResults helperBody helperTail helperOwners helperCheckFuel checkFuel

#print axioms acceptedByteModule_byteHelperTail_fromEntry
#print axioms acceptedByteModule_byteHelperTail
end Goose.Proofs.ConstructionAcceptedExecution
