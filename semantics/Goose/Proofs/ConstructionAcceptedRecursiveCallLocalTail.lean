import Goose.Proofs.ConstructionAcceptedRegisterCallTail

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem typeStatements_scalarLocal_callContext {statements : List Stmt} (form : ScalarLocalStatements statements) :
    ∀ (fuel : Nat) (environment next : TypingEnv) (before after : Nat),
      typeStatements fuel environment statements before = .ok (next, after) →
      next.module = environment.module ∧ next.resultRequests = environment.resultRequests := by
  induction form with
  | nil =>
    intro fuel environment next before after checked
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      simp only [typeStatements, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨rfl, rfl⟩
  | cons id expression origin rest form tail ih =>
    intro fuel environment next before after checked
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at checked; cases checked
    | succ fuel =>
      simp only [typeStatements, bind, StateT.bind] at checked
      cases step : typeStatement fuel environment (.letS id expression origin) before with
      | error failure => simp only [step, Except.bind] at checked; cases checked
      | ok pair =>
        obtain ⟨middle, counter⟩ := pair
        simp only [step, Except.bind] at checked
        cases fuel with
        | zero => change Except.error _ = Except.ok _ at step; cases step
        | succ fuel =>
          have middleShape := typeStatement_let_environment fuel environment middle id expression origin before counter step
          have preserved := ih (fuel + 1) middle next counter after checked
          simpa [middleShape] using preserved

theorem ScalarLocalReplay.registerCall_tail_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (blockFrame child final : ConstructionSourceFrame) (scope fuel target origin : Nat) (statements : List Stmt)
    (context : Context) (callee : Impl) (ty : Ty)
    (position : SourcePosition accepted blockFrame (.block ⟨scope, statements, some (.call target [] origin)⟩))
    (nesting : blockFrame.typingFuel = (fuel + 1) + 1)
    (childTyping : child.typing = { blockFrame.typing with scope := scope })
    (childFuel : child.typingFuel = fuel + 1) (childCounter : child.typingCounter = blockFrame.typingCounter)
    (childSource : child.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes })
    (childCursor : child.rootCursor = blockFrame.rootCursor)
    (replay : ScalarLocalReplay child final statements) (form : ScalarLocalStatements statements)
    (contextAt : blockFrame.typing.module.contexts[target]? = some context)
    (calleeAt : blockFrame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : blockFrame.typing.resultRequests = [.register])
    (available : ∀ roots rootsAfter,
      rpExpr final.source (.call target [] origin) final.rootCursor = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable final.interpretation final.initialized rootsAfter.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue { final with typingFuel := fuel + 1 } (.call target [] origin) ty roots typingAfter rootsAfter := by
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    _, typedStatements, rootedStatements, typedTail, rootedTail⟩ :=
    position.blockTail_checks accepted blockFrame scope (fuel + 1) statements (.call target [] origin) nesting
  obtain ⟨typedReplay, rootedReplay, sourceSame, interpretationSame⟩ := replay
  rw [childTyping, childFuel, childCounter] at typedReplay
  have sameTyping : (final.typing, final.typingCounter) = (next, typingMiddle) :=
    Except.ok.inj (typedReplay.symm.trans typedStatements)
  obtain ⟨sameEnvironment, sameCounter⟩ := Prod.mk.inj sameTyping
  rw [childSource, childCursor] at rootedReplay
  have sameRoots : final.rootCursor = rootMiddle :=
    (Prod.mk.inj (Except.ok.inj (rootedReplay.symm.trans rootedStatements))).2
  have finalRooted : rpExpr final.source (.call target [] origin) final.rootCursor = .ok (roots, rootsAfter) := by
    rw [sourceSame, childSource, sameRoots]
    exact rootedTail
  obtain ⟨sameModule, sameRequests⟩ := typeStatements_scalarLocal_callContext form (fuel + 1)
    { blockFrame.typing with scope := scope } next blockFrame.typingCounter typingMiddle typedStatements
  have singleton := typeExpr_registerCall_tail_result fuel next target origin context callee [] ty typingMiddle typingAfter types
    (by simpa [sameModule] using contextAt) (by simpa [sameModule] using calleeAt) results scalar
    (by simpa [sameRequests] using requests) typedTail
  subst types
  refine ⟨roots, typingAfter, rootsAfter, ?_, finalRooted, available roots rootsAfter finalRooted⟩
  simpa [sameEnvironment, sameCounter] using typedTail

theorem execActivationBody_registerCall_afterStatements (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (ty : Ty) (target origin : Nat)
    (before middle : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : activation.channels = [.register ty])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (middleActs : before.nextAct ≤ middle.nextAct) (middleScopes : before.nextScope ≤ middle.nextScope)
    (inner : ∃ nextTypes nextLive nextAmbient,
      let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      let outcome := invokeCall fuel config environment target [] [.register ty] origin middle
      RootTypesExtend types nextTypes ∧ middle.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      middle.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some (.call target [] origin)⟩ before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True | .escape .. | .jump .. => False) := by
  let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
  have body := execActivationBody_register_call_tail fuel config activation scope statements before middle ty target origin channels normal
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, world, clear, result⟩ := inner
  cases execution : invokeCall fuel config environment target [] [.register ty] origin middle with
  | stop reason after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes world clear result
    rw [body, execution]
    exact ⟨nextTypes, nextLive, nextAmbient, extend, Nat.le_trans middleActs acts, Nat.le_trans middleScopes scopes, world, clear, trivial⟩
  | escape address carriers after | jump destination kind after =>
    simp only [environment] at execution
    simp [execution] at result
  | ok carriers after =>
    simp only [environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes world clear result
    obtain ⟨rfl, value, rfl, represented⟩ := result
    rw [body, execution]
    have released := world.releaseScope config initialized after nextAmbient nextTypes nextLive regions pending
      activation scope before.nextScope
    exact ⟨nextTypes, _, nextAmbient, extend, Nat.le_trans middleActs acts, Nat.le_trans middleScopes scopes, released,
      clear.releaseScope activation scope before.nextScope, rfl, value, rfl, represented⟩

#print axioms execActivationBody_registerCall_afterStatements
#print axioms ScalarLocalReplay.registerCall_tail_checked
#print axioms typeStatements_scalarLocal_callContext
end Goose.Proofs.ConstructionAcceptedExecution
