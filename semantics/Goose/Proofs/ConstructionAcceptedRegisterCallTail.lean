import Goose.Proofs.ConstructionAcceptedRegisterTail
import Goose.Proofs.ConstructionAcceptedRegisterCallExecution
import Goose.Proofs.ConstructionAcceptedRegisterCallTyping
import Goose.Proofs.ConstructionAcceptedScalarLocalPrefix

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

private theorem materialize_noTokens (origin : Nat) (carriers : List Carrier) (state : ExecutionState) :
    materializeOwnedCarriers origin [] carriers state = .ok carriers state := by
  induction carriers generalizing state with
  | nil => simp [materializeOwnedCarriers, pure]
  | cons carrier rest ih =>
    have tail := ih state
    simp only [materializeOwnedCarriers, List.contains_nil, Bool.false_eq_true, ↓reduceIte, pure] at tail
    cases carrier <;> simp [materializeOwnedCarriers, List.mapM_cons, bind, pure, tail]

theorem completion_register_call (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (state : ExecutionState) (ty : Ty) (target origin : Nat) :
    withCompletionChannels [.register ty] origin
      (fun channels => evalProduce (fuel + 1) config environment channels (.call target [] origin)) state =
      invokeCall fuel config environment target [] [.register ty] origin state := by
  cases executed : invokeCall fuel config environment target [] [.register ty] origin state <;>
    simp [withCompletionChannels, completionChannelSetup, evalProduce, selectCompletionChannel, materialize_noTokens, bind, pure, executed]

theorem execActivationBody_register_call_tail (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (before middle : ExecutionState)
    (ty : Ty) (target origin : Nat) (channels : activation.channels = [.register ty])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle) :
    execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some (.call target [] origin)⟩ before =
      match invokeCall fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes }
          target [] [.register ty] origin middle with
      | .ok values after => .ok values (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape destination carriers after => .escape destination carriers (releaseScopeState activation scope before.nextScope after)
      | .jump destination kind after => .jump destination kind (releaseScopeState activation scope before.nextScope after) := by
  have tail := completion_register_call fuel config
    { activation with scopes := (scope, before.nextScope) :: activation.scopes } middle ty target origin
  simp only [ownershipResultScopeState, beq_iff_eq, channels] at normal
  simp only [channels] at tail ⊢
  cases executed : invokeCall fuel config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes, channels := [.register ty] }
      target [] [.register ty] origin middle <;>
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll,
      channels, beq_iff_eq, normal, tail, executed, releaseScope, expressionOrigin]

theorem execActivationBody_empty_registerCall_compose (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (activation : RuntimeActivation) (scope : Nat) (ty : Ty) (target origin : Nat) (before : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (channels : activation.channels = [.register ty])
    (inner : ∃ nextTypes nextLive nextAmbient,
      let scopedState := ownershipResultScopeState activation scope before
      let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
      let outcome := invokeCall fuel config environment target [] [.register ty] origin scopedState
      RootTypesExtend types nextTypes ∧ scopedState.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      scopedState.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False)) :
    ∃ nextTypes nextLive nextAmbient,
      let outcome := execActivationBody (fuel + 2) config activation [] ⟨scope, [], some (.call target [] origin)⟩ before
      RootTypesExtend types nextTypes ∧ before.nextAct ≤ (Goose.Proofs.Exit.stepState outcome).nextAct ∧
      before.nextScope ≤ (Goose.Proofs.Exit.stepState outcome).nextScope ∧
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) nextAmbient nextTypes nextLive regions pending ∧
      FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState outcome) ∧
      (match outcome with
       | .ok carriers _ => nextAmbient = ambient ∧ ∃ value, carriers = [.register value] ∧ ValueRepresentation ty value
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  let scopedState := ownershipResultScopeState activation scope before
  let environment := { activation with scopes := (scope, before.nextScope) :: activation.scopes }
  have normal : execStmts (fuel + 1) config environment [] scopedState = .ok (.normal .unit) scopedState := by
    simp [execStmts, pure]
  have body := execActivationBody_register_call_tail fuel config activation scope [] before scopedState ty target origin channels normal
  obtain ⟨nextTypes, nextLive, nextAmbient, extend, acts, scopes, world, clear, result⟩ := inner
  cases execution : invokeCall fuel config environment target [] [.register ty] origin scopedState with
  | stop reason after =>
    simp only [scopedState, environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes world clear result
    rw [body, execution]
    exact ⟨nextTypes, nextLive, nextAmbient, extend, acts, Nat.le_trans (Nat.le_succ _) scopes, world, clear, trivial⟩
  | escape address carriers after | jump destination kind after =>
    simp only [scopedState, environment] at execution
    simp [execution] at result
  | ok carriers after =>
    simp only [scopedState, environment] at execution
    simp only [execution, Goose.Proofs.Exit.stepState] at acts scopes world clear result
    obtain ⟨rfl, value, rfl, represented⟩ := result
    rw [body, execution]
    have released := world.releaseScope config initialized after nextAmbient nextTypes nextLive regions pending
      activation scope before.nextScope
    exact ⟨nextTypes, _, nextAmbient, extend, acts, Nat.le_trans (Nat.le_succ _) scopes, released,
      clear.releaseScope activation scope before.nextScope, rfl, value, rfl, represented⟩

#print axioms execActivationBody_empty_registerCall_compose
theorem SourcePosition.emptyBlock_registerCall_checked {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope fuel target origin : Nat) (context : Context) (callee : Impl) (ty : Ty)
    (position : SourcePosition accepted frame (.block ⟨scope, [], some (.call target [] origin)⟩))
    (nesting : frame.typingFuel = fuel + 1) (contextAt : frame.typing.module.contexts[target]? = some context)
    (calleeAt : frame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : frame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue frame.source [] ⟨scope, [], some (.call target [] origin)⟩ frame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue { frame with typingFuel := fuel, typing := { frame.typing with scope := scope }, source := { frame.source with scopes := scope :: frame.source.scopes } }
        (.call target [] origin) ty roots typingAfter rootsAfter := by
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    _, statementsTyped, statementsRooted, tailTyped, tailRooted⟩ :=
    position.blockTail_checks accepted frame scope fuel [] (.call target [] origin) nesting
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at statementsTyped; cases statementsTyped
  | succ fuel =>
    simp only [typeStatements, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statementsTyped
    obtain ⟨rfl, rfl⟩ := statementsTyped
    simp only [rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statementsRooted
    cases statementsRooted.2
    have singleton := typeExpr_registerCall_tail_result fuel { frame.typing with scope := scope } target origin context callee [] ty
      frame.typingCounter typingAfter types contextAt calleeAt results scalar requests tailTyped
    subst types
    obtain ⟨middle, otherRoots, final, sameStatements, sameTail, _, finalAvailable⟩ :=
      position.blockTail_effects accepted frame scope [] (.call target [] origin) available
    have sameMiddle : middle = frame.rootCursor := by
      simp only [rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at sameStatements
      exact sameStatements.2.symm
    subst middle
    have sameFinal : rootsAfter = final := (Prod.mk.inj (Except.ok.inj (tailRooted.symm.trans sameTail))).2
    subst final
    exact ⟨roots, typingAfter, rootsAfter, tailTyped, tailRooted, finalAvailable⟩

#print axioms SourcePosition.emptyBlock_registerCall_checked
#print axioms completion_register_call
#print axioms execActivationBody_register_call_tail
end Goose.Proofs.ConstructionAcceptedExecution
