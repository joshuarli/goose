import Goose.Proofs.ConstructionAcceptedBinaryComplete
import Goose.Proofs.ConstructionAcceptedCalleeScope
import Goose.Proofs.ConstructionAcceptedScalarControl

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

theorem evalProduce_register_scalar {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (state : ExecutionState) (ty : Ty) :
    evalProduce (fuel + 1) config environment [.register ty] expression state =
      (do let value ← evalValue fuel config environment expression; pure [Carrier.register value]) state := by
  cases evaluated : evalValue fuel config environment expression state <;> cases form with
  | numeric form =>
    cases form with
    | scalar form =>
      cases form with
      | scalar form => cases form <;> simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
      | not form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
    | unary operation origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
    | conversion kind target origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | binary operation origin left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | comparison operation left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | conjunction left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | disjunction left right => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | not form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | unary operation origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]
  | conversion kind target origin form => simp [evalProduce, selectCompletionChannel, bind, pure, evaluated]

theorem completion_register_scalar {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (state : ExecutionState) (ty : Ty) :
    withCompletionChannels [.register ty] (expressionOrigin expression)
      (fun channels => evalProduce (fuel + 1) config environment channels expression) state =
      (do let value ← evalValue fuel config environment expression; pure [Carrier.register value]) state := by
  have produced := evalProduce_register_scalar form fuel config environment state ty
  cases evaluated : evalValue fuel config environment expression state <;>
    simp [withCompletionChannels, completionChannelSetup, materializeOwnedCarriers, bind, pure, produced, evaluated]

theorem execActivationBody_register_scalar_tail_withBindings {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation) (scope : Nat) (pre : List (Nat × Value)) (statements : List Stmt)
    (before boundState middle : ExecutionState) (ty : Ty) (channels : activation.channels = [.register ty])
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation scope before) = .ok () boundState)
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements boundState = .ok (.normal .unit) middle) :
    execActivationBody (fuel + 2) config activation pre ⟨scope, statements, some expression⟩ before =
      match evalValue fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression middle with
      | .ok value after => .ok [.register value] (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers (releaseScopeState activation scope before.nextScope after)
      | .jump target kind after => .jump target kind (releaseScopeState activation scope before.nextScope after) := by
  have tail := completion_register_scalar form fuel config
    { activation with scopes := (scope, before.nextScope) :: activation.scopes } middle ty
  simp only [ownershipResultScopeState, beq_iff_eq, channels] at bound
  simp only [channels] at normal tail ⊢
  cases evaluated : evalValue fuel config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes, channels := [.register ty] } expression middle <;>
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      channels, beq_iff_eq, bound, normal, tail, evaluated, releaseScope]

theorem execActivationBody_register_scalar_tail {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt)
    (before middle : ExecutionState) (ty : Ty) (channels : activation.channels = [.register ty])
    (normal : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle) :
    execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before =
      match evalValue fuel config { activation with scopes := (scope, before.nextScope) :: activation.scopes } expression middle with
      | .ok value after => .ok [.register value] (releaseScopeState activation scope before.nextScope after)
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers (releaseScopeState activation scope before.nextScope after)
      | .jump target kind after => .jump target kind (releaseScopeState activation scope before.nextScope after) := by
  exact execActivationBody_register_scalar_tail_withBindings form fuel config activation scope [] statements before
    (ownershipResultScopeState activation scope before) middle ty channels (by simp [bindAll, bind, pure]) normal

theorem execActivationBody_register_statements_stopped (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (expression : Expr)
    (before after : ExecutionState) (reason : Goose.Core.Stop)
    (stopped : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .stop reason after) :
    execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before = .stop reason after := by
  simp only [ownershipResultScopeState, beq_iff_eq] at stopped
  simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, stopped]

theorem checkedRegisterTail_activation_clocks {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (before middle : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (ty : Ty)
    (channels : activation.channels = [.register ty])
    (environment : frame.interpretation.environment =
      { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (normal : execStmts (fuel + 1) config frame.interpretation.environment statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (world : AcceptedWorld config frame.initialized middle ambient types live regions pending)
    (source : AcceptedFrame config accepted frame middle types) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    let after := Goose.Proofs.Exit.stepState (execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before)
    after.nextAct = middle.nextAct ∧ after.nextScope = middle.nextScope := by
  have result := evalValue_checked_binary_recursive form fuel config accepted frame middle ambient types live regions pending
    world source ty roots typingAfter rootsAfter checked
  have normal' : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle := by
    simpa only [environment] using normal
  have execution := execActivationBody_register_scalar_tail form fuel config activation scope statements before middle ty channels normal'
  rw [← environment] at execution
  dsimp only
  rw [execution]
  cases evaluated : evalValue fuel config frame.interpretation.environment expression middle with
  | ok value after | escape value carriers after | jump value kind after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    simp [Goose.Proofs.Exit.stepState, releaseScopeState]
  | stop reason after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    simp [Goose.Proofs.Exit.stepState]

#print axioms checkedRegisterTail_activation_clocks
theorem checkedRegisterTail_activation_world {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (activation : RuntimeActivation) (scope : Nat) (statements : List Stmt) (before middle : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (ty : Ty)
    (channels : activation.channels = [.register ty])
    (environment : frame.interpretation.environment =
      { activation with scopes := (scope, before.nextScope) :: activation.scopes })
    (normal : execStmts (fuel + 1) config frame.interpretation.environment statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle)
    (world : AcceptedWorld config frame.initialized middle ambient types live regions pending)
    (source : AcceptedFrame config accepted frame middle types) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    match execActivationBody (fuel + 2) config activation [] ⟨scope, statements, some expression⟩ before with
    | .stop _ after => AcceptedWorld config frame.initialized after ambient types live regions pending ∧
        FutureGlobalsClear config frame.initialized after
    | .ok carriers after => ∃ value, carriers = [.register value] ∧
        AcceptedValue config.layout types frame.interpretation middle ty roots value ∧
        AcceptedWorld config frame.initialized after ambient types
          (fun root => live root ∧ (Goose.Proofs.Exit.runtimeScopeRoots activation scope before.nextScope).contains root = false)
          regions pending ∧ FutureGlobalsClear config frame.initialized after
    | .escape .. | .jump .. => False := by
  have clear : FutureGlobalsClear config frame.initialized middle := source.futureGlobals
  have result := evalValue_checked_binary_recursive form fuel config accepted frame middle ambient types live regions pending
    world source ty roots typingAfter rootsAfter checked
  have normal' : execStmts (fuel + 1) config
      { activation with scopes := (scope, before.nextScope) :: activation.scopes } statements
      (ownershipResultScopeState activation scope before) = .ok (.normal .unit) middle := by
    simpa only [environment] using normal
  have execution := execActivationBody_register_scalar_tail form fuel config activation scope statements before middle ty channels normal'
  rw [← environment] at execution
  rw [execution]
  cases evaluated : evalValue fuel config frame.interpretation.environment expression middle with
  | ok value after =>
    have valid := result.2.1 value after evaluated
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    exact ⟨value, rfl, valid,
      world.releaseScope config frame.initialized middle ambient types live regions pending activation scope before.nextScope,
      clear.releaseScope activation scope before.nextScope⟩
  | stop reason after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at result
    have same := result.1
    subst after
    exact ⟨world, clear⟩
  | escape address carriers after =>
    exact ((evalValue_scalar_controlFree form fuel config frame.interpretation.environment).1 middle address carriers after evaluated).elim
  | jump target kind after =>
    exact ((evalValue_scalar_controlFree form fuel config frame.interpretation.environment).2 middle target kind after evaluated).elim

#print axioms checkedRegisterTail_activation_world
#print axioms execActivationBody_register_statements_stopped
#print axioms execActivationBody_register_scalar_tail_withBindings
#print axioms execActivationBody_register_scalar_tail
#print axioms evalProduce_register_scalar
#print axioms completion_register_scalar
end Goose.Proofs.ConstructionAcceptedExecution
