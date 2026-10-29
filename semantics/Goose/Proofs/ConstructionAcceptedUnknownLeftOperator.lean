import Goose.Proofs.ConstructionAcceptedUnknownOperators

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

inductive InitializerLiteral : Expr → Prop
  | integer (ty : Goose.Core.IntTy) (value : Int) : InitializerLiteral (.lit ty value)
  | boolean (value : Bool) : InitializerLiteral (.bool value)

theorem initializer_literal_roots (config : EvalConfig) (names : Array (List RootRef)) {expression : Expr}
    (form : InitializerLiteral expression) (before : RState) :
    rpExpr (initializerSource config names) expression before = .ok ([], before) := by
  cases form <;> rfl

def InitializerRetainsUnknown (config : EvalConfig) (names : Array (List RootRef)) (expression : Expr) : Prop :=
  ∀ before after roots, before.eff.unknown = true →
    rpExpr (initializerSource config names) expression before = .ok (roots, after) → after.eff.unknown = true

theorem initializer_literal_retainsUnknown (config : EvalConfig) (names : Array (List RootRef)) {expression : Expr}
    (form : InitializerLiteral expression) : InitializerRetainsUnknown config names expression := by
  intro before after roots unknown checked
  have literal := initializer_literal_roots config names form before
  rw [literal] at checked
  cases checked
  exact unknown

theorem initializer_unknown_leftSequence_retained (config : EvalConfig) (names : Array (List RootRef)) (left right : Expr)
    (leftUnknown : InitializerRaisesUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right)
    (before after : RState) (roots : List RootRef)
    (checked : (do let _ ← rpExpr (initializerSource config names) left
                   let _ ← rpExpr (initializerSource config names) right
                   pure []) before = .ok (roots, after)) : after.eff.unknown = true := by
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
  cases first : rpExpr (initializerSource config names) left before with
  | error failure => simp [first] at checked
  | ok pair =>
    obtain ⟨leftRoots, middle⟩ := pair
    have raised := leftUnknown before middle leftRoots first
    simp only [first] at checked
    cases second : rpExpr (initializerSource config names) right middle with
    | error failure => simp [second] at checked
    | ok pair =>
      obtain ⟨rightRoots, final⟩ := pair
      simp [second] at checked
      obtain ⟨_, rfl⟩ := checked
      exact rightRetains middle final rightRoots raised second

theorem initializer_unknown_cmpLeft (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.CmpOp)
    (left right : Expr) (leftUnknown : InitializerRaisesUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right) :
    InitializerRaisesUnknown config names (.cmp operation left right) := by
  intro before after roots checked
  exact initializer_unknown_leftSequence_retained config names left right leftUnknown rightRetains before after roots checked

theorem initializer_unknown_andLeft (config : EvalConfig) (names : Array (List RootRef))
    (left right : Expr) (leftUnknown : InitializerRaisesUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right) :
    InitializerRaisesUnknown config names (.and left right) := by
  intro before after roots checked
  exact initializer_unknown_leftSequence_retained config names left right leftUnknown rightRetains before after roots checked

theorem initializer_unknown_orLeft (config : EvalConfig) (names : Array (List RootRef))
    (left right : Expr) (leftUnknown : InitializerRaisesUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right) :
    InitializerRaisesUnknown config names (.or left right) := by
  intro before after roots checked
  exact initializer_unknown_leftSequence_retained config names left right leftUnknown rightRetains before after roots checked

theorem initializer_unknown_binaryLeft (config : EvalConfig) (names : Array (List RootRef)) (operation : Goose.Core.BinOp)
    (left right : Expr) (origin : Nat) (leftUnknown : InitializerRaisesUnknown config names left) (rightRetains : InitializerRetainsUnknown config names right) :
    InitializerRaisesUnknown config names (.bin operation left right origin) := by
  intro before after roots checked
  change (do let _ ← rpExpr (initializerSource config names) left
             let _ ← rpExpr (initializerSource config names) right
             if binOpMayAbort operation then noteAborts
             pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind] at checked
  cases first : rpExpr (initializerSource config names) left before with
  | error failure => simp [first] at checked
  | ok pair =>
    obtain ⟨leftRoots, middle⟩ := pair
    have raised := leftUnknown before middle leftRoots first
    simp only [first] at checked
    cases second : rpExpr (initializerSource config names) right middle with
    | error failure => simp [second] at checked
    | ok pair =>
      obtain ⟨rightRoots, final⟩ := pair
      have retained := rightRetains middle final rightRoots raised second
      cases aborts : binOpMayAbort operation <;>
        simp [second, aborts, noteAborts, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          pure, StateT.pure, Except.pure] at checked <;>
        obtain ⟨_, rfl⟩ := checked <;> simpa using retained

theorem validated_scalar_initializer_binaryLeft_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (operation : Goose.Core.BinOp) (left right : Expr) (location : Nat)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (expression : descriptor.init = .bin operation left right location)
    (leftForm : OperatorWrappedZeroCall target origin left) (literal : InitializerLiteral right)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id descriptor present scalar
  rw [expression] at rooted
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have leftUnknown := initializer_unknown_operatorWrappedZeroCall config names target origin context callee
      contextAt calleeAt parameters summary leftForm
    have retained := initializer_literal_retainsUnknown config names literal
    have raised := initializer_unknown_binaryLeft config names operation left right location leftUnknown retained ⟨0, {}, []⟩ after roots rooted
    simp [clear] at raised

#print axioms validated_scalar_initializer_binaryLeft_known
#print axioms initializer_literal_retainsUnknown
#print axioms initializer_unknown_binaryLeft
#print axioms initializer_unknown_cmpLeft
#print axioms initializer_unknown_andLeft
#print axioms initializer_unknown_orLeft
end Goose.Proofs.ConstructionAcceptedExecution
