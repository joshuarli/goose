import Goose.Proofs.ConstructionAcceptedUnknownAnyArguments

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem initializer_unknown_zeroCall (config : EvalConfig) (names : Array (List RootRef)) (target : Nat)
    (context : Context) (callee : Impl) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (unknown : callee.summary = .unknown)
    (checked : rpCall (initializerSource config names) target [] before = .ok (roots, after)) :
    after.eff.unknown = true := by
  exact initializer_unknown_anyArgumentCall config names target context callee [] before after roots contextAt calleeAt unknown checked

theorem initializer_unknown_zeroCallExpr (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (unknown : callee.summary = .unknown)
    (checked : rpExpr (initializerSource config names) (.call target [] origin) before = .ok (roots, after)) :
    after.eff.unknown = true := by
  exact initializer_unknown_anyArgumentCallExpr config names target origin context callee [] before after roots contextAt calleeAt unknown checked

theorem initializer_unknown_not (config : EvalConfig) (names : Array (List RootRef)) (expression : Expr)
    (before after : RState) (roots : List RootRef)
    (childUnknown : ∀ childRoots middle, rpExpr (initializerSource config names) expression before = .ok (childRoots, middle) →
      middle.eff.unknown = true)
    (checked : rpExpr (initializerSource config names) (.not expression) before = .ok (roots, after)) :
    after.eff.unknown = true := by
  change (do let _ ← rpExpr (initializerSource config names) expression; pure []) before = .ok (roots, after) at checked
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
  cases child : rpExpr (initializerSource config names) expression before with
  | error failure => simp [child] at checked
  | ok pair =>
    obtain ⟨childRoots, middle⟩ := pair
    simp [child] at checked
    obtain ⟨_, rfl⟩ := checked
    exact childUnknown childRoots middle child

inductive NotWrappedZeroCall (target origin : Nat) : Expr → Prop
  | call : NotWrappedZeroCall target origin (.call target [] origin)
  | not {expression : Expr} : NotWrappedZeroCall target origin expression → NotWrappedZeroCall target origin (.not expression)

theorem initializer_unknown_notWrappedZeroCall (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (unknown : callee.summary = .unknown) :
    ∀ {expression}, NotWrappedZeroCall target origin expression → ∀ before after roots,
      rpExpr (initializerSource config names) expression before = .ok (roots, after) → after.eff.unknown = true := by
  intro expression form
  induction form with
  | call =>
    intro before after roots checked
    exact initializer_unknown_zeroCallExpr config names target origin context callee before after roots contextAt calleeAt parameters unknown checked
  | not inner ih =>
    intro before after roots checked
    exact initializer_unknown_not config names _ before after roots (fun childRoots middle child => ih before middle childRoots child) checked

#print axioms initializer_unknown_notWrappedZeroCall
#print axioms initializer_unknown_not

theorem validated_scalar_initializer_notWrappedZeroCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (form : NotWrappedZeroCall target origin descriptor.init)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id descriptor present scalar
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have raised := initializer_unknown_notWrappedZeroCall config names target origin context callee contextAt calleeAt parameters summary form
      ⟨0, {}, []⟩ after roots rooted
    simp [clear] at raised


theorem validated_scalar_initializer_zeroCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (present : config.module.globals[id]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool)
    (expression : descriptor.init = .call target [] origin)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) : ∃ summary, callee.summary = .known summary := by
  apply validated_scalar_initializer_notWrappedZeroCall_known config accepted id descriptor target origin context callee present scalar
  · rw [expression]
    exact .call
  · exact contextAt
  · exact calleeAt
  · exact parameters

#print axioms validated_scalar_initializer_notWrappedZeroCall_known
#print axioms validated_scalar_initializer_zeroCall_known
#print axioms initializer_unknown_zeroCallExpr
#print axioms initializer_unknown_zeroCall
end Goose.Proofs.ConstructionAcceptedExecution
