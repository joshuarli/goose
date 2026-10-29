import Goose.Proofs.ConstructionAcceptedInitializerUnknown
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def callHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_call_checks" : tactic => do
  let scopedCheck := Lean.mkIdent (callHelperName "checkScopedShrinkAliases")
  let interior := Lean.mkIdent (callHelperName "interiorAliasType")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $scopedCheck $interior at *))

theorem initializer_unknown_zeroCall (config : EvalConfig) (names : Array (List RootRef)) (target : Nat)
    (context : Context) (callee : Impl) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (unknown : callee.summary = .unknown)
    (checked : rpCall (initializerSource config names) target [] before = .ok (roots, after)) :
    after.eff.unknown = true := by
  unfold rpCall at checked
  simp only [initializerSource, contextAt, calleeAt, parameters, unknown] at checked
  unfold_call_checks
  simp [initImpl, callEffects, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
    modify, get, liftV, Goose.Core.forAll, getThe, modifyGet, MonadStateOf.get, MonadStateOf.modifyGet, StateT.get, StateT.modifyGet, unknown] at checked
  cases result : callResultRoots callee context [] with
  | error failure => simp [result] at checked
  | ok value =>
    simp [result] at checked
    obtain ⟨_, rfl⟩ := checked
    rfl

theorem initializer_unknown_zeroCallExpr (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[]) (unknown : callee.summary = .unknown)
    (checked : rpExpr (initializerSource config names) (.call target [] origin) before = .ok (roots, after)) :
    after.eff.unknown = true := by
  simp only [rpExpr, rpArgs, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, initializerSource,
    contextAt, calleeAt, parameters] at checked
  simp [List.forIn_nil, liftV, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at checked
  cases contents : checkContents (initializerSource config names) target [] [] with
  | error failure =>
    simp only [initializerSource] at contents
    simp [contents] at checked
  | ok value =>
    simp only [initializerSource] at contents
    simp [contents] at checked
    exact initializer_unknown_zeroCall config names target context callee before after roots contextAt calleeAt parameters unknown checked

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
