import Goose.Proofs.ConstructionAcceptedInitializerUnknown

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem initializer_unknown_anyArgumentCall (config : EvalConfig) (names : Array (List RootRef)) (target : Nat)
    (context : Context) (callee : Impl) (argumentRoots : List (List RootRef)) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (unknown : callee.summary = .unknown)
    (checked : rpCall (initializerSource config names) target argumentRoots before = .ok (roots, after)) :
    after.eff.unknown = true := by
  unfold rpCall at checked
  simp only [initializerSource, contextAt, calleeAt, unknown] at checked
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, liftV] at checked
  repeat' first | split at checked | simp_all
  all_goals
    simp_all [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure, Except.pure, callEffects, unknown]
    rename_i argCheck argState invalidating invalidState scopedState scopeState checkedArgs argsState update updateState final finalState result resultValue argEq invalidEq scopeEq argsEq updateEq finalEq
    cases updateEq
    cases finalEq
    cases checked.2
    rfl

theorem initializer_unknown_anyArgumentCallExpr (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (arguments : List Arg) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (unknown : callee.summary = .unknown)
    (checked : rpExpr (initializerSource config names) (.call target arguments origin) before = .ok (roots, after)) :
    after.eff.unknown = true := by
  simp only [rpExpr, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, initializerSource,
    contextAt, calleeAt] at checked
  simp only [Array.getElem?_empty, Option.getD_none, List.any_nil, Bool.false_eq_true, if_false] at checked
  repeat' first | split at checked | simp_all
  all_goals exact initializer_unknown_anyArgumentCall config names target context callee _ _ after roots contextAt calleeAt unknown checked

theorem validated_scalar_initializer_anyCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (global : Global) (target origin : Nat) (context : Context) (callee : Impl) (arguments : List Arg)
    (present : config.module.globals[id]? = some global)
    (resultScalar : (∃ integer, global.ty = .int integer) ∨ global.ty = .bool)
    (expression : global.init = .call target arguments origin)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee) :
    ∃ summary, callee.summary = .known summary := by
  obtain ⟨names, roots, after, rooted, clear⟩ := validated_scalar_initializer_noUnknown config accepted id global present resultScalar
  rw [expression] at rooted
  cases summary : callee.summary with
  | known value => exact ⟨value, rfl⟩
  | unknown =>
    have raised := initializer_unknown_anyArgumentCallExpr config names target origin context callee arguments ⟨0, {}, []⟩ after roots
      contextAt calleeAt summary rooted
    simp [clear] at raised

#print axioms validated_scalar_initializer_anyCall_known
#print axioms initializer_unknown_anyArgumentCallExpr
#print axioms initializer_unknown_anyArgumentCall
end Goose.Proofs.ConstructionAcceptedExecution
