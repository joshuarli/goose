import Goose.Proofs.ConstructionAcceptedUnknownCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem initializer_unknown_scalarArgumentCall (config : EvalConfig) (names : Array (List RootRef)) (target : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argumentRoots : List RootRef) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) (unknown : callee.summary = .unknown)
    (checked : rpCall (initializerSource config names) target [argumentRoots] before = .ok (roots, after)) :
    after.eff.unknown = true := by
  exact initializer_unknown_anyArgumentCall config names target context callee [argumentRoots] before after roots contextAt calleeAt unknown checked

theorem initializer_unknown_scalarArgumentCallExpr (config : EvalConfig) (names : Array (List RootRef)) (target origin : Nat)
    (context : Context) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (argument : Expr) (before after : RState) (roots : List RootRef)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) (unknown : callee.summary = .unknown)
    (checked : rpExpr (initializerSource config names) (.call target [.byVal argument] origin) before = .ok (roots, after)) :
    after.eff.unknown = true := by
  exact initializer_unknown_anyArgumentCallExpr config names target origin context callee [.byVal argument] before after roots
    contextAt calleeAt unknown checked

theorem validated_scalar_initializer_scalarArgumentCall_known (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (global : Global) (target origin : Nat) (context : Context) (callee : Impl)
    (parameter : Param) (descriptor : LocalVar) (argument : Expr)
    (present : config.module.globals[id]? = some global)
    (resultScalar : (∃ resultInteger, global.ty = .int resultInteger) ∨ global.ty = .bool)
    (expression : global.init = .call target [.byVal argument] origin)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ integer, descriptor.ty = .int integer) ∨ descriptor.ty = .bool) : ∃ summary, callee.summary = .known summary := by
  exact validated_scalar_initializer_anyCall_known config accepted id global target origin context callee [.byVal argument]
    present resultScalar expression contextAt calleeAt

#print axioms validated_scalar_initializer_scalarArgumentCall_known
#print axioms initializer_unknown_scalarArgumentCallExpr
#print axioms initializer_unknown_scalarArgumentCall
end Goose.Proofs.ConstructionAcceptedExecution
