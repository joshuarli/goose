import Goose.Proofs.ConstructionAcceptedRecursiveArgumentCursor
import Goose.Proofs.ConstructionAcceptedNestedParameterCallEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem recursiveArgumentCall_noParameter {config : EvalConfig} {integer : Goose.Core.IntTy} {implementation : Impl}
    {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl} {parameter : Param}
    {argument : Expr} {before after : RState} {roots : List RootRef} {origin : Nat} (summary : Summary)
    (form : RecursiveArgumentExpression config integer implementation argument)
    (moduleEq : env.mod = config.module) (implementationEq : env.impl = implementation)
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary)
    (clear : NoParameterAccess before.eff)
    (checked : rpExpr env (.call target [.byVal argument] origin) before = .ok (roots, after)) : NoParameterAccess after.eff := by
  apply rpExpr_parameterCall_noParameter summary contextAt calleeAt parameters known
  · intro operandAfter operandRoots operand
    have facts := nestedParameterExpression_source form.toSource env before operandAfter operandRoots moduleEq implementationEq clear operand
    refine ⟨facts.2, ?_⟩
    intro id
    simp [facts.1, rootsTargets]
  · exact checked

theorem recursiveArgumentCallTail_noParameter (config : EvalConfig) (integer : Goose.Core.IntTy) (implementation : Impl)
    (source : PEnv) (scope target origin : Nat) (argument : Expr) (context : Context) (callee : Impl) (parameter : Param) (summary : Summary)
    (before after : RState) (result : List RootRef × (Nat × Nat))
    (form : RecursiveArgumentExpression config integer implementation argument)
    (moduleEq : source.mod = config.module) (implementationEq : source.impl = implementation)
    (contextAt : source.mod.contexts[target]? = some context) (calleeAt : source.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary) (clear : NoParameterAccess before.eff)
    (rooted : rpBlockValue source [] ⟨scope, [], some (.call target [.byVal argument] origin)⟩ before = .ok (result, after)) :
    NoParameterAccess after.eff := by
  obtain ⟨_, middle, roots, statements, tail, resultEq⟩ := rpBlockValue_body rooted
  simp only [List.length_nil, Nat.add_zero, rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statements
  cases statements.2
  exact recursiveArgumentCall_noParameter (env := { source with scopes := scope :: source.scopes }) summary form moduleEq implementationEq
    contextAt calleeAt parameters known clear (by simpa using tail)

#print axioms recursiveArgumentCallTail_noParameter
#print axioms recursiveArgumentCall_noParameter
end Goose.Proofs.ConstructionAcceptedExecution
