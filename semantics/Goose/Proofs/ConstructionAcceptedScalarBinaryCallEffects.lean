import Goose.Proofs.ConstructionAcceptedParameterCallAccess

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem scalarBinaryCall_noParameter {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {operation : Goose.Core.BinOp} {left right : Expr} {operandOrigin origin : Nat}
    {before after : RState} {roots : List RootRef} (summary : Summary)
    (form : AcceptedBinaryExpression (.bin operation left right operandOrigin))
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary)
    (clear : NoParameterAccess before.eff)
    (checked : rpExpr env (.call target [.byVal (.bin operation left right operandOrigin)] origin) before = .ok (roots, after)) :
    NoParameterAccess after.eff := by
  obtain ⟨selected, actual, arguments, middle, selectedAt, actualAt, argumentChecked, contents⟩ := rpExpr_call_argumentChecks checked
  have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextAt)
  subst selected
  have sameCallee : actual = callee := Option.some.inj (actualAt.symm.trans calleeAt)
  subst actual
  cases operand : rpExpr env (.bin operation left right operandOrigin) before with
  | error error => simp [rpArgs, bind, StateT.bind, Except.bind, operand] at argumentChecked
  | ok pair =>
    obtain ⟨operandRoots, operandAfter⟩ := pair
    have rootsEmpty := (rpExpr_bin_operands env operation left right operandOrigin before operandAfter operandRoots operand).1
    have argumentRoots := rpArgs_singleByValue_roots operand argumentChecked
    have argumentsClear : ∀ result, result ∈ arguments → ∀ id, .param id ∉ rootsTargets result := by
      rw [argumentRoots, rootsEmpty]
      simp [rootsTargets]
    have effectsSame := rpArgs_singleByValue_accessTargets operand argumentChecked
    have operandClear := recursiveScalar_noParameter form env before operandAfter operandRoots clear operand
    have middleClear : NoParameterAccess middle.eff := by
      intro id member
      exact operandClear id (by rw [← effectsSame]; exact member)
    exact rpExpr_singleByValue_noParameter summary contextAt calleeAt parameters known middleClear argumentsClear argumentChecked checked

theorem scalarBinaryCallTail_noParameter (source : PEnv) (scope target origin operandOrigin : Nat)
    (operation : Goose.Core.BinOp) (left right : Expr) (context : Context) (callee : Impl) (parameter : Param) (summary : Summary)
    (before after : RState) (result : List RootRef × (Nat × Nat))
    (form : AcceptedBinaryExpression (.bin operation left right operandOrigin))
    (contextAt : source.mod.contexts[target]? = some context) (calleeAt : source.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (known : callee.summary = .known summary) (clear : NoParameterAccess before.eff)
    (rooted : rpBlockValue source [] ⟨scope, [], some (.call target [.byVal (.bin operation left right operandOrigin)] origin)⟩ before = .ok (result, after)) :
    NoParameterAccess after.eff := by
  obtain ⟨_, middle, roots, statements, tail, resultEq⟩ := rpBlockValue_body rooted
  simp only [List.length_nil, Nat.add_zero, rpStmts, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at statements
  cases statements.2
  exact scalarBinaryCall_noParameter (env := { source with scopes := scope :: source.scopes }) summary form contextAt calleeAt parameters known clear (by simpa using tail)

#print axioms scalarBinaryCallTail_noParameter
#print axioms scalarBinaryCall_noParameter
end Goose.Proofs.ConstructionAcceptedExecution
