import Goose.Proofs.ConstructionRootCorrespondenceCursors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem call_byVal_argumentEffects {env : PEnv} {contextId : Nat} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {origin : Nat} {before after : RState} {roots : List RootRef}
    (contextAt : env.mod.contexts[contextId]? = some context)
    (calleeAt : env.mod.impls[context.impl]? = some callee) (parameters : callee.params = #[parameter])
    (checked : rpExpr env (.call contextId [.byVal expression] origin) before = .ok (roots, after)) :
    ∃ argumentRoots argumentAfter,
      rpExpr env expression before = .ok (argumentRoots, argumentAfter) ∧
      EffectTargetsIncluded argumentAfter.eff after.eff := by
  obtain ⟨selected, selectedCallee, allRoots, argsAfter, foundContext, foundCallee, argsChecked, contents⟩ :=
    rpExpr_call_argumentChecks checked
  have sameContext : selected = context := Option.some.inj (foundContext.symm.trans contextAt)
  subst selected
  have sameCallee : selectedCallee = callee := Option.some.inj (foundCallee.symm.trans calleeAt)
  subst selectedCallee
  have arg : ∃ argumentRoots argumentAfter, rpExpr env expression before = .ok (argumentRoots, argumentAfter) := by
    have args := argsChecked
    unfold rpArgs at args
    cases argumentChecked : rpExpr env expression before with
    | error failure => simp [argumentChecked, bind, StateT.bind, Except.bind] at args
    | ok pair => cases pair with | mk found foundAfter => exact ⟨found, foundAfter, rfl⟩
  obtain ⟨argumentRoots, argumentAfter, operand⟩ := arg
  have first := rpArgs_byVal_operandEffects operand argsChecked
  have second := rpExpr_call_argumentEffects contextAt calleeAt parameters argsChecked checked
  exact ⟨argumentRoots, argumentAfter, operand, first.trans second⟩

#print axioms rpArgs_byVal_operandEffects
#print axioms rpExpr_call_argumentEffects
#print axioms call_byVal_argumentEffects
end Goose.Proofs.ConstructionAcceptedExecution
