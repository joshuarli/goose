import Goose.Proofs.ConstructionAcceptedParameterCallAccess

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rpExpr_parameterCall_noParameter {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {before after : RState} {roots : List RootRef} {origin : Nat}
    (summary : Summary) (contextAt : env.mod.contexts[target]? = some context)
    (calleeAt : env.mod.impls[context.impl]? = some callee) (parameters : callee.params = #[parameter])
    (known : callee.summary = .known summary)
    (operandClear : ∀ middle operandRoots, rpExpr env expression before = .ok (operandRoots, middle) →
      NoParameterAccess middle.eff ∧ ∀ id, .param id ∉ rootsTargets operandRoots)
    (checked : rpExpr env (.call target [.byVal expression] origin) before = .ok (roots, after)) :
    NoParameterAccess after.eff := by
  obtain ⟨selected, actual, arguments, middle, selectedAt, actualAt, argumentChecked, contents⟩ :=
    rpExpr_call_argumentChecks checked
  have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans contextAt)
  subst selected
  have sameCallee : actual = callee := Option.some.inj (actualAt.symm.trans calleeAt)
  subst actual
  cases operand : rpExpr env expression before with
  | error error => simp [rpArgs, bind, StateT.bind, Except.bind, operand] at argumentChecked
  | ok pair =>
    obtain ⟨operandRoots, operandAfter⟩ := pair
    obtain ⟨operandEffects, operandRootsClear⟩ := operandClear operandAfter operandRoots operand
    have sameRoots := rpArgs_singleByValue_roots operand argumentChecked
    have argumentsClear : ∀ result, result ∈ arguments → ∀ id, .param id ∉ rootsTargets result := by
      rw [sameRoots]
      intro result member id
      simp only [List.mem_singleton] at member
      subst result
      exact operandRootsClear id
    have sameEffects := rpArgs_singleByValue_accessTargets operand argumentChecked
    have middleClear : NoParameterAccess middle.eff := by
      intro id member
      exact operandEffects id (by rw [← sameEffects]; exact member)
    exact rpExpr_singleByValue_noParameter summary contextAt calleeAt parameters known middleClear argumentsClear argumentChecked checked

#print axioms rpExpr_parameterCall_noParameter
end Goose.Proofs.ConstructionAcceptedExecution
