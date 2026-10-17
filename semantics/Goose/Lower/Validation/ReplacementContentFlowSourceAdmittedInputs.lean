import Goose.Lower.Validation.ReplacementContentFlowSourceCallAdmissions
import Goose.Lower.Validation.SummaryPreservationContentReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

theorem accepted_reference_argument_admission {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {index : Nat} {param : Param} {localVar : LocalVar}
    {caller : Func} {sourceArgs : List (List RootRef)} {argumentRoots : Nat → Option (List RootRef)}
    {actual : List RootRef}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (parameter : impl.params[index]? = some param)
    (variableRow : impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (checked : checkArgRoots impl ctx sourceArgs index = .ok ())
    (known : argumentRoots index = some actual) :
    ∃ upper, admittedArgumentBound (lowerContextAt module ctx impl) argumentRoots index = some upper ∧
      upper.covers (some ((sourceArgs[index]?.getD []).flatMap caller.expandParameterRoot)) = true := by
  obtain ⟨checkedVar, checkedRow, contract⟩ := checkArgRoots_ok impl ctx sourceArgs index param checked parameter
  rw [variableRow] at checkedRow
  cases checkedRow
  obtain ⟨declared, annotation, sourceWithin⟩ := contract reference
  have parameterType := lowerContext_parameter_type (module := module) (ctx := ctx) parameter variableRow
  have metadata := lowerContextRootInfo_parameter_eq parameter annotation
  change (lowerContextAt module ctx impl).roots.params.find? (·.1 == index) = some (index, declared) at metadata
  have roots := lowerContextAt_parameterRoots_eq (module := module) parameter annotation
  by_cases self : RootRef.param index ∈ declared
  · refine ⟨.callerStorage, ?_, ?_⟩
    · simp [admittedArgumentBound, parameterType, known, metadata, reference, self]
    · rfl
  · refine ⟨.roots (unionRoots actual (declared.filterMap fun
      | .global global => some (.global global)
      | _ => none)), ?_, ?_⟩
    · simp [admittedArgumentBound, parameterType, known, metadata, self]
      rfl
    · simp only [ContentInputBound.covers, Option.any_some]
      apply List.all_eq_true.mpr
      intro root member
      have permitted := accepted_call_argument_globals (caller := caller) accepted contextRow implementationRow
        (Array.getElem?_eq_some_iff.mp parameter).1 checked (by simpa [roots] using self) root member
      have closed := lowerContextAt_parameterRoots_closed accepted contextRow implementationRow
      rcases closed index root permitted with own | ⟨global, identity⟩
      · exact False.elim (self (by simpa only [roots, own] using permitted))
      · subst root
        apply List.contains_iff_mem.mpr
        apply unionRoots_right
        apply List.mem_filterMap.mpr
        exact ⟨.global global, by simpa [roots] using permitted, rfl⟩

#print axioms accepted_reference_argument_admission

theorem rpCall_reference_argument_admission {env : PEnv} {context : ContextId}
    {ctx : Context} {impl : Impl} {index : Nat} {param : Param} {localVar : LocalVar}
    {caller : Func} {sourceArgs : List (List RootRef)} {argumentRoots : Nat → Option (List RootRef)}
    {actual result : List RootRef} {before after : RState}
    (accepted : Core.validate env.mod = .ok ())
    (contextRow : env.mod.contexts[context]? = some ctx)
    (implementationRow : env.mod.impls[ctx.impl]? = some impl)
    (parameter : impl.params[index]? = some param)
    (variableRow : impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefLike = true)
    (replayed : rpCall env context sourceArgs before = .ok (result, after))
    (known : argumentRoots index = some actual) :
    ∃ upper, admittedArgumentBound (lowerContextAt env.mod ctx impl) argumentRoots index = some upper ∧
      upper.covers (some ((sourceArgs[index]?.getD []).flatMap caller.expandParameterRoot)) = true := by
  have contract := rpCall_replay_contract contextRow implementationRow replayed
  exact accepted_reference_argument_admission accepted contextRow implementationRow parameter variableRow reference
    ((forAll_ok _ _).mp contract.1 index
      (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp parameter).1)) known

#print axioms rpCall_reference_argument_admission

end Goose.Lower.Validation.ReplacementContentFlowSource
