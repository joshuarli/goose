import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts
import Goose.Lower.Validation.SourceSymbolAnnotationFacts
import Goose.Lower.Validation.SummaryPreservationEffects
import Goose.Lower.Validation.InterfaceTypes

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem indexed_annotation_unique (parameters : List Param)
    (annotation : Param → Option (Nat × List RootRef)) :
    ((parameters.zipIdx.filterMap fun (parameter, index) =>
      (annotation parameter).map fun (_, roots) => (index, roots)).map Prod.fst).Nodup := by
  have distinct : (parameters.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range' _
  have distinct' := List.pairwise_map.mp distinct
  apply List.pairwise_map.mpr
  apply distinct'.filterMap
  intro left right different first firstAt second secondAt
  obtain ⟨a, _, firstEq⟩ := Option.map_eq_some_iff.mp firstAt
  obtain ⟨b, _, secondEq⟩ := Option.map_eq_some_iff.mp secondAt
  cases firstEq
  cases secondEq
  exact different

private theorem result_not_holder {type : Ty} (readable : type.readable = true)
    (mu : Mutability) (payload : Ty) (same : type = .ref mu payload) : payload.isRefLike = false := by
  subst type
  exact readable_not_holder readable

private theorem context_parameter_ok {module : Core.Module} {impl : Core.Impl} {index : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[index]? = some impl)
    (type : Ty) (member : type ∈ impl.params.toList.map (tyOfVar impl ·.var)) : type.paramOk = true := by
  obtain ⟨parameter, parameterMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨position, parameterAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp parameterMember)
  obtain ⟨identity, localVar, localAt, _, parameterOk⟩ :=
    ((validate_modOk module accepted).impl index impl implAt).params position parameter parameterAt
  simpa only [tyOfVar, identity, localAt] using parameterOk

private theorem context_result_readable {module : Core.Module} {impl : Core.Impl} {index : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[index]? = some impl)
    (type : Ty) (member : type ∈ impl.results.toList) : type.readable = true := by
  have metadata := (checkImpl_metadata_checks (validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implAt)))).1
  have checked := (forAll_ok _ _).mp metadata type member
  by_cases readable : type.readable = true
  · exact readable
  · simp [readable, chk] at checked

theorem lowerContext_functionRootFacts_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : ContextId} {context : Context} {impl : Core.Impl}
    (contextAt : module.contexts[index]? = some context) (implAt : module.impls[context.impl]? = some impl) :
    FunctionRootFacts (lowerContextAt module context impl) := by
  have unique : (((lowerContextAt module context impl).roots.contents.toList).map Prod.fst).Nodup := by
    simpa only [lowerContextAt, lowerContextRootInfo, List.toList_toArray] using
      indexed_annotation_unique impl.params.toList (fun parameter => context.contentRoots.find? (·.1 == parameter.var))
  refine ⟨unique, SummaryPreservation.lowerContextAt_parameterRoots_closed accepted contextAt implAt, ?_, ?_, ?_, ?_, ?_⟩
  · exact context_parameter_ok accepted implAt
  · intro parameter slot member
    rw [contentRoots_find unique] at member
    cases found : (lowerContextAt module context impl).roots.contents.find? (·.1 == parameter) with
    | none => simp [found] at member
    | some row =>
      have external := (lowerContextAt_content_facts accepted contextAt implAt row.1 row.2
        (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))).2.2
      have localMember : RootRef.local slot ∈ row.2 := by simpa [found] using member
      exact external _ localMember
  · intro slot member
    cases row : (lowerContextAt module context impl).roots.results[0]? with
    | none => simp [row] at member
    | some roots =>
      have external := lowerContextAt_result_facts accepted contextAt implAt roots
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))
      exact external _ (by simpa [row] using member)
  · intro parameter ceiling found
    have facts := lowerContextAt_content_facts accepted contextAt implAt parameter ceiling
      (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
    rw [List.getElem?_eq_getElem facts.1]
    simpa only [Option.any_some, getElem!_def, List.getElem?_eq_getElem facts.1, Option.getD_some] using facts.2.1
  · intro type member mu payload same
    exact result_not_holder (context_result_readable accepted implAt type member) mu payload same

theorem lowerGlobal_functionRootFacts_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {index : GlobalId} {global : Core.Global}
    (globalAt : module.globals[index]? = some global) :
    FunctionRootFacts (lowerGlobal module global).init := by
  refine ⟨by simp [lowerGlobal], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro index root member
    exact Or.inl (by simpa [Func.parameterRoots, lowerGlobal] using member)
  · simp [lowerGlobal]
  · simp [Func.contentRoots, lowerGlobal]
  · simp [lowerGlobal]
  · simp [lowerGlobal]
  · intro type member mu payload same
    have actual : type = global.ty := by simpa [lowerGlobal] using member
    have scalar := ((validate_modOk module accepted).glob index global globalAt).ty.2
    have valueEq : global.ty = .ref mu payload := actual.symm.trans same
    rw [valueEq] at scalar
    cases scalar

#print axioms lowerContext_functionRootFacts_of_accepted

end Goose.Lower.Validation
