import Goose.Lower.Validation.SummaryPreservationParameters
import Goose.Lower.Validation.SummaryPreservationVariableShape

namespace Goose.Lower.Validation.AdmittedSourceInstructions

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerContextAt_parameter_content_row
    {module : Core.Module} {context : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {parameter : VarId} {ceiling : List RootRef}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (implementationEq : env.impl = impl) (contextEq : env.ctx = context)
    (reference : env.isRefSliceVar parameter = true)
    (contents : env.cont parameter = some ceiling) :
    (lowerContextAt module context impl).roots.contents.find? (·.1 == parameter) =
      some (parameter, ceiling) := by
  obtain ⟨localVar, variableFound, variableReference⟩ :
      ∃ localVar, impl.vars[parameter]? = some localVar ∧ localVar.ty.isRefSlice = true := by
    cases found : env.impl.vars[parameter]? with
    | none => simp [PEnv.isRefSliceVar, found] at reference
    | some localVar =>
      exact ⟨localVar, by simpa only [implementationEq] using found,
        by simpa only [PEnv.isRefSliceVar, found] using reference⟩
  obtain ⟨formal, formalFound, formalVariable, formalMode⟩ :=
    SummaryPreservation.accepted_refSlice_parameter accepted implementationFound variableFound variableReference
  have annotation : (context.contentRoots.find? (·.1 == formal.var)).map (·.2) = some ceiling := by
    simpa only [PEnv.cont, contextEq, formalVariable] using contents
  have native := SummaryPreservation.lowerContextRootInfo_contents_eq formalFound annotation
  exact native

theorem lowerContextAt_parameter_content_observed
    {module : Core.Module} {context : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {parameter : VarId} {ceiling : List RootRef}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (implementationEq : env.impl = impl) (contextEq : env.ctx = context)
    (reference : env.isRefSliceVar parameter = true)
    (contents : env.cont parameter = some ceiling) :
    ((lowerContextAt module context impl).roots.contents.find? (·.1 == parameter)).isSome = true := by
  rw [lowerContextAt_parameter_content_row accepted implementationFound implementationEq
    contextEq reference contents]
  rfl

theorem lowerContextAt_read_parameter_observed
    {module : Core.Module} {context : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {parameter : VarId} {before after : RState} {sourceRoots : List RootRef}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (implementationEq : env.impl = impl) (contextEq : env.ctx = context)
    (reference : env.isRefSliceVar parameter = true)
    (source : rpExpr env (.read (.deref (.read (.var parameter)))) before =
      .ok (sourceRoots, after)) :
    ((lowerContextAt module context impl).roots.contents.find? (·.1 == parameter)).isSome = true := by
  have sourceCopy := source
  simp only [rpExpr] at sourceCopy
  obtain ⟨placeRoots, placeAfter, placeReplay, tail⟩ := (st_bind_ok _ _ _ _).mp sourceCopy
  obtain ⟨readUnit, readBefore, reads, readReplay⟩ := (st_bind_ok _ _ _ _).mp tail
  obtain ⟨ceiling, contents⟩ : ∃ ceiling, env.cont parameter = some ceiling := by
    cases found : env.cont parameter with
    | none =>
      simp only [readRoots, reference, found, ite_true] at readReplay
      inv at readReplay
    | some ceiling => exact ⟨ceiling, rfl⟩
  exact lowerContextAt_parameter_content_observed accepted implementationFound implementationEq
    contextEq reference contents

theorem lowerContextAt_read_parameter_observed_below
    {module : Core.Module} {context : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {parameter : VarId} {before after : RState} {sourceRoots : List RootRef}
    {provenance upper : Prov} {address : ValueId} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (implementationEq : env.impl = impl) (contextEq : env.ctx = context)
    (reference : env.isRefSliceVar parameter = true)
    (source : rpExpr env (.read (.deref (.read (.var parameter)))) before =
      .ok (sourceRoots, after))
    (physical : rootsAt upper.vals address = [.param parameter])
    (below : rootsAt provenance.vals address ⊆ rootsAt upper.vals address)
    (member : RootRef.param index ∈ rootsAt provenance.vals address) :
    ((lowerContextAt module context impl).roots.contents.find? (·.1 == index)).isSome = true := by
  have same : index = parameter := by
    have root := below member
    rw [physical] at root
    exact RootRef.param.inj (List.mem_singleton.mp root)
  subst index
  exact lowerContextAt_read_parameter_observed accepted implementationFound implementationEq contextEq
    reference source

theorem lowerContextAt_forwarded_parameter_observed
    {module : Core.Module} {context callee : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {parameter : VarId} {arguments : List Arg}
    {argumentRoots : List (List RootRef)} {index : Nat} {declared : List RootRef}
    {mutability : Mutability}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (implementationEq : env.impl = impl) (contextEq : env.ctx = context)
    (reference : env.isRefSliceVar parameter = true)
    (checked : checkContent env callee arguments argumentRoots index = .ok ())
    (row : (callee.contentRoots.find? (·.1 == index)).map (·.2) = some declared)
    (argument : arguments[index]? = some (.byRef mutability (.deref (.read (.var parameter))))) :
    ((lowerContextAt module context impl).roots.contents.find? (·.1 == parameter)).isSome = true := by
  obtain ⟨mapped, mappedChecked, localReceiver | parameterReceiver⟩ :=
    checkContent_ok env callee arguments argumentRoots index declared checked row
  · obtain ⟨otherMutability, slot, ceiling, otherArgument, rest⟩ := localReceiver
    rw [argument] at otherArgument
    cases otherArgument
  · obtain ⟨otherMutability, otherParameter, ceiling, otherArgument, contents, rest⟩ := parameterReceiver
    rw [argument] at otherArgument
    cases otherArgument
    exact lowerContextAt_parameter_content_observed accepted implementationFound implementationEq
      contextEq reference contents

theorem lowerContextAt_forwarded_parameter_observed_below
    {module : Core.Module} {context callee : Context} {impl : Impl} {implementation : ImplId}
    {env : PEnv} {parameter : VarId} {arguments : List Arg}
    {argumentRoots : List (List RootRef)} {index : Nat} {declared : List RootRef}
    {mutability : Mutability} {provenance upper : Prov} {address : ValueId} {rawParameter : Nat}
    (accepted : Core.validate module = .ok ())
    (implementationFound : module.impls[implementation]? = some impl)
    (implementationEq : env.impl = impl) (contextEq : env.ctx = context)
    (reference : env.isRefSliceVar parameter = true)
    (checked : checkContent env callee arguments argumentRoots index = .ok ())
    (row : (callee.contentRoots.find? (·.1 == index)).map (·.2) = some declared)
    (argument : arguments[index]? = some (.byRef mutability (.deref (.read (.var parameter)))))
    (physical : rootsAt upper.vals address = [.param parameter])
    (below : rootsAt provenance.vals address ⊆ rootsAt upper.vals address)
    (member : RootRef.param rawParameter ∈ rootsAt provenance.vals address) :
    ((lowerContextAt module context impl).roots.contents.find? (·.1 == rawParameter)).isSome = true := by
  have same : rawParameter = parameter := by
    have root := below member
    rw [physical] at root
    exact RootRef.param.inj (List.mem_singleton.mp root)
  subst rawParameter
  exact lowerContextAt_forwarded_parameter_observed accepted implementationFound implementationEq
    contextEq reference checked row argument

theorem lowerGlobal_load_observed {module : Core.Module} {global : Core.Global} {index : Nat}
    (reference : (((lowerGlobal module global).init.params)[index]?).any Ty.isRefSlice = true) :
    (((lowerGlobal module global).init.roots.contents).find? (·.1 == index)).isSome = true := by
  simp [lowerGlobal] at reference

end Goose.Lower.Validation.AdmittedSourceInstructions
