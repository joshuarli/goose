import Goose.Lower.Validation.SummaryPreservationParameters
import Goose.Lower.Validation.SummaryPreservationVariableShape

namespace Goose.Lower.Validation.AdmittedSourceInstructions

open Goose.Core Goose.Core.Sound Goose.GIR

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
  change ((lowerContextRootInfo context impl).contents.find? (·.1 == parameter)).isSome = true
  rw [native]
  rfl

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

theorem lowerGlobal_load_observed {module : Core.Module} {global : Core.Global} {index : Nat}
    (reference : (((lowerGlobal module global).init.params)[index]?).any Ty.isRefSlice = true) :
    (((lowerGlobal module global).init.roots.contents).find? (·.1 == index)).isSome = true := by
  simp [lowerGlobal] at reference

end Goose.Lower.Validation.AdmittedSourceInstructions
