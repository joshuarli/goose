import Goose.Lower.Validation.AdmittedSourceCallsTransport
import Goose.Lower.Validation.SummaryPreservationParameters

namespace Goose.Lower.Validation.AdmittedSourceCalls

open Goose.Core Goose.GIR

theorem lowerContextAt_content_row_source
    {module : Core.Module} {context : Context} {impl : Impl}
    {parameter : Nat} {declared : List RootRef}
    (row : (parameter, declared) ∈ (lowerContextAt module context impl).roots.contents.toList) :
    ∃ formal, impl.params[parameter]? = some formal ∧
      (context.contentRoots.find? (·.1 == formal.var)).map (·.2) = some declared := by
  change (parameter, declared) ∈ ((impl.params.toList.zipIdx.filterMap fun (formal, index) =>
    (context.contentRoots.find? (·.1 == formal.var)).map fun (_, roots) => (index, roots)).toArray).toList at row
  rw [List.toList_toArray] at row
  obtain ⟨⟨formal, index⟩, formalMember, selected⟩ := List.mem_filterMap.mp row
  have formalAt := List.mk_mem_zipIdx_iff_getElem?.mp formalMember
  cases found : context.contentRoots.find? (·.1 == formal.var) with
  | none => simp [found] at selected
  | some entry =>
    simp only [found, Option.map_some, Option.some.injEq] at selected
    cases selected
    exact ⟨formal, by simpa using formalAt, by simp [found]⟩

theorem checkContents_native_row_receiver_bounds
    {module : Core.Module} {contextId : ContextId} {context : Context} {impl : Impl}
    {env : PEnv} {arguments : List Arg} {argumentRoots : List (List RootRef)}
    {parameter : Nat} {declared : List RootRef}
    (accepted : Core.validate module = .ok ())
    (contextFound : module.contexts[contextId]? = some context)
    (implementationFound : module.impls[context.impl]? = some impl)
    (environment : env.mod = module)
    (checked : checkContents env contextId arguments argumentRoots = .ok ())
    (arity : arguments.length = impl.params.size)
    (row : (parameter, declared) ∈ (lowerContextAt module context impl).roots.contents.toList) :
    ∃ mapped, mapResultRoots argumentRoots [] declared = .ok mapped ∧
      ((∃ mutability slot ceiling,
        arguments[parameter]? = some (.byRef mutability (.var slot)) ∧
        env.ann slot = some ceiling ∧ mapped ⊆ ceiling ∧ ceiling ⊆ mapped) ∨
      (∃ mutability formal ceiling,
        arguments[parameter]? = some (.byRef mutability (.deref (.read (.var formal)))) ∧
        env.cont formal = some ceiling ∧ mapped ⊆ ceiling ∧ ceiling ⊆ mapped)) := by
  obtain ⟨formal, formalAt, annotation⟩ := lowerContextAt_content_row_source row
  have aligned : formal.var = parameter :=
    ((Core.Sound.validate_modOk module accepted).impl context.impl impl implementationFound |>.params
      parameter formal formalAt).1
  apply checkContents_receiver_bounds checked
    (by simpa only [environment] using contextFound)
    (by rw [arity]; exact (Array.getElem?_eq_some_iff.mp formalAt).1)
  simpa only [aligned] using annotation

end Goose.Lower.Validation.AdmittedSourceCalls
