import Goose.Proofs.ConstructionRootCorrespondenceScopes
import Goose.Proofs.ConstructionRepresentation

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation (ValueRepresentation)

private theorem represented_directReference_refLike (ty : Ty) (value : Value) (location : Goose.Core.Loc)
    (represented : ValueRepresentation ty value) (reference : DirectReference value location) :
    ty.isRefLike = true := by
  cases reference <;> cases represented <;> rfl

theorem checked_parameter_localValueRooted (module : Module) (caller : RootInterpretation)
    (callee : RuntimeActivation) (implementation : Impl) (context : Context)
    (arguments : List (List RootRef)) (index : Nat) (parameter : Param) (descriptor : LocalVar)
    (roots : List RootRef) (value : Value)
    (parameterAt : implementation.params[index]? = some parameter)
    (variableAt : implementation.vars[parameter.var]? = some descriptor)
    (parameterVariable : parameter.var = index)
    (checked : checkArgRoots implementation context arguments index = .ok ())
    (shaped : checkAnnotationShape module implementation context = .ok ())
    (argumentAt : arguments[index]? = some roots)
    (represented : ValueRepresentation descriptor.ty value)
    (rooted : DirectValueRooted caller roots value) :
    LocalValueRooted (CallInterpretation caller callee arguments) context parameter.var value := by
  intro location reference
  have refLike := represented_directReference_refLike descriptor.ty value location represented reference
  cases annotated : context.varRoots.find? (·.1 == parameter.var) with
  | none => simp [checkArgRoots, parameterAt, variableAt, refLike, annotated, Goose.Core.reject] at checked
  | some entry =>
    have sameId : entry.1 = parameter.var := by
      have selected := List.find?_some annotated
      simpa using selected
    obtain ⟨id, annotation⟩ := entry
    dsimp only at sameId
    subst id
    refine ⟨annotation, by simp only [Option.map_some], ?_⟩
    exact checkArgRoots_parameterValueRooted module caller callee implementation context arguments index parameter
      descriptor annotation roots value parameterAt variableAt parameterVariable refLike annotated checked shaped
      argumentAt rooted location reference

end Goose.Proofs.ConstructionRootCorrespondence
