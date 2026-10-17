import Goose.Lower.Validation.SummaryPreservationArgumentAnnotations
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceLedger

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource

theorem ReplacementContentFlowSource.CallOccurrence.argument_checked
    {module : Core.Module} {context : ContextId} {ctx : Context} {impl : Impl}
    {env : PEnv} {root : DemandNode} {func : Func} {provenance upper : Prov}
    {value argument : ValueId} {arguments : List ValueId} {origin : Option OriginId} {index : Nat}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[context]? = some ctx)
    (implementationAt : module.impls[ctx.impl]? = some impl)
    (environment : env.mod = module)
    (occurrence : CallOccurrence env root func upper value context arguments origin)
    (parameterBound : index < impl.params.size)
    (reference : (tyOfVar impl (impl.params[index]'parameterBound).var).isRefLike = true)
    (argumentAt : arguments[index]? = some argument)
    (below : rootsAt provenance.vals argument ⊆ rootsAt upper.vals argument) :
    (let declared := (((lowerContextAt module ctx impl).roots.params.find? (·.1 == index)).map (·.2)).getD [];
      declared.contains (.param index) || (mapArgumentRoots func provenance argument index).all declared.contains) = true := by
  obtain ⟨localEnv, path, syntaxArgs, sourceOrigin, before, argumentRoots, argumentsAfter,
    resultRoots, after, access, originEq, node, argumentsReplay, contentChecked, callReplay,
    valueBound, valueRefined, argumentOrigins, _, _⟩ := occurrence
  obtain ⟨bound, roots, rootsAt, refined⟩ := argumentOrigins index argument argumentAt
  have moduleAt : localEnv.mod = module := (congrArg AccessEnv.mod access).trans environment
  have domain := accepted_call_argument_domain accepted contextAt implementationAt moduleAt
    parameterBound callReplay (by simpa only [rootsAt, Option.getD_some] using (GIR.RootsRefine.actual_mono refined below))
  have sourceContext : localEnv.mod.contexts[context]? = some ctx := by simpa only [moduleAt] using contextAt
  have sourceImpl : localEnv.mod.impls[ctx.impl]? = some impl := by simpa only [moduleAt] using implementationAt
  have checked := (rpCall_replay_contract sourceContext sourceImpl callReplay).1
  let parameter := impl.params[index]'parameterBound
  have parameterAt : impl.params[index]? = some parameter := Array.getElem?_eq_getElem parameterBound
  obtain ⟨localVar, variableAt, typeContract⟩ := Core.Sound.checkArgRoots_ok impl ctx argumentRoots index parameter
    ((Core.Sound.forAll_ok _ _).mp checked index (List.mem_range.mpr parameterBound)) parameterAt
  have variableRef : localVar.ty.isRefLike = true := by
    simpa only [tyOfVar, variableAt, Option.map_some, Option.getD_some, parameter] using reference
  obtain ⟨annotation, annotationAt, _⟩ := typeContract variableRef
  have nativeAt : (lowerContextAt module ctx impl).roots.params.find? (·.1 == index) = some (index, annotation) := by
    change (lowerContextRootInfo ctx impl).params.find? (·.1 == index) = _
    rw [lowerContextRootInfo_parameter_lookup parameterAt]
    cases found : ctx.varRoots.find? (·.1 == parameter.var) with
    | none => simp [found] at annotationAt
    | some row =>
      have same : row.2 = annotation := Option.some.inj (by simpa only [found, Option.map_some] using annotationAt)
      simp only [Option.map_some, same]
  simp only [Func.parameterRoots, nativeAt] at domain
  simp only [nativeAt, Option.map_some, Option.getD_some, Bool.or_eq_true]

  rcases domain with generic | contained
  · exact Or.inl (List.contains_iff_mem.mpr generic)
  · apply Or.inr
    exact List.all_eq_true.mpr (fun root member => List.contains_iff_mem.mpr (contained root member))

end Goose.Lower.Validation
