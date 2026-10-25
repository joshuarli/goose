import Goose.Lower.Validation.SummaryPreservationCallSource
import Goose.Lower.Validation.SummaryPreservationCalls
import Goose.Lower.Validation.SummaryPreservationCallEffects
import Goose.Lower.Validation.SummaryPreservationRootRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem mapArgumentRoots_parameter_domain {caller callee : Func} {provenance : Prov}
    {source : List RootRef} {value : ValueId} {index : Nat}
    (closed : ParameterRootsClosed callee)
    (contract : callee.parameterRoots index = [.param index] ∨
      ∀ root ∈ source, root ∈ callee.parameterRoots index)
    (refined : RootsRefine caller (rootsAt provenance.vals value) source) :
    RootRef.param index ∈ callee.parameterRoots index ∨
      ∀ root ∈ mapArgumentRoots caller provenance value index, root ∈ callee.parameterRoots index := by
  classical
  by_cases generic : RootRef.param index ∈ callee.parameterRoots index
  · exact Or.inl generic
  · right
    have subset : ∀ root ∈ source, root ∈ callee.parameterRoots index := by
      rcases contract with singleton | subset
      · exact False.elim (generic (by simp [singleton]))
      · exact subset
    have globalSource : ∀ root ∈ source, ∃ global, root = .global global := by
      intro root member
      rcases closed index root (subset root member) with own | global
      · subst root
        exact False.elim (generic (subset _ member))
      · exact global
    have expanded : ∀ root ∈ rootsAt provenance.vals value,
        ∀ concrete ∈ caller.expandParameterRoot root, concrete ∈ source := by
      intro root member concrete concreteMember
      rcases refined root member with literal | expanded
      · obtain ⟨global, rfl⟩ := globalSource root literal
        have same : concrete = .global global := List.mem_singleton.mp concreteMember
        simpa only [same] using literal
      · exact expanded concrete concreteMember
    intro root member
    have mapped := (mem_union_singletons_fold.mp member).resolve_left (by simp)
    obtain ⟨raw, rawMember, rawMapped⟩ := List.mem_flatMap.mp mapped
    cases raw with
    | «local» slot =>
      have sourceMember := expanded (.local slot) rawMember (.local slot) (by simp [Func.expandParameterRoot])
      obtain ⟨global, impossible⟩ := globalSource _ sourceMember
      cases impossible
    | global global =>
      have same : root = .global global := List.mem_singleton.mp rawMapped
      subst root
      exact subset _ (expanded _ rawMember _ (by simp [Func.expandParameterRoot]))
    | param parameter =>
      obtain ⟨concrete, concreteMember, same⟩ := List.mem_map.mp rawMapped
      have sourceMember := expanded (.param parameter) rawMember concrete concreteMember
      obtain ⟨global, rfl⟩ := globalSource concrete sourceMember
      simp only at same
      subst root
      exact subset _ sourceMember

theorem accepted_call_argument_domain {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {env : PEnv} {caller : Func} {provenance : Prov}
    {sourceArgs : List (List RootRef)} {index : Nat} {value : ValueId}
    {before after : RState} {roots : List RootRef}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (environment : env.mod = module)
    (bound : index < impl.params.size)
    (replayed : rpCall env context sourceArgs before = .ok (roots, after))
    (refined : RootsRefine caller (rootsAt provenance.vals value) (sourceArgs[index]?.getD [])) :
    RootRef.param index ∈ (lowerContextAt module ctx impl).parameterRoots index ∨
      ∀ root ∈ mapArgumentRoots caller provenance value index,
        root ∈ (lowerContextAt module ctx impl).parameterRoots index := by
  have source := rpCall_replay_contract (by simpa only [environment] using contextRow)
    (by simpa only [environment] using implementationRow) replayed
  apply mapArgumentRoots_parameter_domain
    (lowerContextAt_parameterRoots_closed accepted contextRow implementationRow)
    (checkArgRoots_parameterContract accepted contextRow implementationRow bound
      ((forAll_ok _ _).mp source.1 index (List.mem_range.mpr bound))) refined

#print axioms accepted_call_argument_domain

#print axioms mapArgumentRoots_parameter_domain

end Goose.Lower.Validation.SummaryPreservation
