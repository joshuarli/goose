import Goose.Lower.Validation.ReplacementOccurrenceCallFootprint

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.Core.Sound SummaryPreservation ReplacementContentFlow.Model

theorem CallOccurrence.returned_atoms_apart_of_accepted {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    {env : PEnv} (environment : env.mod = module)
    (access : env.access = demand.planContext.approvals.access)
    {func callee : Func} {types : Array (Option VTy)} {provenance upper : Prov} {results : Array (List RootRef)}
    (native : FunctionCanonicalFacts (lower module) func types provenance results)
    {queries : ReplacementQueries} {owner value function : ValueId} {arguments : List ValueId}
    {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ func.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (calleeAt : (lower module).funcs[function]? = some callee)
    (occurrence : CallOccurrence env (.expression rhs) func upper value function arguments callOrigin)
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    {states : Array State} {effects current : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (effectsAt : states[function]? = some effects)
    {resultType : Ty} (result : callee.results = [resultType])
    (reference : resultType.isRefLike = true) (interior : wholeOwnerReference (.data resultType) = false)
    (argumentAtoms : ∀ argument ∈ arguments,
      (flowAt current.values argument).AtomsWithin (OwnerDependencyApart (lower module) func queries owner))
    (contents : ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content func current (flowAt current.values argument)).AtomsWithin
        (OwnerDependencyApart (lower module) func queries owner)) :
    (substitute func current arguments effects.returned).AtomsWithin
      (OwnerDependencyApart (lower module) func queries owner) := by
  have closure := (replacementContentFlow_model_checked statesModel).2.1
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
  obtain ⟨actual, actualAt, actualCanonical⟩ := canonical.1.2 function callee calleeAt
  have same : actual = effects := Option.some.inj (actualAt.symm.trans effectsAt)
  subst actual
  have actualTypes : ((lower module).funcs.map (·.valueTypes (lower module)))[function]?.getD #[] =
      callee.valueTypes (lower module) := by simp only [Array.getElem?_map, calleeAt, Option.map_some, Option.getD_some]
  simp only [actualTypes] at actualCanonical
  have calleeFacts := moduleFacts.functions function callee calleeAt
  have supported := canonical.2.1 function callee effects calleeAt effectsAt
  have footprint := accepted_module_touchFootprint accepted closure calleeAt effectsAt
  exact CallOccurrence.substitute_footprint_apart demand accepted environment access native member called calleeAt occurrence
    targetAt closed ownerKnown (footprint.returned resultType result interior) supported.returned
    (actualCanonical.returned resultType result reference).normalizableAtoms
    ((actualCanonical.returned resultType result reference).externalAtoms calleeFacts.roots.resultExternal)
    argumentAtoms contents

theorem CallOccurrence.touched_atoms_apart_of_accepted {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    {env : PEnv} (environment : env.mod = module)
    (access : env.access = demand.planContext.approvals.access)
    {func callee : Func} {types : Array (Option VTy)} {provenance upper : Prov} {results : Array (List RootRef)}
    (native : FunctionCanonicalFacts (lower module) func types provenance results)
    {queries : ReplacementQueries} {owner value function : ValueId} {arguments : List ValueId}
    {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ func.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (calleeAt : (lower module).funcs[function]? = some callee)
    (occurrence : CallOccurrence env (.expression rhs) func upper value function arguments callOrigin)
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    {states : Array State} {effects current : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (effectsAt : states[function]? = some effects)
    (argumentAtoms : ∀ argument ∈ arguments,
      (flowAt current.values argument).AtomsWithin (OwnerDependencyApart (lower module) func queries owner))
    (contents : ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content func current (flowAt current.values argument)).AtomsWithin
        (OwnerDependencyApart (lower module) func queries owner)) :
    (substitute func current arguments (publicTouches effects.touched)).AtomsWithin
      (OwnerDependencyApart (lower module) func queries owner) := by
  have closure := (replacementContentFlow_model_checked statesModel).2.1
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
  obtain ⟨actual, actualAt, actualCanonical⟩ := canonical.1.2 function callee calleeAt
  have same : actual = effects := Option.some.inj (actualAt.symm.trans effectsAt)
  subst actual
  have actualTypes : ((lower module).funcs.map (·.valueTypes (lower module)))[function]?.getD #[] =
      callee.valueTypes (lower module) := by simp only [Array.getElem?_map, calleeAt, Option.map_some, Option.getD_some]
  simp only [actualTypes] at actualCanonical
  have calleeFacts := moduleFacts.functions function callee calleeAt
  have supported := canonical.2.1 function callee effects calleeAt effectsAt
  have footprint := accepted_module_touchFootprint accepted closure calleeAt effectsAt
  have touchRows := close_touchRows moduleFacts annotations entries addresses closure function callee effects calleeAt effectsAt
  have publicFootprint := publicTouches_atomsWithin footprint.touched
  have publicRows := publicTouches_normalizableAtoms touchRows
  exact CallOccurrence.substitute_footprint_apart demand accepted environment access native member called calleeAt occurrence
    targetAt closed ownerKnown (publicFootprint.mono (fun atom bounded => bounded.1))
    (publicTouches_supported supported.touched) (publicRows.mono (fun atom bounded => bounded.1))
    (publicRows.mono (fun atom bounded => bounded.2)) argumentAtoms contents

theorem CallOccurrence.assigned_atoms_apart_of_accepted {module : Core.Module}
    {planOwner : Nat} {path : List Nat} {place : Place} {rhs : Expr} {origin : OriginId}
    (demand : ReplacementDemandContext module planOwner path place rhs origin)
    (accepted : Core.validate module = .ok ())
    {env : PEnv} (environment : env.mod = module)
    (access : env.access = demand.planContext.approvals.access)
    {func callee : Func} {types : Array (Option VTy)} {provenance upper : Prov} {results : Array (List RootRef)}
    (native : FunctionCanonicalFacts (lower module) func types provenance results)
    {queries : ReplacementQueries} {owner value function : ValueId} {arguments : List ValueId}
    {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ func.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (calleeAt : (lower module).funcs[function]? = some callee)
    (occurrence : CallOccurrence env (.expression rhs) func upper value function arguments callOrigin)
    {target : DemandOwner} (targetAt : demand.planContext.approvals.access.owner place = .ok target)
    (closed : ParameterRootsClosed func)
    (ownerKnown : ReplacementRootsWithin (queries.value owner) (target.roots.flatMap func.expandParameterRoot))
    {states : Array State} {effects current : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (effectsAt : states[function]? = some effects)
    {index : Nat} {raw : Roots} (bounded : index < callee.params.length)
    (writeAt : effects.writes[index]?.getD (.assigned .unknown) = .assigned raw)
    (argumentAtoms : ∀ argument ∈ arguments,
      (flowAt current.values argument).AtomsWithin (OwnerDependencyApart (lower module) func queries owner))
    (contents : ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content func current (flowAt current.values argument)).AtomsWithin
        (OwnerDependencyApart (lower module) func queries owner)) :
    (substitute func current arguments raw).AtomsWithin
      (OwnerDependencyApart (lower module) func queries owner) := by
  have closure := (replacementContentFlow_model_checked statesModel).2.1
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
  obtain ⟨actual, actualAt, actualCanonical⟩ := canonical.1.2 function callee calleeAt
  have same : actual = effects := Option.some.inj (actualAt.symm.trans effectsAt)
  subst actual
  have actualTypes : ((lower module).funcs.map (·.valueTypes (lower module)))[function]?.getD #[] =
      callee.valueTypes (lower module) := by simp only [Array.getElem?_map, calleeAt, Option.map_some, Option.getD_some]
  simp only [actualTypes] at actualCanonical
  have calleeFacts := moduleFacts.functions function callee calleeAt
  have supported := canonical.2.1 function callee effects calleeAt effectsAt
  have footprint := accepted_module_touchFootprint accepted closure calleeAt effectsAt
  have writeBound : index < effects.writes.size := by
    rw [actualCanonical.shape.writes]
    exact bounded
  have actualAt : effects.writes[index]? = some (.assigned raw) := by
    have present := Array.getElem?_eq_getElem writeBound
    rw [present] at writeAt ⊢
    exact congrArg some writeAt
  have symbolic := actualCanonical.memory.writes index writeBound
  simp only [writeAt, Write.SymbolicRefine] at symbolic
  exact CallOccurrence.substitute_footprint_apart demand accepted environment access native member called calleeAt occurrence
    targetAt closed ownerKnown (footprint.writes index raw actualAt)
    (supported.writes (.assigned raw) (by simpa using Array.mem_of_getElem? actualAt))
    symbolic.normalizableAtoms (symbolic.externalAtoms (calleeFacts.roots.contentExternal index)) argumentAtoms contents

#print axioms CallOccurrence.returned_atoms_apart_of_accepted
#print axioms CallOccurrence.touched_atoms_apart_of_accepted
#print axioms CallOccurrence.assigned_atoms_apart_of_accepted

end Goose.Lower.Validation.ReplacementContentFlowSource
