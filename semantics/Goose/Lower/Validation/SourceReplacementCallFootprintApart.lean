import Goose.Lower.Validation.SourceReplacementRawCallApart
import Goose.Lower.Validation.SourceReplacementCurrentCallArguments
import Goose.Lower.Validation.SourceCallFootprintApart

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem site_call_returned_apart_of_contents {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) upper
      value function arguments callOrigin)
    {states : Array State} {final : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final)
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    (notLeaf : ¬ ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper value)
    {current : State} (growth : current.Extends final)
    (within : current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    (contents : ∀ callee, (lower module).funcs[function]? = some callee →
      ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content (lowerContextAt module context impl) current (flowAt current.values argument)).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner)) :
    (callState (lower module) states (lowerContextAt module context impl) current function arguments).1.AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) := by
  have native := (lowerContext_canonical_facts_of_accepted accepted contextAt implAt)
  obtain ⟨callSite⟩ := native.calls block member value function arguments callOrigin called
  obtain ⟨target, targetAt, ownerBound⟩ := site_owner_query_of_accepted accepted contextAt implAt site demand below
  have argumentAtoms := site_current_call_arguments_apart accepted contextAt implAt site member called ⟨chosen.1, chosen.2.1⟩ finalModel growth within
  have closure := (replacementContentFlow_model_checked statesModel).2.1
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
  obtain ⟨effects, effectsAt, _⟩ := canonical.1.2 function callSite.callee callSite.calleeAt
  rw [callState_result _ _ _ _ _ _ _ _ callSite.calleeAt effectsAt]
  obtain ⟨type, typeAt, carrier⟩ := ScopedOrigin.call_nonleaf_carrier (func := lowerContextAt module context impl)
    (types := (lowerContextAt module context impl).valueTypes (lower module))
    ((lowerImpl_dense_definitions module impl).nodup_iff.mpr List.nodup_range) member called chosen notLeaf
  rcases native.callResults block member value function arguments callOrigin called callSite.callee callSite.calleeAt with
    ⟨empty, unit⟩ | ⟨resultType, result, resultAt⟩
  · cases carrier <;> rw [unit] at typeAt <;> cases typeAt
  · have same : type = .data resultType := Option.some.inj (Option.some.inj (typeAt.symm.trans resultAt))
    subst type
    cases carrier with
    | slice mutability element =>
      exact CallOccurrence.returned_atoms_apart_of_accepted demand accepted (congrArg AccessEnv.mod site.access)
        (site.access.trans (demand.access_context contextAt implAt).symm) native member called callSite.calleeAt occurrence targetAt (lowerContextAt_parameterRoots_closed accepted contextAt implAt) ownerBound
        statesModel effectsAt result rfl rfl argumentAtoms (contents callSite.callee callSite.calleeAt)

theorem site_call_touched_apart_of_contents {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) upper
      value function arguments callOrigin)
    {states : Array State} {final : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final)
    {effects : State} (effectsAt : states[function]? = some effects)
    (argumentApart : ∀ argument ∈ arguments, ReplacementApart (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner ((replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).ownerDependencies argument))
    (contents : ∀ callee, (lower module).funcs[function]? = some callee →
      ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content (lowerContextAt module context impl) final (flowAt final.values argument)).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner)) :
    (substitute (lowerContextAt module context impl) final arguments (publicTouches effects.touched)).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) := by
  have native := (lowerContext_canonical_facts_of_accepted accepted contextAt implAt)
  obtain ⟨callSite⟩ := native.calls block member value function arguments callOrigin called
  obtain ⟨target, targetAt, ownerBound⟩ := site_owner_query_of_accepted accepted contextAt implAt site demand below
  have argumentAtoms : ∀ argument ∈ arguments, (flowAt final.values argument).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) := by
    intro argument argumentMember
    have bound := (lowerContextAt_operand_bounds module context impl).1 block member
      (.def value (.call function arguments callOrigin)) called argument argumentMember
    obtain ⟨roots, valueAt⟩ := accepted_context_factory_operand_value accepted contextAt implAt member called argumentMember
    obtain ⟨dependencies, dependenciesAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueAt
    rw [ReplacementFunctionFlow.ownerDependencies_model, finalModel] at dependenciesAt
    have apart := argumentApart argument argumentMember
    rw [replacementQueries_ownerDependencies _ _ _ _ bound,
      ReplacementFunctionFlow.ownerDependencies_model, finalModel] at apart
    simp only [Option.bind_some] at dependenciesAt apart
    rw [dependenciesAt] at apart
    exact ownerDependencies_atoms_apart dependenciesAt apart
  exact CallOccurrence.touched_atoms_apart_of_accepted demand accepted (congrArg AccessEnv.mod site.access)
    (site.access.trans (demand.access_context contextAt implAt).symm) native member called callSite.calleeAt occurrence targetAt (lowerContextAt_parameterRoots_closed accepted contextAt implAt) ownerBound
    statesModel effectsAt argumentAtoms (contents callSite.callee callSite.calleeAt)

theorem site_global_call_returned_apart_of_contents {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init upper
      value function arguments callOrigin)
    {states : Array State} {final : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final)
    (chosen : ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size value)
    (notLeaf : ¬ ScopedDemandLeaf site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper value)
    {current : State} (growth : current.Extends final)
    (within : current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner))
    (contents : ∀ callee, (lower module).funcs[function]? = some callee →
      ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content (lowerGlobal module global).init current (flowAt current.values argument)).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner)) :
    (callState (lower module) states (lowerGlobal module global).init current function arguments).1.AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) := by
  have native := (lowerGlobal_canonical_facts_of_accepted accepted globalAt)
  obtain ⟨callSite⟩ := native.calls block member value function arguments callOrigin called
  obtain ⟨target, targetAt, ownerBound⟩ := site_global_owner_query_of_accepted accepted globalAt site demand below
  have argumentAtoms := site_global_current_call_arguments_apart accepted globalAt site member called ⟨chosen.1, chosen.2.1⟩ finalModel growth within
  have closure := (replacementContentFlow_model_checked statesModel).2.1
  obtain ⟨annotations, entries, addresses⟩ := lower_canonical_factory_structure_of_accepted accepted
  have moduleFacts := lower_canonical_facts_of_accepted accepted
  have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
  obtain ⟨effects, effectsAt, _⟩ := canonical.1.2 function callSite.callee callSite.calleeAt
  rw [callState_result _ _ _ _ _ _ _ _ callSite.calleeAt effectsAt]
  obtain ⟨type, typeAt, carrier⟩ := ScopedOrigin.call_nonleaf_carrier (func := (lowerGlobal module global).init)
    (types := (lowerGlobal module global).init.valueTypes (lower module))
    ((lowerGlobal_dense_definitions module global).nodup_iff.mpr List.nodup_range) member called chosen notLeaf
  rcases native.callResults block member value function arguments callOrigin called callSite.callee callSite.calleeAt with
    ⟨empty, unit⟩ | ⟨resultType, result, resultAt⟩
  · cases carrier <;> rw [unit] at typeAt <;> cases typeAt
  · have same : type = .data resultType := Option.some.inj (Option.some.inj (typeAt.symm.trans resultAt))
    subst type
    cases carrier with
    | slice mutability element =>
      exact CallOccurrence.returned_atoms_apart_of_accepted demand accepted (congrArg AccessEnv.mod site.access)
        (site.access.trans demand.access_global.symm) native member called callSite.calleeAt occurrence targetAt (global_initializer_parameterRoots_closed module global) ownerBound
        statesModel effectsAt result rfl rfl argumentAtoms (contents callSite.callee callSite.calleeAt)

theorem site_global_call_touched_apart_of_contents {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init upper
      value function arguments callOrigin)
    {states : Array State} {final : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final)
    {effects : State} (effectsAt : states[function]? = some effects)
    (argumentApart : ∀ argument ∈ arguments, ReplacementApart (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner ((replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).ownerDependencies argument))
    (contents : ∀ callee, (lower module).funcs[function]? = some callee →
      ∀ (index : Nat), (callee.roots.contents.find? (·.1 == index)).isSome = true →
      (callee.params[index]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[index]? = some argument →
      (content (lowerGlobal module global).init final (flowAt final.values argument)).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner)) :
    (substitute (lowerGlobal module global).init final arguments (publicTouches effects.touched)).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) := by
  have native := (lowerGlobal_canonical_facts_of_accepted accepted globalAt)
  obtain ⟨callSite⟩ := native.calls block member value function arguments callOrigin called
  obtain ⟨target, targetAt, ownerBound⟩ := site_global_owner_query_of_accepted accepted globalAt site demand below
  have argumentAtoms : ∀ argument ∈ arguments, (flowAt final.values argument).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) := by
    intro argument argumentMember
    have bound := (lowerGlobal_operand_bounds module global).1 block member
      (.def value (.call function arguments callOrigin)) called argument argumentMember
    obtain ⟨roots, valueAt⟩ := accepted_global_factory_operand_value accepted globalAt member called argumentMember
    obtain ⟨dependencies, dependenciesAt, _⟩ := ReplacementFunctionFlow.ownerDependencies_of_value valueAt
    rw [ReplacementFunctionFlow.ownerDependencies_model, finalModel] at dependenciesAt
    have apart := argumentApart argument argumentMember
    rw [replacementQueries_ownerDependencies _ _ _ _ bound,
      ReplacementFunctionFlow.ownerDependencies_model, finalModel] at apart
    simp only [Option.bind_some] at dependenciesAt apart
    rw [dependenciesAt] at apart
    exact ownerDependencies_atoms_apart dependenciesAt apart
  exact CallOccurrence.touched_atoms_apart_of_accepted demand accepted (congrArg AccessEnv.mod site.access)
    (site.access.trans demand.access_global.symm) native member called callSite.calleeAt occurrence targetAt (global_initializer_parameterRoots_closed module global) ownerBound
    statesModel effectsAt argumentAtoms (contents callSite.callee callSite.calleeAt)

theorem site_call_assigned_apart_of_contents {module : Core.Module}
    {contextIndex : ContextId} {context : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextIndex]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, impl, context, []⟩ (.block impl.body) []
      (lowerEnv module impl.vars impl.results.toList) (cfg_implState module impl)
      (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module contextIndex
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerContextAt module context impl).provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerContextAt module context impl).valueTypes (lower module)) (lower module).rootCount) upper)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (fresh : site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size)
    {callee : Func} (calleeAt : (lower module).funcs[function]? = some callee)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) upper
      value function arguments callOrigin)
    {states : Array State} {effects current final : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (effectsAt : states[function]? = some effects)
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))).model = some final)
    (growth : current.Extends final)
    (within : current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner))
    {index : Nat} {raw : Roots} (bounded : index < callee.params.length)
    (writeAt : effects.writes[index]?.getD (.assigned .unknown) = .assigned raw)
    (contents : ∀ (parameter : Nat), (callee.roots.contents.find? (·.1 == parameter)).isSome = true →
      (callee.params[parameter]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[parameter]? = some argument →
      (content (lowerContextAt module context impl) current (flowAt current.values argument)).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner)) :
    (substitute (lowerContextAt module context impl) current arguments raw).AtomsWithin (OwnerDependencyApart (lower module) (lowerContextAt module context impl) (replacementQueries (lower module) (lowerContextAt module context impl) ((lowerContextAt module context impl).valueTypes (lower module))) owner) := by
  have argumentAtoms := site_current_call_arguments_apart accepted contextAt implAt site member called fresh finalModel growth within
  obtain ⟨target, targetAt, ownerBound⟩ := site_owner_query_of_accepted accepted contextAt implAt site demand below
  exact CallOccurrence.assigned_atoms_apart_of_accepted demand accepted (congrArg AccessEnv.mod site.access)
    (site.access.trans (demand.access_context contextAt implAt).symm) (lowerContext_canonical_facts_of_accepted accepted contextAt implAt) member called calleeAt occurrence targetAt (lowerContextAt_parameterRoots_closed accepted contextAt implAt) ownerBound
    statesModel effectsAt bounded writeAt argumentAtoms contents

theorem site_global_call_assigned_apart_of_contents {module : Core.Module}
    {globalIndex : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalIndex]? = some global)
    {upper : Prov} {blockIndex position owner replacementValue : Nat} {origin : OriginId}
    (site : SiteOccurrences ⟨module, Core.initImpl, Core.initContext, []⟩ (.expression global.init) []
      (lowerEnv module #[] [global.ty]) (cfg_globalState module global)
      (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))
      upper blockIndex position owner replacementValue origin)
    (demand : ReplacementDemandContext module (module.contexts.size + globalIndex)
      site.source.site.source.sourcePath site.source.site.source.place site.source.site.source.rhs origin)
    (below : ProvenanceBelow
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) (lower module).implTypes)
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) upper)
    {value function : ValueId} {arguments : List ValueId} {callOrigin : Option OriginId} {block : GIR.Block}
    (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    (called : Inst.def value (.call function arguments callOrigin) ∈ block.insts)
    (fresh : site.source.site.source.site.cleared.vals.size ≤ value ∧ value < site.source.site.source.site.captured.vals.size)
    {callee : Func} (calleeAt : (lower module).funcs[function]? = some callee)
    (occurrence : CallOccurrence site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init upper
      value function arguments callOrigin)
    {states : Array State} {effects current final : State}
    (statesModel : (replacementContentFlow (lower module)).model = some states)
    (effectsAt : states[function]? = some effects)
    (finalModel : ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))).model = some final)
    (growth : current.Extends final)
    (within : current.ScopedValuesWithin (ScopedOrigin site.localEnv (.expression site.source.site.source.rhs) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module)) upper site.source.site.source.site.cleared.vals.size site.source.site.source.site.captured.vals.size) (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner))
    {index : Nat} {raw : Roots} (bounded : index < callee.params.length)
    (writeAt : effects.writes[index]?.getD (.assigned .unknown) = .assigned raw)
    (contents : ∀ (parameter : Nat), (callee.roots.contents.find? (·.1 == parameter)).isSome = true →
      (callee.params[parameter]?).any Ty.isRefSlice = true →
      ∀ (argument : ValueId), arguments[parameter]? = some argument →
      (content (lowerGlobal module global).init current (flowAt current.values argument)).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner)) :
    (substitute (lowerGlobal module global).init current arguments raw).AtomsWithin (OwnerDependencyApart (lower module) (lowerGlobal module global).init (replacementQueries (lower module) (lowerGlobal module global).init ((lowerGlobal module global).init.valueTypes (lower module))) owner) := by
  have argumentAtoms := site_global_current_call_arguments_apart accepted globalAt site member called fresh finalModel growth within
  obtain ⟨target, targetAt, ownerBound⟩ := site_global_owner_query_of_accepted accepted globalAt site demand below
  exact CallOccurrence.assigned_atoms_apart_of_accepted demand accepted (congrArg AccessEnv.mod site.access)
    (site.access.trans demand.access_global.symm) (lowerGlobal_canonical_facts_of_accepted accepted globalAt) member called calleeAt occurrence targetAt (global_initializer_parameterRoots_closed module global) ownerBound
    statesModel effectsAt bounded writeAt argumentAtoms contents

#print axioms site_call_returned_apart_of_contents
#print axioms site_call_touched_apart_of_contents
#print axioms site_global_call_returned_apart_of_contents
#print axioms site_global_call_touched_apart_of_contents
#print axioms site_call_assigned_apart_of_contents
#print axioms site_global_call_assigned_apart_of_contents

end Goose.Lower.Validation
