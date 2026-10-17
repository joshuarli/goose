import Goose.Lower.Validation.SourceOccurrenceInductionContext
import Goose.Lower.Validation.SourceOccurrenceGlobalInduction
import Goose.Lower.Validation.SourceOccurrenceFinishContext
import Goose.Lower.Validation.SourceOccurrenceFinishGlobal

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

theorem accepted_context_occurrence_replay_produced {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : RootsBelow results (moduleTypedResultUpper module)) :
    ContextOccurrenceReplayProduced module ctx impl results := by
  apply context_occurrence_replay_produced_of_body accepted contextRow implementationRow
  intro roots range after replayed
  have source : SourceContextEnvironment (implEnv module impl) ⟨module, impl, ctx, []⟩ context :=
    ⟨accepted, ⟨rfl, rfl⟩, rfl, contextRow, implementationRow⟩
  have valid := SourceCanonicalRootFloors.sourceRootScopeValid_block
    (validate_implementation_checks accepted (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implementationRow)))
  exact source_block_occurrence_replay impl.body source valid bounded
    (accepted_context_scope_bounds accepted contextRow implementationRow) _ _ _ _ _

theorem accepted_global_occurrence_replay_produced {module : Core.Module} {global : Core.Global}
    {index : GlobalId} {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (bounded : RootsBelow results (moduleTypedResultUpper module)) :
    GlobalOccurrenceReplayProduced module global results := by
  apply global_occurrence_replay_produced_of_expression accepted globalRow
  intro roots after replayed
  have source : SourceGlobalEnvironment (initEnv module index) ⟨module, initImpl, initContext, []⟩
      (lowerGlobal module global).init :=
    ⟨accepted, ⟨rfl, rfl⟩, rfl, rfl, rfl, global_initializer_parameterRoots_identity module global⟩
  have valid := SourceCanonicalRootFloors.sourceRootScopeValid_global (validate_global_checks accepted globalRow)
  exact global_source_expression_occurrence_replay global.init source valid bounded
    (accepted_global_scope_bounds accepted globalRow) _ _

#print axioms accepted_context_occurrence_replay_produced
#print axioms accepted_global_occurrence_replay_produced

end Goose.Lower.Validation.ReplacementContentFlowSource
