import Goose.Lower.Validation.SummaryPreservationEntryBindingFacts
import Goose.Lower.Validation.SourceOccurrenceInductionAccepted
import Goose.Lower.Validation.SummaryPreservationEntryBindings
import Goose.Lower.Validation.SummaryPreservationSourceBodyResults
import Goose.Lower.Validation.SummaryPreservationSourceScopeBoundsAccepted
import Goose.Lower.Validation.SummaryPreservationReplayFunctionFinish
import Goose.Lower.Validation.ValidationTypedModuleTables

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def ContextReplayProduced (module : Core.Module) (ctx : Context) (impl : Impl)
    (results : Array (List RootRef)) : Prop :=
  ∃ roots range after upper,
    rpBlockValue ⟨module, impl, ctx, []⟩ [] impl.body ⟨impl.params.size, {}⟩ = .ok ((roots, range), after) ∧
    ReplayBuilder (lower module) results ((lowerContextAt module ctx impl).valueTypes (lower module))
      (lowerContextAt module ctx impl) after.eff (lowerEnv module impl.vars impl.results.toList)
      (lowerContextAt module ctx impl).scopes.size (typedContextSlotUpper module ctx impl)
      (cfg_implState module impl) upper ∧
    BuilderReturnsBound upper (contextTypedResultUpper module ctx) (cfg_implState module impl) ∧
    ∀ index, index < impl.params.size → rootsAt upper.vals index =
      rootsAt (entryRootValues (impl.params.toList.map fun p => .data (tyOfVar impl p.var))) index

theorem accepted_context_replay_produced {module : Core.Module} {ctx : Context} {impl : Impl} {context : ContextId}
    {results : Array (List RootRef)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl)
    (bounded : RootsBelow results (moduleTypedResultUpper module)) :
    ContextReplayProduced module ctx impl results := by
  obtain ⟨roots, range, after, upper, replayed, ready, returned, retained, _, _⟩ :=
    ReplacementContentFlowSource.accepted_context_occurrence_replay_produced
      accepted contextRow implementationRow bounded
  exact ⟨roots, range, after, upper, replayed, ready, returned, retained⟩

#print axioms accepted_context_replay_produced

end Goose.Lower.Validation.SummaryPreservation
