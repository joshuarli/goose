import Goose.Lower.Validation.SourceOccurrenceInductionAccepted
import Goose.Lower.Validation.SourceOccurrenceFinishValues
import Goose.Lower.Validation.SummaryPreservationAcceptedResults

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem accepted_context_occurrence_replay_canonical {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ContextOccurrenceReplayProduced module ctx impl
      (resultRoots (lower module) ((lower module).funcs.map fun func => func.valueTypes (lower module))) :=
  accepted_context_occurrence_replay_produced accepted contextRow implementationRow
    (accepted_resultRoots_below accepted)

theorem accepted_global_occurrence_replay_canonical {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    GlobalOccurrenceReplayProduced module global
      (resultRoots (lower module) ((lower module).funcs.map fun func => func.valueTypes (lower module))) :=
  accepted_global_occurrence_replay_produced accepted globalRow (accepted_resultRoots_below accepted)

theorem accepted_context_admittedValues {module : Core.Module} {ctx : Context} {impl : Impl}
    {context : ContextId} (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    (lowerContextAt module ctx impl).admittedValues
      ((lowerContextAt module ctx impl).valueTypes (lower module))
      ((lowerContextAt module ctx impl).provenance
        (resultRoots (lower module) ((lower module).funcs.map fun func => func.valueTypes (lower module)))
        ((lowerContextAt module ctx impl).valueTypes (lower module)) (lower module).rootCount) = true :=
  context_occurrence_admittedValues accepted contextRow implementationRow
    (accepted_context_occurrence_replay_canonical accepted contextRow implementationRow) _

theorem accepted_global_admittedValues {module : Core.Module} {global : Core.Global}
    {index : GlobalId} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    (lowerGlobal module global).init.admittedValues
      ((lowerGlobal module global).init.valueTypes (lower module))
      ((lowerGlobal module global).init.provenance
        (resultRoots (lower module) ((lower module).funcs.map fun func => func.valueTypes (lower module)))
        ((lowerGlobal module global).init.valueTypes (lower module)) (lower module).rootCount) = true :=
  global_occurrence_admittedValues accepted globalRow
    (accepted_global_occurrence_replay_canonical accepted globalRow) _

#print axioms accepted_context_occurrence_replay_canonical
#print axioms accepted_global_occurrence_replay_canonical
#print axioms accepted_context_admittedValues
#print axioms accepted_global_admittedValues

end Goose.Lower.Validation.ReplacementContentFlowSource
