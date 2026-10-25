import Goose.Lower.Validation.SourceOccurrenceInductionAccepted
import Goose.Lower.Validation.SummaryPreservationSourceFunction
import Goose.Lower.Validation.SummaryPreservationGlobalEntryFrame
import Goose.Lower.Validation.SummaryPreservationReplayFinished
import Goose.Lower.Validation.SourceGlobalReadShape

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def GlobalReplayProduced (module : Core.Module) (global : Core.Global)
    (results : Array (List RootRef)) : Prop :=
  ∃ roots after upper,
    rpExpr ⟨module, initImpl, initContext, []⟩ global.init ⟨0, {}⟩ = .ok (roots, after) ∧
    ReplayBuilder (lower module) results ((lowerGlobal module global).init.valueTypes (lower module))
      (lowerGlobal module global).init after.eff (lowerEnv module #[] [global.ty])
      (lowerGlobal module global).init.scopes.size #[] (cfg_globalState module global) upper ∧
    BuilderReturnsBound upper [] (cfg_globalState module global)

theorem accepted_global_replay_produced {module : Core.Module} {global : Core.Global} {index : GlobalId}
    {results : Array (List RootRef)} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (bounded : RootsBelow results (moduleTypedResultUpper module)) : GlobalReplayProduced module global results := by
  obtain ⟨roots, after, upper, replayed, ready, returned, _, _⟩ :=
    ReplacementContentFlowSource.accepted_global_occurrence_replay_produced accepted globalRow bounded
  exact ⟨roots, after, upper, replayed, ready, returned⟩

theorem accepted_global_returnedRoots_empty {module : Core.Module} {global : Core.Global} {index : GlobalId}
    {candidate : Array (List RootRef)} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    (lowerGlobal module global).init.returnedRoots
      ((lowerGlobal module global).init.provenance candidate
        ((lowerGlobal module global).init.valueTypes (lower module)) rootCount) = [] := by
  obtain ⟨roots, after, upper, replayed, ready, returned⟩ :=
    accepted_global_replay_produced accepted globalRow bounded
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro root member
  have impossible := ready.finished_returnedRoots (cfg_global_blocks module global)
    (global_provenance_seed module global _ upper ready.recipes) returned rootCount root member
  cases impossible

theorem accepted_global_effects_refinement {module : Core.Module} {global : Core.Global} {index : GlobalId}
    {candidate : Array (List RootRef)} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global)
    (bounded : RootsBelow candidate (moduleTypedResultUpper module)) (rootCount : Nat) :
    ∃ roots after,
      rpExpr ⟨module, initImpl, initContext, []⟩ global.init ⟨0, {}⟩ = .ok (roots, after) ∧
      EffectRefinement (lowerGlobal module global).init
        ((lowerGlobal module global).init.effects (lower module)
          ((lowerGlobal module global).init.provenance candidate
            ((lowerGlobal module global).init.valueTypes (lower module)) rootCount)) after.eff := by
  obtain ⟨roots, after, upper, replayed, ready, returned⟩ :=
    accepted_global_replay_produced accepted globalRow bounded
  exact ⟨roots, after, replayed, ready.finished_computed_effects (cfg_global_blocks module global) rfl
    (global_provenance_seed module global _ upper ready.recipes) rootCount⟩

#print axioms accepted_global_returnedRoots_empty
#print axioms accepted_global_effects_refinement

#print axioms accepted_global_replay_produced

end Goose.Lower.Validation.SummaryPreservation
